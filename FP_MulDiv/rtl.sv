module fp_muldiv (
    input  logic        clk,
    input  logic        reset,
    input  logic        in_valid,
    input  logic        div,
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic        out_valid,
    output logic [31:0] result
);

    localparam logic [31:0] CANONICAL_NAN = 32'h7FC00000;

    function automatic integer find_msb(input logic [127:0] value);
        integer i;
        begin
            find_msb = -1;
            for (i = 0; i < 128; i = i + 1) begin
                if (value[i]) find_msb = i;
            end
        end
    endfunction

    function automatic logic [127:0] round_divide(
        input logic [127:0] numerator,
        input logic [127:0] denominator
    );
        logic [127:0] q, r, twice_r;
        begin
            q       = numerator / denominator;
            r       = numerator % denominator;
            twice_r = r << 1;

            if ((twice_r > denominator) || ((twice_r == denominator) && q[0])) begin
                q = q + 1'b1;
            end
            round_divide = q;
        end
    endfunction

    function automatic logic [31:0] pack_ratio(
        input logic        sign,
        input logic [127:0] numerator,
        input logic [127:0] denominator,
        input integer      scale
    );
        integer msb_n, msb_d, ratio_exp, exponent_result, shift_amount;
        logic [127:0] n_scaled, d_scaled, rounded;
        logic [31:0]  packed_value;

        begin
            packed_value = {sign, 31'b0};

            if (numerator == 0) begin
                pack_ratio = {sign, 31'b0};
            end else begin
                msb_n = find_msb(numerator);
                msb_d = find_msb(denominator);
                ratio_exp = msb_n - msb_d;

                if (ratio_exp >= 0) begin
                    if (numerator < (denominator << ratio_exp))
                        ratio_exp = ratio_exp - 1;
                end else begin
                    if ((numerator << (-ratio_exp)) < denominator)
                        ratio_exp = ratio_exp - 1;
                end

                exponent_result = scale + ratio_exp;

                if (exponent_result >= -126) begin
                    shift_amount = 23 - ratio_exp;

                    if (shift_amount >= 0) begin
                        n_scaled = numerator << shift_amount;
                        d_scaled = denominator;
                    end else begin
                        n_scaled = numerator;
                        d_scaled = denominator << (-shift_amount);
                    end

                    rounded = round_divide(n_scaled, d_scaled);

                    if (rounded >= 128'h1000000) begin
                        rounded = rounded >> 1;
                        exponent_result = exponent_result + 1;
                    end

                    if (exponent_result > 127) begin
                        packed_value = {sign, 8'hFF, 23'b0};
                    end else begin
                        packed_value = {sign, 8'(exponent_result + 127), rounded[22:0]};
                    end
                end 
                else begin
                    shift_amount = scale + 149;

                    if (shift_amount >= 0) begin
                        n_scaled = numerator << shift_amount;
                        d_scaled = denominator;
                        rounded = round_divide(n_scaled, d_scaled);
                    end else begin
                        if ((-shift_amount) > (msb_n - msb_d + 1)) begin
                            rounded = 0;
                        end else begin
                            n_scaled = numerator;
                            d_scaled = denominator << (-shift_amount);
                            rounded = round_divide(n_scaled, d_scaled);
                        end
                    end

                    if (rounded >= 128'h800000) begin
                        packed_value = {sign, 8'h01, 23'b0};
                    end else begin
                        packed_value = {sign, 8'h00, rounded[22:0]};
                    end
                end

                pack_ratio = packed_value;
            end
        end
    endfunction

    function automatic logic [31:0] fp_calculate(
        input logic        operation_div,
        input logic [31:0] operand_a,
        input logic [31:0] operand_b
    );
        logic        sign_a, sign_b, result_sign;
        logic [7:0]  exponent_a, exponent_b;
        logic [22:0] fraction_a, fraction_b;
        logic [23:0] significand_a, significand_b;
        logic        is_zero_a, is_zero_b, is_inf_a, is_inf_b, is_nan_a, is_nan_b;
        logic [127:0] numerator, denominator;
        integer      scale_a, scale_b, result_scale;

        begin
            sign_a     = operand_a[31];
            sign_b     = operand_b[31];
            exponent_a = operand_a[30:23];
            exponent_b = operand_b[30:23];
            fraction_a = operand_a[22:0];
            fraction_b = operand_b[22:0];

            result_sign = sign_a ^ sign_b;

            is_zero_a = (exponent_a == 0) && (fraction_a == 0);
            is_zero_b = (exponent_b == 0) && (fraction_b == 0);
            is_inf_a  = (exponent_a == 8'hFF) && (fraction_a == 0);
            is_inf_b  = (exponent_b == 8'hFF) && (fraction_b == 0);
            is_nan_a  = (exponent_a == 8'hFF) && (fraction_a != 0);
            is_nan_b  = (exponent_b == 8'hFF) && (fraction_b != 0);

            significand_a = (exponent_a == 0) ? {1'b0, fraction_a} : {1'b1, fraction_a};
            significand_b = (exponent_b == 0) ? {1'b0, fraction_b} : {1'b1, fraction_b};

            scale_a = (exponent_a == 0) ? -149 : $signed({1'b0, exponent_a}) - 150;
            scale_b = (exponent_b == 0) ? -149 : $signed({1'b0, exponent_b}) - 150;

            numerator   = 0;
            denominator = 1;
            result_scale = 0;

            if (is_nan_a || is_nan_b) begin
                fp_calculate = CANONICAL_NAN;
            end 
            else if (!operation_div) begin
                if ((is_inf_a && is_zero_b) || (is_inf_b && is_zero_a)) begin
                    fp_calculate = CANONICAL_NAN;
                end else if (is_inf_a || is_inf_b) begin
                    fp_calculate = {result_sign, 8'hFF, 23'b0};
                end else if (is_zero_a || is_zero_b) begin
                    fp_calculate = {result_sign, 31'b0};
                end else begin
                    numerator    = significand_a * significand_b;
                    denominator  = 1;
                    result_scale = scale_a + scale_b;
                    fp_calculate = pack_ratio(result_sign, numerator, denominator, result_scale);
                end
            end 
            else begin
                if ((is_zero_a && is_zero_b) || (is_inf_a && is_inf_b)) begin
                    fp_calculate = CANONICAL_NAN;
                end else if (is_inf_a || is_zero_b) begin
                    fp_calculate = {result_sign, 8'hFF, 23'b0};
                end else if (is_inf_b || is_zero_a) begin
                    fp_calculate = {result_sign, 31'b0};
                end else begin
                    numerator    = significand_a;
                    denominator  = significand_b;
                    result_scale = scale_a - scale_b;
                    fp_calculate = pack_ratio(result_sign, numerator, denominator, result_scale);
                end
            end
        end
    endfunction

    always_comb begin
        result    = 32'b0;
        out_valid = 1'b0;

        if (in_valid && !reset) begin
            result    = fp_calculate(div, a, b);
            out_valid = 1'b1;
        end
    end

endmodule