module sclk_generator
#(
	parameter MASTER_FREQ = 100_000_000,
	parameter SLAVE_FREQ = 1_800_000
	)
(
	input clk,
	input sclk_en,
	input rst,
	output sclk
	);

	// since sclk is TOGGLING after wait_count number of clk positive edges, 
	// frequency of the slave device is multiplied by 2, so one period of 
	// sclk lasts for 2 * wait_count number of clk positive edges which is 
	// equal to MASTER_FREQ / SLAVE_FREQ

    // max positive edges that can be counted are 1023
	reg[9:0] wait_count = MASTER_FREQ / (SLAVE_FREQ * 2);

	reg sclk_temp = 1'b0;
	reg[10:0] count = 11'd0; // counts clk posedges for sclk generation

	// frequency divider
	always@(posedge rst, posedge clk)
	begin
		if(rst) begin
			count <= 11'd0;
			sclk_temp <= 1'b0;
		end
		else if(sclk_en) begin
			if(count < wait_count) begin
				count <= count + 1;
			end
			else begin
				count <= 11'd0;
                // toggle sclk after half of it's period has passed
				sclk_temp <= ~sclk_temp; 
			end
		end
		else begin
			count <= 11'd0;
			sclk_temp <= 1'b0;
		end
	end

	assign sclk = sclk_temp;

endmodule
