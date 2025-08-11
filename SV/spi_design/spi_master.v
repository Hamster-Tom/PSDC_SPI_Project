module spi_master
    #(parameter SPI_MODE = 1,
      parameter SPI_TRF_BIT = 12)
(
	input clk,
	input sclk,
	input rst,
	input[1:0] req,
	input[(SPI_TRF_BIT-1):0] din,
	input[7:0] wait_duration,
	input miso,
	output[(SPI_TRF_BIT-1):0] dout,
	output sclk_en,
	output cs,
	output mosi,
	output done_tx,
	output done_rx
	);

	// states of the receiver
	parameter IDLE_RX = 1'b0, GET_DATA = 1'b1;

	// states of the transmitter
	parameter IDLE_TX = 2'b00, WAIT_STATE_1 = 2'b01, SEND_DATA = 2'b10, WAIT_STATE_2 = 2'b11;

	reg state_rx = IDLE_RX; // current state of receiver
	reg [1:0] state_tx = IDLE_TX; // current state of transmitter

	// wait registers
	reg[7:0] wait_counter = 8'd0; // counts clk posedges while in wait states
	reg[7:0] wait_duration_reg = 8'd0;

	// temporary registers
	reg mosi_temp;
	reg[(SPI_TRF_BIT-1):0] din_temp = {SPI_TRF_BIT{1'd0}}; // temporary register to store din, it's purpose is to prevent the data on input to interfeer with current transmission of data
	reg[(SPI_TRF_BIT-1):0] dout_temp = {SPI_TRF_BIT{1'd0}};
	reg done_temp_tx = 1'b0;
	reg done_temp_rx = 1'b0;

	// data bit counters
	reg[3:0] data_index_tx = 4'd0;
	reg[3:0] data_index_rx = 4'd0;

	// REQUEST HANDLING
	reg[1:0] req_temp; // store the current request to prevent it's change while performing current reuqest
	always@(posedge clk, posedge rst) begin
		if(rst) begin
			req_temp <= 2'b00; // no operation
		end
		else if(state_tx == IDLE_TX && state_rx == IDLE_RX) begin // request can be changed only when both transmitter and receiver are in their IDLE states!
			req_temp <= req;
		end
		else begin // in other states set req_temp to no operation
			req_temp <= 2'b00;
		end
	end

	// EDGE DETECTION FOR TRANSMITTER AND RECEIVER
	reg sclk_previous_value = 1'b0;
	wire sclk_posedge, sclk_negedge;
	always @(posedge clk) begin
		sclk_previous_value <= sclk; // sample last value of sclk
	end
	assign sclk_posedge = (~sclk_previous_value) & sclk; // positive edge detection (for transmitter)
	assign sclk_negedge = sclk_previous_value & (~sclk); // negative edge detection (for receiver)

	// TRANSMITTER FSM
	always @(posedge clk, posedge rst) begin
		if(rst) begin
			state_tx <= IDLE_TX;
			din_temp <= {SPI_TRF_BIT{1'd0}};
			data_index_tx <= 4'd0;
			mosi_temp <= 1'b0;
			done_temp_tx <= 1'b0;
			wait_counter <= 8'd0;
			wait_duration_reg <= 8'd0;
		end
		else begin
			case (state_tx)

				IDLE_TX: begin
					din_temp <= {SPI_TRF_BIT{1'd0}};
					data_index_tx <= 4'd0;
					mosi_temp <= 1'b0;
					done_temp_tx <= 1'b0;
					wait_counter <= 8'd0;
					if (req_temp == 2'b01 || req_temp == 2'b11) begin // transmit or full duplex request
						din_temp <= din; // sample din
						wait_duration_reg <= wait_duration; // sample wait duration
						state_tx <= WAIT_STATE_1;
					end
				end

				WAIT_STATE_1: begin
					if(wait_counter == wait_duration_reg) begin
						wait_counter <= 8'd0;
						state_tx <= SEND_DATA;
					end
					else begin
						wait_counter <= wait_counter + 1;
					end
				end

				SEND_DATA: begin
					if(sclk_posedge) begin // only send the data on the posedge of sclk
						if(data_index_tx <= (SPI_TRF_BIT-1)) begin
							mosi_temp <= din_temp[(SPI_TRF_BIT-1) - data_index_tx]; // MSB is sent first
							data_index_tx <= data_index_tx + 1;
						end else begin
							state_tx <= WAIT_STATE_2;
							din_temp <= {SPI_TRF_BIT{1'd0}};
							mosi_temp <= 1'b0;
							data_index_tx <= 4'd0;
						end
					end
				end

				WAIT_STATE_2: begin
					if(wait_counter == wait_duration_reg) begin
						done_temp_tx <= 1'b1; // transmission completed
						wait_counter <= 8'd0;
						state_tx <= IDLE_TX;
					end
					else begin
						wait_counter <= wait_counter + 1;
					end
				end

				default: state_tx <= IDLE_TX;

			endcase
		end
	end

	// RECEIVER FSM
	always@(posedge rst, posedge clk) begin
		if(rst) begin
			state_rx <= IDLE_RX;
			done_temp_rx <= 1'b0;
			data_index_rx <= 4'd0;
			dout_temp <= {SPI_TRF_BIT{1'd0}};
		end
		else begin
			case(state_rx)

				IDLE_RX: begin
					done_temp_rx <= 1'b0;
					data_index_rx <= 4'd0;
					if(req_temp == 2'b10 || req_temp == 2'b11) begin // receive or full duplex
						state_rx <= GET_DATA;
					end
				end

				GET_DATA: begin
					if(sclk_negedge) begin // receive data on the negative edge
						if(data_index_rx <= (SPI_TRF_BIT-1)) begin
							data_index_rx <= data_index_rx + 1;
							dout_temp <= {dout_temp[(SPI_TRF_BIT-2):0], miso};
						end
						else begin
							done_temp_rx <= 1'b1;
							data_index_rx <= 4'd0;
							state_rx <= IDLE_RX;
						end
					end
				end

				default: state_rx <= IDLE_RX;

			endcase
		end
	end

	assign done_tx = done_temp_tx;
	assign done_rx = done_temp_rx;
	assign mosi = mosi_temp;
	assign dout = dout_temp;
	assign sclk_en = ((state_tx == SEND_DATA) || (state_rx == GET_DATA))? 1'b1 : 1'b0; // only generate sclk when master is either sending data, receiving data or both
	assign cs = ((state_tx != IDLE_TX) || (state_rx != IDLE_RX))? 1'b0 : 1'b1; // CS is low only when some request is being executed

endmodule
