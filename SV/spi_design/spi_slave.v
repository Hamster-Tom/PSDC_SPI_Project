module spi_slave
    #(parameter SPI_MODE = 1,
      parameter SPI_TRF_BIT = 12)
(
	input clk,
	input sclk,
	input rst,
	input[(SPI_TRF_BIT-1):0] din,
	input cs,
	input mosi,
	output miso,
	output[(SPI_TRF_BIT-1):0] dout
	);

	parameter IDLE_TX = 1'b0, SEND_DATA = 1'b1; // transmitter states
	parameter IDLE_RX = 1'b0, GET_DATA = 1'b1; // receiver states

	reg state_tx = IDLE_TX; // state of the transmitter
	reg state_rx = IDLE_RX; // state of the receiver

	// EDGE DETECTION FOR TRANSMITTER AND RECEIVER
	reg sclk_previous_value = 1'b0;
	wire sclk_posedge, sclk_negedge;
	always @(posedge clk) begin
		sclk_previous_value <= sclk; // sample last value of sclk
	end
	assign sclk_posedge = (~sclk_previous_value) & sclk; // positive edge detection (for transmitter)
	assign sclk_negedge = sclk_previous_value & (~sclk); // negative edge detection (for receiver)

	// temporary registers
	reg miso_temp;
	reg[(SPI_TRF_BIT-1):0] din_temp = {SPI_TRF_BIT{1'd0}}; // temporary register to store din, it's purpose is to prevent the data on input to interfeer with current transmission of data
	reg[(SPI_TRF_BIT-1):0] dout_temp = {SPI_TRF_BIT{1'd0}};
	reg[3:0] data_index_tx = 4'd0;
	reg[3:0] data_index_rx = 4'd0;

	// TRANSMITTER FSM
	always @(posedge clk, posedge rst) begin
		if(rst) begin
			state_tx <= IDLE_TX;
			din_temp <= {SPI_TRF_BIT{1'd0}};
			data_index_tx <= 4'd0;
			miso_temp <= 1'b0;
		end
		else begin
			case (state_tx)

				IDLE_TX: begin
					din_temp <= {SPI_TRF_BIT{1'd0}};
					data_index_tx <= 4'd0;
					miso_temp <= 1'b0;
					if(!cs) begin // transmit or full duplex request
						din_temp <= din; // sample din
						state_tx <= SEND_DATA;
					end
				end

				SEND_DATA: begin
					if(sclk_posedge) begin // only send the data on the posedge of sclk
						if(data_index_tx <= (SPI_TRF_BIT-1)) begin
							miso_temp <= din_temp[(SPI_TRF_BIT-1) - data_index_tx]; // MSB is sent first
							data_index_tx <= data_index_tx + 1;
						end else begin
							state_tx <= IDLE_TX;
							din_temp <= {SPI_TRF_BIT{1'd0}};
							miso_temp <= 1'b0;
							data_index_tx <= 4'd0;
						end
					end
					else if(cs) begin // if cs changes mid transfer return to idle!
						state_tx <= IDLE_TX;
						din_temp <= {SPI_TRF_BIT{1'd0}};
						data_index_tx <= 4'd0;
						miso_temp <= 1'b0;
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
			data_index_rx <= 4'd0;
			dout_temp <= {SPI_TRF_BIT{1'd0}};
		end
		else begin
			case(state_rx)

				IDLE_RX: begin
					data_index_rx <= 4'd0;
					if(!cs) begin
						state_rx <= GET_DATA;
					end
				end

				GET_DATA: begin
					if(sclk_negedge) begin
						if(data_index_rx <= (SPI_TRF_BIT-1)) begin
							data_index_rx <= data_index_rx + 1;
							dout_temp <= {dout_temp[(SPI_TRF_BIT-2):0], mosi};
						end
						else begin
							data_index_rx <= 4'd0;
							state_rx <= IDLE_RX;
						end
					end
					else if(cs) begin // if cs changes mid state, return to idle!
						state_rx <= IDLE_RX;
						data_index_rx <= 4'd0;
						dout_temp <= {SPI_TRF_BIT{1'd0}};
					end
				end

				default: state_rx <= IDLE_RX;

			endcase
		end
	end

	assign miso = miso_temp;
	assign dout = dout_temp;

endmodule
