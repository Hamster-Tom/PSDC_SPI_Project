// spi_top module that is consisted of: sclk_generator, spi_master and spi_slave
// both the master and the slave send the data on positive edge of the sclk, 
// and sample the data on negative edge of the sclk.
// mosi of the master is connected to mosi of the slave.
// miso of the master is connected to miso of the slave.
module spi_top #(
	parameter MASTER_FREQ = 100_000_000,
	parameter SLAVE_FREQ = 1_800_000,
    parameter SPI_MODE = 1,
    parameter SPI_TRF_BIT = 8
	)
(
	input clk,
	input rst,

	// (input for spi_master) request: only TX -> 2'b01, only RX -> 2'b10, 
	// Full Duplex -> 2'b11, No Operation -> 2'00
	input [1:0] req,

	// register to store for how many clk periods CS will be low before sending
	// the first data bit and for how many clk periods CS will remain low after
	// all of the the data bits have been sent
	input [7:0] wait_duration,

	// input registers
	input [(SPI_TRF_BIT-1):0] din_master,
	input [(SPI_TRF_BIT-1):0] din_slave,

	// output registers
	output [(SPI_TRF_BIT-1):0] dout_master,
	output [(SPI_TRF_BIT-1):0] dout_slave,

	// flags from spi_master
	output done_tx,
	output done_rx

	);

	// interconnections between modules
	wire sclk;
	wire mosi;
	wire miso;
	wire cs;
	wire sclk_en;

	sclk_generator #(
		.MASTER_FREQ(MASTER_FREQ),
		.SLAVE_FREQ(SLAVE_FREQ)
	) sclk_generator_inst (
		.clk(clk),
		.rst(rst),
		.sclk_en(sclk_en), // input from master
		.sclk(sclk) // output for both the master and the slave
	);

	spi_master #(
        .SPI_MODE(SPI_MODE),
        .SPI_TRF_BIT(SPI_TRF_BIT)
    ) spi_master_inst (
		.clk(clk),
		.sclk(sclk), // input from generator
		.rst(rst),
		.req(req),
		.din(din_master), // data to be sent to slave
		.wait_duration(wait_duration),
		.miso(miso), // Master Input Slave Output
		.dout(dout_master), // data received from slave
		.sclk_en(sclk_en), // signal that enables the generation of sclk
		.cs(cs), // Chip Select (generated)
		.mosi(mosi), // Master Output Slave Input
		.done_tx(done_tx),
		.done_rx(done_rx)
	);

	spi_slave #(
        .SPI_MODE(SPI_MODE),
        .SPI_TRF_BIT(SPI_TRF_BIT)
    ) spi_slave_inst (
		.clk(clk),
		.rst(rst),
		.din(din_slave), // data to be sent to master
		.sclk(sclk), // input from generator
		.cs(cs), // Chip Select (received)
		.mosi(mosi), // Master Output Slave Input
		.miso(miso), // Master Input Slave Output
		.dout(dout_slave) // data received from master
	);

endmodule
