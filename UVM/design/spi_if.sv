interface spi_if #(
    parameter int CLK_DIV = 4
);
    //
    // DUT-side signals
    //
    logic 		clk;
    logic 		rst_n;
    logic        start;    // Start transmission
    logic [7:0]  tx_data;  // Data to transmit
    logic [7:0]  rx_data;  // Received data
    logic        busy;     // Transmission in progress
    logic        done;     // Transmission complete
    
    // SPI interface signals
    logic        sclk;     // SPI clock
    logic        mosi;     // Master out, slave in
    logic        miso;     // Master in, slave out
    logic        cs_n;     // Chip select (active low)

    //
    // Clocking block for the driver
    // The driver should drive its outputs one clock before the sampling edge.
    // Inputs are sampled on the positive edge of the clock.
    //
    clocking drv_cb @(posedge clk);
        default input #1step output #1ns;
        input  miso, rx_data, busy, done;
        output start, tx_data, cs_n, sclk, mosi;
    endclocking

    //
    // Clocking block for the monitor
    // The monitor samples all signals from the DUT on the positive edge of the clock.
    //
    clocking mon_cb @(posedge clk);
        default input #1step;
        input  start, tx_data, rx_data, busy, done;
        input  sclk, mosi, miso, cs_n;
    endclocking

endinterface
