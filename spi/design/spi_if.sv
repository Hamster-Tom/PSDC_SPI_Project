// File: spi_if.sv
// Description: Defines the interface for the SPI master controller,
// including the clocking blocks for driver and monitor components.

interface spi_if (input clk, input rst_n);
  logic start;
  logic [7:0] tx_data;
  logic [7:0] rx_data;
  logic busy;
  logic done;
  logic sclk;
  logic mosi;
  logic miso;
  logic cs_n;

  // Clocking block for the driver.
  // This helps to synchronize the testbench signals with the DUT clock.
  clocking drv_cb @(posedge clk);
    output start;
    output tx_data;
    input rx_data;
    input busy;
    input done;
    output sclk;
    output mosi;
    input miso;
    output cs_n;
  endclocking

  // Modport for the driver, specifying which signals it can drive.
  modport DRIVER (clocking drv_cb, output sclk, mosi, cs_n, input miso);
  // Modport for the monitor, specifying which signals it can observe.
  modport MONITOR (input clk, rst_n, start, tx_data, rx_data, busy, done, sclk, mosi, miso, cs_n);

endinterface

