// File: spi_tran.sv
// Description: Defines the transaction class to encapsulate all data for a single SPI transfer.
// This is the primary data object passed between testbench components.

class spi_tran;
  // tx_data is randomized to create different stimulus values.
  rand bit [7:0] tx_data;
  // rx_data is captured by the monitor.
  bit [7:0] rx_data;
  // expected_rx_data is used by the scoreboard for comparison.
  bit [7:0] expected_rx_data;

  // Constructor
  function new();
  endfunction

  // Method to print the transaction in a human-readable format.
  function string toString();
    return $sformatf("TX Data: 0x%h, RX Data: 0x%h, Expected: 0x%h", tx_data, rx_data, expected_rx_data);
  endfunction
endclass

