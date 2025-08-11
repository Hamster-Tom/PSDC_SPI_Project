// File: spi_cov.sv
// Description: Implements functional coverage using a covergroup to track
// important design features, such as transmitted and received data values.

class spi_cov;
  covergroup spi_cg;
    // Coverpoint for the transmitted data.
    tx_data_cp: coverpoint spi_tran.tx_data;
    // Coverpoint for the received data.
    rx_data_cp: coverpoint spi_tran.rx_data;
  endgroup

  // Constructor
  function new();
    spi_cg = new();
  endfunction

  // Method to sample the covergroup.
  function void sample(spi_tran tr);
    spi_cg.sample();
  endfunction
endclass

