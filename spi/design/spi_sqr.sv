// File: spi_sqr.sv
// Description: This is a placeholder for a sequencer class.
// In a non-UVM testbench, the sequencer's role is often simplified or handled
// directly by the test class, which populates the driver's mailbox.

class spi_sqr;
  mailbox #(spi_tran) mbx;

  // Constructor
  function new(mailbox #(spi_tran) mbx);
    this.mbx = mbx;
  endfunction
endclass

