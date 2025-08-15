class spi_sqr extends uvm_sequencer #(spi_tran);
  `uvm_component_utils(spi_sqr)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
endclass
