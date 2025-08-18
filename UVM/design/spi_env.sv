class spi_env extends uvm_env;
  `uvm_component_utils(spi_env)

  spi_agt agt;
  spi_scb scb;
  spi_cov cov;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agt = spi_agt::type_id::create("agt", this);
    scb = spi_scb::type_id::create("scb", this);
    cov = spi_cov::type_id::create("cov", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    agt.agt_ap.connect(scb.scb_imp);
    agt.agt_ap.connect(cov.cov_imp);
  endfunction
endclass
