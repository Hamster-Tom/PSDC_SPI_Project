class spi_mon extends uvm_monitor;
  `uvm_component_utils(spi_mon)

  uvm_analysis_port #(spi_tran) mon_ap;
  
  int 				seq_count;
  int 				seq_index;
  string 			seq_type;
  virtual spi_if	vif;
  spi_tran 			tr;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    mon_ap 	= new("mon_ap", this);
  endfunction
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_config_db#(virtual spi_if)::get(this, "", "vif", vif)) begin
      `uvm_error("MONITOR", "Virtual interface not found in config db")
    end
  endfunction
  
  task run_phase(uvm_phase phase);
  	@(vif.mon_cb);
  	@(vif.mon_cb);
    forever begin
    
   	  if(!uvm_config_db#(int)::get(null, "", "seq_count", seq_count)) begin
        `uvm_warning("MONITOR", "Unable to retrieve seq_count from spi_drv")
      end
      if(!uvm_config_db#(int)::get(null, "", "seq_index", seq_index)) begin
        `uvm_warning("MONITOR", "Unable to retrieve seq_index from spi_drv")
      end
      if(!uvm_config_db#(string)::get(null, "", "seq_type", seq_type)) begin
        `uvm_warning("MONITOR", "Unable to retrieve seq_type from spi_drv")
      end
    
      @(vif.mon_cb);
      tr = spi_tran::type_id::create("tr");
      
      tr.tx_data 	= vif.mon_cb.tx_data;
      tr.rx_data 	= vif.mon_cb.rx_data;
      tr.start 		= vif.mon_cb.start;
      tr.busy 		= vif.mon_cb.busy;
      tr.done 		= vif.mon_cb.done;

      `uvm_info("MONITOR", $sformatf("Observed %0d/%0d %s sequences: txdata=0x%h, rxdata=0x%h, start=%0b Next sequence after %0d", 
    								seq_index, seq_count, seq_type, tr.tx_data, tr.rx_data, tr.start, tr.delay), 
                                   	UVM_MEDIUM)

      tr.seq_count = this.seq_count;
      tr.seq_index = this.seq_index;
      tr.seq_type = this.seq_type;
      @(posedge vif.done);
      mon_ap.write(tr);
    end
  endtask
endclass
