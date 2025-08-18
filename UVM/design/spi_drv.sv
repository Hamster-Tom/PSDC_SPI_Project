class spi_drv extends uvm_driver #(spi_tran);
  `uvm_component_utils(spi_drv)
  uvm_analysis_port #(spi_tran) drv_ap;
  
  virtual spi_if vif;
  
  spi_tran tr;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    drv_ap = new("drv_ap", this);
  endfunction
  
  function void build_phase(uvm_phase phase);
  	if(!uvm_config_db#(virtual spi_if)::get(this, "", "vif", vif)) begin
      `uvm_error("DRIVER", "Virtual interface not found in config db")
    end
  endfunction

  task run_phase(uvm_phase phase);
    forever begin
      seq_item_port.get_next_item(tr);
      
      uvm_config_db#(int)	::set(null, "*", "seq_count", tr.seq_count);
      uvm_config_db#(int)	::set(null, "*", "seq_index", tr.seq_index);
      uvm_config_db#(string)::set(null, "*", "seq_type", tr.seq_type);

		@(vif.drv_cb);
		vif.drv_cb.start 	<= 1;
		vif.drv_cb.tx_data 	<= tr.tx_data;
		@(vif.drv_cb);
		vif.drv_cb.start	<= 0;

      `uvm_info("DRIVER", $sformatf("Drive %0d/%0d %s sequences: txdata=0x%h, rxdata=0x%h, start=%0b Next sequence after %0d", 
      								tr.seq_index, tr.seq_count, tr.seq_type, tr.tx_data, tr.rx_data, tr.start, tr.delay), 
									UVM_MEDIUM)
									
		@(posedge vif.done);

      seq_item_port.item_done();
    end
  endtask
endclass
