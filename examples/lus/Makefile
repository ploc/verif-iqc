SRC = $(wildcard *.lus)
#SRC = large_LTI_system.lus

all: ${SRC:%.lus=%_updateState.bounds} ${SRC:%.lus=%_updateOutput.bounds} 

.PHONY: %.check.lus all

%.check.lus: %.lus
	@echo "- Checking validity of lustre source file $<"
	@ lustrec -d build $<  >& /dev/null

build/%_updateOutput.tiny: %.lus %.check.lus
	@echo "- Producing Tiny source for function updateOutput"
	@lustrev -tiny -node updateOutput -tiny-output -tiny-abstract-domain intervals_infint -d build $< >& /dev/null	

build/%_updateState.tiny: %.lus %.check.lus
	@echo "- Producing Tiny source for function updateState"
	@lustrev -tiny -node updateState -tiny-output -tiny-abstract-domain intervals_infint -d build $< >& /dev/null	


build/%.tiny_flat: build/%.tiny
	$(eval lus:=`basename $< | sed "s/_update.*//"`.lus)
	@echo "- Preparing file for analysis: lustre file $(lus)"
	@echo "-- variable def"
	@cat $< | grep ^real > $@
	@cat $@ | xargs |sed "s/real//g;s/ //g;s/;$$//;s/;/\\\|/g;" > $@_vars
	@echo "-- Extracting bounds from input lustre file - focus on delta parameters defined in requires statements"
	@grep requires $(lus) | grep "<=" | sed "s/requires //;s/;//;s/&&/\n/" | sort -u | sed "s/\([^<]*\) <= \([^<]*\) <= \(.*\)/\2 = rand_real(\1, \3);/g" | grep `cat $@_vars` >> $@ || true
	@echo "-- Extracting bounds from input lustre file - focus on d parameters (inputs) defined in assume statements"
	@grep assume $(lus) | grep "<=" | sort -u | sed "s/.*assumes //;s/;//;s/ && /\n/g" | grep -v "+" | sed "s/\([^<]*\) <= \([^<]*\) <= \(.*\)/\2 = rand_real(\1, \3);/g" | grep `cat $@_vars` >> $@
	@echo "-- Extracting bounds - focus on state and input variables bounds"
	@grep "| <= " $(lus) | sed "s/|//g;s/<= \([^;]*\)/= rand_real(-\1,\1)/" | grep `cat $@_vars` >> $@
	@echo "-- Extracting main computation from produced tiny source"
	@gtail -n +`grep -n -m 1 "__update.*=" $< | sed "s/:.*//"` $< |grep -v while | grep -v "}" | grep -v rand_real >> $@

build/%.log_bounds: build/%.tiny_flat
	@echo "- Running floating point analysis: max error for output variables"
	@tiny -v 2 -a intervals_double_err $< >&  $<.log
	@gtail -n +`cat $<.log | grep -n "intervals_double_err" | tail -n 1| sed "s/:.*//"` $<.log  | sed "s/ }.*//;s/\/\* {intervals_double_err//;s/ : \[[^]]*\] + ±/: /g;s/,/\n/g" | sed "s/ //g" | sort -u > $@


%_updateOutput.bounds: build/%_updateOutput.log_bounds
	@cat $< | grep y | sed "s/y.*://;s/$$/,/" |xargs > build/log_values_y
	@python -c "print('Max. Output Error = ',max([`cat build/log_values_y`]))" 

%_updateState.bounds: build/%_updateState.log_bounds
	@cat $< | grep x | sed "s/x.*://;s/$$/,/" |xargs > build/log_values_x
	@python -c "print('Max. State Error = ',max([`cat build/log_values_x`]))" 


