all : full_angle.vo forward_rules.vo

full_angle.vo : full_angle.v
	coqc -R /home/klotz/galapagos/dev/trunk/GeoCoq/ "GeoCoq" full_angle.v


forward_rules.vo : forward_rules.v
	coqc -R /home/klotz/galapagos/dev/trunk/GeoCoq/ "GeoCoq" forward_rules.v

clean :
	rm -f *~ *.glob *.vo
