kat_reification_MLLIB_DEPENDENCIES:= kat_dec kat_reification
kat_reification.cma:$(addsuffix .cmo,$(kat_reification_MLLIB_DEPENDENCIES))
kat_reification.cmxa:$(addsuffix .cmx,$(kat_reification_MLLIB_DEPENDENCIES))
