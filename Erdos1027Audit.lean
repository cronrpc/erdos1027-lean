import Erdos1027Main

/- Audit the actual final theorem types, including implicit parameters,
   and their transitive axiom dependencies. -/
set_option pp.universes true in
#check @Erdos1027Main.erdos_1027

set_option pp.universes true in
#check @Erdos1027Main.erdos_1027_subsets

#print axioms Erdos1027Main.count_lower_bound
#print axioms Erdos1027Main.erdos_1027
#print axioms Erdos1027Main.erdos_1027_subsets
