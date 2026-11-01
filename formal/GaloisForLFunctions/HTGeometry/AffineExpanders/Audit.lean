import GaloisForLFunctions.HTGeometry.AffineExpanders.Family

/-! # Kernel dependency checks for the affine expander family -/

/--
info: 'AffineExpanders.spectralGap_mgg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AffineExpanders.spectralGap_mgg

/--
info: 'AffineExpanders.mgg_expander_family' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AffineExpanders.mgg_expander_family

/--
info: 'AffineExpanders.norm_mgg_centered_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AffineExpanders.norm_mgg_centered_le
