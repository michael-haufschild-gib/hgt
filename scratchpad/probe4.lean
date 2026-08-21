import Mathlib
open scoped Pointwise
open Finset
variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]
#check @Finset.smul_finset_inter
#check @Finset.smul_finset_union
#check @Finset.smul_finset_sdiff
#check @Finset.card_lt_card
#check @Finset.exists_min_image
#check @Finset.mul_subset_mul
example (a b : G) (H : Finset G) : (a • H) * (b • H) = (a*b) • (H * H) := by exact?
