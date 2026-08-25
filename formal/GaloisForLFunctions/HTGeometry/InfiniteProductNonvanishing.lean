import GaloisForLFunctions.HTGeometry.InfiniteProductNearOne

/-!
# Nonvanishing of absolutely convergent complex products

An absolutely summable perturbation of `1` has nonzero total product whenever no individual factor
vanishes.  This removes artificial uniform-smallness assumptions from later canonical products.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- An absolutely convergent complex product cannot vanish unless one factor vanishes. -/
theorem tprod_one_add_ne_zero_of_summable {ι : Type*} {u : ι → ℂ}
    (hsum : Summable fun i => ‖u i‖) (hne : ∀ i, 1 + u i ≠ 0) :
    ∏' i, (1 + u i) ≠ 0 := by
  have hlog : Summable (fun i => Complex.log (1 + u i)) :=
    Complex.summable_log_one_add_of_summable hsum.of_norm
  rw [← Complex.cexp_tsum_eq_tprod hne hlog]
  exact Complex.exp_ne_zero _

end


end GaloisForLFunctions.HTGeometry
