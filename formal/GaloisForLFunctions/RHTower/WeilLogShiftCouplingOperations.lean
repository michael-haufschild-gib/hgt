import GaloisForLFunctions.RHTower.WeilLogShiftCouplingSlack

/-! Transposition and off-diagonal extensionality for finite couplings. -/

open scoped BigOperators NNReal

namespace RHTower

theorem finiteWeilCoupling_ext_of_off_diagonal {ι : Type*} [Fintype ι] {P Q : ι → ℝ≥0}
    (gamma eta : HTGeometry.FiniteNNCoupling P Q)
    (hoff : ∀ u v, u ≠ v → gamma.plan u v = eta.plan u v) : gamma = eta := by
  classical
  apply finiteWeilCoupling_ext
  intro u v
  by_cases huv : u = v
  · subst v
    have hg := congrArg NNReal.toReal (gamma.row u)
    have he := congrArg NNReal.toReal (eta.row u)
    simp only [NNReal.coe_sum] at hg he
    have hz : (∑ w, ((gamma.plan u w : ℝ) - (eta.plan u w : ℝ))) = 0 := by
      rw [Finset.sum_sub_distrib, hg, he, sub_self]
    have hp (w : ι) : (gamma.plan u w : ℝ) - (eta.plan u w : ℝ) =
        if w = u then (gamma.plan u u : ℝ) - (eta.plan u u : ℝ) else 0 := by
      by_cases hw : w = u
      · subst w
        simp
      · rw [hoff u w (fun h => hw h.symm), sub_self, if_neg hw]
    have hsum := Finset.sum_congr rfl (fun w (_ : w ∈ Finset.univ) => hp w)
    rw [hsum] at hz
    simp at hz
    apply NNReal.coe_injective
    linarith only [hz]
  · exact hoff u v huv

def finiteWeilCouplingTranspose {ι : Type*} [Fintype ι] {P Q : ι → ℝ≥0}
    (gamma : HTGeometry.FiniteNNCoupling P Q) : HTGeometry.FiniteNNCoupling Q P where
  plan u v := gamma.plan v u
  row := gamma.col
  col := gamma.row

theorem finiteWeilCouplingTranspose_involutive {ι : Type*} [Fintype ι] {P Q : ι → ℝ≥0}
    (gamma : HTGeometry.FiniteNNCoupling P Q) :
    finiteWeilCouplingTranspose (finiteWeilCouplingTranspose gamma) = gamma := by
  apply finiteWeilCoupling_ext
  intro u v
  rfl

theorem finiteWeilCouplingCost_transpose {ι : Type*} [Fintype ι] {P Q : ι → ℝ≥0}
    (gamma : HTGeometry.FiniteNNCoupling P Q) (c : ι → ι → ℝ) (hc : ∀ u v, c u v = c v u) :
    finiteWeilCouplingCost (finiteWeilCouplingTranspose gamma) c = finiteWeilCouplingCost gamma c := by
  change (∑ u, ∑ v, (gamma.plan v u : ℝ) * c u v) =
    (∑ u, ∑ v, (gamma.plan u v : ℝ) * c u v)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [hc v u]

end RHTower
