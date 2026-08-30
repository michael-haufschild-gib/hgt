import GaloisForLFunctions.RHTower.BurnolCoPoissonCosineClosedContinuousLowerJetSystem
import GaloisForLFunctions.RHTower.BurnolCoPoissonCompletedZeroJets

/-!
# Exact zero-jet detection on the closed cosine co-Poisson source

For every right-half Xi divisor and every literal aperture `0 < b < 1`, the
closed cosine-stable Burnol co-Poisson source has precisely the divisor's
zeta conormal order: every lower completed Mellin jet vanishes on the whole
closed source space, while one explicit logarithmic subwindow has nonzero
jet at that order.

This is a source-selected, coefficient-faithful exact-order statement.  It
does not identify the source space with the full joint jet annihilator (the
remaining `L_a/K_a/P_a` complement theorem), and it makes no RH claim.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- The closed cosine co-Poisson source at `b` has exact Xi-jet order at
`rho`: every lower completed jet is killed globally, and some literal source
survives at the first nonzero jet. -/
def BurnolCoPoissonSourceHasExactXiJetOrder
    (b : ℝ) (rho : XiDivisorSupport) : Prop :=
  (∀ {f : evenSubspace}, f ∈ burnolCoPoissonSourceSpace b →
      ∀ {j : ℕ}, j < burnolCoPoissonXiConormalOrder rho →
        iteratedDeriv j
          (fun w : ℂ => soninMellinEvaluation w ((f : evenSubspace) : SoninL2))
          (rho : ℂ) = 0) ∧
  ∃ f : evenSubspace, f ∈ burnolCoPoissonSourceSpace b ∧
    iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
      (fun w : ℂ => soninMellinEvaluation w ((f : evenSubspace) : SoninL2))
      (rho : ℂ) ≠ 0

/-- **Exact closed-source zero-jet system.** At the aperture of every
positive logarithmic co-Poisson subwindow, all jets below the exact Xi
conormal order vanish on the entire closed cosine source space; its literal
subwindow source has a nonzero jet at that order. -/
theorem burnolCoPoissonSourceSpace_exactJetDetection
    (L : ℝ) (hL : 0 < L) (rho : XiDivisorSupport)
    (hright : 1 / 2 < (rho : ℂ).re) :
    BurnolCoPoissonSourceHasExactXiJetOrder
      (subWindowAperture (Real.exp (-L)) 1) rho := by
  unfold BurnolCoPoissonSourceHasExactXiJetOrder
  let a : ℝ := subWindowAperture (Real.exp (-L)) 1
  have ha : 0 < a :=
    subWindowAperture_pos (Real.exp_pos (-L))
      (Real.exp_le_one_iff.mpr (by linarith))
  constructor
  · intro f hf j hj
    exact iteratedDeriv_soninMellinEvaluation_eq_zero_of_mem_burnolCoPoissonSourceSpace_of_lt
      ha rho hright hj hf
  · let src : BurnolCoPoissonSource a :=
      coPoissonSubWindowSource (Real.exp_pos (-L))
        (Real.exp_le_one_iff.mpr (by linarith))
    refine ⟨src.vector, ?_, ?_⟩
    · exact (burnolCoPoissonAlgebraicSourceSpace a).le_topologicalClosure
        (Submodule.subset_span ⟨src, Or.inl rfl⟩)
    · change iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (burnolCoPoissonExpWindowCompletedEvaluation L hL.le) (rho : ℂ) ≠ 0
      exact iteratedDeriv_burnolCoPoissonExpWindowCompletedEvaluation_ne_zero L hL rho

/-- **Every subcritical aperture has an exact closed-source Xi jet system.**
The explicit source is the logarithmic window `[b, 1]`; it keeps the first
nonzero zeta jet while the closed source relation kills every lower one. -/
theorem burnolCoPoissonSourceSpace_exactJetDetection_of_lt_one
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) (rho : XiDivisorSupport)
    (hright : 1 / 2 < (rho : ℂ).re) :
    BurnolCoPoissonSourceHasExactXiJetOrder b rho := by
  let L : ℝ := -Real.log b
  have hL : 0 < L := by
    dsimp [L]
    rw [neg_pos]
    exact Real.log_neg hb hb1
  have hExp : Real.exp (-L) = b := by
    dsimp [L]
    rw [neg_neg, Real.exp_log hb]
  have ha : subWindowAperture (Real.exp (-L)) 1 = b := by
    rw [hExp]
    exact subWindowAperture_left_eq hb hb1.le
      ((one_lt_inv₀ hb).mpr hb1).le
  rw [← ha]
  exact burnolCoPoissonSourceSpace_exactJetDetection L hL rho hright

end RHTower
