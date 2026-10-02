import GaloisForLFunctions.HTGeometry.OrderOneEntireUnitEquation
import GaloisForLFunctions.RHTower.ThetaHalfLinePortGauge
import GaloisForLFunctions.RHTower.XiZeroCountJensenBound

/-!
# Finite-order rigidity of the exact theta half-port

The growth hypothesis in scalar gauge rigidity can be weakened from finite
exponential type to arbitrary finite order. The theta identity itself forces
the stronger order-one envelope, by differentiated elimination at one simple
critical zero. This theorem supplies no off-axis zero exclusion.
-/

noncomputable section

open Complex Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem orderOneEnvelope_thetaSymmetrizedPort : OrderOneEnvelope thetaSymmetrizedPort := by
  refine (orderOneEnvelope_xi.comp_affine (-1) (1 / 2)).congr fun w => ?_
  rw [thetaSymmetrizedPort, thetaHalfLaplace_add_neg, XiC]
  congr 1
  rw [show (I * w) * I = w * (I * I) by ring, Complex.I_mul_I]
  ring

/-- The causal half-port has the order-one growth of its exact symmetrization. -/
theorem orderOneEnvelope_thetaHalfLaplace : OrderOneEnvelope thetaHalfLaplace := by
  obtain ⟨M, hM, hdecay⟩ := exists_abs_thetaCuspFullSource_le 1
  have hleft (w : ℂ) (hw : w.re ≤ 0) : ‖thetaHalfLaplace w‖ ≤ M := by
    have h := norm_thetaHalfLaplaceTail_le (A := 1) (C := M) (σ := 0) (L := 0)
      hdecay (by norm_num) (by norm_num) hw
    simpa [thetaHalfLaplace] using h
  have hb (w : ℂ) : ‖thetaHalfLaplace w‖ ≤ ‖thetaSymmetrizedPort w‖ + M := by
    by_cases hw : w.re ≤ 0
    · exact (hleft w hw).trans (by linarith [norm_nonneg (thetaSymmetrizedPort w)])
    · have hn : (-w).re ≤ 0 := by simp only [neg_re]; linarith
      calc
        ‖thetaHalfLaplace w‖ = ‖thetaSymmetrizedPort w - thetaHalfLaplace (-w)‖ := by
          simp only [thetaSymmetrizedPort, add_sub_cancel_right]
        _ ≤ ‖thetaSymmetrizedPort w‖ + ‖thetaHalfLaplace (-w)‖ := norm_sub_le _ _
        _ ≤ _ := add_le_add le_rfl (hleft (-w) hn)
  have hnorm : OrderOneEnvelope (fun w => (‖thetaSymmetrizedPort w‖ : ℂ)) := by
    obtain ⟨C, hC, hbound⟩ := orderOneEnvelope_thetaSymmetrizedPort
    exact ⟨C, hC, fun w => by simpa using hbound w⟩
  obtain ⟨C, hC, hbound⟩ := hnorm.add (orderOneEnvelope_const (M : ℂ))
  refine ⟨C, hC, fun w => (hb w).trans ?_⟩
  simpa only [← Complex.ofReal_add, Complex.norm_real,
    Real.norm_of_nonneg (add_nonneg (norm_nonneg _) hM)] using hbound w

/-- Every zero-free entire scalar gauge of finite order preserving the exact
theta half-port symmetrization is the identity. No zero-location premise is used. -/
theorem thetaHalfLaplace_finiteOrder_gauge_eq_one {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (hg0 : ∀ w, g w ≠ 0)
    (hfinite : FiniteOrderEnvelope g)
    (hsym : ∀ w, g w * thetaHalfLaplace w +
      halfPortReflect (fun z => g z * thetaHalfLaplace z) w =
      thetaHalfLaplace w + halfPortReflect thetaHalfLaplace w) :
    ∀ w, g w = 1 := by
  have hrd : Differentiable ℂ (halfPortReflect g) := by
    intro w
    have hc := ((hg (-(starRingEnd ℂ) w)).hasDerivAt.comp ((starRingEnd ℂ) w)
      (hasDerivAt_neg _)).conj_conj
    have he : (⇑(starRingEnd ℂ) ∘ (g ∘ fun z => -z) ∘ ⇑(starRingEnd ℂ)) =
        halfPortReflect g := rfl
    rw [he, Complex.conj_conj] at hc
    exact hc.differentiableAt
  have hr0 : ∀ w, halfPortReflect g w ≠ 0 := by
    intro w hw
    have h := congrArg (starRingEnd ℂ) hw
    apply hg0 (-(starRingEnd ℂ) w)
    simpa only [halfPortReflect, Complex.conj_conj, map_zero] using h
  have hrf : FiniteOrderEnvelope (halfPortReflect g) := by
    obtain ⟨C, d, hC, hb⟩ := hfinite
    exact ⟨C, d, hC, fun w => by simpa [halfPortReflect] using hb (-(starRingEnd ℂ) w)⟩
  have heq (w : ℂ) : g w * thetaHalfLaplace w +
      halfPortReflect g w * thetaHalfLaplace (-w) = thetaSymmetrizedPort w := by
    have hp : halfPortReflect (fun z => g z * thetaHalfLaplace z) w =
        halfPortReflect g w * thetaHalfLaplace (-w) := by
      change (starRingEnd ℂ) (g (-(starRingEnd ℂ) w) *
        thetaHalfLaplace (-(starRingEnd ℂ) w)) = _
      rw [map_mul]
      exact congrArg (halfPortReflect g w * ·) (halfPortReflect_thetaHalfLaplace w)
    simpa only [hp, halfPortReflect_thetaHalfLaplace, thetaSymmetrizedPort] using hsym w
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := exists_simpleCrossing_above 1 (Or.inl rfl) 0
  have hX0 : thetaSymmetrizedPort (γ * I) = 0 := by
    rw [thetaSymmetrizedPort_mul_I, hγ0, ofReal_zero]
  have hX1 : deriv thetaSymmetrizedPort (γ * I) ≠ 0 := by
    rw [deriv_thetaSymmetrizedPort_mul_I]
    exact mul_ne_zero (neg_ne_zero.mpr I_ne_zero)
      (ofReal_ne_zero.mpr (by simpa using ne_of_gt hγ1))
  have hB0 : thetaHalfLaplace (-(γ * I)) ≠ 0 :=
    thetaHalfLaplace_neg_ne_zero_of_nonneg (by simp)
  have hKg := orderOneEnvelope_thetaHalfLaplace
  have hBg : OrderOneEnvelope (fun w => thetaHalfLaplace (-w)) :=
    (hKg.comp_affine (-1) 0).congr fun w => by simp
  have hgg := orderOneEnvelope_of_finiteOrder_unit_equation
    differentiable_thetaHalfLaplace (differentiable_thetaHalfLaplace.comp differentiable_neg)
    differentiable_thetaSymmetrizedPort hg hrd hKg hBg orderOneEnvelope_thetaSymmetrizedPort
    hg0 hr0 hfinite hrf heq hX0 hX1 hB0
  obtain ⟨C, hC, hb⟩ := hgg.subquadratic
  obtain ⟨b, hgb⟩ := exists_linear_of_ne_zero_of_growth hg hg0
    (by norm_num : (0 : ℝ) ≤ 3 / 2) (by norm_num : (3 / 2 : ℝ) < 2) hC hb
  apply thetaHalfLaplace_gauge_eq_one hg hg0 (C := ‖g 0‖) (A := ‖b‖) _ hsym
  intro w
  rw [hgb w, norm_mul, norm_exp]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  exact (Complex.re_le_norm _).trans (by rw [norm_mul])

end RHTower
