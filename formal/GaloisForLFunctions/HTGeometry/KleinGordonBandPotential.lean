import GaloisForLFunctions.HTGeometry.KleinGordonSwitchedPotential

/-!
# Band-limited perturbations, where the two threads meet

The conditional stability estimate reconstructs a perturbation from the field it produces, provided
the perturbation only couples frequencies below a fixed cut-off: `A = P_R A P_R`. Multiplication by a
function of position is never of that form, so as it stood the estimate and the concrete real
potentials of the energy thread had no common ground.

This file supplies it. Compressing any bounded operator to the band, `A ↦ P_R A P_R`, produces an
operator that *is* of that form — because the low-pass projection is idempotent — and that is
self-adjoint whenever the operator is, because the projection is. So the band compression of a real
potential is simultaneously

* an admissible perturbation for the conditional stability estimate, and
* a self-adjoint perturbation for the exact conservation law.

Physically it is the part of the potential a field of bounded frequency can actually feel, and it is
the class on which the inverse problem of this card is well posed.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The low-pass projection is a projection -/

set_option maxHeartbeats 1000000 in
/-- **The low-pass projection is idempotent.** -/
theorem kgLowPassOp_comp_self (R : ℝ) :
    (kgLowPassOp (E := E) R).comp (kgLowPassOp R) = kgLowPassOp R := by
  rw [kgLowPassOp_eq]
  refine fourierMulCLM_comp _ _ (measurable_kgLowPass (E := E) R) _ _ _ _ zero_le_one
    (norm_kgLowPass_le R) (Filter.Eventually.of_forall fun ξ => ?_)
  rw [kgLowPass]
  split <;> simp

theorem kgLowPassOp_idem (R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgLowPassOp R (kgLowPassOp R x) = kgLowPassOp R x := by
  have h := congrArg (fun T : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) => T x)
    (kgLowPassOp_comp_self (E := E) R)
  exact h

/-- **The low-pass projection is self-adjoint.** -/
theorem inner_kgLowPassOp (R : ℝ) (x y : Lp ℂ 2 (volume : Measure E)) :
    (inner ℂ (kgLowPassOp R x) y : ℂ) = inner ℂ x (kgLowPassOp R y) :=
  inner_fourierMulCLM_real _ _ _ (fun ξ => by
    rw [kgLowPass]
    split <;> simp) x y

/-! ## The band compression -/

/-- **The band compression** of a perturbation: the part of it a field of frequency below `R` can
feel. -/
def kgBandOp (W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) (R : ℝ) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  (kgLowPassOp R).comp (W₀.comp (kgLowPassOp R))

theorem kgBandOp_apply (W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgBandOp W₀ R x = kgLowPassOp R (W₀ (kgLowPassOp R x)) := rfl

theorem norm_kgBandOp_le {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)}
    {b : ℝ} (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b) (R : ℝ) : ‖kgBandOp W₀ R‖ ≤ b := by
  refine ContinuousLinearMap.opNorm_le_bound _ hb0 fun x => ?_
  rw [kgBandOp_apply]
  have h1 := norm_kgLowPassOp_apply_le R (W₀ (kgLowPassOp R x))
  have h2 : ‖W₀ (kgLowPassOp (E := E) R x)‖ ≤ b * ‖kgLowPassOp (E := E) R x‖ :=
    W₀.le_of_opNorm_le hW _
  have h3 : ‖kgLowPassOp (E := E) R x‖ ≤ ‖x‖ := norm_kgLowPassOp_apply_le R x
  have h4 : b * ‖kgLowPassOp (E := E) R x‖ ≤ b * ‖x‖ := mul_le_mul_of_nonneg_left h3 hb0
  linarith

/-- **The band compression is self-adjoint whenever the perturbation is.** -/
theorem inner_kgBandOp {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)}
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W₀ x) y : ℂ) = inner ℂ x (W₀ y))
    (R : ℝ) (x y : Lp ℂ 2 (volume : Measure E)) :
    (inner ℂ (kgBandOp W₀ R x) y : ℂ) = inner ℂ x (kgBandOp W₀ R y) := by
  rw [kgBandOp_apply, kgBandOp_apply, inner_kgLowPassOp, hsa, inner_kgLowPassOp]

/-- The difference of two band compressions is the band compression of the difference. -/
theorem kgBandOp_sub (W₁ W₂ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    (kgBandOp W₁ R - kgBandOp W₂ R) x = kgLowPassOp R ((W₁ - W₂) (kgLowPassOp R x)) := by
  rw [sub_apply, kgBandOp_apply, kgBandOp_apply, sub_apply, map_sub]

/-- **The band compression is admissible for the conditional stability estimate**, on the domain
side. -/
theorem kgBandOp_lowPass_dom (W₁ W₂ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (R : ℝ) (v : Lp ℂ 2 (volume : Measure E)) :
    (kgBandOp W₁ R - kgBandOp W₂ R) (kgLowPassOp R v)
      = (kgBandOp W₁ R - kgBandOp W₂ R) v := by
  rw [kgBandOp_sub, kgBandOp_sub, kgLowPassOp_idem]

/-- **The band compression is admissible for the conditional stability estimate**, on the range
side. -/
theorem kgBandOp_lowPass_ran (W₁ W₂ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (R : ℝ) (v : Lp ℂ 2 (volume : Measure E)) :
    kgLowPassOp R ((kgBandOp W₁ R - kgBandOp W₂ R) v)
      = (kgBandOp W₁ R - kgBandOp W₂ R) v := by
  rw [kgBandOp_sub, kgLowPassOp_idem]

/-! ## The inverse problem on a band -/

/-- **Conditional stability for band-limited perturbations.** The class the estimate was written for
is inhabited by the band compression of *any* bounded operator — in particular of a real potential —
so the inverse problem of this card is well posed on each frequency band. -/
theorem norm_kgBandOp_sub_le {W₁ W₂ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)}
    {b : ℝ} (hb0 : 0 ≤ b) (hW₁ : ‖W₁‖ ≤ b) (hW₂ : ‖W₂‖ ≤ b) {R η T : ℝ}
    (hη0 : 0 ≤ η) (hT0 : 0 < T)
    (hobs : ∀ (f k : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T →
      ‖kgFieldMild (kgBandOp W₁ R) f k t - kgFieldMild (kgBandOp W₂ R) f k t‖
        ≤ η * (‖f‖ + ‖k‖)) :
    ‖kgBandOp W₁ R - kgBandOp W₂ R‖
      ≤ 8 * (η * (1 + b * T))
        * (1 / T ^ 2 + 8 * ((1 + R ^ 2) / 2 + b * Real.exp (b * T))) :=
  norm_sub_le_of_lowPass_explicit hb0 (norm_kgBandOp_le hb0 hW₁ R) (norm_kgBandOp_le hb0 hW₂ R)
    (kgBandOp_lowPass_dom W₁ W₂ R) (kgBandOp_lowPass_ran W₁ W₂ R) hη0 hT0 hobs

/-- **The band compression of a real potential is exactly energy-conserving.** So on each band the
same class of perturbations carries both halves of the theory: the inverse problem is well posed on
it, and the evolution it generates conserves the energy exactly. -/
theorem kgBandOp_real_energy_conserved {V : E → ℝ} {bV : ℝ} (hV : Measurable V) (hbV0 : 0 ≤ bV)
    (hbV : ∀ a : E, |V a| ≤ bV) (R : ℝ) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGrad (kgBandOp (kgMulOp hV hbV0 hbV) R) g h t‖ ^ 2
        + ‖kgFieldVel (kgBandOp (kgMulOp hV hbV0 hbV) R) g h t‖ ^ 2
        - RCLike.re (inner ℂ (kgBandOp (kgMulOp hV hbV0 hbV) R
            (kgFieldMild (kgBandOp (kgMulOp hV hbV0 hbV) R) (kgFreqInvOp g) h t))
          (kgFieldMild (kgBandOp (kgMulOp hV hbV0 hbV) R) (kgFreqInvOp g) h t))
      = ‖g‖ ^ 2 + ‖h‖ ^ 2
        - RCLike.re (inner ℂ (kgBandOp (kgMulOp hV hbV0 hbV) R (kgFreqInvOp g))
            (kgFreqInvOp g)) :=
  kgFieldEnergy_conserved hbV0 (norm_kgBandOp_le hbV0 (norm_kgMulOp_le hV hbV0 hbV) R)
    (inner_kgBandOp (inner_kgMulOp hV hbV0 hbV) R) g h t

end GaloisForLFunctions.HTGeometry
