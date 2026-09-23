import GaloisForLFunctions.HTGeometry.ClockThreeDimensionalScaleLaw
import GaloisForLFunctions.HTGeometry.ClockPotentialAlgebra
import GaloisForLFunctions.HTGeometry.ClockDatumExample

/-!
# A coupled scale function

The two-species law of the previous chapter asks that the effective potential of the scale be of the
admissible class. This file exhibits a scale for which it is:

`σ(ξ, η, w) = ε sin(ξ + η + w)`.

It depends on all three coordinates through their sum, so it is neither a slab scale nor a separable
one, and it is bounded together with all its derivatives — which is what the class asks for.

Its derivative array is small: every first derivative is `ε cos(ξ + η + w)` and every second
derivative is `-ε sin(ξ + η + w)`, so the two differentiability records below carry the whole
two-jet.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

open scoped ContDiff

/-- The coupled scale `ε sin(ξ + η + w)`. -/
noncomputable def coupledScale (ε : ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun s t w => ε * Real.sin (s + t + w)

/-- Its common first derivative. -/
noncomputable def coupledScaleD (ε : ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun s t w => ε * Real.cos (s + t + w)

/-- Its common second derivative. -/
noncomputable def coupledScaleDD (ε : ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun s t w => -(ε * Real.sin (s + t + w))

theorem continuous_coupledScale (ε : ℝ) :
    Continuous fun q : (ℝ × ℝ) × ℝ => coupledScale ε q.1.1 q.1.2 q.2 :=
  continuous_const.mul (Real.continuous_sin.comp
    (((continuous_fst.comp continuous_fst).add (continuous_snd.comp continuous_fst)).add
      continuous_snd))

theorem continuous_coupledScaleD (ε : ℝ) :
    Continuous fun q : (ℝ × ℝ) × ℝ => coupledScaleD ε q.1.1 q.1.2 q.2 :=
  continuous_const.mul (Real.continuous_cos.comp
    (((continuous_fst.comp continuous_fst).add (continuous_snd.comp continuous_fst)).add
      continuous_snd))

theorem continuous_coupledScaleDD (ε : ℝ) :
    Continuous fun q : (ℝ × ℝ) × ℝ => coupledScaleDD ε q.1.1 q.1.2 q.2 :=
  (continuous_const.mul (Real.continuous_sin.comp
    (((continuous_fst.comp continuous_fst).add (continuous_snd.comp continuous_fst)).add
      continuous_snd))).neg

/-- **The coupled scale is continuously differentiable in all three coordinates**, with all three
derivatives equal. -/
theorem isC1On3_coupledScale (ε : ℝ) :
    IsC1On3 (coupledScale ε) (coupledScaleD ε) (coupledScaleD ε) (coupledScaleD ε) univ where
  isOpen := isOpen_univ
  hasDerivFst := fun q _ => by
    have hEq : (fun x : ℝ => coupledScale ε x q.1.2 q.2)
        = fun x : ℝ => ε * Real.sin (x + (q.1.2 + q.2)) := by
      funext x
      rw [coupledScale, add_assoc]
    rw [hEq]
    have h := ((Real.hasDerivAt_sin (q.1.1 + (q.1.2 + q.2))).comp_add_const q.1.1
      (q.1.2 + q.2)).const_mul ε
    have hval : ε * Real.cos (q.1.1 + (q.1.2 + q.2)) = coupledScaleD ε q.1.1 q.1.2 q.2 := by
      rw [coupledScaleD, add_assoc]
    rwa [hval] at h
  hasDerivSnd := fun q _ => by
    have hEq : (fun x : ℝ => coupledScale ε q.1.1 x q.2)
        = fun x : ℝ => ε * Real.sin (x + (q.1.1 + q.2)) := by
      funext x
      rw [coupledScale, show q.1.1 + x + q.2 = x + (q.1.1 + q.2) from by ring]
    rw [hEq]
    have h := ((Real.hasDerivAt_sin (q.1.2 + (q.1.1 + q.2))).comp_add_const q.1.2
      (q.1.1 + q.2)).const_mul ε
    have hval : ε * Real.cos (q.1.2 + (q.1.1 + q.2)) = coupledScaleD ε q.1.1 q.1.2 q.2 := by
      rw [coupledScaleD, show q.1.2 + (q.1.1 + q.2) = q.1.1 + q.1.2 + q.2 from by ring]
    rwa [hval] at h
  hasDerivThd := fun q _ => by
    have hEq : (fun x : ℝ => coupledScale ε q.1.1 q.1.2 x)
        = fun x : ℝ => ε * Real.sin (x + (q.1.1 + q.1.2)) := by
      funext x
      rw [coupledScale, show q.1.1 + q.1.2 + x = x + (q.1.1 + q.1.2) from by ring]
    rw [hEq]
    have h := ((Real.hasDerivAt_sin (q.2 + (q.1.1 + q.1.2))).comp_add_const q.2
      (q.1.1 + q.1.2)).const_mul ε
    have hval : ε * Real.cos (q.2 + (q.1.1 + q.1.2)) = coupledScaleD ε q.1.1 q.1.2 q.2 := by
      rw [coupledScaleD, show q.2 + (q.1.1 + q.1.2) = q.1.1 + q.1.2 + q.2 from by ring]
    rwa [hval] at h
  contFst := continuous_coupledScaleD ε
  contSnd := continuous_coupledScaleD ε
  contThd := continuous_coupledScaleD ε

/-- **The first derivative of the coupled scale is again continuously differentiable**, with all
three derivatives equal. -/
theorem isC1On3_coupledScaleD (ε : ℝ) :
    IsC1On3 (coupledScaleD ε) (coupledScaleDD ε) (coupledScaleDD ε) (coupledScaleDD ε) univ where
  isOpen := isOpen_univ
  hasDerivFst := fun q _ => by
    have hEq : (fun x : ℝ => coupledScaleD ε x q.1.2 q.2)
        = fun x : ℝ => ε * Real.cos (x + (q.1.2 + q.2)) := by
      funext x
      rw [coupledScaleD, add_assoc]
    rw [hEq]
    have h := ((Real.hasDerivAt_cos (q.1.1 + (q.1.2 + q.2))).comp_add_const q.1.1
      (q.1.2 + q.2)).const_mul ε
    have hval : ε * -Real.sin (q.1.1 + (q.1.2 + q.2)) = coupledScaleDD ε q.1.1 q.1.2 q.2 := by
      rw [coupledScaleDD, add_assoc]
      ring
    rwa [hval] at h
  hasDerivSnd := fun q _ => by
    have hEq : (fun x : ℝ => coupledScaleD ε q.1.1 x q.2)
        = fun x : ℝ => ε * Real.cos (x + (q.1.1 + q.2)) := by
      funext x
      rw [coupledScaleD, show q.1.1 + x + q.2 = x + (q.1.1 + q.2) from by ring]
    rw [hEq]
    have h := ((Real.hasDerivAt_cos (q.1.2 + (q.1.1 + q.2))).comp_add_const q.1.2
      (q.1.1 + q.2)).const_mul ε
    have hval : ε * -Real.sin (q.1.2 + (q.1.1 + q.2)) = coupledScaleDD ε q.1.1 q.1.2 q.2 := by
      rw [coupledScaleDD, show q.1.2 + (q.1.1 + q.2) = q.1.1 + q.1.2 + q.2 from by ring]
      ring
    rwa [hval] at h
  hasDerivThd := fun q _ => by
    have hEq : (fun x : ℝ => coupledScaleD ε q.1.1 q.1.2 x)
        = fun x : ℝ => ε * Real.cos (x + (q.1.1 + q.1.2)) := by
      funext x
      rw [coupledScaleD, show q.1.1 + q.1.2 + x = x + (q.1.1 + q.1.2) from by ring]
    rw [hEq]
    have h := ((Real.hasDerivAt_cos (q.2 + (q.1.1 + q.1.2))).comp_add_const q.2
      (q.1.1 + q.1.2)).const_mul ε
    have hval : ε * -Real.sin (q.2 + (q.1.1 + q.1.2)) = coupledScaleDD ε q.1.1 q.1.2 q.2 := by
      rw [coupledScaleDD, show q.2 + (q.1.1 + q.1.2) = q.1.1 + q.1.2 + q.2 from by ring]
      ring
    rwa [hval] at h
  contFst := continuous_coupledScaleDD ε
  contSnd := continuous_coupledScaleDD ε
  contThd := continuous_coupledScaleDD ε

/-- The lift of the coupled scale to Minkowski space is smooth. -/
theorem contDiff_nullTransLift_coupledScale (ε : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (nullTransLift (coupledScale ε) n) := by
  have hlin : ContDiff ℝ ∞ fun x : Fin (n + 3) → ℝ => x 0 + x 1 + (x 0 - x 1) + x 2 :=
    (((contDiff_apply ℝ ℝ 0).add (contDiff_apply ℝ ℝ 1)).add
      ((contDiff_apply ℝ ℝ 0).sub (contDiff_apply ℝ ℝ 1))).add (contDiff_apply ℝ ℝ 2)
  exact contDiff_const.mul (Real.contDiff_sin.comp hlin)

/-! ## The complex side -/

/-- **The sine is bounded on a strip by the hyperbolic cosine of its half-width.** -/
theorem norm_sin_le_cosh {ρ : ℝ} (hρ : 0 ≤ ρ) {z : ℂ} (hz : |z.im| ≤ ρ) :
    ‖Complex.sin z‖ ≤ Real.cosh ρ := by
  have hform : Complex.sin z
      = (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * Complex.I / 2 :=
    Complex.ext rfl rfl
  have h1 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp, Complex.mul_I_re]
  have h2 : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp, Complex.mul_I_re, Complex.neg_im, neg_neg]
  have hstep : ‖Complex.sin z‖ ≤ (Real.exp z.im + Real.exp (-z.im)) / 2 := by
    rw [hform, norm_div, norm_mul, Complex.norm_I, mul_one]
    have hnum : ‖Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)‖
        ≤ Real.exp z.im + Real.exp (-z.im) := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [h1, h2]
    have h2norm : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2norm]
    exact div_le_div_of_nonneg_right hnum (by norm_num)
  have hcosh : (Real.exp z.im + Real.exp (-z.im)) / 2 = Real.cosh z.im := (Real.cosh_eq _).symm
  rw [hcosh] at hstep
  refine hstep.trans (Real.cosh_le_cosh.mpr ?_)
  rwa [abs_of_nonneg hρ]

/-- The complexified scale `ε sin(ξ + η + z)`. -/
noncomputable def coupledSin (ε : ℝ) : ℝ → ℝ → ℂ → ℂ :=
  fun s t z => (ε : ℂ) * Complex.sin ((s : ℂ) + (t : ℂ) + z)

/-- The complexified first derivative `ε cos(ξ + η + z)`. -/
noncomputable def coupledCos (ε : ℝ) : ℝ → ℝ → ℂ → ℂ :=
  fun s t z => (ε : ℂ) * Complex.cos ((s : ℂ) + (t : ℂ) + z)

/-- The complexified effective potential of the coupled scale. -/
noncomputable def coupledPotential (a massSq ε : ℝ) : ℝ → ℝ → ℂ → ℂ :=
  fun s t z => ((massSq : ℝ) : ℂ) * Complex.exp (2 * coupledSin ε s t z)
    - ((3 * a : ℝ) : ℂ) * coupledSin ε s t z
    + ((3 * a ^ (2 : ℕ) : ℝ) : ℂ) * (coupledCos ε s t z * coupledCos ε s t z)

theorem im_add_ofReal_ofReal (s t : ℝ) (z : ℂ) : ((s : ℂ) + (t : ℂ) + z).im = z.im := by
  simp

/-- **The complexified scale is an admissible potential.** -/
theorem boundedC1_coupledSin (ε : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    BoundedC1Potential (coupledSin ε) (fun s t z => (ε : ℂ) * Complex.cos ((s : ℂ) + (t : ℂ) + z))
      (fun s t z => (ε : ℂ) * Complex.cos ((s : ℂ) + (t : ℂ) + z)) ρ (|ε| * Real.cosh ρ) := by
  have hatom : BoundedC1Potential (fun s t z => Complex.sin ((s : ℂ) + (t : ℂ) + z))
      (fun s t z => Complex.cos ((s : ℂ) + (t : ℂ) + z))
      (fun s t z => Complex.cos ((s : ℂ) + (t : ℂ) + z)) ρ (Real.cosh ρ) :=
    BoundedC1Potential.ofSum Complex.hasDerivAt_sin Complex.continuous_cos
      (Real.cosh_pos ρ).le (fun s t z hz => norm_sin_le_cosh hρ
        (by rw [im_add_ofReal_ofReal]; exact le_of_lt (mem_imStrip.mp hz)))
  have hconst := BoundedC1Potential.const ((ε : ℝ) : ℂ) ρ
  have hmul := hconst.mul hatom
  have hnorm : ‖((ε : ℝ) : ℂ)‖ = |ε| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm] at hmul
  exact hmul.congr_deriv (by funext s t z; ring) (by funext s t z; ring)

/-- **The complexified first derivative is an admissible potential.** -/
theorem boundedC1_coupledCos (ε : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    BoundedC1Potential (coupledCos ε)
      (fun s t z => (ε : ℂ) * -Complex.sin ((s : ℂ) + (t : ℂ) + z))
      (fun s t z => (ε : ℂ) * -Complex.sin ((s : ℂ) + (t : ℂ) + z)) ρ (|ε| * Real.cosh ρ) := by
  have hatom : BoundedC1Potential (fun s t z => Complex.cos ((s : ℂ) + (t : ℂ) + z))
      (fun s t z => -Complex.sin ((s : ℂ) + (t : ℂ) + z))
      (fun s t z => -Complex.sin ((s : ℂ) + (t : ℂ) + z)) ρ (Real.cosh ρ) :=
    BoundedC1Potential.ofSum Complex.hasDerivAt_cos Complex.continuous_sin.neg
      (Real.cosh_pos ρ).le (fun s t z hz => norm_cos_le_cosh hρ
        (by rw [im_add_ofReal_ofReal]; exact le_of_lt (mem_imStrip.mp hz)))
  have hconst := BoundedC1Potential.const ((ε : ℝ) : ℂ) ρ
  have hmul := hconst.mul hatom
  have hnorm : ‖((ε : ℝ) : ℂ)‖ = |ε| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm] at hmul
  exact hmul.congr_deriv (by funext s t z; ring) (by funext s t z; ring)

/-- **The effective potential of the coupled scale is admissible.** -/
theorem exists_boundedC1_coupledPotential (a massSq ε : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ (Vs Vt : ℝ → ℝ → ℂ → ℂ) (Mv : ℝ),
      BoundedC1Potential (coupledPotential a massSq ε) Vs Vt ρ Mv := by
  have hSin := boundedC1_coupledSin ε hρ
  have hCos := boundedC1_coupledCos ε hρ
  have hExp := hSin.cexp_two
  have hT1 := (BoundedC1Potential.const ((massSq : ℝ) : ℂ) ρ).mul hExp
  have hT2 := (BoundedC1Potential.const ((3 * a : ℝ) : ℂ) ρ).mul hSin
  have hT3 := (BoundedC1Potential.const ((3 * a ^ (2 : ℕ) : ℝ) : ℂ) ρ).mul (hCos.mul hCos)
  exact ⟨_, _, _, (hT1.sub hT2).add hT3⟩

/-- **The effective potential of the coupled scale is a real quantity on the real axis**, and its
value is the effective potential of the real scale. -/
theorem coupledPotential_ofReal (a massSq ε : ℝ) (s t w : ℝ) :
    coupledPotential a massSq ε s t ((w : ℝ) : ℂ)
      = ((massSq * Real.exp (2 * (ε * Real.sin (s + t + w)))
          - 3 * a * (ε * Real.sin (s + t + w))
          + 3 * a ^ (2 : ℕ) * (ε * Real.cos (s + t + w) * (ε * Real.cos (s + t + w))) : ℝ) : ℂ) := by
  have hz : ((s : ℂ) + (t : ℂ) + ((w : ℝ) : ℂ)) = ((s + t + w : ℝ) : ℂ) := by
    push_cast
    ring
  rw [coupledPotential, coupledSin, coupledCos, hz, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
  push_cast
  ring

theorem realOnAxis_coupledPotential (a massSq ε : ℝ) :
    RealOnAxis (coupledPotential a massSq ε) := by
  intro s t w
  rw [coupledPotential_ofReal, Complex.ofReal_im]

/-- **The effective potential of the coupled scale, computed from the scale's derivatives, is the
real part of the complexified potential.** -/
theorem conformalPotentialTri_coupledScale (a massSq ε : ℝ) :
    conformalPotentialTri a massSq (coupledScale ε) (coupledScaleD ε) (coupledScaleD ε)
        (coupledScaleD ε) (coupledScaleDD ε) (coupledScaleDD ε) (coupledScaleDD ε)
      = fun s t w => (coupledPotential a massSq ε s t ((w : ℝ) : ℂ)).re := by
  funext s t w
  rw [coupledPotential_ofReal, Complex.ofReal_re, conformalPotentialTri, coupledScale,
    coupledScaleD, coupledScaleDD]
  ring

/-! ## The scale law for the coupled scale -/

/-- An admissible potential carries a clock datum, once the radii and the rectangle are chosen. -/
theorem clockDatum_of_boundedC1 {V Vs Vt : ℝ → ℝ → ℂ → ℂ} {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ}
    (hV : BoundedC1Potential V Vs Vt ρ₀ Mv) (hρ₀ : 0 < ρ₀) (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀)
    (hT : 0 ≤ T) (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁)
    (hρ₃0 : 0 < ρ₃) (hρ₃ : ρ₃ < ρ₂) :
    ClockDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T where
  pos := hρ₀
  potC1 := hV.potC1
  massNonneg := hV.boundNonneg
  mass := fun s t _ _ z hz => hV.bound s t z hz
  radNonneg := hρ0
  rad := hρ
  sideNonneg := hT
  small := hsmall
  rad₁Nonneg := hρ₁0
  rad₁ := hρ₁
  rad₂Nonneg := hρ₂0
  rad₂ := hρ₂
  rad₃Pos := hρ₃0
  rad₃ := hρ₃

/-- **The two-species scale law for an explicit coupled scale, in every dimension at least three.**

For the scale `σ(ξ,η,w) = ε sin(ξ + η + w)` — which depends on all three coordinates through their
sum, so it is neither a slab scale nor a separable one — two species of the same conjugation weight
and different calibrated masses return the conformal scale of the spacetime. No hypothesis is left
on the potential: its admissibility is proved, not assumed. -/
theorem twoSpecies_scale_reconstruction_coupledScale (n : ℕ) (a ε : ℝ) {massSq : ℝ}
    (hmassSq : massSq ≠ 0) {other₁ other₂ : (Fin (n + 3) → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin (n + 3) → ℝ) → ℝ) (W : Set (Fin (n + 3) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
            (slabEps_ne_zero (n + 1))).chart.dalembert
          ((SmoothPseudoMetric.ofSignature (slabEps (n + 1))
            (slabEps_ne_zero (n + 1))).chart.conformalPotential a massSq
              (nullTransLift (coupledScale ε) n)) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
            (slabEps_ne_zero (n + 1))).chart.dalembert other₁ u W)
    (h₂ : ∀ (u : (Fin (n + 3) → ℝ) → ℝ) (W : Set (Fin (n + 3) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
            (slabEps_ne_zero (n + 1))).chart.dalembert
          ((SmoothPseudoMetric.ofSignature (slabEps (n + 1))
            (slabEps_ne_zero (n + 1))).chart.conformalPotential a 0
              (nullTransLift (coupledScale ε) n)) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
            (slabEps_ne_zero (n + 1))).chart.dalembert other₂ u W)
    (x : Fin (n + 3) → ℝ) :
    (other₁ x - other₂ x) / massSq = Real.exp (2 * nullTransLift (coupledScale ε) n x) := by
  obtain ⟨Vs, Vt, Mv, hV⟩ := exists_boundedC1_coupledPotential a massSq ε zero_le_one
  have hMv0 : 0 ≤ Mv := hV.boundNonneg
  obtain ⟨T, hTpos, hsmall⟩ := exists_small_side
    (A := 4 + Mv * (1 : ℝ) ^ (2 : ℕ) / 4) (B := ((1 : ℝ) - 1 / 2) / 2) (by positivity) (by norm_num)
  have hD := clockDatum_of_boundedC1 (ρ := (1 : ℝ) / 2) (ρ₁ := (1 : ℝ) / 4)
    (ρ₂ := (1 : ℝ) / 8) (ρ₃ := (1 : ℝ) / 16) hV one_pos (by norm_num) (by norm_num)
    hTpos.le hsmall (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  exact hD.twoSpecies_scale_reconstruction_of_scale (realOnAxis_coupledPotential a massSq ε)
    (fun s t z hz => hV.bound s t z hz) hTpos n a hmassSq (isC1On3_coupledScale ε)
    (isC1On3_coupledScaleD ε) (isC1On3_coupledScaleD ε) (isC1On3_coupledScaleD ε)
    (contDiff_nullTransLift_coupledScale ε n) (conformalPotentialTri_coupledScale a massSq ε)
    h₁ h₂ x

end GaloisForLFunctions.HTGeometry
