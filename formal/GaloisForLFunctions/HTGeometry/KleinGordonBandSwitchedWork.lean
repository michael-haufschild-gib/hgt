import GaloisForLFunctions.HTGeometry.KleinGordonTimeBandGradient

/-!
# The classical work–energy balance on a band

The adiabatic layer proves the work–energy identity for an abstract self-adjoint moving background.
This file makes every term of it a quantity of the field itself, in the register the clock programme
uses: a real potential of varying strength, compressed to a band.

Compression is linear in the operator, so the compression of `φ(t)V` is the switched compression
`φ(t)·P_RVP_R`, and that operator is self-adjoint and norm-differentiable for the same reasons as the
uncompressed one. The gradient on a band is `⟨D⟩_R u` (statement 283) and the potential term is an
honest integral, because `P_R u = u` along the solution. The identity of statement 202 therefore reads

`[‖⟨D⟩_R u(t)‖² + ‖∂ₜu(t)‖² − φ(t)∫V|u(t)|²] − [same at 0] = −∫₀ᵗ φ'(s)∫V|u(s)|² ds`:

the energy of the field changes exactly by the work the switching does on it.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section BandSwitched

variable {V : E → ℝ} {φ φ' : ℝ → ℝ} {bV : ℝ}

/-- **A real potential of varying strength, compressed to a band.** -/
def kgBandSwitchedPotential (hV : Measurable V) (hbV0 : 0 ≤ bV) (hbV : ∀ a : E, |V a| ≤ bV)
    (φ : ℝ → ℝ) (R : ℝ) :
    ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) :=
  kgScaledPotential (kgBandOp (kgMulOp hV hbV0 hbV) R) φ

/-- Compressing a switched real potential is switching the compressed one. -/
theorem kgBandSwitchedPotential_eq (hV : Measurable V) (hbV0 : 0 ≤ bV)
    (hbV : ∀ a : E, |V a| ≤ bV) (φ : ℝ → ℝ) (R : ℝ) :
    kgBandSwitchedPotential hV hbV0 hbV φ R
      = kgBandOpT (kgSwitchedPotential hV hbV0 hbV φ) R :=
  (kgBandOpT_kgScaledPotential _ φ R).symm

theorem norm_kgBandSwitchedPotential_le (hV : Measurable V) (hbV0 : 0 ≤ bV)
    (hbV : ∀ a : E, |V a| ≤ bV) (R r : ℝ) :
    ‖kgBandSwitchedPotential hV hbV0 hbV φ R r‖ ≤ |φ r| * bV := by
  rw [kgBandSwitchedPotential, norm_kgScaledPotential]
  exact mul_le_mul_of_nonneg_left (norm_kgBandOp_le hbV0 (norm_kgMulOp_le hV hbV0 hbV) R)
    (abs_nonneg _)

theorem inner_kgBandSwitchedPotential (hV : Measurable V) (hbV0 : 0 ≤ bV)
    (hbV : ∀ a : E, |V a| ≤ bV) (R r : ℝ) (u w : Lp ℂ 2 (volume : Measure E)) :
    (inner ℂ (kgBandSwitchedPotential hV hbV0 hbV φ R r u) w : ℂ)
      = inner ℂ u (kgBandSwitchedPotential hV hbV0 hbV φ R r w) :=
  inner_kgScaledPotential (inner_kgBandOp (inner_kgMulOp hV hbV0 hbV) R) r u w

theorem hasDerivAt_kgBandSwitchedPotential (hV : Measurable V) (hbV0 : 0 ≤ bV)
    (hbV : ∀ a : E, |V a| ≤ bV) (hφ : ∀ r : ℝ, HasDerivAt φ (φ' r) r) (R t : ℝ) :
    HasDerivAt (kgBandSwitchedPotential hV hbV0 hbV φ R)
      (kgBandSwitchedPotential hV hbV0 hbV φ' R t) t :=
  hasDerivAt_kgScaledPotential hφ t

theorem continuous_kgBandSwitchedPotential_apply (hV : Measurable V) (hbV0 : 0 ≤ bV)
    (hbV : ∀ a : E, |V a| ≤ bV) (hφc : Continuous φ) (R : ℝ)
    (w : Lp ℂ 2 (volume : Measure E)) :
    Continuous fun r : ℝ => kgBandSwitchedPotential hV hbV0 hbV φ R r w :=
  continuous_kgScaledPotential_apply hφc w

/-- **The potential term of a band-compressed real potential** is the potential energy of the
band-limited part of the field. -/
theorem re_inner_kgBandOp_kgMulOp (hV : Measurable V) (hbV0 : 0 ≤ bV)
    (hbV : ∀ a : E, |V a| ≤ bV) (R : ℝ) (u : Lp ℂ 2 (volume : Measure E)) :
    RCLike.re (inner ℂ (kgBandOp (kgMulOp hV hbV0 hbV) R u) u)
      = RCLike.re ((∫ a : E,
          ((V a * ‖(kgLowPassOp R u : E → ℂ) a‖ ^ 2 : ℝ) : ℂ)) : ℂ) := by
  rw [kgBandOp_apply, inner_kgLowPassOp]
  exact re_inner_kgMulOp hV hbV0 hbV (kgLowPassOp R u)

/-- **The work density of a band-compressed switched potential.** -/
theorem re_inner_kgBandSwitchedPotential (hV : Measurable V) (hbV0 : 0 ≤ bV)
    (hbV : ∀ a : E, |V a| ≤ bV) (R s : ℝ) (u : Lp ℂ 2 (volume : Measure E)) :
    RCLike.re (inner ℂ (kgBandSwitchedPotential hV hbV0 hbV φ R s u) u)
      = φ s * RCLike.re ((∫ a : E,
          ((V a * ‖(kgLowPassOp R u : E → ℂ) a‖ ^ 2 : ℝ) : ℂ)) : ℂ) := by
  rw [kgBandSwitchedPotential, re_inner_kgScaledPotential,
    re_inner_kgBandOp_kgMulOp hV hbV0 hbV R u]

end BandSwitched

/-! ## The energy in concrete terms -/

section BandSwitchedEnergy

variable {V : E → ℝ} {φ φ' : ℝ → ℝ} {bV b L : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The adiabatic energy on a band, with every term a quantity of the field.** -/
theorem kgBandSwitched_energy_eq (hV : Measurable V) (hbV0 : 0 ≤ bV)
    (hbV : ∀ a : E, |V a| ≤ bV) (hφc : Continuous φ) (hb0 : 0 ≤ b)
    (hφb : ∀ r : ℝ, |φ r| * bV ≤ b) (R : ℝ) (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgAdiabaticEnergy (kgBandSwitchedPotential hV hbV0 hbV φ R) (kgFreqLowOp R x)
        (kgLowPassOp R y) t
      = ‖kgFreqLowOp R (kgFieldMildT (kgBandSwitchedPotential hV hbV0 hbV φ R)
            (kgLowPassOp R x) (kgLowPassOp R y) t)‖ ^ 2
        + ‖kgFieldVelT (kgBandSwitchedPotential hV hbV0 hbV φ R) (kgFreqLowOp R x)
            (kgLowPassOp R y) t‖ ^ 2
        - φ t * RCLike.re ((∫ a : E, ((V a
            * ‖(kgFieldMildT (kgBandSwitchedPotential hV hbV0 hbV φ R) (kgLowPassOp R x)
                (kgLowPassOp R y) t : E → ℂ) a‖ ^ 2 : ℝ) : ℂ)) : ℂ) := by
  set W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) :=
    kgSwitchedPotential hV hbV0 hbV φ with hWdef
  have hWb : ∀ r : ℝ, ‖W r‖ ≤ b := fun r =>
    le_trans (norm_kgSwitchedPotential_le hV hbV0 hbV r) (hφb r)
  have hWs : ∀ w : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r w := fun w =>
    continuous_kgScaledPotential_apply hφc w
  have hbridge : kgBandSwitchedPotential hV hbV0 hbV φ R = kgBandOpT W R :=
    kgBandSwitchedPotential_eq hV hbV0 hbV φ R
  have hdatum : kgFreqInvOp (kgFreqLowOp (E := E) R x) = kgLowPassOp R x :=
    kgFreqInvOp_kgFreqLowOp R x
  have hgrad : kgFieldGradT (kgBandSwitchedPotential hV hbV0 hbV φ R) (kgFreqLowOp R x)
        (kgLowPassOp R y) t
      = kgFreqLowOp R (kgFieldMildT (kgBandSwitchedPotential hV hbV0 hbV φ R)
          (kgLowPassOp R x) (kgLowPassOp R y) t) := by
    rw [hbridge, ← hdatum]
    exact kgFieldGradT_band hb0 hWb hWs R x y t
  have hband : kgLowPassOp R (kgFieldMildT (kgBandSwitchedPotential hV hbV0 hbV φ R)
        (kgLowPassOp R x) (kgLowPassOp R y) t)
      = kgFieldMildT (kgBandSwitchedPotential hV hbV0 hbV φ R) (kgLowPassOp R x)
          (kgLowPassOp R y) t := by
    rw [hbridge]
    exact kgBandOpT_lowPass_invariant hb0 hWb hWs R x y t
  rw [kgAdiabaticEnergy, ← kgFieldEnergyT_eq_norm_sq, hdatum, hgrad,
    re_inner_kgBandSwitchedPotential hV hbV0 hbV R t _, hband]

set_option maxHeartbeats 1000000 in
/-- **The classical work–energy balance on a band.** The energy of the field changes exactly by the
work the switching does on it, with every term an integral of the solution. -/
theorem kgBandSwitched_work (hV : Measurable V) (hbV0 : 0 ≤ bV) (hbV : ∀ a : E, |V a| ≤ bV)
    (hφ : ∀ r : ℝ, HasDerivAt φ (φ' r) r) (hφ'c : Continuous φ') (hb0 : 0 ≤ b)
    (hφb : ∀ r : ℝ, |φ r| * bV ≤ b) (hφL : ∀ r : ℝ, |φ' r| * bV ≤ L)
    (R : ℝ) (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgAdiabaticEnergy (kgBandSwitchedPotential hV hbV0 hbV φ R) (kgFreqLowOp R x)
          (kgLowPassOp R y) t
        - kgAdiabaticEnergy (kgBandSwitchedPotential hV hbV0 hbV φ R) (kgFreqLowOp R x)
          (kgLowPassOp R y) 0
      = -∫ s in (0 : ℝ)..t, φ' s * RCLike.re ((∫ a : E, ((V a
          * ‖(kgFieldMildT (kgBandSwitchedPotential hV hbV0 hbV φ R) (kgLowPassOp R x)
              (kgLowPassOp R y) s : E → ℂ) a‖ ^ 2 : ℝ) : ℂ)) : ℂ) := by
  have hφd : Differentiable ℝ φ := fun r => (hφ r).differentiableAt
  have hφc : Continuous φ := hφd.continuous
  set W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) :=
    kgSwitchedPotential hV hbV0 hbV φ with hWdef
  have hWb : ∀ r : ℝ, ‖W r‖ ≤ b := fun r =>
    le_trans (norm_kgSwitchedPotential_le hV hbV0 hbV r) (hφb r)
  have hWs : ∀ w : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r w := fun w =>
    continuous_kgScaledPotential_apply hφc w
  have hbridge : kgBandSwitchedPotential hV hbV0 hbV φ R = kgBandOpT W R :=
    kgBandSwitchedPotential_eq hV hbV0 hbV φ R
  have hdatum : kgFreqInvOp (kgFreqLowOp (E := E) R x) = kgLowPassOp R x :=
    kgFreqInvOp_kgFreqLowOp R x
  have hBb : ∀ r : ℝ, ‖kgBandSwitchedPotential hV hbV0 hbV φ R r‖ ≤ b := fun r =>
    le_trans (norm_kgBandSwitchedPotential_le hV hbV0 hbV R r) (hφb r)
  have hBs : ∀ w : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => kgBandSwitchedPotential hV hbV0 hbV φ R r w := fun w =>
    continuous_kgBandSwitchedPotential_apply hV hbV0 hbV hφc R w
  have hBL : ∀ r : ℝ, ‖kgBandSwitchedPotential hV hbV0 hbV φ' R r‖ ≤ L := fun r =>
    le_trans (norm_kgBandSwitchedPotential_le hV hbV0 hbV R r) (hφL r)
  have hBds : ∀ w : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => kgBandSwitchedPotential hV hbV0 hbV φ' R r w := fun w =>
    continuous_kgBandSwitchedPotential_apply hV hbV0 hbV hφ'c R w
  have hkey := kgAdiabaticEnergy_sub hb0 hBb hBs
    (fun r => inner_kgBandSwitchedPotential hV hbV0 hbV R r)
    (fun r => hasDerivAt_kgBandSwitchedPotential hV hbV0 hbV hφ R r) hBL hBds
    (kgFreqLowOp R x) (kgLowPassOp R y) t
  rw [hkey, hdatum]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  have hband : kgLowPassOp R (kgFieldMildT (kgBandSwitchedPotential hV hbV0 hbV φ R)
        (kgLowPassOp R x) (kgLowPassOp R y) s)
      = kgFieldMildT (kgBandSwitchedPotential hV hbV0 hbV φ R) (kgLowPassOp R x)
          (kgLowPassOp R y) s := by
    rw [hbridge]
    exact kgBandOpT_lowPass_invariant hb0 hWb hWs R x y s
  rw [re_inner_kgBandSwitchedPotential hV hbV0 hbV R s _, hband]

/-- **The adiabatic estimate on a band.** The energy of the band field grows at most at the rate at
which the potential is switched. -/
theorem kgBandSwitched_energy_le (hV : Measurable V) (hbV0 : 0 ≤ bV)
    (hbV : ∀ a : E, |V a| ≤ bV) (hφ : ∀ r : ℝ, HasDerivAt φ (φ' r) r)
    (hb0 : 0 ≤ b) (hb1 : b < 1) (hφb : ∀ r : ℝ, |φ r| * bV ≤ b)
    (hL0 : 0 ≤ L) (hφL : ∀ r : ℝ, |φ' r| * bV ≤ L) (R : ℝ)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgAdiabaticEnergy (kgBandSwitchedPotential hV hbV0 hbV φ R) g h t
      ≤ kgAdiabaticEnergy (kgBandSwitchedPotential hV hbV0 hbV φ R) g h 0
        * Real.exp (L / (1 - b) * |t|) := by
  have hW0 : ‖kgBandOp (kgMulOp hV hbV0 hbV) R‖ ≤ bV :=
    norm_kgBandOp_le hbV0 (norm_kgMulOp_le hV hbV0 hbV) R
  have hφb' : ∀ r : ℝ, |φ r| * ‖kgBandOp (kgMulOp hV hbV0 hbV) R‖ ≤ b := fun r =>
    le_trans (mul_le_mul_of_nonneg_left hW0 (abs_nonneg _)) (hφb r)
  have hφL' : ∀ r : ℝ, |φ' r| * ‖kgBandOp (kgMulOp hV hbV0 hbV) R‖ ≤ L := fun r =>
    le_trans (mul_le_mul_of_nonneg_left hW0 (abs_nonneg _)) (hφL r)
  exact kgScaledPotential_energy_le (inner_kgBandOp (inner_kgMulOp hV hbV0 hbV) R) hφ hb0 hb1
    hφb' hL0 hφL' g h t

end BandSwitchedEnergy

end GaloisForLFunctions.HTGeometry
