import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonAdiabaticWork

/-!
# A real potential of varying strength

The last abstraction. Statements 193–196 gave a concrete self-adjoint perturbation — multiplication by
a bounded real function of position — and 203–204 gave a concrete way of moving one — switching it on
and off by a scalar profile. Composing them leaves a statement with no abstract hypotheses at all:

`∂ₜ²u = -⟨D⟩²u + φ(t)V(x)u`,

a real potential whose strength varies in time. Its work density is `φ̇(t)·∫V|u|²`, its energy obeys the
exact accounting, and it satisfies the adiabatic estimate with constants read off from `φ`, `φ̇` and the
sup-norm of `V`.

This is the equation a clock in a background of varying strength actually solves, and everything the
card proves about it is now stated in terms of the three quantities an experiment can bound.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Switched

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {φ φ' : ℝ → ℝ}

/-- The potential term of a switched background is the profile times the fixed one. -/
theorem re_inner_kgScaledPotential (s : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    RCLike.re (inner ℂ (kgScaledPotential W₀ φ s x) x)
      = φ s * RCLike.re (inner ℂ (W₀ x) x) := by
  show RCLike.re (inner ℂ (((φ s : ℝ) : ℂ) • W₀ x) x) = _
  rw [inner_smul_left, Complex.conj_ofReal]
  simp

end Switched

/-! ## The switched real potential -/

section SwitchedReal

variable {V : E → ℝ} {φ φ' : ℝ → ℝ} {bV : ℝ}

/-- **A real potential of varying strength**, as a moving background. -/
def kgSwitchedPotential (hV : Measurable V) (hbV0 : 0 ≤ bV) (hbV : ∀ a : E, |V a| ≤ bV)
    (φ : ℝ → ℝ) : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) :=
  kgScaledPotential (kgMulOp hV hbV0 hbV) φ

theorem norm_kgSwitchedPotential_le (hV : Measurable V) (hbV0 : 0 ≤ bV)
    (hbV : ∀ a : E, |V a| ≤ bV) (r : ℝ) :
    ‖kgSwitchedPotential hV hbV0 hbV φ r‖ ≤ |φ r| * bV := by
  rw [kgSwitchedPotential, norm_kgScaledPotential]
  exact mul_le_mul_of_nonneg_left (norm_kgMulOp_le hV hbV0 hbV) (abs_nonneg _)

theorem inner_kgSwitchedPotential (hV : Measurable V) (hbV0 : 0 ≤ bV)
    (hbV : ∀ a : E, |V a| ≤ bV) (r : ℝ) (x y : Lp ℂ 2 (volume : Measure E)) :
    (inner ℂ (kgSwitchedPotential hV hbV0 hbV φ r x) y : ℂ)
      = inner ℂ x (kgSwitchedPotential hV hbV0 hbV φ r y) :=
  inner_kgScaledPotential (inner_kgMulOp hV hbV0 hbV) r x y

theorem hasDerivAt_kgSwitchedPotential (hV : Measurable V) (hbV0 : 0 ≤ bV)
    (hbV : ∀ a : E, |V a| ≤ bV) (hφ : ∀ r : ℝ, HasDerivAt φ (φ' r) r) (t : ℝ) :
    HasDerivAt (kgSwitchedPotential hV hbV0 hbV φ)
      (kgSwitchedPotential hV hbV0 hbV φ' t) t :=
  hasDerivAt_kgScaledPotential hφ t

/-- **The work density of a switched real potential** is the rate of switching times the potential
energy of the field. -/
theorem re_inner_kgSwitchedPotential (hV : Measurable V) (hbV0 : 0 ≤ bV)
    (hbV : ∀ a : E, |V a| ≤ bV) (s : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    RCLike.re (inner ℂ (kgSwitchedPotential hV hbV0 hbV φ s x) x)
      = φ s * RCLike.re ((∫ a : E, ((V a * ‖(x : E → ℂ) a‖ ^ (2 : ℕ) : ℝ) : ℂ)) : ℂ) := by
  rw [kgSwitchedPotential, re_inner_kgScaledPotential, re_inner_kgMulOp hV hbV0 hbV x]

/-- **The adiabatic estimate for a real potential of varying strength.** Every constant is read off
from the profile, its derivative, and the sup-norm of the potential. -/
theorem kgSwitchedPotential_energy_le (hV : Measurable V) (hbV0 : 0 ≤ bV)
    (hbV : ∀ a : E, |V a| ≤ bV) (hφ : ∀ r : ℝ, HasDerivAt φ (φ' r) r)
    {b L : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (hφb : ∀ r : ℝ, |φ r| * bV ≤ b)
    (hL0 : 0 ≤ L) (hφL : ∀ r : ℝ, |φ' r| * bV ≤ L)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgAdiabaticEnergy (kgSwitchedPotential hV hbV0 hbV φ) g h t
      ≤ kgAdiabaticEnergy (kgSwitchedPotential hV hbV0 hbV φ) g h 0
        * Real.exp (L / (1 - b) * |t|) := by
  have hW0 : ‖kgMulOp hV hbV0 hbV‖ ≤ bV := norm_kgMulOp_le hV hbV0 hbV
  have hφb' : ∀ r : ℝ, |φ r| * ‖kgMulOp hV hbV0 hbV‖ ≤ b := fun r =>
    le_trans (mul_le_mul_of_nonneg_left hW0 (abs_nonneg _)) (hφb r)
  have hφL' : ∀ r : ℝ, |φ' r| * ‖kgMulOp hV hbV0 hbV‖ ≤ L := fun r =>
    le_trans (mul_le_mul_of_nonneg_left hW0 (abs_nonneg _)) (hφL r)
  exact kgScaledPotential_energy_le (inner_kgMulOp hV hbV0 hbV) hφ hb0 hb1 hφb' hL0 hφL' g h t

/-- **The exact work accounting for a real potential of varying strength.** -/
theorem kgSwitchedPotential_work (hV : Measurable V) (hbV0 : 0 ≤ bV)
    (hbV : ∀ a : E, |V a| ≤ bV) (hφ : ∀ r : ℝ, HasDerivAt φ (φ' r) r) (hφ'c : Continuous φ')
    {b L : ℝ} (hb0 : 0 ≤ b) (hφb : ∀ r : ℝ, |φ r| * bV ≤ b)
    (hφL : ∀ r : ℝ, |φ' r| * bV ≤ L)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgAdiabaticEnergy (kgSwitchedPotential hV hbV0 hbV φ) g h t
        - kgAdiabaticEnergy (kgSwitchedPotential hV hbV0 hbV φ) g h 0
      = -∫ s in (0 : ℝ)..t, φ' s * RCLike.re ((∫ a : E,
          ((V a * ‖(kgFieldMildT (kgSwitchedPotential hV hbV0 hbV φ) (kgFreqInvOp g) h s :
            E → ℂ) a‖ ^ (2 : ℕ) : ℝ) : ℂ)) : ℂ) := by
  have hφb' : ∀ r : ℝ, ‖kgSwitchedPotential hV hbV0 hbV φ r‖ ≤ b := fun r =>
    le_trans (norm_kgSwitchedPotential_le hV hbV0 hbV r) (hφb r)
  have hφL' : ∀ r : ℝ, ‖kgSwitchedPotential hV hbV0 hbV φ' r‖ ≤ L := fun r =>
    le_trans (norm_kgSwitchedPotential_le hV hbV0 hbV r) (hφL r)
  have hφd : Differentiable ℝ φ := fun r => (hφ r).differentiableAt
  have hWs : ∀ y : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => kgSwitchedPotential hV hbV0 hbV φ r y := fun y =>
    continuous_kgScaledPotential_apply hφd.continuous y
  have hWds : ∀ y : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => kgSwitchedPotential hV hbV0 hbV φ' r y := fun y =>
    continuous_kgScaledPotential_apply hφ'c y
  have hmain := kgAdiabaticEnergy_sub hb0 hφb' hWs
    (fun r x y => inner_kgSwitchedPotential hV hbV0 hbV r x y)
    (fun r => hasDerivAt_kgSwitchedPotential hV hbV0 hbV hφ r) hφL' hWds g h t
  rw [hmain]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  exact re_inner_kgSwitchedPotential hV hbV0 hbV s _

end SwitchedReal

end GaloisForLFunctions.HTGeometry
