/-
# Böttcher tower — Tier 2a: logarithmic potential theory foundations

Mathlib has no logarithmic capacity / equilibrium measure / energy, so the
capacity-separation core of q62 (`q62-bottcher-independence-natural-boundary.md`
Step 1, used in all three cases) must be built from the measure/integral layer up.

This file fixes the definitions:
  * the logarithmic kernel  k(x,y) = -log‖x-y‖ = log(1/‖x-y‖)
  * the logarithmic potential  Uᵘ(z) = ∫ k(z,ζ) dμ(ζ)
  * the logarithmic energy  I(μ) = ∬ k(x,y) dμ(x) dμ(y) = ∫ Uᵘ dμ

Conventions match the card: energy is the `log(1/·)` (Frostman) sign, so the
equilibrium measure *minimises* `I`, and capacity = exp(-inf I).

Definitions only here (Tier 2a); the energy-variation and strong-minimum-principle
lemmas come in later Tier-2 files.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic

open MeasureTheory

namespace Bottcher

/-- The logarithmic kernel `k(x,y) = -log‖x-y‖ = log(1/‖x-y‖)` on `ℂ`.
With this (Frostman) sign the equilibrium measure minimises energy. -/
noncomputable def logKernel (x y : ℂ) : ℝ := - Real.log ‖x - y‖

/-- The logarithmic potential `Uᵘ(z) = ∫ k(z,ζ) dμ(ζ)` of a measure `μ` on `ℂ`. -/
noncomputable def logPotential (μ : Measure ℂ) (z : ℂ) : ℝ :=
  ∫ ζ, logKernel z ζ ∂μ

/-- The logarithmic energy `I(μ) = ∬ k(x,y) dμ(x) dμ(y) = ∫ Uᵘ dμ`. -/
noncomputable def logEnergy (μ : Measure ℂ) : ℝ :=
  ∫ z, logPotential μ z ∂μ

/-- Symmetry of the kernel: `k(x,y) = k(y,x)`. -/
theorem logKernel_symm (x y : ℂ) : logKernel x y = logKernel y x := by
  unfold logKernel
  rw [show x - y = -(y - x) by ring, norm_neg]

/-- The mutual logarithmic energy `J(μ,ν) = ∬ k(x,y) dμ(x) dν(y) = ∫ Uᵛ dμ`.
With this, `logEnergy μ = logEnergyPair μ μ` and the convex-combination expansion
`I((1-t)μ+tν) = (1-t)²I(μ) + 2t(1-t)J(μ,ν) + t²I(ν)` is the heart of the
capacity strict-gain (Tier 2c). -/
noncomputable def logEnergyPair (μ ν : Measure ℂ) : ℝ :=
  ∫ z, logPotential ν z ∂μ

/-- The diagonal of the mutual energy is the energy. -/
theorem logEnergyPair_self (μ : Measure ℂ) : logEnergyPair μ μ = logEnergy μ := rfl

/-- The logarithmic potential is homogeneous in the measure: `U^(c•μ) = c·Uᵘ`. -/
theorem logPotential_smul (μ : Measure ℂ) (c : ENNReal) (z : ℂ) :
    logPotential (c • μ) z = c.toReal * logPotential μ z := by
  unfold logPotential
  rw [integral_smul_measure, smul_eq_mul]

/-- The logarithmic potential is additive in the measure, given finite-energy
integrability at `z`: `U^(μ+ν) = Uᵘ + Uᵛ`. -/
theorem logPotential_add (μ ν : Measure ℂ) (z : ℂ)
    (hμ : Integrable (fun ζ => logKernel z ζ) μ)
    (hν : Integrable (fun ζ => logKernel z ζ) ν) :
    logPotential (μ + ν) z = logPotential μ z + logPotential ν z := by
  unfold logPotential
  exact integral_add_measure hμ hν

/-- Mutual energy scales in the outer measure: `J(c•μ, ν) = c·J(μ,ν)`. -/
theorem logEnergyPair_smul_left (μ ν : Measure ℂ) (c : ENNReal) :
    logEnergyPair (c • μ) ν = c.toReal * logEnergyPair μ ν := by
  unfold logEnergyPair
  rw [integral_smul_measure, smul_eq_mul]

/-- Mutual energy scales in the inner measure: `J(μ, c•ν) = c·J(μ,ν)`. -/
theorem logEnergyPair_smul_right (μ ν : Measure ℂ) (c : ENNReal) :
    logEnergyPair μ (c • ν) = c.toReal * logEnergyPair μ ν := by
  unfold logEnergyPair
  simp_rw [logPotential_smul]
  rw [integral_const_mul]

/-- Mutual energy is additive in the outer measure (given the potential of `ν` is
integrable against each piece). -/
theorem logEnergyPair_add_left (μ μ' ν : Measure ℂ)
    (hμ : Integrable (fun z => logPotential ν z) μ)
    (hμ' : Integrable (fun z => logPotential ν z) μ') :
    logEnergyPair (μ + μ') ν = logEnergyPair μ ν + logEnergyPair μ' ν := by
  unfold logEnergyPair
  exact integral_add_measure hμ hμ'

/-- Mutual energy is additive in the inner measure (given finite-energy
integrability of the kernel against `ν, ν'` pointwise, and of the resulting
potentials against `μ`). -/
theorem logEnergyPair_add_right (μ ν ν' : Measure ℂ)
    (hν : ∀ z, Integrable (fun ζ => logKernel z ζ) ν)
    (hν' : ∀ z, Integrable (fun ζ => logKernel z ζ) ν')
    (hpotν : Integrable (fun z => logPotential ν z) μ)
    (hpotν' : Integrable (fun z => logPotential ν' z) μ) :
    logEnergyPair μ (ν + ν') = logEnergyPair μ ν + logEnergyPair μ ν' := by
  unfold logEnergyPair
  rw [show (fun z => logPotential (ν + ν') z)
        = (fun z => logPotential ν z + logPotential ν' z) from
      funext fun z => logPotential_add ν ν' z (hν z) (hν' z)]
  exact integral_add hpotν hpotν'

/-- Logarithmic energy scales quadratically: `I(c•μ) = c²·I(μ)`. A hypothesis-free
consequence of bi-homogeneity, and a brick of the capacity argument
(`cap = exp(-inf I)`, so quadratic energy scaling is degree-`1` capacity scaling). -/
theorem logEnergy_smul (μ : Measure ℂ) (c : ENNReal) :
    logEnergy (c • μ) = c.toReal ^ 2 * logEnergy μ := by
  rw [← logEnergyPair_self (c • μ), logEnergyPair_smul_left μ (c • μ) c,
      logEnergyPair_smul_right μ μ c, logEnergyPair_self μ]
  ring

/-- **Convex-combination energy expansion** (the algebraic heart of Tier 2c).
`I(a•μ + b•ν) = a²·I(μ) + ab·J(μ,ν) + ba·J(ν,μ) + b²·I(ν)`.
Specialised to `a = 1-t`, `b = t` and combined with symmetry `J(μ,ν)=J(ν,μ)`,
this is the card's `I(μ_t) = V_A - 2t(1-t)∫g dν + t²(I(ν)-V_A)` once `μ` is the
equilibrium measure. Finite-energy integrability rides as explicit hypotheses. -/
theorem logEnergy_convexCombo (μ ν : Measure ℂ) (a b : ENNReal)
    (hA1 : Integrable (fun z => logPotential (a • μ + b • ν) z) (a • μ))
    (hA2 : Integrable (fun z => logPotential (a • μ + b • ν) z) (b • ν))
    (hkaμ : ∀ z, Integrable (fun ζ => logKernel z ζ) (a • μ))
    (hkbν : ∀ z, Integrable (fun ζ => logKernel z ζ) (b • ν))
    (hpμ_aμ : Integrable (fun z => logPotential (a • μ) z) μ)
    (hpμ_bν : Integrable (fun z => logPotential (b • ν) z) μ)
    (hpν_aμ : Integrable (fun z => logPotential (a • μ) z) ν)
    (hpν_bν : Integrable (fun z => logPotential (b • ν) z) ν) :
    logEnergy (a • μ + b • ν)
      = a.toReal ^ 2 * logEnergy μ + a.toReal * b.toReal * logEnergyPair μ ν
        + b.toReal * a.toReal * logEnergyPair ν μ + b.toReal ^ 2 * logEnergy ν := by
  rw [← logEnergyPair_self (a • μ + b • ν),
      logEnergyPair_add_left (a • μ) (b • ν) (a • μ + b • ν) hA1 hA2,
      logEnergyPair_smul_left μ (a • μ + b • ν) a,
      logEnergyPair_smul_left ν (a • μ + b • ν) b,
      logEnergyPair_add_right μ (a • μ) (b • ν) hkaμ hkbν hpμ_aμ hpμ_bν,
      logEnergyPair_add_right ν (a • μ) (b • ν) hkaμ hkbν hpν_aμ hpν_bν,
      logEnergyPair_smul_right μ μ a, logEnergyPair_smul_right μ ν b,
      logEnergyPair_smul_right ν μ a, logEnergyPair_smul_right ν ν b,
      logEnergyPair_self μ, logEnergyPair_self ν]
  ring

end Bottcher
