import GaloisForLFunctions.RHTower.PrimeClockFiniteScaling
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Cofinal transfer across the finite-prime logarithmic boundary

The finite reflected prime-clock energy has a sharp horizontal window of width
`1 / log N`.  This file records the robust consequences needed by any cofinal
finite-prime architecture:

* an approximate eigenmode of a contraction has modulus at most its error above one;
* uniformly bounded reciprocal radial modes over arbitrarily large scales have zero exponent;
* if reflected prime-clock energy is `o((log N)^2)`, the horizontal displacement tends to zero.

The final theorem is the real-variable core of the analytic transfer principle: if holomorphic
finite-prime approximants converge locally uniformly and their zero fibers have sub-log-square
reflected energy, every limiting zero lies on the critical line.
-/

open Filter

namespace FinitePrimeBoundaryTransfer

/-- An approximate eigenmode of a contraction cannot have modulus larger than `1 + ε`.

This is the normed-space form of the quantum-channel observation: contractivity, rather than exact
reversibility, already controls the radial part of a transfer mode. -/
theorem norm_le_one_add_of_approx_eigenmode
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (x : E) (lambda : ℂ) (eps : ℝ)
    (hx : x ≠ 0) (hT : ‖T‖ ≤ 1)
    (happrox : ‖T x - lambda • x‖ ≤ eps * ‖x‖) :
    ‖lambda‖ ≤ 1 + eps := by
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hTx : ‖T x‖ ≤ ‖x‖ := by
    calc
      ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  have hmain : ‖lambda‖ * ‖x‖ ≤ (1 + eps) * ‖x‖ := by
    calc
      ‖lambda‖ * ‖x‖ = ‖lambda • x‖ := (norm_smul lambda x).symm
      _ = ‖(lambda • x - T x) + T x‖ := by congr 1; abel
      _ ≤ ‖lambda • x - T x‖ + ‖T x‖ := norm_add_le _ _
      _ = ‖T x - lambda • x‖ + ‖T x‖ := by rw [norm_sub_rev]
      _ ≤ eps * ‖x‖ + ‖x‖ := add_le_add happrox hTx
      _ = (1 + eps) * ‖x‖ := by ring
  exact le_of_mul_le_mul_right hmain hxnorm

/-- Reciprocal radial powers cannot both remain uniformly bounded on arbitrarily large scales
unless their exponent is zero. -/
theorem exponent_eq_zero_of_uniform_reflected_bounds
    {a C : ℝ}
    (hbound : ∀ R : ℝ, ∃ q : ℝ,
      R ≤ q ∧ q ^ a ≤ C ∧ q ^ (-a) ≤ C) :
    a = 0 := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have hlim : Tendsto (fun q : ℝ => q ^ (-a)) atTop atTop :=
      tendsto_rpow_atTop (neg_pos.mpr ha)
    obtain ⟨R, hR⟩ := eventually_atTop.1 (hlim.eventually (eventually_gt_atTop C))
    obtain ⟨q, hRq, -, hqneg⟩ := hbound R
    exact ((not_lt_of_ge hqneg) (hR q hRq)).elim
  · exact ha
  · have hlim : Tendsto (fun q : ℝ => q ^ a) atTop atTop :=
      tendsto_rpow_atTop ha
    obtain ⟨R, hR⟩ := eventually_atTop.1 (hlim.eventually (eventually_gt_atTop C))
    obtain ⟨q, hRq, hqpos, -⟩ := hbound R
    exact ((not_lt_of_ge hqpos) (hR q hRq)).elim

end FinitePrimeBoundaryTransfer

namespace RHTower

open Topology

/-- Quantitative finite-cutoff pinning.  Once the normalized susceptibility is at least `1/4`,
the squared horizontal displacement is bounded by reflected energy divided by `log(N)^2`. -/
theorem horizontalDisplacement_sq_le_energy_div_log_sq
    (N : ℕ) (epsilon : ℝ) (hN : 2 ≤ N)
    (hsusceptibility :
      (1 / 4 : ℝ) ≤ primeClockSusceptibility N / Real.log N ^ 2) :
    epsilon ^ 2 ≤ primeClockCutoffEnergy N epsilon / Real.log N ^ 2 := by
  have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hlower := primeClockCutoffEnergy_quadratic_lower N epsilon
  have hscale :
      epsilon ^ 2 ≤
        4 * epsilon ^ 2 * (primeClockSusceptibility N / Real.log N ^ 2) := by
    nlinarith [sq_nonneg epsilon]
  calc
    epsilon ^ 2 ≤
        4 * epsilon ^ 2 * (primeClockSusceptibility N / Real.log N ^ 2) := hscale
    _ = (4 * epsilon ^ 2 * primeClockSusceptibility N) / Real.log N ^ 2 := by
      field_simp
    _ ≤ primeClockCutoffEnergy N epsilon / Real.log N ^ 2 := by
      exact div_le_div_of_nonneg_right hlower (sq_nonneg _)

/-- **Cofinal logarithmic boundary transfer.**

If reflected finite-prime energy is `o((log N)^2)`, then the associated horizontal displacement
tends to zero.  In an analytic approximation architecture, applying this theorem to approximant
zeros supplied by locally uniform convergence pins every limiting zero to the critical line. -/
theorem tendsto_horizontalDisplacement_zero_of_energy_div_log_sq_tendsto_zero
    (epsilon : ℕ → ℝ)
    (henergy : Tendsto
      (fun N : ℕ => primeClockCutoffEnergy N (epsilon N) / Real.log N ^ 2)
      atTop (𝓝 0)) :
    Tendsto epsilon atTop (𝓝 0) := by
  have hratio := tendsto_primeClockSusceptibility_div_log_sq
  have hratioLower : ∀ᶠ N : ℕ in atTop,
      (1 / 4 : ℝ) ≤ primeClockSusceptibility N / Real.log N ^ 2 := by
    filter_upwards [(tendsto_order.1 hratio).1 (1 / 4 : ℝ) (by norm_num)] with N hN
    exact hN.le
  have hsqBound : ∀ᶠ N : ℕ in atTop,
      epsilon N ^ 2 ≤
        primeClockCutoffEnergy N (epsilon N) / Real.log N ^ 2 := by
    filter_upwards [hratioLower, eventually_ge_atTop 2] with N hratioN hN
    exact horizontalDisplacement_sq_le_energy_div_log_sq N (epsilon N) hN hratioN
  have hsq : Tendsto (fun N : ℕ => epsilon N ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun N => sq_nonneg (epsilon N)
    · exact hsqBound
    · exact henergy
  have habs : Tendsto (fun N : ℕ => |epsilon N|) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hsq.sqrt
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using habs

end RHTower
