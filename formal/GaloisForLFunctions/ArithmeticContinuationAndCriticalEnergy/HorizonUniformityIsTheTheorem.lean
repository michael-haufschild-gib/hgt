import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.ContinuationTransportsAdmission
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Horizon uniformity is the theorem

A continuation bound whose coefficient may depend on the observation horizon is worthless, and the
reason is not subtle: the explicit family

`Esc_T(ε) = exp(2(½ − ε) log(T+1)) − 1`

* vanishes identically at the endpoint `ε = ½`, so the endpoint budget holds with constant `0`;
* satisfies the *exact* linear continuation identity
  `−∂_ε Esc_T(ε) = 2 log(T+1) · (1 + Esc_T(ε))`
  at every damping, so its loss is linearly controlled with a coefficient that is finite — indeed
  constant in `ε` — for each fixed horizon;
* is admitted at no damping below `½`, since `Esc_T(ε) → ∞` with the horizon.

So an endpoint budget together with a per-horizon linear continuation bound implies nothing.  The
consequence is recorded as a non-existence statement: on no interval `[a, ½]` with `a > 0` does
this family carry a horizon-free continuation budget.  The programme's hypothesis `∃ β ∀ T` is
therefore not a convenience of the formulation; the quantifier order is the mathematics.

The family also shows that `½` is the right endpoint to start from and not an artefact: the escape
rate `2(½ − ε)` is exactly the gap to the endpoint, which is the shape the arithmetic family would
have if a zero sat on the boundary of the critical strip.
-/

open Set Filter

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-- The escape family: endpoint-admitted, horizonwise linearly controlled, admitted nowhere
below half damping. -/
def escapeEnergy (ε : ℝ) (T : ℕ) : ℝ :=
  Real.exp (2 * (1 / 2 - ε) * Real.log ((T : ℝ) + 1)) - 1

/-- Its damping derivative, with the horizon-dependent rate `2 log(T+1)`. -/
def escapeEnergyDeriv (T : ℕ) (ε : ℝ) : ℝ :=
  -(2 * Real.log ((T : ℝ) + 1)) * (1 + escapeEnergy ε T)

theorem log_natCast_add_one_nonneg (T : ℕ) : 0 ≤ Real.log ((T : ℝ) + 1) :=
  Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) T])

theorem escapeEnergy_nonneg {ε : ℝ} (hε : ε ≤ 1 / 2) (T : ℕ) : 0 ≤ escapeEnergy ε T := by
  have h : 0 ≤ 2 * (1 / 2 - ε) * Real.log ((T : ℝ) + 1) := by
    have := log_natCast_add_one_nonneg T
    have h2 : 0 ≤ 2 * (1 / 2 - ε) := by linarith
    positivity
  have := Real.one_le_exp h
  simp only [escapeEnergy]
  linarith

@[simp] theorem escapeEnergy_half (T : ℕ) : escapeEnergy (1 / 2) T = 0 := by
  simp [escapeEnergy]

/-- The endpoint budget is available with constant `0`. -/
theorem admits_escapeEnergy_half : Admits escapeEnergy (1 / 2) :=
  ⟨0, fun T => le_of_eq (escapeEnergy_half T)⟩

/-- **The exact horizonwise continuation identity.**  For each horizon the loss is linear in
`1 + Esc_T`, with the constant rate `2 log(T+1)`. -/
theorem hasDerivAt_escapeEnergy (ε : ℝ) (T : ℕ) :
    HasDerivAt (fun x => escapeEnergy x T) (escapeEnergyDeriv T ε) ε := by
  have hg : HasDerivAt (fun x : ℝ => 2 * (1 / 2 - x) * Real.log ((T : ℝ) + 1))
      (2 * (0 - 1) * Real.log ((T : ℝ) + 1)) ε :=
    (((hasDerivAt_const ε (1 / 2 : ℝ)).sub (hasDerivAt_id ε)).const_mul
      (2 : ℝ)).mul_const _
  refine (hg.exp.sub_const 1).congr_deriv ?_
  simp only [escapeEnergyDeriv, escapeEnergy]
  ring

/-- Below half damping the family escapes with the horizon. -/
theorem tendsto_escapeEnergy_atTop {ε : ℝ} (hε : ε < 1 / 2) :
    Tendsto (fun T : ℕ => escapeEnergy ε T) atTop atTop := by
  have h1 : Tendsto (fun T : ℕ => ((T : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun T : ℕ => Real.log ((T : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp h1
  have h3 : Tendsto (fun T : ℕ => 2 * (1 / 2 - ε) * Real.log ((T : ℝ) + 1)) atTop atTop :=
    h2.const_mul_atTop (by linarith)
  exact tendsto_atTop_add_const_right _ (-1) (Real.tendsto_exp_atTop.comp h3)

/-- No damping below `½` is admitted. -/
theorem not_admits_escapeEnergy {ε : ℝ} (hε : ε < 1 / 2) : ¬ Admits escapeEnergy ε := by
  rintro ⟨B, hB⟩
  obtain ⟨T, hT⟩ := ((tendsto_escapeEnergy_atTop hε).eventually_gt_atTop B).exists
  exact absurd (hB T) (not_le.mpr hT)

theorem not_cofinallyAdmits_escapeEnergy : ¬ CofinallyAdmits escapeEnergy := by
  intro h
  obtain ⟨ε, hε0, hε, hadm⟩ := h (1 / 2) (by norm_num)
  exact not_admits_escapeEnergy hε hadm

/-- **The quantifier order is the mathematics.**  On no interval `[a, ½]` with `a > 0` does the
escape family admit a horizon-free linear continuation budget — although it satisfies an exact
linear continuation identity for each horizon separately, and is admitted at the endpoint. -/
theorem not_linearContinuation_escapeEnergy {a : ℝ} (ha2 : a < 1 / 2) :
    ¬ LinearContinuation escapeEnergy escapeEnergyDeriv a (1 / 2) := by
  intro hcont
  refine not_admits_escapeEnergy ha2 (Admits.of_linearContinuation (le_of_lt ha2) ?_ ?_ hcont
    admits_escapeEnergy_half)
  · exact fun ε hε T => escapeEnergy_nonneg hε.2 T
  · exact fun T ε _ => hasDerivAt_escapeEnergy ε T

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
