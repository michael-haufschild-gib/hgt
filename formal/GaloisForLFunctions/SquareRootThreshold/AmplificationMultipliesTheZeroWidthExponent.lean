import GaloisForLFunctions.SquareRootThreshold.TheZeroWidthIsALandauExponent

/-!
# Amplification multiplies the zero-width exponent

Deligne's proof of the Weil conjectures amplifies: the `k`-th tensor power of a sheaf has `k`
times the weight, and the known pole of its top cohomology evaluates the amplified weight from
outside. The analytic imitation for `ζ` raises the Chebyshev deficit to a power. This module
records what the power knows.

Let `D(T)` be the integrated logarithmic Chebyshev deficit (`ccmLogChebyshevDeficitPrimitive`)
and `deficitAbsRates` the exponents `β ≥ 0` with `|D(T)| ≤ B(1 + T)e^{(½+β)T}`; their infimum is
the zero width (`zetaZeroWidth_eq_sInf_deficitAbsRates`). The admissible exponents of the `k`-th
power, `|D(T)|^k ≤ B(1 + T)^k e^{(k/2+γ)T}`, form `deficitPowerRates k`.

* `mem_deficitPowerRates_iff`: `γ ∈ deficitPowerRates k ↔ γ/k ∈ deficitAbsRates`, by `k`-th
  roots in one direction and `k`-th powers in the other.
* `deficitPowerRates_eq_image`: the amplified exponents are the `k`-fold dilates of the
  exponents of `D`.
* `sInf_deficitPowerRates`: `inf (deficitPowerRates k) = k · zetaZeroWidth`.
* `riemannHypothesis_iff_sInf_deficitPowerRates_eq_zero`: RH iff the amplified exponent is `0`.

The abscissa of `|D|^k` is `k/2 + k · zetaZeroWidth`: `k` times the abscissa of `D`, and nothing
else. A power of the deficit carries exactly the information of the deficit. Where Deligne's
argument has an independent evaluation of the amplified exponent, the analytic imitation has none,
and the amplification returns the width it started from.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

/-- Admissible exponents of the `k`-th power of the integrated Chebyshev deficit:
`|D(T)|^k ≤ B (1 + T)^k e^{(k/2 + γ) T}` for all `T ≥ 0`. -/
def deficitPowerRates (k : ℕ) : Set ℝ :=
  {γ : ℝ | 0 ≤ γ ∧ ∃ B : ℝ, ∀ T : ℝ, 0 ≤ T →
    |ccmLogChebyshevDeficitPrimitive T| ^ k ≤
      B * (1 + T) ^ k * Real.exp (((k : ℝ) / 2 + γ) * T)}

theorem deficitPowerRates_one : deficitPowerRates 1 = deficitAbsRates := by
  ext γ
  simp [deficitPowerRates, deficitAbsRates]

/-- `γ` is an admissible exponent of the `k`-th power iff `γ/k` is one of the deficit. -/
theorem mem_deficitPowerRates_iff {k : ℕ} (hk : 0 < k) {γ : ℝ} :
    γ ∈ deficitPowerRates k ↔ γ / k ∈ deficitAbsRates := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := hkpos.ne'
  constructor
  · rintro ⟨hγ, B, hB⟩
    refine ⟨div_nonneg hγ hkpos.le, B ^ ((k : ℝ)⁻¹), fun T hT => ?_⟩
    have hDT := hB T hT
    have hT1 : (0 : ℝ) ≤ 1 + T := by linarith
    have hpos : 0 < (1 + T) ^ k * Real.exp (((k : ℝ) / 2 + γ) * T) := by positivity
    -- the constant is forced nonnegative by a single value of `T`
    have hB0 : 0 ≤ B := by
      by_contra hBneg
      have h1 : B * (1 + T) ^ k * Real.exp (((k : ℝ) / 2 + γ) * T) < 0 := by
        rw [mul_assoc]
        exact mul_neg_of_neg_of_pos (lt_of_not_ge hBneg) hpos
      have h0 : 0 ≤ |ccmLogChebyshevDeficitPrimitive T| ^ k := by positivity
      linarith
    -- take `k`-th roots
    have hroot := Real.rpow_le_rpow (by positivity) hDT (by positivity : (0 : ℝ) ≤ (k : ℝ)⁻¹)
    rw [Real.pow_rpow_inv_natCast (abs_nonneg _) hk.ne'] at hroot
    have hrhs : (B * (1 + T) ^ k * Real.exp (((k : ℝ) / 2 + γ) * T)) ^ ((k : ℝ)⁻¹) =
        B ^ ((k : ℝ)⁻¹) * (1 + T) * Real.exp ((1 / 2 + γ / k) * T) := by
      rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, Real.mul_rpow hB0 (by positivity),
        Real.pow_rpow_inv_natCast hT1 hk.ne', ← Real.exp_mul]
      congr 2
      field_simp
    rwa [hrhs] at hroot
  · rintro ⟨hγ, B, hB⟩
    refine ⟨?_, B ^ k, fun T hT => ?_⟩
    · by_contra h
      have : γ / k < 0 := div_neg_of_neg_of_pos (lt_of_not_ge h) hkpos
      linarith
    · have h := pow_le_pow_left₀ (abs_nonneg _) (hB T hT) k
      have hexp : Real.exp ((1 / 2 + γ / k) * T) ^ k = Real.exp (((k : ℝ) / 2 + γ) * T) := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp
      rwa [mul_pow, mul_pow, hexp] at h

/-- The admissible exponents of the `k`-th power are the `k`-fold dilates of those of the
deficit. -/
theorem deficitPowerRates_eq_image {k : ℕ} (hk : 0 < k) :
    deficitPowerRates k = (fun β : ℝ => (k : ℝ) * β) '' deficitAbsRates := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  ext γ
  rw [mem_deficitPowerRates_iff hk]
  constructor
  · intro h
    exact ⟨γ / k, h, by field_simp⟩
  · rintro ⟨β, hβ, rfl⟩
    rwa [mul_div_cancel_left₀ β hk0]

/-- **Amplification multiplies the exponent.** The infimum of the admissible exponents of the
`k`-th power of the deficit is `k` times the zero width. -/
theorem sInf_deficitPowerRates {k : ℕ} (hk : 0 < k) :
    sInf (deficitPowerRates k) = k * zetaZeroWidth := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hne : (deficitPowerRates k).Nonempty := by
    refine ⟨k * (zetaZeroWidth + 1), (mem_deficitPowerRates_iff hk).mpr ?_⟩
    rw [mul_div_cancel_left₀ _ hkpos.ne']
    exact mem_deficitAbsRates_of_lt (by linarith)
  have hbdd : BddBelow (deficitPowerRates k) := ⟨0, fun _ h => h.1⟩
  refine le_antisymm ?_ (le_csInf hne fun γ hγ => ?_)
  · refine le_of_forall_pos_le_add fun ε hε => csInf_le hbdd ?_
    rw [mem_deficitPowerRates_iff hk]
    refine mem_deficitAbsRates_of_lt ?_
    rw [lt_div_iff₀ hkpos]
    have : zetaZeroWidth * k = k * zetaZeroWidth := mul_comm _ _
    linarith
  · have := zetaZeroWidth_le_of_mem_deficitAbsRates ((mem_deficitPowerRates_iff hk).mp hγ)
    rwa [le_div_iff₀ hkpos, mul_comm] at this

/-- RH iff the amplified exponent vanishes, for every `k ≥ 1`. -/
theorem riemannHypothesis_iff_sInf_deficitPowerRates_eq_zero {k : ℕ} (hk : 0 < k) :
    RiemannHypothesis ↔ sInf (deficitPowerRates k) = 0 := by
  rw [sInf_deficitPowerRates hk, riemannHypothesis_iff_zetaZeroWidth_eq_zero]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  constructor
  · intro h
    rw [h, mul_zero]
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hkpos.ne'
    · exact h

end GaloisForLFunctions.SquareRootThreshold
