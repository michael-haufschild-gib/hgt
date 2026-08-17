import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Int.Star

/-!
# The polynomial orbit weight has bounded generator ratios

On the valuation lattice the polynomial weight is `w_κ(ν) = (1 + |ν|₁)^{-κ}`, and the only property
a weighted shift needs is that consecutive weights have a bounded ratio.  That is a one-line
consequence of the triangle inequality in the form

`1 + |ν + s|₁ ≤ (1 + |ν|₁)(1 + |s|₁)`,

which holds because the cross term `|ν|₁ |s|₁` is nonnegative.  Raising to the power `κ` gives the
ratio bound `(1 + |s|₁)^κ`, uniform in `ν` — so both oriented weighted shifts are bounded, with a
bound depending only on the step.
-/

open Finset

noncomputable section

namespace RHTower

variable {ι : Type*} [Fintype ι]

/-- The `ℓ¹` size of a valuation label. -/
def latticeL1 (ν : ι → ℤ) : ℕ := ∑ i, (ν i).natAbs

theorem latticeL1_add_le (ν s : ι → ℤ) :
    latticeL1 (ν + s) ≤ latticeL1 ν + latticeL1 s := by
  rw [latticeL1, latticeL1, latticeL1, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simpa using Int.natAbs_add_le (ν i) (s i)

/-- The bracketed size is submultiplicative under a lattice step. -/
theorem one_add_latticeL1_add_le (ν s : ι → ℤ) :
    (1 : ℝ) + (latticeL1 (ν + s) : ℝ) ≤ (1 + (latticeL1 ν : ℝ)) * (1 + (latticeL1 s : ℝ)) := by
  have hadd : (latticeL1 (ν + s) : ℝ) ≤ (latticeL1 ν : ℝ) + (latticeL1 s : ℝ) := by
    exact_mod_cast latticeL1_add_le ν s
  have hν : (0 : ℝ) ≤ (latticeL1 ν : ℝ) := Nat.cast_nonneg _
  have hs : (0 : ℝ) ≤ (latticeL1 s : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hν hs]

/-- The polynomial orbit weight. -/
def polyWeight (κ : ℝ) (ν : ι → ℤ) : ℝ := (1 + (latticeL1 ν : ℝ)) ^ (-κ)

theorem polyWeight_pos (κ : ℝ) (ν : ι → ℤ) : 0 < polyWeight κ ν := by
  rw [polyWeight]
  exact Real.rpow_pos_of_pos (by positivity) _

/-- **`(14)`: the generator ratio is bounded by a power of the step.** -/
theorem polyWeight_ratio_le {κ : ℝ} (hκ : 0 ≤ κ) (ν s : ι → ℤ) :
    polyWeight κ ν / polyWeight κ (ν + s) ≤ (1 + (latticeL1 s : ℝ)) ^ κ := by
  have hν : (0 : ℝ) < 1 + (latticeL1 ν : ℝ) := by positivity
  have hs : (0 : ℝ) < 1 + (latticeL1 s : ℝ) := by positivity
  have hνs : (0 : ℝ) < 1 + (latticeL1 (ν + s) : ℝ) := by positivity
  have hratio : polyWeight κ ν / polyWeight κ (ν + s)
      = ((1 + (latticeL1 (ν + s) : ℝ)) / (1 + (latticeL1 ν : ℝ))) ^ κ := by
    rw [polyWeight, polyWeight, Real.div_rpow hνs.le hν.le]
    rw [Real.rpow_neg hν.le, Real.rpow_neg hνs.le]
    field_simp
  rw [hratio]
  refine Real.rpow_le_rpow (by positivity) ?_ hκ
  rw [div_le_iff₀ hν]
  calc (1 : ℝ) + (latticeL1 (ν + s) : ℝ)
      ≤ (1 + (latticeL1 ν : ℝ)) * (1 + (latticeL1 s : ℝ)) := one_add_latticeL1_add_le ν s
    _ = (1 + (latticeL1 s : ℝ)) * (1 + (latticeL1 ν : ℝ)) := mul_comm _ _

/-- The reciprocal ratio obeys the same bound, so both oriented weighted shifts are bounded. -/
theorem polyWeight_ratio_le' {κ : ℝ} (hκ : 0 ≤ κ) (ν s : ι → ℤ) :
    polyWeight κ (ν + s) / polyWeight κ ν ≤ (1 + (latticeL1 s : ℝ)) ^ κ := by
  have h := polyWeight_ratio_le hκ (ν + s) (-s)
  have hval : ν + s + -s = ν := by
    funext i
    simp
  rw [hval] at h
  have hneg : latticeL1 (-s) = latticeL1 s := by
    rw [latticeL1, latticeL1]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  rwa [hneg] at h

/-- **The event weight of `(12)`.**  At a logarithmic event clock the weighted event factor is a
single lattice power. -/
theorem polyWeight_sq_mul_event_le {κ σ Q : ℝ} (hσ : 0 ≤ σ) (ν : ι → ℤ) {τ : ℝ}
    (hτ : τ ≤ Q * Real.log (2 + (latticeL1 ν : ℝ))) :
    polyWeight κ ν ^ 2 * Real.exp (2 * σ * τ)
      ≤ (1 + (latticeL1 ν : ℝ)) ^ (-2 * κ) * (2 + (latticeL1 ν : ℝ)) ^ (2 * σ * Q) := by
  have hbase : (0 : ℝ) < 2 + (latticeL1 ν : ℝ) := by positivity
  have h1 : (0 : ℝ) < 1 + (latticeL1 ν : ℝ) := by positivity
  have hsq : polyWeight κ ν ^ 2 = (1 + (latticeL1 ν : ℝ)) ^ (-2 * κ) := by
    rw [polyWeight, ← Real.rpow_natCast ((1 + (latticeL1 ν : ℝ)) ^ (-κ)) 2,
      ← Real.rpow_mul h1.le]
    norm_num
    ring_nf
  have hexp : Real.exp (2 * σ * τ) ≤ (2 + (latticeL1 ν : ℝ)) ^ (2 * σ * Q) := by
    have hmul : 2 * σ * τ ≤ 2 * σ * Q * Real.log (2 + (latticeL1 ν : ℝ)) := by
      have h2σ : (0 : ℝ) ≤ 2 * σ := by linarith
      nlinarith [hτ, h2σ]
    calc Real.exp (2 * σ * τ) ≤ Real.exp (2 * σ * Q * Real.log (2 + (latticeL1 ν : ℝ))) :=
          Real.exp_le_exp.mpr hmul
      _ = (2 + (latticeL1 ν : ℝ)) ^ (2 * σ * Q) := by
          rw [Real.rpow_def_of_pos hbase]
          ring_nf
  rw [hsq]
  exact mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg h1.le _)

end RHTower
