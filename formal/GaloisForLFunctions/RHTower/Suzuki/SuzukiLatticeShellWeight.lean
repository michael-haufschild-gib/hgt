import GaloisForLFunctions.RHTower.Suzuki.SuzukiLatticeWeightComparison

/-!
# `(17)`: the polynomial group estimate

The shell weight is dominated by the coordinate moments, each of which the sharp moment bound
controls by `(1+|x|)^m` times the corresponding moment of the initial field; and every moment of
order at most `m` of a field is dominated by its shell-weighted norm.  So conjugating the evolution
by the polynomial weight costs exactly `m` powers of the time.
-/

open Finset

noncomputable section

namespace RHTower

variable {P : Type*} [Fintype P] [DecidableEq P]

local notation "H" => lp (fun _ : (P → ℤ) => ℂ) 2

/-- The shell weight of degree `m`. -/
def shellWeight (m : ℕ) (r : P → ℤ) : ℝ := (1 + (orbitLength r : ℝ)) ^ m

omit [DecidableEq P] in
theorem one_le_shellWeight (m : ℕ) (r : P → ℤ) : 1 ≤ shellWeight m r := by
  rw [shellWeight]
  refine one_le_pow₀ ?_
  have : (0 : ℝ) ≤ (orbitLength r : ℝ) := by positivity
  linarith

omit [DecidableEq P] in
theorem shellWeight_pos (m : ℕ) (r : P → ℤ) : 0 < shellWeight m r :=
  lt_of_lt_of_le zero_lt_one (one_le_shellWeight m r)

omit [DecidableEq P] in
/-- Every coordinate moment of order at most `m` is dominated by the shell weight. -/
theorem abs_posPow_le_shellWeight {i m : ℕ} (him : i ≤ m) (p : P) (r : P → ℤ) :
    ‖((r p : ℤ) : ℂ) ^ i‖ ≤ shellWeight m r := by
  have habs : ‖((r p : ℤ) : ℂ)‖ = |((r p : ℤ) : ℝ)| := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  have hcoord : |((r p : ℤ) : ℝ)| ≤ (orbitLength r : ℝ) := by
    have hle : (r p).natAbs ≤ orbitLength r := by
      rw [orbitLength]
      exact Finset.single_le_sum (f := fun s => (r s).natAbs) (fun s _ => Nat.zero_le _)
        (Finset.mem_univ p)
    have hcast : |((r p : ℤ) : ℝ)| = (((r p).natAbs : ℕ) : ℝ) := by simp [Int.cast_abs]
    rw [hcast]
    exact_mod_cast hle
  have hbase : ‖((r p : ℤ) : ℂ)‖ ≤ 1 + (orbitLength r : ℝ) := by
    rw [habs]
    linarith
  rw [norm_pow, shellWeight]
  calc ‖((r p : ℤ) : ℂ)‖ ^ i ≤ (1 + (orbitLength r : ℝ)) ^ i :=
        pow_le_pow_left₀ (norm_nonneg _) hbase i
    _ ≤ (1 + (orbitLength r : ℝ)) ^ m := by
        refine pow_le_pow_right₀ ?_ him
        have : (0 : ℝ) ≤ (orbitLength r : ℝ) := by positivity
        linarith

omit [Fintype P] [DecidableEq P] in
/-- The pointwise modulus of an `ℓ²` field, as an `ℓ²` field. -/
def absL2 (u : H) : H :=
  ⟨fun r => ((‖((u : H) : (P → ℤ) → ℂ) r‖ : ℝ) : ℂ), by
    refine memℓp_gen ?_
    refine ((memℓp_gen_iff (p := 2) (by norm_num)).mp (lp.memℓp u)).congr fun r => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]⟩

omit [Fintype P] [DecidableEq P] in
@[simp]
theorem coe_absL2 (u : H) (r : P → ℤ) :
    ((absL2 u : H) : (P → ℤ) → ℂ) r = ((‖((u : H) : (P → ℤ) → ℂ) r‖ : ℝ) : ℂ) := rfl

omit [Fintype P] [DecidableEq P] in
theorem norm_absL2 (u : H) : ‖(absL2 u : H)‖ = ‖u‖ := by
  refine le_antisymm (norm_le_of_pointwise_le fun r => ?_) (norm_le_of_pointwise_le fun r => ?_)
  · rw [coe_absL2, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  · rw [coe_absL2, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]

/-- The shell-weighted field. -/
def shellWeightField (m : ℕ) (g : (P → ℤ) → ℂ) : (P → ℤ) → ℂ :=
  fun r => ((shellWeight m r : ℝ) : ℂ) * g r

omit [DecidableEq P] in
theorem support_shellWeightField_subset (m : ℕ) (g : (P → ℤ) → ℂ) :
    Function.support (shellWeightField m g) ⊆ Function.support g := by
  intro r hr
  simp only [Function.mem_support, shellWeightField] at hr ⊢
  intro hcon
  rw [hcon, mul_zero] at hr
  exact hr rfl

omit [DecidableEq P] in
/-- Every coordinate moment of order at most `m` is bounded by the shell-weighted norm. -/
theorem norm_posPow_le_shellWeighted {i m : ℕ} (him : i ≤ m) (p : P) {g : (P → ℤ) → ℂ}
    (hg : (Function.support g).Finite) :
    ‖(l2OfFinSupp (posPowField p i g)
        (hg.subset (support_posPowField_subset p i g)) : H)‖
      ≤ ‖(l2OfFinSupp (shellWeightField m g)
          (hg.subset (support_shellWeightField_subset m g)) : H)‖ := by
  refine norm_le_of_pointwise_le fun r => ?_
  rw [coe_l2OfFinSupp, coe_l2OfFinSupp, posPowField, shellWeightField, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (shellWeight_pos m r).le]
  exact mul_le_mul_of_nonneg_right (abs_posPow_le_shellWeight him p r) (norm_nonneg _)

end RHTower
