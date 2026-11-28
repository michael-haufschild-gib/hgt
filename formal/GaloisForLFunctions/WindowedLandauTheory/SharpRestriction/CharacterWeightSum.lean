import GaloisForLFunctions.RHTower.Sieve.HarmonicDyadicBlock
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The degree-one term uses the base field estimate. The
higher-degree terms are bounded by a geometric sum and a
logarithmic harmonic sum. -/

noncomputable section

namespace WindowedLandauTheory.ConcN

private theorem geom_part (Q : ℝ) (hQ : 1 < Q) (M : ℕ) :
    ∑ δ ∈ Finset.Icc 2 (M + 1), (Q ^ (δ - 1))⁻¹ ≤ (1 - (Q ^ M)⁻¹) / (Q - 1) := by
  have hQ1 : Q - 1 ≠ 0 := (sub_pos.mpr hQ).ne'
  have hQ0 : Q ≠ 0 := by positivity
  suffices h : ∑ δ ∈ Finset.Icc 2 (M + 1), (Q ^ (δ - 1))⁻¹ = (1 - (Q ^ M)⁻¹) / (Q - 1) from h.le
  induction M with
  | zero =>
    rw [Finset.Icc_eq_empty_of_lt (show 0 + 1 < 2 by omega)]
    simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ m + 1 + 1), ih, Nat.add_sub_cancel]
    field_simp
    ring

private theorem harm_part (M : ℕ) :
    ∑ δ ∈ Finset.Icc 2 (M + 1), ((δ : ℝ))⁻¹ ≤ Real.log ((M + 1 : ℕ) : ℝ) := by
  simpa [one_div, show (2 : ℝ) - 1 = 1 by norm_num] using
    (RHTower.Sieve.sum_Icc_one_div_le_log_sub (m := 2) (n := M + 1) (by omega) (by omega))

private theorem term_le (q δ b : ℕ) (hq : 2 ≤ q) (hδ : 2 ≤ δ)
    (h : δ * b ≤ δ * (q - 1) + (q ^ δ - 1) / (q - 1)) :
    (b : ℝ) * ((q : ℝ) ^ δ - 1)⁻¹ ≤ ((q : ℝ) ^ (δ - 1))⁻¹ + ((δ : ℝ))⁻¹ * ((q : ℝ) - 1)⁻¹ := by
  have hq1 : (1:ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hB : (0:ℝ) < (q:ℝ) - 1 := by linarith
  have hD : (0:ℝ) < δ := by exact_mod_cast (by omega : 0 < δ)
  have hP1 : (1:ℝ) ≤ (q:ℝ) ^ (δ - 1) := one_le_pow₀ hq1.le
  have hP0 : (q:ℝ) ^ (δ - 1) ≠ 0 := by positivity
  have hpow : (q:ℝ) ^ δ = (q:ℝ) * (q:ℝ) ^ (δ - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hA : (0:ℝ) < (q:ℝ) ^ δ - 1 := by nlinarith
  have hcast : ((q ^ δ - 1 : ℕ) : ℝ) = (q:ℝ) ^ δ - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hcast2 : ((q - 1 : ℕ) : ℝ) = (q:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hR : (δ:ℝ) * b ≤ δ * ((q:ℝ) - 1) + ((q:ℝ) ^ δ - 1) / ((q:ℝ) - 1) := by
    have h' : ((δ * b : ℕ) : ℝ) ≤ ((δ * (q - 1) + (q ^ δ - 1) / (q - 1) : ℕ) : ℝ) :=
      Nat.cast_le.mpr h
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, hcast2] at h'
    have h'' : (((q ^ δ - 1) / (q - 1) : ℕ) : ℝ) ≤ ((q ^ δ - 1 : ℕ) : ℝ) / ((q - 1 : ℕ) : ℝ) :=
      Nat.cast_div_le
    rw [hcast, hcast2] at h''
    linarith
  have hstep : (b:ℝ) ≤ ((q:ℝ) - 1) + ((q:ℝ) ^ δ - 1) / ((q:ℝ) - 1) / δ := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hD]
    nlinarith
  have e1 : ((q:ℝ) ^ (δ - 1))⁻¹ * ((q:ℝ) ^ δ - 1) = (q:ℝ) - ((q:ℝ) ^ (δ - 1))⁻¹ := by
    rw [hpow, mul_comm (q:ℝ) ((q:ℝ) ^ (δ - 1)), mul_sub, inv_mul_cancel_left₀ hP0, mul_one]
  have e2 : ((δ:ℝ))⁻¹ * ((q:ℝ) - 1)⁻¹ * ((q:ℝ) ^ δ - 1) =
      ((q:ℝ) ^ δ - 1) / ((q:ℝ) - 1) / δ := by
    ring
  have hPinv : ((q:ℝ) ^ (δ - 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hP1
  have key : (b:ℝ) ≤ (((q:ℝ) ^ (δ - 1))⁻¹ + ((δ:ℝ))⁻¹ * ((q:ℝ) - 1)⁻¹) * ((q:ℝ) ^ δ - 1) := by
    rw [add_mul, e1, e2]
    linarith
  calc (b:ℝ) * ((q:ℝ) ^ δ - 1)⁻¹
      ≤ ((((q:ℝ) ^ (δ - 1))⁻¹ + ((δ:ℝ))⁻¹ * ((q:ℝ) - 1)⁻¹) * ((q:ℝ) ^ δ - 1)) *
          ((q:ℝ) ^ δ - 1)⁻¹ :=
        mul_le_mul_of_nonneg_right key (inv_nonneg.mpr hA.le)
    _ = ((q:ℝ) ^ (δ - 1))⁻¹ + ((δ:ℝ))⁻¹ * ((q:ℝ) - 1)⁻¹ := mul_inv_cancel_right₀ hA.ne' _

theorem character_weight_sum_le (q N : ℕ) (hN : 1 ≤ N) (hq : 2 ≤ q) (b : ℕ → ℕ) (m : ℝ)
    (h1 : (b 1 : ℝ) * ((q : ℝ) - 1)⁻¹ ≤ m)
    (h2 : ∀ δ, 2 ≤ δ → δ * b δ ≤ δ * (q - 1) + (q ^ δ - 1) / (q - 1)) :
    ∑ δ ∈ Finset.Icc 1 N, (b δ : ℝ) * ((q : ℝ) ^ δ - 1)⁻¹ ≤
      m + (1 + Real.log N) / ((q : ℝ) - 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hQ : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hQ1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (by omega : 1 ≤ M + 1)]
  have hI : Finset.Ioc 1 (M + 1) = Finset.Icc 2 (M + 1) := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [hI, pow_one]
  have h3 : ∑ δ ∈ Finset.Icc 2 (M + 1), (b δ : ℝ) * ((q : ℝ) ^ δ - 1)⁻¹ ≤
      ∑ δ ∈ Finset.Icc 2 (M + 1), (((q : ℝ) ^ (δ - 1))⁻¹ + ((δ : ℝ))⁻¹ * ((q : ℝ) - 1)⁻¹) :=
    Finset.sum_le_sum fun δ hδ =>
      term_le q δ (b δ) hq (Finset.mem_Icc.1 hδ).1 (h2 δ (Finset.mem_Icc.1 hδ).1)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at h3
  have h4 := geom_part (q : ℝ) hQ M
  have h5 := harm_part M
  have h6 : (1 - ((q : ℝ) ^ M)⁻¹) / ((q : ℝ) - 1) ≤ 1 / ((q : ℝ) - 1) := by
    apply div_le_div_of_nonneg_right _ hQ1.le
    have : 0 ≤ ((q : ℝ) ^ M)⁻¹ := by positivity
    linarith
  have h7 : (∑ δ ∈ Finset.Icc 2 (M + 1), ((δ : ℝ))⁻¹) * ((q : ℝ) - 1)⁻¹ ≤
      Real.log ((M + 1 : ℕ) : ℝ) * ((q : ℝ) - 1)⁻¹ :=
    mul_le_mul_of_nonneg_right h5 (inv_nonneg.2 hQ1.le)
  have h8 : (1 + Real.log ((M + 1 : ℕ) : ℝ)) / ((q : ℝ) - 1) =
      1 / ((q : ℝ) - 1) + Real.log ((M + 1 : ℕ) : ℝ) * ((q : ℝ) - 1)⁻¹ := by
    rw [add_div, div_eq_mul_inv (Real.log _)]
  rw [h8]
  linarith

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.character_weight_sum_le
