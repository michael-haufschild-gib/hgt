import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Polynomial.Roots

/-!
# The finite-rank phase law

For real weights `v_j` with `Σ v_j = 1` on at most `m` unit phases `u_j`, the moments
`b_n = Σ_j v_j u_j^n` satisfy `max_{1 ≤ n ≤ m} |b_n| ≥ 1/m`. The coefficient vector of
`∏_j (x - u_j)` lies in the kernel of the `(m+1) × (m+1)` Toeplitz matrix `(b_{a-b})`; the row
through its largest coefficient gives the bound. Equality holds for equal weights on `m` of the
`(m+1)`-st roots of unity, where `b_n = -u_*^n/m` for `1 ≤ n ≤ m` and `b_{m+1} = 1`.
-/

open Complex Polynomial
open scoped ComplexConjugate

namespace HTGeometry

noncomputable section

variable {ι : Type*}

/-- The phase moments `b_n = Σ_j v_j u_j^n` of real weights on phases. -/
def unitPhaseMoment (s : Finset ι) (v : ι → ℝ) (u : ι → ℂ) (n : ℤ) : ℂ :=
  ∑ j ∈ s, (v j : ℂ) * u j ^ n

theorem unitPhaseMoment_zero {s : Finset ι} {v : ι → ℝ} (hs : ∑ j ∈ s, v j = 1) (u : ι → ℂ) :
    unitPhaseMoment s v u 0 = 1 := by
  simp [unitPhaseMoment, ← Complex.ofReal_sum, hs]

/-- `b_{-n} = conj b_n` for unit phases. -/
theorem unitPhaseMoment_neg {s : Finset ι} (v : ι → ℝ) {u : ι → ℂ} (hu : ∀ j ∈ s, ‖u j‖ = 1)
    (n : ℤ) : unitPhaseMoment s v u (-n) = conj (unitPhaseMoment s v u n) := by
  rw [unitPhaseMoment, unitPhaseMoment, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hu0 : u j ≠ 0 := by
    intro h; have := hu j hj; rw [h, norm_zero] at this; exact zero_ne_one this
  have hinv : (u j)⁻¹ = conj (u j) := by
    rw [Complex.inv_def, ← Complex.sq_norm, hu j hj]; simp
  rw [map_mul, Complex.conj_ofReal, map_zpow₀, ← hinv, zpow_neg, inv_zpow]

theorem norm_unitPhaseMoment_neg {s : Finset ι} (v : ι → ℝ) {u : ι → ℂ} (hu : ∀ j ∈ s, ‖u j‖ = 1)
    (n : ℤ) : ‖unitPhaseMoment s v u (-n)‖ = ‖unitPhaseMoment s v u n‖ := by
  rw [unitPhaseMoment_neg v hu, Complex.norm_conj]

/-- The kernel relation: the coefficients `c_k` of `∏_j (x - u_j)` annihilate every shifted row
`Σ_k c_k b_{k-a} = 0` of the Toeplitz matrix `(b_{a-b})`. -/
theorem sum_coeff_mul_unitPhaseMoment_eq_zero {s : Finset ι} (v : ι → ℝ) {u : ι → ℂ}
    (hu : ∀ j ∈ s, ‖u j‖ = 1) {m : ℕ} (hcard : s.card ≤ m) (a : ℕ) :
    ∑ k ∈ Finset.range (m + 1), (∏ j ∈ s, (X - C (u j))).coeff k *
      unitPhaseMoment s v u ((k : ℤ) - a) = 0 := by
  set P := ∏ j ∈ s, (X - C (u j))
  have hdeg : P.natDegree < m + 1 := by
    rw [natDegree_finsetProd_X_sub_C_eq_card]; omega
  have hu0 : ∀ j ∈ s, u j ≠ 0 := by
    intro j hj h; have := hu j hj; rw [h, norm_zero] at this; exact zero_ne_one this
  have heval : ∀ j ∈ s, ∑ k ∈ Finset.range (m + 1), P.coeff k * u j ^ k = 0 := by
    intro j hj
    rw [← eval_eq_sum_range' hdeg, eval_prod]
    exact Finset.prod_eq_zero hj (by simp)
  simp only [unitPhaseMoment, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j hj => ?_
  have : ∀ k : ℕ, P.coeff k * ((v j : ℂ) * u j ^ ((k : ℤ) - a)) =
      ((v j : ℂ) / u j ^ a) * (P.coeff k * u j ^ k) := by
    intro k
    rw [zpow_sub₀ (hu0 j hj), zpow_natCast, zpow_natCast]
    field_simp
  simp only [this, ← Finset.mul_sum, heval j hj, mul_zero]

/-- **The finite-rank phase law (39).** For real weights with `Σ v_j = 1` on at most `m ≥ 1` unit
phases, `max_{1 ≤ n ≤ m} |b_n| ≥ 1/m`. -/
theorem exists_one_div_le_norm_unitPhaseMoment {s : Finset ι} {v : ι → ℝ}
    (hs : ∑ j ∈ s, v j = 1) {u : ι → ℂ} (hu : ∀ j ∈ s, ‖u j‖ = 1) {m : ℕ} (hm : 1 ≤ m)
    (hcard : s.card ≤ m) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ m ∧ 1 / (m : ℝ) ≤ ‖unitPhaseMoment s v u n‖ := by
  by_contra H
  push Not at H
  set P := ∏ j ∈ s, (X - C (u j))
  have hmon : P.Monic := monic_prod_X_sub_C u s
  have hdeg : P.natDegree ≤ m := by rw [natDegree_finsetProd_X_sub_C_eq_card]; exact hcard
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image (Finset.range (m + 1)) (fun k => ‖P.coeff k‖)
    ⟨0, by simp⟩
  have hca : 1 ≤ ‖P.coeff a‖ := by
    have := hmax P.natDegree (Finset.mem_range.mpr (by omega))
    rwa [coeff_natDegree, hmon.leadingCoeff, norm_one] at this
  have hrel := sum_coeff_mul_unitPhaseMoment_eq_zero v hu hcard a
  rw [← Finset.add_sum_erase _ _ ha, show ((a : ℤ) - a) = 0 by ring, unitPhaseMoment_zero hs,
    mul_one] at hrel
  have hbound : ∀ k ∈ (Finset.range (m + 1)).erase a,
      ‖P.coeff k * unitPhaseMoment s v u ((k : ℤ) - a)‖ < ‖P.coeff a‖ * (1 / m) := by
    intro k hk
    obtain ⟨hka, hk⟩ := Finset.mem_erase.mp hk
    rw [Finset.mem_range] at hk ha
    rw [norm_mul]
    have hb : ‖unitPhaseMoment s v u ((k : ℤ) - a)‖ < 1 / m := by
      rcases lt_or_gt_of_ne hka with h | h
      · have := H (a - k) (by omega) (by omega)
        rwa [← norm_unitPhaseMoment_neg v hu, show -((a - k : ℕ) : ℤ) = (k : ℤ) - a by
          rw [Nat.cast_sub h.le]; ring] at this
      · have := H (k - a) (by omega) (by omega)
        rwa [show ((k - a : ℕ) : ℤ) = (k : ℤ) - a by rw [Nat.cast_sub h.le]] at this
    calc ‖P.coeff k‖ * ‖unitPhaseMoment s v u ((k : ℤ) - a)‖ ≤
          ‖P.coeff a‖ * ‖unitPhaseMoment s v u ((k : ℤ) - a)‖ :=
          mul_le_mul_of_nonneg_right (hmax k (Finset.mem_range.mpr hk)) (norm_nonneg _)
      _ < ‖P.coeff a‖ * (1 / m) := mul_lt_mul_of_pos_left hb (by linarith)
  have hne : ((Finset.range (m + 1)).erase a).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem ha, Finset.card_range]; omega
  have hlt : ‖∑ k ∈ (Finset.range (m + 1)).erase a, P.coeff k *
      unitPhaseMoment s v u ((k : ℤ) - a)‖ < ‖P.coeff a‖ := by
    calc _ ≤ ∑ k ∈ (Finset.range (m + 1)).erase a,
          ‖P.coeff k * unitPhaseMoment s v u ((k : ℤ) - a)‖ := norm_sum_le _ _
      _ < ∑ k ∈ (Finset.range (m + 1)).erase a, ‖P.coeff a‖ * (1 / m) :=
          Finset.sum_lt_sum_of_nonempty hne hbound
      _ = ‖P.coeff a‖ := by
          rw [Finset.sum_const, Finset.card_erase_of_mem ha, Finset.card_range, nsmul_eq_mul]
          have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
          field_simp; push_cast; ring
  rw [add_eq_zero_iff_eq_neg] at hrel
  rw [hrel, norm_neg] at hlt
  exact lt_irrefl _ hlt

/-- The primitive `N`-th root of unity `e^{2πi/N}`. -/
def unitRootPhase (N : ℕ) : ℂ := cexp (2 * Real.pi * I / N)

/-- **Sharpness of (39).** Equal weights `1/m` on the `(m+1)`-st roots of unity other than
`u_* = ζ^{k₀}`: `b_n = -u_*^n/m` for `1 ≤ n ≤ m`, and `b_{m+1} = 1`. -/
theorem unitPhaseMoment_omitted_root {m : ℕ} (hm : 1 ≤ m) {k₀ : ℕ} (hk₀ : k₀ < m + 1) :
    (∀ n : ℕ, 1 ≤ n → n ≤ m →
      unitPhaseMoment ((Finset.range (m + 1)).erase k₀) (fun _ => 1 / m)
        (fun k => unitRootPhase (m + 1) ^ k) n = -(unitRootPhase (m + 1) ^ k₀) ^ n / m) ∧
    unitPhaseMoment ((Finset.range (m + 1)).erase k₀) (fun _ => 1 / m)
        (fun k => unitRootPhase (m + 1) ^ k) (m + 1 : ℕ) = 1 := by
  have hprim : IsPrimitiveRoot (unitRootPhase (m + 1)) (m + 1) :=
    Complex.isPrimitiveRoot_exp (m + 1) (by omega)
  have hmem : k₀ ∈ Finset.range (m + 1) := Finset.mem_range.mpr hk₀
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  constructor
  · intro n hn1 hn2
    have hne : unitRootPhase (m + 1) ^ n ≠ 1 := by
      rw [Ne, hprim.pow_eq_one_iff_dvd]
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    have hpow : (unitRootPhase (m + 1) ^ n) ^ (m + 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
    have hgeom : ∑ k ∈ Finset.range (m + 1), (unitRootPhase (m + 1) ^ n) ^ k = 0 := by
      rw [geom_sum_eq hne, hpow, sub_self, zero_div]
    have hsplit := Finset.add_sum_erase (Finset.range (m + 1))
      (fun k => (unitRootPhase (m + 1) ^ n) ^ k) hmem
    rw [hgeom] at hsplit
    simp only [unitPhaseMoment, zpow_natCast, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_natCast]
    rw [← Finset.mul_sum]
    have : ∑ k ∈ (Finset.range (m + 1)).erase k₀, (unitRootPhase (m + 1) ^ k) ^ n =
        -(unitRootPhase (m + 1) ^ k₀) ^ n := by
      have h2 : ∀ k, (unitRootPhase (m + 1) ^ k) ^ n = (unitRootPhase (m + 1) ^ n) ^ k := by
        intro k; rw [← pow_mul, ← pow_mul, mul_comm]
      simp only [h2]
      linear_combination hsplit
    rw [this]; field_simp
  · simp only [unitPhaseMoment, zpow_natCast, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_natCast]
    have h1 : ∀ k, (unitRootPhase (m + 1) ^ k) ^ (m + 1) = 1 := by
      intro k; rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
    simp only [h1, mul_one, Finset.sum_const, Finset.card_erase_of_mem hmem, Finset.card_range,
      add_tsub_cancel_right, nsmul_eq_mul]
    field_simp

/-- Equality in (39): the omitted-root configuration has `|b_n| = 1/m` for all `1 ≤ n ≤ m`. -/
theorem norm_unitPhaseMoment_omitted_root {m : ℕ} (hm : 1 ≤ m) {k₀ : ℕ} (hk₀ : k₀ < m + 1) {n : ℕ}
    (hn1 : 1 ≤ n) (hn2 : n ≤ m) :
    ‖unitPhaseMoment ((Finset.range (m + 1)).erase k₀) (fun _ => 1 / m)
        (fun k => unitRootPhase (m + 1) ^ k) n‖ = 1 / m := by
  have hprim : IsPrimitiveRoot (unitRootPhase (m + 1)) (m + 1) :=
    Complex.isPrimitiveRoot_exp (m + 1) (by omega)
  rw [(unitPhaseMoment_omitted_root hm hk₀).1 n hn1 hn2, norm_div, norm_neg, norm_pow, norm_pow,
    hprim.norm'_eq_one (by omega), one_pow, one_pow, Complex.norm_natCast]

end

end HTGeometry
