import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Rotated relations with polynomial coefficients

Let `F(w) = Σ f_k w^k` be entire with `f_k ≠ 0` and `f_{k+1}/f_k → 0`, as for every function of order less than one
with regular coefficients. A relation

`T(w) F(w) = A(w) F(ϑ w) + B(w) F(ϑ̄ w)`,  `|ϑ| = 1`, `ϑ ≠ ±1`,

with polynomial coefficients is **trivial**: `T = A = B = 0`.

Read the coefficient of `w^{D+m}`, `D` the top degree. The coefficient at index `m` dominates, since all others carry a
ratio `f_{m+j}/f_m → 0`. So `t_D − a_D ϑ^m − b_D ϑ̄^m → 0`, and the characters `1`, `ϑ^m`, `ϑ̄^m` are independent.

This is the coefficient boundary of the second-order mechanism: a relation of Bethe type with `|a| = |b|` cannot have
coefficients of finite type, so the only possible relations carry coefficients as large as `F` itself. Those include
the vacuous `a = F(ϑ̄ ·)`, `b = −F(ϑ ·)`, `T = 0`.
-/

open Finset Filter Topology Polynomial

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- **Uniqueness of power series.** A power series with sum zero everywhere has zero coefficients. -/
theorem eq_zero_of_forall_hasSum_zero {c : ℕ → ℂ} (h : ∀ w : ℂ, HasSum (fun n => c n * w ^ n) 0) (n : ℕ) :
    c n = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hsum1 : Summable c := by simpa using (h 1).summable
    set K : ℝ := ∑' j, ‖c (j + (n + 1))‖ with hK
    have hKs : Summable fun j => ‖c (j + (n + 1))‖ :=
      ((summable_nat_add_iff (n + 1)).mpr hsum1).norm
    have hK0 : 0 ≤ K := tsum_nonneg fun _ => norm_nonneg _
    have hbound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ‖c n‖ ≤ ε * K := by
      intro ε hε hε1
      have hg := (hasSum_nat_add_iff' (n + 1)).mpr (h (ε : ℂ))
      have hhead : ∑ j ∈ range (n + 1), c j * (ε : ℂ) ^ j = c n * (ε : ℂ) ^ n := by
        rw [sum_range_succ, sum_eq_zero, zero_add]
        intro j hj
        rw [ih j (mem_range.mp hj), zero_mul]
      rw [hhead, zero_sub] at hg
      have hnorm : ‖-(c n * (ε : ℂ) ^ n)‖ ≤ ∑' j, ‖c (j + (n + 1)) * (ε : ℂ) ^ (j + (n + 1))‖ := by
        rw [← hg.tsum_eq]
        exact norm_tsum_le_tsum_norm hg.summable.norm
      have hterm : ∀ j, ‖c (j + (n + 1)) * (ε : ℂ) ^ (j + (n + 1))‖ ≤
          ‖c (j + (n + 1))‖ * ε ^ (n + 1) := by
        intro j
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hε.le]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [add_comm]
        exact pow_le_pow_of_le_one hε.le hε1 (Nat.le_add_right _ _)
      have hle : ∑' j, ‖c (j + (n + 1)) * (ε : ℂ) ^ (j + (n + 1))‖ ≤ K * ε ^ (n + 1) := by
        rw [hK, ← tsum_mul_right]
        exact Summable.tsum_le_tsum hterm hg.summable.norm (hKs.mul_right _)
      rw [norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hε.le] at hnorm
      have hpos : 0 < ε ^ n := pow_pos hε n
      have h3 : ‖c n‖ * ε ^ n ≤ (ε * K) * ε ^ n := by
        calc ‖c n‖ * ε ^ n ≤ K * ε ^ (n + 1) := hnorm.trans hle
          _ = _ := by rw [pow_succ]; ring
      exact le_of_mul_le_mul_right h3 hpos
    by_contra hne
    have hpos : 0 < ‖c n‖ := norm_pos_iff.mpr hne
    set ε : ℝ := min 1 (‖c n‖ / (2 * (K + 1))) with hε
    have hε0 : 0 < ε := lt_min one_pos (by positivity)
    have hb := hbound ε hε0 (min_le_left _ _)
    have h1 : ε ≤ ‖c n‖ / (2 * (K + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith

/-- The shifted coefficient of `w^i G(w)`. -/
private def shiftCoeff (g : ℕ → ℂ) (i n : ℕ) : ℂ := if i ≤ n then g (n - i) else 0

private lemma hasSum_shift {g : ℕ → ℂ} {w G : ℂ} (hG : HasSum (fun k => g k * w ^ k) G) (i : ℕ) :
    HasSum (fun n => shiftCoeff g i n * w ^ n) (w ^ i * G) := by
  have hinj : Function.Injective fun k : ℕ => k + i := add_left_injective i
  have hf : ∀ x ∉ Set.range (fun k : ℕ => k + i), shiftCoeff g i x * w ^ x = 0 := by
    intro x hx
    have hlt : ¬ i ≤ x := fun hle => hx ⟨x - i, by simp only; omega⟩
    simp [shiftCoeff, hlt]
  refine (hinj.hasSum_iff hf).mp ?_
  have h := hG.mul_left (w ^ i)
  have hfun : ((fun n => shiftCoeff g i n * w ^ n) ∘ fun k : ℕ => k + i) =
      fun k => w ^ i * (g k * w ^ k) := by
    funext k
    simp only [Function.comp, shiftCoeff, Nat.le_add_left, if_true, Nat.add_sub_cancel, pow_add]
    ring
  rw [hfun]
  exact h

/-- The power series of a polynomial times a function. -/
private lemma hasSum_poly_mul {g : ℕ → ℂ} {w G : ℂ} (hG : HasSum (fun k => g k * w ^ k) G)
    (P : ℂ[X]) {D : ℕ} (hD : P.natDegree ≤ D) :
    HasSum (fun n => (∑ i ∈ range (D + 1), P.coeff i * shiftCoeff g i n) * w ^ n) (P.eval w * G) := by
  have hval : P.eval w * G = ∑ i ∈ range (D + 1), P.coeff i * (w ^ i * G) := by
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le hD), sum_mul]
    exact sum_congr rfl fun i _ => by ring
  rw [hval]
  have h : ∀ i ∈ range (D + 1), HasSum (fun n => P.coeff i * (shiftCoeff g i n * w ^ n))
      (P.coeff i * (w ^ i * G)) := fun i _ => (hasSum_shift hG i).mul_left _
  have hfun : (fun n => (∑ i ∈ range (D + 1), P.coeff i * shiftCoeff g i n) * w ^ n) =
      fun n => ∑ i ∈ range (D + 1), P.coeff i * (shiftCoeff g i n * w ^ n) := by
    funext n
    rw [sum_mul]
    exact sum_congr rfl fun i _ => by ring
  rw [hfun]
  exact hasSum_sum h

/-- Iterating the ratio: `f_{m+j}/f_m → 0` for every `j ≥ 1`. -/
private lemma tendsto_norm_div {f : ℕ → ℂ} (hf0 : ∀ k, f k ≠ 0)
    (hratio : Tendsto (fun k => ‖f (k + 1) / f k‖) atTop (𝓝 0)) (j : ℕ) (hj : 1 ≤ j) :
    Tendsto (fun m => ‖f (m + j) / f m‖) atTop (𝓝 0) := by
  induction j, hj using Nat.le_induction with
  | base => exact hratio
  | succ j hj ih =>
    have h1 : Tendsto (fun m => ‖f (m + j + 1) / f (m + j)‖) atTop (𝓝 0) :=
      hratio.comp (tendsto_add_atTop_nat j)
    have h2 := h1.mul ih
    rw [mul_zero] at h2
    refine h2.congr fun m => ?_
    rw [← norm_mul, ← add_assoc]
    congr 1
    field_simp [hf0 (m + j), hf0 m]

/-- **Independence of the three characters.** -/
private lemma eq_zero_of_tendsto_rotation {ϑ t a b : ℂ} (hn : ‖ϑ‖ = 1) (h1 : ϑ ≠ 1) (h2 : ϑ ≠ star ϑ)
    (hx : Tendsto (fun m : ℕ => t - a * ϑ ^ m - b * (star ϑ) ^ m) atTop (𝓝 0)) :
    t = 0 ∧ a = 0 ∧ b = 0 := by
  set x : ℕ → ℂ := fun m => t - a * ϑ ^ m - b * (star ϑ) ^ m with hxdef
  have hstar1 : star ϑ ≠ 1 := fun h => h1 (by simpa using congrArg star h)
  have hx1 : Tendsto (fun m => x (m + 1)) atTop (𝓝 0) := hx.comp (tendsto_add_atTop_nat 1)
  have hx2 : Tendsto (fun m => x (m + 2)) atTop (𝓝 0) := hx.comp (tendsto_add_atTop_nat 2)
  -- The constant term.
  have hz : Tendsto (fun m => x (m + 2) - (ϑ + star ϑ) * x (m + 1) + ϑ * star ϑ * x m) atTop (𝓝 0) := by
    have := (hx2.sub (hx1.const_mul (ϑ + star ϑ))).add (hx.const_mul (ϑ * star ϑ))
    simpa using this
  have hzconst : ∀ m, x (m + 2) - (ϑ + star ϑ) * x (m + 1) + ϑ * star ϑ * x m =
      t * (1 - ϑ) * (1 - star ϑ) := by
    intro m
    simp only [hxdef]
    ring
  simp only [hzconst] at hz
  have ht0 := tendsto_nhds_unique tendsto_const_nhds hz
  have ht : t = 0 := by
    rcases mul_eq_zero.mp ht0 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd (sub_eq_zero.mp h).symm h1
    · exact absurd (sub_eq_zero.mp h).symm hstar1
  -- The coefficient of `ϑ^m`.
  have hy : Tendsto (fun m => x (m + 1) - star ϑ * x m) atTop (𝓝 0) := by
    have := hx1.sub (hx.const_mul (star ϑ))
    simpa using this
  have hyval : ∀ m, ‖x (m + 1) - star ϑ * x m‖ = ‖a‖ * ‖ϑ - star ϑ‖ := by
    intro m
    have : x (m + 1) - star ϑ * x m = -(a * (ϑ - star ϑ)) * ϑ ^ m := by
      simp only [hxdef, ht]
      ring
    rw [this, norm_mul, norm_neg, norm_mul, norm_pow, hn, one_pow, mul_one]
  have ha0 : ‖a‖ * ‖ϑ - star ϑ‖ = 0 := by
    have h3 := hy.norm
    simp only [hyval, norm_zero] at h3
    exact tendsto_nhds_unique tendsto_const_nhds h3
  have hne : ‖ϑ - star ϑ‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h2)
  have ha : a = 0 := norm_eq_zero.mp ((mul_eq_zero.mp ha0).resolve_right hne)
  -- The coefficient of `ϑ̄^m`.
  have hxval : ∀ m, ‖x m‖ = ‖b‖ := by
    intro m
    have : x m = -(b * (star ϑ) ^ m) := by
      simp only [hxdef, ht, ha]
      ring
    rw [this, norm_neg, norm_mul, norm_pow, norm_star, hn, one_pow, mul_one]
  have hb0 : ‖b‖ = 0 := by
    have h3 := hx.norm
    simp only [hxval, norm_zero] at h3
    exact tendsto_nhds_unique tendsto_const_nhds h3
  exact ⟨ht, ha, norm_eq_zero.mp hb0⟩

/-- **A rotated relation with polynomial coefficients is trivial.** -/
theorem polynomial_rotated_relation_trivial {f : ℕ → ℂ} (hf0 : ∀ k, f k ≠ 0)
    (hratio : Tendsto (fun k => ‖f (k + 1) / f k‖) atTop (𝓝 0)) {F : ℂ → ℂ}
    (hF : ∀ w, HasSum (fun k => f k * w ^ k) (F w)) {ϑ : ℂ} (hn : ‖ϑ‖ = 1) (h1 : ϑ ≠ 1)
    (h2 : ϑ ≠ star ϑ) {T A B : ℂ[X]}
    (hrel : ∀ w, T.eval w * F w = A.eval w * F (ϑ * w) + B.eval w * F (star ϑ * w)) :
    T = 0 ∧ A = 0 ∧ B = 0 := by
  set D : ℕ := max T.natDegree (max A.natDegree B.natDegree) with hD
  have hTD : T.natDegree ≤ D := le_max_left _ _
  have hAD : A.natDegree ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hBD : B.natDegree ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  set gU : ℕ → ℂ := fun k => f k * ϑ ^ k with hgU
  set gV : ℕ → ℂ := fun k => f k * (star ϑ) ^ k with hgV
  have hU : ∀ w, HasSum (fun k => gU k * w ^ k) (F (ϑ * w)) := fun w => by
    have h := hF (ϑ * w)
    have hfun : (fun k => f k * (ϑ * w) ^ k) = fun k => gU k * w ^ k := by
      funext k
      simp only [hgU, mul_pow]
      ring
    rwa [hfun] at h
  have hV : ∀ w, HasSum (fun k => gV k * w ^ k) (F (star ϑ * w)) := fun w => by
    have h := hF (star ϑ * w)
    have hfun : (fun k => f k * (star ϑ * w) ^ k) = fun k => gV k * w ^ k := by
      funext k
      simp only [hgV, mul_pow]
      ring
    rwa [hfun] at h
  set C : ℕ → ℂ := fun n => ∑ i ∈ range (D + 1), T.coeff i * shiftCoeff f i n -
    ∑ i ∈ range (D + 1), A.coeff i * shiftCoeff gU i n -
    ∑ i ∈ range (D + 1), B.coeff i * shiftCoeff gV i n with hC
  have hzero : ∀ n, C n = 0 := by
    refine eq_zero_of_forall_hasSum_zero fun w => ?_
    have h3 := ((hasSum_poly_mul (hF w) T hTD).sub (hasSum_poly_mul (hU w) A hAD)).sub
      (hasSum_poly_mul (hV w) B hBD)
    have hval : T.eval w * F w - A.eval w * F (ϑ * w) - B.eval w * F (star ϑ * w) = 0 := by
      rw [hrel]
      ring
    rw [hval] at h3
    have hfun : (fun n => C n * w ^ n) = fun n =>
        (∑ i ∈ range (D + 1), T.coeff i * shiftCoeff f i n) * w ^ n -
        (∑ i ∈ range (D + 1), A.coeff i * shiftCoeff gU i n) * w ^ n -
        (∑ i ∈ range (D + 1), B.coeff i * shiftCoeff gV i n) * w ^ n := by
      funext n
      simp only [hC]
      ring
    rw [hfun]
    exact h3
  -- The bracket at each index.
  set bracket : ℕ → ℕ → ℂ := fun i e => T.coeff i - A.coeff i * ϑ ^ e - B.coeff i * (star ϑ) ^ e
    with hbracket
  have hbracket_le : ∀ i e, ‖bracket i e‖ ≤ ‖T.coeff i‖ + ‖A.coeff i‖ + ‖B.coeff i‖ := by
    intro i e
    have ha : ‖A.coeff i * ϑ ^ e‖ = ‖A.coeff i‖ := by rw [norm_mul, norm_pow, hn, one_pow, mul_one]
    have hb : ‖B.coeff i * (star ϑ) ^ e‖ = ‖B.coeff i‖ := by
      rw [norm_mul, norm_pow, norm_star, hn, one_pow, mul_one]
    calc ‖bracket i e‖ ≤ ‖T.coeff i - A.coeff i * ϑ ^ e‖ + ‖B.coeff i * (star ϑ) ^ e‖ := norm_sub_le _ _
      _ ≤ ‖T.coeff i‖ + ‖A.coeff i * ϑ ^ e‖ + ‖B.coeff i * (star ϑ) ^ e‖ := by
          gcongr
          exact norm_sub_le _ _
      _ = _ := by rw [ha, hb]
  have hexp : ∀ m, C (D + m) = ∑ i ∈ range (D + 1), f (D + m - i) * bracket i (D + m - i) := by
    intro m
    simp only [hC, ← sum_sub_distrib]
    refine sum_congr rfl fun i hi => ?_
    have hle : i ≤ D + m := by
      have := mem_range.mp hi
      omega
    simp only [shiftCoeff, if_pos hle, hgU, hgV, hbracket]
    ring
  -- The limit of the top bracket.
  have hlim : Tendsto (fun m => bracket D m) atTop (𝓝 0) := by
    set K : ℕ → ℝ := fun i => ‖T.coeff i‖ + ‖A.coeff i‖ + ‖B.coeff i‖ with hK
    have hR : Tendsto (fun m => ∑ i ∈ range D, ‖f (m + (D - i)) / f m‖ * K i) atTop (𝓝 0) := by
      have := tendsto_finsetSum (range D) (fun i hi =>
        (tendsto_norm_div hf0 hratio (D - i) (by have := mem_range.mp hi; omega)).mul_const (K i))
      simpa using this
    refine squeeze_zero_norm (fun m => ?_) hR
    have h4 := hzero (D + m)
    rw [hexp, sum_range_succ] at h4
    have hD' : D + m - D = m := by omega
    rw [hD'] at h4
    have h5 : bracket D m = -∑ i ∈ range D, (f (D + m - i) / f m) * bracket i (D + m - i) := by
      have hfm := hf0 m
      have h6 : f m * bracket D m = -∑ i ∈ range D, f (D + m - i) * bracket i (D + m - i) := by
        linear_combination h4
      have h7 : bracket D m = (f m)⁻¹ * (f m * bracket D m) := by field_simp
      rw [h7, h6, mul_neg, mul_sum, neg_inj]
      refine sum_congr rfl fun i _ => ?_
      field_simp
    rw [h5, norm_neg]
    refine (norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_)
    have hidx : D + m - i = m + (D - i) := by
      have := mem_range.mp hi
      omega
    rw [norm_mul, hidx]
    exact mul_le_mul_of_nonneg_left (hbracket_le i _) (norm_nonneg _)
  obtain ⟨ht, ha, hb⟩ := eq_zero_of_tendsto_rotation hn h1 h2 hlim
  -- From the top coefficients to the polynomials.
  by_cases hD0 : D = 0
  · have hT0 : T.natDegree = 0 := by omega
    have hA0 : A.natDegree = 0 := by omega
    have hB0 : B.natDegree = 0 := by omega
    rw [hD0] at ht ha hb
    refine ⟨?_, ?_, ?_⟩
    · rw [eq_C_of_natDegree_eq_zero hT0, ht, C_0]
    · rw [eq_C_of_natDegree_eq_zero hA0, ha, C_0]
    · rw [eq_C_of_natDegree_eq_zero hB0, hb, C_0]
  · exfalso
    have hcase : T.natDegree = D ∨ A.natDegree = D ∨ B.natDegree = D := by
      rcases max_choice T.natDegree (max A.natDegree B.natDegree) with h | h
      · exact Or.inl (by rw [hD, h])
      · rcases max_choice A.natDegree B.natDegree with h' | h'
        · exact Or.inr (Or.inl (by rw [hD, h, h']))
        · exact Or.inr (Or.inr (by rw [hD, h, h']))
    rcases hcase with h | h | h
    · have hl : T.leadingCoeff = 0 := by rw [leadingCoeff, h]; exact ht
      rw [leadingCoeff_eq_zero.mp hl, natDegree_zero] at h
      exact hD0 h.symm
    · have hl : A.leadingCoeff = 0 := by rw [leadingCoeff, h]; exact ha
      rw [leadingCoeff_eq_zero.mp hl, natDegree_zero] at h
      exact hD0 h.symm
    · have hl : B.leadingCoeff = 0 := by rw [leadingCoeff, h]; exact hb
      rw [leadingCoeff_eq_zero.mp hl, natDegree_zero] at h
      exact hD0 h.symm

end GaloisForLFunctions.RigidArithmeticOfCuts
