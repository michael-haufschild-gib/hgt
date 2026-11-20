import Mathlib
import GaloisForLFunctions.WindowedLandauTheory.TheBalanceIdentity
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# Increment bounds for the Cesàro functionals

Two Lipschitz estimates for the Cesàro functionals `G_ψ` of host characters, from Chebyshev's
bound `Σ_{n ≤ y} Λ(n) ≤ 6y` and Mertens' bound `|Σ_{n ≤ N} Λ(n)/n - log N| ≤ log 4 + 4`:

* in the weight (`norm_mul_classCesaro_sub_le`): `‖w G_ψ(A/w) - w' G_ψ(A/w')‖ ≤ 7A/w · (w' - w)` for
  `0 < w ≤ w'`; the ramp `Σ c_n (A/n - w)⁺` moves by at most `(w' - w) Σ_{n ≤ A/w} Λ(n)`;
* in the point (`norm_classCesaro_sub_le`, `abs_zetaCesaroFunctional_sub_le`): for `|y - x| ≤ 1`,
  `‖G_ψ(y) - G_ψ(x)‖ ≤ log(x+1) + log 4 + 4 + ‖ℓ(ψ)‖` when `ψ ≠ 0`, and
  `|G_ζ(y) - G_ζ(x)| ≤ log 4 + 7`.
-/

open Finset ArithmeticFunction

namespace WindowedLandauTheory

noncomputable section

section Increments

variable {H : Type} [AddCommGroup H] [Fintype H]

open Classical in
theorem norm_cosetAverage_le (I : AddSubgroup (SignPair × H)) (h : SignPair × H) (ψ : AddChar (SignPair × H) ℂ) : ‖cosetAverage I h ψ‖ ≤ 1 := by
  unfold cosetAverage
  have hc : (0 : ℝ) < ((univ.filter (· ∈ I)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 ⟨0, by simp⟩
  rw [norm_div, Complex.norm_natCast, div_le_one hc]
  calc ‖∑ x ∈ univ.filter (· ∈ I), ψ (h + x)‖ ≤ ∑ x ∈ univ.filter (· ∈ I), ‖ψ (h + x)‖ :=
        norm_sum_le _ _
    _ = ((univ.filter (· ∈ I)).card : ℝ) := by simp [AddChar.norm_apply]

theorem norm_classValue_le (D : FrobeniusData H) (ψ : AddChar (SignPair × H) ℂ) (n : ℕ) :
    ‖classValue D ψ n‖ ≤ 1 := by
  unfold classValue
  rw [norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun p _ => norm_cosetAverage_le _ _ _

end Increments

/-! ## Chebyshev and Mertens -/

theorem sum_Icc_vonMangoldt_le {y : ℝ} (hy : 0 ≤ y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, vonMangoldt n ≤ 6 * y := by
  have h1 : ∑ n ∈ Icc 1 ⌊y⌋₊, vonMangoldt n = Chebyshev.psi y := by
    rw [Chebyshev.psi_eq_sum_Icc]
    refine Finset.sum_subset (fun n hn => ?_) (fun n hn hn' => ?_)
    · simp only [Finset.mem_Icc] at hn ⊢
      omega
    · have h0 : n = 0 := by
        simp only [Finset.mem_Icc] at hn hn'
        omega
      subst h0
      simp
  have hlog : Real.log 4 + 4 ≤ 6 := by
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h4]
    linarith [Real.log_two_lt_d9]
  rw [h1]
  exact (Chebyshev.psi_le_const_mul_self hy).trans (mul_le_mul_of_nonneg_right hlog hy)

/-- Mertens, upper form at a real point: `Σ_{n ≤ y} Λ(n)/n ≤ log y + log 4 + 4` for `y ≥ 1`. -/
theorem sum_Icc_vonMangoldt_div_le {y : ℝ} (hy : 1 ≤ y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, vonMangoldt n / n ≤ Real.log y + (Real.log 4 + 4) := by
  have hN : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
  have h := (abs_le.1 (RHTower.Mertens.mertens_first ⌊y⌋₊ hN)).2
  have hfl : Real.log ⌊y⌋₊ ≤ Real.log y :=
    Real.log_le_log (by exact_mod_cast hN) (Nat.floor_le (by linarith))
  linarith

/-- Mertens, lower form at a real point: `log y - log 2 - (log 4 + 4) ≤ Σ_{n ≤ y} Λ(n)/n`. -/
theorem le_sum_Icc_vonMangoldt_div {y : ℝ} (hy : 1 ≤ y) :
    Real.log y - Real.log 2 - (Real.log 4 + 4) ≤ ∑ n ∈ Icc 1 ⌊y⌋₊, vonMangoldt n / n := by
  have hN : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
  have h := (abs_le.1 (RHTower.Mertens.mertens_first ⌊y⌋₊ hN)).1
  have hfl : y / 2 ≤ ⌊y⌋₊ := by
    have := Nat.lt_floor_add_one y
    have h1 : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hN
    linarith
  have hlog : Real.log y - Real.log 2 ≤ Real.log ⌊y⌋₊ := by
    rw [← Real.log_div (by linarith) (by norm_num)]
    exact Real.log_le_log (by linarith) hfl
  linarith

/-! ## Splitting a range of summation -/

theorem sum_Icc_eq_add_filter {M : Type*} [AddCommMonoid M] (f : ℕ → M) {m k : ℕ}
    (hmk : m ≤ k) :
    ∑ n ∈ Icc 1 k, f n = ∑ n ∈ Icc 1 m, f n + ∑ n ∈ (Icc 1 k).filter (m < ·), f n := by
  rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 k) (· ≤ m)]
  congr 1
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, not_le]

/-! ## Ramps in the point -/

/-- The ramp `Σ_{n ≤ y} c_n (y/n - 1)` moves by at most `(y - z) Σ_{n ≤ y} Λ(n)/n` when
`‖c_n‖ ≤ Λ(n)` and `0 ≤ z ≤ y`. -/
theorem norm_ramp_sub_le (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ vonMangoldt n) {z y : ℝ} (hz : 0 ≤ z)
    (hzy : z ≤ y) :
    ‖∑ n ∈ Icc 1 ⌊y⌋₊, c n * ((y / n - 1 : ℝ) : ℂ) -
        ∑ n ∈ Icc 1 ⌊z⌋₊, c n * ((z / n - 1 : ℝ) : ℂ)‖ ≤
      (y - z) * ∑ n ∈ Icc 1 ⌊y⌋₊, vonMangoldt n / n := by
  have hfl : ⌊z⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hzy
  rw [sum_Icc_eq_add_filter _ hfl]
  have e : ∑ n ∈ Icc 1 ⌊z⌋₊, c n * ((y / n - 1 : ℝ) : ℂ) +
      ∑ n ∈ (Icc 1 ⌊y⌋₊).filter (⌊z⌋₊ < ·), c n * ((y / n - 1 : ℝ) : ℂ) -
      ∑ n ∈ Icc 1 ⌊z⌋₊, c n * ((z / n - 1 : ℝ) : ℂ) =
      ∑ n ∈ Icc 1 ⌊z⌋₊, c n * (((y - z) / n : ℝ) : ℂ) +
      ∑ n ∈ (Icc 1 ⌊y⌋₊).filter (⌊z⌋₊ < ·), c n * ((y / n - 1 : ℝ) : ℂ) := by
    rw [add_sub_right_comm, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← mul_sub]
    congr 1
    push_cast
    ring
  rw [e]
  have b1 : ∀ n ∈ Icc 1 ⌊z⌋₊, ‖c n * (((y - z) / n : ℝ) : ℂ)‖ ≤ (y - z) * (vonMangoldt n / n) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by
      have := (Finset.mem_Icc.1 hn).1
      exact_mod_cast this
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (by linarith) hn0.le)]
    calc ‖c n‖ * ((y - z) / n) ≤ vonMangoldt n * ((y - z) / n) :=
          mul_le_mul_of_nonneg_right (hc n) (div_nonneg (by linarith) hn0.le)
      _ = (y - z) * (vonMangoldt n / n) := by ring
  have b2 : ∀ n ∈ (Icc 1 ⌊y⌋₊).filter (⌊z⌋₊ < ·), ‖c n * ((y / n - 1 : ℝ) : ℂ)‖ ≤
      (y - z) * (vonMangoldt n / n) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_filter.1 hn
    have hn0 : (0 : ℝ) < n := by
      have := (Finset.mem_Icc.1 hn1).1
      exact_mod_cast this
    have hny : (n : ℝ) ≤ y := (Nat.cast_le.2 (Finset.mem_Icc.1 hn1).2).trans (Nat.floor_le (hz.trans hzy))
    have hnz : z < n := (Nat.floor_lt hz).1 hn2
    have h0 : 0 ≤ y / n - 1 := by
      rw [sub_nonneg, le_div_iff₀ hn0, one_mul]
      exact hny
    have h1 : y / n - 1 ≤ (y - z) / n := by
      rw [div_sub_one hn0.ne', div_le_div_iff_of_pos_right hn0]
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
    calc ‖c n‖ * (y / n - 1) ≤ vonMangoldt n * ((y - z) / n) :=
          mul_le_mul (hc n) h1 h0 vonMangoldt_nonneg
      _ = (y - z) * (vonMangoldt n / n) := by ring
  calc _ ≤ ‖∑ n ∈ Icc 1 ⌊z⌋₊, c n * (((y - z) / n : ℝ) : ℂ)‖ +
        ‖∑ n ∈ (Icc 1 ⌊y⌋₊).filter (⌊z⌋₊ < ·), c n * ((y / n - 1 : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ ∑ n ∈ Icc 1 ⌊z⌋₊, (y - z) * (vonMangoldt n / n) +
        ∑ n ∈ (Icc 1 ⌊y⌋₊).filter (⌊z⌋₊ < ·), (y - z) * (vonMangoldt n / n) :=
        add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum b1))
          ((norm_sum_le _ _).trans (Finset.sum_le_sum b2))
    _ = (y - z) * ∑ n ∈ Icc 1 ⌊y⌋₊, vonMangoldt n / n := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add, ← sum_Icc_eq_add_filter _ hfl]

/-- For the von Mangoldt ramp `S(y) = Σ_{n ≤ y} Λ(n)(y/n - 1)` and `0 ≤ z ≤ y`:
`(y - z) Σ_{n ≤ z} Λ(n)/n ≤ S(y) - S(z)`. -/
theorem le_vonMangoldtRamp_sub {z y : ℝ} (hz : 0 ≤ z) (hzy : z ≤ y) :
    (y - z) * ∑ n ∈ Icc 1 ⌊z⌋₊, vonMangoldt n / n ≤
      ∑ n ∈ Icc 1 ⌊y⌋₊, vonMangoldt n * (y / n - 1) -
        ∑ n ∈ Icc 1 ⌊z⌋₊, vonMangoldt n * (z / n - 1) := by
  have hfl : ⌊z⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hzy
  rw [sum_Icc_eq_add_filter _ hfl]
  have h2 : 0 ≤ ∑ n ∈ (Icc 1 ⌊y⌋₊).filter (⌊z⌋₊ < ·), vonMangoldt n * (y / n - 1) := by
    refine Finset.sum_nonneg fun n hn => mul_nonneg vonMangoldt_nonneg ?_
    obtain ⟨hn1, _⟩ := Finset.mem_filter.1 hn
    have hn0 : (0 : ℝ) < n := by
      have := (Finset.mem_Icc.1 hn1).1
      exact_mod_cast this
    have hny : (n : ℝ) ≤ y := (Nat.cast_le.2 (Finset.mem_Icc.1 hn1).2).trans (Nat.floor_le (hz.trans hzy))
    rw [sub_nonneg, le_div_iff₀ hn0, one_mul]
    exact hny
  have h1 : (y - z) * ∑ n ∈ Icc 1 ⌊z⌋₊, vonMangoldt n / n =
      ∑ n ∈ Icc 1 ⌊z⌋₊, vonMangoldt n * (y / n - 1) - ∑ n ∈ Icc 1 ⌊z⌋₊, vonMangoldt n * (z / n - 1) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  linarith

/-! ## Ramps in the weight -/

/-- The weighted ramp `Σ_{n ≤ A/w} c_n (A/n - w)` moves by at most `(w' - w) Σ_{n ≤ A/w} Λ(n)` when
`‖c_n‖ ≤ Λ(n)` and `0 < w ≤ w'`. -/
theorem norm_weightRamp_sub_le (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ vonMangoldt n) {A w w' : ℝ}
    (hA : 0 ≤ A) (hw : 0 < w) (hww : w ≤ w') :
    ‖∑ n ∈ Icc 1 ⌊A / w⌋₊, c n * ((A / n - w : ℝ) : ℂ) -
        ∑ n ∈ Icc 1 ⌊A / w'⌋₊, c n * ((A / n - w' : ℝ) : ℂ)‖ ≤
      (w' - w) * ∑ n ∈ Icc 1 ⌊A / w⌋₊, vonMangoldt n := by
  have hw' : 0 < w' := hw.trans_le hww
  have hdiv : A / w' ≤ A / w := div_le_div_of_nonneg_left hA hw hww
  have hfl : ⌊A / w'⌋₊ ≤ ⌊A / w⌋₊ := Nat.floor_le_floor hdiv
  rw [sum_Icc_eq_add_filter _ hfl]
  have e : ∑ n ∈ Icc 1 ⌊A / w'⌋₊, c n * ((A / n - w : ℝ) : ℂ) +
      ∑ n ∈ (Icc 1 ⌊A / w⌋₊).filter (⌊A / w'⌋₊ < ·), c n * ((A / n - w : ℝ) : ℂ) -
      ∑ n ∈ Icc 1 ⌊A / w'⌋₊, c n * ((A / n - w' : ℝ) : ℂ) =
      ∑ n ∈ Icc 1 ⌊A / w'⌋₊, c n * ((w' - w : ℝ) : ℂ) +
      ∑ n ∈ (Icc 1 ⌊A / w⌋₊).filter (⌊A / w'⌋₊ < ·), c n * ((A / n - w : ℝ) : ℂ) := by
    rw [add_sub_right_comm, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← mul_sub]
    congr 1
    push_cast
    ring
  rw [e]
  have b1 : ∀ n ∈ Icc 1 ⌊A / w'⌋₊, ‖c n * ((w' - w : ℝ) : ℂ)‖ ≤ (w' - w) * vonMangoldt n := by
    intro n _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), mul_comm]
    exact mul_le_mul_of_nonneg_left (hc n) (by linarith)
  have b2 : ∀ n ∈ (Icc 1 ⌊A / w⌋₊).filter (⌊A / w'⌋₊ < ·), ‖c n * ((A / n - w : ℝ) : ℂ)‖ ≤
      (w' - w) * vonMangoldt n := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_filter.1 hn
    have hn0 : (0 : ℝ) < n := by
      have := (Finset.mem_Icc.1 hn1).1
      exact_mod_cast this
    have hnA : (n : ℝ) ≤ A / w :=
      (Nat.cast_le.2 (Finset.mem_Icc.1 hn1).2).trans (Nat.floor_le (div_nonneg hA hw.le))
    have hnA' : A / w' < n := (Nat.floor_lt (div_nonneg hA hw'.le)).1 hn2
    have h0 : 0 ≤ A / n - w := by
      rw [sub_nonneg, le_div_iff₀ hn0]
      rw [le_div_iff₀ hw] at hnA
      linarith
    have h1 : A / n - w ≤ w' - w := by
      have : A / n < w' := by
        rw [div_lt_iff₀ hn0]
        rw [div_lt_iff₀ hw'] at hnA'
        linarith
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0, mul_comm]
    exact mul_le_mul h1 (hc n) (norm_nonneg _) (by linarith)
  calc _ ≤ ‖∑ n ∈ Icc 1 ⌊A / w'⌋₊, c n * ((w' - w : ℝ) : ℂ)‖ +
        ‖∑ n ∈ (Icc 1 ⌊A / w⌋₊).filter (⌊A / w'⌋₊ < ·), c n * ((A / n - w : ℝ) : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ ∑ n ∈ Icc 1 ⌊A / w'⌋₊, (w' - w) * vonMangoldt n +
        ∑ n ∈ (Icc 1 ⌊A / w⌋₊).filter (⌊A / w'⌋₊ < ·), (w' - w) * vonMangoldt n :=
        add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum b1))
          ((norm_sum_le _ _).trans (Finset.sum_le_sum b2))
    _ = (w' - w) * ∑ n ∈ Icc 1 ⌊A / w⌋₊, vonMangoldt n := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add, ← sum_Icc_eq_add_filter _ hfl]

end

end WindowedLandauTheory
