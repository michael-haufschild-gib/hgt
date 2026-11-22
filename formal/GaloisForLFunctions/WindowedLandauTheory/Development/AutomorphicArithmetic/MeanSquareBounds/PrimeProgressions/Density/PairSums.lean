import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.Definitions
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.ZeroDensity.TwistedPairs
import GaloisForLFunctions.RHTower.DirichletCharacterPartialSumBound
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HyperbolaSumsOfAVonMangoldtTail

/-! Pairs of characters and pairs of separated ordinates give distinct correlation bounds. -/

open Complex Finset

noncomputable section

namespace QH.PrimeProgressions.Density

open QH.ZeroDensity

private lemma norm_cpow_neg_sub_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) {w : ℂ}
    (hw : 0 ≤ w.re) : ‖(b : ℂ) ^ (-w) - (a : ℂ) ^ (-w)‖ ≤ ‖w‖ * ((b - a) / a) := by
  rcases eq_or_ne w 0 with rfl | hw0
  · simp
  have h := QH.norm_cpow_increment_le (ρ := -w) (neg_ne_zero.mpr hw0)
    (z := a) (h := b - a) (σ := 0) ha (sub_nonneg.mpr hab) zero_le_one
    (by simpa using neg_nonpos.mpr hw)
  rw [show a + (b - a) = b by ring, norm_neg, zero_sub, Real.rpow_neg_one] at h
  calc _ ≤ ‖w‖ * a⁻¹ * (b - a) := h
    _ = _ := by ring

lemma norm_cpow_step_le' {i U : ℕ} (hU : 1 ≤ U) (hi : U ≤ i) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖(((i + 1 : ℕ) : ℂ) ^ (-w) - (i : ℂ) ^ (-w))‖ ≤ ‖w‖ / U := by
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (by omega : 1 ≤ i)
  have h := norm_cpow_neg_sub_le (a := i) (b := (i : ℝ) + 1) hi1 (by linarith) hw
  have e1 : (((i : ℝ) : ℂ)) = (i : ℂ) := by push_cast; rfl
  have e2 : ((((i : ℝ) + 1 : ℝ)) : ℂ) = ((i + 1 : ℕ) : ℂ) := by push_cast; rfl
  rw [e1, e2] at h
  refine h.trans ?_
  have hUi : (U : ℝ) ≤ i := by exact_mod_cast hi
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have : ((i : ℝ) + 1 - i) / i ≤ 1 / U := by
    rw [add_sub_cancel_left]
    exact one_div_le_one_div_of_le hU0 hUi
  calc ‖w‖ * (((i : ℝ) + 1 - i) / i) ≤ ‖w‖ * (1 / U) :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = ‖w‖ / U := by ring

lemma norm_sum_twist_le (g : ℕ → ℂ) {m : ℝ} (hGs : ∀ k, ‖∑ i ∈ range k, g i‖ ≤ m) {w : ℂ}
    (hw : 0 ≤ w.re) {U : ℕ} (hU : 1 ≤ U) :
    ‖∑ n ∈ Ioc U (2 * U), g n * (n : ℂ) ^ (-w)‖ ≤ 2 * m * (1 + ‖w‖) := by
  set f : ℕ → ℂ := fun n => (n : ℂ) ^ (-w) with hf
  have hm0 : 0 ≤ m := (norm_nonneg _).trans (hGs 0)
  have hrw : ∑ n ∈ Ioc U (2 * U), g n * (n : ℂ) ^ (-w) = ∑ n ∈ Ioc U (2 * U), f n • g n := by
    refine sum_congr rfl (fun n _ => ?_); simp only [hf, smul_eq_mul]; ring
  rw [hrw, Finset.sum_Ioc_by_parts f g (by omega : U < 2 * U)]
  have hb1 : ‖f (2 * U) • ∑ i ∈ range (2 * U + 1), g i‖ ≤ m := by
    rw [smul_eq_mul, norm_mul]
    calc ‖f (2 * U)‖ * ‖∑ i ∈ range (2 * U + 1), g i‖ ≤ 1 * m :=
          mul_le_mul (QH.ZeroDensity.norm_cpow_neg_le_one (by omega) hw) (hGs _) (norm_nonneg _) zero_le_one
      _ = m := one_mul m
  have hb2 : ‖f (U + 1) • ∑ i ∈ range (U + 1), g i‖ ≤ m := by
    rw [smul_eq_mul, norm_mul]
    calc ‖f (U + 1)‖ * ‖∑ i ∈ range (U + 1), g i‖ ≤ 1 * m :=
          mul_le_mul (norm_natCast_cpow_neg_le_one (by omega) hw) (hGs _) (norm_nonneg _) zero_le_one
      _ = m := one_mul m
  have hb3 : ‖∑ i ∈ Ioc U (2 * U - 1), (f (i + 1) - f i) • ∑ k ∈ range (i + 1), g k‖ ≤ m * ‖w‖ := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ Ioc U (2 * U - 1),
        ‖(f (i + 1) - f i) • ∑ k ∈ range (i + 1), g k‖ ≤ ‖w‖ / U * m := by
      intro i hi
      rw [smul_eq_mul, norm_mul]
      have hi' : U ≤ i := by have := (mem_Ioc.1 hi).1; omega
      exact mul_le_mul (norm_cpow_step_le' hU hi' hw) (hGs _) (norm_nonneg _) (by positivity)
    refine (sum_le_sum hterm).trans ?_
    rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]
    have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
    have hcnt : ((2 * U - 1 - U : ℕ) : ℝ) ≤ U := by exact_mod_cast (by omega : 2 * U - 1 - U ≤ U)
    calc ((2 * U - 1 - U : ℕ) : ℝ) * (‖w‖ / U * m) ≤ U * (‖w‖ / U * m) :=
          mul_le_mul_of_nonneg_right hcnt (by positivity)
      _ = m * ‖w‖ := by field_simp
  calc ‖f (2 * U) • ∑ i ∈ range (2 * U + 1), g i - f (U + 1) • ∑ i ∈ range (U + 1), g i -
        ∑ i ∈ Ioc U (2 * U - 1), (f (i + 1) - f i) • ∑ k ∈ range (i + 1), g k‖
      ≤ m + m + m * ‖w‖ := by
        refine (norm_sub_le _ _).trans ?_
        refine add_le_add ((norm_sub_le _ _).trans (add_le_add hb1 hb2)) hb3
    _ ≤ 2 * m * (1 + ‖w‖) := by nlinarith [norm_nonneg w]

theorem pair_cross_bound : PairCross := by
  intro M _ ψ hψ w hw U hU
  have h := norm_sum_twist_le (fun n => ψ (n : ZMod M)) (m := (M : ℝ))
    (fun k => RHTower.norm_dirichletCharacter_sum_range_le ψ hψ k) hw hU
  refine h.trans ?_
  have : (0 : ℝ) ≤ M := by positivity
  nlinarith [norm_nonneg w]

lemma norm_sum_range_periodic_le {M : ℕ} [NeZero M] (h : ZMod M → ℂ) {K : ℝ} (hK : ∀ a, ‖h a‖ ≤ K)
    (h0 : ∑ a : ZMod M, h a = 0) (k : ℕ) : ‖∑ n ∈ range k, h (n : ZMod M)‖ ≤ K * M := by
  have hq : ∑ n ∈ range M, h (n : ZMod M) = 0 := by
    rw [← h0]
    refine Finset.sum_bij' (fun n _ => (n : ZMod M)) (fun a _ => a.val) ?_ ?_ ?_ ?_ ?_
    · intro n _; exact Finset.mem_univ _
    · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
    · intro n hn; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hn)
    · intro a _; exact ZMod.natCast_zmod_val a
    · intro n _; rfl
  have hper (n : ℕ) : h ((n + M : ℕ) : ZMod M) = h (n : ZMod M) := by push_cast; simp
  calc ‖∑ n ∈ range k, h (n : ZMod M)‖ ≤ ∑ n ∈ range M, ‖h (n : ZMod M)‖ :=
      GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.norm_sum_range_periodic_le
        (NeZero.pos M) hper hq k
    _ ≤ ∑ _ ∈ range M, K := sum_le_sum (fun n _ => hK n)
    _ = K * M := by simp [mul_comm]

lemma norm_cpow_sub_prim_le {i : ℕ} (hi : 1 ≤ i) {w : ℂ} (hw : 0 ≤ w.re) (hw1 : 1 - w ≠ 0) :
    ‖((i + 1 : ℕ) : ℂ) ^ (-w) - (((i + 1 : ℕ) : ℂ) ^ (1 - w) - (i : ℂ) ^ (1 - w)) / (1 - w)‖ ≤
      ‖w‖ / i := by
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hi0 : (0 : ℝ) < i := by linarith
  have hle : (i : ℝ) ≤ (i : ℝ) + 1 := by linarith
  have h0 : (0 : ℝ) ∉ Set.uIcc (i : ℝ) ((i : ℝ) + 1) := by
    rw [Set.uIcc_of_le hle]; intro h; linarith [h.1]
  have hr : -w ≠ -1 := by
    intro h; apply hw1; linear_combination h
  have hint := integral_cpow (a := (i : ℝ)) (b := (i : ℝ) + 1) (r := -w) (Or.inr ⟨hr, h0⟩)
  have e : -w + 1 = 1 - w := by ring
  have e1 : (((i : ℝ) : ℂ)) = (i : ℂ) := by push_cast; rfl
  have e2 : ((((i : ℝ) + 1 : ℝ)) : ℂ) = ((i + 1 : ℕ) : ℂ) := by push_cast; rfl
  rw [e, e1, e2] at hint
  set c : ℂ := ((i + 1 : ℕ) : ℂ) ^ (-w) with hc
  have hconst : ∫ _x : ℝ in (i : ℝ)..((i : ℝ) + 1), c = c := by
    rw [intervalIntegral.integral_const]; simp
  have hsub : c - (((i + 1 : ℕ) : ℂ) ^ (1 - w) - (i : ℂ) ^ (1 - w)) / (1 - w) =
      ∫ x : ℝ in (i : ℝ)..((i : ℝ) + 1), (c - (x : ℂ) ^ (-w)) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegral.intervalIntegrable_cpow (Or.inr h0)), hconst, hint]
  rw [hsub]
  have hb : ∀ x ∈ Set.uIoc (i : ℝ) ((i : ℝ) + 1), ‖c - (x : ℂ) ^ (-w)‖ ≤ ‖w‖ / i := by
    intro x hx
    rw [Set.uIoc_of_le hle] at hx
    have hx1 : 1 ≤ x := by linarith [hx.1]
    have hx0 : 0 < x := by linarith
    have h := norm_cpow_neg_sub_le (a := x) (b := (i : ℝ) + 1) hx1 hx.2 hw
    rw [e2] at h
    refine h.trans ?_
    have : ((i : ℝ) + 1 - x) / x ≤ 1 / i :=
      div_le_div₀ zero_le_one (by linarith [hx.1]) hi0 hx.1.le
    calc ‖w‖ * (((i : ℝ) + 1 - x) / x) ≤ ‖w‖ * (1 / i) :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = ‖w‖ / i := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa using this

lemma norm_sum_cpow_sub_prim_le {U : ℕ} (hU : 1 ≤ U) {w : ℂ} (hw : 0 ≤ w.re) (hw1 : 1 - w ≠ 0)
    (V : ℕ) (hV : U ≤ V) :
    ‖∑ n ∈ Ioc U V, (n : ℂ) ^ (-w) - ((V : ℂ) ^ (1 - w) - (U : ℂ) ^ (1 - w)) / (1 - w)‖ ≤
      ((V : ℝ) - U) * (‖w‖ / U) := by
  induction V, hV using Nat.le_induction with
  | base => simp
  | succ V hV ih =>
    have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
    rw [Finset.sum_Ioc_succ_top (by omega : U ≤ V)]
    have hstep := norm_cpow_sub_prim_le (i := V) (by omega) hw hw1
    have hstep' : ‖((V + 1 : ℕ) : ℂ) ^ (-w) -
        (((V + 1 : ℕ) : ℂ) ^ (1 - w) - (V : ℂ) ^ (1 - w)) / (1 - w)‖ ≤ ‖w‖ / U := by
      refine hstep.trans ?_
      exact div_le_div_of_nonneg_left (norm_nonneg _) hU0 (by exact_mod_cast hV)
    have hsplit : ∑ n ∈ Ioc U V, (n : ℂ) ^ (-w) + ((V + 1 : ℕ) : ℂ) ^ (-w) -
        (((V + 1 : ℕ) : ℂ) ^ (1 - w) - (U : ℂ) ^ (1 - w)) / (1 - w) =
        (∑ n ∈ Ioc U V, (n : ℂ) ^ (-w) - ((V : ℂ) ^ (1 - w) - (U : ℂ) ^ (1 - w)) / (1 - w)) +
        (((V + 1 : ℕ) : ℂ) ^ (-w) -
          (((V + 1 : ℕ) : ℂ) ^ (1 - w) - (V : ℂ) ^ (1 - w)) / (1 - w)) := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ((add_le_add ih hstep').trans (le_of_eq ?_))
    push_cast; ring

lemma norm_prim_dyadic_le {U : ℕ} (hU : 1 ≤ U) {w : ℂ} (hw : 0 ≤ w.re) (ht : w.im ≠ 0) :
    ‖(((2 * U : ℕ) : ℂ) ^ (1 - w) - (U : ℂ) ^ (1 - w)) / (1 - w)‖ ≤
      3 * (U : ℝ) ^ (1 - w.re) / |w.im| := by
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hre : (1 - w).re = 1 - w.re := by simp
  have hP : 0 < (U : ℝ) ^ (1 - w.re) := Real.rpow_pos_of_pos hU0 _
  have h1 : ‖(U : ℂ) ^ (1 - w)‖ = (U : ℝ) ^ (1 - w.re) := by
    rw [norm_natCast_cpow_of_pos (by omega), hre]
  have h2 : ‖((2 * U : ℕ) : ℂ) ^ (1 - w)‖ ≤ 2 * (U : ℝ) ^ (1 - w.re) := by
    rw [norm_natCast_cpow_of_pos (by omega), hre]
    push_cast
    rw [Real.mul_rpow (by norm_num) hU0.le]
    refine mul_le_mul_of_nonneg_right ?_ hP.le
    calc (2 : ℝ) ^ (1 - w.re) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have h3 : |w.im| ≤ ‖1 - w‖ := by
    have := Complex.abs_im_le_norm (1 - w)
    simpa using this
  have ht0 : 0 < |w.im| := abs_pos.mpr ht
  rw [norm_div]
  refine div_le_div₀ (by positivity) ?_ ht0 h3
  refine (norm_sub_le _ _).trans ?_
  rw [h1]; linarith

theorem pair_same_bound : PairSame := by
  intro M _ w hw hw1 ht U hU
  have hM0 : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have h1w : 1 - w ≠ 0 := by
    intro h; apply ht
    have := congrArg Complex.im h
    simpa using this
  set c : ℂ := (Fintype.card (ZMod M)ˣ : ℂ) / (M : ℂ) with hc
  have hcn : ‖c‖ ≤ 1 := by
    rw [hc, norm_div, Complex.norm_natCast, Complex.norm_natCast, div_le_one hM0,
      ZMod.card_units_eq_totient]
    exact_mod_cast Nat.totient_le M
  set h : ZMod M → ℂ := fun a => (1 : DirichletCharacter ℂ M) a - c with hh
  have hK : ∀ a, ‖h a‖ ≤ 2 := by
    intro a
    refine (norm_sub_le _ _).trans ?_
    have := DirichletCharacter.norm_le_one (1 : DirichletCharacter ℂ M) a
    linarith
  have hsum0 : ∑ a : ZMod M, h a = 0 := by
    simp only [hh]
    rw [Finset.sum_sub_distrib, MulChar.sum_one_eq_card_units, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, hc]
    have : (M : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
    field_simp
    ring
  have hA := norm_sum_twist_le (fun n => h (n : ZMod M)) (m := 2 * (M : ℝ))
    (fun k => norm_sum_range_periodic_le h hK hsum0 k) hw hU
  have hB := norm_sum_cpow_sub_prim_le hU hw h1w (2 * U) (by omega)
  have hC := norm_prim_dyadic_le hU hw ht
  have hB' : ((((2 * U : ℕ) : ℝ)) - U) * (‖w‖ / U) = ‖w‖ := by
    push_cast; field_simp; ring
  rw [hB'] at hB
  have hS : ‖∑ n ∈ Ioc U (2 * U), (n : ℂ) ^ (-w)‖ ≤ ‖w‖ + 3 * (U : ℝ) ^ (1 - w.re) / |w.im| := by
    have := norm_add_le (∑ n ∈ Ioc U (2 * U), (n : ℂ) ^ (-w) -
      (((2 * U : ℕ) : ℂ) ^ (1 - w) - (U : ℂ) ^ (1 - w)) / (1 - w))
      ((((2 * U : ℕ) : ℂ) ^ (1 - w) - (U : ℂ) ^ (1 - w)) / (1 - w))
    rw [sub_add_cancel] at this
    linarith
  have hsplit : ∑ n ∈ Ioc U (2 * U), (1 : DirichletCharacter ℂ M) (n : ZMod M) * (n : ℂ) ^ (-w) =
      ∑ n ∈ Ioc U (2 * U), h (n : ZMod M) * (n : ℂ) ^ (-w) +
        c * ∑ n ∈ Ioc U (2 * U), (n : ℂ) ^ (-w) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [hh]; ring
  rw [hsplit]
  have hQ : 0 ≤ (U : ℝ) ^ (1 - w.re) / |w.im| := by positivity
  have hcS : ‖c * ∑ n ∈ Ioc U (2 * U), (n : ℂ) ^ (-w)‖ ≤
      ‖w‖ + 3 * (U : ℝ) ^ (1 - w.re) / |w.im| := by
    rw [norm_mul]
    calc ‖c‖ * ‖∑ n ∈ Ioc U (2 * U), (n : ℂ) ^ (-w)‖
        ≤ 1 * (‖w‖ + 3 * (U : ℝ) ^ (1 - w.re) / |w.im|) :=
          mul_le_mul hcn hS (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  refine (norm_add_le _ _).trans ((add_le_add hA hcS).trans ?_)
  have e3 : 3 * (U : ℝ) ^ (1 - w.re) / |w.im| = 3 * ((U : ℝ) ^ (1 - w.re) / |w.im|) := by ring
  have e4 : 4 * (U : ℝ) ^ (1 - w.re) / |w.im| = 4 * ((U : ℝ) ^ (1 - w.re) / |w.im|) := by ring
  rw [e3, e4]
  nlinarith [norm_nonneg w]

end QH.PrimeProgressions.Density
