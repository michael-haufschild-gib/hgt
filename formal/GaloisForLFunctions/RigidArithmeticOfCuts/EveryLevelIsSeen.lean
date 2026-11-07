import GaloisForLFunctions.RigidArithmeticOfCuts.TheQuadraticGapIsTheHarmonicMass
import GaloisForLFunctions.RHTower.MertensSecondTheorem

/-!
# Every level is seen

What reads a twin that agrees with `Λ` on all prime powers up to a level `y` growing with `N`? The Selberg reading does, up to the
top of the range.

**The sharp law** (`exists_abs_selberg_gap_sub_le_sharp`). Uniformly in the filter,

`ledger(Selberg Λ, N) − ledger(Selberg (Λ − 2b), N) = 4 L N Σ_{e ≤ N} b(e)/e + O(√N log N)`.

The improvement over `N^{3/4}` is the hyperbola method on squares: `Λ_even ∗ Λ_even` has partial sum `Σ_{j ≤ √N} Λ(j) ψ(√N/j)`, of
size `√N log N`.

**The order at a level** (`exists_level_gap_order`). The mass above `y` is `≍ 1/√y`, so for `y ≤ N/(K log² N)` the gap has exact order
`N/√y`. A linear ledger moves by at most `2 w ψ(√N)` (`abs_ledger_sub_filteredTwin_le`), so the quadratic reading gains
exactly the factor `√(N/y)` over the linear one, and this gain tends to `1` at the top of the range. Above that level nothing separates the two scales.
-/

open Finset Filter Topology
open ArithmeticFunction (vonMangoldt cardFactors)
open GaloisForLFunctions.ArithmeticKreinLangerTheory
open GaloisForLFunctions.ArithmeticAuxiliaryDynamics
open GaloisForLFunctions.ArithmeticOfSquareRootPrecision

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

variable {c : ℕ →₀ ℤ} {m B : ℕ} {b : ℕ → ℝ}

/-- The even part of `Λ` lives on squares: `Σ_{e ≤ N} Λ_even(e) f(e) = Σ_{j ≤ √N} Λ(j) f(j²)`. -/
theorem sum_even_mul (f : ℕ → ℝ) (N : ℕ) :
    ∑ e ∈ Ioc 0 N, evenVonMangoldt e * f e = ∑ j ∈ Ioc 0 (Nat.sqrt N), vonMangoldt j * f (j ^ 2) := by
  symm
  refine sum_bij_ne_zero (fun j _ _ => j ^ 2) ?_ ?_ ?_ ?_
  · intro j hj _
    obtain ⟨h1, h2⟩ := mem_Ioc.mp hj
    exact mem_Ioc.mpr ⟨by positivity, Nat.le_sqrt'.mp h2⟩
  · intro a _ _ b _ _ h
    exact Nat.pow_left_injective (by norm_num) h
  · intro n hn hne
    have heq : evenVonMangoldt n ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have hf : f n ≠ 0 := fun h => hne (by rw [h, mul_zero])
    have hΛ : vonMangoldt n ≠ 0 := by
      intro h0
      apply heq
      simp [evenVonMangoldt, h0]
    have heven : Even (cardFactors n) := by
      by_contra h
      apply heq
      simp [evenVonMangoldt, h]
    obtain ⟨p, k, hp, hk, rfl⟩ := isPrimePow_nat_iff _ |>.mp
      (not_not.mp (mt ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hΛ))
    rw [ArithmeticFunction.cardFactors_apply_prime_pow hp] at heven
    obtain ⟨i, rfl⟩ := heven
    have hi : 0 < i := by omega
    have hp0 : p ^ i ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hsq : (p ^ i) ^ 2 = p ^ (i + i) := by rw [← pow_mul, mul_two]
    have hval : vonMangoldt (p ^ i) ≠ 0 := by
      rw [ArithmeticFunction.vonMangoldt_apply_pow hi.ne', ArithmeticFunction.vonMangoldt_apply_prime hp]
      exact (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    refine ⟨p ^ i, mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hp0, Nat.le_sqrt'.mpr ?_⟩, ?_, hsq⟩
    · rw [hsq]
      exact (mem_Ioc.mp hn).2
    · rw [hsq]
      exact mul_ne_zero hval hf
  · intro j hj _
    have hj0 : j ≠ 0 := by
      have := (mem_Ioc.mp hj).1
      omega
    have heven : Even (cardFactors (j ^ 2)) := by
      rw [sq, ArithmeticFunction.cardFactors_mul hj0 hj0]
      exact ⟨_, rfl⟩
    rw [evenVonMangoldt, if_pos heven, ArithmeticFunction.vonMangoldt_apply_pow two_ne_zero]

/-- Mertens' bound: `Σ_{j ≤ s} Λ(j)/j ≤ log s + A`. -/
theorem exists_sum_vonMangoldt_div_le :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℕ, ∑ j ∈ Ioc 0 s, vonMangoldt j / (j : ℝ) ≤ Real.log s + A := by
  obtain ⟨A, hA⟩ := _root_.RHTower.tendsto_sum_vonMangoldt_div_sub_log.bddAbove_range
  refine ⟨max A 0, le_max_right _ _, fun s => ?_⟩
  have h := hA ⟨s, rfl⟩
  have hset : Ioc 0 s = Icc 1 s := by
    ext j
    simp only [mem_Ioc, mem_Icc]
    omega
  rw [hset]
  have h2 := le_max_left A 0
  simp only at h
  linarith

/-- **The hyperbola method on squares.** `Λ_even ∗ Λ_even` has partial sum `≪ √N log N`. -/
theorem exists_sum_conv_even_le :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ N : ℕ, 1 ≤ N →
      ∑ n ∈ Ioc 0 N, conv evenVonMangoldt evenVonMangoldt n ≤ C₁ * (Real.sqrt N * (1 + Real.log N)) := by
  obtain ⟨A, hA0, hA⟩ := exists_sum_vonMangoldt_div_le
  have hC : (0 : ℝ) ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith
  refine ⟨(Real.log 4 + 4) * (1 + A), by positivity, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hb := evenVonMangoldt_nonneg
  have hswap := sum_Ioc_sum_divisors (fun d e => evenVonMangoldt d * evenVonMangoldt e) N
  have hconv : ∑ n ∈ Ioc 0 N, conv evenVonMangoldt evenVonMangoldt n =
      ∑ e ∈ Ioc 0 N, evenVonMangoldt e * Chebyshev.psi (Nat.sqrt (N / e)) := by
    simp only [conv]
    rw [hswap]
    refine sum_congr rfl fun e _ => ?_
    rw [← sum_evenVonMangoldt, mul_sum]
    exact sum_congr rfl fun d _ => mul_comm _ _
  rw [hconv]
  have hterm : ∀ e ∈ Ioc 0 N, evenVonMangoldt e * Chebyshev.psi (Nat.sqrt (N / e)) ≤
      evenVonMangoldt e * (((Real.log 4 + 4) * Real.sqrt N) * (1 / Real.sqrt e)) := by
    intro e he
    have he0 : (0 : ℝ) < e := by exact_mod_cast (mem_Ioc.mp he).1
    refine mul_le_mul_of_nonneg_left ?_ (hb e)
    have h1 : Chebyshev.psi (Nat.sqrt (N / e) : ℝ) ≤ (Real.log 4 + 4) * (Nat.sqrt (N / e) : ℝ) :=
      Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _)
    have h2 : (Nat.sqrt (N / e) : ℝ) ≤ Real.sqrt ((N / e : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
    have h3 : Real.sqrt ((N / e : ℕ) : ℝ) ≤ Real.sqrt ((N : ℝ) / e) :=
      Real.sqrt_le_sqrt Nat.cast_div_le
    have h4 : Real.sqrt ((N : ℝ) / e) = Real.sqrt N * (1 / Real.sqrt e) := by
      rw [Real.sqrt_div hN0, div_eq_mul_one_div]
    refine h1.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (h2.trans (h3.trans h4.le)) hC
  refine (sum_le_sum hterm).trans ?_
  have hreindex := sum_even_mul (fun e : ℕ => 1 / Real.sqrt e) N
  have hval : ∑ e ∈ Ioc 0 N, evenVonMangoldt e * (((Real.log 4 + 4) * Real.sqrt N) * (1 / Real.sqrt e)) =
      ((Real.log 4 + 4) * Real.sqrt N) * ∑ j ∈ Ioc 0 (Nat.sqrt N), vonMangoldt j / (j : ℝ) := by
    rw [← sum_congr rfl (fun e _ => by ring :
      ∀ e ∈ Ioc 0 N, ((Real.log 4 + 4) * Real.sqrt N) * (evenVonMangoldt e * (1 / Real.sqrt e)) =
        evenVonMangoldt e * (((Real.log 4 + 4) * Real.sqrt N) * (1 / Real.sqrt e))), ← mul_sum, hreindex]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    have hsq : Real.sqrt ((j ^ 2 : ℕ) : ℝ) = j := by
      push_cast
      exact Real.sqrt_sq (Nat.cast_nonneg j)
    rw [hsq]
    ring
  rw [hval]
  have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hlogs : Real.log (Nat.sqrt N : ℝ) ≤ Real.log N := by
    rcases Nat.eq_zero_or_pos (Nat.sqrt N) with h0 | h0
    · rw [h0]
      simpa using hlog0
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast Nat.sqrt_le_self N)
  have hS := hA (Nat.sqrt N)
  have hbound : ∑ j ∈ Ioc 0 (Nat.sqrt N), vonMangoldt j / (j : ℝ) ≤ (1 + A) * (1 + Real.log N) := by
    have h5 : (1 + A) * (1 + Real.log N) = 1 + Real.log N + A + A * Real.log N := by ring
    have h6 : 0 ≤ A * Real.log N := mul_nonneg hA0 hlog0
    linarith
  calc _ ≤ ((Real.log 4 + 4) * Real.sqrt N) * ((1 + A) * (1 + Real.log N)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

/-- The arithmetic of the three pieces of the gap. -/
private lemma gap_arith_sharp {L E W C C₁ R ℓ lg s Lb Bb Y : ℝ} (hL : 0 ≤ L) (hE : 0 ≤ E) (hW : 0 ≤ W)
    (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hR : 0 ≤ R) (hℓ : 1 ≤ ℓ) (hlg : lg ≤ ℓ) (hs0 : 0 ≤ s) (hs : s ≤ R)
    (hℓval : ℓ = 1 + lg) (hY : |Y| ≤ (L + E * (1 + lg)) * (C * s)) (hLb0 : 0 ≤ Lb)
    (hLb1 : Lb ≤ W * (lg * (C * s))) (hBb0 : 0 ≤ Bb) (hBb1 : Bb ≤ W * (C₁ * (R * ℓ))) :
    |2 * Lb + 4 * Y - 4 * Bb| ≤ (4 * ((L + E) * C) + 2 * (W * C) + 4 * (W * C₁)) * (R * ℓ) := by
  have hCs : C * s ≤ C * R := mul_le_mul_of_nonneg_left hs hC
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hA : (L + E * (1 + lg)) * (C * s) ≤ ((L + E) * C) * (R * ℓ) := by
    have h1 : L + E * (1 + lg) ≤ (L + E) * ℓ := by
      rw [← hℓval]
      nlinarith
    calc _ ≤ ((L + E) * ℓ) * (C * R) := mul_le_mul h1 hCs (mul_nonneg hC hs0) (by positivity)
      _ = _ := by ring
  have hB : W * (lg * (C * s)) ≤ (W * C) * (R * ℓ) := by
    have h2 : lg * (C * s) ≤ ℓ * (C * R) := mul_le_mul hlg hCs (mul_nonneg hC hs0) hℓ0
    calc _ ≤ W * (ℓ * (C * R)) := mul_le_mul_of_nonneg_left h2 hW
      _ = _ := by ring
  have hD : W * (C₁ * (R * ℓ)) = (W * C₁) * (R * ℓ) := by ring
  have hp1 : 0 ≤ (W * C) * (R * ℓ) := by positivity
  have hp2 : 0 ≤ (W * C₁) * (R * ℓ) := by positivity
  obtain ⟨hc1, hc2⟩ := abs_le.mp hY
  have hval : (4 * ((L + E) * C) + 2 * (W * C) + 4 * (W * C₁)) * (R * ℓ) =
      4 * (((L + E) * C) * (R * ℓ)) + 2 * ((W * C) * (R * ℓ)) + 4 * ((W * C₁) * (R * ℓ)) := by ring
  rw [hval, abs_le]
  rw [hD] at hBb1
  constructor <;> linarith

/-- **The sharp law of the gap.** Uniformly in the filter, the Selberg gap is `4 L N Σ_{e≤N} b(e)/e + O(√N log N)`. -/
theorem exists_abs_selberg_gap_sub_le_sharp (hP : IsProducer c m B) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ b : ℕ → ℝ, IsEvenFilter b → ∀ N : ℕ, 1 ≤ N →
      |ledger c (selbergWeight vonMangoldtWeight) N - ledger c (selbergWeight (filteredTwin b)) N -
          4 * stencilSlope c * N * harmonicMass b N| ≤ M * (Real.sqrt N * (1 + Real.log N)) := by
  obtain ⟨C₁, hC₁, hconv⟩ := exists_sum_conv_even_le
  have hL : 0 ≤ stencilSlope c := (stencilSlope_pos hP).le
  have hE : 0 ≤ stencilErrorConst c := stencilErrorConst_nonneg c
  have hW : (0 : ℝ) ≤ ((peak c : ℤ) : ℝ) := by
    have h1 := hP.nonneg 0
    have h2 := hP.stepWeight_le_peak 0
    exact_mod_cast h1.trans h2
  have hC : (0 : ℝ) ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith
  refine ⟨4 * ((stencilSlope c + stencilErrorConst c) * (Real.log 4 + 4)) +
    2 * (((peak c : ℤ) : ℝ) * (Real.log 4 + 4)) + 4 * (((peak c : ℤ) : ℝ) * C₁), by positivity,
    fun b hb N hN => ?_⟩
  have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hLbnn : ∀ n : ℕ, 0 ≤ b n * Real.log n := fun n =>
    mul_nonneg (hb.nonneg n) (Real.log_natCast_nonneg n)
  have hexpand : ledger c (selbergWeight (filteredTwin b)) N =
      ledger c (selbergWeight vonMangoldtWeight) N +
        ((-2) * ledger c (fun n => b n * Real.log n) N +
          ((-4) * ledger c (conv vonMangoldtWeight b) N + 4 * ledger c (conv b b) N)) := by
    have hfun : ledger c (selbergWeight (filteredTwin b)) N = ledger c (fun n =>
        selbergWeight vonMangoldtWeight n + ((-2) * (b n * Real.log n) +
          ((-4) * conv vonMangoldtWeight b n + 4 * conv b b n))) N := by
      simp only [ledger, selbergWeight_filteredTwin]
    rw [hfun, ledger_add, ledger_add, ledger_smul, ledger_add, ledger_smul, ledger_smul]
  have hLb1 : ledger c (fun n => b n * Real.log n) N ≤
      ((peak c : ℤ) : ℝ) * (Real.log N * ((Real.log 4 + 4) * (Nat.sqrt N : ℝ))) := by
    refine (ledger_le hP hLbnn N).trans (mul_le_mul_of_nonneg_left ?_ hW)
    have h1 : ∑ d ∈ Ioc 0 N, b d * Real.log d ≤ ∑ d ∈ Ioc 0 N, b d * Real.log N := by
      refine sum_le_sum fun d hd => mul_le_mul_of_nonneg_left ?_ (hb.nonneg d)
      obtain ⟨hd0, hdN⟩ := mem_Ioc.mp hd
      exact Real.log_le_log (by exact_mod_cast hd0) (by exact_mod_cast hdN)
    refine h1.trans ?_
    rw [← sum_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hb.sum_le N) hlog0
  have hconvnn : ∀ n, 0 ≤ conv b b n := fun n =>
    sum_nonneg fun d _ => mul_nonneg (hb.nonneg d) (hb.nonneg _)
  have hBb1 : ledger c (conv b b) N ≤
      ((peak c : ℤ) : ℝ) * (C₁ * (Real.sqrt N * (1 + Real.log N))) := by
    refine (ledger_le hP hconvnn N).trans (mul_le_mul_of_nonneg_left ?_ hW)
    exact (sum_le_sum fun n _ => conv_filter_le hb n).trans (hconv N hN)
  have hgap : ledger c (selbergWeight vonMangoldtWeight) N - ledger c (selbergWeight (filteredTwin b)) N -
      4 * stencilSlope c * N * harmonicMass b N =
      2 * ledger c (fun n => b n * Real.log n) N +
        4 * (ledger c (conv vonMangoldtWeight b) N - stencilSlope c * N * harmonicMass b N) -
          4 * ledger c (conv b b) N := by
    rw [hexpand]
    ring
  rw [hgap]
  exact gap_arith_sharp hL hE hW hC hC₁ (Real.sqrt_nonneg _) (by linarith) (by linarith)
    (Nat.cast_nonneg _) Real.nat_sqrt_le_real_sqrt rfl (abs_ledger_conv_sub_le hP hb N)
    (ledger_nonneg hP hLbnn N) hLb1 (ledger_nonneg hP hconvnn N) hBb1

/-- A linear ledger moves by at most `2 w ψ(√N)` under a filter. -/
theorem abs_ledger_sub_filteredTwin_le (hP : IsProducer c m B) (hb : IsEvenFilter b) (N : ℕ) :
    |ledger c vonMangoldtWeight N - ledger c (filteredTwin b) N| ≤
      2 * ((peak c : ℤ) : ℝ) * ((Real.log 4 + 4) * (Nat.sqrt N : ℝ)) := by
  have hW : (0 : ℝ) ≤ ((peak c : ℤ) : ℝ) := by
    have h1 := hP.nonneg 0
    have h2 := hP.stepWeight_le_peak 0
    exact_mod_cast h1.trans h2
  have hfun : filteredTwin b = fun n => vonMangoldtWeight n - (2 * b n) := by
    funext n
    rfl
  rw [hfun, ledger_sub, sub_sub_cancel, ledger_smul]
  have h0 := ledger_nonneg hP hb.nonneg N
  rw [abs_of_nonneg (by positivity)]
  have h1 := (ledger_le hP hb.nonneg N).trans (mul_le_mul_of_nonneg_left (hb.sum_le N) hW)
  linarith

/-! ### The mass above a level -/

/-- The mass above a level, on the square roots. -/
theorem harmonicMass_level_eq {y N : ℕ} (h : y ≤ N) :
    harmonicMass (levelFilter y) N =
      ∑ j ∈ Ioc (Nat.sqrt y) (Nat.sqrt N), vonMangoldt j / (j : ℝ) ^ 2 := by
  rw [harmonicMass_level h, harmonicMass_even, harmonicMass_even,
    ← sum_Ioc_consecutive _ (Nat.zero_le (Nat.sqrt y)) (Nat.sqrt_le_sqrt h)]
  ring

/-- **The mass above a level is at least `1/(8√y)`.** The lower bound is the prime number theorem in `(√y, 2√y]`. -/
theorem exists_le_harmonicMass_level :
    ∃ y₀ : ℕ, 1 ≤ y₀ ∧ ∀ y N : ℕ, y₀ ≤ y → 4 * y ≤ N →
      1 / (8 * Real.sqrt y) ≤ harmonicMass (levelFilter y) N := by
  have hpnt := eventually_abs_psi_sub_le (ε := 1 / 8) (by norm_num)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hpnt
  set t₀ : ℕ := ⌈max x₀ 1⌉₊ with ht₀
  have ht₀R : max x₀ 1 ≤ (t₀ : ℝ) := Nat.le_ceil _
  have ht₀1 : (1 : ℝ) ≤ t₀ := (le_max_right _ _).trans ht₀R
  have ht₀N : 1 ≤ t₀ := by exact_mod_cast ht₀1
  refine ⟨t₀ ^ 2, Nat.one_le_pow _ _ ht₀N, fun y N hy hN => ?_⟩
  set t := Nat.sqrt y with ht
  have htt₀ : t₀ ≤ t := Nat.le_sqrt'.mpr hy
  have htR : (t₀ : ℝ) ≤ t := by exact_mod_cast htt₀
  have ht1 : (1 : ℝ) ≤ t := ht₀1.trans htR
  have htx : x₀ ≤ t := (le_max_left _ _).trans (ht₀R.trans htR)
  have hyN : y ≤ N := by omega
  rw [harmonicMass_level_eq hyN]
  have h2t : 2 * t ≤ Nat.sqrt N := by
    refine Nat.le_sqrt'.mpr ?_
    have := Nat.sqrt_le' y
    nlinarith
  have hsub : ∑ j ∈ Ioc t (2 * t), vonMangoldt j / (j : ℝ) ^ 2 ≤
      ∑ j ∈ Ioc t (Nat.sqrt N), vonMangoldt j / (j : ℝ) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right h2t) fun j _ _ =>
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  refine le_trans ?_ hsub
  have hterm : ∀ j ∈ Ioc t (2 * t), vonMangoldt j / (2 * (t : ℝ)) ^ 2 ≤ vonMangoldt j / (j : ℝ) ^ 2 := by
    intro j hj
    obtain ⟨h1, h2⟩ := mem_Ioc.mp hj
    have hjR : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
    have hj2 : (j : ℝ) ≤ 2 * t := by exact_mod_cast h2
    exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg (by positivity)
      (pow_le_pow_left₀ hjR.le hj2 2)
  refine le_trans ?_ (sum_le_sum hterm)
  rw [← sum_div]
  have hpsi : ∀ n : ℕ, Chebyshev.psi (n : ℝ) = ∑ j ∈ Ioc 0 n, vonMangoldt j := fun n => by
    rw [Chebyshev.psi, Nat.floor_natCast]
  have hdiff : ∑ j ∈ Ioc t (2 * t), vonMangoldt j =
      Chebyshev.psi ((2 * t : ℕ) : ℝ) - Chebyshev.psi (t : ℝ) := by
    rw [hpsi, hpsi, ← sum_Ioc_consecutive _ (Nat.zero_le t) (by omega : t ≤ 2 * t)]
    ring
  have h1 := abs_le.mp (hx₀ (t : ℝ) htx)
  have h2 := abs_le.mp (hx₀ ((2 * t : ℕ) : ℝ) (by push_cast; linarith))
  push_cast at h2
  have hmass : (t : ℝ) / 2 ≤ ∑ j ∈ Ioc t (2 * t), vonMangoldt j := by
    rw [hdiff]
    push_cast
    linarith [h1.2, h2.1]
  have hsqrt : (t : ℝ) ≤ Real.sqrt y := Real.nat_sqrt_le_real_sqrt
  have hrt : 0 < Real.sqrt y := by linarith
  have hfinal : 1 / (8 * Real.sqrt y) ≤ 1 / (8 * (t : ℝ)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  refine hfinal.trans ?_
  have hval : 1 / (8 * (t : ℝ)) = ((t : ℝ) / 2) / (2 * (t : ℝ)) ^ 2 := by
    field_simp
    ring
  rw [hval]
  exact div_le_div_of_nonneg_right hmass (by positivity)

/-- The tail of `Σ Λ(j)/j²` by partial summation against Chebyshev's bound. -/
private lemma sum_Ioc_vonMangoldt_div_sq_le {t : ℕ} (ht : 1 ≤ t) {J : ℕ} (hJ : t ≤ J) :
    ∑ j ∈ Ioc t J, vonMangoldt j / (j : ℝ) ^ 2 ≤
      (∑ j ∈ Ioc t J, vonMangoldt j) / (J : ℝ) ^ 2 +
        2 * (Real.log 4 + 4) * (1 / (t : ℝ) - 1 / (J : ℝ)) := by
  have hC : (0 : ℝ) ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith
  induction J, hJ using Nat.le_induction with
  | base => simp
  | succ J hJ ih =>
    have hJ1 : 1 ≤ J := ht.trans hJ
    have hJR : (0 : ℝ) < J := by exact_mod_cast hJ1
    have hset : Ioc t (J + 1) = insert (J + 1) (Ioc t J) := by
      ext j
      simp only [mem_Ioc, mem_insert]
      omega
    have hnot : J + 1 ∉ Ioc t J := by simp
    rw [hset, sum_insert hnot, sum_insert hnot]
    set D := ∑ j ∈ Ioc t J, vonMangoldt j with hD
    have hD0 : 0 ≤ D := sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
    have hDle : D ≤ (Real.log 4 + 4) * J := by
      have h1 : D ≤ ∑ j ∈ Ioc 0 J, vonMangoldt j :=
        sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_left (Nat.zero_le t))
          fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
      have h2 := Chebyshev.psi_le_const_mul_self (x := (J : ℝ)) (Nat.cast_nonneg J)
      rw [Chebyshev.psi, Nat.floor_natCast] at h2
      linarith
    set Λ₁ := vonMangoldt (J + 1) with hΛ₁
    push_cast
    have hkey : D * (1 / (J : ℝ) ^ 2 - 1 / ((J : ℝ) + 1) ^ 2) ≤
        2 * (Real.log 4 + 4) * (1 / (J : ℝ) - 1 / ((J : ℝ) + 1)) := by
      have h1 : 1 / (J : ℝ) ^ 2 - 1 / ((J : ℝ) + 1) ^ 2 =
          (2 * (J : ℝ) + 1) / ((J : ℝ) ^ 2 * ((J : ℝ) + 1) ^ 2) := by
        field_simp
        ring
      have h2 : 1 / (J : ℝ) - 1 / ((J : ℝ) + 1) = 1 / ((J : ℝ) * ((J : ℝ) + 1)) := by
        field_simp
        ring
      rw [h1, h2, ← mul_div_assoc, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have h3 : D * (2 * (J : ℝ) + 1) ≤ ((Real.log 4 + 4) * J) * (2 * ((J : ℝ) + 1)) :=
        mul_le_mul hDle (by linarith) (by positivity) (by positivity)
      have hpos : 0 ≤ (J : ℝ) * ((J : ℝ) + 1) := by positivity
      calc D * (2 * (J : ℝ) + 1) * ((J : ℝ) * ((J : ℝ) + 1))
          ≤ ((Real.log 4 + 4) * J) * (2 * ((J : ℝ) + 1)) * ((J : ℝ) * ((J : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right h3 hpos
        _ = _ := by ring
    have hsplit : (Λ₁ + D) / ((J : ℝ) + 1) ^ 2 = Λ₁ / ((J : ℝ) + 1) ^ 2 + D / ((J : ℝ) + 1) ^ 2 := add_div _ _ _
    have hexp : D * (1 / (J : ℝ) ^ 2 - 1 / ((J : ℝ) + 1) ^ 2) =
        D / (J : ℝ) ^ 2 - D / ((J : ℝ) + 1) ^ 2 := by ring
    have hexp2 : 2 * (Real.log 4 + 4) * (1 / (J : ℝ) - 1 / ((J : ℝ) + 1)) =
        2 * (Real.log 4 + 4) * (1 / (J : ℝ)) - 2 * (Real.log 4 + 4) * (1 / ((J : ℝ) + 1)) := by ring
    rw [hsplit]
    rw [hexp, hexp2] at hkey
    have hexp3 : 2 * (Real.log 4 + 4) * (1 / (t : ℝ) - 1 / ((J : ℝ) + 1)) =
        2 * (Real.log 4 + 4) * (1 / (t : ℝ)) - 2 * (Real.log 4 + 4) * (1 / ((J : ℝ) + 1)) := by ring
    have hexp4 : 2 * (Real.log 4 + 4) * (1 / (t : ℝ) - 1 / (J : ℝ)) =
        2 * (Real.log 4 + 4) * (1 / (t : ℝ)) - 2 * (Real.log 4 + 4) * (1 / (J : ℝ)) := by ring
    rw [hexp3]
    rw [hexp4] at ih
    linarith

/-- **The mass above a level is at most `C/√y`.** -/
theorem harmonicMass_level_le {y N : ℕ} (hy : 1 ≤ y) (hyN : y ≤ N) :
    harmonicMass (levelFilter y) N ≤ 6 * (Real.log 4 + 4) / Real.sqrt y := by
  have hC : (0 : ℝ) ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith
  rw [harmonicMass_level_eq hyN]
  set t := Nat.sqrt y with ht
  have ht1 : 1 ≤ t := Nat.le_sqrt'.mpr (by simpa using hy)
  have htR : (0 : ℝ) < t := by exact_mod_cast ht1
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hJ : t ≤ Nat.sqrt N := Nat.sqrt_le_sqrt hyN
  set J := Nat.sqrt N with hJdef
  have hJR : (0 : ℝ) < J := by exact_mod_cast ht1.trans hJ
  have hmain := sum_Ioc_vonMangoldt_div_sq_le ht1 hJ
  have hD : (∑ j ∈ Ioc t J, vonMangoldt j) / (J : ℝ) ^ 2 ≤ (Real.log 4 + 4) / J := by
    have h1 : ∑ j ∈ Ioc t J, vonMangoldt j ≤ ∑ j ∈ Ioc 0 J, vonMangoldt j :=
      sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_left (Nat.zero_le t))
        fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
    have h2 := Chebyshev.psi_le_const_mul_self (x := (J : ℝ)) (Nat.cast_nonneg J)
    rw [Chebyshev.psi, Nat.floor_natCast] at h2
    rw [div_le_div_iff₀ (by positivity) hJR]
    nlinarith
  have hJt : (Real.log 4 + 4) / (J : ℝ) ≤ (Real.log 4 + 4) / t := by
    refine div_le_div_of_nonneg_left hC htR (by exact_mod_cast hJ)
  have hthird : 2 * (Real.log 4 + 4) * (1 / (t : ℝ) - 1 / (J : ℝ)) ≤ 2 * (Real.log 4 + 4) * (1 / (t : ℝ)) := by
    have : 0 ≤ 1 / (J : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  -- `√y < t + 1 ≤ 2t`.
  have hrt : Real.sqrt y ≤ 2 * t := by
    have hlt : y < (t + 1) ^ 2 := by
      have := Nat.lt_succ_sqrt y
      nlinarith
    have hR : (y : ℝ) ≤ (2 * (t : ℝ)) ^ 2 := by
      have h1 : (y : ℝ) < ((t : ℝ) + 1) ^ 2 := by exact_mod_cast hlt
      have h2 : (1 : ℝ) ≤ t := by exact_mod_cast ht1
      nlinarith
    exact Real.sqrt_le_iff.mpr ⟨by positivity, hR⟩
  have hrtpos : 0 < Real.sqrt y := Real.sqrt_pos.mpr hyR
  have htinv : 1 / (t : ℝ) ≤ 2 / Real.sqrt y := by
    rw [div_le_div_iff₀ htR hrtpos]
    linarith
  have hfinal : 6 * (Real.log 4 + 4) / Real.sqrt y = 3 * (Real.log 4 + 4) * (2 / Real.sqrt y) := by ring
  rw [hfinal]
  have h3 : 3 * (Real.log 4 + 4) * (1 / (t : ℝ)) ≤ 3 * (Real.log 4 + 4) * (2 / Real.sqrt y) :=
    mul_le_mul_of_nonneg_left htinv (by positivity)
  have h4 : (Real.log 4 + 4) / t = (Real.log 4 + 4) * (1 / (t : ℝ)) := by ring
  linarith

/-- **Every level is seen.** For levels `y₀ ≤ y` with `K √y (1 + log N) ≤ √N`, the Selberg gap of the twin agreeing with `Λ` up to
`y` has exact order `N/√y`. -/
theorem exists_level_gap_order (hP : IsProducer c m B) :
    ∃ (K c₁ c₂ : ℝ) (y₀ : ℕ), 0 < K ∧ 0 < c₁ ∧ 0 < c₂ ∧ ∀ y N : ℕ, y₀ ≤ y → 1 ≤ N →
      K * Real.sqrt y * (1 + Real.log N) ≤ Real.sqrt N →
      c₁ * ((N : ℝ) / Real.sqrt y) ≤
          ledger c (selbergWeight vonMangoldtWeight) N -
            ledger c (selbergWeight (filteredTwin (levelFilter y))) N ∧
        ledger c (selbergWeight vonMangoldtWeight) N -
            ledger c (selbergWeight (filteredTwin (levelFilter y))) N ≤ c₂ * ((N : ℝ) / Real.sqrt y) := by
  obtain ⟨M, hM0, hlaw⟩ := exists_abs_selberg_gap_sub_le_sharp hP
  obtain ⟨y₀, hy₀, hlower⟩ := exists_le_harmonicMass_level
  have hL := stencilSlope_pos hP
  have hC : (0 : ℝ) < Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith
  refine ⟨max 2 (4 * M / stencilSlope c), stencilSlope c / 4, 24 * stencilSlope c * (Real.log 4 + 4) +
    stencilSlope c / 4, y₀, by positivity, by positivity, by positivity, fun y N hy hN hsmall => ?_⟩
  have hy1 : 1 ≤ y := hy₀.trans hy
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy1
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hrt : 0 < Real.sqrt y := Real.sqrt_pos.mpr hyR
  have hrN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNR
  set ℓ := 1 + Real.log N with hℓ
  have hℓ1 : 1 ≤ ℓ := by linarith
  -- The hypothesis gives both `4y ≤ N` and the smallness of the error.
  have h2 : 2 * Real.sqrt y ≤ Real.sqrt N := by
    have h1 : 2 * Real.sqrt y * 1 ≤ max 2 (4 * M / stencilSlope c) * Real.sqrt y * ℓ :=
      mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) hrt.le) hℓ1 (by norm_num) (by positivity)
    linarith
  have h4y : 4 * y ≤ N := by
    have h3 : (2 * Real.sqrt y) ^ 2 ≤ Real.sqrt N ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    rw [mul_pow, Real.sq_sqrt hyR.le, Real.sq_sqrt hNR.le] at h3
    exact_mod_cast (by linarith : (4 : ℝ) * y ≤ N)
  have hyN : y ≤ N := by omega
  have hmass := hlower y N hy h4y
  have hmassup := harmonicMass_level_le hy1 hyN
  have hsm : M * Real.sqrt y * ℓ ≤ stencilSlope c / 4 * Real.sqrt N := by
    have h1 : 4 * M / stencilSlope c * Real.sqrt y * ℓ ≤ max 2 (4 * M / stencilSlope c) * Real.sqrt y * ℓ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hrt.le) (by linarith)
    have h3 : 4 * M / stencilSlope c * Real.sqrt y * ℓ ≤ Real.sqrt N := h1.trans hsmall
    have h5 : 4 * M / stencilSlope c * Real.sqrt y * ℓ = (4 * (M * Real.sqrt y * ℓ)) / stencilSlope c := by ring
    rw [h5, div_le_iff₀ hL] at h3
    linarith
  have herr : M * (Real.sqrt N * ℓ) ≤ stencilSlope c / 4 * ((N : ℝ) / Real.sqrt y) := by
    have hNsq : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt hNR.le).symm
    have h6 : M * (Real.sqrt N * ℓ) = (M * Real.sqrt y * ℓ) * (Real.sqrt N / Real.sqrt y) := by
      field_simp
    rw [h6]
    calc _ ≤ (stencilSlope c / 4 * Real.sqrt N) * (Real.sqrt N / Real.sqrt y) :=
          mul_le_mul_of_nonneg_right hsm (by positivity)
      _ = stencilSlope c / 4 * ((Real.sqrt N * Real.sqrt N) / Real.sqrt y) := by ring
      _ = _ := by rw [← hNsq]
  obtain ⟨hl1, hl2⟩ := abs_le.mp (hlaw (levelFilter y) (isEvenFilter_level y) N hN)
  have hNy : 0 < (N : ℝ) / Real.sqrt y := by positivity
  have hmain1 : stencilSlope c / 2 * ((N : ℝ) / Real.sqrt y) ≤
      4 * stencilSlope c * N * harmonicMass (levelFilter y) N := by
    have h7 : 4 * stencilSlope c * N * (1 / (8 * Real.sqrt y)) ≤
        4 * stencilSlope c * N * harmonicMass (levelFilter y) N :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    have h8 : 4 * stencilSlope c * N * (1 / (8 * Real.sqrt y)) = stencilSlope c / 2 * ((N : ℝ) / Real.sqrt y) := by
      field_simp
      ring
    linarith
  have hmain2 : 4 * stencilSlope c * N * harmonicMass (levelFilter y) N ≤
      24 * stencilSlope c * (Real.log 4 + 4) * ((N : ℝ) / Real.sqrt y) := by
    have h7 := mul_le_mul_of_nonneg_left hmassup (by positivity : 0 ≤ 4 * stencilSlope c * N)
    have h8 : 4 * stencilSlope c * N * (6 * (Real.log 4 + 4) / Real.sqrt y) =
        24 * stencilSlope c * (Real.log 4 + 4) * ((N : ℝ) / Real.sqrt y) := by
      ring
    linarith
  constructor
  · have h9 : stencilSlope c / 4 * ((N : ℝ) / Real.sqrt y) =
        stencilSlope c / 2 * ((N : ℝ) / Real.sqrt y) - stencilSlope c / 4 * ((N : ℝ) / Real.sqrt y) := by ring
    linarith
  · have h9 : (24 * stencilSlope c * (Real.log 4 + 4) + stencilSlope c / 4) * ((N : ℝ) / Real.sqrt y) =
        24 * stencilSlope c * (Real.log 4 + 4) * ((N : ℝ) / Real.sqrt y) +
          stencilSlope c / 4 * ((N : ℝ) / Real.sqrt y) := by ring
    linarith

end GaloisForLFunctions.RigidArithmeticOfCuts
