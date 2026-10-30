import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheUpwardPrimeRowsRealizeTheCompletedShellCorrection
import GaloisForLFunctions.HTGeometry.HarmonicQuotientTailBound

/-!
# Polynomial harmonic control of prime-index boundary errors

The reciprocal Mangoldt mass of a width-`B` window is at most `2B+2`,
and at most `8(B+1)/√Y` beyond `Y≥2B+2`. Splitting harmonic rows at
`N/n=4(B+1)(log N)²` controls both literal upward cutoff changes by
`O((B+1)⁶/√(log N))` in normalized squared norm.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  BezoutValuationIncidence RenormalizedArithmeticPotentialTheory.CompletedShell

private theorem primeIndexBoundaryMass_card_le (B Y : ℕ) :
    ((Icc (Y - B) (Y + B + 1)).card : ℝ) ≤ 2 * B + 2 := by
  rw [Nat.card_Icc]
  exact_mod_cast (show Y + B + 1 + 1 - (Y - B) ≤ 2 * B + 2 by omega)

/-- Every reciprocal Mangoldt boundary window has a global linear-width bound. -/
theorem primeIndexBoundaryMass_le_width (B Y : ℕ) :
    primeIndexBoundaryMass B Y ≤ 2 * B + 2 := by
  have hterm (k : ℕ) : (ArithmeticFunction.vonMangoldt k : ℝ) / k ≤ 1 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      apply (div_le_one hk0).mpr
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        ((Real.log_le_sub_one_of_pos hk0).trans (by linarith))
  calc
    _ ≤ ∑ _k ∈ Icc (Y - B) (Y + B + 1), (1 : ℝ) := sum_le_sum fun k _ => hterm k
    _ = ((Icc (Y - B) (Y + B + 1)).card : ℝ) := by simp
    _ ≤ _ := primeIndexBoundaryMass_card_le B Y

/-- Away from zero, an entire prime-index window costs its width divided by the square root. -/
theorem primeIndexBoundaryMass_le_sqrt {B Y : ℕ} (hY : 2 * B + 2 ≤ Y) :
    primeIndexBoundaryMass B Y ≤ 8 * ((B : ℝ) + 1) / Real.sqrt Y := by
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hsY : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY0
  have hterm (k : ℕ) (hk : k ∈ Icc (Y - B) (Y + B + 1)) :
      (ArithmeticFunction.vonMangoldt k : ℝ) / k ≤ 4 / Real.sqrt Y := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by have := (mem_Icc.mp hk).1; omega)
    have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hk1
    have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
    have hYk : (Y : ℝ) ≤ 2 * k := by
      exact_mod_cast (show Y ≤ 2 * k by have := (mem_Icc.mp hk).1; omega)
    have hsqrt : Real.sqrt Y ≤ 2 * Real.sqrt k := by
      nlinarith only [Real.sq_sqrt hY0.le, Real.sq_sqrt hk0.le, hYk,
        Real.sqrt_nonneg (Y : ℝ), hsk]
    calc
      _ ≤ Real.log k / k := div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log hk0.le
      _ = (Real.log k * (Real.sqrt k)⁻¹) / Real.sqrt k := by
        field_simp [hsk.ne', hk0.ne']
        rw [Real.sq_sqrt hk0.le]
      _ ≤ 2 / Real.sqrt k := div_le_div_of_nonneg_right
        (_root_.RHTower.WeilAbscissa.log_div_sqrt_le hk1) hsk.le
      _ ≤ _ := (div_le_div_iff₀ hsk hsY).mpr (by linarith only [hsqrt])
  calc
    _ ≤ ∑ _k ∈ Icc (Y - B) (Y + B + 1), 4 / Real.sqrt Y := sum_le_sum hterm
    _ ≤ (2 * (B : ℝ) + 2) * (4 / Real.sqrt Y) := by
      rw [sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (primeIndexBoundaryMass_card_le B Y) (by positivity)
    _ = _ := by ring

private theorem real_quotient_lt_two_nat_quotient {N n : ℕ} (hn : n ∈ Icc 1 N) :
    (N : ℝ) / n < 2 * ((N / n : ℕ) : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hy : (1 : ℝ) ≤ ((N / n : ℕ) : ℝ) := by
    exact_mod_cast Nat.div_pos (mem_Icc.mp hn).2 (mem_Icc.mp hn).1
  have hf : (N : ℝ) / n < (N / n : ℕ) + 1 := by
    rw [div_lt_iff₀ hn0]
    have hmod := Nat.mod_lt N (mem_Icc.mp hn).1
    have hid := Nat.mod_add_div N n
    have hlt : N < (N / n + 1) * n := by nlinarith only [hmod, hid]
    exact_mod_cast hlt
  linarith only [hf, hy]

/-- Both literal prime cutoffs have a quantitative harmonic error, uniform in strip width. -/
theorem exists_linearizedUpwardCoefficient_boundary_polynomial_harmonic_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 1 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 1 ≤ N → 1 ≤ Real.log (N : ℝ) →
      ∀ c : ℝ, 0 < c → c ≤ (N : ℝ) → ∀ B : ℕ,
      (∑ n ∈ Icc 1 N,
        ((linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n) /
          Real.sqrt n) ^ 2) / Real.log N ≤ K * ((B : ℝ) + 1) ^ 6 / Real.sqrt (Real.log N) := by
  let D : ℝ := 32 * m.totient
  have hD : 0 < D := by
    have hφm : 0 < (m.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm
    dsimp only [D]
    positivity
  refine ⟨14 * D ^ 2, by positivity, ?_⟩
  intro N hN hlog c hc hcN B
  let b : ℝ := (B : ℝ) + 1
  let L := Real.log (N : ℝ)
  let T := 4 * b * L ^ 2
  let R : ℕ → ℝ := fun n =>
    (linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n
  have hb : 1 ≤ b := by dsimp only [b]; have h : (0 : ℝ) ≤ B := Nat.cast_nonneg B; linarith only [h]
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hL : 1 ≤ L := hlog
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hL2 : 1 ≤ L ^ 2 := by nlinarith only [hL]
  have hsL : 1 ≤ Real.sqrt L := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL
  have hT : 1 ≤ T := by dsimp only [T]; nlinarith only [hb, hL2]
  have hglobal : ∀ n ∈ Icc 1 N, |R n| ≤ (D * b ^ 2) / Real.sqrt n := by
    intro n hn
    dsimp only [R]
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg n)
    have hsource := abs_linearizedUpwardCoefficient_sub_reciprocal_le hφ hsupp hM hc hm
      (mem_Icc.mp hn).1 hcN (B := B)
    refine hsource.trans ?_
    have hmass := mul_le_mul_of_nonneg_left (primeIndexBoundaryMass_le_width B (N / n))
      (show 0 ≤ 4 * (B : ℝ) * m.totient by positivity)
    have hBb : (B : ℝ) ≤ b := by dsimp only [b]; linarith
    calc
      _ ≤ 4 * (B : ℝ) * m.totient * (2 * B + 2) := hmass
      _ = 8 * m.totient * ((B : ℝ) * b) := by dsimp only [b]; ring
      _ ≤ 8 * m.totient * b ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [pow_two] using mul_le_mul_of_nonneg_right hBb hb0.le
      _ ≤ D * b ^ 2 := by
        dsimp only [D]
        have h := mul_nonneg (Nat.cast_nonneg m.totient) (sq_nonneg b)
        nlinarith only [h]
  have hgood : ∀ n ∈ Icc 1 N, T ≤ (N : ℝ) / n → |R n| ≤ (D * b ^ 2 / L) / Real.sqrt n := by
    intro n hn ht
    have hquot := real_quotient_lt_two_nat_quotient hn
    have hYbL : 2 * b * L ^ 2 ≤ ((N / n : ℕ) : ℝ) := by
      dsimp only [T] at ht
      linarith only [ht, hquot]
    have hYb : 2 * b ≤ ((N / n : ℕ) : ℝ) := by
      have hsmall : 2 * b ≤ 2 * b * L ^ 2 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hL2 (show 0 ≤ 2 * b by positivity)
      exact hsmall.trans hYbL
    have hYnat : 2 * B + 2 ≤ N / n := by
      dsimp only [b] at hYb
      exact_mod_cast hYb
    have hYL : L ^ 2 ≤ ((N / n : ℕ) : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hb (sq_nonneg L)
      nlinarith only [hYbL, h, sq_nonneg L]
    have hs : L ≤ Real.sqrt ((N / n : ℕ) : ℝ) := by
      have h := Real.sqrt_le_sqrt hYL
      simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hL0] using h
    have hmass : primeIndexBoundaryMass B (N / n) ≤ 8 * b / L :=
      (primeIndexBoundaryMass_le_sqrt hYnat).trans
        (div_le_div_of_nonneg_left (by positivity) hL0 hs)
    dsimp only [R]
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg n)
    refine (abs_linearizedUpwardCoefficient_sub_reciprocal_le hφ hsupp hM hc hm
      (mem_Icc.mp hn).1 hcN (B := B)).trans ?_
    calc
      _ ≤ 4 * (B : ℝ) * m.totient * (8 * b / L) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = D * ((B : ℝ) * b) / L := by dsimp only [D]; ring
      _ ≤ D * b ^ 2 / L := by
        apply div_le_div_of_nonneg_right _ hL0.le
        apply mul_le_mul_of_nonneg_left _ hD.le
        have hBb : (B : ℝ) ≤ b := by dsimp only [b]; linarith
        simpa only [pow_two] using mul_le_mul_of_nonneg_right hBb hb0.le
  have hsum := HTGeometry.sum_sq_le_harmonic_quotient_tail hN hT R hglobal hgood
  have hhead : (D * b ^ 2 / L) ^ 2 * (1 + L) ≤ 2 * D ^ 2 * b ^ 6 * Real.sqrt L := by
    have hfrac : (1 + L) / L ^ 2 ≤ 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos hL0)).mpr
      nlinarith only [hL]
    calc
      _ = D ^ 2 * b ^ 4 * ((1 + L) / L ^ 2) := by ring
      _ ≤ D ^ 2 * b ^ 4 * 2 := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ ≤ D ^ 2 * b ^ 6 * 2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb (by norm_num : 4 ≤ 6)) (sq_nonneg D)) zero_le_two
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hsL (show 0 ≤ 2 * D ^ 2 * b ^ 6 by positivity)
        nlinarith only [h]
  have hlogL : Real.log L ≤ 2 * Real.sqrt L := by
    have h := _root_.RHTower.WeilAbscissa.log_div_sqrt_le hL
    have hs0 : 0 < Real.sqrt L := zero_lt_one.trans_le hsL
    have hh : Real.log L / Real.sqrt L ≤ 2 := by simpa only [div_eq_mul_inv] using h
    exact (div_le_iff₀ hs0).mp hh
  have hlogT : 1 + Real.log (2 * T) ≤ 12 * b * Real.sqrt L := by
    have hid : 2 * T = (8 * b) * L ^ 2 := by dsimp only [T]; ring
    rw [hid, Real.log_mul (by positivity) (pow_ne_zero 2 hL0.ne'), Real.log_pow]
    have hlogb := Real.log_le_sub_one_of_pos (show 0 < 8 * b by positivity)
    have h1 := mul_le_mul_of_nonneg_left hsL (show 0 ≤ 8 * b by positivity)
    have h2 := mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg L)
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hlogb, hlogL, h1, h2]
  have htail : (D * b ^ 2) ^ 2 * (1 + Real.log (2 * T)) ≤ 12 * D ^ 2 * b ^ 6 * Real.sqrt L := by
    calc
      _ ≤ (D * b ^ 2) ^ 2 * (12 * b * Real.sqrt L) :=
        mul_le_mul_of_nonneg_left hlogT (sq_nonneg _)
      _ = 12 * D ^ 2 * b ^ 5 * Real.sqrt L := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb (by norm_num : 5 ≤ 6)) (by positivity))
        (Real.sqrt_nonneg L)
  have hraw : (∑ n ∈ Icc 1 N, R n ^ 2) ≤ 14 * D ^ 2 * b ^ 6 * Real.sqrt L := by
    have h := hsum.trans (add_le_add hhead htail)
    nlinarith only [h]
  change (∑ n ∈ Icc 1 N, R n ^ 2) / L ≤ (14 * D ^ 2) * b ^ 6 / Real.sqrt L
  calc
    _ ≤ (14 * D ^ 2 * b ^ 6 * Real.sqrt L) / L := div_le_div_of_nonneg_right hraw hL0.le
    _ = (14 * D ^ 2 * b ^ 6 * Real.sqrt L) / (Real.sqrt L) ^ 2 := by rw [Real.sq_sqrt hL0.le]
    _ = _ := by field_simp

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.primeIndexBoundaryMass_le_sqrt
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_linearizedUpwardCoefficient_boundary_polynomial_harmonic_bound
