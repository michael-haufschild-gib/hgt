import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowContinuation
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.NumberTheory.LSeries.Dirichlet

set_option maxHeartbeats 800000

open Complex Finset Set

noncomputable section

namespace RHTower

/-- The exact dyadic weighted von-Mangoldt window at the integer scale `n`. -/
def dyadicWeightedPrimeWindow (n : ℕ) : ℝ :=
  ∑ k ∈ Ioc (n / 2) n,
    ArithmeticFunction.vonMangoldt k / Real.sqrt k

/-- The internal integer-window form is exactly the floor-and-negative-power expression in the
dyadic prime inequality. -/
theorem dyadicWeightedPrimeWindow_eq_floorSum (n : ℕ) :
    dyadicWeightedPrimeWindow n =
      ∑ k ∈ Ioc ⌊(n : ℝ) / 2⌋₊ n,
        ((k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k := by
  have hfloor : ⌊(n : ℝ) / 2⌋₊ = n / 2 := by
    simpa using (Nat.floor_div_eq_div (K := ℝ) n 2)
  rw [dyadicWeightedPrimeWindow, hfloor]
  apply Finset.sum_congr rfl
  intro k hk
  rcases k.eq_zero_or_pos with rfl | hkpos
  · norm_num
  · have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hkreal.le]
    ring

/-- One term before regrouping the moving-window sum by its output index. -/
def dyadicSharpPrimeWindowDoubleTerm (s : ℂ) (kj : ℕ × ℕ) : ℂ :=
  if kj.2 < kj.1 then
    ((ArithmeticFunction.vonMangoldt kj.1 / Real.sqrt kj.1 : ℝ) : ℂ) *
      (((kj.1 + kj.2 : ℕ) : ℂ) ^ (-s))
  else 0

private theorem summable_norm_dyadicSharpPrimeWindowDoubleTerm
    {s : ℂ} (hs : 3 / 2 < s.re) :
    Summable (fun kj : ℕ × ℕ => ‖dyadicSharpPrimeWindowDoubleTerm s kj‖) := by
  rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
  constructor
  · intro k
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset (Finset.finite_toSet (range k))
    intro j hj
    simp only [Function.mem_support] at hj
    simp only [mem_coe, Finset.mem_range]
    by_contra hnot
    simp only [dyadicSharpPrimeWindowDoubleTerm, Prod.fst, Prod.snd,
      if_neg hnot, norm_zero] at hj
    exact hj rfl
  · let z : ℂ := ((s.re - 1 / 2 : ℝ) : ℂ)
    have hz : 1 < z.re := by
      dsimp only [z]
      simp only [ofReal_re]
      linarith
    have hvm : LSeriesSummable
        (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) z :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt hz
    apply Summable.of_norm_bounded hvm.norm
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
    rcases k.eq_zero_or_pos with rfl | hk
    · simp [dyadicSharpPrimeWindowDoubleTerm]
    · have hk0 : k ≠ 0 := Nat.ne_of_gt hk
      have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
      rw [tsum_eq_sum (s := range k) (fun j hj => by
        simp only [Finset.mem_range] at hj
        simp only [dyadicSharpPrimeWindowDoubleTerm, Prod.fst, Prod.snd,
          if_neg hj, norm_zero])]
      calc
        (∑ j ∈ range k, ‖dyadicSharpPrimeWindowDoubleTerm s (k, j)‖) ≤
            ∑ _j ∈ range k,
              ArithmeticFunction.vonMangoldt k / Real.sqrt k *
                (k : ℝ) ^ (-s.re) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjk : j < k := mem_range.mp hj
          have hkjpos : 0 < k + j := by omega
          have hkle : (k : ℝ) ≤ ((k + j : ℕ) : ℝ) := by
            exact_mod_cast (show k ≤ k + j by omega)
          rw [dyadicSharpPrimeWindowDoubleTerm, if_pos hjk,
            norm_mul, norm_real, Real.norm_eq_abs,
            abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
              (Real.sqrt_nonneg k)),
            Complex.norm_natCast_cpow_of_pos hkjpos]
          simp only [neg_re]
          apply mul_le_mul_of_nonneg_left _
            (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg k))
          exact Real.rpow_le_rpow_of_nonpos hkreal hkle (by linarith)
        _ = ArithmeticFunction.vonMangoldt k / Real.sqrt k *
              ((k : ℝ) * (k : ℝ) ^ (-s.re)) := by
          rw [sum_const, card_range, nsmul_eq_mul]
          ring
        _ = ‖LSeries.term
              (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) z k‖ := by
          rw [LSeries.term_of_ne_zero hk0, norm_div, norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
            Complex.norm_natCast_cpow_of_pos hk]
          simp only [z, ofReal_re]
          rw [Real.sqrt_eq_rpow]
          calc
            ArithmeticFunction.vonMangoldt k / (k : ℝ) ^ (1 / 2 : ℝ) *
                ((k : ℝ) * (k : ℝ) ^ (-s.re)) =
                ArithmeticFunction.vonMangoldt k *
                  ((k : ℝ) ^ (-(1 / 2 : ℝ)) *
                    ((k : ℝ) ^ (1 : ℝ) * (k : ℝ) ^ (-s.re))) := by
              rw [div_eq_mul_inv, ← Real.rpow_neg hkreal.le, Real.rpow_one]
              ring
            _ = ArithmeticFunction.vonMangoldt k *
                (k : ℝ) ^ (-(1 / 2 : ℝ) + (1 + -s.re)) := by
              rw [← Real.rpow_add hkreal, ← Real.rpow_add hkreal]
            _ = ArithmeticFunction.vonMangoldt k /
                (k : ℝ) ^ (s.re - 1 / 2) := by
              rw [show -(1 / 2 : ℝ) + (1 + -s.re) =
                  -(s.re - 1 / 2) by ring,
                Real.rpow_neg hkreal.le]
              ring

theorem summable_dyadicSharpPrimeWindowDoubleTerm
    {s : ℂ} (hs : 3 / 2 < s.re) :
    Summable (dyadicSharpPrimeWindowDoubleTerm s) :=
  (summable_norm_dyadicSharpPrimeWindowDoubleTerm hs).of_norm

theorem tsum_dyadicSharpPrimeWindowDoubleTerm_right
    (k : ℕ) (s : ℂ) :
    (∑' j : ℕ, dyadicSharpPrimeWindowDoubleTerm s (k, j)) =
      ((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ) *
        dyadicSharpPrimeWindowKernel k s := by
  rw [tsum_eq_sum (s := range k) (fun j hj => by
    simp only [Finset.mem_range] at hj
    simp only [dyadicSharpPrimeWindowDoubleTerm, if_neg hj])]
  rw [dyadicSharpPrimeWindowKernel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [dyadicSharpPrimeWindowDoubleTerm,
    if_pos (Finset.mem_range.mp hj)]

private theorem antidiagonal_doubleTerm_eq_LSeriesTerm_window
    (s : ℂ) (n : ℕ) :
    (∑' p : ↥(Finset.HasAntidiagonal.antidiagonal n),
        dyadicSharpPrimeWindowDoubleTerm s p.1) =
      LSeries.term (fun m => ((dyadicWeightedPrimeWindow m : ℝ) : ℂ)) s n := by
  rw [tsum_fintype]
  rw [← Finset.sum_subtype (Finset.HasAntidiagonal.antidiagonal n) (fun _ => Iff.rfl)
    (fun p => dyadicSharpPrimeWindowDoubleTerm s p)]
  change (∑ a ∈ Finset.HasAntidiagonal.antidiagonal n,
    dyadicSharpPrimeWindowDoubleTerm s (a.1, a.2)) = _
  rw [show (∑ a ∈ Finset.HasAntidiagonal.antidiagonal n,
      dyadicSharpPrimeWindowDoubleTerm s (a.1, a.2)) =
      ∑ k ∈ range n.succ,
        dyadicSharpPrimeWindowDoubleTerm s (k, n - k) by
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k j => dyadicSharpPrimeWindowDoubleTerm s (k, j)) n]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [dyadicSharpPrimeWindowDoubleTerm, dyadicWeightedPrimeWindow]
  · rw [LSeries.term_of_ne_zero hn.ne']
    rw [dyadicWeightedPrimeWindow, ofReal_sum]
    rw [Finset.sum_div]
    rw [← Finset.sum_div]
    rw [Finset.sum_div]
    have hset : (range n.succ).filter (fun k => n - k < k) =
        Finset.Ioc (n / 2) n := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
        Finset.mem_Ioc]
      omega
    calc
      (∑ k ∈ range n.succ,
          dyadicSharpPrimeWindowDoubleTerm s (k, n - k)) =
          ∑ k ∈ (range n.succ).filter (fun k => n - k < k),
            ((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ) *
              ((n : ℂ) ^ (-s)) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro k hk
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
        by_cases hcond : n - k < k
        · rw [if_pos hcond, dyadicSharpPrimeWindowDoubleTerm, if_pos hcond,
            Nat.add_sub_of_le hkn]
        · rw [if_neg hcond, dyadicSharpPrimeWindowDoubleTerm, if_neg hcond]
      _ = ∑ k ∈ Ioc (n / 2) n,
            ((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ) *
              ((n : ℂ) ^ (-s)) := by rw [hset]
      _ = ∑ i ∈ Ioc (n / 2) n,
            ((ArithmeticFunction.vonMangoldt i / Real.sqrt i : ℝ) : ℂ) /
              (n : ℂ) ^ s := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Complex.cpow_neg]
        ring

/-- Reversing the sharp moving-window sum produces exactly the dyadic kernel series. -/
theorem LSeries_dyadicWeightedPrimeWindow_eq_kernelSeries
    {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeries (fun n => ((dyadicWeightedPrimeWindow n : ℝ) : ℂ)) s =
      ∑' k : ℕ,
        ((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ) *
          dyadicSharpPrimeWindowKernel k s := by
  let e := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ))
  have hdouble := summable_dyadicSharpPrimeWindowDoubleTerm hs
  have hsigma : Summable
      (fun p : (n : ℕ) × ↥(Finset.HasAntidiagonal.antidiagonal n) =>
      dyadicSharpPrimeWindowDoubleTerm s (e p)) := by
    exact e.summable_iff.mpr hdouble
  rw [LSeries]
  calc
    (∑' n : ℕ,
        LSeries.term (fun m => ((dyadicWeightedPrimeWindow m : ℝ) : ℂ)) s n) =
        ∑' n : ℕ, ∑' p : ↥(Finset.HasAntidiagonal.antidiagonal n),
          dyadicSharpPrimeWindowDoubleTerm s p.1 := by
      apply tsum_congr
      intro n
      exact (antidiagonal_doubleTerm_eq_LSeriesTerm_window s n).symm
    _ = ∑' p : (n : ℕ) × ↥(Finset.HasAntidiagonal.antidiagonal n),
          dyadicSharpPrimeWindowDoubleTerm s (e p) := by
      change (∑' n : ℕ,
        ∑' p : ↥(Finset.HasAntidiagonal.antidiagonal n),
        dyadicSharpPrimeWindowDoubleTerm s (e ⟨n, p⟩)) = _
      rw [← hsigma.tsum_sigma]
    _ = ∑' kj : ℕ × ℕ, dyadicSharpPrimeWindowDoubleTerm s kj :=
      e.tsum_eq (dyadicSharpPrimeWindowDoubleTerm s)
    _ = ∑' k : ℕ, ∑' j : ℕ,
          dyadicSharpPrimeWindowDoubleTerm s (k, j) := hdouble.tsum_prod
    _ = ∑' k : ℕ,
        ((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ) *
          dyadicSharpPrimeWindowKernel k s := by
      apply tsum_congr
      intro k
      exact tsum_dyadicSharpPrimeWindowDoubleTerm_right k s

theorem dyadicWeightedPrimeWindow_LSeriesSummable
    {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable
      (fun n => ((dyadicWeightedPrimeWindow n : ℝ) : ℂ)) s := by
  let e := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ))
  have hdouble := summable_dyadicSharpPrimeWindowDoubleTerm hs
  have hsigma : Summable
      (fun p : (n : ℕ) × ↥(Finset.HasAntidiagonal.antidiagonal n) =>
      dyadicSharpPrimeWindowDoubleTerm s (e p)) := by
    exact e.summable_iff.mpr hdouble
  exact hsigma.sigma.congr fun n => by
    change
      (∑' p : ↥(Finset.HasAntidiagonal.antidiagonal n),
        dyadicSharpPrimeWindowDoubleTerm s p.1) =
        LSeries.term (fun m => ((dyadicWeightedPrimeWindow m : ℝ) : ℂ)) s n
    exact antidiagonal_doubleTerm_eq_LSeriesTerm_window s n

private theorem weighted_dyadicKernel_eq_main_add_error
    (k : ℕ) (s : ℂ) :
    ((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ) *
        dyadicSharpPrimeWindowKernel k s =
      sharpPrimeWindowMellin (Real.log 2) s *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (s - 1 / 2) k +
        dyadicSharpPrimeWindowErrorSummand s k := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp [dyadicSharpPrimeWindowKernel, dyadicSharpPrimeWindowErrorSummand,
      dyadicSharpPrimeWindowError, dyadicSharpPrimeWindowIntegralMain]
  · have hk0 : k ≠ 0 := Nat.ne_of_gt hk
    have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
    rw [dyadicSharpPrimeWindowErrorSummand,
      dyadicSharpPrimeWindowError,
      dyadicSharpPrimeWindowIntegralMain_eq_scaledMellin hk s,
      LSeries.term_of_ne_zero hk0]
    have hsqrt : ((Real.sqrt k : ℝ) : ℂ) = (k : ℂ) ^ (1 / 2 : ℂ) := by
      rw [Real.sqrt_eq_rpow]
      simpa using Complex.ofReal_cpow (Nat.cast_nonneg k) (1 / 2 : ℝ)
    rw [ofReal_div, hsqrt]
    have hsqrt0 : (k : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hkC)
    have hpow : (k : ℂ) ^ (1 - s) / (k : ℂ) ^ (1 / 2 : ℂ) =
        1 / (k : ℂ) ^ (s - 1 / 2) := by
      rw [← Complex.cpow_sub _ _ hkC]
      rw [show (1 - s) - 1 / 2 = -(s - 1 / 2) by ring,
        Complex.cpow_neg]
      simp only [one_div]
    rw [mul_sub]
    have hmain :
        (((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ) /
            (k : ℂ) ^ (1 / 2 : ℂ)) *
              ((k : ℂ) ^ (1 - s) * sharpPrimeWindowMellin (Real.log 2) s) =
          sharpPrimeWindowMellin (Real.log 2) s *
            (((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ) /
              (k : ℂ) ^ (s - 1 / 2)) := by
      calc
        (((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ) /
            (k : ℂ) ^ (1 / 2 : ℂ)) *
              ((k : ℂ) ^ (1 - s) * sharpPrimeWindowMellin (Real.log 2) s) =
            ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ) *
              ((k : ℂ) ^ (1 - s) / (k : ℂ) ^ (1 / 2 : ℂ)) *
                sharpPrimeWindowMellin (Real.log 2) s := by ring
        _ = _ := by rw [hpow]; ring
    rw [hmain]
    ring

/-- The honest weighted-window Dirichlet series is the von-Mangoldt logarithmic derivative
multiplied by the dyadic Mellin factor, plus the holomorphic quadrature remainder. -/
theorem LSeries_dyadicWeightedPrimeWindow_eq_zetaLogDeriv
    {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeries (fun n => ((dyadicWeightedPrimeWindow n : ℝ) : ℂ)) s =
      -sharpPrimeWindowMellin (Real.log 2) s *
          zetaLogDeriv (s - 1 / 2) +
        dyadicSharpPrimeWindowErrorSeries s := by
  have hshift : 1 < (s - 1 / 2).re := by
    norm_num [Complex.sub_re] at hs ⊢
    linarith
  have hvm : LSeriesSummable
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s - 1 / 2) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hshift
  have hmain : Summable (fun k =>
      sharpPrimeWindowMellin (Real.log 2) s *
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (s - 1 / 2) k) := hvm.mul_left _
  have herr := summable_dyadicSharpPrimeWindowErrorSummand
    (by linarith : 1 / 2 < s.re)
  calc
    LSeries (fun n => ((dyadicWeightedPrimeWindow n : ℝ) : ℂ)) s =
        ∑' k : ℕ,
          ((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ) *
            dyadicSharpPrimeWindowKernel k s :=
      LSeries_dyadicWeightedPrimeWindow_eq_kernelSeries hs
    _ = ∑' k : ℕ,
        (sharpPrimeWindowMellin (Real.log 2) s *
            LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (s - 1 / 2) k +
          dyadicSharpPrimeWindowErrorSummand s k) := by
      apply tsum_congr
      intro k
      exact weighted_dyadicKernel_eq_main_add_error k s
    _ = (∑' k : ℕ,
          sharpPrimeWindowMellin (Real.log 2) s *
            LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (s - 1 / 2) k) +
        ∑' k : ℕ, dyadicSharpPrimeWindowErrorSummand s k :=
      hmain.tsum_add herr
    _ = sharpPrimeWindowMellin (Real.log 2) s *
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (s - 1 / 2) +
        dyadicSharpPrimeWindowErrorSeries s := by
      rw [tsum_mul_left]
      rfl
    _ = -sharpPrimeWindowMellin (Real.log 2) s *
          zetaLogDeriv (s - 1 / 2) +
        dyadicSharpPrimeWindowErrorSeries s := by
      rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hshift,
        zetaLogDeriv]
      ring

/-- The source-defined sharp coefficient whose lower subpower control is the requested upper
subpower estimate for the dyadic weighted prime window. -/
def dyadicSharpPrimeSourceCoefficient (n : ℕ) : ℝ :=
  4 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n -
    2 * dyadicWeightedPrimeWindow n

/-- The requested upper estimate is pointwise identical to a lower estimate for the exact
source coefficient, with only the harmless factor two on the correction constant. -/
theorem dyadicWeightedPrimeWindow_upper_iff_sourceCoefficient_lower
    (n : ℕ) (C epsilon : ℝ) :
    dyadicWeightedPrimeWindow n ≤
        2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
          C * (n : ℝ) ^ epsilon ↔
      0 ≤ dyadicSharpPrimeSourceCoefficient n +
        2 * C * (n : ℝ) ^ epsilon := by
  rw [dyadicSharpPrimeSourceCoefficient]
  constructor <;> intro h <;> linarith

theorem dyadicSharpPrimeSourceCoefficient_LSeriesSummable
    {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ)) s := by
  have hsqrt := RHTower.CompactBVPrimeWindow.sqrt_LSeriesSummable hs
  have hwindow := dyadicWeightedPrimeWindow_LSeriesSummable hs
  have hdiff := (hsqrt.smul
    ((4 * (1 - (Real.sqrt 2)⁻¹) : ℝ) : ℂ)).sub
      (hwindow.smul (2 : ℂ))
  change Summable
    (LSeries.term (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ)) s)
  change Summable (LSeries.term _ s) at hdiff
  exact hdiff.congr fun n => by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [LSeries.term_zero]
    · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
      rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        dyadicSharpPrimeSourceCoefficient, ofReal_sub, ofReal_mul]
      norm_num

private theorem sharpPrimeWindowMellin_logTwo_three_halves :
    sharpPrimeWindowMellin (Real.log 2) (3 / 2 : ℂ) =
      2 * (1 - (Real.sqrt 2)⁻¹) := by
  rw [sharpPrimeWindowMellin_three_halves]
  have hexpReal : Real.exp (-Real.log 2 / 2) = (Real.sqrt 2)⁻¹ := by
    rw [show -Real.log 2 / 2 = -(Real.log 2 / 2) by ring,
      Real.exp_neg]
    have hexpHalf : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
      rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        Real.exp_log (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]
    rw [hexpHalf]
  have hexpComplex : Complex.exp (-(Real.log 2 : ℂ) / 2) =
      ((Real.sqrt 2)⁻¹ : ℝ) := by
    rw [show -(Real.log 2 : ℂ) / 2 = ((-Real.log 2 / 2 : ℝ) : ℂ) by
      norm_num]
    rw [← Complex.ofReal_exp, hexpReal]
  rw [hexpComplex]

/-- **Initial-half-plane source identity.**  The ordinary Dirichlet series of the exact finite
sharp prime--polar coefficient is the canonical pole-filled continued source. -/
theorem LSeries_dyadicSharpPrimeSourceCoefficient_eq_continuedSource
    {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeries
        (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ)) s =
      dyadicSharpPrimeContinuedSource s := by
  have hsqrt := RHTower.CompactBVPrimeWindow.sqrt_LSeriesSummable hs
  have hwindow := dyadicWeightedPrimeWindow_LSeriesSummable hs
  have hscaledSqrt := hsqrt.smul
    ((4 * (1 - (Real.sqrt 2)⁻¹) : ℝ) : ℂ)
  have hscaledWindow := hwindow.smul (2 : ℂ)
  have hcontinued := dyadicSharpPrimeContinuedSource_eq_zetaLogDeriv hs
  calc
    LSeries
        (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ)) s =
        LSeries
          (((4 * (1 - (Real.sqrt 2)⁻¹) : ℝ) : ℂ) •
              (fun n : ℕ => ((Real.sqrt n : ℝ) : ℂ)) -
            (2 : ℂ) •
              (fun n => ((dyadicWeightedPrimeWindow n : ℝ) : ℂ))) s := by
      apply LSeries_congr
      intro n hn
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        dyadicSharpPrimeSourceCoefficient, ofReal_sub, ofReal_mul]
      norm_num
    _ = ((4 * (1 - (Real.sqrt 2)⁻¹) : ℝ) : ℂ) *
          LSeries (fun n : ℕ => ((Real.sqrt n : ℝ) : ℂ)) s -
        2 * LSeries
          (fun n => ((dyadicWeightedPrimeWindow n : ℝ) : ℂ)) s := by
      rw [LSeries_sub hscaledSqrt hscaledWindow, LSeries_smul, LSeries_smul]
    _ = ((4 * (1 - (Real.sqrt 2)⁻¹) : ℝ) : ℂ) *
          riemannZeta (s - 1 / 2) -
        2 * (-sharpPrimeWindowMellin (Real.log 2) s *
            zetaLogDeriv (s - 1 / 2) +
          dyadicSharpPrimeWindowErrorSeries s) := by
      rw [RHTower.CompactBVPrimeWindow.LSeries_sqrt_eq_riemannZeta_shift hs,
        LSeries_dyadicWeightedPrimeWindow_eq_zetaLogDeriv hs]
    _ = 2 * sharpPrimeWindowMellin (Real.log 2) (3 / 2) *
          riemannZeta (s - 1 / 2) +
        2 * sharpPrimeWindowMellin (Real.log 2) s *
          zetaLogDeriv (s - 1 / 2) -
        2 * dyadicSharpPrimeWindowErrorSeries s := by
      rw [sharpPrimeWindowMellin_logTwo_three_halves]
      norm_num
      ring
    _ = dyadicSharpPrimeContinuedSource s := hcontinued.symm

end RHTower
