import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowSquarePositiveExcessDuality
import GaloisForLFunctions.RHTower.XiThermalPrimeSquareEnergySpectrum

/-!
# Chebyshev-width transfer for sharp windows and square-aperture positive excess

This file isolates and proves the exact Abel-transfer theorem needed to compare both Route I's
literal pointwise sharp-window endpoint and its square-aperture Hilbert energy with the classical
zero-width invariant.

If the Chebyshev error satisfies

`|ψ(x) - x| = Oε(x^(1/2 + α + ε))`,

then the dyadic critical-Mellin error increment is

`Oε(n^(α + ε))`.

The same estimate gives the eventual pointwise sharp-window upper spectrum at width `alpha`, and
the existing fixed-power Landau theorem recovers `XiZeroHalfPlaneBound alpha` from that spectrum.
After sampling at `n = m²` and squaring the positive part, the corresponding Dirichlet abscissa is
at most `1 + 4α`; existing zero-by-zero lower bounds give the reverse inequality at intrinsic
rightmost Xi displacement. Thus, once the classical generalized von Koch source estimate is
supplied, neither pointwise nor square-aperture spectrum is an independent source mechanism.

All results here are unconditional Lean theorems.  In particular, the analytic source estimate is
an explicit hypothesis, not an axiom or hidden declaration.
-/

open Complex Filter Function Set LSeries MeasureTheory

namespace RHTower

noncomputable section

/-- Power spectrum of the Chebyshev error at transverse width `alpha`. -/
def ChebyshevErrorPowerSpectrum (alpha : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) x| ≤
        C * x ^ (1 / 2 + alpha + epsilon)

/-- The Abel primitive of an error of size `t^(1/2+beta)` contributes at most
`(C/beta) X^beta`. -/
private lemma criticalMellinError_integral_bound
    {E : ℝ → ℝ} {C beta X : ℝ}
    (hC : 0 ≤ C) (hbeta : 0 < beta) (hX : 1 ≤ X)
    (hE : ∀ t : ℝ, 1 ≤ t → |E t| ≤ C * t ^ (1 / 2 + beta)) :
    |∫ t in Set.Ioc (1 : ℝ) X, E t * t ^ (-3 / 2 : ℝ)| ≤
      C / beta * X ^ beta := by
  rw [← intervalIntegral.integral_of_le hX]
  rw [← Real.norm_eq_abs]
  have hzero : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) X := by
    rw [Set.uIcc_of_le hX]
    intro h
    linarith [h.1]
  have hmajorInt : IntervalIntegrable (fun t : ℝ => C * t ^ (beta - 1))
      MeasureTheory.volume 1 X :=
    (intervalIntegral.intervalIntegrable_rpow
      (Or.inr hzero)).const_mul C
  calc
    ‖∫ t in (1 : ℝ)..X, E t * t ^ (-3 / 2 : ℝ)‖ ≤
        ∫ t in (1 : ℝ)..X, C * t ^ (beta - 1) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hX
      · filter_upwards with t ht
        have ht1 : 1 ≤ t := ht.1.le
        have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
        calc
          |E t| * t ^ (-3 / 2 : ℝ) ≤
              (C * t ^ (1 / 2 + beta)) * t ^ (-3 / 2 : ℝ) := by
            exact mul_le_mul_of_nonneg_right (hE t ht1)
              (Real.rpow_nonneg ht0.le _)
          _ = C * (t ^ (1 / 2 + beta) * t ^ (-3 / 2 : ℝ)) := by ring
          _ = C * t ^ (beta - 1) := by
            rw [← Real.rpow_add ht0]
            congr 2
            ring
      · exact hmajorInt
    _ = C * ((X ^ beta - 1) / beta) := by
      rw [intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by linarith : -1 < beta - 1))]
      rw [show beta - 1 + 1 = beta by ring, Real.one_rpow]
    _ ≤ C / beta * X ^ beta := by
      have hXpow : 0 ≤ X ^ beta := Real.rpow_nonneg (by linarith) _
      rw [div_eq_mul_inv, div_eq_mul_inv]
      nlinarith [inv_pos.mpr hbeta]

/-- Quantitative Abel transfer from a Chebyshev error exponent to the exact sharp-window
critical-Mellin increment. -/
theorem dyadicCriticalMellinErrorIncrement_abs_le_of_chebyshevErrorPower
    {alpha epsilon C : ℝ} (halpha : 0 ≤ alpha) (hepsilon : 0 < epsilon)
    (hC : 0 ≤ C)
    (herror : ∀ x : ℝ, 1 ≤ x →
      |criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) x| ≤
        C * x ^ (1 / 2 + alpha + epsilon))
    {n : ℕ} (hn : 2 ≤ n) :
    |dyadicCriticalMellinErrorIncrement n| ≤
      (2 * C + C / (alpha + epsilon)) * (n : ℝ) ^ (alpha + epsilon) := by
  let beta : ℝ := alpha + epsilon
  have hbeta : 0 < beta := by dsimp only [beta]; linarith
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hhalf1 : (1 : ℝ) ≤ (n : ℝ) / 2 := by linarith
  have hhalf0 : (0 : ℝ) < (n : ℝ) / 2 := by linarith
  have hpowHalf : ((n : ℝ) / 2) ^ beta ≤ (n : ℝ) ^ beta :=
    Real.rpow_le_rpow hhalf0.le (by linarith) hbeta.le
  have hEndFull :
      |criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) n /
          Real.sqrt n| ≤ C * (n : ℝ) ^ beta := by
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
    calc
      |criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) n| /
            Real.sqrt n ≤
          (C * (n : ℝ) ^ (1 / 2 + alpha + epsilon)) / Real.sqrt n := by
        gcongr
        simpa only [show (1 / 2 + alpha + epsilon : ℝ) = 1 / 2 + beta by
          dsimp only [beta]
          ring] using herror n (by linarith)
      _ = C * (n : ℝ) ^ beta := by
        rw [show (1 / 2 + alpha + epsilon : ℝ) = 1 / 2 + beta by
          dsimp only [beta]
          ring, Real.rpow_add hn0, ← Real.sqrt_eq_rpow]
        field_simp [Real.sqrt_pos.mpr hn0]
  have hEndHalf :
      |criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) ((n : ℝ) / 2) /
          Real.sqrt ((n : ℝ) / 2)| ≤ C * (n : ℝ) ^ beta := by
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      |criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) ((n : ℝ) / 2)| /
            Real.sqrt ((n : ℝ) / 2) ≤
          (C * ((n : ℝ) / 2) ^ (1 / 2 + alpha + epsilon)) /
            Real.sqrt ((n : ℝ) / 2) := by
        gcongr
        simpa only [show (1 / 2 + alpha + epsilon : ℝ) = 1 / 2 + beta by
          dsimp only [beta]
          ring] using herror ((n : ℝ) / 2) hhalf1
      _ = C * ((n : ℝ) / 2) ^ beta := by
        rw [show (1 / 2 + alpha + epsilon : ℝ) = 1 / 2 + beta by
          dsimp only [beta]
          ring, Real.rpow_add hhalf0, ← Real.sqrt_eq_rpow]
        field_simp [Real.sqrt_pos.mpr hhalf0]
      _ ≤ C * (n : ℝ) ^ beta := mul_le_mul_of_nonneg_left hpowHalf hC
  have hIntFull := criticalMellinError_integral_bound hC hbeta
    (by linarith : (1 : ℝ) ≤ n)
    (fun t ht => by
      simpa only [show (1 / 2 + alpha + epsilon : ℝ) = 1 / 2 + beta by
        dsimp only [beta]
        ring] using herror t ht)
  have hIntHalf := criticalMellinError_integral_bound hC hbeta hhalf1
    (fun t ht => by
      simpa only [show (1 / 2 + alpha + epsilon : ℝ) = 1 / 2 + beta by
        dsimp only [beta]
        ring] using herror t ht)
  have hIntHalf' :
      |∫ t in Set.Ioc (1 : ℝ) ((n : ℝ) / 2),
          criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) t *
            t ^ (-3 / 2 : ℝ)| ≤ C / beta * (n : ℝ) ^ beta := by
    exact hIntHalf.trans
      (mul_le_mul_of_nonneg_left hpowHalf (div_nonneg hC hbeta.le))
  rw [dyadicCriticalMellinErrorIncrement]
  have htri := abs_add_le
    (criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) n /
        Real.sqrt n -
      criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) ((n : ℝ) / 2) /
        Real.sqrt ((n : ℝ) / 2))
    ((1 / 2 : ℝ) *
      ((∫ t in Set.Ioc (1 : ℝ) n,
          criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) t *
            t ^ (-3 / 2 : ℝ)) -
        ∫ t in Set.Ioc (1 : ℝ) ((n : ℝ) / 2),
          criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) t *
            t ^ (-3 / 2 : ℝ)))
  have hsubEnd := abs_sub
    (criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) n / Real.sqrt n)
    (criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) ((n : ℝ) / 2) /
      Real.sqrt ((n : ℝ) / 2))
  have hsubInt := abs_sub
    (∫ t in Set.Ioc (1 : ℝ) n,
      criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) t *
        t ^ (-3 / 2 : ℝ))
    (∫ t in Set.Ioc (1 : ℝ) ((n : ℝ) / 2),
      criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) t *
        t ^ (-3 / 2 : ℝ))
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at htri
  dsimp only [beta] at hEndFull hEndHalf hIntFull hIntHalf' ⊢
  nlinarith

/-- At square apertures the centered deviation is exactly the Abel error increment. -/
theorem squarePrimeWindowCenteredDeviation_eq_errorIncrement
    {m : ℕ} (hm : 2 ≤ m) :
    squarePrimeWindowCenteredDeviation m =
      dyadicCriticalMellinErrorIncrement (m ^ 2) := by
  rw [squarePrimeWindowCenteredDeviation,
    dyadicWeightedPrimeWindow_eq_floorSum,
    dyadicWeightedPrimeWindow_eq_main_add_errorIncrement (by nlinarith)]
  simp only [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg m)]
  ring

/-- The one-sided square-aperture excess is dominated by the absolute Abel increment. -/
theorem squarePrimeWindowPositiveExcess_le_errorIncrement_abs
    {m : ℕ} (hm : 2 ≤ m) :
    dyadicWeightedPrimeWindowPositiveExcess (m ^ 2) ≤
      |dyadicCriticalMellinErrorIncrement (m ^ 2)| := by
  rw [squarePrimeWindowPositiveExcess_eq_posPart_centeredDeviation,
    squarePrimeWindowCenteredDeviation_eq_errorIncrement hm]
  exact max_le (le_abs_self _) (abs_nonneg _)

/-- Pointwise coefficient bound after square sampling and Hilbert squaring. -/
theorem squarePrimeWindowPositiveExcessSquare_coefficient_norm_le
    {alpha epsilon C : ℝ} (halpha : 0 ≤ alpha) (hepsilon : 0 < epsilon)
    (hC : 0 ≤ C)
    (herror : ∀ x : ℝ, 1 ≤ x →
      |criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) x| ≤
        C * x ^ (1 / 2 + alpha + epsilon))
    {m : ℕ} (hm : 2 ≤ m) :
    ‖squarePrimeWindowPositiveExcessSquareDirichletCoefficient m‖ ≤
      (2 * C + C / (alpha + epsilon)) ^ 2 *
        (m : ℝ) ^ (4 * (alpha + epsilon)) := by
  let D : ℝ := 2 * C + C / (alpha + epsilon)
  have hbeta : 0 < alpha + epsilon := by linarith
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  have hinc :=
    dyadicCriticalMellinErrorIncrement_abs_le_of_chebyshevErrorPower
      halpha hepsilon hC herror hm2
  have hexcess := squarePrimeWindowPositiveExcess_le_errorIncrement_abs hm
  have hexcessNonneg := dyadicWeightedPrimeWindowPositiveExcess_nonneg (m ^ 2)
  have hbound : dyadicWeightedPrimeWindowPositiveExcess (m ^ 2) ≤
      D * ((m ^ 2 : ℕ) : ℝ) ^ (alpha + epsilon) :=
    hexcess.trans hinc
  rw [squarePrimeWindowPositiveExcessSquareDirichletCoefficient,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc
    dyadicWeightedPrimeWindowPositiveExcess (m ^ 2) ^ 2 ≤
        (D * ((m ^ 2 : ℕ) : ℝ) ^ (alpha + epsilon)) ^ 2 :=
      (sq_le_sq₀ hexcessNonneg
        (mul_nonneg hD (Real.rpow_nonneg (Nat.cast_nonneg _) _))).2 hbound
    _ = D ^ 2 * (m : ℝ) ^ (4 * (alpha + epsilon)) := by
      rw [Nat.cast_pow]
      have hinner : ((m : ℝ) ^ 2) ^ (alpha + epsilon) =
          (m : ℝ) ^ (2 * (alpha + epsilon)) := by
        rw [← Real.rpow_natCast]
        exact (Real.rpow_mul (Nat.cast_nonneg m) 2 (alpha + epsilon)).symm
      rw [mul_pow]
      congr 1
      rw [hinner]
      calc
        ((m : ℝ) ^ (2 * (alpha + epsilon))) ^ 2 =
            ((m : ℝ) ^ (2 * (alpha + epsilon))) ^ (2 : ℝ) := by
          exact (Real.rpow_natCast
            ((m : ℝ) ^ (2 * (alpha + epsilon))) 2).symm
        _ = (m : ℝ) ^ ((2 * (alpha + epsilon)) * 2) :=
          (Real.rpow_mul (Nat.cast_nonneg m) (2 * (alpha + epsilon)) 2).symm
        _ = (m : ℝ) ^ (4 * (alpha + epsilon)) := by ring_nf

/-- **Chebyshev-to-square-energy width transfer.**  A Chebyshev error width `alpha` gives the
sharp square-energy abscissa upper bound `1 + 4*alpha`. -/
theorem squarePrimeWindowPositiveExcessSquare_abscissa_le_of_chebyshevErrorPowerSpectrum
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (herror : ChebyshevErrorPowerSpectrum alpha) :
    LSeries.abscissaOfAbsConv
        squarePrimeWindowPositiveExcessSquareDirichletCoefficient ≤
      (((1 + 4 * alpha : ℝ) : EReal)) := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  have hyR : 1 + 4 * alpha < y := by exact_mod_cast hy
  let epsilon : ℝ := (y - (1 + 4 * alpha)) / 8
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  obtain ⟨C, hC, hCerror⟩ := herror epsilon hepsilon
  let D : ℝ := 2 * C + C / (alpha + epsilon)
  let B : ℝ := max (D ^ 2)
    ‖squarePrimeWindowPositiveExcessSquareDirichletCoefficient 1‖
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hBnonneg : 0 ≤ B := le_trans (sq_nonneg D) (le_max_left _ _)
  apply LSeriesSummable_of_le_const_mul_rpow
    (x := 1 + 4 * (alpha + epsilon))
  · norm_num [epsilon]
    linarith
  · refine ⟨B, ?_⟩
    intro m hm
    have hmPos : 0 < m := Nat.pos_of_ne_zero hm
    by_cases hmOne : m = 1
    · subst m
      simp [B]
    · have hm2 : 2 ≤ m := by omega
      have hcoeff :=
        squarePrimeWindowPositiveExcessSquare_coefficient_norm_le
          halpha hepsilon hC hCerror hm2
      have hDB : D ^ 2 ≤ B := le_max_left _ _
      have hpowNonneg : 0 ≤ (m : ℝ) ^ (4 * (alpha + epsilon)) :=
        Real.rpow_nonneg (Nat.cast_nonneg m) _
      calc
        ‖squarePrimeWindowPositiveExcessSquareDirichletCoefficient m‖ ≤
            D ^ 2 * (m : ℝ) ^ (4 * (alpha + epsilon)) := hcoeff
        _ ≤ B * (m : ℝ) ^ (4 * (alpha + epsilon)) :=
          mul_le_mul_of_nonneg_right hDB hpowNonneg
        _ = B * (m : ℝ) ^ ((1 + 4 * (alpha + epsilon)) - 1) := by
          congr 2
          ring

/-- Eventual all-epsilon upper spectrum of the literal sharp dyadic prime window at transverse
width `alpha`.  The cutoff is fixed before `epsilon` is chosen. -/
def DyadicWeightedPrimeWindowPowerUpper (alpha : ℝ) (N : ℕ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
      dyadicWeightedPrimeWindow n ≤
        2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
          C * (n : ℝ) ^ (alpha + epsilon)

/-- Exact endpoint identification with the original Route I source predicate. -/
theorem dyadicWeightedPrimeWindowPowerUpper_zero_iff_subpowerUpper (N : ℕ) :
    DyadicWeightedPrimeWindowPowerUpper 0 N ↔
      DyadicWeightedPrimeWindowSubpowerUpper N := by
  simp only [DyadicWeightedPrimeWindowPowerUpper,
    DyadicWeightedPrimeWindowSubpowerUpper, zero_add]

/-- The Chebyshev error spectrum transfers not only to square energy but to the literal pointwise
sharp-window upper spectrum. -/
theorem dyadicWeightedPrimeWindowPowerUpper_of_chebyshevErrorPowerSpectrum
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (herror : ChebyshevErrorPowerSpectrum alpha) :
    DyadicWeightedPrimeWindowPowerUpper alpha 2 := by
  intro epsilon hepsilon
  obtain ⟨C, hC, hCerror⟩ := herror epsilon hepsilon
  let D : ℝ := 2 * C + C / (alpha + epsilon)
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  refine ⟨D, hD, ?_⟩
  intro n hn
  have hinc :=
    dyadicCriticalMellinErrorIncrement_abs_le_of_chebyshevErrorPower
      halpha hepsilon hC hCerror hn
  rw [dyadicWeightedPrimeWindow_eq_floorSum,
    dyadicWeightedPrimeWindow_eq_main_add_errorIncrement hn]
  simpa only [D, add_comm] using
    add_le_add_left ((le_abs_self _).trans hinc)
      (2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n)

/-- The literal pointwise upper spectrum recovers the same Xi half-plane width.  The proof uses
one intermediate exponent strictly between an offending zero and the claimed width, then invokes
the existing fixed-power Landau theorem. -/
theorem xiZeroHalfPlaneBound_of_dyadicWeightedPrimeWindowPowerUpper
    {alpha : ℝ} {N : ℕ} (halpha : 0 ≤ alpha)
    (hwindow : DyadicWeightedPrimeWindowPowerUpper alpha N) :
    XiZeroHalfPlaneBound alpha := by
  intro rho hzero
  by_contra hnot
  have hrho : 1 / 2 + alpha < rho.re := lt_of_not_ge hnot
  let epsilon : ℝ := (rho.re - (1 / 2 + alpha)) / 2
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  obtain ⟨C, hC, htail⟩ := hwindow epsilon hepsilon
  let support : XiDivisorSupport :=
    ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hpos := xi_divisor_pos_on_support support
  have hn : 0 < Int.toNat
      ((MeromorphicOn.divisor xi Set.univ) (support : ℂ)) := by
    omega
  let q : XiZeroCopy := ⟨support, ⟨0, hn⟩⟩
  have hqright : 0 < (I * xiSpectralPoint q).re := by
    have hcoord : I * xiSpectralPoint q = rho - 1 / 2 := by
      simpa only [q, support] using I_mul_xiSpectralPoint q
    rw [hcoord, Complex.sub_re]
    norm_num
    linarith
  let qr : XiRightZeroCopy := ⟨q, hqright⟩
  have hqbound :=
    xiRightCenteredZero_re_le_of_eventually_dyadicWeightedPrimeWindow_upper
      (alpha := alpha + epsilon) (N := N) (C := C)
      (by linarith) hC htail qr
  have hcoord : (xiRightCenteredZero qr).re = rho.re - 1 / 2 := by
    change (I * xiSpectralPoint q).re = _
    have heq : I * xiSpectralPoint q = rho - 1 / 2 := by
      simpa only [q, support] using I_mul_xiSpectralPoint q
    rw [heq, Complex.sub_re]
    norm_num
  rw [hcoord] at hqbound
  dsimp only [epsilon] at hqbound
  linarith

/-- Chebyshev width implies the matching Xi zero half-plane width.  This is the unconditional
reverse direction needed to certify that the source hypothesis carries genuine zero information. -/
theorem xiZeroHalfPlaneBound_of_chebyshevErrorPowerSpectrum
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (herror : ChebyshevErrorPowerSpectrum alpha) :
    XiZeroHalfPlaneBound alpha := by
  have habscissa :=
    squarePrimeWindowPositiveExcessSquare_abscissa_le_of_chebyshevErrorPowerSpectrum
      halpha herror
  intro rho hzero
  by_cases hrho : 1 / 2 < rho.re
  · have hlower :=
      four_mul_xi_zero_re_sub_one_le_squarePrimeWindowPositiveExcessSquare_abscissa
        hzero hrho
    have hreal : 4 * rho.re - 1 ≤ 1 + 4 * alpha := by
      exact_mod_cast hlower.trans habscissa
    linarith
  · linarith

/-- At intrinsic Xi width the classical Chebyshev source spectrum gives exact, rather than merely
one-sided, square-energy abscissa. -/
theorem squarePrimeWindowPositiveExcessSquare_abscissa_eq_intrinsicXiWidth
    (hne : Nonempty XiRightZeroCopy)
    (herror : ChebyshevErrorPowerSpectrum xiRightTransverseSup) :
    LSeries.abscissaOfAbsConv
        squarePrimeWindowPositiveExcessSquareDirichletCoefficient =
      (((1 + 4 * xiRightTransverseSup : ℝ) : EReal)) := by
  apply le_antisymm
  · exact
      squarePrimeWindowPositiveExcessSquare_abscissa_le_of_chebyshevErrorPowerSpectrum
        xiRightTransverseSup_nonneg herror
  · exact
      one_add_four_mul_xiRightTransverseSup_le_squarePrimeWindowPositiveExcessSquare_abscissa
        hne

/-- The zero-width Chebyshev source spectrum forces RH through the square-aperture energy
abscissa. -/
theorem riemannHypothesis_of_chebyshevErrorPowerSpectrum_zero
    (herror : ChebyshevErrorPowerSpectrum 0) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_squarePrimeWindowPositiveExcessSquare_abscissa_le_one
  simpa using
    squarePrimeWindowPositiveExcessSquare_abscissa_le_of_chebyshevErrorPowerSpectrum
      (alpha := 0) le_rfl herror

end

end RHTower
