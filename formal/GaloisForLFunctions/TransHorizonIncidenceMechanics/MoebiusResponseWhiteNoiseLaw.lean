import GaloisForLFunctions.TransHorizonIncidenceMechanics.MoebiusBezoutDecorrelation
import GaloisForLFunctions.BiScaleUncertainty.UniversalRamanujanCovarianceAndBiScaleRigidity
import GaloisForLFunctions.BezoutValuationIncidence.CofinalMobiusGradientCoercivityAndRenormalizedDefect
import GaloisForLFunctions.RHTower.Sieve.ReciprocalTotientLogBound
import GaloisForLFunctions.RHTower.Sieve.SquarefreeTotientDivisorIdentity

/-!
# The Möbius response is asymptotically white

Over a complete period the lag-`h` covariance of a sieve response is diagonal in the Selberg
coordinates with the Ramanujan lag weights as eigenvalues,
`Cov_N(h) = Σ_{2 ≤ e ≤ N} c_e(h) Y_N(e)²`. For the Möbius weight
`Y_N(e) = μ(e)/e · m_e(N/e)`, so every lag `h ≥ 1`, whose weights are bounded by `σ(h)`, sees only
the summable masses `τ(e)²/e²` against null coprime harmonic sums: `Cov_N(h; μ) → 0`.

The variance `Cov_N(0; μ) = Σ φ(e) Y_N(e)²` does not collapse. On the top octave `N/2 < e ≤ N` the
harmonic sum is `m_e(1) = 1`, so the variance is at least `Σ φ(e)/e²` over odd squarefree `e` there.
Cauchy–Schwarz against `Σ 1/φ(e) ≤ 8` (from `Σ_{e ≤ X} e/φ(e) ≤ 4X`) and the density `4/π²` of odd
squarefree integers give `Cov_N(0; μ) ≥ 1/288` at all large horizons.

Hence the normalized correlation `Cov_N(h)/Cov_N(0)` tends to zero at every lag `h ≥ 1`: on the
period torus the Möbius response is asymptotically white noise, every translation dissipates twice
the variance, and the dissipation rate `R_N(μ)` is bounded below by a positive constant.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

private theorem moebiusReal_sq_le_one (e : ℕ) : moebiusReal e ^ 2 ≤ 1 := by
  have h : |moebiusReal e| ≤ 1 := by
    unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  nlinarith [abs_nonneg (moebiusReal e), sq_abs (moebiusReal e)]

/-! ### Bounded multipliers on the Möbius Selberg coordinates -/

/-- `Y_N(e)² = μ(e)²/e² · m_e(N/e)²`. -/
theorem selbergMultiplesCoord_moebiusReal_sq (N e : ℕ) :
    selbergMultiplesCoord N moebiusReal e ^ 2 =
      moebiusReal e ^ 2 / (e : ℝ) ^ 2 * coprimeHarmonicMoebius e (N / e) ^ 2 := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · have h0 : selbergMultiplesCoord N moebiusReal 0 = 0 := by
      unfold selbergMultiplesCoord
      exact sum_eq_zero fun d hd => by
        simp only [mem_filter, mem_Icc, zero_dvd_iff] at hd; omega
    simp [h0, moebiusReal]
  · rw [selbergMultiplesCoord_moebiusReal N he]; ring

/-- **Bounded multipliers are null.** For every bounded weight `w`,
`Σ_{e ≤ N} w(e) Y_N(e)² → 0` for the Möbius coordinates. -/
theorem tendsto_sum_bounded_mul_moebiusCoord_sq {w : ℕ → ℝ} {B : ℝ} (hw : ∀ e, |w e| ≤ B) :
    Tendsto (fun N : ℕ => ∑ e ∈ Icc 1 N, w e * selbergMultiplesCoord N moebiusReal e ^ 2)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hτ⟩ := RHTower.card_divisors_le_const_mul_rpow (show (0 : ℝ) < 1 / 4 by norm_num)
  set F : ℕ → ℕ → ℝ := fun N f =>
    w f * (moebiusReal f ^ 2 / (f : ℝ) ^ 2 * coprimeHarmonicMoebius f (N / f) ^ 2)
  have hfin (N : ℕ) :
      ∑ e ∈ Icc 1 N, w e * selbergMultiplesCoord N moebiusReal e ^ 2 = ∑' f, F N f := by
    simp_rw [selbergMultiplesCoord_moebiusReal_sq]
    rw [tsum_eq_sum (s := Icc 1 N)]
    intro f hf
    rcases Nat.eq_zero_or_pos f with rfl | hf0
    · simp [F, moebiusReal]
    · have hNf : N < f := by simp only [mem_Icc, not_and, not_le] at hf; exact hf hf0
      simp [F, Nat.div_eq_of_lt hNf, coprimeHarmonicMoebius]
  simp_rw [hfin]
  rw [← tsum_zero]
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun f => B * C ^ 2 * (f : ℝ) ^ (-(3 / 2 : ℝ))) ?_ ?_ ?_
  · exact (Real.summable_nat_rpow.mpr (by norm_num)).mul_left _
  · intro f
    by_cases hsq : Squarefree f
    · have hm := tendsto_coprimeHarmonicMoebius_prod f.primeFactors
        (fun p hp => Nat.prime_of_mem_primeFactors hp)
      rw [Nat.prod_primeFactors_of_squarefree hsq] at hm
      have hm' := ((hm.comp (Nat.tendsto_div_const_atTop hsq.ne_zero)).pow 2).const_mul
        (w f * (moebiusReal f ^ 2 / (f : ℝ) ^ 2))
      simpa [F, mul_assoc] using hm'
    · have : ∀ N, F N f = 0 := fun N => by
        simp [F, moebiusReal_eq_zero_of_not_squarefree _ hsq]
      simp [this]
  · filter_upwards with N f
    rcases Nat.eq_zero_or_pos f with rfl | hf0
    · simp only [F, Nat.cast_zero]
      simp [moebiusReal]
    have hfR : (0 : ℝ) < f := by exact_mod_cast hf0
    have hw0 : 0 ≤ B := (abs_nonneg _).trans (hw 0)
    have hgen : |coprimeHarmonicMoebius f (N / f)| * |moebiusReal f| ≤ C * (f : ℝ) ^ (1 / 4 : ℝ) := by
      by_cases hsq : Squarefree f
      · have hμ : |moebiusReal f| ≤ 1 := by
          unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        calc |coprimeHarmonicMoebius f (N / f)| * |moebiusReal f|
            ≤ (f.divisors.card : ℝ) * 1 :=
              mul_le_mul (abs_coprimeHarmonicMoebius_le_card_divisors hsq _) hμ (abs_nonneg _)
                (Nat.cast_nonneg _)
          _ ≤ C * (f : ℝ) ^ (1 / 4 : ℝ) := by rw [mul_one]; exact hτ f hf0
      · rw [moebiusReal_eq_zero_of_not_squarefree _ hsq, abs_zero, mul_zero]; positivity
    have hpow : (C * (f : ℝ) ^ (1 / 4 : ℝ)) ^ 2 / (f : ℝ) ^ 2 = C ^ 2 * (f : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [mul_pow, ← Real.rpow_natCast ((f : ℝ) ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hfR.le,
        ← Real.rpow_natCast (f : ℝ) 2, mul_div_assoc, ← Real.rpow_sub hfR]
      norm_num
    have hsq2 : moebiusReal f ^ 2 * coprimeHarmonicMoebius f (N / f) ^ 2 ≤
        (C * (f : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hgen 2
      rwa [mul_pow, sq_abs, sq_abs, mul_comm] at this
    rw [Real.norm_eq_abs]
    calc |F N f| = |w f| * (moebiusReal f ^ 2 * coprimeHarmonicMoebius f (N / f) ^ 2 /
          (f : ℝ) ^ 2) := by
          simp only [F]
          rw [abs_mul, abs_of_nonneg (by positivity :
            (0 : ℝ) ≤ moebiusReal f ^ 2 / (f : ℝ) ^ 2 * coprimeHarmonicMoebius f (N / f) ^ 2)]
          ring
      _ ≤ B * ((C * (f : ℝ) ^ (1 / 4 : ℝ)) ^ 2 / (f : ℝ) ^ 2) :=
          mul_le_mul (hw f) (div_le_div_of_nonneg_right hsq2 (by positivity)) (by positivity) hw0
      _ = B * C ^ 2 * (f : ℝ) ^ (-(3 / 2 : ℝ)) := by rw [hpow]; ring

/-! ### Every nonzero lag decorrelates -/

/-- Ramanujan lag weights at a fixed lag `h ≥ 1` are bounded by `σ(h)`. -/
theorem abs_ramanujanLagWeight_le_sigma {h : ℕ} (hh : 1 ≤ h) (e : ℕ) :
    |ramanujanLagWeight h e| ≤ ∑ d ∈ h.divisors, (d : ℝ) := by
  rw [ramanujanLagWeight_eq_sum_divisors]
  calc |∑ d ∈ e.divisors, (if d ∣ h then (d : ℝ) else 0) * (μ (e / d) : ℝ)|
      ≤ ∑ d ∈ e.divisors, |(if d ∣ h then (d : ℝ) else 0) * (μ (e / d) : ℝ)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ e.divisors.filter (· ∣ h), (d : ℝ) := by
        rw [sum_filter]
        refine sum_le_sum fun d _ => ?_
        split_ifs
        · rw [abs_mul, Nat.abs_cast]
          have : |(μ (e / d) : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          nlinarith [Nat.cast_nonneg (α := ℝ) d]
        · simp
    _ ≤ ∑ d ∈ h.divisors, (d : ℝ) := by
        refine sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) fun _ _ _ => Nat.cast_nonneg _
        exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2, by omega⟩

/-- **Lag decorrelation.** At every lag `h ≥ 1` the complete-period covariance of the Möbius
response tends to zero. -/
theorem tendsto_periodCovariance_moebius {h : ℕ} (hh : 1 ≤ h) :
    Tendsto (fun N : ℕ => TwoLagSieve.periodCovariance N moebiusReal h) atTop (𝓝 0) := by
  set w : ℕ → ℝ := fun e => if 2 ≤ e then ramanujanLagWeight h e else 0
  have hw : ∀ e, |w e| ≤ ∑ d ∈ h.divisors, (d : ℝ) := fun e => by
    simp only [w]; split_ifs
    · exact abs_ramanujanLagWeight_le_sigma hh e
    · rw [abs_zero]; positivity
  refine (tendsto_sum_bounded_mul_moebiusCoord_sq hw).congr fun N => ?_
  rw [periodCovariance_eq_ramanujanLagWeight_diagonal]
  have hI : Icc 2 N = (Icc 1 N).filter (2 ≤ ·) := by
    ext e; simp only [mem_Icc, mem_filter]; omega
  rw [hI, sum_filter]
  exact sum_congr rfl fun e _ => by simp only [w]; split_ifs <;> simp

/-! ### The variance floor -/

/-- `Σ_{e ≤ X} e/φ(e) ≤ 4X`, from `e/φ(e) = Σ_{d | e} μ²(d)/φ(d)`. -/
theorem sum_totientRatio_le (X : ℕ) :
    ∑ e ∈ Icc 1 X, (e : ℝ) / (Nat.totient e : ℝ) ≤ 4 * X := by
  have hI : Icc 1 X = Ioc 0 X := by ext; simp only [mem_Icc, mem_Ioc]; omega
  have hconv : ∀ e : ℕ, (e : ℝ) / (Nat.totient e : ℝ) =
      (RHTower.Sieve.sqfreeTotientInv * ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
        ArithmeticFunction ℝ)) e := fun e => by
    rw [mul_comm, RHTower.Sieve.zeta_mul_sqfreeTotientInv, RHTower.Sieve.totientRatio_apply]
  simp_rw [hconv]
  rw [hI, ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum, ← hI]
  calc ∑ d ∈ Icc 1 X, RHTower.Sieve.sqfreeTotientInv d * ((X / d : ℕ) : ℝ)
      ≤ ∑ d ∈ Icc 1 X, RHTower.Sieve.sqfreeTotientInv d * ((X : ℝ) / d) :=
        sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (Nat.cast_div_le)
          (RHTower.Sieve.sqfreeTotientInv_nonneg d)
    _ = X * ∑ d ∈ Icc 1 X, RHTower.Sieve.sqfreeTotientInv d / d := by
        rw [mul_sum]; exact sum_congr rfl fun d _ => by ring
    _ ≤ X * 4 := mul_le_mul_of_nonneg_left (RHTower.Sieve.sum_sqfreeTotientInv_div_le X)
        (Nat.cast_nonneg X)
    _ = 4 * X := by ring

/-- On the top octave the Möbius coordinate is `μ(e)/e`: `m_e(1) = 1`. -/
private theorem coprimeHarmonicMoebius_one (e : ℕ) : coprimeHarmonicMoebius e 1 = 1 := by
  simp [coprimeHarmonicMoebius, moebiusReal]

/-- The variance dominates `Σ φ(e)/e²` over the odd squarefree window `(M, 2M]`, `M = ⌊N/2⌋`. -/
theorem sum_window_le_periodCovariance_zero (N : ℕ) :
    ∑ e ∈ oddSquarefreeWindow (N / 2), (Nat.totient e : ℝ) / (e : ℝ) ^ 2 ≤
      TwoLagSieve.periodCovariance N moebiusReal 0 := by
  rw [periodCovariance_eq_ramanujanLagWeight_diagonal]
  have hsub : oddSquarefreeWindow (N / 2) ⊆ Icc 2 N := fun e he => by
    simp only [oddSquarefreeWindow, mem_filter, mem_Ioc] at he
    simp only [mem_Icc]; omega
  calc ∑ e ∈ oddSquarefreeWindow (N / 2), (Nat.totient e : ℝ) / (e : ℝ) ^ 2
      = ∑ e ∈ oddSquarefreeWindow (N / 2),
          ramanujanLagWeight 0 e * selbergMultiplesCoord N moebiusReal e ^ 2 := by
        refine sum_congr rfl fun e he => ?_
        simp only [oddSquarefreeWindow, mem_filter, mem_Ioc] at he
        obtain ⟨⟨h1, h2⟩, -, hsq⟩ := he
        have he0 : 0 < e := by omega
        have hNe : N / e = 1 := by
          have h1 : N / e < 2 := (Nat.div_lt_iff_lt_mul he0).mpr (by omega)
          have h2 : 1 ≤ N / e := (Nat.le_div_iff_mul_le he0).mpr (by omega)
          omega
        have hμ : moebiusReal e ^ 2 = 1 := by
          unfold moebiusReal
          have h1 : |(μ e : ℝ)| = 1 := by exact_mod_cast abs_moebius_eq_one_of_squarefree hsq
          rw [← sq_abs, h1]; norm_num
        rw [ramanujanLagWeight_zero_left, selbergMultiplesCoord_moebiusReal_sq, hNe,
          coprimeHarmonicMoebius_one, hμ]
        ring
    _ ≤ ∑ e ∈ Icc 2 N, ramanujanLagWeight 0 e * selbergMultiplesCoord N moebiusReal e ^ 2 := by
        refine sum_le_sum_of_subset_of_nonneg hsub fun e _ _ => ?_
        rw [ramanujanLagWeight_zero_left]; positivity

/-- Cauchy–Schwarz on the window: `(Σ 1/e)² ≤ 8 Σ φ(e)/e²`. -/
theorem sq_sum_inv_window_le (M : ℕ) :
    (∑ e ∈ oddSquarefreeWindow M, (1 : ℝ) / e) ^ 2 ≤
      8 * ∑ e ∈ oddSquarefreeWindow M, (Nat.totient e : ℝ) / (e : ℝ) ^ 2 := by
  set W := oddSquarefreeWindow M
  have hmem : ∀ e ∈ W, M < e ∧ e ≤ 2 * M := fun e he => by
    simp only [W, oddSquarefreeWindow, mem_filter, mem_Ioc] at he; omega
  have hφpos : ∀ e ∈ W, (0 : ℝ) < Nat.totient e := fun e he => by
    exact_mod_cast Nat.totient_pos.mpr (by have := hmem e he; omega)
  have hg : ∀ e ∈ W, (0 : ℝ) < 1 / (Nat.totient e : ℝ) := fun e he => by
    have := hφpos e he; positivity
  -- the reciprocal totient mass of the window is at most `8`
  have hφsum : ∑ e ∈ W, 1 / (Nat.totient e : ℝ) ≤ 8 := by
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · have : W = ∅ := by
        ext e; simp only [W, oddSquarefreeWindow, mem_filter, mem_Ioc]; simp; omega
      simp [this]
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    have hWsub : W ⊆ Icc 1 (2 * M) := fun e he => by
      have := hmem e he; simp only [mem_Icc]; omega
    calc ∑ e ∈ W, 1 / (Nat.totient e : ℝ)
        ≤ ∑ e ∈ W, ((e : ℝ) / (Nat.totient e : ℝ)) / M := by
          refine sum_le_sum fun e he => ?_
          have hme := hmem e he
          have hφ := hφpos e he
          rw [div_div, div_le_div_iff₀ hφ (by positivity), one_mul]
          have : (M : ℝ) ≤ e := by exact_mod_cast hme.1.le
          nlinarith
      _ ≤ ∑ e ∈ Icc 1 (2 * M), ((e : ℝ) / (Nat.totient e : ℝ)) / M :=
          sum_le_sum_of_subset_of_nonneg hWsub fun _ _ _ => by positivity
      _ = (∑ e ∈ Icc 1 (2 * M), (e : ℝ) / (Nat.totient e : ℝ)) / M := by rw [sum_div]
      _ ≤ (4 * ((2 * M : ℕ) : ℝ)) / M :=
          div_le_div_of_nonneg_right (sum_totientRatio_le (2 * M)) hMR.le
      _ = 8 := by push_cast; field_simp; ring
  have hcs := sq_sum_div_le_sum_sq_div W (fun e => (1 : ℝ) / e) hg
  have hrhs : ∑ e ∈ W, ((1 : ℝ) / e) ^ 2 / (1 / (Nat.totient e : ℝ)) =
      ∑ e ∈ W, (Nat.totient e : ℝ) / (e : ℝ) ^ 2 :=
    sum_congr rfl fun e _ => by field_simp
  rw [hrhs] at hcs
  rcases (sum_nonneg fun e he => (hg e he).le).eq_or_lt with h0 | hpos
  · have hW : W = ∅ := by
      by_contra hne
      obtain ⟨e, he⟩ := nonempty_iff_ne_empty.mpr hne
      have := (sum_pos (fun e he => hg e he) ⟨e, he⟩)
      linarith
    simp [hW]
  · rw [div_le_iff₀ hpos] at hcs
    have hR : 0 ≤ ∑ e ∈ W, (Nat.totient e : ℝ) / (e : ℝ) ^ 2 :=
      sum_nonneg fun _ _ => by positivity
    nlinarith

/-- **Variance floor.** At all large horizons the complete-period variance of the Möbius response
is at least `1/288`. -/
theorem eventually_periodCovariance_moebius_zero_ge :
    ∀ᶠ N : ℕ in atTop, (1 : ℝ) / 288 ≤ TwoLagSieve.periodCovariance N moebiusReal 0 := by
  have hD : (1 : ℝ) / 3 < RHTower.Sieve.squarefreeDensity * 2 / 3 := by
    rw [RHTower.Sieve.squarefreeDensity_eq]
    have hpi : Real.pi ^ 2 < 12 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have h6 : (1 : ℝ) / 2 < 6 / Real.pi ^ 2 := by
      rw [lt_div_iff₀ (by positivity)]; linarith
    linarith
  have hcount := (tendsto_oddSquarefreeWindow_card_div.eventually (eventually_gt_nhds hD)).and
    (eventually_gt_atTop 0)
  filter_upwards [(Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0)).eventually hcount]
    with N ⟨hW, hM⟩
  set M := N / 2
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hWc : (M : ℝ) / 3 ≤ (oddSquarefreeWindow M).card := by
    rw [lt_div_iff₀ hMR] at hW; linarith
  have hinv : (1 : ℝ) / 6 ≤ ∑ e ∈ oddSquarefreeWindow M, (1 : ℝ) / e := by
    calc (1 : ℝ) / 6 ≤ (oddSquarefreeWindow M).card * (1 / (2 * M)) := by
          rw [mul_one_div, le_div_iff₀ (by positivity)]; linarith
      _ = ∑ e ∈ oddSquarefreeWindow M, (1 : ℝ) / (2 * M) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ e ∈ oddSquarefreeWindow M, (1 : ℝ) / e := by
          refine sum_le_sum fun e he => ?_
          simp only [oddSquarefreeWindow, mem_filter, mem_Ioc] at he
          have h1 : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
          have h2 : (e : ℝ) ≤ 2 * M := by exact_mod_cast he.1.2
          exact one_div_le_one_div_of_le h1 h2
  have hcs := sq_sum_inv_window_le M
  have hwin := sum_window_le_periodCovariance_zero N
  nlinarith

/-! ### White noise and the dissipation floor -/

/-- **White-noise law.** At every lag `h ≥ 1` the normalized period correlation of the Möbius
response, `Cov_N(h)/Cov_N(0)`, tends to zero. -/
theorem tendsto_periodCorrelation_moebius {h : ℕ} (hh : 1 ≤ h) :
    Tendsto (fun N : ℕ => TwoLagSieve.periodCovariance N moebiusReal h /
      TwoLagSieve.periodCovariance N moebiusReal 0) atTop (𝓝 0) := by
  have h0 := (tendsto_periodCovariance_moebius hh).abs.const_mul 288
  rw [abs_zero, mul_zero] at h0
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_periodCovariance_moebius_zero_ge] with N hN
  have hpos : 0 < TwoLagSieve.periodCovariance N moebiusReal 0 := by linarith
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have := abs_nonneg (TwoLagSieve.periodCovariance N moebiusReal h)
  nlinarith

/-- **Every translation dissipates twice the variance.** At every lag `h ≥ 1` the period
mean-square translation difference of the Möbius response, divided by twice the variance,
tends to one. -/
theorem tendsto_periodShiftDifferenceEnergy_div_variance_moebius {h : ℕ} (hh : 1 ≤ h) :
    Tendsto (fun N : ℕ => periodShiftDifferenceEnergy N moebiusReal h /
      (2 * TwoLagSieve.periodCovariance N moebiusReal 0)) atTop (𝓝 1) := by
  have h1 := (tendsto_periodCorrelation_moebius hh).const_sub 1
  rw [sub_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_periodCovariance_moebius_zero_ge] with N hN
  have hpos : 0 < TwoLagSieve.periodCovariance N moebiusReal 0 := by linarith
  rw [periodShiftDifferenceEnergy_eq_two_sub_periodCovariance]
  field_simp

/-- **Dissipation floor.** At all large horizons the dissipation rate of the Möbius defect is at
least `1/576`: by the period law the renormalized defect drops by at least `L/576` over every
complete period `L`. -/
theorem eventually_sieveSuccessorReserve_moebius_ge :
    ∀ᶠ N : ℕ in atTop, (1 : ℝ) / 576 ≤ sieveSuccessorReserve N moebiusReal := by
  filter_upwards [eventually_periodCovariance_moebius_zero_ge,
    tendsto_bezoutCoprimeQuadraticForm_moebius.eventually
      (eventually_le_nhds (show (0 : ℝ) < 1 / 576 by norm_num))] with N hvar hbez
  have hsel : TwoLagSieve.periodCovariance N moebiusReal 0 ≤
      selbergTotientDiagonalForm N moebiusReal := by
    rw [periodCovariance_eq_ramanujanLagWeight_diagonal, selbergTotientDiagonalForm]
    simp_rw [ramanujanLagWeight_zero_left]
    exact sum_le_sum_of_subset_of_nonneg (fun e he => by simp only [mem_Icc] at he ⊢; omega)
      fun e _ _ => by positivity
  unfold sieveSuccessorReserve
  linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
