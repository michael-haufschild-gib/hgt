import GaloisForLFunctions.BezoutValuationIncidence.PolynomialWindowTranslatedMomentTransfer
import GaloisForLFunctions.BiScaleUncertainty.UniversalRamanujanCovarianceAndBiScaleRigidity
import GaloisForLFunctions.BiScaleUncertainty.SieveHighestModeStability

/-!
# Polynomial-horizon recovery from windows at arbitrary phase

**Two-point spectrum from `N` lags.** The complete-period lag covariance is
`Cov(g) = Σ_{2 ≤ e ≤ N} c_e(g) Y(e)²` with the Ramanujan sum `c_e(g) = Σ_{d ∣ (e,g)} d μ(e/d)`.
Möbius inversion in the lag variable gives `Σ_{ab = f} μ(a) c_e(b) = f μ(e/f) [f ∣ e]`, and a second
inversion over multiples recovers every Selberg energy from the lags `1, …, N` alone:

`Y(q)² = Σ_{u ≤ N/q} (qu)⁻¹ Σ_{ab = qu} μ(a) Cov(b)`, `2 ≤ q ≤ N`.

The inversion is stable with constant `H_N² ≤ (1 + log N)²`.

**From windows.** The window transfer law gives every lag covariance from one window of length
`K` at arbitrary phase with error `S_N V / K`, so all Selberg energies are recovered within
`H_N² S_N V / K`. Likewise the fifth and sixth window moments of two rows, read on windows at
arbitrary and unrelated phases, feed the complete-period top-anchor stability theorem: the rows
agree up to a translation once the windows are longer than an explicit polynomial in their
`ℓ¹` norms. Complete-period observation is thus replaced by polynomial-horizon observation at
unknown phase. The constants of the complete-period theorems are unchanged; this gives no
constants independent of `N` for those theorems themselves.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ## §1. Möbius inversion of the Ramanujan lag weight in the lag variable -/

/-- `Σ_{ab = f} μ(a) [d ∣ b] = [d = f]`: Möbius inversion of the divisor indicator of `d`. -/
private theorem sum_moebius_dvd_indicator {f d : ℕ} (hf : 0 < f) :
    (∑ x ∈ f.divisorsAntidiagonal, (μ x.1 : ℝ) * (if d ∣ x.2 then 1 else 0)) =
      if f = d then 1 else 0 := by
  have hinv := (sum_eq_iff_sum_smul_moebius_eq (R := ℝ) (f := fun n => if n = d then 1 else 0)
    (g := fun n => if d ∣ n then 1 else 0)).mp (fun n hn => by
      rw [sum_ite_eq']
      simp [Nat.mem_divisors, hn.ne'])
  have h := hinv f hf
  simp only [zsmul_eq_mul] at h
  exact h

/-- **Lag inversion of the Ramanujan weight.** `Σ_{ab = f} μ(a) c_e(b) = f μ(e/f)` if `f ∣ e`, and
`0` otherwise. -/
theorem sum_moebius_ramanujanLagWeight {f e : ℕ} (hf : 0 < f) (he : 0 < e) :
    (∑ x ∈ f.divisorsAntidiagonal, (μ x.1 : ℝ) * ramanujanLagWeight x.2 e) =
      if f ∣ e then (f : ℝ) * (μ (e / f) : ℝ) else 0 := by
  simp_rw [ramanujanLagWeight_eq_sum_divisors, mul_sum]
  rw [sum_comm]
  have hterm : ∀ d ∈ e.divisors,
      (∑ x ∈ f.divisorsAntidiagonal,
        (μ x.1 : ℝ) * ((if d ∣ x.2 then (d : ℝ) else 0) * (μ (e / d) : ℝ))) =
      (d : ℝ) * (μ (e / d) : ℝ) * (if f = d then 1 else 0) := by
    intro d hd
    rw [← sum_moebius_dvd_indicator hf, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  rw [sum_congr rfl hterm]
  simp only [mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq]
  simp only [Nat.mem_divisors, he.ne', ne_eq, not_false_eq_true, and_true]

/-! ## §2. Recovery of the two-point spectrum from the lags `1, …, N` -/

/-- The lag-inversion readout of the Selberg energy at mode `q` from lag data `C`. -/
def lagSpectrumReadout (N q : ℕ) (C : ℕ → ℝ) : ℝ :=
  ∑ u ∈ Icc 1 (N / q), (1 / ((q * u : ℕ) : ℝ)) *
    ∑ x ∈ (q * u).divisorsAntidiagonal, (μ x.1 : ℝ) * C x.2

private theorem sum_moebius_divisorsAntidiagonal_snd (n : ℕ) :
    (∑ x ∈ n.divisorsAntidiagonal, (μ x.2 : ℝ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => (f n : ℝ)) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply, one_apply] at h
  rw [Nat.sum_divisorsAntidiagonal' (fun _ b => (μ b : ℝ))]
  push_cast at h
  rw [h]

private theorem sum_filter_dvd_reindex' (p N : ℕ) (hp : 0 < p) (f : ℕ → ℝ) :
    ∑ n ∈ (Icc 1 N).filter (fun n => p ∣ n), f n = ∑ m ∈ Icc 1 (N / p), f (p * m) := by
  refine (sum_nbij' (i := fun m => p * m) (j := fun n => n / p) ?_ ?_ ?_ ?_ ?_).symm
  · intro m hm
    rw [mem_Icc] at hm
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, ⟨m, rfl⟩⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    · exact (Nat.le_div_iff_mul_le hp).mp hm.2 |>.trans_eq' (Nat.mul_comm _ _)
  · intro n hn
    obtain ⟨hn, ⟨m, rfl⟩⟩ := mem_filter.mp hn
    rw [mem_Icc] at hn ⊢
    rw [Nat.mul_div_cancel_left m hp]
    refine ⟨Nat.pos_of_ne_zero fun h => by simp [h] at hn, ?_⟩
    exact (Nat.le_div_iff_mul_le hp).mpr (by rw [Nat.mul_comm]; exact hn.2)
  · intro m _
    exact Nat.mul_div_cancel_left m hp
  · intro n hn
    obtain ⟨_, ⟨m, rfl⟩⟩ := mem_filter.mp hn
    rw [Nat.mul_div_cancel_left m hp]
  · intro m _
    rfl

/-- Möbius-weighted lag sums of complete-period covariances isolate the multiples of `f`. -/
private theorem sum_moebius_periodCovariance (N : ℕ) (c : ℕ → ℝ) {f : ℕ} (hf : 0 < f) :
    (∑ x ∈ f.divisorsAntidiagonal, (μ x.1 : ℝ) * TwoLagSieve.periodCovariance N c x.2) =
      ∑ e ∈ Icc 2 N, (if f ∣ e then (f : ℝ) * (μ (e / f) : ℝ) else 0) *
        selbergMultiplesCoord N c e ^ 2 := by
  simp_rw [periodCovariance_eq_ramanujanLagWeight_diagonal, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun e he => ?_
  rw [← sum_moebius_ramanujanLagWeight hf (by have := (mem_Icc.mp he).1; omega), sum_mul]
  exact sum_congr rfl fun x _ => by ring

/-- **Two-point spectrum from `N` lags.** Every Selberg energy `Y(q)²`, `2 ≤ q ≤ N`, is the lag
readout of the complete-period covariances at lags `1, …, N`. -/
theorem lagSpectrumReadout_periodCovariance {N q : ℕ} (hq : q ∈ Icc 2 N) (c : ℕ → ℝ) :
    lagSpectrumReadout N q (TwoLagSieve.periodCovariance N c) =
      selbergMultiplesCoord N c q ^ 2 := by
  obtain ⟨hq2, hqN⟩ := mem_Icc.mp hq
  unfold lagSpectrumReadout
  have hinner : ∀ u ∈ Icc 1 (N / q),
      (1 / ((q * u : ℕ) : ℝ)) * ∑ x ∈ (q * u).divisorsAntidiagonal,
        (μ x.1 : ℝ) * TwoLagSieve.periodCovariance N c x.2 =
      ∑ w ∈ Icc 1 (N / q / u), (μ w : ℝ) * selbergMultiplesCoord N c (q * (u * w)) ^ 2 := by
    intro u hu
    have hu1 := (mem_Icc.mp hu).1
    have hf : 0 < q * u := Nat.mul_pos (by omega) hu1
    rw [sum_moebius_periodCovariance N c hf, mul_sum]
    have hqu0 : ((q * u : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
    have hfilter : (∑ e ∈ Icc 2 N, 1 / ((q * u : ℕ) : ℝ) *
        ((if q * u ∣ e then ((q * u : ℕ) : ℝ) * (μ (e / (q * u)) : ℝ) else 0) *
          selbergMultiplesCoord N c e ^ 2)) =
        ∑ e ∈ (Icc 1 N).filter (fun e => q * u ∣ e),
          (μ (e / (q * u)) : ℝ) * selbergMultiplesCoord N c e ^ 2 := by
      rw [sum_filter]
      have hI : Icc 1 N = insert 1 (Icc 2 N) := by
        ext x
        simp only [mem_insert, mem_Icc]
        omega
      rw [hI, sum_insert (by simp)]
      have h1 : ¬ q * u ∣ 1 := fun h => by
        have := Nat.le_of_dvd one_pos h
        nlinarith
      rw [if_neg h1, zero_add]
      refine sum_congr rfl fun e _ => ?_
      split_ifs
      · field_simp
      · simp
    rw [hfilter, sum_filter_dvd_reindex' (q * u) N hf, Nat.div_div_eq_div_mul]
    refine sum_congr rfl fun w _ => ?_
    rw [Nat.mul_div_cancel_left w hf, Nat.mul_assoc]
  rw [sum_congr rfl hinner]
  rw [← sum_Icc_divisorsAntidiagonal_swap
    (fun a b => (μ b : ℝ) * selbergMultiplesCoord N c (q * (a * b)) ^ 2) (N / q)]
  have hcol2 : ∀ n ∈ Icc 1 (N / q),
      (∑ x ∈ n.divisorsAntidiagonal, (μ x.2 : ℝ) * selbergMultiplesCoord N c (q * (x.1 * x.2)) ^ 2)
        = (if n = 1 then 1 else 0) * selbergMultiplesCoord N c (q * n) ^ 2 := by
    intro n _
    rw [← sum_moebius_divisorsAntidiagonal_snd n, sum_mul]
    exact sum_congr rfl fun x hx => by rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
  rw [sum_congr rfl hcol2]
  have h1 : 1 ∈ Icc 1 (N / q) := mem_Icc.mpr ⟨le_rfl, (Nat.le_div_iff_mul_le (by omega)).mpr
    (by simpa using hqN)⟩
  rw [sum_eq_single_of_mem 1 h1 fun n _ hn => by simp [hn]]
  simp

/-- Divisor-weighted harmonic bound `Σ_{f ≤ N} d(f)/f ≤ H_N²`. -/
private theorem sum_card_divisors_div_le (N : ℕ) :
    (∑ f ∈ Icc 1 N, ((f.divisorsAntidiagonal.card : ℕ) : ℝ) / f) ≤ (harmonic N : ℝ) ^ 2 := by
  have hrw : ∀ f ∈ Icc 1 N, ((f.divisorsAntidiagonal.card : ℕ) : ℝ) / f =
      ∑ x ∈ f.divisorsAntidiagonal, (1 / (x.1 : ℝ)) * (1 / (x.2 : ℝ)) := by
    intro f _
    rw [card_eq_sum_ones, Nat.cast_sum, sum_div]
    refine sum_congr rfl fun x hx => ?_
    rw [← (Nat.mem_divisorsAntidiagonal.mp hx).1]
    push_cast
    rw [one_div_mul_one_div]
  rw [sum_congr rfl hrw, sum_Icc_divisorsAntidiagonal_swap
    (fun a b => (1 / (a : ℝ)) * (1 / (b : ℝ))) N]
  have hH : (harmonic N : ℝ) = ∑ i ∈ Icc 1 N, (1 : ℝ) / i := by
    rw [_root_.harmonic_eq_sum_Icc]
    push_cast
    exact sum_congr rfl fun i _ => (one_div _).symm
  rw [sq, hH, sum_mul]
  refine sum_le_sum fun a ha => ?_
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.div_le_self N a))
    fun i _ _ => by positivity

/-- **Stability of the lag readout.** Lag data within `η` of the true covariances on `[1, N]` give
every Selberg energy within `H_N² η`. -/
theorem abs_lagSpectrumReadout_sub_le {N q : ℕ} (hq : q ∈ Icc 2 N) (c : ℕ → ℝ) (C : ℕ → ℝ)
    {η : ℝ} (hη : ∀ g ∈ Icc 1 N, |C g - TwoLagSieve.periodCovariance N c g| ≤ η) :
    |lagSpectrumReadout N q C - selbergMultiplesCoord N c q ^ 2| ≤ (harmonic N : ℝ) ^ 2 * η := by
  obtain ⟨hq2, hqN⟩ := mem_Icc.mp hq
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη 1 (mem_Icc.mpr ⟨le_rfl, by omega⟩))
  rw [← lagSpectrumReadout_periodCovariance hq c]
  unfold lagSpectrumReadout
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hpt : ∀ u ∈ Icc 1 (N / q),
      |(1 / ((q * u : ℕ) : ℝ)) * ∑ x ∈ (q * u).divisorsAntidiagonal, (μ x.1 : ℝ) * C x.2 -
        (1 / ((q * u : ℕ) : ℝ)) * ∑ x ∈ (q * u).divisorsAntidiagonal,
          (μ x.1 : ℝ) * TwoLagSieve.periodCovariance N c x.2| ≤
        η * (((q * u).divisorsAntidiagonal.card : ℕ) : ℝ) / (q * u : ℕ) := by
    intro u hu
    have hu1 := (mem_Icc.mp hu).1
    have hquN : q * u ≤ N := by
      have := (Nat.le_div_iff_mul_le (by omega)).mp (mem_Icc.mp hu).2
      linarith [Nat.mul_comm u q]
    have hpos : (0 : ℝ) < (q * u : ℕ) := by exact_mod_cast Nat.mul_pos (by omega) hu1
    rw [← mul_sub, ← sum_sub_distrib, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / _)]
    rw [mul_comm, ← div_eq_mul_one_div]
    refine div_le_div_of_nonneg_right ?_ hpos.le
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [card_eq_sum_ones, Nat.cast_sum, mul_sum]
    refine sum_le_sum fun x hx => ?_
    have hx := Nat.mem_divisorsAntidiagonal.mp hx
    have hx2 : x.2 ∈ Icc 1 N := by
      refine mem_Icc.mpr ⟨Nat.pos_of_ne_zero fun h => ?_, ?_⟩
      · rw [h, mul_zero] at hx
        exact hx.2 hx.1.symm
      · exact (Nat.le_of_dvd (by omega) ⟨x.1, by rw [← hx.1]; ring⟩).trans hquN
    rw [← mul_sub, abs_mul]
    have hμ : |(μ x.1 : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    push_cast
    nlinarith [hη x.2 hx2, abs_nonneg (C x.2 - TwoLagSieve.periodCovariance N c x.2)]
  refine (sum_le_sum hpt).trans ?_
  have hsub : (∑ u ∈ Icc 1 (N / q), η * (((q * u).divisorsAntidiagonal.card : ℕ) : ℝ) /
      (q * u : ℕ)) ≤ η * ∑ f ∈ Icc 1 N, ((f.divisorsAntidiagonal.card : ℕ) : ℝ) / f := by
    rw [mul_sum]
    have hmap : (∑ u ∈ Icc 1 (N / q), η * (((q * u).divisorsAntidiagonal.card : ℕ) : ℝ) /
        (q * u : ℕ)) = ∑ f ∈ (Icc 1 N).filter (fun f => q ∣ f),
          η * (((f.divisorsAntidiagonal.card : ℕ) : ℝ) / f) := by
      rw [sum_filter_dvd_reindex' q N (by omega)]
      exact sum_congr rfl fun u _ => by ring
    rw [hmap]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun f _ _ =>
      mul_nonneg hη0 (by positivity)
  calc _ ≤ η * ∑ f ∈ Icc 1 N, ((f.divisorsAntidiagonal.card : ℕ) : ℝ) / f := hsub
    _ ≤ η * (harmonic N : ℝ) ^ 2 := mul_le_mul_of_nonneg_left (sum_card_divisors_div_le N) hη0
    _ = _ := by ring

/-! ## §3. Recovery from one window at arbitrary phase -/

/-- The normalized centered window covariance at lag `g`. -/
def windowLagCovariance (N : ℕ) (c : ℕ → ℝ) (A K g : ℕ) : ℝ :=
  (∑ k ∈ Icc (A + 1) (A + K),
    (sieveSeq N c k - finiteHarmonicSum N c) * (sieveSeq N c (k + g) - finiteHarmonicSum N c)) / K

/-- Every window covariance is within `S_N V / K` of the complete-period covariance. -/
theorem abs_windowLagCovariance_sub_le {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (A g : ℕ) {K : ℕ}
    (hK : 0 < K) :
    |windowLagCovariance N c A K g - TwoLagSieve.periodCovariance N c g| ≤
      sieveWindowObservabilityConstant N * sieveVariance N c / K := by
  have h0 := abs_window_centeredTranslatedMoment_sub_le hN c (finiteHarmonicSum N c) ![0, g] A K
  rw [sub_self, zero_pow two_ne_zero, zero_add] at h0
  have hnn : 0 ≤ sieveWindowObservabilityConstant N * sieveVariance N c :=
    mul_nonneg (sieveWindowObservabilityConstant_nonneg N)
      (sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have h : |(∑ k ∈ Icc (A + 1) (A + K), ∏ i, (sieveSeq N c (k + ![0, g] i) - finiteHarmonicSum N c)) -
      (K : ℝ) * SieveMoments.translatedMoment N (sieveRowShift c (finiteHarmonicSum N c)) ![0, g]| ≤
      sieveWindowObservabilityConstant N * sieveVariance N c :=
    h0.trans_eq (Real.sq_sqrt hnn)
  have hT : SieveMoments.translatedMoment N (sieveRowShift c (finiteHarmonicSum N c)) ![0, g] =
      TwoLagSieve.periodCovariance N c g := by
    rw [translatedMoment_eq_Icc]
    unfold TwoLagSieve.periodCovariance
    congr 1
    have hset : Icc 1 N.factorial = Ioc 0 N.factorial := by
      ext x
      simp only [mem_Icc, mem_Ioc]
      omega
    rw [hset]
    refine sum_congr rfl fun k _ => ?_
    simp [Fin.prod_univ_two, sieveSeq_sieveRowShift hN]
  rw [hT] at h
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    add_zero] at h
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  unfold windowLagCovariance
  rw [show (∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c k - finiteHarmonicSum N c) *
      (sieveSeq N c (k + g) - finiteHarmonicSum N c)) / K - TwoLagSieve.periodCovariance N c g =
      ((∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c k - finiteHarmonicSum N c) *
        (sieveSeq N c (k + g) - finiteHarmonicSum N c)) -
          K * TwoLagSieve.periodCovariance N c g) / K by field_simp]
  rw [abs_div, abs_of_pos hKR]
  exact div_le_div_of_nonneg_right h hKR.le

/-- **Two-point spectrum from one window.** At every phase, the lag readout of the window
covariances recovers each Selberg energy within `H_N² S_N V / K`. -/
theorem abs_lagSpectrumReadout_window_sub_le {N q : ℕ} (hq : q ∈ Icc 2 N) (c : ℕ → ℝ)
    (A : ℕ) {K : ℕ} (hK : 0 < K) :
    |lagSpectrumReadout N q (windowLagCovariance N c A K) - selbergMultiplesCoord N c q ^ 2| ≤
      (harmonic N : ℝ) ^ 2 * (sieveWindowObservabilityConstant N * sieveVariance N c / K) :=
  abs_lagSpectrumReadout_sub_le hq c _ fun g _ =>
    abs_windowLagCovariance_sub_le (by have := mem_Icc.mp hq; omega) c A g hK

/-- **Recovery up to translation from windows at unrelated phases.** If the fifth and sixth
window moments of two rows, read on windows of length `K` at arbitrary phases `A` and `B`, agree
within `K η`, and `η + (‖c‖₁^m + ‖e‖₁^m)/K ≤ δ³` for `m = 5, 6`, then the rows agree up to a
translation within `2 (Σ_{q ≤ N} φ(q)) δ`, provided both carry a unit top-order coordinate. -/
theorem exists_translate_error_of_windows (N : ℕ) (hN : 2 ≤ N) (c e : ℕ → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hc : 1 ≤ |selbergMultiplesCoord N c (SieveMoments.TopAnchor.topOrder N)|)
    (he : 1 ≤ |selbergMultiplesCoord N e (SieveMoments.TopAnchor.topOrder N)|)
    (A B : ℕ) {K : ℕ} (hK : 0 < K) (η : ℝ)
    (hw5 : ∀ v : Fin 5 → ℕ,
      |(∑ k ∈ Icc (A + 1) (A + K), ∏ i, sieveSeq N c (k + v i)) -
        ∑ k ∈ Icc (B + 1) (B + K), ∏ i, sieveSeq N e (k + v i)| ≤ K * η)
    (hw6 : ∀ v : Fin 6 → ℕ,
      |(∑ k ∈ Icc (A + 1) (A + K), ∏ i, sieveSeq N c (k + v i)) -
        ∑ k ∈ Icc (B + 1) (B + K), ∏ i, sieveSeq N e (k + v i)| ≤ K * η)
    (hb5 : η + ((∑ d ∈ Icc 1 N, |c d|) ^ 5 + (∑ d ∈ Icc 1 N, |e d|) ^ 5) / K ≤ δ ^ 3)
    (hb6 : η + ((∑ d ∈ Icc 1 N, |c d|) ^ 6 + (∑ d ∈ Icc 1 N, |e d|) ^ 6) / K ≤ δ ^ 3) :
    ∃ t : ℕ, ∀ n : ℕ, |sieveSeq N e n - sieveSeq N c (n + t)| ≤
      2 * (∑ q ∈ Icc 1 N, (q.totient : ℝ)) * δ := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hlift : ∀ (m : ℕ) (v : Fin m → ℕ),
      |(∑ k ∈ Icc (A + 1) (A + K), ∏ i, sieveSeq N c (k + v i)) -
        ∑ k ∈ Icc (B + 1) (B + K), ∏ i, sieveSeq N e (k + v i)| ≤ K * η →
      |SieveMoments.translatedMoment N c v - SieveMoments.translatedMoment N e v| ≤
        η + ((∑ d ∈ Icc 1 N, |c d|) ^ m + (∑ d ∈ Icc 1 N, |e d|) ^ m) / K := by
    intro m v hv
    have h1 := abs_window_translatedMoment_sub_le N c v A K
    have h2 := abs_window_translatedMoment_sub_le N e v B K
    set Wc := ∑ k ∈ Icc (A + 1) (A + K), ∏ i, sieveSeq N c (k + v i)
    set We := ∑ k ∈ Icc (B + 1) (B + K), ∏ i, sieveSeq N e (k + v i)
    set Tc := SieveMoments.translatedMoment N c v
    set Te := SieveMoments.translatedMoment N e v
    have key : |(K : ℝ) * (Tc - Te)| ≤
        K * η + ((∑ d ∈ Icc 1 N, |c d|) ^ m + (∑ d ∈ Icc 1 N, |e d|) ^ m) := by
      have hsplit : (K : ℝ) * (Tc - Te) = (Wc - We) - (Wc - K * Tc) + (We - K * Te) := by ring
      rw [hsplit]
      calc |(Wc - We) - (Wc - K * Tc) + (We - K * Te)|
          ≤ |(Wc - We) - (Wc - K * Tc)| + |We - K * Te| := abs_add_le _ _
        _ ≤ |Wc - We| + |Wc - K * Tc| + |We - K * Te| := by
          have := abs_sub (Wc - We) (Wc - K * Tc)
          linarith
        _ ≤ _ := by linarith
    rw [abs_mul, abs_of_pos hKR] at key
    rw [add_div' _ _ _ hKR.ne', le_div_iff₀ hKR]
    nlinarith [key]
  exact SieveMoments.TopAnchor.exists_translate_error N hN c e δ hδ hδ1 hc he
    (fun v => (hlift 5 v (hw5 v)).trans hb5) (fun v => (hlift 6 v (hw6 v)).trans hb6)

end

end GaloisForLFunctions.BezoutValuationIncidence
