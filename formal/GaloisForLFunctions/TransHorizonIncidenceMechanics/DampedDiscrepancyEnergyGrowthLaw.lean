import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedPrimitiveEnergyHalfThreshold
import GaloisForLFunctions.HTGeometry.RpowPartialSumBound
import GaloisForLFunctions.RHTower.Sieve.LevinsonGcdFormBound

/-!
# The growth law of the discrepancy energy below one half

The period mean square of the zero-mean primitive (the centered discrepancy) of the damped row has
the Jordan spectrum `12 E_prim = Σ_{2 ≤ q ≤ N} J₂(q) Y_N(q)²`. Below the threshold `ε = 1/2` its size
is pinned to the exponent `1 - 2ε`:

* **upper bound** (`0 < ε < 1/2`): every mode is at most `ζ(1+ε)² q^{-2ε}`, and
  `Σ_{q ≤ N} q^{-2ε} ≤ N^{1-2ε}/(1-2ε)`;
* **lower bound** (`ε ≥ 0`): on the odd squarefree top octave `N/2 < q ≤ N` the coordinate is the single
  term `c_ε(q)/q`, so the mode mass is `J₂(q) q^{-2-2ε} ≥ (φ(q)/q) N^{-2ε}`, and the octave carries
  at least `N^{1-2ε}/3456` of mass at all large horizons.

Hence `E_prim(N; c_ε) ≍ N^{1-2ε}` for `0 < ε < 1/2`: the discrepancy of the damped response grows
like a walk of `N^{1-2ε}` independent unit steps, interpolating between the linear growth of the
Möbius row and the bounded discrepancy above one half. For the Möbius row the coprime harmonic sums
obey `|m_f(x)| ≤ f/φ(f)`, which caps the growth at `N log N`.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- On the top octave `N < 2q`, the Selberg coordinate is the single term `c(q)/q`. -/
theorem selbergMultiplesCoord_of_top_octave {N q : ℕ} (hq : N < 2 * q) (hqN : q ≤ N) (hq0 : 0 < q)
    (c : ℕ → ℝ) : selbergMultiplesCoord N c q = c q / q := by
  unfold selbergMultiplesCoord
  have hset : (Icc 1 N).filter (fun d => q ∣ d) = {q} := by
    ext d
    simp only [mem_filter, mem_Icc, mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨k, rfl⟩⟩
      rcases k with _ | _ | k
      · simp at h1
      · ring
      · nlinarith
    · intro h; rw [h]; exact ⟨⟨hq0, hqN⟩, dvd_refl q⟩
  rw [hset, sum_singleton]

/-! ### The upper bound below one half -/

/-- **Upper growth law.** For `0 < ε < 1/2`, `12 E_prim(N; c_ε) ≤ ζ(1+ε)² N^{1-2ε}/(1-2ε)`. -/
theorem sievePrimitiveEnergy_pmPowerDamped_le_rpow {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (N : ℕ) :
    12 * sievePrimitiveEnergy N (pmPowerDampedRealWeight ε) ≤
      (∑' m : ℕ, (m : ℝ) ^ (-1 - ε)) ^ 2 * ((N : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)) := by
  set Z := ∑' m : ℕ, (m : ℝ) ^ (-1 - ε)
  rw [twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal]
  have hpartial := HTGeometry.sum_rpow_sub_one_le (a := 1 - 2 * ε) (by linarith) (by linarith) N
  have hrewrite : ∑ q ∈ Icc 1 N, (q : ℝ) ^ (-2 * ε) =
      ∑ n ∈ range N, ((n : ℝ) + 1) ^ (1 - 2 * ε - 1) := by
    rw [show Icc 1 N = Ico 1 (N + 1) by ext q; simp only [mem_Icc, mem_Ico]; omega,
      Finset.sum_Ico_eq_sum_range, show N + 1 - 1 = N by omega]
    exact sum_congr rfl fun n _ => by push_cast; ring_nf
  calc ∑ q ∈ Icc 2 N, jordanTotient2 q * selbergMultiplesCoord N (pmPowerDampedRealWeight ε) q ^ 2
      ≤ ∑ q ∈ Icc 1 N, Z ^ 2 * (q : ℝ) ^ (-2 * ε) := by
        refine (sum_le_sum fun q hq => jordan_mode_le hε N (by have := (mem_Icc.mp hq).1; omega)).trans
          (sum_le_sum_of_subset_of_nonneg (fun q hq => by simp only [mem_Icc] at hq ⊢; omega)
            fun q _ _ => mul_nonneg (sq_nonneg Z) (Real.rpow_nonneg (Nat.cast_nonneg q) _))
    _ = Z ^ 2 * ∑ q ∈ Icc 1 N, (q : ℝ) ^ (-2 * ε) := by rw [mul_sum]
    _ ≤ Z ^ 2 * ((N : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)) := by
        rw [hrewrite]; exact mul_le_mul_of_nonneg_left hpartial (sq_nonneg Z)

/-! ### The lower bound from the top octave -/

/-- **Lower growth law.** For every `ε ≥ 0`, at all large horizons,
`⌊N/2⌋ N^{-2ε} ≤ 3456 E_prim(N; c_ε)`. -/
theorem eventually_sievePrimitiveEnergy_pmPowerDamped_ge {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ᶠ N : ℕ in atTop, ((N / 2 : ℕ) : ℝ) * (N : ℝ) ^ (-2 * ε) ≤
      3456 * sievePrimitiveEnergy N (pmPowerDampedRealWeight ε) := by
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
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hNe : (0 : ℝ) < (N : ℝ) ^ (-2 * ε) := Real.rpow_pos_of_pos hNR _
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
  have hφ : (1 : ℝ) / 288 ≤ ∑ e ∈ oddSquarefreeWindow M, (Nat.totient e : ℝ) / (e : ℝ) ^ 2 := by
    nlinarith
  -- on the window each Jordan mode carries at least `M N^{-2ε} φ(e)/e²`
  have hwin : (M : ℝ) * (N : ℝ) ^ (-2 * ε) *
      ∑ e ∈ oddSquarefreeWindow M, (Nat.totient e : ℝ) / (e : ℝ) ^ 2 ≤
      12 * sievePrimitiveEnergy N (pmPowerDampedRealWeight ε) := by
    rw [twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal, mul_sum]
    have hsub : oddSquarefreeWindow M ⊆ Icc 2 N := fun e he => by
      simp only [oddSquarefreeWindow, mem_filter, mem_Ioc] at he
      simp only [mem_Icc]; omega
    refine le_trans (sum_le_sum fun e he => ?_) (sum_le_sum_of_subset_of_nonneg hsub
      fun q _ _ => mul_nonneg (jordanTotient2_nonneg q) (sq_nonneg _))
    simp only [oddSquarefreeWindow, mem_filter, mem_Ioc] at he
    obtain ⟨⟨h1, h2⟩, -, hsq⟩ := he
    have he0 : 0 < e := by omega
    have heR : (0 : ℝ) < e := by exact_mod_cast he0
    have hY : selbergMultiplesCoord N (pmPowerDampedRealWeight ε) e =
        pmPowerDampedRealWeight ε e / e :=
      selbergMultiplesCoord_of_top_octave (by omega) (by omega) he0 _
    have hμ : moebiusReal e ^ 2 = 1 := by
      unfold moebiusReal
      have h1 : |(μ e : ℝ)| = 1 := by exact_mod_cast abs_moebius_eq_one_of_squarefree hsq
      rw [← sq_abs, h1]; norm_num
    have hpow : ((e : ℝ) ^ (-ε)) ^ 2 = (e : ℝ) ^ (-2 * ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul heR.le]; push_cast; ring_nf
    have hY2 : selbergMultiplesCoord N (pmPowerDampedRealWeight ε) e ^ 2 =
        (e : ℝ) ^ (-2 * ε) / (e : ℝ) ^ 2 := by
      rw [hY, pmPowerDampedRealWeight, div_pow, mul_pow, hμ, one_mul, hpow]
    have heN : (e : ℝ) ≤ N := by exact_mod_cast (show e ≤ N by omega)
    have hepow : (N : ℝ) ^ (-2 * ε) ≤ (e : ℝ) ^ (-2 * ε) :=
      Real.rpow_le_rpow_of_nonpos heR heN (by linarith)
    have hJ := jordanTotient2_ge_mul_totient e
    have hMe : (M : ℝ) ≤ e := by exact_mod_cast h1.le
    rw [hY2]
    have hφ0 : (0 : ℝ) ≤ (Nat.totient e : ℝ) / (e : ℝ) ^ 2 := by positivity
    calc (M : ℝ) * (N : ℝ) ^ (-2 * ε) * ((Nat.totient e : ℝ) / (e : ℝ) ^ 2)
        ≤ (e : ℝ) * (e : ℝ) ^ (-2 * ε) * ((Nat.totient e : ℝ) / (e : ℝ) ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ hφ0
          exact mul_le_mul hMe hepow hNe.le heR.le
      _ = (e : ℝ) * (Nat.totient e : ℝ) * ((e : ℝ) ^ (-2 * ε) / (e : ℝ) ^ 2) := by ring
      _ ≤ jordanTotient2 e * ((e : ℝ) ^ (-2 * ε) / (e : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hJ (by positivity)
  have hMN : ((N / 2 : ℕ) : ℝ) = M := rfl
  rw [hMN]
  have hprod : 0 ≤ (M : ℝ) * (N : ℝ) ^ (-2 * ε) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hφ hprod]

/-- **Growth law below one half.** For `0 < ε < 1/2`, `E_prim(N; c_ε) ≍ N^{1-2ε}`: at all large
horizons `N^{1-2ε}/10368 ≤ E_prim(N; c_ε) ≤ ζ(1+ε)² N^{1-2ε}/(12(1-2ε))`. -/
theorem eventually_sievePrimitiveEnergy_pmPowerDamped_growth {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 - 2 * ε) / 10368 ≤ sievePrimitiveEnergy N (pmPowerDampedRealWeight ε) ∧
        sievePrimitiveEnergy N (pmPowerDampedRealWeight ε) ≤
          (∑' m : ℕ, (m : ℝ) ^ (-1 - ε)) ^ 2 * (N : ℝ) ^ (1 - 2 * ε) / (12 * (1 - 2 * ε)) := by
  filter_upwards [eventually_sievePrimitiveEnergy_pmPowerDamped_ge hε.le, eventually_ge_atTop 3]
    with N hlow hN
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  constructor
  · have hhalf : (N : ℝ) / 3 ≤ ((N / 2 : ℕ) : ℝ) := by
      have : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by
        have := Nat.lt_div_mul_add (a := N) (b := 2) (by norm_num)
        have h' : (N : ℝ) < ((N / 2 : ℕ) : ℝ) * 2 + 2 := by exact_mod_cast this
        have h2 : ((N : ℕ) : ℝ) ≤ ((N / 2 : ℕ) : ℝ) * 2 + 1 := by
          have : N ≤ N / 2 * 2 + 1 := by omega
          exact_mod_cast this
        linarith
      linarith
    have hpow : (N : ℝ) ^ (1 - 2 * ε) = (N : ℝ) * (N : ℝ) ^ (-2 * ε) := by
      rw [show 1 - 2 * ε = 1 + -2 * ε by ring, Real.rpow_add hNpos, Real.rpow_one]
    have hNe : 0 < (N : ℝ) ^ (-2 * ε) := Real.rpow_pos_of_pos hNpos _
    rw [hpow]
    nlinarith [mul_le_mul_of_nonneg_right hhalf hNe.le]
  · have h := sievePrimitiveEnergy_pmPowerDamped_le_rpow hε hε2 N
    have h12 : (0 : ℝ) < 1 - 2 * ε := by linarith
    rw [le_div_iff₀ (by positivity)]
    calc sievePrimitiveEnergy N (pmPowerDampedRealWeight ε) * (12 * (1 - 2 * ε))
        = 12 * sievePrimitiveEnergy N (pmPowerDampedRealWeight ε) * (1 - 2 * ε) := by ring
      _ ≤ (∑' m : ℕ, (m : ℝ) ^ (-1 - ε)) ^ 2 * ((N : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)) *
            (1 - 2 * ε) := mul_le_mul_of_nonneg_right h h12.le
      _ = _ := by rw [mul_assoc, div_mul_cancel₀ _ h12.ne']


/-! ### The Möbius row: an `N log N` cap -/

/-- Each prime of a squarefree modulus multiplies the coprime harmonic bound by at most
`p/(p-1)`: `|m_{∏ s}(n)| ≤ ∏_{p ∈ s} p/(p-1)`. -/
theorem abs_coprimeHarmonicMoebius_prod_le_ratio (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (n : ℕ) :
    |coprimeHarmonicMoebius (∏ p ∈ s, p) n| ≤ ∏ p ∈ s, ((p : ℝ) / ((p : ℝ) - 1)) := by
  induction s using Finset.induction generalizing n with
  | empty => simpa using abs_coprimeHarmonicMoebius_one_le n
  | insert p s hps ih =>
    have hp : p.Prime := hs p (mem_insert_self p s)
    have ih' := fun n => ih (fun q hq => hs q (mem_insert_of_mem hq)) n
    rw [prod_insert hps, prod_insert hps]
    set f := ∏ q ∈ s, q
    set A := ∏ q ∈ s, ((q : ℝ) / ((q : ℝ) - 1))
    have hpf : ¬ p ∣ f := by
      intro h
      obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
      have := (Nat.prime_dvd_prime_iff_eq hp (hs q (mem_insert_of_mem hq))).mp hpq
      exact hps (this ▸ hq)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hA : 0 ≤ A := prod_nonneg fun q hq => by
      have : (2 : ℝ) ≤ q := by exact_mod_cast (hs q (mem_insert_of_mem hq)).two_le
      exact div_nonneg (by linarith) (by linarith)
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [coprimeHarmonicMoebius]; positivity
      have hstep := coprimeHarmonicMoebius_prime_step hp hpf n
      rw [mul_comm p f]
      have hrec : coprimeHarmonicMoebius (f * p) n =
          coprimeHarmonicMoebius f n + coprimeHarmonicMoebius (f * p) (n / p) / p := by linarith
      have h1 := ih' n
      have h2 := ihn (n / p) (Nat.div_lt_self hn hp.one_lt)
      rw [mul_comm p f] at h2
      have hp0 : (0 : ℝ) < p := by linarith
      calc |coprimeHarmonicMoebius (f * p) n|
          ≤ |coprimeHarmonicMoebius f n| + |coprimeHarmonicMoebius (f * p) (n / p)| / p := by
            rw [hrec]
            calc _ ≤ |coprimeHarmonicMoebius f n| + |coprimeHarmonicMoebius (f * p) (n / p) / p| :=
                  abs_add_le _ _
              _ = _ := by rw [abs_div, abs_of_pos hp0]
        _ ≤ A + (p / (p - 1) * A) / p := by gcongr
        _ = p / (p - 1) * A := by field_simp; ring

/-- For squarefree `f`, `|m_f(n)| ≤ f/φ(f)`. -/
theorem abs_coprimeHarmonicMoebius_le_ratio {f : ℕ} (hf : Squarefree f) (n : ℕ) :
    |coprimeHarmonicMoebius f n| ≤ (f : ℝ) / (Nat.totient f : ℝ) := by
  have h := abs_coprimeHarmonicMoebius_prod_le_ratio f.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) n
  rw [Nat.prod_primeFactors_of_squarefree hf] at h
  refine h.trans_eq ?_
  have hφ := Nat.totient_mul_prod_primeFactors f
  rw [Nat.prod_primeFactors_of_squarefree hf] at hφ
  have hf0 : 0 < f := Nat.pos_of_ne_zero hf.ne_zero
  have hφ' : Nat.totient f = ∏ p ∈ f.primeFactors, (p - 1) := by
    rw [mul_comm] at hφ; exact Nat.eq_of_mul_eq_mul_left hf0 hφ
  have hfR : (f : ℝ) = ∏ p ∈ f.primeFactors, (p : ℝ) := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hf]
    push_cast; rfl
  have hφR : (Nat.totient f : ℝ) = ∏ p ∈ f.primeFactors, ((p : ℝ) - 1) := by
    rw [hφ', Nat.cast_prod]
    exact prod_congr rfl fun p hp => by
      rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]
  rw [hfR, hφR, prod_div_distrib]

/-- **Möbius cap.** `12 E_prim(N; μ) ≤ 64 N (1 + log N)`: the Möbius discrepancy energy lies between
linear and `N log N` growth. -/
theorem sievePrimitiveEnergy_moebius_le (N : ℕ) :
    12 * sievePrimitiveEnergy N moebiusReal ≤ 64 * (N : ℝ) * (1 + Real.log N) := by
  rw [twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal]
  have hmode : ∀ q ∈ Icc 2 N, jordanTotient2 q * selbergMultiplesCoord N moebiusReal q ^ 2 ≤
      (N : ℝ) * (((q : ℝ) / (Nat.totient q : ℝ)) ^ 2 / (q : ℝ)) := by
    intro q hq
    obtain ⟨hq2, hqN⟩ := mem_Icc.mp hq
    have hq0 : 0 < q := by omega
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
    rw [selbergMultiplesCoord_moebiusReal_sq]
    by_cases hsq : Squarefree q
    · have hμ : moebiusReal q ^ 2 = 1 := by
        unfold moebiusReal
        have h1 : |(μ q : ℝ)| = 1 := by exact_mod_cast abs_moebius_eq_one_of_squarefree hsq
        rw [← sq_abs, h1]; norm_num
      rw [hμ]
      have hm := abs_coprimeHarmonicMoebius_le_ratio hsq (N / q)
      have hm2 : coprimeHarmonicMoebius q (N / q) ^ 2 ≤ ((q : ℝ) / (Nat.totient q : ℝ)) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hm 2
      have hJ := jordanTotient2_le_sq q
      have hJ0 := jordanTotient2_nonneg q
      have hqN' : (q : ℝ) ≤ N := by exact_mod_cast hqN
      have hr0 : 0 ≤ ((q : ℝ) / (Nat.totient q : ℝ)) ^ 2 := sq_nonneg _
      calc jordanTotient2 q * (1 / (q : ℝ) ^ 2 * coprimeHarmonicMoebius q (N / q) ^ 2)
          ≤ (q : ℝ) ^ 2 * (1 / (q : ℝ) ^ 2 * ((q : ℝ) / (Nat.totient q : ℝ)) ^ 2) := by
            apply mul_le_mul hJ _ (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left hm2 (by positivity)
        _ = (q : ℝ) * (((q : ℝ) / (Nat.totient q : ℝ)) ^ 2 / (q : ℝ)) := by field_simp
        _ ≤ (N : ℝ) * (((q : ℝ) / (Nat.totient q : ℝ)) ^ 2 / (q : ℝ)) :=
            mul_le_mul_of_nonneg_right hqN' (by positivity)
    · rw [moebiusReal_eq_zero_of_not_squarefree q hsq]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, zero_mul,
        mul_zero]
      positivity
  calc ∑ q ∈ Icc 2 N, jordanTotient2 q * selbergMultiplesCoord N moebiusReal q ^ 2
      ≤ ∑ q ∈ Icc 2 N, (N : ℝ) * (((q : ℝ) / (Nat.totient q : ℝ)) ^ 2 / (q : ℝ)) := sum_le_sum hmode
    _ ≤ ∑ q ∈ Icc 1 N, (N : ℝ) * (((q : ℝ) / (Nat.totient q : ℝ)) ^ 2 / (q : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg (fun q hq => by simp only [mem_Icc] at hq ⊢; omega)
          fun q _ _ => by positivity
    _ = (N : ℝ) * ∑ q ∈ Icc 1 N, ((q : ℝ) / (Nat.totient q : ℝ)) ^ 2 / (q : ℝ) := by rw [mul_sum]
    _ ≤ (N : ℝ) * (64 * (1 + Real.log N)) :=
        mul_le_mul_of_nonneg_left (RHTower.Sieve.sum_totientRatio_sq_div_le N) (Nat.cast_nonneg N)
    _ = 64 * (N : ℝ) * (1 + Real.log N) := by ring

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
