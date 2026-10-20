import GaloisForLFunctions.BezoutValuationIncidence.SharpInitialPrefixObservabilityAndExactGramDeterminants
import GaloisForLFunctions.BiScaleUncertainty.SignedLcmFractionalDefectAndCompleteFibreCollapse

/-!
# Phase-uniform window sandwich and a quadratic observability horizon

On a window of `K` consecutive positions the squared response of a row equals `K` times its
period mean square up to the signed lcm defect, whose size is at most `‖c‖₁²`. Finite
Ramanujan inversion `c(d) = d Σ_m μ(m) Y(dm)` bounds `‖c‖₁ ≤ Σ_q σ(q)|Y(q)|`, and
Cauchy–Schwarz against the Selberg form gives `‖c‖₁² ≤ S_N Q_Sel(c)` with the explicit
observability constant `S_N = Σ_{q ≤ N} σ(q)²/φ(q) ≤ (27/4) N² (1 + log N)`.

Hence, at every phase `A` and every offset `κ`,
`|Σ_{A < k ≤ A+K} (s(k) - κ)² - K Q| ≤ S_N Q`, `Q = (H - κ)² + V`:
windows longer than `S_N` reproduce the period variance up to a relative error `S_N/K`.
A row whose response is constant on such a window, or whose prefix discrepancy vanishes on
`K + 1` consecutive prefixes, has zero variance. This replaces the exponentially long
common-return windows by polynomially long windows at arbitrary phase. It does not reach the
conjectured linear horizon `2N - 3`.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ## §1. Shifting the response by a constant -/

/-- The row whose response is the response of `c` minus `κ`: only the unit coefficient moves. -/
def sieveRowShift (c : ℕ → ℝ) (κ : ℝ) : ℕ → ℝ :=
  fun d => c d - if d = 1 then κ else 0

theorem sieveSeq_sieveRowShift {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (c : ℕ → ℝ) (κ : ℝ) :
    sieveSeq N (sieveRowShift c κ) k = sieveSeq N c k - κ := by
  have h1 : (1 : ℕ) ∈ (Icc 1 N).filter (fun d => d ∣ k) :=
    mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hN⟩, one_dvd k⟩
  unfold sieveSeq sieveRowShift
  rw [sum_sub_distrib, sum_ite_eq' _ 1, if_pos h1]

theorem finiteHarmonicSum_sieveRowShift {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (κ : ℝ) :
    finiteHarmonicSum N (sieveRowShift c κ) = finiteHarmonicSum N c - κ := by
  unfold finiteHarmonicSum sieveRowShift
  simp only [sub_div, sum_sub_distrib]
  rw [show (∑ d ∈ Icc 1 N, (if d = 1 then κ else 0) / (d : ℝ)) =
      ∑ d ∈ Icc 1 N, if d = 1 then κ else 0 from
    sum_congr rfl fun d _ => by split_ifs with h <;> simp [h]]
  rw [sum_ite_eq' _ 1, if_pos (mem_Icc.mpr ⟨le_rfl, hN⟩)]

theorem sieveVariance_sieveRowShift (N : ℕ) (c : ℕ → ℝ) (κ : ℝ) :
    sieveVariance N (sieveRowShift c κ) = sieveVariance N c := by
  unfold sieveVariance
  refine sum_congr rfl fun e he => ?_
  have he2 : 2 ≤ e := (mem_Icc.mp he).1
  congr 2
  unfold selbergMultiplesCoord sieveRowShift
  refine sum_congr rfl fun d hd => ?_
  have hd1 : d ≠ 1 := by
    rintro rfl
    have := Nat.le_of_dvd one_pos (mem_filter.mp hd).2
    omega
  simp [hd1]

/-- The period mean square of the shifted row is the offset harmonic square plus the variance. -/
theorem selbergTotientDiagonalForm_sieveRowShift {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (κ : ℝ) :
    selbergTotientDiagonalForm N (sieveRowShift c κ) =
      (finiteHarmonicSum N c - κ) ^ 2 + sieveVariance N c := by
  rw [selberg_eq_harmonic_sq_add_variance, finiteHarmonicSum_sieveRowShift hN,
    sieveVariance_sieveRowShift]

/-! ## §2. The window error is at most the squared `ℓ¹` norm -/

/-- Two fractional parts differ by at most one, so the lcm defect moves by at most `‖c‖₁²`. -/
theorem abs_signedLcmFractDefect_sub_le (N M₁ M₂ : ℕ) (c : ℕ → ℝ) :
    |signedLcmFractDefect N M₂ c - signedLcmFractDefect N M₁ c| ≤
      (∑ d ∈ Icc 1 N, |c d|) ^ 2 := by
  unfold signedLcmFractDefect
  rw [← sum_sub_distrib, sq, sum_mul_sum, ← sum_product']
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p _ => ?_)
  have hf : ∀ M, 0 ≤ fractDivSeq (Nat.lcm p.1 p.2) M ∧ fractDivSeq (Nat.lcm p.1 p.2) M < 1 :=
    fun M => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hdiff : |fractDivSeq (Nat.lcm p.1 p.2) M₂ - fractDivSeq (Nat.lcm p.1 p.2) M₁| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hf M₁, hf M₂]
  rw [← mul_sub, abs_mul, abs_mul]
  calc |c p.1| * |c p.2| * |fractDivSeq (Nat.lcm p.1 p.2) M₂ - fractDivSeq (Nat.lcm p.1 p.2) M₁|
      ≤ |c p.1| * |c p.2| * 1 :=
        mul_le_mul_of_nonneg_left hdiff (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = |c p.1| * |c p.2| := mul_one _

/-- On every window, the squared response is `K Q_Sel` up to `‖c‖₁²`, at every phase. -/
theorem abs_window_sum_sq_sieveSeq_sub_le (N A K : ℕ) (c : ℕ → ℝ) :
    |(∑ k ∈ Icc (A + 1) (A + K), sieveSeq N c k ^ 2) -
        (K : ℝ) * selbergTotientDiagonalForm N c| ≤ (∑ d ∈ Icc 1 N, |c d|) ^ 2 := by
  have hwin := sievedDivisorIntervalMeanSquare_eq_selberg_sub_defect_diff N A (A + K)
    (Nat.le_add_right A K) c
  rw [show A + K - A = K by omega] at hwin
  have hsum : (∑ k ∈ Icc (A + 1) (A + K), sieveSeq N c k ^ 2) =
      ∑ k ∈ Icc (A + 1) (A + K), sievedDivisorSum N c k ^ (2 : ℕ) :=
    sum_congr rfl fun k hk => by
      rw [sieveSeq_eq_sievedDivisorSum N c (by have := (mem_Icc.mp hk).1; omega)]
  rw [hsum, hwin, sub_sub_cancel_left, abs_neg]
  exact abs_signedLcmFractDefect_sub_le N A (A + K) c

/-! ## §3. Finite Ramanujan inversion and the inverse `ℓ¹` inequality -/

private theorem sum_moebius_divisorsAntidiagonal (n : ℕ) :
    (∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℝ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => (f n : ℝ)) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply, one_apply] at h
  rw [Nat.sum_divisorsAntidiagonal (fun a _ => (μ a : ℝ))]
  push_cast at h
  rw [h]

private theorem sum_filter_dvd_reindex (p N : ℕ) (hp : 0 < p) (f : ℕ → ℝ) :
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

/-- **Finite Ramanujan inversion.** Every coefficient of a row is recovered from its Selberg
multiples coordinates: `c(d) = d Σ_{m ≤ N/d} μ(m) Y(dm)`. -/
theorem sieveRow_eq_moebius_selbergMultiplesCoord {N d : ℕ} (hd : d ∈ Icc 1 N) (c : ℕ → ℝ) :
    c d = (d : ℝ) * ∑ m ∈ Icc 1 (N / d), (μ m : ℝ) * selbergMultiplesCoord N c (d * m) := by
  obtain ⟨hd1, hdN⟩ := mem_Icc.mp hd
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hY : ∀ m ∈ Icc 1 (N / d), selbergMultiplesCoord N c (d * m) =
      ∑ i ∈ Icc 1 (N / d / m), c (d * (m * i)) / ((d * (m * i) : ℕ) : ℝ) := by
    intro m hm
    have hm1 := (mem_Icc.mp hm).1
    unfold selbergMultiplesCoord
    rw [sum_filter_dvd_reindex (d * m) N (Nat.mul_pos (by omega) hm1), Nat.div_div_eq_div_mul]
    simp only [Nat.mul_assoc]
  rw [sum_congr rfl fun m hm => by rw [hY m hm, mul_sum]]
  rw [← sum_Icc_divisorsAntidiagonal_swap
    (fun a b => (μ a : ℝ) * (c (d * (a * b)) / ((d * (a * b) : ℕ) : ℝ))) (N / d)]
  have hcol : ∀ n ∈ Icc 1 (N / d),
      (∑ x ∈ n.divisorsAntidiagonal,
        (μ x.1 : ℝ) * (c (d * (x.1 * x.2)) / ((d * (x.1 * x.2) : ℕ) : ℝ))) =
      (if n = 1 then 1 else 0) * (c (d * n) / ((d * n : ℕ) : ℝ)) := by
    intro n _
    rw [← sum_moebius_divisorsAntidiagonal n, sum_mul]
    exact sum_congr rfl fun x hx => by rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
  rw [sum_congr rfl hcol]
  have h1 : 1 ∈ Icc 1 (N / d) := mem_Icc.mpr ⟨le_rfl, (Nat.le_div_iff_mul_le (by omega)).mpr
    (by simpa using hdN)⟩
  rw [sum_eq_single_of_mem 1 h1 fun n _ hn => by simp [hn]]
  simp only [if_pos, mul_one, one_mul]
  field_simp

/-- **Inverse `ℓ¹` inequality.** `Σ_d |c(d)| ≤ Σ_q σ(q) |Y(q)|`. -/
theorem sum_abs_le_sum_sigma_mul_abs_selbergMultiplesCoord (N : ℕ) (c : ℕ → ℝ) :
    (∑ d ∈ Icc 1 N, |c d|) ≤
      ∑ q ∈ Icc 1 N, ((ArithmeticFunction.sigma 1 q : ℕ) : ℝ) * |selbergMultiplesCoord N c q| := by
  have hpt : ∀ d ∈ Icc 1 N,
      |c d| ≤ ∑ m ∈ Icc 1 (N / d), (d : ℝ) * |selbergMultiplesCoord N c (d * m)| := by
    intro d hd
    rw [sieveRow_eq_moebius_selbergMultiplesCoord hd c, abs_mul, Nat.abs_cast, ← mul_sum]
    refine mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans
      (sum_le_sum fun m _ => ?_)) (Nat.cast_nonneg d)
    rw [abs_mul]
    have : |(μ m : ℝ)| ≤ 1 := by
      have := abs_moebius_le_one (n := m)
      exact_mod_cast this
    exact (mul_le_of_le_one_left (abs_nonneg _) this)
  refine (sum_le_sum hpt).trans_eq ?_
  rw [← sum_Icc_divisorsAntidiagonal_swap
    (fun a b => (a : ℝ) * |selbergMultiplesCoord N c (a * b)|) N]
  refine sum_congr rfl fun q _ => ?_
  have hq : ∀ x ∈ q.divisorsAntidiagonal,
      (x.1 : ℝ) * |selbergMultiplesCoord N c (x.1 * x.2)| =
        (x.1 : ℝ) * |selbergMultiplesCoord N c q| := fun x hx => by
    rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
  rw [sum_congr rfl hq, ← sum_mul, Nat.sum_divisorsAntidiagonal (fun a _ => (a : ℝ)),
    sigma_one_apply]
  push_cast
  ring

/-- The window observability constant `S_N = Σ_{q ≤ N} σ(q)² / φ(q)`. -/
def sieveWindowObservabilityConstant (N : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 N, ((ArithmeticFunction.sigma 1 q : ℕ) : ℝ) ^ 2 / (Nat.totient q : ℝ)

theorem sieveWindowObservabilityConstant_nonneg (N : ℕ) :
    0 ≤ sieveWindowObservabilityConstant N :=
  sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- **`ℓ¹` control by the period mean square.** `‖c‖₁² ≤ S_N Q_Sel(c)`. -/
theorem sum_abs_sq_le_observabilityConstant_mul_selberg (N : ℕ) (c : ℕ → ℝ) :
    (∑ d ∈ Icc 1 N, |c d|) ^ 2 ≤
      sieveWindowObservabilityConstant N * selbergTotientDiagonalForm N c := by
  have h1 := sum_abs_le_sum_sigma_mul_abs_selbergMultiplesCoord N c
  have hpos : ∀ q ∈ Icc 1 N, (0 : ℝ) < Nat.totient q := fun q hq => by
    exact_mod_cast Nat.totient_pos.mpr (mem_Icc.mp hq).1
  have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 N)
    (fun q => ((ArithmeticFunction.sigma 1 q : ℕ) : ℝ) / Real.sqrt (Nat.totient q))
    (fun q => Real.sqrt (Nat.totient q) * |selbergMultiplesCoord N c q|)
  have hfg : ∀ q ∈ Icc 1 N,
      ((ArithmeticFunction.sigma 1 q : ℕ) : ℝ) / Real.sqrt (Nat.totient q) *
        (Real.sqrt (Nat.totient q) * |selbergMultiplesCoord N c q|) =
      ((ArithmeticFunction.sigma 1 q : ℕ) : ℝ) * |selbergMultiplesCoord N c q| := fun q hq => by
    have hs : Real.sqrt (Nat.totient q) ≠ 0 := (Real.sqrt_pos.mpr (hpos q hq)).ne'
    field_simp
  have hf : ∀ q ∈ Icc 1 N, (((ArithmeticFunction.sigma 1 q : ℕ) : ℝ) / Real.sqrt (Nat.totient q)) ^ 2 =
      ((ArithmeticFunction.sigma 1 q : ℕ) : ℝ) ^ 2 / (Nat.totient q : ℝ) := fun q hq => by
    rw [div_pow, Real.sq_sqrt (hpos q hq).le]
  have hg : ∀ q ∈ Icc 1 N, (Real.sqrt (Nat.totient q) * |selbergMultiplesCoord N c q|) ^ 2 =
      (Nat.totient q : ℝ) * selbergMultiplesCoord N c q ^ (2 : ℕ) := fun q hq => by
    rw [mul_pow, Real.sq_sqrt (hpos q hq).le, sq_abs]
  rw [sum_congr rfl hfg, sum_congr rfl hf, sum_congr rfl hg] at hcs
  have h0 : 0 ≤ ∑ d ∈ Icc 1 N, |c d| := sum_nonneg fun _ _ => abs_nonneg _
  calc (∑ d ∈ Icc 1 N, |c d|) ^ 2
      ≤ (∑ q ∈ Icc 1 N, ((ArithmeticFunction.sigma 1 q : ℕ) : ℝ) * |selbergMultiplesCoord N c q|) ^ 2 :=
        pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := hcs

/-! ## §4. The phase-uniform sandwich and observability -/

/-- **Phase-uniform window sandwich.** For every phase `A`, length `K` and offset `κ`,
`|Σ_{A<k≤A+K} (s(k) - κ)² - K Q| ≤ S_N Q` with `Q = (H - κ)² + V`. -/
theorem abs_window_sum_sq_sub_le_observabilityConstant {N : ℕ} (hN : 1 ≤ N) (A K : ℕ)
    (c : ℕ → ℝ) (κ : ℝ) :
    |(∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c k - κ) ^ 2) -
        (K : ℝ) * ((finiteHarmonicSum N c - κ) ^ 2 + sieveVariance N c)| ≤
      sieveWindowObservabilityConstant N *
        ((finiteHarmonicSum N c - κ) ^ 2 + sieveVariance N c) := by
  have hshift : (∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c k - κ) ^ 2) =
      ∑ k ∈ Icc (A + 1) (A + K), sieveSeq N (sieveRowShift c κ) k ^ 2 :=
    sum_congr rfl fun k hk => by
      rw [sieveSeq_sieveRowShift hN k]
  rw [hshift, ← selbergTotientDiagonalForm_sieveRowShift hN]
  exact (abs_window_sum_sq_sieveSeq_sub_le N A K _).trans
    (sum_abs_sq_le_observabilityConstant_mul_selberg N _)

/-- Lower half of the sandwich: a window longer than `S_N` sees `(K - S_N)` times the period
mean square. -/
theorem window_sum_sq_ge {N : ℕ} (hN : 1 ≤ N) (A K : ℕ) (c : ℕ → ℝ) (κ : ℝ) :
    ((K : ℝ) - sieveWindowObservabilityConstant N) *
        ((finiteHarmonicSum N c - κ) ^ 2 + sieveVariance N c) ≤
      ∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c k - κ) ^ 2 := by
  have h := abs_window_sum_sq_sub_le_observabilityConstant hN A K c κ
  rw [abs_le] at h
  linarith [h.1]

/-- **Arbitrary-phase observability.** If the response is constant on a window longer than
`S_N`, the row has zero variance and the constant is the harmonic mean. -/
theorem sieveVariance_eq_zero_of_const_on_window {N A K : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (κ : ℝ)
    (hK : sieveWindowObservabilityConstant N < K)
    (hconst : ∀ k ∈ Icc (A + 1) (A + K), sieveSeq N c k = κ) :
    sieveVariance N c = 0 ∧ finiteHarmonicSum N c = κ := by
  have h := window_sum_sq_ge hN A K c κ
  rw [sum_eq_zero fun k hk => by rw [hconst k hk, sub_self]; ring] at h
  have hV : 0 ≤ sieveVariance N c :=
    sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hQ : (finiteHarmonicSum N c - κ) ^ 2 + sieveVariance N c ≤ 0 := by
    by_contra hneg
    push Not at hneg
    have := mul_pos (sub_pos.mpr hK) hneg
    linarith
  have hsq := sq_nonneg (finiteHarmonicSum N c - κ)
  refine ⟨by linarith, ?_⟩
  have : (finiteHarmonicSum N c - κ) ^ 2 = 0 := by linarith
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  linarith

/-- **Arbitrary-phase prefix observability.** Vanishing prefix discrepancy at `K + 1`
consecutive prefixes, `K > S_N`, forces zero variance, at every phase `A`. -/
theorem sieveVariance_eq_zero_of_discrepancy_window {N A K : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ)
    (hK : sieveWindowObservabilityConstant N < K)
    (hzero : ∀ M ∈ Icc A (A + K), sievePrefixDiscrepancy N M c = 0) :
    sieveVariance N c = 0 := by
  refine (sieveVariance_eq_zero_of_const_on_window (A := A) hN c (finiteHarmonicSum N c) hK
    fun k hk => ?_).1
  obtain ⟨hk1, hk2⟩ := mem_Icc.mp hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hstep := sievePrefixDiscrepancy_succ_sub N m c
  rw [hzero (m + 1) (mem_Icc.mpr ⟨by omega, hk2⟩), hzero m (mem_Icc.mpr ⟨by omega, by omega⟩),
    sub_zero] at hstep
  rw [sieveSeq_eq_sievedDivisorSum N c (by omega)]
  linarith

/-! ## §5. A near-quadratic bound on the observability constant -/

/-- The local loss at the primes `2` and `3` in the bound `σ(q)² ≤ κ(q) q d(q) φ(q)`. -/
def smallPrimeSigmaLoss (q : ℕ) : ℝ :=
  (if 2 ∣ q then 4 else 1) * (if 3 ∣ q then 27 / 16 else 1)

private theorem smallPrimeSigmaLoss_le (q : ℕ) : smallPrimeSigmaLoss q ≤ 27 / 4 := by
  unfold smallPrimeSigmaLoss
  split_ifs <;> norm_num

private theorem smallPrimeSigmaLoss_nonneg (q : ℕ) : 0 ≤ smallPrimeSigmaLoss q := by
  unfold smallPrimeSigmaLoss
  split_ifs <;> norm_num

private theorem indicator_mul_of_coprime {r : ℕ} (hr : r.Prime) {a b : ℕ} (hab : a.Coprime b)
    (x : ℝ) :
    (if r ∣ a * b then x else 1) = (if r ∣ a then x else 1) * (if r ∣ b then x else 1) := by
  by_cases ha : r ∣ a <;> by_cases hb : r ∣ b
  · have h1 : r ∣ 1 := by rw [← Nat.Coprime.gcd_eq_one hab]; exact Nat.dvd_gcd ha hb
    exact absurd (Nat.dvd_one.mp h1) hr.one_lt.ne'
  · simp [ha, hb, dvd_mul_of_dvd_left ha]
  · simp [ha, hb, dvd_mul_of_dvd_right hb]
  · simp [ha, hb, hr.dvd_mul]

private theorem smallPrimeSigmaLoss_mul {a b : ℕ} (hab : a.Coprime b) :
    smallPrimeSigmaLoss (a * b) = smallPrimeSigmaLoss a * smallPrimeSigmaLoss b := by
  unfold smallPrimeSigmaLoss
  rw [indicator_mul_of_coprime Nat.prime_two hab, indicator_mul_of_coprime Nat.prime_three hab]
  ring

private theorem prime_pow_sigma_bound {p : ℕ} (hp : p.Prime) (j : ℕ) :
    ((ArithmeticFunction.sigma 1 (p ^ (j + 1)) : ℕ) : ℝ) ^ 2 ≤
      smallPrimeSigmaLoss (p ^ (j + 1)) * ((p ^ (j + 1) : ℕ) : ℝ) *
        ((p ^ (j + 1)).divisors.card : ℝ) * (Nat.totient (p ^ (j + 1)) : ℝ) := by
  set P : ℝ := (p : ℝ) with hPdef
  have hP2 : (2 : ℝ) ≤ P := by rw [hPdef]; exact_mod_cast hp.two_le
  set S : ℝ := ((ArithmeticFunction.sigma 1 (p ^ (j + 1)) : ℕ) : ℝ) with hSdef
  have hS : S * (P - 1) = P ^ (j + 2) - 1 := by
    rw [hSdef, sigma_apply_prime_pow hp]
    push_cast
    simp only [mul_one]
    exact geom_sum_mul P (j + 2)
  have hS0 : 0 ≤ S := Nat.cast_nonneg _
  have hcard : ((p ^ (j + 1)).divisors.card : ℝ) = (j : ℝ) + 2 := by
    rw [← sigma_zero_apply, sigma_zero_apply_prime_pow hp]
    push_cast
    ring
  have htot : (Nat.totient (p ^ (j + 1)) : ℝ) = P ^ j * (P - 1) := by
    rw [Nat.totient_prime_pow hp (Nat.succ_pos j), Nat.succ_sub_one, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_sub hp.one_le, Nat.cast_one]
  rw [hcard, htot]
  push_cast
  -- the loss covers `p³ ≤ κ (j + 2) (p - 1)³`
  have hloss : P ^ 3 ≤ smallPrimeSigmaLoss (p ^ (j + 1)) * ((j : ℝ) + 2) * (P - 1) ^ 3 := by
    have hj : (2 : ℝ) ≤ (j : ℝ) + 2 := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have h2 : 2 ∣ p ^ (j + 1) ↔ p = 2 :=
      ⟨fun h => ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
        (Nat.prime_two.dvd_of_dvd_pow h)).symm,
        fun h => by subst h; exact dvd_pow_self 2 (Nat.succ_ne_zero j)⟩
    have h3 : 3 ∣ p ^ (j + 1) ↔ p = 3 :=
      ⟨fun h => ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h)).symm,
        fun h => by subst h; exact dvd_pow_self 3 (Nat.succ_ne_zero j)⟩
    unfold smallPrimeSigmaLoss
    by_cases hp2 : p = 2
    · rw [if_pos (h2.mpr hp2), if_neg (by rw [h3]; omega)]
      have hP : P = 2 := by rw [hPdef, hp2]; norm_num
      rw [hP]
      nlinarith
    by_cases hp3 : p = 3
    · rw [if_neg (by rw [h2]; omega), if_pos (h3.mpr hp3)]
      have hP : P = 3 := by rw [hPdef, hp3]; norm_num
      rw [hP]
      nlinarith
    rw [if_neg (by rw [h2]; exact hp2), if_neg (by rw [h3]; exact hp3)]
    have hp5 : (5 : ℝ) ≤ P := by
      have h5 : 5 ≤ p := by
        rcases (by have := hp.two_le; omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h | h | h | h
        · exact absurd h hp2
        · exact absurd h hp3
        · exact absurd hp (by rw [h]; norm_num)
        · exact h
      rw [hPdef]
      exact_mod_cast h5
    have hcube : P ^ 3 ≤ 2 * (P - 1) ^ 3 := by nlinarith [sq_nonneg (P - 5)]
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ P - 1) 3]
  have hP1 : 0 < P - 1 := by linarith
  have hkey : (S * (P - 1)) ^ 2 ≤ P ^ (2 * j + 4) := by
    rw [hS]
    have h1 : (1 : ℝ) ≤ P ^ (j + 2) := one_le_pow₀ (by linarith)
    have : P ^ (2 * j + 4) = (P ^ (j + 2)) ^ 2 := by ring
    rw [this]
    nlinarith
  have hPpow : 0 < P ^ (2 * j + 1) := pow_pos (by linarith) _
  have hrhs : P ^ (2 * j + 4) ≤
      smallPrimeSigmaLoss (p ^ (j + 1)) * ((j : ℝ) + 2) * (P - 1) ^ 3 * P ^ (2 * j + 1) := by
    have : P ^ (2 * j + 4) = P ^ 3 * P ^ (2 * j + 1) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hloss hPpow.le
  have hfin : S ^ 2 * (P - 1) ^ 2 ≤
      (smallPrimeSigmaLoss (p ^ (j + 1)) * P ^ (j + 1) * ((j : ℝ) + 2) * (P ^ j * (P - 1))) *
        (P - 1) ^ 2 := by
    have : (smallPrimeSigmaLoss (p ^ (j + 1)) * P ^ (j + 1) * ((j : ℝ) + 2) *
        (P ^ j * (P - 1))) * (P - 1) ^ 2 =
        smallPrimeSigmaLoss (p ^ (j + 1)) * ((j : ℝ) + 2) * (P - 1) ^ 3 * P ^ (2 * j + 1) := by
      ring
    rw [this]
    nlinarith
  exact le_of_mul_le_mul_right hfin (pow_pos hP1 2)

/-- **Multiplicative divisor bound.** `σ(q)² ≤ κ(q) q d(q) φ(q)` with `κ(q) ≤ 27/4`. -/
theorem sigma_sq_le_smallPrimeSigmaLoss_mul (q : ℕ) :
    ((ArithmeticFunction.sigma 1 q : ℕ) : ℝ) ^ 2 ≤
      smallPrimeSigmaLoss q * (q : ℝ) * (q.divisors.card : ℝ) * (Nat.totient q : ℝ) := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p k hp =>
    rcases k with _ | j
    · simp [smallPrimeSigmaLoss]
    · exact prime_pow_sigma_bound hp j
  | coprime a b _ _ hab ha hb =>
    rw [isMultiplicative_sigma.map_mul_of_coprime hab, Nat.Coprime.card_divisors_mul hab,
      Nat.totient_mul hab, smallPrimeSigmaLoss_mul hab]
    push_cast
    have hrb : 0 ≤ smallPrimeSigmaLoss a * (a : ℝ) * (a.divisors.card : ℝ) *
        (Nat.totient a : ℝ) := by
      have := smallPrimeSigmaLoss_nonneg a
      positivity
    calc (((ArithmeticFunction.sigma 1 a : ℕ) : ℝ) * ((ArithmeticFunction.sigma 1 b : ℕ) : ℝ)) ^ 2
        = ((ArithmeticFunction.sigma 1 a : ℕ) : ℝ) ^ 2 *
            ((ArithmeticFunction.sigma 1 b : ℕ) : ℝ) ^ 2 := by ring
      _ ≤ (smallPrimeSigmaLoss a * (a : ℝ) * (a.divisors.card : ℝ) * (Nat.totient a : ℝ)) *
          (smallPrimeSigmaLoss b * (b : ℝ) * (b.divisors.card : ℝ) * (Nat.totient b : ℝ)) :=
        mul_le_mul ha hb (sq_nonneg _) hrb
      _ = _ := by ring

/-- Dirichlet's divisor bound `Σ_{q ≤ N} d(q) ≤ N (1 + log N)`. -/
theorem sum_card_divisors_le (N : ℕ) :
    (∑ q ∈ Icc 1 N, (q.divisors.card : ℝ)) ≤ (N : ℝ) * (1 + Real.log N) := by
  have hcount : ∀ q ∈ Icc 1 N, (q.divisors.card : ℝ) =
      ∑ j ∈ Icc 1 N, if j ∣ q then (1 : ℝ) else 0 := by
    intro q hq
    obtain ⟨hq1, hqN⟩ := mem_Icc.mp hq
    rw [sum_boole]
    congr 1
    congr 1
    ext j
    simp only [Nat.mem_divisors, mem_filter, mem_Icc]
    constructor
    · rintro ⟨hj, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hj hq1, (Nat.le_of_dvd hq1 hj).trans hqN⟩, hj⟩
    · rintro ⟨_, hj⟩
      exact ⟨hj, by omega⟩
  rw [sum_congr rfl hcount, sum_comm]
  have hcol : ∀ j ∈ Icc 1 N, (∑ q ∈ Icc 1 N, if j ∣ q then (1 : ℝ) else 0) ≤ (N : ℝ) / j := by
    intro j hj
    rw [sum_boole]
    have hIoc : Icc 1 N = Ioc 0 N := by
      ext x
      simp only [mem_Icc, mem_Ioc]
      omega
    rw [hIoc, Nat.Ioc_filter_dvd_card_eq_div]
    exact Nat.cast_div_le
  refine (sum_le_sum hcol).trans ?_
  have hharm : (∑ j ∈ Icc 1 N, (N : ℝ) / j) = (N : ℝ) * (harmonic N : ℝ) := by
    rw [_root_.harmonic_eq_sum_Icc]
    push_cast
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by rw [div_eq_mul_inv]
  rw [hharm]
  exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (Nat.cast_nonneg N)

/-- **Near-quadratic observability constant.** `S_N ≤ (27/4) N² (1 + log N)`. -/
theorem sieveWindowObservabilityConstant_le (N : ℕ) :
    sieveWindowObservabilityConstant N ≤ 27 / 4 * (N : ℝ) ^ 2 * (1 + Real.log N) := by
  have hpt : ∀ q ∈ Icc 1 N, ((ArithmeticFunction.sigma 1 q : ℕ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ≤
      27 / 4 * (N : ℝ) * (q.divisors.card : ℝ) := by
    intro q hq
    obtain ⟨hq1, hqN⟩ := mem_Icc.mp hq
    have hphi : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq1
    rw [div_le_iff₀ hphi]
    refine (sigma_sq_le_smallPrimeSigmaLoss_mul q).trans ?_
    have hqR : (q : ℝ) ≤ N := by exact_mod_cast hqN
    have hd : 0 ≤ (q.divisors.card : ℝ) := Nat.cast_nonneg _
    have hk := smallPrimeSigmaLoss_le q
    have hk0 := smallPrimeSigmaLoss_nonneg q
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    calc smallPrimeSigmaLoss q * (q : ℝ) * (q.divisors.card : ℝ) * (Nat.totient q : ℝ)
        ≤ 27 / 4 * (N : ℝ) * (q.divisors.card : ℝ) * (Nat.totient q : ℝ) := by
          gcongr
      _ = _ := by ring
  unfold sieveWindowObservabilityConstant
  refine (sum_le_sum hpt).trans ?_
  rw [← mul_sum]
  calc 27 / 4 * (N : ℝ) * ∑ q ∈ Icc 1 N, (q.divisors.card : ℝ)
      ≤ 27 / 4 * (N : ℝ) * ((N : ℝ) * (1 + Real.log N)) :=
        mul_le_mul_of_nonneg_left (sum_card_divisors_le N) (by positivity)
    _ = _ := by ring

/-- **Quadratic arbitrary-phase observability horizon.** At every phase, vanishing prefix
discrepancy on more than `(27/4) N² (1 + log N) + 1` consecutive prefixes forces zero
variance. -/
theorem sieveVariance_eq_zero_of_discrepancy_window_quadratic {N A K : ℕ} (hN : 1 ≤ N)
    (c : ℕ → ℝ) (hK : 27 / 4 * (N : ℝ) ^ 2 * (1 + Real.log N) < K)
    (hzero : ∀ M ∈ Icc A (A + K), sievePrefixDiscrepancy N M c = 0) :
    sieveVariance N c = 0 :=
  sieveVariance_eq_zero_of_discrepancy_window hN c
    ((sieveWindowObservabilityConstant_le N).trans_lt hK) hzero

end

end GaloisForLFunctions.BezoutValuationIncidence
