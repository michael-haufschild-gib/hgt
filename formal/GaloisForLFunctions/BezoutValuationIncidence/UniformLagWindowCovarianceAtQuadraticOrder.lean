import GaloisForLFunctions.BezoutValuationIncidence.TrapezoidWindowSandwichAtQuadraticOrder
import GaloisForLFunctions.BezoutValuationIncidence.PolynomialHorizonRecoveryFromArbitraryPhaseWindows
import GaloisForLFunctions.BezoutValuationIncidence.PhaseUniformWindowPoincareAndLongWindowDissipation
import GaloisForLFunctions.BezoutValuationIncidence.RamanujanLagCoefficientAndTotientQuotient

/-!
# Window covariances at every lag, at quadratic order

The Ramanujan sum is the power sum of the primitive roots: `Σ_{ζ primitive of order q} ζ^g = c_q(g)`,
because both sides have divisor sums `q [q ∣ g]`. For a centered response `s' = s - H` with Selberg
coordinates `Y`, the lagged sums `s'(k) ± s'(k + g)` are exponential sums over the response
frequencies with coefficients `Y(ord ζ)(1 ± ζ^g)`. Polarization and the box-window sandwich give,
at every phase `A`, length `K` and lag `g`,

`|Σ_{A<k≤A+K} (s(k) - H)(s(k+g) - H) - K Cov(g)| ≤ (2N² - 1) V`,

with `Cov(g) = Σ_{2 ≤ e ≤ N} c_e(g) Y(e)²` the complete-period covariance and `V` the variance.
The bound is uniform in the lag. It replaces the constant `Σ_{q ≤ N} σ(q)²/φ(q)` of order
`N² log N` in the window covariance and lag-spectrum laws, and at lag one it bounds the windowed
successor correlation by the period successor reserve at quadratic order.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower.Sieve
open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ## §1. The Ramanujan sum as a power sum of primitive roots -/

theorem ramanujanLagWeight_eq_ramanujanLagCoefficient (g q : ℕ) :
    ramanujanLagWeight g q = ramanujanLagCoefficient q g := by
  rw [ramanujanLagWeight_eq_sum_divisors, ramanujanLagCoefficient]
  refine sum_congr rfl fun d _ => ?_
  rw [mul_comm, moebiusReal]

/-- The roots of unity of order dividing `q` are the primitive roots of the divisors of `q`. -/
theorem sum_divisors_sum_primitiveRoots_pow {q : ℕ} (hq : 0 < q) (g : ℕ) :
    ∑ d ∈ q.divisors, ∑ ζ ∈ primitiveRoots d ℂ, ζ ^ g = if q ∣ g then (q : ℂ) else 0 := by
  classical
  rw [← sum_nthRootsFinset_pow hq g, IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots,
    sum_biUnion fun d _ d' _ hne => IsPrimitiveRoot.disjoint hne]

/-- **Ramanujan's sum is the power sum of the primitive roots.** -/
theorem sum_primitiveRoots_pow (g : ℕ) {q : ℕ} (hq : 0 < q) :
    ∑ ζ ∈ primitiveRoots q ℂ, ζ ^ g = (ramanujanLagWeight g q : ℂ) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    have hA := sum_divisors_sum_primitiveRoots_pow hq g
    have hB : ∑ d ∈ q.divisors, (ramanujanLagWeight g d : ℂ) = if q ∣ g then (q : ℂ) else 0 := by
      have h := sum_divisors_ramanujanLagCoefficient q g
      simp_rw [← ramanujanLagWeight_eq_ramanujanLagCoefficient] at h
      rw [← Complex.ofReal_sum, h]
      split_ifs <;> simp
    rw [← Nat.cons_self_properDivisors hq.ne', sum_cons] at hA hB
    have hprop : ∑ d ∈ q.properDivisors, ∑ ζ ∈ primitiveRoots d ℂ, ζ ^ g =
        ∑ d ∈ q.properDivisors, (ramanujanLagWeight g d : ℂ) :=
      sum_congr rfl fun d hd => by
        have hd' := Nat.mem_properDivisors.mp hd
        exact ih d hd'.2 (Nat.pos_of_dvd_of_pos hd'.1 hq)
    rw [hprop] at hA
    exact add_right_cancel (hA.trans hB.symm)

/-! ## §2. Order-graded sums over the response frequencies -/

theorem sum_responseRoots_eq_sum_primitiveRoots (N : ℕ) (F : ℂ → ℂ) :
    ∑ ζ ∈ responseRoots N, F ζ = ∑ q ∈ Icc 1 N, ∑ ζ ∈ primitiveRoots q ℂ, F ζ := by
  classical
  have hset : responseRoots N = (Icc 1 N).biUnion fun q => primitiveRoots q ℂ := by
    ext ζ
    rw [mem_biUnion]
    constructor
    · intro hζ
      have hq := orderOf_mem_Icc_of_mem_responseRoots hζ
      exact ⟨orderOf ζ, hq,
        (mem_primitiveRoots (mem_Icc.mp hq).1).mpr (IsPrimitiveRoot.orderOf ζ)⟩
    · rintro ⟨q, hq, hζ⟩
      exact primitiveRoot_mem_responseRoots hq ((mem_primitiveRoots (mem_Icc.mp hq).1).mp hζ)
  rw [hset, sum_biUnion fun q _ q' _ hne => IsPrimitiveRoot.disjoint hne]

/-- Weighting the lag phase `ζ^g` by a function of the order gives Ramanujan sums. -/
theorem sum_responseRoots_orderOf_mul_pow (N : ℕ) (f : ℕ → ℝ) (g : ℕ) :
    ∑ ζ ∈ responseRoots N, (f (orderOf ζ) : ℂ) * ζ ^ g =
      ((∑ q ∈ Icc 1 N, f q * ramanujanLagWeight g q : ℝ) : ℂ) := by
  rw [sum_responseRoots_eq_sum_primitiveRoots, Complex.ofReal_sum]
  refine sum_congr rfl fun q hq => ?_
  have hq0 := (mem_Icc.mp hq).1
  rw [sum_congr rfl (g := fun ζ => (f q : ℂ) * ζ ^ g) fun ζ hζ => by
      rw [← ((mem_primitiveRoots hq0).mp hζ).eq_orderOf],
    ← mul_sum, sum_primitiveRoots_pow g hq0, Complex.ofReal_mul]

/-! ## §3. Polarization -/

/-- **Uniform-lag window covariance at quadratic order.** -/
theorem abs_window_lag_covariance_sub_le {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) (A K g : ℕ) :
    |∑ k ∈ Icc (A + 1) (A + K),
        (sieveSeq N c k - finiteHarmonicSum N c) * (sieveSeq N c (k + g) - finiteHarmonicSum N c) -
        K * TwoLagSieve.periodCovariance N c g| ≤
      (2 * (N : ℝ) ^ 2 - 1) * sieveVariance N c := by
  set H := finiteHarmonicSum N c
  set c' := sieveRowShift c H with hc'
  have hN1 : 1 ≤ N := by omega
  have hs' : ∀ k, sieveSeq N c k - H = sieveSeq N c' k := fun k =>
    (sieveSeq_sieveRowShift hN1 k c H).symm
  set b : ℂ → ℝ := fun ζ => selbergMultiplesCoord N c' (orderOf ζ) with hb
  have hspec : ∀ k, (sieveSeq N c' k : ℂ) = ∑ ζ ∈ responseRoots N, (b ζ : ℂ) * ζ ^ k :=
    fun k => sieveSeq_eq_sum_responseRoots N c' k
  -- the lagged sums `s'(k) ± s'(k+g)` as exponential sums
  set ap : ℂ → ℂ := fun ζ => (b ζ : ℂ) * (1 + ζ ^ g) with hap
  set am : ℂ → ℂ := fun ζ => (b ζ : ℂ) * (1 - ζ ^ g) with ham
  have hup : ∀ k, (sieveSeq N c' k + sieveSeq N c' (k + g)) ^ 2 =
      ‖∑ ζ ∈ responseRoots N, ap ζ * ζ ^ k‖ ^ 2 := fun k => by
    have : ((sieveSeq N c' k + sieveSeq N c' (k + g) : ℝ) : ℂ) =
        ∑ ζ ∈ responseRoots N, ap ζ * ζ ^ k := by
      rw [Complex.ofReal_add, hspec, hspec, ← sum_add_distrib]
      refine sum_congr rfl fun ζ _ => ?_
      rw [hap, pow_add]
      ring
    rw [← this, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hum : ∀ k, (sieveSeq N c' k - sieveSeq N c' (k + g)) ^ 2 =
      ‖∑ ζ ∈ responseRoots N, am ζ * ζ ^ k‖ ^ 2 := fun k => by
    have : ((sieveSeq N c' k - sieveSeq N c' (k + g) : ℝ) : ℂ) =
        ∑ ζ ∈ responseRoots N, am ζ * ζ ^ k := by
      rw [Complex.ofReal_sub, hspec, hspec, ← sum_sub_distrib]
      refine sum_congr rfl fun ζ _ => ?_
      rw [ham, pow_add]
      ring
    rw [← this, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hP := abs_window_sum_norm_sq_sub_le hN (subset_refl _) ap A K
  have hM := abs_window_sum_norm_sq_sub_le hN (subset_refl _) am A K
  simp only [← hup] at hP
  simp only [← hum] at hM
  -- coefficient energies
  have hnorm : ∀ ζ ∈ responseRoots N, ‖ζ ^ g‖ = 1 := fun ζ hζ => by
    rw [norm_pow, norm_eq_one_of_mem_responseRoots hζ, one_pow]
  have hcoef : ∀ ζ ∈ responseRoots N,
      ‖ap ζ‖ ^ 2 - ‖am ζ‖ ^ 2 = 4 * (b ζ ^ 2 * (ζ ^ g).re) ∧
        ‖ap ζ‖ ^ 2 + ‖am ζ‖ ^ 2 = 4 * b ζ ^ 2 := by
    intro ζ hζ
    have hz := hnorm ζ hζ
    have hre : (ζ ^ g).re ^ 2 + (ζ ^ g).im ^ 2 = 1 := by
      have h := Complex.normSq_eq_norm_sq (ζ ^ g)
      rw [hz, Complex.normSq_apply] at h
      nlinarith
    simp only [hap, ham, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, Complex.sub_re,
      Complex.sub_im]
    constructor <;> nlinarith
  set Bp := ∑ ζ ∈ responseRoots N, ‖ap ζ‖ ^ 2
  set Bm := ∑ ζ ∈ responseRoots N, ‖am ζ‖ ^ 2
  have hdiff : Bp - Bm = 4 * ∑ ζ ∈ responseRoots N, b ζ ^ 2 * (ζ ^ g).re := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun ζ hζ => (hcoef ζ hζ).1
  have hsum : Bp + Bm = 4 * ∑ ζ ∈ responseRoots N, b ζ ^ 2 := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun ζ hζ => (hcoef ζ hζ).2
  -- the diagonal is the period covariance and the energy is the variance
  have hcov : ∑ ζ ∈ responseRoots N, b ζ ^ 2 * (ζ ^ g).re =
      TwoLagSieve.periodCovariance N c g := by
    have h := sum_responseRoots_orderOf_mul_pow N (fun q => selbergMultiplesCoord N c' q ^ 2) g
    have hre := congrArg Complex.re h
    simp only [Complex.re_sum, Complex.ofReal_re] at hre
    have hl : ∀ ζ ∈ responseRoots N,
        (((selbergMultiplesCoord N c' (orderOf ζ) ^ 2 : ℝ) : ℂ) * ζ ^ g).re =
          b ζ ^ 2 * (ζ ^ g).re := fun ζ _ => by
      rw [Complex.re_ofReal_mul]
    rw [sum_congr rfl hl] at hre
    have hIoc : Ioc 1 N = Icc 2 N := by
      ext e
      simp only [mem_Ioc, mem_Icc]
      omega
    rw [hre, periodCovariance_eq_ramanujanLagWeight_diagonal, Icc_eq_cons_Ioc (by omega : 1 ≤ N),
      sum_cons, hIoc]
    have h1 : selbergMultiplesCoord N c' 1 = 0 := by
      have := finiteHarmonicSum_sieveRowShift hN1 c H
      unfold finiteHarmonicSum at this
      simp only [selbergMultiplesCoord, one_dvd, filter_true]
      rw [this]
      exact sub_self _
    rw [h1, zero_pow two_ne_zero, zero_mul, zero_add]
    refine sum_congr rfl fun e he => ?_
    rw [selbergMultiplesCoord_sieveRowShift_of_two_le N c H (mem_Icc.mp he).1, mul_comm]
  have hvar : ∑ ζ ∈ responseRoots N, b ζ ^ 2 = sieveVariance N c := by
    rw [sum_responseRoots_selberg_sq, selbergTotientDiagonalForm_sieveRowShift hN1, sub_self,
      zero_pow two_ne_zero, zero_add]
  -- polarization
  have hpol : ∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c k - H) * (sieveSeq N c (k + g) - H) =
      (∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c' k + sieveSeq N c' (k + g)) ^ 2 -
        ∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c' k - sieveSeq N c' (k + g)) ^ 2) / 4 := by
    rw [← sum_sub_distrib, sum_div]
    refine sum_congr rfl fun k _ => ?_
    rw [hs', hs']
    ring
  rw [hpol, ← hcov, ← hvar]
  have hP' := abs_le.mp hP
  have hM' := abs_le.mp hM
  have hBm : 0 ≤ Bm := sum_nonneg fun _ _ => sq_nonneg _
  have hBp : 0 ≤ Bp := sum_nonneg fun _ _ => sq_nonneg _
  have hNR : (1 : ℝ) ≤ 2 * (N : ℝ) ^ 2 - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  rw [abs_le]
  constructor <;> nlinarith

/-! ## §4. Consequences for the window laws -/

/-- Every normalized window covariance is within `(2N² - 1) V / K` of the period covariance. -/
theorem abs_windowLagCovariance_sub_le_two_mul_sq {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) (A g : ℕ)
    {K : ℕ} (hK : 0 < K) :
    |windowLagCovariance N c A K g - TwoLagSieve.periodCovariance N c g| ≤
      (2 * (N : ℝ) ^ 2 - 1) * sieveVariance N c / K := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have h := abs_window_lag_covariance_sub_le hN c A K g
  rw [windowLagCovariance, le_div_iff₀ hKR]
  calc |(∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c k - finiteHarmonicSum N c) *
          (sieveSeq N c (k + g) - finiteHarmonicSum N c)) / K -
          TwoLagSieve.periodCovariance N c g| * K
      = |∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c k - finiteHarmonicSum N c) *
          (sieveSeq N c (k + g) - finiteHarmonicSum N c) -
          K * TwoLagSieve.periodCovariance N c g| := by
        rw [← abs_of_pos hKR, ← abs_mul, abs_of_pos hKR, sub_mul, div_mul_cancel₀ _ hKR.ne',
          mul_comm]
    _ ≤ _ := h

/-- The lag-spectrum readout of window covariances recovers every Selberg energy within
`H_N² (2N² - 1) V / K`. -/
theorem abs_lagSpectrumReadout_window_sub_le_two_mul_sq {N q : ℕ} (hN : 2 ≤ N)
    (hq : q ∈ Icc 2 N) (c : ℕ → ℝ) (A : ℕ) {K : ℕ} (hK : 0 < K) :
    |lagSpectrumReadout N q (windowLagCovariance N c A K) - selbergMultiplesCoord N c q ^ 2| ≤
      (harmonic N : ℝ) ^ 2 * ((2 * (N : ℝ) ^ 2 - 1) * sieveVariance N c / K) :=
  abs_lagSpectrumReadout_sub_le hq c _ fun g _ =>
    abs_windowLagCovariance_sub_le_two_mul_sq hN c A g hK

end

end GaloisForLFunctions.BezoutValuationIncidence
