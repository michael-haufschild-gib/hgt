import GaloisForLFunctions.BezoutValuationIncidence.UniformLagWindowCovarianceAtQuadraticOrder
import GaloisForLFunctions.BiScaleUncertainty.SieveCoordinateSupNorm

/-!
# Window Dirichlet energy and long-window dissipation at quadratic order

With every two-point window statistic known to quadratic order, the window laws of the successor
calculus lose their logarithm. Write `V` for the variance, `R = Σ_{e ≥ 2} (φ(e) - μ(e)) Y(e)²` for
the successor reserve and `S = 2N² - 1`.

* The lag-one period covariance is `Σ_{e ≥ 2} μ(e) Y(e)² = V - R`.
* The window Dirichlet energy `D_W = Σ_{A<k≤A+K} (s(k+1) - s(k))²` is two window squares minus twice a
  lag-one window covariance, so `|D_W - 2 K R| ≤ 4 S V` at every phase.
* Hence the window Poincaré inequality `Σ_W (s - H)² ≤ D_W + 5 S V`.
* The response deviates from its mean by at most `√((Φ(N) - 1) V)` at every point, since
  `|c_q(k)| ≤ φ(q)` and `Σ_{2 ≤ q ≤ N} φ(q) = Φ(N) - 1`.
* The renormalized window defect satisfies `2 R_W ≤ 4 H² - (K - 10 N²) V`: in `ker P` every window
  longer than `10 N²` is strictly dissipative at every phase.

The window sandwich itself cannot hold below `N² / (1 + log N)³` up to lower order, so the
quadratic scale of these thresholds is the natural one.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ## §1. The lag-one covariance is the variance minus the reserve -/

theorem periodCovariance_one_eq_sub_reserve {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    TwoLagSieve.periodCovariance N c 1 = sieveVariance N c - sieveSuccessorReserve N c := by
  rw [periodCovariance_eq_ramanujanLagWeight_diagonal, sieveSuccessorReserve_eq_sum_Icc_two hN]
  unfold sieveVariance
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun e _ => ?_
  rw [ramanujanLagWeight_one_left, moebiusReal]
  ring

/-! ## §2. Window Dirichlet energy and Poincaré inequality -/

theorem window_sum_sq_centered_bounds {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) (A K : ℕ) :
    |∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c k - finiteHarmonicSum N c) ^ 2 -
        K * sieveVariance N c| ≤ (2 * (N : ℝ) ^ 2 - 1) * sieveVariance N c := by
  have h := isWindowSandwichConstant_two_mul_sq hN A K c (finiteHarmonicSum N c)
  rwa [sub_self, zero_pow two_ne_zero, zero_add] at h

/-- **Window reserve sandwich at quadratic order.** `|D_W - 2 K R| ≤ 4 (2N² - 1) V`. -/
theorem abs_shortWindowDirichletEnergy_sub_reserve_le_two_mul_sq {N : ℕ} (hN : 2 ≤ N)
    (A K : ℕ) (c : ℕ → ℝ) :
    |shortWindowDirichletEnergy N A K c - 2 * (K : ℝ) * sieveSuccessorReserve N c| ≤
      4 * ((2 * (N : ℝ) ^ 2 - 1) * sieveVariance N c) := by
  set H := finiteHarmonicSum N c
  have hD : shortWindowDirichletEnergy N A K c =
      (∑ k ∈ Icc (A + 1 + 1) (A + 1 + K), (sieveSeq N c k - H) ^ 2) +
        (∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c k - H) ^ 2) -
          2 * ∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c k - H) * (sieveSeq N c (k + 1) - H) := by
    have hshift : (∑ k ∈ Icc (A + 1 + 1) (A + 1 + K), (sieveSeq N c k - H) ^ 2) =
        ∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c (k + 1) - H) ^ 2 := by
      rw [show A + 1 + K = A + K + 1 by omega, ← Finset.map_add_right_Icc, Finset.sum_map]
      rfl
    unfold shortWindowDirichletEnergy
    rw [hshift, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  have h1 := abs_le.mp (window_sum_sq_centered_bounds hN c (A + 1) K)
  have h2 := abs_le.mp (window_sum_sq_centered_bounds hN c A K)
  have h3 := abs_le.mp (abs_window_lag_covariance_sub_le hN c A K 1)
  rw [periodCovariance_one_eq_sub_reserve (by omega)] at h3
  rw [hD, abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- Two-sided window coercivity: `(K - 4 S) V ≤ D_W ≤ (4K + 4 S) V` with `S = 2N² - 1`. -/
theorem shortWindowDirichletEnergy_bounds_two_mul_sq {N : ℕ} (hN : 2 ≤ N) (A K : ℕ)
    (c : ℕ → ℝ) :
    ((K : ℝ) - 4 * (2 * (N : ℝ) ^ 2 - 1)) * sieveVariance N c ≤
        shortWindowDirichletEnergy N A K c ∧
      shortWindowDirichletEnergy N A K c ≤
        (4 * (K : ℝ) + 4 * (2 * (N : ℝ) ^ 2 - 1)) * sieveVariance N c := by
  have h := abs_le.mp (abs_shortWindowDirichletEnergy_sub_reserve_le_two_mul_sq hN A K c)
  obtain ⟨hlo, hhi⟩ := half_sieveVariance_le_sieveSuccessorReserve (by omega : 1 ≤ N) c
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  constructor <;> nlinarith [h.1, h.2]

/-- **Window Poincaré inequality at quadratic order.** `Σ_W (s - H)² ≤ D_W + 5 (2N² - 1) V`. -/
theorem window_poincare_two_mul_sq {N : ℕ} (hN : 2 ≤ N) (A K : ℕ) (c : ℕ → ℝ) :
    (∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c k - finiteHarmonicSum N c) ^ 2) ≤
      shortWindowDirichletEnergy N A K c + 5 * ((2 * (N : ℝ) ^ 2 - 1) * sieveVariance N c) := by
  have hs := (abs_le.mp (window_sum_sq_centered_bounds hN c A K)).2
  have hd := (shortWindowDirichletEnergy_bounds_two_mul_sq hN A K c).1
  nlinarith

/-! ## §3. The pointwise deviation bound -/

/-- **Sup bound.** `(s(k) - H)² ≤ (Φ(N) - 1) V` at every point. -/
theorem sieveSeq_sub_harmonic_sq_le {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (k : ℕ) :
    (sieveSeq N c k - finiteHarmonicSum N c) ^ 2 ≤
      ((cyclotomicIncidenceOrder N : ℝ) - 1) * sieveVariance N c := by
  have hexp := SieveMoments.sieveSeq_ramanujan_expansion N c k
  rw [Icc_eq_cons_Ioc hN, sum_cons] at hexp
  have hIoc : Ioc 1 N = Icc 2 N := by
    ext e
    simp only [mem_Ioc, mem_Icc]
    omega
  have h1 : ramanujanLagCoefficient 1 k = 1 := by simp [ramanujanLagCoefficient, moebiusReal]
  have hY1 : selbergMultiplesCoord N c 1 = finiteHarmonicSum N c := by
    simp [selbergMultiplesCoord, finiteHarmonicSum]
  rw [hIoc, h1, hY1, mul_one] at hexp
  have hdev : sieveSeq N c k - finiteHarmonicSum N c =
      ∑ q ∈ Icc 2 N, selbergMultiplesCoord N c q * ramanujanLagCoefficient q k := by
    rw [hexp]
    ring
  rw [hdev]
  have habs : |∑ q ∈ Icc 2 N, selbergMultiplesCoord N c q * ramanujanLagCoefficient q k| ≤
      ∑ q ∈ Icc 2 N, Real.sqrt (q.totient : ℝ) *
        (Real.sqrt (q.totient : ℝ) * |selbergMultiplesCoord N c q|) := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun q _ => ?_)
    rw [abs_mul, ← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right (SieveMoments.abs_ramanujanLagCoefficient_le_totient q k) (abs_nonneg _)
  have hcs := sum_mul_sq_le_sq_mul_sq (Icc 2 N) (fun q => Real.sqrt (q.totient : ℝ))
    (fun q => Real.sqrt (q.totient : ℝ) * |selbergMultiplesCoord N c q|)
  have hφ : ∑ q ∈ Icc 2 N, Real.sqrt (q.totient : ℝ) ^ 2 =
      (cyclotomicIncidenceOrder N : ℝ) - 1 := by
    simp only [Real.sq_sqrt (Nat.cast_nonneg _)]
    unfold cyclotomicIncidenceOrder
    rw [Icc_eq_cons_Ioc hN, sum_cons, hIoc]
    push_cast
    simp
  have hV : ∑ q ∈ Icc 2 N, (Real.sqrt (q.totient : ℝ) * |selbergMultiplesCoord N c q|) ^ 2 =
      sieveVariance N c := by
    unfold sieveVariance
    refine sum_congr rfl fun q _ => ?_
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), sq_abs]
  rw [hφ, hV] at hcs
  calc (∑ q ∈ Icc 2 N, selbergMultiplesCoord N c q * ramanujanLagCoefficient q k) ^ 2
      = |∑ q ∈ Icc 2 N, selbergMultiplesCoord N c q * ramanujanLagCoefficient q k| ^ 2 :=
        (sq_abs _).symm
    _ ≤ (∑ q ∈ Icc 2 N, Real.sqrt (q.totient : ℝ) *
          (Real.sqrt (q.totient : ℝ) * |selbergMultiplesCoord N c q|)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ ≤ _ := hcs

/-! ## §4. Long-window dissipation -/

/-- **Long-window dissipation at quadratic order.** At every phase,
`2 R_W ≤ 4 H² - (K - 10 N²) V` for the renormalized defect of the window `(A, A + K]`. -/
theorem two_mul_shortWindowRenormalizedDefect_le_ten_mul_sq {N : ℕ} (hN : 2 ≤ N) (A K : ℕ)
    (c : ℕ → ℝ) :
    2 * shortWindowRenormalizedDefect N A K c ≤
      4 * finiteHarmonicSum N c ^ 2 - ((K : ℝ) - 10 * (N : ℝ) ^ 2) * sieveVariance N c := by
  set H := finiteHarmonicSum N c
  set V := sieveVariance N c
  have hV : 0 ≤ V := sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  set m : ℝ := ((cyclotomicIncidenceOrder N : ℝ) - 1) * V with hm
  have hΦ : 2 * (cyclotomicIncidenceOrder N : ℝ) ≤ (N : ℝ) * (N + 1) := by
    exact_mod_cast two_mul_cyclotomicIncidenceOrder_le N
  have hΦ1 : (1 : ℝ) ≤ cyclotomicIncidenceOrder N := by
    have : 1 ≤ cyclotomicIncidenceOrder N := by
      unfold cyclotomicIncidenceOrder
      rw [Icc_eq_cons_Ioc (by omega : 1 ≤ N), sum_cons]
      simp
    exact_mod_cast this
  have hm0 : 0 ≤ m := mul_nonneg (by linarith) hV
  have he := sieveSeq_sub_harmonic_sq_le (by omega : 1 ≤ N) c (A + K + 1)
  have hb := sieveSeq_sub_harmonic_sq_le (by omega : 1 ≤ N) c (A + 1)
  rw [← hm] at he hb
  have hD := (shortWindowDirichletEnergy_bounds_two_mul_sq hN A K c).1
  rw [two_mul_shortWindowRenormalizedDefect_eq]
  -- boundary squares: `s = H + s'` with `s'² ≤ m`
  set x := sieveSeq N c (A + K + 1) - H
  set y := sieveSeq N c (A + 1) - H
  have hbd : sieveSeq N c (A + K + 1) ^ 2 - sieveSeq N c (A + 1) ^ 2 ≤ 2 * m + 4 * H ^ 2 := by
    have e1 : sieveSeq N c (A + K + 1) = x + H := by ring
    have e2 : sieveSeq N c (A + 1) = y + H := by ring
    rw [e1, e2]
    nlinarith [sq_nonneg (x - 2 * H), sq_nonneg (y + 2 * H), sq_nonneg x, sq_nonneg y]
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h2m : 2 * m ≤ ((N : ℝ) * (N + 1) - 2) * V := by
    rw [hm]
    nlinarith
  have hq : 0 ≤ ((N : ℝ) ^ 2 - N + 6) * V := mul_nonneg (by nlinarith) hV
  change ((K : ℝ) - 4 * (2 * (N : ℝ) ^ 2 - 1)) * V ≤ shortWindowDirichletEnergy N A K c at hD
  nlinarith [hD, hbd, h2m, hq]

/-- In `ker P`, every window longer than `10 N²` is strictly dissipative at every phase. -/
theorem shortWindowRenormalizedDefect_neg_of_ten_mul_sq_lt {N : ℕ} (hN : 2 ≤ N) (A K : ℕ)
    (c : ℕ → ℝ) (hker : finiteHarmonicSum N c = 0) (hK : 10 * (N : ℝ) ^ 2 < K)
    (hV : 0 < sieveVariance N c) :
    shortWindowRenormalizedDefect N A K c < 0 := by
  have h := two_mul_shortWindowRenormalizedDefect_le_ten_mul_sq hN A K c
  rw [hker] at h
  have := mul_pos (sub_pos.mpr hK) hV
  nlinarith

end

end GaloisForLFunctions.BezoutValuationIncidence
