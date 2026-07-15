import GaloisForLFunctions.RHTower.BVPrimeWindowHolomorphy
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import GaloisForLFunctions.RHTower.XiLogDerivNotHolonomic

/-!
# Dirichlet identities for bounded-variation prime windows

This file identifies the analytic scaled grid error with the finite-sum Mellin error in the paper,
then reverses the moving-window double series on its initial half-plane.
-/

open Complex Finset Set

noncomputable section

namespace RHTower
namespace CompactBVPrimeWindow

/-- Finite Mellin kernel at scale `k`, written with the original integer Mellin power. -/
def discreteMellinKernel (W : CompactBVPrimeWindow) (k : ℕ) (s : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (W.gridCount k),
    W (((i + 1 : ℕ) : ℝ) / k) * (((i + 1 : ℕ) : ℂ) ^ (-s))

/-- The paper's finite-sum quadrature error. -/
def mellinError (W : CompactBVPrimeWindow) (k : ℕ) (s : ℂ) : ℂ :=
  W.discreteMellinKernel k s - (k : ℂ) ^ (1 - s) * W.mellinTransform s

private theorem scale_mul_mellinIntegrand
    (W : CompactBVPrimeWindow) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (s : ℂ) :
    (k : ℂ) ^ (1 - s) * (((1 / (k : ℝ)) : ℝ) : ℂ) *
        W.mellinIntegrand s ((n : ℝ) / k) =
      W ((n : ℝ) / k) * (n : ℂ) ^ (-s) := by
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hscale :
      (k : ℂ) ^ (1 - s) * (((1 / (k : ℝ)) : ℝ) : ℂ) =
        (k : ℂ) ^ (-s) := by
    rw [one_div, Complex.ofReal_inv, Complex.ofReal_natCast,
      ← Complex.cpow_neg_one]
    rw [← Complex.cpow_add _ _ hkC]
    congr 1
    ring
  have hmul := Complex.mul_cpow_ofReal_nonneg
    (div_nonneg hnreal.le hkreal.le) hkreal.le (-s)
  have hdivmul : (n : ℝ) / k * k = n := by field_simp
  have hdivmulC :
      ((((n : ℝ) / k : ℝ) : ℂ) * (k : ℂ)) = (n : ℂ) := by
    exact_mod_cast hdivmul
  have hpower :
      ((((n : ℝ) / k : ℝ) : ℂ) ^ (-s)) * (k : ℂ) ^ (-s) =
        (n : ℂ) ^ (-s) := by
    simp only [Complex.ofReal_natCast] at hmul
    rw [hdivmulC] at hmul
    simpa only [Complex.ofReal_natCast] using hmul.symm
  rw [W.mellinIntegrand_eq_raw]
  rw [hscale]
  calc
    (k : ℂ) ^ (-s) *
        (W ((n : ℝ) / k) * ((((n : ℝ) / k : ℝ) : ℂ) ^ (-s))) =
      W ((n : ℝ) / k) *
        (((((n : ℝ) / k : ℝ) : ℂ) ^ (-s)) * (k : ℂ) ^ (-s)) := by ring
    _ = W ((n : ℝ) / k) * (n : ℂ) ^ (-s) := by rw [hpower]

/-- The Riemann-sum normalization is exactly the finite integer Mellin kernel. -/
theorem scale_mul_gridRiemannSum_eq_discreteMellinKernel
    (W : CompactBVPrimeWindow) {k : ℕ} (hk : 0 < k) (s : ℂ) :
    (k : ℂ) ^ (1 - s) * W.gridRiemannSum k s =
      W.discreteMellinKernel k s := by
  rw [gridRiemannSum, discreteMellinKernel, Complex.real_smul]
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact scale_mul_mellinIntegrand W (by omega) hk s

/-- The paper's finite-sum error is exactly the analytic scaled grid error. -/
theorem mellinError_eq_scaledGridError
    (W : CompactBVPrimeWindow) {k : ℕ} (hk : 0 < k) (s : ℂ) :
    W.mellinError k s = W.scaledGridError k s := by
  rw [mellinError, scaledGridError, gridError, mul_sub,
    W.scale_mul_gridRiemannSum_eq_discreteMellinKernel hk s]

/-- The finite Mellin error inherits the compact-uniform `k^{-Re s}` estimate. -/
theorem exists_uniform_norm_mellinError_le_rpow
    (W : CompactBVPrimeWindow) {K : Set ℂ} (hK : IsCompact K) (hKne : K.Nonempty) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ s ∈ K, ∀ k : ℕ, 1 ≤ k →
      ‖W.mellinError k s‖ ≤ Q * (k : ℝ) ^ (-s.re) := by
  obtain ⟨Q, hQ0, hQ⟩ := W.exists_uniform_norm_scaledGridError_le_rpow hK hKne
  refine ⟨Q, hQ0, ?_⟩
  intro s hs k hk
  rw [W.mellinError_eq_scaledGridError (by omega) s]
  exact hQ s hs k hk

end CompactBVPrimeWindow
end RHTower

namespace RHTower
namespace CompactBVPrimeWindow

/-- One term of the moving-window double series, indexed by prime-power index and output index. -/
def doubleTerm (W : CompactBVPrimeWindow) (s : ℂ) (kn : ℕ × ℕ) : ℂ :=
  if kn.1 = 0 ∨ kn.2 = 0 then 0 else
    ((ArithmeticFunction.vonMangoldt kn.1 / Real.sqrt kn.1 : ℝ) : ℂ) *
      W ((kn.2 : ℝ) / kn.1) * (kn.2 : ℂ) ^ (-s)

/-- The honest weighted moving-prime window at output index `n`. -/
def weightedPrimeWindow (W : CompactBVPrimeWindow) (n : ℕ) : ℂ :=
  ∑' k : ℕ, ((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ) *
    W ((n : ℝ) / k)

private theorem doubleTerm_eq_zero_of_gridCount_lt
    (W : CompactBVPrimeWindow) (s : ℂ) {k n : ℕ} (hk : 0 < k)
    (hn : W.gridCount k < n) :
    W.doubleTerm s (k, n) = 0 := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hceil : W.upper * (k : ℝ) < n := by
    have hcast : (W.gridCount k : ℝ) < n := by exact_mod_cast hn
    exact (Nat.le_ceil (W.upper * (k : ℝ))).trans_lt (by
      simpa only [gridCount] using hcast)
  have hratio : W.upper < (n : ℝ) / k := by
    exact (lt_div_iff₀ hkreal).2 (by simpa [mul_comm] using hceil)
  have hoff : (n : ℝ) / k ∉ Set.Icc W.lower W.upper := by
    simp only [Set.mem_Icc, not_and_or]
    exact Or.inr (not_le.mpr hratio)
  rw [doubleTerm, if_neg (by omega), W.eq_zero_off_support _ hoff]
  simp

end CompactBVPrimeWindow
end RHTower

namespace RHTower
namespace CompactBVPrimeWindow

private theorem norm_doubleTerm_le
    (W : CompactBVPrimeWindow) {s : ℂ} (hsre : 0 < s.re)
    {k n : ℕ} (hk : 0 < k) :
    ‖W.doubleTerm s (k, n)‖ ≤
      ArithmeticFunction.vonMangoldt k / Real.sqrt k *
        (eVariationOn W Set.univ).toReal *
          (W.lower * (k : ℝ)) ^ (-s.re) := by
  have hnonneg : 0 ≤
      ArithmeticFunction.vonMangoldt k / Real.sqrt k *
        (eVariationOn W Set.univ).toReal *
          (W.lower * (k : ℝ)) ^ (-s.re) :=
    mul_nonneg
      (mul_nonneg
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg k))
        ENNReal.toReal_nonneg)
      (Real.rpow_nonneg
        (mul_nonneg W.lower_pos.le (by exact_mod_cast (Nat.zero_le k))) _)
  rcases n.eq_zero_or_pos with rfl | hn
  · simpa [doubleTerm] using hnonneg
  by_cases hW : W ((n : ℝ) / k) = 0
  · simpa [doubleTerm, hk.ne', hn.ne', hW] using hnonneg
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hsupport : (n : ℝ) / k ∈ Set.Icc W.lower W.upper := by
    by_contra hnot
    exact hW (W.eq_zero_off_support _ hnot)
  have hlower : W.lower * (k : ℝ) ≤ n :=
    (le_div_iff₀ hkreal).mp hsupport.1
  have hlowerPos : 0 < W.lower * (k : ℝ) := mul_pos W.lower_pos hkreal
  have hpow : (n : ℝ) ^ (-s.re) ≤
      (W.lower * (k : ℝ)) ^ (-s.re) :=
    Real.rpow_le_rpow_of_nonpos hlowerPos hlower (by linarith)
  rw [doubleTerm, if_neg (by omega), norm_mul, norm_mul, norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.sqrt_nonneg k)),
    Complex.norm_natCast_cpow_of_pos hn]
  simp only [neg_re]
  calc
    ArithmeticFunction.vonMangoldt k / Real.sqrt k *
        ‖W ((n : ℝ) / k)‖ * (n : ℝ) ^ (-s.re) ≤
      ArithmeticFunction.vonMangoldt k / Real.sqrt k *
        (eVariationOn W Set.univ).toReal * (n : ℝ) ^ (-s.re) := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left (W.norm_le_totalVariation _)
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg k))
      · positivity
    _ ≤ ArithmeticFunction.vonMangoldt k / Real.sqrt k *
        (eVariationOn W Set.univ).toReal *
          (W.lower * (k : ℝ)) ^ (-s.re) := by
      exact mul_le_mul_of_nonneg_left hpow <|
        mul_nonneg
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg k))
          ENNReal.toReal_nonneg

end CompactBVPrimeWindow
end RHTower

namespace RHTower
namespace CompactBVPrimeWindow

private theorem summable_norm_doubleTerm
    (W : CompactBVPrimeWindow) {s : ℂ} (hs : 3 / 2 < s.re) :
    Summable (fun kn : ℕ × ℕ => ‖W.doubleTerm s kn‖) := by
  rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
  constructor
  · intro k
    rcases k.eq_zero_or_pos with rfl | hk
    · simpa [doubleTerm] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
    · apply summable_of_hasFiniteSupport
      apply Set.Finite.subset (Finset.finite_toSet (range (W.gridCount k + 1)))
      intro n hn
      simp only [Function.mem_support] at hn
      simp only [Finset.mem_coe, Finset.mem_range]
      by_contra hnot
      have hlt : W.gridCount k < n := by omega
      rw [W.doubleTerm_eq_zero_of_gridCount_lt s hk hlt, norm_zero] at hn
      exact hn rfl
  · let sigma : ℝ := s.re
    let z : ℂ := ((sigma - 1 / 2 : ℝ) : ℂ)
    let V : ℝ := (eVariationOn W Set.univ).toReal
    let A : ℝ := V * (W.upper + 2) * W.lower ^ (-sigma)
    have hz : 1 < z.re := by
      dsimp only [z, sigma]
      simp only [ofReal_re]
      linarith
    have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
    have hupper : 0 ≤ W.upper + 2 := by linarith [W.upper_pos]
    have hA0 : 0 ≤ A := by
      dsimp only [A]
      exact mul_nonneg (mul_nonneg hV0 hupper)
        (Real.rpow_nonneg W.lower_pos.le _)
    have hvm : LSeriesSummable
        (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) z :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt hz
    have hmajor : Summable (fun k => A *
        ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) z k‖) :=
      hvm.norm.mul_left A
    apply Summable.of_norm_bounded hmajor
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
    rcases k.eq_zero_or_pos with rfl | hk
    · simp [doubleTerm]
    · have hk0 : k ≠ 0 := Nat.ne_of_gt hk
      have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
      have hcount : (W.gridCount k + 1 : ℕ) ≤
          (W.upper + 2) * (k : ℝ) := by
        have hD := W.gridCount_div_le_upper_add_one (show 1 ≤ k by omega)
        have hbase : (W.gridCount k : ℝ) ≤ (W.upper + 1) * (k : ℝ) := by
          exact (div_le_iff₀ hkreal).mp hD
        norm_num only [Nat.cast_add, Nat.cast_one]
        nlinarith [show (1 : ℝ) ≤ k by exact_mod_cast (show 1 ≤ k by omega)]
      rw [tsum_eq_sum (s := range (W.gridCount k + 1)) (fun n hn => by
        simp only [Finset.mem_range] at hn
        have hlt : W.gridCount k < n := by omega
        rw [W.doubleTerm_eq_zero_of_gridCount_lt s hk hlt, norm_zero])]
      calc
        (∑ n ∈ range (W.gridCount k + 1), ‖W.doubleTerm s (k, n)‖) ≤
            ∑ _n ∈ range (W.gridCount k + 1),
              ArithmeticFunction.vonMangoldt k / Real.sqrt k * V *
                (W.lower * (k : ℝ)) ^ (-sigma) := by
          apply Finset.sum_le_sum
          intro n hn
          simpa only [V, sigma] using W.norm_doubleTerm_le (by linarith : 0 < s.re) hk
        _ = (W.gridCount k + 1 : ℕ) *
              (ArithmeticFunction.vonMangoldt k / Real.sqrt k * V *
                (W.lower * (k : ℝ)) ^ (-sigma)) := by
          rw [sum_const, card_range, nsmul_eq_mul]
        _ ≤ ((W.upper + 2) * (k : ℝ)) *
              (ArithmeticFunction.vonMangoldt k / Real.sqrt k * V *
                (W.lower * (k : ℝ)) ^ (-sigma)) := by
          apply mul_le_mul_of_nonneg_right hcount
          exact mul_nonneg
            (mul_nonneg
              (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg k)) hV0)
            (Real.rpow_nonneg (mul_nonneg W.lower_pos.le hkreal.le) _)
        _ = A * ‖LSeries.term
              (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) z k‖ := by
          rw [LSeries.term_of_ne_zero hk0, norm_div, norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
            Complex.norm_natCast_cpow_of_pos hk, Real.sqrt_eq_rpow]
          simp only [z, ofReal_re]
          rw [Real.mul_rpow W.lower_pos.le hkreal.le]
          dsimp only [A]
          calc
            ((W.upper + 2) * (k : ℝ)) *
                (ArithmeticFunction.vonMangoldt k / (k : ℝ) ^ (1 / 2 : ℝ) * V *
                  (W.lower ^ (-sigma) * (k : ℝ) ^ (-sigma))) =
              (V * (W.upper + 2) * W.lower ^ (-sigma)) *
                (ArithmeticFunction.vonMangoldt k *
                  ((k : ℝ) ^ (1 : ℝ) *
                    ((k : ℝ) ^ (-(1 / 2 : ℝ)) * (k : ℝ) ^ (-sigma)))) := by
              rw [div_eq_mul_inv, ← Real.rpow_neg hkreal.le, Real.rpow_one]
              ring
            _ = (V * (W.upper + 2) * W.lower ^ (-sigma)) *
                (ArithmeticFunction.vonMangoldt k *
                  (k : ℝ) ^ (1 + (-(1 / 2 : ℝ) + -sigma))) := by
              rw [← Real.rpow_add hkreal, ← Real.rpow_add hkreal]
            _ = (V * (W.upper + 2) * W.lower ^ (-sigma)) *
                (ArithmeticFunction.vonMangoldt k /
                  (k : ℝ) ^ (sigma - 1 / 2)) := by
              rw [show 1 + (-(1 / 2 : ℝ) + -sigma) =
                  -(sigma - 1 / 2) by ring,
                Real.rpow_neg hkreal.le]
              ring

/-- The moving-window double series is absolutely summable on its initial half-plane. -/
theorem summable_doubleTerm
    (W : CompactBVPrimeWindow) {s : ℂ} (hs : 3 / 2 < s.re) :
    Summable (W.doubleTerm s) :=
  (W.summable_norm_doubleTerm hs).of_norm

end CompactBVPrimeWindow
end RHTower

namespace RHTower
namespace CompactBVPrimeWindow

/-- Summing the double-series term over the output index gives the finite Mellin kernel. -/
theorem tsum_doubleTerm_right
    (W : CompactBVPrimeWindow) {s : ℂ} {k : ℕ} (hk : 0 < k) :
    ∑' n : ℕ, W.doubleTerm s (k, n) =
      ((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ) *
        W.discreteMellinKernel k s := by
  rw [tsum_eq_sum (s := range (W.gridCount k + 1)) (fun n hn => by
    simp only [Finset.mem_range] at hn
    have hlt : W.gridCount k < n := by omega
    exact W.doubleTerm_eq_zero_of_gridCount_lt s hk hlt)]
  rw [Finset.sum_range_succ']
  simp only [doubleTerm, hk.ne', Nat.add_eq_zero_iff, one_ne_zero, and_false,
    or_false, if_false, Nat.cast_add, Nat.cast_one, zero_div, or_true, if_true, add_zero,
    discreteMellinKernel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end CompactBVPrimeWindow
end RHTower

namespace RHTower
namespace CompactBVPrimeWindow

/-- Summing the double-series term over the prime-power index gives the moving-window coefficient. -/
theorem tsum_doubleTerm_left
    (W : CompactBVPrimeWindow) (s : ℂ) (n : ℕ) :
    ∑' k : ℕ, W.doubleTerm s (k, n) =
      LSeries.term W.weightedPrimeWindow s n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [doubleTerm, LSeries.term]
  rw [LSeries.term_of_ne_zero hn.ne']
  calc
    (∑' k : ℕ, W.doubleTerm s (k, n)) =
        ∑' k : ℕ,
          (((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ) *
            W ((n : ℝ) / k)) * (n : ℂ) ^ (-s) := by
      apply tsum_congr
      intro k
      rcases k.eq_zero_or_pos with rfl | hk
      · simp [doubleTerm]
      · simp only [doubleTerm, hk.ne', hn.ne', or_false, if_false]
    _ = W.weightedPrimeWindow n * (n : ℂ) ^ (-s) := by
      rw [weightedPrimeWindow, tsum_mul_right]
    _ = W.weightedPrimeWindow n / (n : ℂ) ^ s := by
      rw [Complex.cpow_neg]
      rfl

end CompactBVPrimeWindow
end RHTower

namespace RHTower
namespace CompactBVPrimeWindow

set_option maxHeartbeats 500000 in
/-- Absolute convergence justifies reversing the moving-window double series. -/
theorem LSeries_weightedPrimeWindow_eq_kernel_series
    (W : CompactBVPrimeWindow) {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeries W.weightedPrimeWindow s =
      ∑' k : ℕ,
        ((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ) *
          W.discreteMellinKernel k s := by
  have hdouble : Summable
      (Function.uncurry (fun k n => W.doubleTerm s (k, n))) :=
    W.summable_doubleTerm hs
  calc
    LSeries W.weightedPrimeWindow s =
        ∑' n : ℕ, ∑' k : ℕ, W.doubleTerm s (k, n) := by
      apply tsum_congr
      intro n
      exact (W.tsum_doubleTerm_left s n).symm
    _ = ∑' k : ℕ, ∑' n : ℕ, W.doubleTerm s (k, n) :=
      hdouble.tsum_comm
    _ = ∑' k : ℕ,
        ((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ) *
          W.discreteMellinKernel k s := by
      apply tsum_congr
      intro k
      rcases k.eq_zero_or_pos with rfl | hk
      · simp [doubleTerm, discreteMellinKernel, gridCount]
      · exact W.tsum_doubleTerm_right hk

end CompactBVPrimeWindow
end RHTower

namespace RHTower
namespace CompactBVPrimeWindow

private theorem weighted_discreteMellinKernel_eq_main_add_error
    (W : CompactBVPrimeWindow) (k : ℕ) (s : ℂ) :
    ((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ) *
        W.discreteMellinKernel k s =
      W.mellinTransform s *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (s - 1 / 2) k +
        W.errorSummand s k := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp [discreteMellinKernel, errorSummand, gridCount, scaledGridError, gridError,
      gridRiemannSum]
  · have hk0 : k ≠ 0 := Nat.ne_of_gt hk
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
    rw [errorSummand, ← W.mellinError_eq_scaledGridError hk s, mellinError,
      LSeries.term_of_ne_zero hk0]
    have hsqrt : ((Real.sqrt k : ℝ) : ℂ) = (k : ℂ) ^ (1 / 2 : ℂ) := by
      rw [Real.sqrt_eq_rpow]
      simpa using Complex.ofReal_cpow (Nat.cast_nonneg k) (1 / 2 : ℝ)
    rw [ofReal_div, hsqrt]
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
              ((k : ℂ) ^ (1 - s) * W.mellinTransform s) =
          W.mellinTransform s *
            (((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ) /
              (k : ℂ) ^ (s - 1 / 2)) := by
      calc
        (((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ) /
            (k : ℂ) ^ (1 / 2 : ℂ)) *
              ((k : ℂ) ^ (1 - s) * W.mellinTransform s) =
            ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ) *
              ((k : ℂ) ^ (1 - s) / (k : ℂ) ^ (1 / 2 : ℂ)) *
                W.mellinTransform s := by ring
        _ = _ := by rw [hpow]; ring
    rw [hmain]
    ring

/-- The BV quadrature remainder is summable at every point of its right half-plane. -/
theorem summable_errorSummand
    (W : CompactBVPrimeWindow) {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun k : ℕ => W.errorSummand s k) :=
  W.summableLocallyUniformlyOn_errorSummand.summable hs

/-- The honest BV moving-window Dirichlet series is a Mellin-weighted zeta logarithmic derivative
plus its holomorphic quadrature remainder. -/
theorem LSeries_weightedPrimeWindow_eq_zetaLogDeriv
    (W : CompactBVPrimeWindow) {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeries W.weightedPrimeWindow s =
      -W.mellinTransform s * zetaLogDeriv (s - 1 / 2) +
        W.errorSeries s := by
  have hshift : 1 < (s - 1 / 2).re := by
    norm_num [Complex.sub_re] at hs ⊢
    linarith
  have hvm : LSeriesSummable
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s - 1 / 2) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hshift
  have hmain : Summable (fun k =>
      W.mellinTransform s *
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (s - 1 / 2) k) := hvm.mul_left _
  have herr := W.summable_errorSummand (by linarith : 1 / 2 < s.re)
  calc
    LSeries W.weightedPrimeWindow s =
        ∑' k : ℕ,
          ((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ) *
            W.discreteMellinKernel k s :=
      W.LSeries_weightedPrimeWindow_eq_kernel_series hs
    _ = ∑' k : ℕ,
        (W.mellinTransform s *
            LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (s - 1 / 2) k +
          W.errorSummand s k) := by
      apply tsum_congr
      intro k
      exact W.weighted_discreteMellinKernel_eq_main_add_error k s
    _ = (∑' k : ℕ,
          W.mellinTransform s *
            LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (s - 1 / 2) k) +
        ∑' k : ℕ, W.errorSummand s k :=
      hmain.tsum_add herr
    _ = W.mellinTransform s *
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (s - 1 / 2) +
        W.errorSeries s := by
      rw [tsum_mul_left]
      rfl
    _ = -W.mellinTransform s * zetaLogDeriv (s - 1 / 2) +
        W.errorSeries s := by
      rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hshift,
        zetaLogDeriv]
      ring

end CompactBVPrimeWindow
end RHTower

namespace RHTower
namespace CompactBVPrimeWindow

/-- A nonzero moving-prime summand can occur only in the exact multiplicative support band
`n / upper <= k <= n / lower`. -/
theorem prime_index_mem_support_band_of_term_ne_zero
    (W : CompactBVPrimeWindow) {n k : ℕ}
    (hterm : ((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ) *
        W ((n : ℝ) / k) ≠ 0) :
    (n : ℝ) / W.upper ≤ k ∧ (k : ℝ) ≤ (n : ℝ) / W.lower := by
  have hk0 : k ≠ 0 := by
    intro hk
    subst k
    simp at hterm
  have hkreal : (0 : ℝ) < k := by exact_mod_cast (Nat.pos_of_ne_zero hk0)
  have hW : W ((n : ℝ) / k) ≠ 0 := by
    exact fun h => hterm (by rw [h]; simp)
  have hsupp : (n : ℝ) / k ∈ Set.Icc W.lower W.upper := by
    by_contra hnot
    exact hW (W.eq_zero_off_support _ hnot)
  constructor
  · apply (div_le_iff₀ W.upper_pos).2
    exact (div_le_iff₀ hkreal).1 hsupp.2 |>.trans_eq (by ring)
  · apply (le_div_iff₀ W.lower_pos).2
    simpa [mul_comm] using (le_div_iff₀ hkreal).1 hsupp.1

/-- Concrete finite upper cutoff for the moving-prime sum at output index `n`. -/
def primeIndexBound (W : CompactBVPrimeWindow) (n : ℕ) : ℕ :=
  Nat.ceil ((n : ℝ) / W.lower)

private theorem weightedPrimeTerm_eq_zero_of_primeIndexBound_lt
    (W : CompactBVPrimeWindow) {n k : ℕ} (hk : W.primeIndexBound n < k) :
    ((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ) *
      W ((n : ℝ) / k) = 0 := by
  have hkpos : 0 < k := by omega
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hdiv : (n : ℝ) / W.lower < k :=
    (Nat.le_ceil ((n : ℝ) / W.lower)).trans_lt (by exact_mod_cast hk)
  have hnk : (n : ℝ) < W.lower * k := by
    have := (div_lt_iff₀ W.lower_pos).1 hdiv
    nlinarith
  have hratio : (n : ℝ) / k < W.lower := by
    exact (div_lt_iff₀ hkreal).2 (by simpa [mul_comm] using hnk)
  have hoff : (n : ℝ) / k ∉ Set.Icc W.lower W.upper := by
    simp only [Set.mem_Icc, not_and_or]
    exact Or.inl (not_le.mpr hratio)
  rw [W.eq_zero_off_support _ hoff, mul_zero]

/-- The moving-prime statistic is literally a finite sum; no convergence convention enters its
arithmetic definition. -/
theorem weightedPrimeWindow_eq_finite_sum
    (W : CompactBVPrimeWindow) (n : ℕ) :
    W.weightedPrimeWindow n =
      ∑ k ∈ Finset.range (W.primeIndexBound n + 1),
        ((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ) *
          W ((n : ℝ) / k) := by
  rw [weightedPrimeWindow]
  apply tsum_eq_sum
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  exact W.weightedPrimeTerm_eq_zero_of_primeIndexBound_lt (by omega)

end CompactBVPrimeWindow
end RHTower
