import GaloisForLFunctions.RHTower.XiMobiusSchurValuationIntertwiner
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Arithmetic Schur renormalization

The one-step Gamma--valuation identity extends to a cofinal Schur algorithm.  For arbitrary
disk nodes, every finite valuation prefix leaves an exact shifted Szego residual; the residual
is strictly positive at every finite depth and vanishes only cofinally.  A fixed-point rigidity
law and weighted-Vandermonde theorem make this realization minimal.

At reciprocal-prime nodes the abstract boundary coordinate is the corrected Gamma conductor
cross already identified by `XiTransverseGammaValuationCoherence`.  Thus repeated Gamma Schur
elimination is exact prime-power valuation translation, not a scalar capacity approximation.

This file proves the universal and arithmetic source laws.  It does not assert the open
nonexpansive transport from this source colligation to the Xi boundary-leakage system.
-/

namespace RHTower

noncomputable section

open scoped BigOperators ENNReal NNReal
open Matrix

/-! ## Universal Schur system -/

/-- Real Hardy space carrying the completed geometric Schur coordinates. -/
abbrev PrimeHardy := lp (fun _ : ℕ => ℝ) 2

theorem memlp_two_geometric {q : ℝ} (hq : |q| < 1) :
    Memℓp (fun m : ℕ => q ^ m) 2 := by
  apply memℓp_gen
  have hs : Summable (fun n : ℕ => (|q| ^ 2) ^ n) :=
    summable_geometric_of_norm_lt_one (show ‖|q| ^ 2‖ < 1 by
      rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (abs_nonneg q)]
      nlinarith [abs_nonneg q])
  refine hs.congr (fun n => ?_)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, abs_pow]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- Completed geometric Schur coordinate vector at disk node `q`. -/
def hardyKernel (q : ℝ) (hq : |q| < 1) : PrimeHardy :=
  ⟨fun m => q ^ m, memlp_two_geometric hq⟩

@[simp] theorem hardyKernel_apply (q : ℝ) (hq : |q| < 1) (m : ℕ) :
    hardyKernel q hq m = q ^ m := rfl

/-- Inner product of two real Hardy coherent kernels is the Szegő kernel. -/
theorem inner_hardyKernel (q r : ℝ) (hq : |q| < 1) (hr : |r| < 1) :
    inner ℝ (hardyKernel q hq) (hardyKernel r hr) =
      1 / (1 - q * r) := by
  rw [lp.inner_eq_tsum]
  simp only [RCLike.inner_apply, conj_trivial, hardyKernel_apply]
  have hprod : |q * r| < 1 := by
    rw [abs_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (abs_nonneg q) hq hr.le
  calc
    (∑' x : ℕ, r ^ x * q ^ x) = ∑' x : ℕ, (q * r) ^ x := by
      apply tsum_congr
      intro x
      rw [mul_pow]
      ring
    _ = (1 - q * r)⁻¹ := by
      rw [tsum_geometric_of_norm_lt_one]
      simpa [Real.norm_eq_abs] using hprod
    _ = 1 / (1 - q * r) := by ring

/-- Depth-`n` coordinate of a geometric Schur system with disk node `q` and boundary amplitude
`a`. -/
def arithmeticSchurValuationCoordinate (q a : ℝ) (n : ℕ) : ℝ :=
  a * q ^ n

/-- The unique kernel whose removal of the boundary coordinate reproduces itself after diagonal
translation by the two disk nodes. -/
def arithmeticSchurKernel (q r a b : ℝ) : ℝ :=
  a * b / (1 - q * r)

/-- Gram kernel of the first `N` translated boundary coordinates. -/
def arithmeticSchurPrefixKernel (N : ℕ) (q r a b : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,
    arithmeticSchurValuationCoordinate q a n *
      arithmeticSchurValuationCoordinate r b n

/-- **Cofinal Schur exhaustion.** Every finite prefix leaves exactly the original kernel
translated by `N` valuation depths. -/
theorem arithmeticSchurKernel_sub_prefix_eq_residual
    (N : ℕ) (q r a b : ℝ) (hqr : 1 - q * r ≠ 0) :
    arithmeticSchurKernel q r a b -
        arithmeticSchurPrefixKernel N q r a b =
      (q * r) ^ N * arithmeticSchurKernel q r a b := by
  induction N with
  | zero =>
      simp [arithmeticSchurPrefixKernel]
  | succ N ih =>
      rw [arithmeticSchurPrefixKernel, Finset.sum_range_succ]
      change arithmeticSchurKernel q r a b -
          (arithmeticSchurPrefixKernel N q r a b +
            arithmeticSchurValuationCoordinate q a N *
              arithmeticSchurValuationCoordinate r b N) = _
      rw [sub_add_eq_sub_sub, ih]
      simp only [arithmeticSchurValuationCoordinate, arithmeticSchurKernel,
        mul_pow, pow_succ]
      field_simp [hqr]
      ring

/-- One Schur step removes the current boundary coordinate and advances the residual by one
valuation depth. -/
theorem arithmeticSchurResidual_sub_coordinate_eq_succ
    (N : ℕ) (q r a b : ℝ) (hqr : 1 - q * r ≠ 0) :
    (q * r) ^ N * arithmeticSchurKernel q r a b -
        arithmeticSchurValuationCoordinate q a N *
          arithmeticSchurValuationCoordinate r b N =
      (q * r) ^ (N + 1) * arithmeticSchurKernel q r a b := by
  simp only [arithmeticSchurValuationCoordinate, arithmeticSchurKernel,
    mul_pow, pow_succ]
  field_simp [hqr]
  ring

/-- The Schur fixed-point equation uniquely determines the Szego kernel. -/
theorem arithmeticSchurKernel_eq_of_fixedPoint
    (q r a b L : ℝ) (hqr : 1 - q * r ≠ 0)
    (hL : L - a * b = q * r * L) :
    L = arithmeticSchurKernel q r a b := by
  rw [arithmeticSchurKernel, eq_div_iff hqr]
  linarith

/-- Every diagonal residual is strictly positive at every finite depth.  Cofinal exhaustion
cannot be replaced by any finite valuation cutoff. -/
theorem arithmeticSchur_self_residual_pos
    (N : ℕ) {q a : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (ha : 0 < a) :
    0 < (q * q) ^ N * arithmeticSchurKernel q q a a := by
  have hqq0 : 0 < q * q := mul_pos hq0 hq0
  have hqq1 : q * q < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left hq0.le hq1 hq1.le
  have hden : 0 < 1 - q * q := sub_pos.mpr hqq1
  exact mul_pos (pow_pos hqq0 N) (div_pos (mul_pos ha ha) hden)

/-- The cofinal residual vanishes pointwise. -/
theorem tendsto_arithmeticSchur_residual_atTop
    {q r a b : ℝ} (hqr0 : 0 ≤ q * r) (hqr1 : q * r < 1) :
    Filter.Tendsto
      (fun N : ℕ => (q * r) ^ N * arithmeticSchurKernel q r a b)
      Filter.atTop (nhds 0) := by
  simpa using
    (tendsto_pow_atTop_nhds_zero_of_lt_one hqr0 hqr1).mul_const
      (arithmeticSchurKernel q r a b)

/-! ## Minimality -/

/-- Finite observation matrix of translated boundary coordinates. -/
def arithmeticSchurSamplingMatrix
    {N : ℕ} (q a : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun n j => arithmeticSchurValuationCoordinate (q j) (a j) n

/-- The translated-coordinate matrix is a weighted Vandermonde matrix. -/
theorem arithmeticSchurSamplingMatrix_factorization
    {N : ℕ} (q a : Fin N → ℝ) :
    arithmeticSchurSamplingMatrix q a =
      (Matrix.vandermonde q)ᵀ * Matrix.diagonal a := by
  classical
  ext n j
  rw [Matrix.mul_diagonal]
  simp [arithmeticSchurSamplingMatrix, arithmeticSchurValuationCoordinate,
    Matrix.vandermonde]
  ring

/-- Distinct disk nodes and nonzero boundary coordinates make the cofinal Schur realization
minimal on every finite marked packet. -/
theorem arithmeticSchurSamplingMatrix_det_ne_zero
    {N : ℕ} {q a : Fin N → ℝ} (hq : Function.Injective q)
    (ha : ∀ j, a j ≠ 0) :
    (arithmeticSchurSamplingMatrix q a).det ≠ 0 := by
  rw [arithmeticSchurSamplingMatrix_factorization, Matrix.det_mul,
    Matrix.det_transpose]
  apply mul_ne_zero
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr hq
  · rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    exact fun j _ => ha j

/-! ## Reciprocal-prime/Gamma specialization -/

/-- Arithmetic boundary amplitude selected by the corrected Gamma conductor. -/
def arithmeticPrimeSchurBoundaryAmplitude (p : Nat.Primes) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode 1 p
  Real.sqrt q * (1 - q)

/-- The universal translated coordinate is the actual half-shifted prime-valuation coordinate. -/
theorem arithmeticSchurValuationCoordinate_prime_eq
    (p : Nat.Primes) (n : ℕ) :
    arithmeticSchurValuationCoordinate
        (xiTransversePrimeApertureDiskNode 1 p)
        (arithmeticPrimeSchurBoundaryAmplitude p) n =
      xiTransversePrimeHalfShiftedValuationCoordinate p n := by
  simp only [arithmeticSchurValuationCoordinate,
    arithmeticPrimeSchurBoundaryAmplitude,
    xiTransversePrimeHalfShiftedValuationCoordinate,
    xiTransversePrimeValuationIncrement]
  ring

/-- The universal Schur kernel specializes to the completed Gamma--valuation Szego kernel. -/
theorem arithmeticSchurKernel_prime_eq (p r : Nat.Primes) :
    arithmeticSchurKernel
        (xiTransversePrimeApertureDiskNode 1 p)
        (xiTransversePrimeApertureDiskNode 1 r)
        (arithmeticPrimeSchurBoundaryAmplitude p)
        (arithmeticPrimeSchurBoundaryAmplitude r) =
      xiTransverseGammaValuationSzegoKernel p r := by
  simp only [arithmeticSchurKernel, arithmeticPrimeSchurBoundaryAmplitude,
    xiTransverseGammaValuationSzegoKernel]
  ring

/-- **Arithmetic Schur-renormalization law.** Repeated transported-Gamma elimination removes the
first `N` prime-power valuation coordinates and leaves precisely the `N`-step translated
Gamma--valuation kernel. -/
theorem xiTransverseGammaValuationSzegoKernel_sub_prefix_eq_residual
    (N : ℕ) (p r : Nat.Primes) :
    xiTransverseGammaValuationSzegoKernel p r -
        (∑ n ∈ Finset.range N,
          xiTransversePrimeHalfShiftedValuationCoordinate p n *
            xiTransversePrimeHalfShiftedValuationCoordinate r n) =
      (xiTransversePrimeApertureDiskNode 1 p *
          xiTransversePrimeApertureDiskNode 1 r) ^ N *
        xiTransverseGammaValuationSzegoKernel p r := by
  have hp0 : 0 ≤ xiTransversePrimeApertureDiskNode 1 p :=
    (xiTransversePrimeApertureDiskNode_pos 1 p).le
  have hr0 : 0 ≤ xiTransversePrimeApertureDiskNode 1 r :=
    (xiTransversePrimeApertureDiskNode_pos 1 r).le
  have hp1 : xiTransversePrimeApertureDiskNode 1 p < 1 :=
    xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hr1 : xiTransversePrimeApertureDiskNode 1 r < 1 :=
    xiTransversePrimeApertureDiskNode_lt_one (by norm_num) r
  have hprod : xiTransversePrimeApertureDiskNode 1 p *
      xiTransversePrimeApertureDiskNode 1 r < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left hp0 hp1 hr1.le
  have hden : 1 - xiTransversePrimeApertureDiskNode 1 p *
      xiTransversePrimeApertureDiskNode 1 r ≠ 0 :=
    (sub_pos.mpr hprod).ne'
  simpa only [arithmeticSchurKernel_prime_eq,
    arithmeticSchurValuationCoordinate_prime_eq,
    arithmeticSchurPrefixKernel] using
    arithmeticSchurKernel_sub_prefix_eq_residual N
      (xiTransversePrimeApertureDiskNode 1 p)
      (xiTransversePrimeApertureDiskNode 1 r)
      (arithmeticPrimeSchurBoundaryAmplitude p)
      (arithmeticPrimeSchurBoundaryAmplitude r) hden

/-- Every finite arithmetic Schur chain leaves a strictly positive diagonal residual. -/
theorem xiTransverseGammaValuationSzegoKernel_sub_prefix_self_pos
    (N : ℕ) (p : Nat.Primes) :
    0 < xiTransverseGammaValuationSzegoKernel p p -
      (∑ n ∈ Finset.range N,
        xiTransversePrimeHalfShiftedValuationCoordinate p n ^ 2) := by
  rw [show (∑ n ∈ Finset.range N,
      xiTransversePrimeHalfShiftedValuationCoordinate p n ^ 2) =
      ∑ n ∈ Finset.range N,
        xiTransversePrimeHalfShiftedValuationCoordinate p n *
          xiTransversePrimeHalfShiftedValuationCoordinate p n by
    apply Finset.sum_congr rfl
    intro n hn
    ring]
  rw [xiTransverseGammaValuationSzegoKernel_sub_prefix_eq_residual]
  rw [← arithmeticSchurKernel_prime_eq]
  exact arithmeticSchur_self_residual_pos N
    (xiTransversePrimeApertureDiskNode_pos 1 p)
    (xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p)
    (by
      exact mul_pos
        (Real.sqrt_pos.2 (xiTransversePrimeApertureDiskNode_pos 1 p))
        (sub_pos.mpr
          (xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p)))

/-- The arithmetic Schur residual vanishes only in the cofinal valuation limit. -/
theorem tendsto_xiTransverseGammaValuationSzegoKernel_residual_atTop
    (p r : Nat.Primes) :
    Filter.Tendsto
      (fun N : ℕ =>
        (xiTransversePrimeApertureDiskNode 1 p *
            xiTransversePrimeApertureDiskNode 1 r) ^ N *
          xiTransverseGammaValuationSzegoKernel p r)
      Filter.atTop (nhds 0) := by
  have hp0 : 0 ≤ xiTransversePrimeApertureDiskNode 1 p :=
    (xiTransversePrimeApertureDiskNode_pos 1 p).le
  have hr0 : 0 ≤ xiTransversePrimeApertureDiskNode 1 r :=
    (xiTransversePrimeApertureDiskNode_pos 1 r).le
  have hp1 : xiTransversePrimeApertureDiskNode 1 p < 1 :=
    xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hr1 : xiTransversePrimeApertureDiskNode 1 r < 1 :=
    xiTransversePrimeApertureDiskNode_lt_one (by norm_num) r
  exact tendsto_arithmeticSchur_residual_atTop
    (mul_nonneg hp0 hr0)
    (mul_lt_one_of_nonneg_of_lt_one_left hp0 hp1 hr1.le)

/-! ## Intrinsic Fisher whitening -/

/-- The globally summable Mobius difference kernel is the exact diagonal Fisher congruence of
the coherent Gamma--valuation kernel. -/
theorem xiMobiusPrimeSchurDifferenceKernel_eq_fisherCongruence
    (p r : Nat.Primes) :
    xiMobiusPrimeSchurDifferenceKernel p r =
      xiMobiusPrimeSchurValuationDamping p *
        xiMobiusPrimeSchurValuationDamping r *
          xiTransverseGammaValuationSzegoKernel p r := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let s := xiTransversePrimeApertureDiskNode 1 r
  have hq0 : 0 ≤ q := (xiTransversePrimeApertureDiskNode_pos 1 p).le
  have hs0 : 0 ≤ s := (xiTransversePrimeApertureDiskNode_pos 1 r).le
  have hq1 : q < 1 :=
    xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hs1 : s < 1 :=
    xiTransversePrimeApertureDiskNode_lt_one (by norm_num) r
  have hqplus : 1 + q ≠ 0 := by linarith
  have hsplus : 1 + s ≠ 0 := by linarith
  have hqsminus : 1 - q * s ≠ 0 := by
    have : q * s < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_left hq0 hq1 hs1.le
    linarith
  simp only [xiMobiusPrimeSchurDifferenceKernel,
    xiMobiusPrimeSchurValuationDamping,
    xiTransverseGammaValuationSzegoKernel]
  rw [show xiTransversePrimeApertureDiskNode 1 p = q by rfl,
    show xiTransversePrimeApertureDiskNode 1 r = s by rfl]
  field_simp [hqplus, hsplus, hqsminus]
  rw [Real.sq_sqrt hq0, Real.sq_sqrt hs0]
  ring

/-- **Intrinsic Fisher-whitening isometry.** On every finite source packet, the Mobius RKHS
quadratic form is exactly the Gamma--valuation form after diagonal Fisher damping. Hence inverse
whitening, although unbounded in ambient prime `ell2`, is isometric after quotienting by the
source Gram nullspaces and extends uniquely to the intrinsic Hilbert completions. -/
theorem xiMobiusPrimeSchurDifference_quadratic_eq_gamma_damped
    {I : Type*} [Fintype I] (p : I → Nat.Primes) (u : I → ℝ) :
    (∑ i, ∑ j,
      xiMobiusPrimeSchurDifferenceKernel (p i) (p j) * u i * u j) =
    ∑ i, ∑ j,
      xiTransverseGammaValuationSzegoKernel (p i) (p j) *
        (xiMobiusPrimeSchurValuationDamping (p i) * u i) *
        (xiMobiusPrimeSchurValuationDamping (p j) * u j) := by
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [xiMobiusPrimeSchurDifferenceKernel_eq_fisherCongruence]
  ring

/-- Fisher damping commutes with valuation translation. The intrinsic source isometry therefore
intertwines the complete arithmetic Schur flow, not merely its depth-zero Gram. -/
theorem xiMobiusPrimeSchurForwardDifference_succ
    (p : Nat.Primes) (n : ℕ) :
    xiMobiusPrimeSchurForwardDifference p (n + 1) =
      xiTransversePrimeApertureDiskNode 1 p *
        xiMobiusPrimeSchurForwardDifference p n := by
  rw [xiMobiusPrimeSchurForwardDifference_eq_dampedValuation,
    xiMobiusPrimeSchurForwardDifference_eq_dampedValuation,
    xiTransversePrimeHalfShiftedValuationCoordinate_succ]
  ring

end

end RHTower
