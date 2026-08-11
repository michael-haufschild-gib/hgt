import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryAdaptiveArithmeticSourceLaw

/-!
# Pointwise positivity fails maximally for the actual adaptive mixed Gamma kernel

The mixed factorial carrier can change sign, but that alone does not prove that its positive
Gamma average changes sign.  This module closes that gap for the literal adaptive arithmetic
source kernel.

For a linear amplitude `A_a(X) = 1 - aX`, the common source kernel is exactly

`x^(-(1/2+w)) / (96 w^9) *
  (24 w^4 B₂(z) - 12 a w² B₃(z) + a² B₄(z))`, `z = w log x`.

On the physical ray `x ≥ 1`, its discriminant is controlled by

`3 B₃(z)² - 2 B₂(z) B₄(z)
  = z⁶ + 10z⁵ + 42z⁴ + 90z³ + 105z² + 90z + 45 > 0`.

Consequently every physical source point admits a linear amplitude for which the actual Gamma
kernel is strictly negative.  A rational fixed witness is also given at `x = exp (1 / w)`.
Thus neither positivity of unmixed reverse-Bessel kernels nor positivity of Gamma density can
prove source domination.  Any valid sign theorem must retain actual null-flag admission or compare
the signed rational--Gamma and von Mangoldt formations after aggregation.
-/

open Complex Matrix MeasureTheory Set Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Complete one-parameter family of linear amplitudes used to classify the common source kernel. -/
def xiShiftedAdaptiveLinearAmplitude (a : ℝ) : Polynomial ℝ :=
  1 - C a * X

private theorem linearSquareExpansion (a : ℝ) :
    xiShiftedAdaptiveLinearAmplitude a ^ 2 =
      C 1 + C (-2 * a) * X + C (a ^ 2) * X ^ 2 := by
  norm_num [xiShiftedAdaptiveLinearAmplitude]
  ring_nf
  rw [← Polynomial.C_ofNat (R := ℝ) 2]

theorem xiShiftedAdaptiveLinearAmplitude_natDegree
    {a : ℝ} (ha : a ≠ 0) :
    (xiShiftedAdaptiveLinearAmplitude a).natDegree = 1 := by
  rw [show xiShiftedAdaptiveLinearAmplitude a = C (-a) * X + C 1 by
    simp [xiShiftedAdaptiveLinearAmplitude]
    ring_nf]
  exact Polynomial.natDegree_linear (neg_ne_zero.mpr ha)

theorem xiShiftedAdaptiveLinearAmplitude_sq_natDegree
    {a : ℝ} (ha : a ≠ 0) :
    (xiShiftedAdaptiveLinearAmplitude a ^ 2).natDegree = 2 := by
  rw [Polynomial.natDegree_pow, xiShiftedAdaptiveLinearAmplitude_natDegree ha]

theorem xiShiftedAdaptiveLinearAmplitude_sq_coeff_zero (a : ℝ) :
    (xiShiftedAdaptiveLinearAmplitude a ^ 2).coeff 0 = 1 := by
  rw [linearSquareExpansion]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_X_pow]
  norm_num

theorem xiShiftedAdaptiveLinearAmplitude_sq_coeff_one (a : ℝ) :
    (xiShiftedAdaptiveLinearAmplitude a ^ 2).coeff 1 = -2 * a := by
  rw [linearSquareExpansion]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_X_pow]
  norm_num

theorem xiShiftedAdaptiveLinearAmplitude_sq_coeff_two (a : ℝ) :
    (xiShiftedAdaptiveLinearAmplitude a ^ 2).coeff 2 = a ^ 2 := by
  rw [linearSquareExpansion]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_X_pow]
  norm_num

/-- **Exact linear-amplitude classification.** The literal adaptive Gamma kernel is one quadratic
in the linear-amplitude slope.  This is after the positive Gamma average, not merely an identity
for the mixed factorial integrand. -/
theorem xiShiftedAdaptiveMixedGammaKernel_linearAmplitude_eq
    {w a x : ℝ} (hw : 0 < w) (ha : a ≠ 0) :
    xiShiftedAdaptiveMixedGammaKernel w (xiShiftedAdaptiveLinearAmplitude a) x =
      x ^ (-(1 / 2 + w)) / (96 * w ^ 9) *
        (24 * w ^ 4 * reverseBesselPoly 2 (w * Real.log x) -
          12 * a * w ^ 2 * reverseBesselPoly 3 (w * Real.log x) +
          a ^ 2 * reverseBesselPoly 4 (w * Real.log x)) := by
  rw [← xiShiftedHankelBoundaryRadialKernel_adaptiveOddPacket_eq_mixedGammaKernel
    (ne_of_gt hw)]
  have hdeg := xiShiftedAdaptiveLinearAmplitude_sq_natDegree ha
  simp only [xiShiftedHankelBoundaryRadialKernel]
  have hsize : (xiShiftedAdaptiveLinearAmplitude a ^ 2).natDegree + 1 = 3 := by
    omega
  let e : Fin ((xiShiftedAdaptiveLinearAmplitude a ^ 2).natDegree + 1) ≃ Fin 3 :=
    finCongr hsize
  let f : Fin ((xiShiftedAdaptiveLinearAmplitude a ^ 2).natDegree + 1) → ℝ :=
    fun j =>
      xiShiftedBoundaryAdaptiveMidpointCoefficients 1
            (xiShiftedOddCrossingCoefficientPacket
              (xiShiftedAdaptiveLinearAmplitude a)) j *
          radialBesselKernel (2 + (j : ℕ)) (1 / 2 + w) x /
            completedSourceMomentScale (2 + (j : ℕ)) w
  change (∑ j, f j) = _
  have hsum : (∑ j, f j) = ∑ k : Fin 3, f (e.symm k) := by
    exact Fintype.sum_equiv e f (fun k => f (e.symm k))
      (fun j => by simp [e])
  rw [hsum]
  let j0 : Fin ((xiShiftedAdaptiveLinearAmplitude a ^ 2).natDegree + 1) :=
    ⟨0, by omega⟩
  let j1 : Fin ((xiShiftedAdaptiveLinearAmplitude a ^ 2).natDegree + 1) :=
    ⟨1, by omega⟩
  let j2 : Fin ((xiShiftedAdaptiveLinearAmplitude a ^ 2).natDegree + 1) :=
    ⟨2, by omega⟩
  have he0 : e.symm (0 : Fin 3) = j0 := Fin.ext (by simp [e, j0])
  have he1 : e.symm (1 : Fin 3) = j1 := Fin.ext (by simp [e, j1])
  have he2 : e.symm (2 : Fin 3) = j2 := Fin.ext (by simp [e, j2])
  rw [show (∑ k : Fin 3, f (e.symm k)) =
      f (e.symm 0) + f (e.symm 1) + f (e.symm 2) by
    simp [Fin.sum_univ_succ]
    ring_nf]
  rw [he0, he1, he2]
  simp only [f, j0, j1, j2]
  have hpacket
      (j : Fin ((xiShiftedAdaptiveLinearAmplitude a ^ 2).natDegree + 1)) :
      xiShiftedOddCrossingCoefficientPacket (xiShiftedAdaptiveLinearAmplitude a) j =
        (xiShiftedAdaptiveLinearAmplitude a ^ 2).coeff (j : ℕ) := by
    rfl
  simp only [xiShiftedBoundaryAdaptiveMidpointCoefficients, hpacket]
  rw [xiShiftedAdaptiveLinearAmplitude_sq_coeff_zero,
    xiShiftedAdaptiveLinearAmplitude_sq_coeff_one,
    xiShiftedAdaptiveLinearAmplitude_sq_coeff_two]
  norm_num [completedSourceMomentScale]
  simp_rw [radialBesselKernel_half_add_eq_reverseBesselPoly]
  field_simp [ne_of_gt hw]
  ring_nf

/-- Reverse-Bessel discriminant controlling sign of the complete linear-amplitude family. -/
def xiShiftedAdaptiveLinearKernelDiscriminant (z : ℝ) : ℝ :=
  3 * reverseBesselPoly 3 z ^ 2 -
    2 * reverseBesselPoly 2 z * reverseBesselPoly 4 z

/-- The discriminant is a polynomial with strictly positive coefficients. -/
theorem xiShiftedAdaptiveLinearKernelDiscriminant_eq (z : ℝ) :
    xiShiftedAdaptiveLinearKernelDiscriminant z =
      z ^ 6 + 10 * z ^ 5 + 42 * z ^ 4 + 90 * z ^ 3 +
        105 * z ^ 2 + 90 * z + 45 := by
  norm_num [xiShiftedAdaptiveLinearKernelDiscriminant, reverseBesselPoly,
    Finset.sum_range_succ, squaredRadialJetWeight]
  ring_nf

theorem xiShiftedAdaptiveLinearKernelDiscriminant_pos
    {z : ℝ} (hz : 0 ≤ z) :
    0 < xiShiftedAdaptiveLinearKernelDiscriminant z := by
  rw [xiShiftedAdaptiveLinearKernelDiscriminant_eq]
  positivity

/-! ## Lorentz signature on the full affine-amplitude plane -/

/-- Real affine amplitudes.  The monic positive-root sector is `b = -r`, `c = 1`. -/
def xiShiftedAdaptiveAffineAmplitude (b c : ℝ) : Polynomial ℝ :=
  C b + C c * X

private theorem affineSquareExpansion (b c : ℝ) :
    xiShiftedAdaptiveAffineAmplitude b c ^ 2 =
      C (b ^ 2) + C (2 * b * c) * X + C (c ^ 2) * X ^ 2 := by
  norm_num [xiShiftedAdaptiveAffineAmplitude]
  ring_nf
  rw [← Polynomial.C_ofNat (R := ℝ) 2]

theorem xiShiftedAdaptiveAffineAmplitude_natDegree
    {b c : ℝ} (hc : c ≠ 0) :
    (xiShiftedAdaptiveAffineAmplitude b c).natDegree = 1 := by
  rw [show xiShiftedAdaptiveAffineAmplitude b c = C c * X + C b by
    simp [xiShiftedAdaptiveAffineAmplitude]
    ring_nf]
  exact Polynomial.natDegree_linear hc

theorem xiShiftedAdaptiveAffineAmplitude_sq_natDegree
    {b c : ℝ} (hc : c ≠ 0) :
    (xiShiftedAdaptiveAffineAmplitude b c ^ 2).natDegree = 2 := by
  rw [Polynomial.natDegree_pow, xiShiftedAdaptiveAffineAmplitude_natDegree hc]

theorem xiShiftedAdaptiveAffineAmplitude_sq_coeff_zero (b c : ℝ) :
    (xiShiftedAdaptiveAffineAmplitude b c ^ 2).coeff 0 = b ^ 2 := by
  rw [affineSquareExpansion]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_X_pow]
  norm_num

theorem xiShiftedAdaptiveAffineAmplitude_sq_coeff_one (b c : ℝ) :
    (xiShiftedAdaptiveAffineAmplitude b c ^ 2).coeff 1 = 2 * b * c := by
  rw [affineSquareExpansion]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_X_pow]
  norm_num

theorem xiShiftedAdaptiveAffineAmplitude_sq_coeff_two (b c : ℝ) :
    (xiShiftedAdaptiveAffineAmplitude b c ^ 2).coeff 2 = c ^ 2 := by
  rw [affineSquareExpansion]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_X_pow]
  norm_num

/-- **Exact affine-amplitude law.**  After the positive Gamma average, the literal common source
kernel is the binary quadratic form displayed here. -/
theorem xiShiftedAdaptiveMixedGammaKernel_affineAmplitude_eq
    {w b c x : ℝ} (hw : 0 < w) (hc : c ≠ 0) :
    xiShiftedAdaptiveMixedGammaKernel w (xiShiftedAdaptiveAffineAmplitude b c) x =
      x ^ (-(1 / 2 + w)) / (96 * w ^ 9) *
        (24 * b ^ 2 * w ^ 4 * reverseBesselPoly 2 (w * Real.log x) +
          12 * b * c * w ^ 2 * reverseBesselPoly 3 (w * Real.log x) +
          c ^ 2 * reverseBesselPoly 4 (w * Real.log x)) := by
  rw [← xiShiftedHankelBoundaryRadialKernel_adaptiveOddPacket_eq_mixedGammaKernel
    (ne_of_gt hw)]
  have hdeg := xiShiftedAdaptiveAffineAmplitude_sq_natDegree (b := b) hc
  simp only [xiShiftedHankelBoundaryRadialKernel]
  have hsize : (xiShiftedAdaptiveAffineAmplitude b c ^ 2).natDegree + 1 = 3 := by
    omega
  let e : Fin ((xiShiftedAdaptiveAffineAmplitude b c ^ 2).natDegree + 1) ≃ Fin 3 :=
    finCongr hsize
  let f : Fin ((xiShiftedAdaptiveAffineAmplitude b c ^ 2).natDegree + 1) → ℝ :=
    fun j =>
      xiShiftedBoundaryAdaptiveMidpointCoefficients 1
            (xiShiftedOddCrossingCoefficientPacket
              (xiShiftedAdaptiveAffineAmplitude b c)) j *
          radialBesselKernel (2 + (j : ℕ)) (1 / 2 + w) x /
            completedSourceMomentScale (2 + (j : ℕ)) w
  change (∑ j, f j) = _
  have hsum : (∑ j, f j) = ∑ k : Fin 3, f (e.symm k) := by
    exact Fintype.sum_equiv e f (fun k => f (e.symm k))
      (fun j => by simp [e])
  rw [hsum]
  let j0 : Fin ((xiShiftedAdaptiveAffineAmplitude b c ^ 2).natDegree + 1) :=
    ⟨0, by omega⟩
  let j1 : Fin ((xiShiftedAdaptiveAffineAmplitude b c ^ 2).natDegree + 1) :=
    ⟨1, by omega⟩
  let j2 : Fin ((xiShiftedAdaptiveAffineAmplitude b c ^ 2).natDegree + 1) :=
    ⟨2, by omega⟩
  have he0 : e.symm (0 : Fin 3) = j0 := Fin.ext (by simp [e, j0])
  have he1 : e.symm (1 : Fin 3) = j1 := Fin.ext (by simp [e, j1])
  have he2 : e.symm (2 : Fin 3) = j2 := Fin.ext (by simp [e, j2])
  rw [show (∑ k : Fin 3, f (e.symm k)) =
      f (e.symm 0) + f (e.symm 1) + f (e.symm 2) by
    simp [Fin.sum_univ_succ]
    ring_nf]
  rw [he0, he1, he2]
  simp only [f, j0, j1, j2]
  have hpacket
      (j : Fin ((xiShiftedAdaptiveAffineAmplitude b c ^ 2).natDegree + 1)) :
      xiShiftedOddCrossingCoefficientPacket (xiShiftedAdaptiveAffineAmplitude b c) j =
        (xiShiftedAdaptiveAffineAmplitude b c ^ 2).coeff (j : ℕ) := by
    rfl
  simp only [xiShiftedBoundaryAdaptiveMidpointCoefficients, hpacket]
  rw [xiShiftedAdaptiveAffineAmplitude_sq_coeff_zero,
    xiShiftedAdaptiveAffineAmplitude_sq_coeff_one,
    xiShiftedAdaptiveAffineAmplitude_sq_coeff_two]
  norm_num [completedSourceMomentScale]
  simp_rw [radialBesselKernel_half_add_eq_reverseBesselPoly]
  field_simp [ne_of_gt hw]
  ring_nf

/-- Determinant of the symmetric affine-kernel Gram matrix. -/
def xiShiftedAdaptiveAffineKernelGramDeterminant (w z : ℝ) : ℝ :=
  (24 * w ^ 4 * reverseBesselPoly 2 z) * reverseBesselPoly 4 z -
    (6 * w ^ 2 * reverseBesselPoly 3 z) ^ 2

/-- **Lorentz determinant identity.**  The full affine-amplitude plane has a nondegenerate
indefinite kernel form at every physical source coordinate. -/
theorem xiShiftedAdaptiveAffineKernelGramDeterminant_eq (w z : ℝ) :
    xiShiftedAdaptiveAffineKernelGramDeterminant w z =
      -12 * w ^ 4 * xiShiftedAdaptiveLinearKernelDiscriminant z := by
  unfold xiShiftedAdaptiveAffineKernelGramDeterminant
    xiShiftedAdaptiveLinearKernelDiscriminant
  ring

theorem xiShiftedAdaptiveAffineKernelGramDeterminant_neg
    {w z : ℝ} (hw : 0 < w) (hz : 0 ≤ z) :
    xiShiftedAdaptiveAffineKernelGramDeterminant w z < 0 := by
  rw [xiShiftedAdaptiveAffineKernelGramDeterminant_eq]
  have hdisc := xiShiftedAdaptiveLinearKernelDiscriminant_pos hz
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (by norm_num) (pow_pos hw 4)) hdisc

/-- Positive-root vertex of the kernel quadratic restricted to monic amplitudes `X-r`. -/
def xiShiftedAdaptiveAffineMonicMinimizer (w x : ℝ) : ℝ :=
  reverseBesselPoly 3 (w * Real.log x) /
    (4 * w ^ 2 * reverseBesselPoly 2 (w * Real.log x))

theorem xiShiftedAdaptiveAffineMonicMinimizer_pos
    {w x : ℝ} (hw : 0 < w) (hx : 1 ≤ x) :
    0 < xiShiftedAdaptiveAffineMonicMinimizer w x := by
  have hz : 0 ≤ w * Real.log x := mul_nonneg hw.le (Real.log_nonneg hx)
  unfold xiShiftedAdaptiveAffineMonicMinimizer
  exact div_pos (reverseBesselPoly_pos 3 hz)
    (mul_pos (by positivity) (reverseBesselPoly_pos 2 hz))

/-- Exact negative value at the positive-root monic vertex. -/
theorem xiShiftedAdaptiveMixedGammaKernel_affineMonicMinimizer_eq
    {w x : ℝ} (hw : 0 < w) (hx : 1 ≤ x) :
    xiShiftedAdaptiveMixedGammaKernel w
        (xiShiftedAdaptiveAffineAmplitude
          (-(xiShiftedAdaptiveAffineMonicMinimizer w x)) 1) x =
      -(x ^ (-(1 / 2 + w)) *
          xiShiftedAdaptiveLinearKernelDiscriminant (w * Real.log x) /
        (192 * w ^ 9 * reverseBesselPoly 2 (w * Real.log x))) := by
  rw [xiShiftedAdaptiveMixedGammaKernel_affineAmplitude_eq hw (by norm_num)]
  have hz : 0 ≤ w * Real.log x := mul_nonneg hw.le (Real.log_nonneg hx)
  have hB2 : 0 < reverseBesselPoly 2 (w * Real.log x) :=
    reverseBesselPoly_pos 2 hz
  unfold xiShiftedAdaptiveAffineMonicMinimizer
    xiShiftedAdaptiveLinearKernelDiscriminant
  field_simp [ne_of_gt hw, ne_of_gt hB2]
  ring_nf

/-- **Monic positive-root pointwise no-go.**  Every physical source point has a monic amplitude
`X-r`, with `r>0`, whose literal Gamma-averaged common kernel is strictly negative. -/
theorem exists_pos_root_xiShiftedAdaptiveMixedGammaKernel_monic_neg
    {w x : ℝ} (hw : 0 < w) (hx : 1 ≤ x) :
    ∃ r : ℝ, 0 < r ∧
      xiShiftedAdaptiveMixedGammaKernel w
        (xiShiftedAdaptiveAffineAmplitude (-r) 1) x < 0 := by
  refine ⟨xiShiftedAdaptiveAffineMonicMinimizer w x,
    xiShiftedAdaptiveAffineMonicMinimizer_pos hw hx, ?_⟩
  rw [xiShiftedAdaptiveMixedGammaKernel_affineMonicMinimizer_eq hw hx]
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hz : 0 ≤ w * Real.log x := mul_nonneg hw.le (Real.log_nonneg hx)
  have hdisc := xiShiftedAdaptiveLinearKernelDiscriminant_pos hz
  have hB2 := reverseBesselPoly_pos 2 hz
  have hrpow : 0 < x ^ (-(1 / 2 + w)) := Real.rpow_pos_of_pos hxpos _
  exact neg_lt_zero.mpr
    (div_pos (mul_pos hrpow hdisc) (mul_pos (by positivity) hB2))

/-- Vertex of the source-point linear-amplitude quadratic. -/
def xiShiftedAdaptiveLinearKernelMinimizer (w x : ℝ) : ℝ :=
  6 * w ^ 2 * reverseBesselPoly 3 (w * Real.log x) /
    reverseBesselPoly 4 (w * Real.log x)

/-- Exact minimum value of the linear-amplitude kernel on every physical source point. -/
theorem xiShiftedAdaptiveMixedGammaKernel_linearMinimizer_eq
    {w x : ℝ} (hw : 0 < w) (hx : 1 ≤ x) :
    xiShiftedAdaptiveMixedGammaKernel w
        (xiShiftedAdaptiveLinearAmplitude
          (xiShiftedAdaptiveLinearKernelMinimizer w x)) x =
      -(x ^ (-(1 / 2 + w)) *
          xiShiftedAdaptiveLinearKernelDiscriminant (w * Real.log x) /
        (8 * w ^ 5 * reverseBesselPoly 4 (w * Real.log x))) := by
  have hz : 0 ≤ w * Real.log x := mul_nonneg hw.le (Real.log_nonneg hx)
  have hB3 : 0 < reverseBesselPoly 3 (w * Real.log x) :=
    reverseBesselPoly_pos 3 hz
  have hB4 : 0 < reverseBesselPoly 4 (w * Real.log x) :=
    reverseBesselPoly_pos 4 hz
  have ha : xiShiftedAdaptiveLinearKernelMinimizer w x ≠ 0 := by
    unfold xiShiftedAdaptiveLinearKernelMinimizer
    positivity
  rw [xiShiftedAdaptiveMixedGammaKernel_linearAmplitude_eq hw ha]
  unfold xiShiftedAdaptiveLinearKernelMinimizer
    xiShiftedAdaptiveLinearKernelDiscriminant
  field_simp [ne_of_gt hw, ne_of_gt hB4]
  ring_nf

/-- At every point of the physical Euler ray, the exact minimizing linear amplitude makes the
literal adaptive Gamma kernel strictly negative. -/
theorem xiShiftedAdaptiveMixedGammaKernel_linearMinimizer_neg
    {w x : ℝ} (hw : 0 < w) (hx : 1 ≤ x) :
    xiShiftedAdaptiveMixedGammaKernel w
        (xiShiftedAdaptiveLinearAmplitude
          (xiShiftedAdaptiveLinearKernelMinimizer w x)) x < 0 := by
  rw [xiShiftedAdaptiveMixedGammaKernel_linearMinimizer_eq hw hx]
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hz : 0 ≤ w * Real.log x := mul_nonneg hw.le (Real.log_nonneg hx)
  have hdisc : 0 < xiShiftedAdaptiveLinearKernelDiscriminant (w * Real.log x) :=
    xiShiftedAdaptiveLinearKernelDiscriminant_pos hz
  have hB4 : 0 < reverseBesselPoly 4 (w * Real.log x) :=
    reverseBesselPoly_pos 4 hz
  have hrpow : 0 < x ^ (-(1 / 2 + w)) := Real.rpow_pos_of_pos hxpos _
  exact neg_lt_zero.mpr
    (div_pos (mul_pos hrpow hdisc) (mul_pos (by positivity) hB4))

/-- **Maximal actual-kernel pointwise-positivity no-go.** Every physical source point has a
linear amplitude whose literal common Gamma kernel is negative there. -/
theorem forall_eulerRay_exists_xiShiftedAdaptiveMixedGammaKernel_neg
    {w : ℝ} (hw : 1 / 2 < w) :
    ∀ x : ℝ, 1 ≤ x →
      ∃ A : Polynomial ℝ, xiShiftedAdaptiveMixedGammaKernel w A x < 0 := by
  intro x hx
  exact ⟨xiShiftedAdaptiveLinearAmplitude
      (xiShiftedAdaptiveLinearKernelMinimizer w x),
    xiShiftedAdaptiveMixedGammaKernel_linearMinimizer_neg (by linarith) hx⟩

/-! ## A fixed rational witness -/

/-- Linear amplitude giving a compact exact counterexample at `x = exp (1 / w)`. -/
def xiShiftedAdaptiveKernelCounterexampleAmplitude (w : ℝ) : Polynomial ℝ :=
  xiShiftedAdaptiveLinearAmplitude ((111 / 133 : ℝ) * w ^ 2)

/-- Exact reverse-Bessel values at the fixed source coordinate `w log x = 1`. -/
theorem reverseBesselPoly_two_one : reverseBesselPoly 2 1 = 7 := by
  norm_num [reverseBesselPoly, Finset.sum_range_succ, squaredRadialJetWeight]

theorem reverseBesselPoly_three_one : reverseBesselPoly 3 1 = 37 := by
  norm_num [reverseBesselPoly, Finset.sum_range_succ, squaredRadialJetWeight]

theorem reverseBesselPoly_four_one : reverseBesselPoly 4 1 = 266 := by
  norm_num [reverseBesselPoly, Finset.sum_range_succ, squaredRadialJetWeight]

/-- Exact rational physical-ray witness obtained by specializing the quadratic classification. -/
theorem xiShiftedAdaptiveMixedGammaKernel_counterexample_eq
    {w : ℝ} (hw : 0 < w) :
    xiShiftedAdaptiveMixedGammaKernel w
        (xiShiftedAdaptiveKernelCounterexampleAmplitude w) (Real.exp (1 / w)) =
      -(383 / (2128 * w ^ 5)) *
        (Real.exp (1 / w)) ^ (-(1 / 2 + w)) := by
  rw [show xiShiftedAdaptiveKernelCounterexampleAmplitude w =
      xiShiftedAdaptiveLinearAmplitude ((111 / 133 : ℝ) * w ^ 2) by rfl]
  rw [xiShiftedAdaptiveMixedGammaKernel_linearAmplitude_eq hw
    (mul_ne_zero (by norm_num) (pow_ne_zero _ (ne_of_gt hw)))]
  rw [Real.log_exp]
  have hw0 : w ≠ 0 := ne_of_gt hw
  field_simp [hw0]
  norm_num [reverseBesselPoly, Finset.sum_range_succ, squaredRadialJetWeight]

theorem xiShiftedAdaptiveMixedGammaKernel_counterexample_sourcePoint_gt_one
    {w : ℝ} (hw : 0 < w) :
    1 < Real.exp (1 / w) := by
  exact Real.one_lt_exp_iff.mpr (one_div_pos.mpr hw)

theorem xiShiftedAdaptiveMixedGammaKernel_counterexample_neg
    {w : ℝ} (hw : 0 < w) :
    xiShiftedAdaptiveMixedGammaKernel w
        (xiShiftedAdaptiveKernelCounterexampleAmplitude w) (Real.exp (1 / w)) < 0 := by
  rw [xiShiftedAdaptiveMixedGammaKernel_counterexample_eq hw]
  have hfactor : 0 < (Real.exp (1 / w)) ^ (-(1 / 2 + w)) :=
    Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hcoeff : 0 < 383 / (2128 * w ^ 5) := by positivity
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hcoeff) hfactor

/-- Fixed-witness form of the actual-kernel no-go inside the open Euler source ray. -/
theorem exists_xiShiftedAdaptiveMixedGammaKernel_neg_on_eulerRay
    {w : ℝ} (hw : 1 / 2 < w) :
    ∃ A : Polynomial ℝ, ∃ x : ℝ,
      1 < x ∧ xiShiftedAdaptiveMixedGammaKernel w A x < 0 := by
  refine ⟨xiShiftedAdaptiveKernelCounterexampleAmplitude w,
    Real.exp (1 / w), ?_, ?_⟩
  · exact xiShiftedAdaptiveMixedGammaKernel_counterexample_sourcePoint_gt_one
      (by linarith)
  · exact xiShiftedAdaptiveMixedGammaKernel_counterexample_neg (by linarith)

end

end RHTower
