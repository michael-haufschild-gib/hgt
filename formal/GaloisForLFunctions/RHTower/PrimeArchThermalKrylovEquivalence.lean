import GaloisForLFunctions.HTGeometry.FiniteAtomicThermalRealization
import GaloisForLFunctions.HTGeometry.HilbertSchmidtAlgebra
import GaloisForLFunctions.RHTower.PrimeArchCentralMomentGerm
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor
import GaloisForLFunctions.RHTower.PrimeArchThermalKrylovRH
import GaloisForLFunctions.RHTower.XiEndpointCompletedValueBound
import GaloisForLFunctions.RHTower.XiGlobalReflectionDefectEnergy
import GaloisForLFunctions.RHTower.XiReciprocalSquareSourceCore
import GaloisForLFunctions.RHTower.XiZerosInfinite

/-!
# RH as an explicit thermodynamic KMS moment limit

The finite-system capstone has a converse.  Every centered reciprocal-square Xi value has
strictly positive real part, unconditionally: the explicit completed endpoint bound forces every
Xi zero high enough that its imaginary displacement dominates its critical-strip horizontal
displacement.  Enumerate the multiplicity-exact Xi divisor and truncate the positive atomic moments

`m_N(n) = sum_{j < N} lambda_j^(n+1)`.

The finite-atomic KMS realization therefore turns each truncation into canonical finite Wightman
data without RH.  The second thermal moment has an exact decomposition as the first nontrivial
prime--archimedean source moment plus a nonnegative orientation energy.  Vanishing of that one
energy, equivalently convergence of just the second thermal moment to its source value, is RH.
Absolute summability of every reciprocal-square power then upgrades this one-value criterion to
pointwise convergence of the complete source moment tower.

This theorem identifies the precise mathematical content of the thermodynamic proposal.  Finite
quantum positivity is unconditional; the orientation-bearing datum is one scalar thermodynamic
limit equality.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

noncomputable local instance : Encodable XiZeroCopy := Encodable.ofCountable _

noncomputable local instance : Infinite XiDivisorSupport :=
  Set.infinite_coe_iff.mpr xiDivisorSupport_infinite

private noncomputable def xiFirstZeroCopyForThermal
    (rho : XiDivisorSupport) : XiZeroCopy := by
  have hpos := xi_divisor_pos_on_support rho
  have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by omega
  exact ⟨rho, ⟨0, hn⟩⟩

private theorem xiFirstZeroCopyForThermal_injective :
    Function.Injective xiFirstZeroCopyForThermal := by
  intro rho sigma h
  exact congrArg Sigma.fst h

noncomputable local instance : Infinite XiZeroCopy :=
  Infinite.of_injective xiFirstZeroCopyForThermal
    xiFirstZeroCopyForThermal_injective

noncomputable local instance : Denumerable XiZeroCopy :=
  Denumerable.ofEncodableOfInfinite XiZeroCopy

/-- The real reciprocal-square coordinate used as both mass and node in the thermal truncation. -/
def xiThermalNode (q : XiZeroCopy) : ℝ :=
  (xiZeroCopyReciprocalSquare q).re

/-- A fixed multiplicity-exact enumeration of the countably infinite Xi divisor. -/
def xiThermalEnumeration (j : ℕ) : XiZeroCopy :=
  Denumerable.ofNat XiZeroCopy j

/-- The fixed thermal enumeration visits every multiplicity copy exactly once. -/
theorem xiThermalEnumeration_bijective :
    Function.Bijective xiThermalEnumeration := by
  simpa only [xiThermalEnumeration] using
    (Denumerable.eqv XiZeroCopy).symm.bijective

/-- The `N`-atom reciprocal-square moment truncation.  The extra factor `lambda_j` makes its
`n`-th moment equal to `sum_{j < N} lambda_j^(n+1)`. -/
def xiThermalTruncation (N n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, xiThermalNode (xiThermalEnumeration j) *
    xiThermalNode (xiThermalEnumeration j) ^ n

/-- **Unconditional reciprocal-square sector law.**  Every Xi thermal node is strictly positive.
The completed endpoint value forces the squared zero height above `1`, while the open critical
strip keeps the squared horizontal displacement below `1/4`. -/
theorem xiThermalNode_pos (q : XiZeroCopy) : 0 < xiThermalNode q := by
  have hCpos : 0 < xiEndpointCompletedCurvature := xiEndpointCompletedCurvature_pos
  have hCinv : 2 < 1 / xiEndpointCompletedCurvature := by
    rw [lt_div_iff₀ hCpos]
    nlinarith [xiEndpointCompletedCurvature_lt_one_half]
  have hheight := xiZeroCopy_im_sq_ge_endpoint_source_inverse_gap q
  have hgamma : 1 < (q.1 : ℂ).im ^ 2 := by linarith
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hdelta : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 := by
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hnum : 0 < (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
    linarith
  have hden : 0 < Complex.normSq ((q.1 : ℂ) - 1 / 2) ^ 2 := by
    exact pow_pos (Complex.normSq_pos.mpr
      (sub_ne_zero.mpr (xi_divisor_support_ne_half q.1))) _
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have hden' : 0 < Complex.normSq ((q.1 : ℂ) - ((1 / 2 : ℝ) : ℂ)) ^ 2 := by
    simpa only [← hhalf] using hden
  rw [xiThermalNode, xiZeroCopyReciprocalSquare_eq, xiCentralReciprocalSquare]
  rw [hhalf]
  simp only [Complex.neg_re, pow_two, Complex.mul_re, Complex.inv_re, Complex.inv_im,
    Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
  rw [show -((((q.1 : ℂ).re - 1 / 2) /
          Complex.normSq ((q.1 : ℂ) - ((1 / 2 : ℝ) : ℂ))) *
          (((q.1 : ℂ).re - 1 / 2) /
            Complex.normSq ((q.1 : ℂ) - ((1 / 2 : ℝ) : ℂ))) -
        (-(q.1 : ℂ).im / Complex.normSq ((q.1 : ℂ) - ((1 / 2 : ℝ) : ℂ))) *
          (-(q.1 : ℂ).im / Complex.normSq ((q.1 : ℂ) - ((1 / 2 : ℝ) : ℂ)))) =
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) /
        Complex.normSq ((q.1 : ℂ) - ((1 / 2 : ℝ) : ℂ)) ^ 2 by ring]
  exact div_pos hnum hden'

/-- Backward-compatible RH-specialized form of unconditional thermal-node positivity. -/
theorem xiThermalNode_pos_of_rh (_hRH : RiemannHypothesis) (q : XiZeroCopy) :
    0 < xiThermalNode q :=
  xiThermalNode_pos q

/-- Under RH the real thermal node recovers the full complex reciprocal-square coordinate. -/
theorem xiThermalNode_complex_of_rh (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    (xiThermalNode q : ℂ) = xiZeroCopyReciprocalSquare q := by
  obtain ⟨x, _, hcoord⟩ := xiCentralReciprocalSquare_pos_real_of_rh hRH q.1
  have hcopy : xiZeroCopyReciprocalSquare q = (x : ℂ) := by
    rw [xiZeroCopyReciprocalSquare_eq]
    exact hcoord
  rw [xiThermalNode, hcopy]
  simp

/-- Every positive power of the real reciprocal-square Xi nodes is summable. -/
theorem summable_xiThermalNode_pow (n : ℕ) :
    Summable (fun q : XiZeroCopy => xiThermalNode q ^ (n + 1)) := by
  apply Summable.of_norm_bounded
    (summable_xiZeroCopyReciprocalSquare_pow n).norm
  intro q
  have h := pow_le_pow_left₀
    (abs_nonneg (xiZeroCopyReciprocalSquare q).re)
    (Complex.abs_re_le_norm (xiZeroCopyReciprocalSquare q)) (n + 1)
  rw [Real.norm_eq_abs, abs_pow, norm_pow]
  simpa only [xiThermalNode] using h

/-- The squared real parts of the reciprocal-square Xi coordinates are summable. -/
theorem summable_xiThermalNode_sq :
    Summable (fun q : XiZeroCopy => xiThermalNode q ^ 2) := by
  simpa using summable_xiThermalNode_pow 1

/-- The squared imaginary parts of the reciprocal-square Xi coordinates are summable. -/
theorem summable_xiThermalOrientationTerm :
    Summable (fun q : XiZeroCopy => (xiZeroCopyReciprocalSquare q).im ^ 2) := by
  apply Summable.of_norm_bounded
    (summable_xiZeroCopyReciprocalSquare_pow 1).norm
  intro q
  have h := pow_le_pow_left₀
    (abs_nonneg (xiZeroCopyReciprocalSquare q).im)
    (Complex.abs_im_le_norm (xiZeroCopyReciprocalSquare q)) 2
  rw [Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (xiZeroCopyReciprocalSquare q).im), norm_pow]
  simpa only [sq_abs] using h

/-- The unconditional positive thermodynamic moment tower of the Xi nodes. -/
def xiThermalPositiveMoment (n : ℕ) : ℝ :=
  ∑' q : XiZeroCopy, xiThermalNode q ^ (n + 1)

/-- The canonical thermodynamic second moment of the unconditional positive Xi nodes. -/
def xiThermalSecondMoment : ℝ :=
  ∑' q : XiZeroCopy, xiThermalNode q ^ 2

theorem xiThermalPositiveMoment_one_eq_secondMoment :
    xiThermalPositiveMoment 1 = xiThermalSecondMoment := by
  rfl

/-- The transverse orientation energy lost when the complex reciprocal-square second moment is
replaced by the positive thermal second moment. -/
def xiThermalOrientationEnergy : ℝ :=
  ∑' q : XiZeroCopy, (xiZeroCopyReciprocalSquare q).im ^ 2

/-- The Hermitian square mass of the reciprocal-square Xi spectrum.  Operator-theoretically this
is the squared Hilbert--Schmidt mass of the squared reciprocal diagonal. -/
def xiReciprocalSquareHermitianMass : ℝ :=
  ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ ^ 2

theorem summable_xiReciprocalSquareHermitianMass :
    Summable (fun q : XiZeroCopy => ‖xiZeroCopyReciprocalSquare q‖ ^ 2) := by
  simpa only [norm_pow] using (summable_xiZeroCopyReciprocalSquare_pow 1).norm

/-- The Hermitian square mass is the kernel Hilbert--Schmidt norm of the squared reciprocal
diagonal. -/
theorem xiReciprocalSquareHermitianMass_eq_kernel_hsNormSq :
    xiReciprocalSquareHermitianMass =
      HilbertSchmidt.hsNormSq
        (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1) := by
  rw [xiReciprocalSquareHermitianMass, xiReciprocalDiagonalKernel,
    HilbertSchmidt.hsPow_diagMul,
    HilbertSchmidt.hsNormSq_diagMul_infinite]
  apply tsum_congr
  intro q
  rw [xiZeroCopyReciprocalSquare]

/-- The Hilbert--Schmidt kernel square represents the existing squared reciprocal operator. -/
theorem toOperator_xiReciprocalDiagonalKernel_sq :
    HilbertSchmidt.toOperator
        (HilbertSchmidt.isHS_hsPow isHS_xiReciprocalDiagonalKernel 1) =
      xiReciprocalSquareOperator := by
  change HilbertSchmidt.toOperator
      (HilbertSchmidt.isHS_hsComp isHS_xiReciprocalDiagonalKernel
        isHS_xiReciprocalDiagonalKernel) = _
  rw [HilbertSchmidt.toOperator_hsComp]
  rfl

/-- **Static operator-state value law.**  The Hermitian square mass is exactly the squared
Hilbert--Schmidt norm of the concrete squared reciprocal Xi operator. -/
theorem xiReciprocalSquareHermitianMass_eq_operator_hsNormSq :
    xiReciprocalSquareHermitianMass =
      ContinuousLinearMap.hsNormSq xiReciprocalSquareOperator := by
  rw [xiReciprocalSquareHermitianMass_eq_kernel_hsNormSq,
    ← HilbertSchmidt.hsNormSq_toOperator
      (HilbertSchmidt.isHS_hsPow isHS_xiReciprocalDiagonalKernel 1),
    toOperator_xiReciprocalDiagonalKernel_sq]

/-- **Prime--Gamma value as a holomorphic operator trace.**  The first nontrivial normalized
prime--archimedean source moment is exactly the real trace of the fourth reciprocal Xi kernel
power.  This is an unconditional source/divisor value identity. -/
theorem normalizedPrimeArchMoment_one_eq_re_trace_xiReciprocalKernel_four :
    normalizedPrimeArchMoment 1 =
      (∑' q : XiZeroCopy,
        HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 3 (q, q)).re := by
  have htrace :
      (∑' q : XiZeroCopy,
        HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 3 (q, q)) =
      ∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q ^ 2 := by
    rw [xiReciprocalDiagonalKernel, HilbertSchmidt.hsPow_diagMul]
    apply tsum_congr
    intro q
    simp only [HilbertSchmidt.diagMul, if_pos]
    rw [xiZeroCopyReciprocalSquare]
    ring
  have hsource := primeArchSourceMoment_eq_xiCentralReciprocalMoment 1
  calc
    normalizedPrimeArchMoment 1 = (xiCentralReciprocalMoment 1).re := by
      simpa [normalizedPrimeArchMoment, normalizedPrimeArchMomentGerm] using
        congrArg Complex.re hsource
    _ = (∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q ^ 2).re := by
      rw [tsum_xiZeroCopyReciprocalSquare_pow]
    _ = (∑' q : XiZeroCopy,
        HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 3 (q, q)).re := by
      rw [htrace]

/-- The Hermitian square mass splits into the positive thermal second moment and its transverse
orientation energy. -/
theorem xiReciprocalSquareHermitianMass_eq_secondMoment_add_orientation :
    xiReciprocalSquareHermitianMass =
      xiThermalSecondMoment + xiThermalOrientationEnergy := by
  rw [xiReciprocalSquareHermitianMass, xiThermalSecondMoment,
    xiThermalOrientationEnergy, ← summable_xiThermalNode_sq.tsum_add
      summable_xiThermalOrientationTerm]
  apply tsum_congr
  intro q
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [xiThermalNode, pow_two]

/-- The pointwise smoothing weight relating the thermal orientation energy to the global
reciprocal reflection defect. -/
def xiThermalReflectionWeight (q : XiZeroCopy) : ℝ :=
  (xiReciprocalCoordinate q).re ^ 2

private lemma xiReciprocal_norm_sub_conj_sq_eq_four_im_sq (z : ℂ) :
    ‖z - (starRingEnd ℂ) z‖ ^ 2 = 4 * z.im ^ 2 := by
  rw [norm_sub_conj_sq, Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_two, Complex.mul_re]
  ring

/-- The thermal orientation term is exactly the global reflection-defect term multiplied by the
square of the real reciprocal coordinate. -/
theorem xiThermalOrientationTerm_eq_weighted_globalDefect (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im ^ 2 =
      xiThermalReflectionWeight q *
        ‖xiReciprocalCoordinate q -
          (starRingEnd ℂ) (xiReciprocalCoordinate q)‖ ^ 2 := by
  rw [xiThermalReflectionWeight, xiReciprocal_norm_sub_conj_sq_eq_four_im_sq]
  change (((xiReciprocalCoordinate q) ^ 2).im) ^ 2 = _
  simp only [pow_two, Complex.mul_im]
  ring

/-- The reflection-smoothing weight is strictly positive at every Xi zero. -/
theorem xiThermalReflectionWeight_pos (q : XiZeroCopy) :
    0 < xiThermalReflectionWeight q := by
  rw [xiThermalReflectionWeight]
  apply sq_pos_of_ne_zero
  rw [xiReciprocalCoordinate, Complex.inv_re]
  have hspectralRe : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
    simp [xiSpectralPoint]
  rw [hspectralRe]
  exact div_ne_zero (xi_divisor_support_im_ne_zero q.1)
    (ne_of_gt (Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q)))

/-- The endpoint source bound makes the reflection-smoothing weight strictly smaller than one. -/
theorem xiThermalReflectionWeight_lt_one (q : XiZeroCopy) :
    xiThermalReflectionWeight q < 1 := by
  have hCpos : 0 < xiEndpointCompletedCurvature := xiEndpointCompletedCurvature_pos
  have hCinv : 2 < 1 / xiEndpointCompletedCurvature := by
    rw [lt_div_iff₀ hCpos]
    nlinarith [xiEndpointCompletedCurvature_lt_one_half]
  have hheight := xiZeroCopy_im_sq_ge_endpoint_source_inverse_gap q
  have hgamma : 1 < (q.1 : ℂ).im ^ 2 := by linarith
  have hspectralNormSq : 1 < Complex.normSq (xiSpectralPoint q) := by
    rw [← Complex.sq_norm, norm_xiSpectralPoint, Complex.sq_norm,
      Complex.normSq_apply]
    norm_num
    nlinarith [sq_nonneg ((q.1 : ℂ).re - 1 / 2)]
  have hinvNormSq : ‖xiReciprocalCoordinate q‖ ^ 2 < 1 := by
    rw [xiReciprocalCoordinate, Complex.sq_norm, Complex.normSq_inv]
    exact inv_lt_one_of_one_lt₀ hspectralNormSq
  have hreSqLeNormSq :
      (xiReciprocalCoordinate q).re ^ 2 ≤ ‖xiReciprocalCoordinate q‖ ^ 2 := by
    nlinarith [Complex.sq_norm_sub_sq_re (xiReciprocalCoordinate q),
      sq_nonneg (xiReciprocalCoordinate q).im]
  exact lt_of_le_of_lt hreSqLeNormSq hinvNormSq

/-- The complete thermal orientation energy is the strictly positively weighted global
reflection-defect energy. -/
theorem xiThermalOrientationEnergy_eq_weightedGlobalDefect :
    xiThermalOrientationEnergy =
      ∑' q : XiZeroCopy, xiThermalReflectionWeight q *
        ‖xiReciprocalCoordinate q -
          (starRingEnd ℂ) (xiReciprocalCoordinate q)‖ ^ 2 := by
  rw [xiThermalOrientationEnergy]
  apply tsum_congr
  exact xiThermalOrientationTerm_eq_weighted_globalDefect

/-- **Thermal source-gap identity.**  The thermodynamic second moment minus its transverse
orientation energy is exactly the first nontrivial normalized prime--Gamma source moment. -/
theorem xiThermalSecondMoment_sub_orientationEnergy_eq_source :
    xiThermalSecondMoment - xiThermalOrientationEnergy =
      normalizedPrimeArchMoment 1 := by
  have hpow := summable_xiZeroCopyReciprocalSquare_pow 1
  calc
    xiThermalSecondMoment - xiThermalOrientationEnergy =
        ∑' q : XiZeroCopy,
          (xiThermalNode q ^ 2 - (xiZeroCopyReciprocalSquare q).im ^ 2) := by
      rw [xiThermalSecondMoment, xiThermalOrientationEnergy,
        summable_xiThermalNode_sq.tsum_sub summable_xiThermalOrientationTerm]
    _ = ∑' q : XiZeroCopy, (xiZeroCopyReciprocalSquare q ^ 2).re := by
      apply tsum_congr
      intro q
      simp only [xiThermalNode, pow_two, Complex.mul_re]
    _ = (xiCentralReciprocalMoment 1).re := by
      rw [← Complex.re_tsum hpow, tsum_xiZeroCopyReciprocalSquare_pow]
    _ = normalizedPrimeArchMoment 1 := by
      have hsource := primeArchSourceMoment_eq_xiCentralReciprocalMoment 1
      simpa [normalizedPrimeArchMoment, normalizedPrimeArchMomentGerm] using
        congrArg Complex.re hsource.symm

/-- **Hermitian/holomorphic trace-gap identity.**  The Hermitian square mass exceeds the
prime--Gamma holomorphic trace value by exactly twice the thermal orientation energy. -/
theorem xiReciprocalSquareHermitianMass_sub_source_eq_two_orientationEnergy :
    xiReciprocalSquareHermitianMass - normalizedPrimeArchMoment 1 =
      2 * xiThermalOrientationEnergy := by
  have hmass := xiReciprocalSquareHermitianMass_eq_secondMoment_add_orientation
  have hsource := xiThermalSecondMoment_sub_orientationEnergy_eq_source
  linarith

/-- The positive thermal second moment is the arithmetic mean of the Hermitian square mass and
the prime--Gamma holomorphic trace value. -/
theorem xiThermalSecondMoment_eq_average_mass_source :
    xiThermalSecondMoment =
      (xiReciprocalSquareHermitianMass + normalizedPrimeArchMoment 1) / 2 := by
  have hmass := xiReciprocalSquareHermitianMass_eq_secondMoment_add_orientation
  have hsource := xiThermalSecondMoment_sub_orientationEnergy_eq_source
  linarith

theorem xiThermalOrientationEnergy_nonneg :
    0 ≤ xiThermalOrientationEnergy := by
  exact tsum_nonneg (fun q => sq_nonneg (xiZeroCopyReciprocalSquare q).im)

/-- Universal Hermitian-mass domination of the prime--Gamma holomorphic trace value. -/
theorem normalizedPrimeArchMoment_one_le_xiReciprocalSquareHermitianMass :
    normalizedPrimeArchMoment 1 ≤ xiReciprocalSquareHermitianMass := by
  have hgap := xiReciprocalSquareHermitianMass_sub_source_eq_two_orientationEnergy
  have henergy := xiThermalOrientationEnergy_nonneg
  linarith

/-- The thermal orientation energy is bounded by the unsmoothed global reflection defect. -/
theorem xiThermalOrientationEnergy_le_globalReflectionDefectEnergy :
    xiThermalOrientationEnergy ≤ xiGlobalReflectionDefectEnergy := by
  rw [xiThermalOrientationEnergy, xiGlobalReflectionDefectEnergy]
  apply summable_xiThermalOrientationTerm.tsum_le_tsum
  · intro q
    rw [xiThermalOrientationTerm_eq_weighted_globalDefect]
    exact mul_le_of_le_one_left (sq_nonneg _)
      (xiThermalReflectionWeight_lt_one q).le
  · exact summable_xiGlobalReflectionDefectEnergy

/-- The prime--Gamma source value is an unconditional lower bound for the thermal second moment. -/
theorem normalizedPrimeArchMoment_one_le_xiThermalSecondMoment :
    normalizedPrimeArchMoment 1 ≤ xiThermalSecondMoment := by
  have hgap := xiThermalSecondMoment_sub_orientationEnergy_eq_source
  have henergy := xiThermalOrientationEnergy_nonneg
  linarith

/-- Vanishing of the single transverse thermal energy is exactly RH. -/
theorem xiThermalOrientationEnergy_eq_zero_iff_rh :
    xiThermalOrientationEnergy = 0 ↔ RiemannHypothesis := by
  constructor
  · intro hzero
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hterm := summable_xiThermalOrientationTerm.le_tsum q
      (fun j _ => sq_nonneg (xiZeroCopyReciprocalSquare j).im)
    rw [← xiThermalOrientationEnergy, hzero] at hterm
    have him : (xiZeroCopyReciprocalSquare q).im = 0 := by
      nlinarith [sq_nonneg (xiZeroCopyReciprocalSquare q).im]
    have hre : (q.1 : ℂ).re = 1 / 2 := by
      rw [xiZeroCopyReciprocalSquare_eq] at him
      exact (xiCentralReciprocalSquare_im_eq_zero_iff q.1).mp him
    refine ⟨(xiSpectralPoint q).re, ?_⟩
    apply Complex.ext
    · simp
    · simp [xiSpectralPoint, hre]
  · intro hRH
    rw [xiThermalOrientationEnergy]
    rw [show (fun q : XiZeroCopy => (xiZeroCopyReciprocalSquare q).im ^ 2) =
        fun _ => 0 by
      funext q
      obtain ⟨x, _, hcoord⟩ :=
        xiCentralReciprocalSquare_pos_real_of_rh hRH q.1
      rw [xiZeroCopyReciprocalSquare_eq, hcoord]
      simp]
    simp

/-- Saturation of the universal Hermitian-mass lower bound is exactly RH. -/
theorem xiReciprocalSquareHermitianMass_eq_source_iff_rh :
    xiReciprocalSquareHermitianMass = normalizedPrimeArchMoment 1 ↔
      RiemannHypothesis := by
  rw [← xiThermalOrientationEnergy_eq_zero_iff_rh]
  constructor <;> intro h
  · have hgap := xiReciprocalSquareHermitianMass_sub_source_eq_two_orientationEnergy
    linarith
  · have hgap := xiReciprocalSquareHermitianMass_sub_source_eq_two_orientationEnergy
    linarith

/-- **One operator-mass inequality for RH.**  The reverse of universal Hermitian-mass domination
is equivalent to RH. -/
theorem xiReciprocalSquareHermitianMass_le_source_iff_rh :
    xiReciprocalSquareHermitianMass ≤ normalizedPrimeArchMoment 1 ↔
      RiemannHypothesis := by
  constructor
  · intro hupper
    apply xiReciprocalSquareHermitianMass_eq_source_iff_rh.mp
    exact le_antisymm hupper
      normalizedPrimeArchMoment_one_le_xiReciprocalSquareHermitianMass
  · intro hRH
    exact (xiReciprocalSquareHermitianMass_eq_source_iff_rh.mpr hRH).le

/-- Equality between the squared reciprocal operator's Hilbert--Schmidt norm and the prime--Gamma
trace value is exactly RH. -/
theorem xiReciprocalSquareOperator_hsNormSq_eq_source_iff_rh :
    ContinuousLinearMap.hsNormSq xiReciprocalSquareOperator =
        normalizedPrimeArchMoment 1 ↔ RiemannHypothesis := by
  rw [← xiReciprocalSquareHermitianMass_eq_operator_hsNormSq]
  exact xiReciprocalSquareHermitianMass_eq_source_iff_rh

/-- **Static-operator RH inequality.**  The reverse Hilbert--Schmidt/holomorphic-trace inequality
for the concrete squared reciprocal operator is equivalent to RH. -/
theorem xiReciprocalSquareOperator_hsNormSq_le_source_iff_rh :
    ContinuousLinearMap.hsNormSq xiReciprocalSquareOperator ≤
        normalizedPrimeArchMoment 1 ↔ RiemannHypothesis := by
  rw [← xiReciprocalSquareHermitianMass_eq_operator_hsNormSq]
  exact xiReciprocalSquareHermitianMass_le_source_iff_rh

/-- **Hilbert--Schmidt/holomorphic-trace gap law.**  The excess of the squared reciprocal
kernel's Hilbert--Schmidt mass over the real fourth trace is exactly twice the transverse
orientation energy. -/
theorem xiReciprocalKernel_hsNormSq_sub_reTrace_four_eq_two_orientationEnergy :
    HilbertSchmidt.hsNormSq
          (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1) -
        (∑' q : XiZeroCopy,
          HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 3 (q, q)).re =
      2 * xiThermalOrientationEnergy := by
  rw [← xiReciprocalSquareHermitianMass_eq_kernel_hsNormSq,
    ← normalizedPrimeArchMoment_one_eq_re_trace_xiReciprocalKernel_four]
  exact xiReciprocalSquareHermitianMass_sub_source_eq_two_orientationEnergy

/-- The real holomorphic fourth trace never exceeds the Hermitian mass of the squared reciprocal
kernel. -/
theorem xiReciprocalKernel_reTrace_four_le_hsNormSq :
    (∑' q : XiZeroCopy,
        HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 3 (q, q)).re ≤
      HilbertSchmidt.hsNormSq
        (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1) := by
  rw [← xiReciprocalSquareHermitianMass_eq_kernel_hsNormSq,
    ← normalizedPrimeArchMoment_one_eq_re_trace_xiReciprocalKernel_four]
  exact normalizedPrimeArchMoment_one_le_xiReciprocalSquareHermitianMass

/-- Saturation of the universal real-fourth-trace/Hilbert--Schmidt inequality is exactly RH. -/
theorem xiReciprocalKernel_hsNormSq_eq_reTrace_four_iff_rh :
    HilbertSchmidt.hsNormSq
        (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1) =
      (∑' q : XiZeroCopy,
        HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 3 (q, q)).re ↔
      RiemannHypothesis := by
  rw [← xiReciprocalSquareHermitianMass_eq_kernel_hsNormSq,
    ← normalizedPrimeArchMoment_one_eq_re_trace_xiReciprocalKernel_four]
  exact xiReciprocalSquareHermitianMass_eq_source_iff_rh

/-- **Static operator saturation law for RH.**  Reversing the universal fourth-trace versus
Hilbert--Schmidt-mass inequality for the concrete reciprocal Xi kernel is equivalent to RH. -/
theorem xiReciprocalKernel_hsNormSq_le_reTrace_four_iff_rh :
    HilbertSchmidt.hsNormSq
        (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1) ≤
      (∑' q : XiZeroCopy,
        HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 3 (q, q)).re ↔
      RiemannHypothesis := by
  rw [← xiReciprocalSquareHermitianMass_eq_kernel_hsNormSq,
    ← normalizedPrimeArchMoment_one_eq_re_trace_xiReciprocalKernel_four]
  exact xiReciprocalSquareHermitianMass_le_source_iff_rh

/-- Away from RH, the high-height-damped thermal defect is strictly smaller than the unsmoothed
global reflection defect. -/
theorem xiThermalOrientationEnergy_lt_globalReflectionDefectEnergy_of_not_rh
    (hnot : ¬ RiemannHypothesis) :
    xiThermalOrientationEnergy < xiGlobalReflectionDefectEnergy := by
  have henergyPos : 0 < xiThermalOrientationEnergy := by
    apply lt_of_le_of_ne xiThermalOrientationEnergy_nonneg
    intro hzero
    apply hnot
    exact xiThermalOrientationEnergy_eq_zero_iff_rh.mp hzero.symm
  have hex : ∃ q : XiZeroCopy,
      0 < (xiZeroCopyReciprocalSquare q).im ^ 2 := by
    by_contra hnone
    push Not at hnone
    have hallzero : ∀ q : XiZeroCopy,
        (xiZeroCopyReciprocalSquare q).im ^ 2 = 0 := by
      intro q
      exact le_antisymm (hnone q) (sq_nonneg _)
    rw [xiThermalOrientationEnergy] at henergyPos
    simp only [hallzero, tsum_zero] at henergyPos
    exact (lt_irrefl 0 henergyPos)
  obtain ⟨q, hq⟩ := hex
  have hle : ∀ j : XiZeroCopy,
      (xiZeroCopyReciprocalSquare j).im ^ 2 ≤
        ‖xiReciprocalCoordinate j -
          (starRingEnd ℂ) (xiReciprocalCoordinate j)‖ ^ 2 := by
    intro j
    rw [xiThermalOrientationTerm_eq_weighted_globalDefect]
    exact mul_le_of_le_one_left (sq_nonneg _)
      (xiThermalReflectionWeight_lt_one j).le
  have hdefectPos : 0 < ‖xiReciprocalCoordinate q -
      (starRingEnd ℂ) (xiReciprocalCoordinate q)‖ ^ 2 := by
    by_contra hnonpos
    have hzero : ‖xiReciprocalCoordinate q -
        (starRingEnd ℂ) (xiReciprocalCoordinate q)‖ ^ 2 = 0 :=
      le_antisymm (le_of_not_gt hnonpos) (sq_nonneg _)
    rw [xiThermalOrientationTerm_eq_weighted_globalDefect, hzero, mul_zero] at hq
    exact (lt_irrefl 0 hq)
  have hlt : (xiZeroCopyReciprocalSquare q).im ^ 2 <
      ‖xiReciprocalCoordinate q -
        (starRingEnd ℂ) (xiReciprocalCoordinate q)‖ ^ 2 := by
    rw [xiThermalOrientationTerm_eq_weighted_globalDefect]
    exact mul_lt_of_lt_one_left hdefectPos (xiThermalReflectionWeight_lt_one q)
  rw [xiThermalOrientationEnergy, xiGlobalReflectionDefectEnergy]
  exact Summable.tsum_lt_tsum hle hlt summable_xiThermalOrientationTerm
    summable_xiGlobalReflectionDefectEnergy

/-- Strict damping of the global reflection defect is the positive form of failure of RH. -/
theorem xiThermalOrientationEnergy_lt_globalReflectionDefectEnergy_iff_not_rh :
    xiThermalOrientationEnergy < xiGlobalReflectionDefectEnergy ↔
      ¬ RiemannHypothesis := by
  constructor
  · intro hlt hRH
    have hthermal := xiThermalOrientationEnergy_eq_zero_iff_rh.mpr hRH
    have hglobal := xiGlobalReflectionDefectEnergy_eq_zero_iff_rh.mpr hRH
    linarith
  · exact xiThermalOrientationEnergy_lt_globalReflectionDefectEnergy_of_not_rh

/-- The thermal source gap is bounded by the existing global source--divisor gap. -/
theorem xiThermalSecondMoment_source_gap_le_globalSourceGap :
    xiThermalSecondMoment - normalizedPrimeArchMoment 1 ≤
      2 * (xiReciprocalHermitianMass - primeArchCentralCurvature) := by
  have hgap := xiThermalSecondMoment_sub_orientationEnergy_eq_source
  rw [← xiGlobalReflectionDefectEnergy_eq_mass_sub_source]
  calc
    xiThermalSecondMoment - normalizedPrimeArchMoment 1 =
        xiThermalOrientationEnergy := by linarith
    _ ≤ xiGlobalReflectionDefectEnergy :=
      xiThermalOrientationEnergy_le_globalReflectionDefectEnergy

/-- Equality in the unconditional thermal lower bound is exactly RH. -/
theorem xiThermalSecondMoment_eq_source_iff_rh :
    xiThermalSecondMoment = normalizedPrimeArchMoment 1 ↔
      RiemannHypothesis := by
  rw [← xiThermalOrientationEnergy_eq_zero_iff_rh]
  constructor
  · intro heq
    linarith [xiThermalSecondMoment_sub_orientationEnergy_eq_source]
  · intro hzero
    linarith [xiThermalSecondMoment_sub_orientationEnergy_eq_source]

/-- **One-inequality RH criterion.**  The reverse of the unconditional thermal lower bound is
equivalent to RH.  This is the only scalar estimate still required by the thermal construction. -/
theorem xiThermalSecondMoment_le_source_iff_rh :
    xiThermalSecondMoment ≤ normalizedPrimeArchMoment 1 ↔
      RiemannHypothesis := by
  constructor
  · intro hupper
    apply xiThermalSecondMoment_eq_source_iff_rh.mp
    exact le_antisymm hupper normalizedPrimeArchMoment_one_le_xiThermalSecondMoment
  · intro hRH
    exact (xiThermalSecondMoment_eq_source_iff_rh.mpr hRH).le

set_option maxHeartbeats 500000 in
/-- The enumerated finite thermal systems converge in every coordinate to the unconditional
positive thermodynamic moment tower. -/
theorem hasSum_xiThermalEnumeration_positiveMoment (n : ℕ) :
    HasSum (fun j : ℕ => xiThermalNode (xiThermalEnumeration j) ^ (n + 1))
      (xiThermalPositiveMoment n) := by
  let e : XiZeroCopy ≃ ℕ := Denumerable.eqv XiZeroCopy
  have hsum : HasSum (fun q : XiZeroCopy => xiThermalNode q ^ (n + 1))
      (xiThermalPositiveMoment n) := by
    simpa [xiThermalPositiveMoment] using (summable_xiThermalNode_pow n).hasSum
  have hsumNat : HasSum
      (fun j : ℕ => xiThermalNode (e.symm j) ^ (n + 1))
      (xiThermalPositiveMoment n) := e.symm.hasSum_iff.mpr hsum
  simpa [xiThermalEnumeration, e] using hsumNat

/-- The complete finite KMS tower converges unconditionally to its positive thermodynamic moment
tower; no RH input is needed for existence of the thermodynamic limit. -/
theorem tendsto_xiThermalTruncation_positiveMoment :
    Tendsto xiThermalTruncation atTop (nhds xiThermalPositiveMoment) := by
  apply tendsto_pi_nhds.mpr
  intro n
  have ht := (hasSum_xiThermalEnumeration_positiveMoment n).tendsto_sum_nat
  simpa only [xiThermalTruncation, pow_succ, mul_comm] using ht

/-- The enumerated thermal second moments sum to the canonical thermodynamic value. -/
theorem hasSum_xiThermalEnumeration_sq :
    HasSum (fun j : ℕ => xiThermalNode (xiThermalEnumeration j) ^ 2)
      xiThermalSecondMoment := by
  simpa only [xiThermalPositiveMoment_one_eq_secondMoment] using
    hasSum_xiThermalEnumeration_positiveMoment 1

/-- The second moment of the unconditional finite thermal systems always converges to the
canonical thermal second moment. -/
theorem tendsto_xiThermalTruncation_one :
    Tendsto (fun N => xiThermalTruncation N 1) atTop
      (nhds xiThermalSecondMoment) := by
  have ht := hasSum_xiThermalEnumeration_sq.tendsto_sum_nat
  simpa only [xiThermalTruncation, pow_one, pow_two] using ht

set_option maxHeartbeats 500000 in
/-- Under RH, the enumerated positive reciprocal-square powers sum to the source-defined
normalized prime--archimedean moments. -/
theorem hasSum_xiThermalEnumeration_pow_of_rh
    (hRH : RiemannHypothesis) (n : ℕ) :
    HasSum (fun j : ℕ => xiThermalNode (xiThermalEnumeration j) ^ (n + 1))
      (normalizedPrimeArchMoment n) := by
  let e : XiZeroCopy ≃ ℕ := Denumerable.eqv XiZeroCopy
  have hsumXi : HasSum
      (fun q : XiZeroCopy => xiZeroCopyReciprocalSquare q ^ (n + 1))
      (xiCentralReciprocalMoment n) := by
    simpa [tsum_xiZeroCopyReciprocalSquare_pow n] using
      (summable_xiZeroCopyReciprocalSquare_pow n).hasSum
  have hsumNat : HasSum
      (fun j : ℕ => xiZeroCopyReciprocalSquare (e.symm j) ^ (n + 1))
      (xiCentralReciprocalMoment n) := by
    exact e.symm.hasSum_iff.mpr hsumXi
  have hsumRe : HasSum
      (fun j : ℕ => (xiZeroCopyReciprocalSquare (e.symm j) ^ (n + 1)).re)
      (xiCentralReciprocalMoment n).re := by
    exact hsumNat.mapL Complex.reCLM
  have htarget : (xiCentralReciprocalMoment n).re = normalizedPrimeArchMoment n := by
    have hsource := primeArchSourceMoment_eq_xiCentralReciprocalMoment n
    simpa [normalizedPrimeArchMoment, normalizedPrimeArchMomentGerm] using
      congrArg Complex.re hsource.symm
  rw [htarget] at hsumRe
  convert hsumRe using 1
  funext j
  change xiThermalNode (e.symm j) ^ (n + 1) =
    (xiZeroCopyReciprocalSquare (e.symm j) ^ (n + 1)).re
  rw [← xiThermalNode_complex_of_rh hRH (e.symm j)]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- Identification of the unconditional positive thermal moment tower with the prime--Gamma
source moment tower is exactly RH.  The second coordinate already decides the equality. -/
theorem xiThermalPositiveMoment_eq_source_iff_rh :
    xiThermalPositiveMoment = normalizedPrimeArchMoment ↔
      RiemannHypothesis := by
  constructor
  · intro heq
    apply xiThermalSecondMoment_eq_source_iff_rh.mp
    rw [← xiThermalPositiveMoment_one_eq_secondMoment, heq]
  · intro hRH
    funext n
    exact (hasSum_xiThermalEnumeration_positiveMoment n).tsum_eq.symm.trans
      (hasSum_xiThermalEnumeration_pow_of_rh hRH n).tsum_eq

/-- RH makes the finite reciprocal-square truncations converge pointwise to the complete source
moment tower. -/
theorem tendsto_xiThermalTruncation_of_rh (hRH : RiemannHypothesis) :
    Tendsto xiThermalTruncation atTop (nhds normalizedPrimeArchMoment) := by
  apply tendsto_pi_nhds.mpr
  intro n
  have ht := (hasSum_xiThermalEnumeration_pow_of_rh hRH n).tendsto_sum_nat
  simpa only [xiThermalTruncation, pow_succ, mul_comm] using ht

/-- **One-value thermodynamic RH law.**  Convergence of only the second thermal moment to the
first nontrivial prime--Gamma source moment is equivalent to RH. -/
theorem tendsto_xiThermalTruncation_one_iff_rh :
    Tendsto (fun N => xiThermalTruncation N 1) atTop
      (nhds (normalizedPrimeArchMoment 1)) ↔ RiemannHypothesis := by
  constructor
  · intro hsource
    have hcanonical := tendsto_xiThermalTruncation_one
    have heq : xiThermalSecondMoment = normalizedPrimeArchMoment 1 :=
      tendsto_nhds_unique hcanonical hsource
    exact xiThermalSecondMoment_eq_source_iff_rh.mp heq
  · intro hRH
    have ht := tendsto_xiThermalTruncation_of_rh hRH
    exact (tendsto_pi_nhds.mp ht) 1

/-- Every explicit reciprocal-square truncation is a canonical finite KMS/Wightman moment
sequence, unconditionally. -/
theorem finiteKMSWightmanMomentSequence_xiThermalTruncation (N : ℕ) :
    FiniteKMSWightmanMomentSequence (xiThermalTruncation N) := by
  let node : Fin N → ℝ := fun i => xiThermalNode (xiThermalEnumeration i)
  refine ⟨N, 0, HTGeometry.finiteAtomicThermalEnergy node,
    HTGeometry.finiteAtomicKMSAmplitude node, ?_⟩
  funext n
  rw [HTGeometry.thermalEvenGapMoment_finiteAtomicKMS node node
    (fun _ => (xiThermalNode_pos _).le)
    (fun _ => (xiThermalNode_pos _).le)]
  exact (Fin.sum_univ_eq_sum_range
    (fun j : ℕ => xiThermalNode (xiThermalEnumeration j) *
      xiThermalNode (xiThermalEnumeration j) ^ n) N).symm

/-- The unconditional positive thermodynamic moment tower belongs to the closed trace-Hankel
cone.  This is the direct reusable consumer of finite KMS realizability plus full pointwise
thermodynamic convergence. -/
theorem sequenceTraceHankelNonnegative_xiThermalPositiveMoment :
    SequenceTraceHankelNonnegative xiThermalPositiveMoment := by
  exact sequenceTraceHankelNonnegative_of_finiteThermalKrylov_tendsto
    xiThermalTruncation xiThermalPositiveMoment
    (fun N => finiteKMSWightmanMomentSequence_finiteThermalKrylov
      (finiteKMSWightmanMomentSequence_xiThermalTruncation N))
    tendsto_xiThermalTruncation_positiveMoment

/-- Backward-compatible RH-specialized form of unconditional finite KMS realizability. -/
theorem finiteKMSWightmanMomentSequence_xiThermalTruncation_of_rh
    (_hRH : RiemannHypothesis) (N : ℕ) :
    FiniteKMSWightmanMomentSequence (xiThermalTruncation N) :=
  finiteKMSWightmanMomentSequence_xiThermalTruncation N

/-- Pointwise convergence of the unconditional finite KMS tower to the complete prime--Gamma
moment tower is equivalent to RH. -/
theorem tendsto_xiThermalTruncation_iff_rh :
    Tendsto xiThermalTruncation atTop (nhds normalizedPrimeArchMoment) ↔
      RiemannHypothesis := by
  constructor
  · intro hconv
    exact riemannHypothesis_of_primeArchFiniteKMSWightman_tendsto
      xiThermalTruncation finiteKMSWightmanMomentSequence_xiThermalTruncation hconv
  · exact tendsto_xiThermalTruncation_of_rh

/-- **Thermodynamic KMS equivalence for RH.**  For the explicit multiplicity-exact Xi
truncations, finite KMS realizability together with pointwise convergence to the prime--Gamma
source moments is equivalent to RH. -/
theorem riemannHypothesis_iff_xiThermalTruncation_KMS_tendsto :
    RiemannHypothesis ↔
      (∀ N, FiniteKMSWightmanMomentSequence (xiThermalTruncation N)) ∧
        Tendsto xiThermalTruncation atTop (nhds normalizedPrimeArchMoment) := by
  constructor
  · intro hRH
    exact ⟨finiteKMSWightmanMomentSequence_xiThermalTruncation,
      tendsto_xiThermalTruncation_of_rh hRH⟩
  · rintro ⟨hfinite, hconv⟩
    exact riemannHypothesis_of_primeArchFiniteKMSWightman_tendsto
      xiThermalTruncation hfinite hconv

end

end RHTower
