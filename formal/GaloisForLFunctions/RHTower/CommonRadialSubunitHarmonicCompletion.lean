import GaloisForLFunctions.RHTower.RecurrentPrimeBoundaryDensityTransgression
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolBaseNuclearSynthesis
import GaloisForLFunctions.RHTower.PolynomialFockAdaptedTangentPacketSynthesis
import GaloisForLFunctions.HTGeometry.OperatorAbsoluteValueBetween
import GaloisForLFunctions.HTGeometry.HilbertSchmidtDominatesPointwise
import GaloisForLFunctions.HTGeometry.CompactSelfAdjointEigenvalue
import GaloisForLFunctions.HTGeometry.PureStateProjectorTangentInertia
import GaloisForLFunctions.HTGeometry.OrthonormalNormalize
import GaloisForLFunctions.HTGeometry.HilbertSchmidtNormComparison
import GaloisForLFunctions.HTGeometry.HilbertBlockOperator
import GaloisForLFunctions.RHTower.FrankensteinPrimitiveXiMixedBurnolSchurGap

open Complex Matrix Set MeasureTheory Filter Topology
open scoped BigOperators InnerProductSpace ComplexOrder

namespace RHTower

noncomputable section

open ContinuousLinearMap
open GaloisForLFunctions.HTGeometry

local instance commonRadialPrimeFactTwoNeTop : Fact ((2 : ENNReal) ≠ ⊤) :=
  ⟨by norm_num⟩

local instance commonRadialPrimeMeasurableSpace : MeasurableSpace Nat.Primes := ⊤

/-- Literal common half-line radial carrier used by both prime--Hodge and Burnol sources. -/
abbrev CommonRadialSpace := routePBurnolHalfLineL2

/-- Normalizing scalar converting the zero-depth Burnol column into the normalized Stokes
prime--Hodge radial mode. -/
def commonRadialPrimeScale (a : {d : ℝ // 0 < d}) (p : Nat.Primes) : ℝ :=
  Real.sqrt (routePPrimitiveGammaJuliaStokesApertureScaleSq a.1 p) *
    Real.log (p : ℝ) /
      Real.sqrt (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent a.1)

theorem commonRadialPrimeScale_pos (a : {d : ℝ // 0 < d}) (p : Nat.Primes) :
    0 < commonRadialPrimeScale a p := by
  unfold commonRadialPrimeScale
  exact div_pos
    (mul_pos
      (Real.sqrt_pos.2
        (routePPrimitiveGammaJuliaStokesApertureScaleSq_pos a.property p))
      (Real.log_pos (by exact_mod_cast p.property.one_lt)))
    (Real.sqrt_pos.2
      (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos a.property))

/-- The literal weighted mode `2 b_d(p) L exp (-log(p)L)` represented using the already checked
Burnol half-line feature. -/
def commonRadialPrimeField (a : {d : ℝ // 0 < d})
    (p : Nat.Primes) : CommonRadialSpace :=
  (commonRadialPrimeScale a p : ℂ) •
    routePPrimitiveBurnolWindowFeatureLp (p, 0) 0

theorem inner_routePPrimitiveBurnolWindowFeatureLp_prime_zero
    (p q : Nat.Primes) :
    inner ℂ (routePPrimitiveBurnolWindowFeatureLp (p, 0) 0)
        (routePPrimitiveBurnolWindowFeatureLp (q, 0) 0) =
      finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (p, 0)) *
        routePBaseCauchyCubicKernel 1
          (xiGammaEulerPrimitiveLogFrequency (p, 0))
          (xiGammaEulerPrimitiveLogFrequency (q, 0)) 0 *
        star (finiteVonMangoldtDepthOneAmplitude
          (xiGammaEulerValuationNat (q, 0))) := by
  let labels : Fin 2 → Nat.Primes × ℕ := ![(p, 0), (q, 0)]
  let clocks : Fin 2 → ℝ := fun _ => 0
  have hgram := congrArg (fun M => M (0 : Fin 2) (1 : Fin 2))
    (routePPrimitiveBurnolWindowGramMatrix_eq_gram_L2 labels clocks)
  have hbase := congrArg (fun M => M (0 : Fin 2) (1 : Fin 2))
    (routePPrimitiveBurnolWindowGramMatrix_eq_baseCauchy labels clocks)
  rw [hbase, routePPrimitiveBaseCauchyCubicKernelMatrix_apply] at hgram
  simpa [labels, clocks, Matrix.gram_apply] using hgram.symm

/-- Mixed zero-clock Gram entry between a prime--Hodge mode and any resolved primitive Burnol
column. -/
theorem inner_routePPrimitiveBurnolWindowFeatureLp_prime_zero_base
    (p : Nat.Primes) (pe : RoutePPrimitiveIndex) :
    inner ℂ (routePPrimitiveBurnolWindowFeatureLp (p, 0) 0)
        (routePPrimitiveBurnolBaseField pe) =
      finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (p, 0)) *
        routePBaseCauchyCubicKernel 1
          (xiGammaEulerPrimitiveLogFrequency (p, 0))
          (xiGammaEulerPrimitiveLogFrequency pe) 0 *
        star (finiteVonMangoldtDepthOneAmplitude
          (xiGammaEulerValuationNat pe)) := by
  let labels : Fin 2 → Nat.Primes × ℕ := ![(p, 0), pe]
  let clocks : Fin 2 → ℝ := fun _ => 0
  have hgram := congrArg (fun M => M (0 : Fin 2) (1 : Fin 2))
    (routePPrimitiveBurnolWindowGramMatrix_eq_gram_L2 labels clocks)
  have hbase := congrArg (fun M => M (0 : Fin 2) (1 : Fin 2))
    (routePPrimitiveBurnolWindowGramMatrix_eq_baseCauchy labels clocks)
  rw [hbase, routePPrimitiveBaseCauchyCubicKernelMatrix_apply] at hgram
  simpa [labels, clocks, Matrix.gram_apply, routePPrimitiveBurnolBaseField] using
    hgram.symm

/-- Positive real overlap of one normalized prime mode with one primitive Burnol column. -/
def commonRadialPrimeBurnolOverlap
    (a : {d : ℝ // 0 < d}) (p : Nat.Primes) (pe : RoutePPrimitiveIndex) : ℝ :=
  commonRadialPrimeScale a p *
    Real.sqrt (ArithmeticFunction.vonMangoldt
      (xiGammaEulerValuationNat (p, 0)) / xiGammaEulerValuationNat (p, 0)) *
    (2 / (xiGammaEulerPrimitiveLogFrequency (p, 0) +
      xiGammaEulerPrimitiveLogFrequency pe) ^ 3) *
    Real.sqrt (ArithmeticFunction.vonMangoldt
      (xiGammaEulerValuationNat pe) / xiGammaEulerValuationNat pe)

theorem inner_commonRadialPrimeField_routePPrimitiveBurnolBaseField
    (a : {d : ℝ // 0 < d}) (p : Nat.Primes) (pe : RoutePPrimitiveIndex) :
    inner ℂ (commonRadialPrimeField a p)
      (routePPrimitiveBurnolBaseField pe) =
        (commonRadialPrimeBurnolOverlap a p pe : ℂ) := by
  rw [commonRadialPrimeField, inner_smul_left,
    inner_routePPrimitiveBurnolWindowFeatureLp_prime_zero_base]
  have hkernel : routePBaseCauchyCubicKernel 1
      (xiGammaEulerPrimitiveLogFrequency (p, 0))
      (xiGammaEulerPrimitiveLogFrequency pe) 0 =
        ((2 / (xiGammaEulerPrimitiveLogFrequency (p, 0) +
          xiGammaEulerPrimitiveLogFrequency pe) ^ 3 : ℝ) : ℂ) := by
    unfold routePBaseCauchyCubicKernel routePCollisionPairFrequency
    push_cast
    norm_num
  rw [hkernel]
  unfold commonRadialPrimeBurnolOverlap finiteVonMangoldtDepthOneAmplitude
  push_cast
  simp
  ring

theorem commonRadialPrimeBurnolOverlap_pos
    (a : {d : ℝ // 0 < d}) (p : Nat.Primes) (pe : RoutePPrimitiveIndex) :
    0 < commonRadialPrimeBurnolOverlap a p pe := by
  have hp : 0 < xiGammaEulerPrimitiveLogFrequency (p, 0) :=
    xiGammaEulerPrimitiveLogFrequency_pos (p, 0)
  have hpe : 0 < xiGammaEulerPrimitiveLogFrequency pe :=
    xiGammaEulerPrimitiveLogFrequency_pos pe
  have hamp_sq_pos (pe' : RoutePPrimitiveIndex) :
      0 < ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat pe') /
        xiGammaEulerValuationNat pe' := by
    apply div_pos
    · rw [xiGammaEulerValuationNat, vonMangoldt_prime_pow_succ_eq_log pe']
      exact Real.log_pos (by exact_mod_cast pe'.1.property.one_lt)
    · exact_mod_cast pow_pos pe'.1.property.pos (pe'.2 + 1)
  unfold commonRadialPrimeBurnolOverlap
  exact mul_pos
    (mul_pos
      (mul_pos (commonRadialPrimeScale_pos a p)
        (Real.sqrt_pos.2 (hamp_sq_pos (p, 0))))
      (div_pos (by norm_num) (pow_pos (add_pos hp hpe) 3)))
    (Real.sqrt_pos.2 (hamp_sq_pos pe))

theorem commonRadialPrimeBurnolOverlap_le_norm
    (a : {d : ℝ // 0 < d}) (p : Nat.Primes) (pe : RoutePPrimitiveIndex) :
    commonRadialPrimeBurnolOverlap a p pe ≤
      ‖commonRadialPrimeField a p‖ * ‖routePPrimitiveBurnolBaseField pe‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (commonRadialPrimeField a p)
    (routePPrimitiveBurnolBaseField pe)
  rw [inner_commonRadialPrimeField_routePPrimitiveBurnolBaseField,
    norm_real, Real.norm_eq_abs,
    abs_of_pos (commonRadialPrimeBurnolOverlap_pos a p pe)] at h
  exact h

theorem summable_commonRadialPrimeBurnolOverlap_mul
    (a : {d : ℝ // 0 < d}) (p q : Nat.Primes) :
    Summable fun pe : RoutePPrimitiveIndex =>
      commonRadialPrimeBurnolOverlap a p pe *
        commonRadialPrimeBurnolOverlap a q pe := by
  have hmajor : Summable fun pe : RoutePPrimitiveIndex =>
      (‖commonRadialPrimeField a p‖ * ‖commonRadialPrimeField a q‖) *
        ‖routePPrimitiveBurnolBaseField pe‖ ^ 2 :=
    summable_norm_sq_routePPrimitiveBurnolBaseField.mul_left _
  refine Summable.of_nonneg_of_le
    (fun pe => mul_nonneg (commonRadialPrimeBurnolOverlap_pos a p pe).le
      (commonRadialPrimeBurnolOverlap_pos a q pe).le) (fun pe => ?_) hmajor
  have hp := commonRadialPrimeBurnolOverlap_le_norm a p pe
  have hq := commonRadialPrimeBurnolOverlap_le_norm a q pe
  have hmul := mul_le_mul hp hq
    (commonRadialPrimeBurnolOverlap_pos a q pe).le
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  nlinarith [norm_nonneg (commonRadialPrimeField a p),
    norm_nonneg (commonRadialPrimeField a q),
    norm_nonneg (routePPrimitiveBurnolBaseField pe)]

theorem re_inner_commonRadialPrimeField_routePPrimitiveBurnolBaseField_pos
    (a : {d : ℝ // 0 < d}) (p : Nat.Primes) (pe : RoutePPrimitiveIndex) :
    0 < (inner ℂ (commonRadialPrimeField a p)
      (routePPrimitiveBurnolBaseField pe)).re := by
  rw [inner_commonRadialPrimeField_routePPrimitiveBurnolBaseField]
  simpa using commonRadialPrimeBurnolOverlap_pos a p pe

theorem im_inner_commonRadialPrimeField_routePPrimitiveBurnolBaseField_eq_zero
    (a : {d : ℝ // 0 < d}) (p : Nat.Primes) (pe : RoutePPrimitiveIndex) :
    (inner ℂ (commonRadialPrimeField a p)
      (routePPrimitiveBurnolBaseField pe)).im = 0 := by
  rw [inner_commonRadialPrimeField_routePPrimitiveBurnolBaseField]
  simp

/-- Exact Gram identity: the radial prime family represents the normalized Stokes kernel. -/
theorem inner_commonRadialPrimeField_eq_normalizedStokesPrimeKernel
    (a : {d : ℝ // 0 < d}) (p q : Nat.Primes) :
    inner ℂ (commonRadialPrimeField a p) (commonRadialPrimeField a q) =
      normalizedStokesPrimeKernel a.1 (p, q) := by
  rw [commonRadialPrimeField, commonRadialPrimeField,
    inner_smul_left, inner_smul_right,
    inner_routePPrimitiveBurnolWindowFeatureLp_prime_zero]
  rw [show (starRingEnd ℂ) (commonRadialPrimeScale a p : ℂ) =
      (commonRadialPrimeScale a p : ℂ) by simp]
  rw [commonRadialPrimeScale, commonRadialPrimeScale,
    normalizedStokesPrimeKernel,
    routePPrimitiveGammaJuliaStokesCofinalChildKernel]
  rw [xiGammaEulerPrimitiveLogFrequency_prime_zero,
    xiGammaEulerPrimitiveLogFrequency_prime_zero]
  have hJ : 0 < gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent a.1 :=
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos a.property
  have hsqrtJ : Real.sqrt
      (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent a.1) ≠ 0 := by
    positivity
  push_cast
  field_simp [hsqrtJ, hJ.ne']
  have hsqrtJcomplex :
      (Real.sqrt (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent a.1) : ℂ) ^ 2 =
        (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent a.1 : ℂ) := by
    norm_cast
    exact Real.sq_sqrt hJ.le
  rw [hsqrtJcomplex]
  ring

theorem norm_sq_commonRadialPrimeField
    (a : {d : ℝ // 0 < d}) (p : Nat.Primes) :
    ‖commonRadialPrimeField a p‖ ^ 2 =
      routePPrimitiveGammaJuliaStokesTransportedPrimeWeight a.1 p /
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent a.1 := by
  have h := inner_commonRadialPrimeField_eq_normalizedStokesPrimeKernel a p p
  rw [inner_self_eq_norm_sq_to_K, normalizedStokesPrimeKernel,
    routePPrimitiveGammaJuliaStokesCofinalChildKernel_diagonal a.property] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

theorem summable_norm_sq_commonRadialPrimeField (a : {d : ℝ // 0 < d}) :
    Summable fun p : Nat.Primes => ‖commonRadialPrimeField a p‖ ^ 2 := by
  refine (summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight
    a.property).div_const
      (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent a.1) |>.congr ?_
  intro p
  exact (norm_sq_commonRadialPrimeField a p).symm

theorem tsum_norm_sq_commonRadialPrimeField (a : {d : ℝ // 0 < d}) :
    (∑' p : Nat.Primes, ‖commonRadialPrimeField a p‖ ^ 2) = 1 := by
  rw [tsum_congr (norm_sq_commonRadialPrimeField a), tsum_div_const,
    tsum_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight a.property]
  exact div_self
    (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos a.property).ne'

theorem summable_norm_inner_commonRadialPrimeField_sq
    (a : {d : ℝ // 0 < d}) (x : CommonRadialSpace) :
    Summable fun p : Nat.Primes =>
      ‖inner ℂ (commonRadialPrimeField a p) x‖ ^ (2 : ℝ) := by
  have hmajor : Summable fun p : Nat.Primes =>
      ‖commonRadialPrimeField a p‖ ^ 2 * ‖x‖ ^ 2 :=
    (summable_norm_sq_commonRadialPrimeField a).mul_right (‖x‖ ^ 2)
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) hmajor
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  nlinarith [norm_inner_le_norm (𝕜 := ℂ) (commonRadialPrimeField a p) x,
    norm_nonneg (inner ℂ (commonRadialPrimeField a p) x),
    norm_nonneg (commonRadialPrimeField a p), norm_nonneg x]

theorem commonRadialPrimeField_bessel
    (a : {d : ℝ // 0 < d}) (x : CommonRadialSpace) :
    (∑' p : Nat.Primes,
      ‖inner ℂ (commonRadialPrimeField a p) x‖ ^ (2 : ℝ)) ≤
        ((1 : ℝ) * ‖x‖) ^ (2 : ℝ) := by
  have hterm (p : Nat.Primes) :
      ‖inner ℂ (commonRadialPrimeField a p) x‖ ^ (2 : ℝ) ≤
        ‖commonRadialPrimeField a p‖ ^ 2 * ‖x‖ ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith [norm_inner_le_norm (𝕜 := ℂ) (commonRadialPrimeField a p) x,
      norm_nonneg (inner ℂ (commonRadialPrimeField a p) x),
      norm_nonneg (commonRadialPrimeField a p), norm_nonneg x]
  calc
    (∑' p : Nat.Primes,
        ‖inner ℂ (commonRadialPrimeField a p) x‖ ^ (2 : ℝ)) ≤
        ∑' p : Nat.Primes, ‖commonRadialPrimeField a p‖ ^ 2 * ‖x‖ ^ 2 := by
      exact Summable.tsum_le_tsum hterm
        (summable_norm_inner_commonRadialPrimeField_sq a x)
        ((summable_norm_sq_commonRadialPrimeField a).mul_right (‖x‖ ^ 2))
    _ = (∑' p : Nat.Primes, ‖commonRadialPrimeField a p‖ ^ 2) * ‖x‖ ^ 2 := by
      rw [tsum_mul_right]
    _ = ((1 : ℝ) * ‖x‖) ^ (2 : ℝ) := by
      rw [tsum_norm_sq_commonRadialPrimeField]
      norm_num

/-- Adjont of literal prime-column synthesis: formula `(CRSHC.2)` as a bounded map from the
common radial carrier to the prime carrier. -/
def commonRadialPrimeSynthesis (a : {d : ℝ // 0 < d}) :
    lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ] CommonRadialSpace :=
  besselFamilySynthesisOperator (commonRadialPrimeField a)
    (summable_norm_inner_commonRadialPrimeField_sq a) zero_le_one
    (commonRadialPrimeField_bessel a)

def commonRadialPrimeReachability (a : {d : ℝ // 0 < d}) :
    CommonRadialSpace →L[ℂ] lp (fun _ : Nat.Primes => ℂ) 2 :=
  ContinuousLinearMap.adjoint (commonRadialPrimeSynthesis a)

theorem commonRadialPrimeSynthesis_basis
    (a : {d : ℝ // 0 < d}) (p : Nat.Primes) :
    commonRadialPrimeSynthesis a (HilbertSchmidt.lpBasis Nat.Primes p) =
      commonRadialPrimeField a p := by
  have hb : HTGeometry.ellTwoCoordinateBasis Nat.Primes =
      HilbertSchmidt.lpBasis Nat.Primes := rfl
  rw [← hb]
  exact
    besselFamilySynthesisOperator_coordinateBasis
      (commonRadialPrimeField a)
      (summable_norm_inner_commonRadialPrimeField_sq a) zero_le_one
      (commonRadialPrimeField_bessel a) p

theorem commonRadialPrimeSynthesis_isHilbertSchmidt (a : {d : ℝ // 0 < d}) :
    (commonRadialPrimeSynthesis a).IsHilbertSchmidt := by
  apply ContinuousLinearMap.isHilbertSchmidt_of_summable
    (HilbertSchmidt.lpBasis Nat.Primes)
  simpa only [commonRadialPrimeSynthesis_basis] using
    summable_norm_sq_commonRadialPrimeField a

theorem hsNormSq_commonRadialPrimeSynthesis (a : {d : ℝ // 0 < d}) :
    ContinuousLinearMap.hsNormSq (commonRadialPrimeSynthesis a) = 1 := by
  rw [ContinuousLinearMap.hsNormSq_eq (commonRadialPrimeSynthesis_isHilbertSchmidt a)
    (HilbertSchmidt.lpBasis Nat.Primes)]
  simpa only [commonRadialPrimeSynthesis_basis] using
    tsum_norm_sq_commonRadialPrimeField a

theorem commonRadialPrimeReachability_isHilbertSchmidt
    (a : {d : ℝ // 0 < d}) :
    (commonRadialPrimeReachability a).IsHilbertSchmidt := by
  exact (commonRadialPrimeSynthesis_isHilbertSchmidt a).adjoint

theorem hsNormSq_commonRadialPrimeReachability (a : {d : ℝ // 0 < d}) :
    ContinuousLinearMap.hsNormSq (commonRadialPrimeReachability a) = 1 := by
  rw [commonRadialPrimeReachability]
  rw [(commonRadialPrimeSynthesis_isHilbertSchmidt a).hsNormSq_adjoint]
  exact hsNormSq_commonRadialPrimeSynthesis a

/-- The reachability coordinate is the literal radial analysis coefficient. -/
theorem inner_basis_commonRadialPrimeReachability
    (a : {d : ℝ // 0 < d}) (p : Nat.Primes) (x : CommonRadialSpace) :
    inner ℂ (HilbertSchmidt.lpBasis Nat.Primes p)
        (commonRadialPrimeReachability a x) =
      inner ℂ (commonRadialPrimeField a p) x := by
  rw [commonRadialPrimeReachability,
    ContinuousLinearMap.adjoint_inner_right,
    commonRadialPrimeSynthesis_basis]

theorem normalizedStokesPrimeOperator_apply_basis_coordinate
    (a : {d : ℝ // 0 < d}) (p q : Nat.Primes) :
    normalizedStokesPrimeOperator a.property
        (HilbertSchmidt.lpBasis Nat.Primes q) p =
      normalizedStokesPrimeKernel a.1 (p, q) := by
  rw [normalizedStokesPrimeOperator, HilbertSchmidt.toOperator_apply,
    HilbertSchmidt.lpBasis_apply]
  rw [tsum_eq_single q]
  · simp
  · intro j hj
    simp [lp.single, hj]

/-- Exact prime covariance law `W_d W_d* = A_d`. -/
theorem commonRadialPrimeReachability_comp_synthesis
    (a : {d : ℝ // 0 < d}) :
    commonRadialPrimeReachability a ∘L commonRadialPrimeSynthesis a =
      normalizedStokesPrimeOperator a.property := by
  apply continuousLinearMap_eq_of_eq_on_hilbertBasis
    (HilbertSchmidt.lpBasis Nat.Primes)
  intro q
  apply lp.ext
  funext p
  have hleft := inner_basis_commonRadialPrimeReachability a p
    (commonRadialPrimeSynthesis a (HilbertSchmidt.lpBasis Nat.Primes q))
  rw [commonRadialPrimeSynthesis_basis,
    inner_commonRadialPrimeField_eq_normalizedStokesPrimeKernel] at hleft
  have hcoord :
      (commonRadialPrimeReachability a
        (commonRadialPrimeSynthesis a (HilbertSchmidt.lpBasis Nat.Primes q))) p =
        normalizedStokesPrimeKernel a.1 (p, q) := by
    rw [commonRadialPrimeSynthesis_basis]
    rw [HilbertSchmidt.lpBasis_apply, lp.inner_single_left] at hleft
    simpa using hleft
  change
    (commonRadialPrimeReachability a
      (commonRadialPrimeSynthesis a (HilbertSchmidt.lpBasis Nat.Primes q))) p =
        normalizedStokesPrimeOperator a.property
          (HilbertSchmidt.lpBasis Nat.Primes q) p
  rw [hcoord, normalizedStokesPrimeOperator_apply_basis_coordinate]

theorem normalizedStokesPrimeOperator_isPositive'
    (a : {d : ℝ // 0 < d}) :
    (normalizedStokesPrimeOperator a.property).IsPositive := by
  rw [← commonRadialPrimeReachability_comp_synthesis a]
  change ((ContinuousLinearMap.adjoint (commonRadialPrimeSynthesis a)) ∘L
    commonRadialPrimeSynthesis a).IsPositive
  have hnonneg := ContinuousLinearMap.adjoint_comp_self_nonneg
    (commonRadialPrimeSynthesis a)
  rw [ContinuousLinearMap.le_def, sub_zero,
    ContinuousLinearMap.isPositive_iff] at hnonneg
  rw [ContinuousLinearMap.isPositive_iff]
  exact hnonneg

theorem normalizedStokesPrimeOperator_memSchattenClass_one'
    (a : {d : ℝ // 0 < d}) :
    MemSchattenClass 1 (normalizedStokesPrimeOperator a.property) := by
  rw [← commonRadialPrimeReachability_comp_synthesis a]
  change MemSchattenClass 1
    ((ContinuousLinearMap.adjoint (commonRadialPrimeSynthesis a)) ∘L
      commonRadialPrimeSynthesis a)
  apply (memRectSchattenClass_iff_memSchattenClass 1 _).mp
  exact memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted
    (commonRadialPrimeSynthesis_isHilbertSchmidt a)
    (commonRadialPrimeSynthesis_isHilbertSchmidt a).adjoint

theorem opTrace_normalizedStokesPrimeOperator
    (a : {d : ℝ // 0 < d}) :
    ContinuousLinearMap.opTrace (normalizedStokesPrimeOperator a.property) = 1 := by
  rw [← commonRadialPrimeReachability_comp_synthesis a]
  change ContinuousLinearMap.opTrace
    ((ContinuousLinearMap.adjoint (commonRadialPrimeSynthesis a)) ∘L
      commonRadialPrimeSynthesis a) = 1
  rw [ContinuousLinearMap.opTrace_adjoint_comp_self]
  have hreal := ContinuousLinearMap.hsInner_self_re
    (commonRadialPrimeSynthesis_isHilbertSchmidt a)
  rw [hsNormSq_commonRadialPrimeSynthesis] at hreal
  have hstar := ContinuousLinearMap.hsInner_conj_symm
    (commonRadialPrimeSynthesis a) (commonRadialPrimeSynthesis a)
  have him : (ContinuousLinearMap.hsInner
      (commonRadialPrimeSynthesis a) (commonRadialPrimeSynthesis a)).im = 0 := by
    apply_fun Complex.im at hstar
    change (ContinuousLinearMap.hsInner
      (commonRadialPrimeSynthesis a) (commonRadialPrimeSynthesis a)).im =
        -(ContinuousLinearMap.hsInner
          (commonRadialPrimeSynthesis a) (commonRadialPrimeSynthesis a)).im at hstar
    linarith
  exact Complex.ext (by simpa using hreal) (by simpa using him)

/-- Any two distinct prime radial modes are genuinely independent. -/
theorem commonRadialPrimeField_linearIndependent_pair
    (a : {d : ℝ // 0 < d}) {p q : Nat.Primes} (hpq : p ≠ q) :
    LinearIndependent ℂ ![commonRadialPrimeField a p,
      commonRadialPrimeField a q] := by
  rw [← HTGeometry.projectiveGramTangentEnergy_pos_iff_linearIndependent_pair]
  have hpval : (p : ℕ) ≠ (q : ℕ) := by
    intro h
    exact hpq (Subtype.ext h)
  have hlog : Real.log (p : ℝ) ≠ Real.log (q : ℝ) := by
    intro h
    have hcast : (p : ℝ) = (q : ℝ) :=
      Real.strictMonoOn_log.injOn
        (by
          show 0 < (p : ℝ)
          exact_mod_cast p.property.pos)
        (by
          show 0 < (q : ℝ)
          exact_mod_cast q.property.pos) h
    exact hpval (by exact_mod_cast hcast)
  have hcoh : routePBaseCauchyCubicNormalizedCoherenceSq
      (Real.log (p : ℝ)) (Real.log (q : ℝ)) 0 < 1 :=
    routePBaseCauchyCubicNormalizedCoherenceSq_lt_one
      (Real.log_pos (by exact_mod_cast p.property.one_lt))
      (Real.log_pos (by exact_mod_cast q.property.one_lt)) (Or.inl hlog)
  have hwp := routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_pos
    a.property p
  have hwq := routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_pos
    a.property q
  have hJ := gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos
    a.property
  unfold HTGeometry.projectiveGramTangentEnergy
  rw [norm_sq_commonRadialPrimeField, norm_sq_commonRadialPrimeField,
    Complex.sq_norm,
    inner_commonRadialPrimeField_eq_normalizedStokesPrimeKernel,
    normalizedStokesPrimeKernel, Complex.normSq_div,
    normSq_routePPrimitiveGammaJuliaStokesCofinalChildKernel a.property,
    Complex.normSq_ofReal]
  field_simp [hJ.ne']
  simpa using mul_pos (mul_pos hwp hwq) (sub_pos.mpr hcoh)

/-- Strict radial contraction: the Hilbert--Schmidt unit mass occupies at least two independent
prime directions, so no unit singular value can consume it all. -/
theorem norm_commonRadialPrimeSynthesis_lt_one
    (a : {d : ℝ // 0 < d}) :
    ‖commonRadialPrimeSynthesis a‖ < 1 := by
  let S := commonRadialPrimeSynthesis a
  have hS : S.IsHilbertSchmidt := commonRadialPrimeSynthesis_isHilbertSchmidt a
  have hhs : S.hsNorm = 1 := by
    have hsq := ContinuousLinearMap.sq_hsNorm S
    rw [show S.hsNormSq = 1 by
      exact hsNormSq_commonRadialPrimeSynthesis a] at hsq
    nlinarith [ContinuousLinearMap.hsNorm_nonneg S]
  have hnorm_le : ‖S‖ ≤ 1 := by
    simpa [hhs] using ContinuousLinearMap.norm_le_hsNorm hS
  by_contra hstrict
  have hnorm : ‖S‖ = 1 := le_antisymm hnorm_le (not_lt.mp hstrict)
  let A : lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ]
      lp (fun _ : Nat.Primes => ℂ) 2 :=
    ContinuousLinearMap.adjoint S ∘L S
  have hAeq : A = normalizedStokesPrimeOperator a.property := by
    simpa [A, S, commonRadialPrimeReachability] using
      commonRadialPrimeReachability_comp_synthesis a
  have hAnorm : ‖A‖ = 1 := by
    change ‖ContinuousLinearMap.adjoint S ∘L S‖ = 1
    rw [ContinuousLinearMap.norm_adjoint_comp_self, hnorm]
    norm_num
  have hApos : A.IsPositive := by
    rw [hAeq]
    exact normalizedStokesPrimeOperator_isPositive' a
  have hAcpt : IsCompactOperator A := by
    rw [hAeq]
    exact (normalizedStokesPrimeOperator_memSchattenClass_one' a).isCompactOperator
      zero_lt_one
  have hAne : A ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hAnorm
    norm_num at hAnorm
  obtain ⟨mu, x, hmuabs, hx, heig⟩ :=
    ContinuousLinearMap.exists_unit_eigenvector_norm hAcpt hApos.isSymmetric hAne
  have hmu_nonneg : 0 ≤ mu := by
    have hquad := ((ContinuousLinearMap.isPositive_iff A).mp hApos).2 x
    have hre := (Complex.nonneg_iff.mp hquad).1
    rw [heig, inner_smul_left, inner_self_eq_norm_sq_to_K, hx] at hre
    norm_num at hre
    simpa using hre
  have hmu : mu = 1 := by
    rw [abs_of_nonneg hmu_nonneg, hAnorm] at hmuabs
    exact hmuabs
  have hnormSx : ‖S x‖ ^ 2 = 1 := by
    have hadj := ContinuousLinearMap.adjoint_inner_right S x (S x)
    have hinner : inner ℂ x (A x) = inner ℂ (S x) (S x) := by
      simpa [A] using hadj
    rw [heig, inner_smul_right, hmu] at hinner
    have hre := congrArg Complex.re hinner
    simp [inner_self_eq_norm_sq_to_K, hx] at hre
    norm_cast at hre
    exact hre.symm
  let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  let p3 : Nat.Primes := ⟨3, Nat.prime_three⟩
  let e2 := HilbertSchmidt.lpBasis Nat.Primes p2
  let e3 := HilbertSchmidt.lpBasis Nat.Primes p3
  have hp23 : p2 ≠ p3 := by
    intro h
    have := congrArg Subtype.val h
    norm_num [p2, p3] at this
  have hLI : LinearIndependent ℂ ![S e2, S e3] := by
    simpa [S, e2, e3, commonRadialPrimeSynthesis_basis] using
      commonRadialPrimeField_linearIndependent_pair a hp23
  obtain ⟨y, hyorth, hyS⟩ : ∃ y,
      inner ℂ x y = 0 ∧ S y ≠ 0 := by
    by_contra hnone
    push Not at hnone
    let y2 := e2 - inner ℂ x e2 • x
    let y3 := e3 - inner ℂ x e3 • x
    have hy2orth : inner ℂ x y2 = 0 := by
      simp [y2, hx]
    have hy3orth : inner ℂ x y3 = 0 := by
      simp [y3, hx]
    have hSy2 : S y2 = 0 := hnone y2 hy2orth
    have hSy3 : S y3 = 0 := hnone y3 hy3orth
    have hSe2 : S e2 = inner ℂ x e2 • S x := by
      apply sub_eq_zero.mp
      simpa [y2, map_sub, map_smul] using hSy2
    have hSe3 : S e3 = inner ℂ x e3 • S x := by
      apply sub_eq_zero.mp
      simpa [y3, map_sub, map_smul] using hSy3
    have hrel : inner ℂ x e3 • S e2 +
        (-inner ℂ x e2) • S e3 = 0 := by
      rw [hSe2, hSe3]
      simp [smul_smul, mul_comm]
    have hcoeff := LinearIndependent.pair_iff.mp hLI
      (inner ℂ x e3) (-inner ℂ x e2) hrel
    have hxe2 : inner ℂ x e2 = 0 := neg_eq_zero.mp hcoeff.2
    have hSe2zero : S e2 = 0 := by simp [hSe2, hxe2]
    have honezero := LinearIndependent.pair_iff.mp hLI (1 : ℂ) 0 (by
      simp [hSe2zero])
    exact one_ne_zero honezero.1
  have hy0 : y ≠ 0 := by
    intro hzero
    apply hyS
    rw [hzero, map_zero]
  let v : Fin 2 → lp (fun _ : Nat.Primes => ℂ) 2 := ![x, y]
  have hvne : ∀ i, v i ≠ 0 := by
    intro i
    fin_cases i
    · change x ≠ 0
      exact norm_ne_zero_iff.mp (by simp [hx])
    · change y ≠ 0
      exact hy0
  have hvorth : ∀ i j, i ≠ j → inner ℂ (v i) (v j) = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hyorth
    · change inner ℂ y x = 0
      have hconj := inner_conj_symm (𝕜 := ℂ) x y
      rw [hyorth] at hconj
      apply_fun star at hconj
      simpa using hconj
    · exact (hij rfl).elim
  have hvon := orthonormal_normalize hvne hvorth
  have henergy := sum_norm_sq_apply_le_hsNormSq hS hvon
  rw [show S.hsNormSq = 1 by
    exact hsNormSq_commonRadialPrimeSynthesis a] at henergy
  simp only [Fin.sum_univ_two] at henergy
  change ‖S (((‖x‖ : ℂ)⁻¹) • x)‖ ^ 2 +
      ‖S (((‖y‖ : ℂ)⁻¹) • y)‖ ^ 2 ≤ 1 at henergy
  have hxnormCast : ((‖x‖ : ℂ)⁻¹) = 1 := by simp [hx]
  rw [hxnormCast, one_smul, hnormSx] at henergy
  have hynorm : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy0
  have hyimage : S (((‖y‖ : ℂ)⁻¹) • y) ≠ 0 := by
    rw [map_smul]
    exact smul_ne_zero (by
      exact inv_ne_zero (Complex.ofReal_ne_zero.mpr hynorm.ne')) hyS
  have hyenergy : 0 < ‖S (((‖y‖ : ℂ)⁻¹) • y)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hyimage)
  nlinarith

/-- Operator adjunction preserves norm.  This local infrastructure proof derives the equality
from the two C-star identities and submultiplicativity, without a finite-dimensional assumption. -/
theorem norm_adjoint_eq_norm
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) : ‖ContinuousLinearMap.adjoint T‖ = ‖T‖ := by
  by_cases hT : T = 0
  · simp [hT]
  have hTpos : 0 < ‖T‖ := norm_pos_iff.mpr hT
  have hAdj : ContinuousLinearMap.adjoint T ≠ 0 := by
    intro hzero
    have hzero' := congrArg ContinuousLinearMap.adjoint hzero
    rw [ContinuousLinearMap.adjoint_adjoint] at hzero'
    exact hT (by simpa using hzero')
  have hAdjpos : 0 < ‖ContinuousLinearMap.adjoint T‖ := norm_pos_iff.mpr hAdj
  have hforward := ContinuousLinearMap.opNorm_comp_le
    (ContinuousLinearMap.adjoint T) T
  rw [ContinuousLinearMap.norm_adjoint_comp_self] at hforward
  have hreverse := ContinuousLinearMap.opNorm_comp_le T
    (ContinuousLinearMap.adjoint T)
  have hcstar := ContinuousLinearMap.norm_adjoint_comp_self
    (ContinuousLinearMap.adjoint T)
  rw [ContinuousLinearMap.adjoint_adjoint] at hcstar
  rw [hcstar] at hreverse
  nlinarith [norm_nonneg T, norm_nonneg (ContinuousLinearMap.adjoint T)]

theorem norm_commonRadialPrimeReachability_lt_one
    (a : {d : ℝ // 0 < d}) :
    ‖commonRadialPrimeReachability a‖ < 1 := by
  rw [commonRadialPrimeReachability, norm_adjoint_eq_norm]
  exact norm_commonRadialPrimeSynthesis_lt_one a

/-- A Hilbert--Schmidt range covariance is trace class. -/
theorem rangeCovariance_memSchattenClass_one_of_hilbertSchmidt
    {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : E →L[ℂ] H} (hT : T.IsHilbertSchmidt) :
    MemSchattenClass 1 (rangeCovariance T) := by
  rw [rangeCovariance]
  apply (memRectSchattenClass_iff_memSchattenClass 1 _).mp
  exact memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted
    hT.adjoint hT

/-- Exact trace of a Hilbert--Schmidt range covariance. -/
theorem re_opTrace_rangeCovariance_eq_hsNormSq
    {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : E →L[ℂ] H} (hT : T.IsHilbertSchmidt) :
    (ContinuousLinearMap.opTrace (rangeCovariance T)).re =
      ContinuousLinearMap.hsNormSq T := by
  have htrace := ContinuousLinearMap.re_opTrace_adjoint_comp_self hT.adjoint
  rw [ContinuousLinearMap.adjoint_adjoint, hT.hsNormSq_adjoint] at htrace
  exact htrace

/-- Canonical common-radial synthesis carrying the literal Burnol source into prime coordinates. -/
abbrev CommonRadialBurnolSourceSpace :=
  Lp ℂ 2 (@Measure.count RoutePPrimitiveIndex
    instMeasurableSpaceRoutePPrimitiveIndex)

def commonRadialPrimeSourceSynthesis (a : {d : ℝ // 0 < d}) :
    CommonRadialBurnolSourceSpace →L[ℂ]
      lp (fun _ : Nat.Primes => ℂ) 2 :=
  commonRadialPrimeReachability a ∘L routePPrimitiveBurnolBaseSynthesis

/-- Canonical common-radial prime symbol `W_d S_base W_d*`. -/
def commonRadialPrimeSourceSymbol (a : {d : ℝ // 0 < d}) :
    lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ]
      lp (fun _ : Nat.Primes => ℂ) 2 :=
  rangeCovariance (commonRadialPrimeSourceSynthesis a)

theorem commonRadialPrimeSourceSynthesis_isHilbertSchmidt
    (a : {d : ℝ // 0 < d}) :
    (commonRadialPrimeSourceSynthesis a).IsHilbertSchmidt := by
  exact routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt.comp_left
    (commonRadialPrimeReachability a)

/-- Exact Burnol sandwich factorization of the canonical prime symbol. -/
theorem commonRadialPrimeSourceSymbol_eq_sandwich
    (a : {d : ℝ // 0 < d}) :
    commonRadialPrimeSourceSymbol a =
      commonRadialPrimeReachability a ∘L
        routePPrimitiveBurnolBaseNuclearSource ∘L
          commonRadialPrimeSynthesis a := by
  unfold commonRadialPrimeSourceSymbol commonRadialPrimeSourceSynthesis
    routePPrimitiveBurnolBaseNuclearSource rangeCovariance
  rw [ContinuousLinearMap.adjoint_comp]
  rw [show ContinuousLinearMap.adjoint (commonRadialPrimeReachability a) =
      commonRadialPrimeSynthesis a by
    rw [commonRadialPrimeReachability,
      ContinuousLinearMap.adjoint_adjoint]]
  ext x
  rfl

theorem commonRadialPrimeSourceSymbol_isPositive
    (a : {d : ℝ // 0 < d}) :
    (commonRadialPrimeSourceSymbol a).IsPositive :=
  rangeCovariance_isPositive (commonRadialPrimeSourceSynthesis a)

theorem commonRadialPrimeSourceSymbol_memSchattenClass_one
    (a : {d : ℝ // 0 < d}) :
    MemSchattenClass 1 (commonRadialPrimeSourceSymbol a) :=
  rangeCovariance_memSchattenClass_one_of_hilbertSchmidt
    (commonRadialPrimeSourceSynthesis_isHilbertSchmidt a)

set_option maxHeartbeats 800000 in
/-- Every canonical prime matrix entry is the convergent sum of its positive primitive-depth
radial overlaps. -/
theorem inner_basis_commonRadialPrimeSourceSymbol_eq_tsum_overlap
    (a : {d : ℝ // 0 < d}) (p q : Nat.Primes) :
    inner ℂ (HilbertSchmidt.lpBasis Nat.Primes p)
        (commonRadialPrimeSourceSymbol a
          (HilbertSchmidt.lpBasis Nat.Primes q)) =
      ∑' pe : RoutePPrimitiveIndex,
        ((commonRadialPrimeBurnolOverlap a p pe *
          commonRadialPrimeBurnolOverlap a q pe : ℝ) : ℂ) := by
  rw [commonRadialPrimeSourceSymbol_eq_sandwich]
  simp only [ContinuousLinearMap.comp_apply]
  rw [commonRadialPrimeSynthesis_basis,
    inner_basis_commonRadialPrimeReachability]
  letI : MeasurableSpace RoutePPrimitiveIndex :=
    instMeasurableSpaceRoutePPrimitiveIndex
  rw [routePPrimitiveBurnolBaseNuclearSource,
    routePPrimitiveBurnolBaseSynthesis,
    rangeCovariance_l2Synthesis_apply]
  let mu :=
    @Measure.count RoutePPrimitiveIndex instMeasurableSpaceRoutePPrimitiveIndex
  let u := routePPrimitiveBurnolBaseFieldLp
  let gp := commonRadialPrimeField a p
  let gq := commonRadialPrimeField a q
  have hfield : ∀ᵐ pe ∂mu, u pe = routePPrimitiveBurnolBaseField pe := by
    change ∀ᵐ pe ∂(@Measure.count RoutePPrimitiveIndex
      instMeasurableSpaceRoutePPrimitiveIndex),
        routePPrimitiveBurnolBaseFieldLp pe = routePPrimitiveBurnolBaseField pe
    exact memLp_two_routePPrimitiveBurnolBaseField.coeFn_toLp
  have hactualVec : Integrable (fun pe =>
      inner ℂ (routePPrimitiveBurnolBaseField pe) gq •
        routePPrimitiveBurnolBaseField pe) mu := by
    rw [integrable_count_iff]
    have hmajor : Summable fun pe : RoutePPrimitiveIndex =>
        ‖gq‖ * ‖routePPrimitiveBurnolBaseField pe‖ ^ 2 :=
      summable_norm_sq_routePPrimitiveBurnolBaseField.mul_left _
    refine Summable.of_nonneg_of_le (fun pe => norm_nonneg _) (fun pe => ?_) hmajor
    rw [norm_smul]
    have hi := norm_inner_le_norm (𝕜 := ℂ)
      (routePPrimitiveBurnolBaseField pe) gq
    nlinarith [norm_nonneg (inner ℂ (routePPrimitiveBurnolBaseField pe) gq),
      norm_nonneg (routePPrimitiveBurnolBaseField pe), norm_nonneg gq]
  have hvec : Integrable (fun pe => inner ℂ (u pe) gq • u pe) mu := by
    refine hactualVec.congr ?_
    filter_upwards [hfield] with pe hpe
    rw [hpe]
  have hpoint : ∀ᵐ pe ∂mu,
      inner ℂ gp (inner ℂ (u pe) gq • u pe) =
        ((commonRadialPrimeBurnolOverlap a p pe *
          commonRadialPrimeBurnolOverlap a q pe : ℝ) : ℂ) := by
    filter_upwards [hfield] with pe hpe
    rw [hpe, inner_smul_right,
      inner_commonRadialPrimeField_routePPrimitiveBurnolBaseField]
    have hraw := inner_commonRadialPrimeField_routePPrimitiveBurnolBaseField
      a q pe
    have hsymm := inner_conj_symm (𝕜 := ℂ) gq
      (routePPrimitiveBurnolBaseField pe)
    rw [hraw] at hsymm
    apply_fun starRingEnd ℂ at hsymm
    have hreverse : inner ℂ (routePPrimitiveBurnolBaseField pe) gq =
        (commonRadialPrimeBurnolOverlap a q pe : ℂ) := by
      simpa using hsymm
    rw [hreverse]
    simp
    ring
  have hactual : Integrable (fun pe =>
      ((commonRadialPrimeBurnolOverlap a p pe *
        commonRadialPrimeBurnolOverlap a q pe : ℝ) : ℂ)) mu :=
    integrable_count_iff.mpr (by
      refine (summable_commonRadialPrimeBurnolOverlap_mul a p q).congr ?_
      intro pe
      rw [norm_real, Real.norm_eq_abs,
        abs_of_pos (mul_pos
          (commonRadialPrimeBurnolOverlap_pos a p pe)
          (commonRadialPrimeBurnolOverlap_pos a q pe))])
  change inner ℂ gp
    (∫ pe, inner ℂ (u pe) gq • u pe ∂mu) = _
  calc
    inner ℂ gp (∫ pe, inner ℂ (u pe) gq • u pe ∂mu) =
        ∫ pe, inner ℂ gp (inner ℂ (u pe) gq • u pe) ∂mu := by
      rw [integral_inner hvec gp]
    _ = ∫ pe, ((commonRadialPrimeBurnolOverlap a p pe *
          commonRadialPrimeBurnolOverlap a q pe : ℝ) : ℂ) ∂mu :=
      integral_congr_ae hpoint
    _ = ∑' pe : RoutePPrimitiveIndex,
        ((commonRadialPrimeBurnolOverlap a p pe *
          commonRadialPrimeBurnolOverlap a q pe : ℝ) : ℂ) := by
      rw [integral_countable hactual]
      simp [mu]

theorem re_inner_basis_commonRadialPrimeSourceSymbol_pos
    (a : {d : ℝ // 0 < d}) (p q : Nat.Primes) :
    0 < (inner ℂ (HilbertSchmidt.lpBasis Nat.Primes p)
      (commonRadialPrimeSourceSymbol a
        (HilbertSchmidt.lpBasis Nat.Primes q))).re := by
  rw [inner_basis_commonRadialPrimeSourceSymbol_eq_tsum_overlap]
  have hsumR := summable_commonRadialPrimeBurnolOverlap_mul a p q
  have hsumC : Summable fun pe : RoutePPrimitiveIndex =>
      ((commonRadialPrimeBurnolOverlap a p pe *
        commonRadialPrimeBurnolOverlap a q pe : ℝ) : ℂ) :=
    Complex.summable_ofReal.mpr hsumR
  have hre := Complex.reCLM.map_tsum hsumC
  change (∑' pe : RoutePPrimitiveIndex,
      ((commonRadialPrimeBurnolOverlap a p pe *
        commonRadialPrimeBurnolOverlap a q pe : ℝ) : ℂ)).re =
      ∑' pe : RoutePPrimitiveIndex,
        commonRadialPrimeBurnolOverlap a p pe *
          commonRadialPrimeBurnolOverlap a q pe at hre
  rw [hre]
  let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  exact hsumR.tsum_pos
    (fun pe => mul_nonneg (commonRadialPrimeBurnolOverlap_pos a p pe).le
      (commonRadialPrimeBurnolOverlap_pos a q pe).le)
    (p2, 0)
    (mul_pos (commonRadialPrimeBurnolOverlap_pos a p (p2, 0))
      (commonRadialPrimeBurnolOverlap_pos a q (p2, 0)))

theorem im_inner_basis_commonRadialPrimeSourceSymbol_eq_zero
    (a : {d : ℝ // 0 < d}) (p q : Nat.Primes) :
    (inner ℂ (HilbertSchmidt.lpBasis Nat.Primes p)
      (commonRadialPrimeSourceSymbol a
        (HilbertSchmidt.lpBasis Nat.Primes q))).im = 0 := by
  rw [inner_basis_commonRadialPrimeSourceSymbol_eq_tsum_overlap]
  have him := Complex.imCLM.map_tsum
    (Complex.summable_ofReal.mpr
      (summable_commonRadialPrimeBurnolOverlap_mul a p q))
  change (∑' pe : RoutePPrimitiveIndex,
      ((commonRadialPrimeBurnolOverlap a p pe *
        commonRadialPrimeBurnolOverlap a q pe : ℝ) : ℂ)).im =
      ∑' _pe : RoutePPrimitiveIndex, (0 : ℝ) at him
  rw [him]
  simp

theorem re_opTrace_commonRadialPrimeSourceSymbol_eq_hsNormSq
    (a : {d : ℝ // 0 < d}) :
    (ContinuousLinearMap.opTrace (commonRadialPrimeSourceSymbol a)).re =
      ContinuousLinearMap.hsNormSq (commonRadialPrimeSourceSynthesis a) :=
  re_opTrace_rangeCovariance_eq_hsNormSq
    (commonRadialPrimeSourceSynthesis_isHilbertSchmidt a)

theorem re_opTrace_commonRadialPrimeSourceSymbol_pos
    (a : {d : ℝ // 0 < d}) :
    0 < (ContinuousLinearMap.opTrace (commonRadialPrimeSourceSymbol a)).re := by
  rw [re_opTrace_commonRadialPrimeSourceSymbol_eq_hsNormSq]
  have hQ := commonRadialPrimeSourceSynthesis_isHilbertSchmidt a
  have hQne : commonRadialPrimeSourceSynthesis a ≠ 0 := by
    intro hzero
    have hCzero : commonRadialPrimeSourceSymbol a = 0 := by
      simp [commonRadialPrimeSourceSymbol, rangeCovariance, hzero]
    let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
    have hentry := re_inner_basis_commonRadialPrimeSourceSymbol_pos a p2 p2
    rw [hCzero] at hentry
    simp at hentry
  have hnonneg := ContinuousLinearMap.hsNormSq_nonneg
    (commonRadialPrimeSourceSynthesis a)
  exact lt_of_le_of_ne hnonneg
    (fun h => hQne ((ContinuousLinearMap.hsNormSq_eq_zero_iff hQ).mp h.symm))

theorem hsNormSq_commonRadialPrimeSourceSynthesis_le
    (a : {d : ℝ // 0 < d}) :
    ContinuousLinearMap.hsNormSq (commonRadialPrimeSourceSynthesis a) ≤
      ‖commonRadialPrimeReachability a‖ ^ 2 *
        routePPrimitiveBaseCauchyCubicTraceBudget := by
  simpa [commonRadialPrimeSourceSynthesis,
    hsNormSq_routePPrimitiveBurnolBaseSynthesis_eq_budget] using
      ContinuousLinearMap.hsNormSq_comp_left_le
        routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt
        (commonRadialPrimeReachability a)

theorem re_opTrace_commonRadialPrimeSourceSymbol_le
    (a : {d : ℝ // 0 < d}) :
    (ContinuousLinearMap.opTrace (commonRadialPrimeSourceSymbol a)).re ≤
      ‖commonRadialPrimeReachability a‖ ^ 2 *
        routePPrimitiveBaseCauchyCubicTraceBudget := by
  rw [re_opTrace_commonRadialPrimeSourceSymbol_eq_hsNormSq]
  exact hsNormSq_commonRadialPrimeSourceSynthesis_le a

theorem re_opTrace_commonRadialPrimeSourceSymbol_lt_budget
    (a : {d : ℝ // 0 < d}) :
    (ContinuousLinearMap.opTrace (commonRadialPrimeSourceSymbol a)).re <
      routePPrimitiveBaseCauchyCubicTraceBudget := by
  calc
    (ContinuousLinearMap.opTrace (commonRadialPrimeSourceSymbol a)).re ≤
        ‖commonRadialPrimeReachability a‖ ^ 2 *
          routePPrimitiveBaseCauchyCubicTraceBudget :=
      re_opTrace_commonRadialPrimeSourceSymbol_le a
    _ < routePPrimitiveBaseCauchyCubicTraceBudget := by
      have hn := norm_commonRadialPrimeReachability_lt_one a
      have hb := routePPrimitiveBaseCauchyCubicTraceBudget_pos
      have hn2 : ‖commonRadialPrimeReachability a‖ ^ 2 < 1 := by
        nlinarith [norm_nonneg (commonRadialPrimeReachability a)]
      rw [mul_lt_iff_lt_one_left hb]
      exact hn2

theorem re_opTrace_commonRadialPrimeSourceSymbol_lt_one
    (a : {d : ℝ // 0 < d}) :
    (ContinuousLinearMap.opTrace (commonRadialPrimeSourceSymbol a)).re < 1 :=
  lt_trans (re_opTrace_commonRadialPrimeSourceSymbol_lt_budget a)
    routePPrimitiveBaseCauchyCubicTraceBudget_lt_one

/-- Contractive common-radial endomorphisms allowed in the exact admissible class. -/
abbrev CommonRadialContraction :=
  {V : CommonRadialSpace →L[ℂ] CommonRadialSpace // ‖V‖ ≤ 1}

/-- Contracted synthesis `W_d V B` from the complete primitive Burnol source. -/
def commonRadialPrimeContractedSynthesis (a : {d : ℝ // 0 < d})
    (V : CommonRadialContraction) :
    CommonRadialBurnolSourceSpace →L[ℂ]
      lp (fun _ : Nat.Primes => ℂ) 2 :=
  commonRadialPrimeReachability a ∘L V.1 ∘L
    routePPrimitiveBurnolBaseSynthesis

/-- Exact contractive-class covariance `W_d V S_base V* W_d*`. -/
def commonRadialPrimeContractedSymbol (a : {d : ℝ // 0 < d})
    (V : CommonRadialContraction) :
    lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ]
      lp (fun _ : Nat.Primes => ℂ) 2 :=
  rangeCovariance (commonRadialPrimeContractedSynthesis a V)

theorem commonRadialPrimeContractedSynthesis_isHilbertSchmidt
    (a : {d : ℝ // 0 < d}) (V : CommonRadialContraction) :
    (commonRadialPrimeContractedSynthesis a V).IsHilbertSchmidt := by
  exact (routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt.comp_left V.1).comp_left
    (commonRadialPrimeReachability a)

theorem commonRadialPrimeContractedSymbol_eq_sandwich
    (a : {d : ℝ // 0 < d}) (V : CommonRadialContraction) :
    commonRadialPrimeContractedSymbol a V =
      commonRadialPrimeReachability a ∘L V.1 ∘L
        routePPrimitiveBurnolBaseNuclearSource ∘L
          ContinuousLinearMap.adjoint V.1 ∘L commonRadialPrimeSynthesis a := by
  unfold commonRadialPrimeContractedSymbol commonRadialPrimeContractedSynthesis
    routePPrimitiveBurnolBaseNuclearSource rangeCovariance
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp]
  rw [show ContinuousLinearMap.adjoint (commonRadialPrimeReachability a) =
      commonRadialPrimeSynthesis a by
    rw [commonRadialPrimeReachability,
      ContinuousLinearMap.adjoint_adjoint]]
  ext x
  rfl

theorem commonRadialPrimeContractedSymbol_isPositive
    (a : {d : ℝ // 0 < d}) (V : CommonRadialContraction) :
    (commonRadialPrimeContractedSymbol a V).IsPositive :=
  rangeCovariance_isPositive (commonRadialPrimeContractedSynthesis a V)

theorem commonRadialPrimeContractedSymbol_memSchattenClass_one
    (a : {d : ℝ // 0 < d}) (V : CommonRadialContraction) :
    MemSchattenClass 1 (commonRadialPrimeContractedSymbol a V) :=
  rangeCovariance_memSchattenClass_one_of_hilbertSchmidt
    (commonRadialPrimeContractedSynthesis_isHilbertSchmidt a V)

theorem re_opTrace_commonRadialPrimeContractedSymbol_eq_hsNormSq
    (a : {d : ℝ // 0 < d}) (V : CommonRadialContraction) :
    (ContinuousLinearMap.opTrace (commonRadialPrimeContractedSymbol a V)).re =
      ContinuousLinearMap.hsNormSq (commonRadialPrimeContractedSynthesis a V) :=
  re_opTrace_rangeCovariance_eq_hsNormSq
    (commonRadialPrimeContractedSynthesis_isHilbertSchmidt a V)

theorem hsNormSq_commonRadialPrimeContractedSynthesis_le
    (a : {d : ℝ // 0 < d}) (V : CommonRadialContraction) :
    ContinuousLinearMap.hsNormSq (commonRadialPrimeContractedSynthesis a V) ≤
      ‖commonRadialPrimeReachability a‖ ^ 2 * ‖V.1‖ ^ 2 *
        routePPrimitiveBaseCauchyCubicTraceBudget := by
  have hinner := ContinuousLinearMap.hsNormSq_comp_left_le
    routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt V.1
  have houter := ContinuousLinearMap.hsNormSq_comp_left_le
    (routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt.comp_left V.1)
    (commonRadialPrimeReachability a)
  rw [hsNormSq_routePPrimitiveBurnolBaseSynthesis_eq_budget] at hinner
  calc
    ContinuousLinearMap.hsNormSq (commonRadialPrimeContractedSynthesis a V) ≤
        ‖commonRadialPrimeReachability a‖ ^ 2 *
          ContinuousLinearMap.hsNormSq
            (V.1 ∘L routePPrimitiveBurnolBaseSynthesis) := by
      simpa [commonRadialPrimeContractedSynthesis] using houter
    _ ≤ ‖commonRadialPrimeReachability a‖ ^ 2 *
        (‖V.1‖ ^ 2 * routePPrimitiveBaseCauchyCubicTraceBudget) := by
      exact mul_le_mul_of_nonneg_left hinner (sq_nonneg _)
    _ = ‖commonRadialPrimeReachability a‖ ^ 2 * ‖V.1‖ ^ 2 *
        routePPrimitiveBaseCauchyCubicTraceBudget := by ring

theorem re_opTrace_commonRadialPrimeContractedSymbol_le
    (a : {d : ℝ // 0 < d}) (V : CommonRadialContraction) :
    (ContinuousLinearMap.opTrace (commonRadialPrimeContractedSymbol a V)).re ≤
      ‖commonRadialPrimeReachability a‖ ^ 2 * ‖V.1‖ ^ 2 *
        routePPrimitiveBaseCauchyCubicTraceBudget := by
  rw [re_opTrace_commonRadialPrimeContractedSymbol_eq_hsNormSq]
  exact hsNormSq_commonRadialPrimeContractedSynthesis_le a V

theorem re_opTrace_commonRadialPrimeContractedSymbol_lt_one
    (a : {d : ℝ // 0 < d}) (V : CommonRadialContraction) :
    (ContinuousLinearMap.opTrace (commonRadialPrimeContractedSymbol a V)).re < 1 := by
  have hw := norm_commonRadialPrimeReachability_lt_one a
  have hv := V.property
  have hbpos := routePPrimitiveBaseCauchyCubicTraceBudget_pos
  have hblt := routePPrimitiveBaseCauchyCubicTraceBudget_lt_one
  have hw2 : ‖commonRadialPrimeReachability a‖ ^ 2 < 1 := by
    nlinarith [norm_nonneg (commonRadialPrimeReachability a)]
  have hv2 : ‖V.1‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg V.1]
  have hcoef : ‖commonRadialPrimeReachability a‖ ^ 2 * ‖V.1‖ ^ 2 < 1 :=
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hv2 (sq_nonneg _)) (by simpa using hw2)
  calc
    (ContinuousLinearMap.opTrace (commonRadialPrimeContractedSymbol a V)).re ≤
        ‖commonRadialPrimeReachability a‖ ^ 2 * ‖V.1‖ ^ 2 *
          routePPrimitiveBaseCauchyCubicTraceBudget :=
      re_opTrace_commonRadialPrimeContractedSymbol_le a V
    _ < routePPrimitiveBaseCauchyCubicTraceBudget := by
      rw [mul_lt_iff_lt_one_left hbpos]
      exact hcoef
    _ < 1 := hblt

/-! ## Recurrent history lift -/

/-- History written as an outer `ℓ²` sum of prime `ℓ²` slices. -/
abbrev CommonRadialHistorySlices :=
  lp (fun _ : ℕ => lp (fun _ : Nat.Primes => ℂ) 2) 2

set_option maxHeartbeats 800000 in
/-- Flattened history-to-slice reindexing. -/
def commonRadialHistoryToSlicesLinear :
    PrimeHodgeHistoryHilbert →ₗ[ℂ] CommonRadialHistorySlices where
  toFun x :=
    ⟨fun n => historyPrimeSlice x n,
      memℓp_gen (by
        refine (summable_norm_sq_historyPrimeSlice x).congr (fun n => ?_)
        rw [ENNReal.toReal_ofNat, ← Real.rpow_natCast]
        norm_num)⟩
  map_add' x y := by
    ext n p
    rfl
  map_smul' c x := by
    ext n p
    rfl

theorem norm_commonRadialHistoryToSlicesLinear
    (x : PrimeHodgeHistoryHilbert) :
    ‖commonRadialHistoryToSlicesLinear x‖ = ‖x‖ := by
  have hsq : ‖commonRadialHistoryToSlicesLinear x‖ ^ 2 = ‖x‖ ^ 2 := by
    calc
      ‖commonRadialHistoryToSlicesLinear x‖ ^ 2 =
          ∑' n : ℕ, ‖historyPrimeSlice x n‖ ^ 2 := by
        simpa [commonRadialHistoryToSlicesLinear] using
          lp.norm_rpow_eq_tsum (p := 2)
            (E := fun _ : ℕ => lp (fun _ : Nat.Primes => ℂ) 2)
            (by norm_num) (commonRadialHistoryToSlicesLinear x)
      _ = ‖x‖ ^ 2 := tsum_norm_sq_historyPrimeSlice x
  nlinarith [norm_nonneg (commonRadialHistoryToSlicesLinear x), norm_nonneg x]

def commonRadialHistoryToSlicesIsometry :
    PrimeHodgeHistoryHilbert →ₗᵢ[ℂ] CommonRadialHistorySlices :=
  LinearIsometry.mk commonRadialHistoryToSlicesLinear
    norm_commonRadialHistoryToSlicesLinear

/-- Inverse coordinate flattening. -/
def commonRadialHistoryOfSlices (y : CommonRadialHistorySlices) :
    PrimeHodgeHistoryHilbert :=
  ⟨fun np => y np.1 np.2, HilbertSchmidt.memℓp_of_sq (by
    rw [summable_prod_of_nonneg (fun np => sq_nonneg ‖y np.1 np.2‖)]
    constructor
    · intro n
      exact HilbertSchmidt.summable_coe_sq (y n)
    · have hy : Summable fun n : ℕ => ‖y n‖ ^ 2 := by
        refine ((lp.memℓp y).summable (by norm_num)).congr (fun n => ?_)
        rw [ENNReal.toReal_ofNat, ← Real.rpow_natCast]
        norm_num
      refine hy.congr (fun n => ?_)
      simpa using HilbertSchmidt.lp_norm_sq_eq (y n))⟩

theorem commonRadialHistoryToSlicesIsometry_surjective :
    Function.Surjective commonRadialHistoryToSlicesIsometry := by
  intro y
  refine ⟨commonRadialHistoryOfSlices y, ?_⟩
  ext n p
  simp [commonRadialHistoryToSlicesIsometry,
    commonRadialHistoryToSlicesLinear, commonRadialHistoryOfSlices]

/-- Unitary reindexing between the flat history-prime carrier and sliced history carrier. -/
def commonRadialHistorySlicesEquiv :
    PrimeHodgeHistoryHilbert ≃ₗᵢ[ℂ] CommonRadialHistorySlices :=
  LinearIsometryEquiv.ofSurjective commonRadialHistoryToSlicesIsometry
    commonRadialHistoryToSlicesIsometry_surjective

@[simp] theorem commonRadialHistorySlicesEquiv_apply
    (x : PrimeHodgeHistoryHilbert) (n : ℕ) :
    commonRadialHistorySlicesEquiv x n = historyPrimeSlice x n := by
  simp [commonRadialHistorySlicesEquiv,
    commonRadialHistoryToSlicesIsometry, commonRadialHistoryToSlicesLinear]

/-- A positive bounded block family gives a positive operator on its Hilbert direct sum. -/
theorem blockOperator_isPositive
    {ι : Type*} {K : ι → Type*}
    [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)]
    (T : ∀ i, K i →L[ℂ] K i) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (hpos : ∀ i, (T i).IsPositive) :
    (blockOperator T hC hT).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff]
  constructor
  · intro x y
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    apply tsum_congr
    intro i
    change inner ℂ (T i (x i)) (y i) = inner ℂ (x i) (T i (y i))
    exact (hpos i).inner_left_eq_inner_right (x i) (y i)
  · intro x
    rw [lp.inner_eq_tsum]
    let q : ι → ℂ := fun i => inner ℂ (T i (x i)) (x i)
    change 0 ≤ ∑' i, q i
    have hxsum : Summable fun i => ‖x i‖ ^ 2 := by
      refine ((lp.memℓp x).summable (by norm_num)).congr (fun i => ?_)
      rw [ENNReal.toReal_ofNat, ← Real.rpow_natCast]
      norm_num
    have hqnorm : Summable fun i => ‖q i‖ := by
      refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_)
        (hxsum.mul_left C)
      dsimp [q]
      calc
        ‖inner ℂ (T i (x i)) (x i)‖ ≤ ‖T i (x i)‖ * ‖x i‖ :=
          norm_inner_le_norm _ _
        _ ≤ (C * ‖x i‖) * ‖x i‖ := by
          gcongr
          exact le_trans ((T i).le_opNorm _) (mul_le_mul_of_nonneg_right
            (hT i) (norm_nonneg _))
        _ = C * ‖x i‖ ^ 2 := by ring
    have hq : Summable q := hqnorm.of_norm
    rw [Complex.nonneg_iff]
    constructor
    · have hre := Complex.reCLM.map_tsum hq
      change (∑' i, q i).re = ∑' i, (q i).re at hre
      rw [hre]
      exact tsum_nonneg fun i => (Complex.nonneg_iff.mp
        (((ContinuousLinearMap.isPositive_iff (T i)).mp (hpos i)).2 (x i))).1
    · have him := Complex.imCLM.map_tsum hq
      change (∑' i, q i).im = ∑' i, (q i).im at him
      rw [him]
      have hzero : ∀ i, (q i).im = 0 := fun i => by
        exact (Complex.nonneg_iff.mp
          (((ContinuousLinearMap.isPositive_iff (T i)).mp (hpos i)).2 (x i))).2.symm
      simp [hzero]

/-- Constant block-diagonal action on sliced history. -/
def commonRadialConstantHistoryBlock
    (C : lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ]
      lp (fun _ : Nat.Primes => ℂ) 2) :
    CommonRadialHistorySlices →L[ℂ] CommonRadialHistorySlices :=
  blockOperator (fun _ : ℕ => C) (norm_nonneg C) (fun _ => le_rfl)

@[simp] theorem commonRadialConstantHistoryBlock_apply
    (C : lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ]
      lp (fun _ : Nat.Primes => ℂ) 2)
    (x : CommonRadialHistorySlices) (n : ℕ) :
    commonRadialConstantHistoryBlock C x n = C (x n) := rfl

theorem commonRadialConstantHistoryBlock_isPositive
    {C : lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ]
      lp (fun _ : Nat.Primes => ℂ) 2} (hC : C.IsPositive) :
    (commonRadialConstantHistoryBlock C).IsPositive :=
  blockOperator_isPositive (fun _ : ℕ => C) (norm_nonneg C)
    (fun _ => le_rfl) (fun _ => hC)

/-- Constant prime-block history lift, transported back to flat history-prime coordinates. -/
def recurrentConstantBlockLift
    (C : lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ]
      lp (fun _ : Nat.Primes => ℂ) 2) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  commonRadialHistorySlicesEquiv.symm.toLinearIsometry.toContinuousLinearMap ∘L
    commonRadialConstantHistoryBlock C ∘L
      commonRadialHistorySlicesEquiv.toLinearIsometry.toContinuousLinearMap

theorem commonRadialHistorySlicesEquiv_recurrentConstantBlockLift
    (C : lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ]
      lp (fun _ : Nat.Primes => ℂ) 2) (x : PrimeHodgeHistoryHilbert) :
    commonRadialHistorySlicesEquiv (recurrentConstantBlockLift C x) =
      commonRadialConstantHistoryBlock C (commonRadialHistorySlicesEquiv x) := by
  simp [recurrentConstantBlockLift]

theorem historyPrimeSlice_recurrentConstantBlockLift
    (C : lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ]
      lp (fun _ : Nat.Primes => ℂ) 2)
    (x : PrimeHodgeHistoryHilbert) (n : ℕ) :
    historyPrimeSlice (recurrentConstantBlockLift C x) n =
      C (historyPrimeSlice x n) := by
  have h := congrArg (fun y : CommonRadialHistorySlices => y n)
    (commonRadialHistorySlicesEquiv_recurrentConstantBlockLift C x)
  simpa using h

theorem recurrentConstantBlockLift_apply_coordinate
    (C : lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ]
      lp (fun _ : Nat.Primes => ℂ) 2)
    (x : PrimeHodgeHistoryHilbert) (n : ℕ) (p : Nat.Primes) :
    recurrentConstantBlockLift C x (n, p) = C (historyPrimeSlice x n) p := by
  have h := congrArg (fun y : lp (fun _ : Nat.Primes => ℂ) 2 => y p)
    (historyPrimeSlice_recurrentConstantBlockLift C x n)
  exact h

theorem recurrentConstantBlockLift_isPositive
    {C : lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ]
      lp (fun _ : Nat.Primes => ℂ) 2} (hC : C.IsPositive) :
    (recurrentConstantBlockLift C).IsPositive := by
  let E := commonRadialHistorySlicesEquiv
  let B := commonRadialConstantHistoryBlock C
  have hB : B.IsPositive := commonRadialConstantHistoryBlock_isPositive hC
  rw [ContinuousLinearMap.isPositive_iff]
  constructor
  · intro x y
    calc
      inner ℂ (recurrentConstantBlockLift C x) y =
          inner ℂ (E (recurrentConstantBlockLift C x)) (E y) :=
        (E.inner_map_map _ _).symm
      _ = inner ℂ (B (E x)) (E y) := by
        rw [show E (recurrentConstantBlockLift C x) = B (E x) by
          exact commonRadialHistorySlicesEquiv_recurrentConstantBlockLift C x]
      _ = inner ℂ (E x) (B (E y)) := hB.inner_left_eq_inner_right _ _
      _ = inner ℂ (E x) (E (recurrentConstantBlockLift C y)) := by
        rw [show E (recurrentConstantBlockLift C y) = B (E y) by
          exact commonRadialHistorySlicesEquiv_recurrentConstantBlockLift C y]
      _ = inner ℂ x (recurrentConstantBlockLift C y) := E.inner_map_map _ _
  · intro x
    have hx := ((ContinuousLinearMap.isPositive_iff B).mp hB).2 (E x)
    have heq : inner ℂ (recurrentConstantBlockLift C x) x =
        inner ℂ (B (E x)) (E x) := by
      calc
        inner ℂ (recurrentConstantBlockLift C x) x =
            inner ℂ (E (recurrentConstantBlockLift C x)) (E x) :=
          (E.inner_map_map _ _).symm
        _ = inner ℂ (B (E x)) (E x) := by
          rw [show E (recurrentConstantBlockLift C x) = B (E x) by
            exact commonRadialHistorySlicesEquiv_recurrentConstantBlockLift C x]
    rwa [heq]

theorem historyPrimeSlice_historyGradeEmbeddingCLM_self
    (n : ℕ) (x : lp (fun _ : Nat.Primes => ℂ) 2) :
    historyPrimeSlice (historyGradeEmbeddingCLM n x) n = x := by
  ext p
  change lpScalarInjection (historyGradeIndex n) (historyGradeIndex_injective n) x
      (historyGradeIndex n p) = x p
  exact lpScalarInjection_coordinate (historyGradeIndex n)
    (historyGradeIndex_injective n) x p

/-- Every history-grade compression of a constant block lift is its prime block. -/
theorem recurrentGradeCompression_recurrentConstantBlockLift
    (C : lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ]
      lp (fun _ : Nat.Primes => ℂ) 2) (n : ℕ) :
    recurrentGradeCompression (recurrentConstantBlockLift C) n = C := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext p
  rw [recurrentGradeCompression]
  simp only [ContinuousLinearMap.comp_apply]
  rw [adjoint_historyGradeEmbeddingCLM, lpCoordinatePullback_apply]
  change recurrentConstantBlockLift C (historyGradeEmbeddingCLM n x) (n, p) =
    C x p
  rw [recurrentConstantBlockLift_apply_coordinate,
    historyPrimeSlice_historyGradeEmbeddingCLM_self]

/-- Constant history blocks are fixed by unilateral-shift conjugation. -/
theorem recurrentHistoryConjugate_recurrentConstantBlockLift
    (C : lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ]
      lp (fun _ : Nat.Primes => ℂ) 2) :
    recurrentHistoryConjugate (recurrentConstantBlockLift C) =
      recurrentConstantBlockLift C := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext np
  rcases np with ⟨n, p⟩
  rw [recurrentHistoryConjugate]
  simp only [ContinuousLinearMap.comp_apply]
  rw [adjoint_historyShiftCLM, lpCoordinatePullback_apply]
  change recurrentConstantBlockLift C (historyShiftCLM x) (n + 1, p) =
    recurrentConstantBlockLift C x (n, p)
  rw [recurrentConstantBlockLift_apply_coordinate,
    recurrentConstantBlockLift_apply_coordinate,
    historyShift_slice_succ]

theorem recurrentHistoryConjugate_add
    (S T : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert) :
    recurrentHistoryConjugate (S + T) =
      recurrentHistoryConjugate S + recurrentHistoryConjugate T := by
  ext x
  simp [recurrentHistoryConjugate, ContinuousLinearMap.comp_apply]

/-- Canonical positive completion obtained by adjoining a positive recurrent prime block. -/
def recurrentConstantBlockCompletion
    (a : {d : ℝ // 0 < d})
    (C : lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ]
      lp (fun _ : Nat.Primes => ℂ) 2) (hC : C.IsPositive) :
    RecurrentPrimePositiveCompletion a where
  operator := recurrentPrimeMinimalCompletion a.property +
    recurrentConstantBlockLift C
  positive := (recurrentPrimeMinimalCompletion_isPositive a.property).add
    (recurrentConstantBlockLift_isPositive hC)
  displacement := by
    rw [recurrentHistoryConjugate_add,
      recurrentHistoryConjugate_recurrentConstantBlockLift]
    have hG := recurrentPrimeMinimalCompletion_displacement a.property
    rw [← hG]
    abel

theorem recurrentConstantBlockCompletion_remainder
    (a : {d : ℝ // 0 < d})
    (C : lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ]
      lp (fun _ : Nat.Primes => ℂ) 2) (hC : C.IsPositive) :
    (recurrentConstantBlockCompletion a C hC).remainder =
      recurrentConstantBlockLift C := by
  rw [RecurrentPrimePositiveCompletion.remainder]
  change recurrentPrimeMinimalCompletion a.property + recurrentConstantBlockLift C -
      recurrentPrimeMinimalCompletion a.property = recurrentConstantBlockLift C
  abel

/-- Canonical Burnol-source recurrent completion. -/
def commonRadialPrimeSourceHistoryCompletion (a : {d : ℝ // 0 < d}) :
    RecurrentPrimePositiveCompletion a :=
  recurrentConstantBlockCompletion a (commonRadialPrimeSourceSymbol a)
    (commonRadialPrimeSourceSymbol_isPositive a)

theorem commonRadialPrimeSourceHistoryCompletion_remainder
    (a : {d : ℝ // 0 < d}) :
    (commonRadialPrimeSourceHistoryCompletion a).remainder =
      recurrentConstantBlockLift (commonRadialPrimeSourceSymbol a) :=
  recurrentConstantBlockCompletion_remainder a _ _

theorem commonRadialPrimeSourceHistoryCompletion_gradeCompression
    (a : {d : ℝ // 0 < d}) (n : ℕ) :
    recurrentGradeCompression
        (commonRadialPrimeSourceHistoryCompletion a).remainder n =
      commonRadialPrimeSourceSymbol a := by
  rw [commonRadialPrimeSourceHistoryCompletion_remainder,
    recurrentGradeCompression_recurrentConstantBlockLift]

theorem commonRadialPrimeSourceHistoryCompletion_totalBoundaryExcess
    (a : {d : ℝ // 0 < d}) :
    recurrentTotalBoundaryExcess a
        (commonRadialPrimeSourceHistoryCompletion a).operator =
      (ContinuousLinearMap.opTrace (commonRadialPrimeSourceSymbol a)).re := by
  let X := commonRadialPrimeSourceHistoryCompletion a
  have htrace : MemSchattenClass 1
      (recurrentGradeCompression X.remainder 0) := by
    change MemSchattenClass 1
      (recurrentGradeCompression
        (commonRadialPrimeSourceHistoryCompletion a).remainder 0)
    rw [commonRadialPrimeSourceHistoryCompletion_gradeCompression]
    exact commonRadialPrimeSourceSymbol_memSchattenClass_one a
  rw [X.totalBoundaryExcess_eq_re_opTrace htrace]
  change (ContinuousLinearMap.opTrace
      (recurrentGradeCompression
        (commonRadialPrimeSourceHistoryCompletion a).remainder 0)).re = _
  rw [commonRadialPrimeSourceHistoryCompletion_gradeCompression]

theorem commonRadialPrimeSourceHistoryCompletion_totalBoundaryExcess_pos
    (a : {d : ℝ // 0 < d}) :
    0 < recurrentTotalBoundaryExcess a
      (commonRadialPrimeSourceHistoryCompletion a).operator := by
  rw [commonRadialPrimeSourceHistoryCompletion_totalBoundaryExcess]
  exact re_opTrace_commonRadialPrimeSourceSymbol_pos a

theorem commonRadialPrimeSourceHistoryCompletion_totalBoundaryExcess_lt_one
    (a : {d : ℝ // 0 < d}) :
    recurrentTotalBoundaryExcess a
        (commonRadialPrimeSourceHistoryCompletion a).operator < 1 := by
  rw [commonRadialPrimeSourceHistoryCompletion_totalBoundaryExcess]
  exact re_opTrace_commonRadialPrimeSourceSymbol_lt_one a

/-- A constant history block with one strictly positive diagonal entry is not trace class on the
full history carrier: that same nonzero trace mass repeats at every history grade. -/
theorem recurrentConstantBlockLift_not_memSchattenClass_one_of_pos_diagonal
    {C : lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ]
      lp (fun _ : Nat.Primes => ℂ) 2} (p : Nat.Primes)
    (hp : 0 < (inner ℂ (HilbertSchmidt.lpBasis Nat.Primes p)
      (C (HilbertSchmidt.lpBasis Nat.Primes p))).re) :
    ¬ MemSchattenClass 1 (recurrentConstantBlockLift C) := by
  intro htrace
  let b := HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex
  have hall := htrace.one_summable_norm_inner_diag_basis b
  have hinj : Function.Injective (fun n : ℕ => (n, p)) := by
    intro n m h
    exact congrArg Prod.fst h
  have hsub : Summable fun n : ℕ =>
      ‖inner ℂ (b (n, p)) (recurrentConstantBlockLift C (b (n, p)))‖ := by
    exact hall.comp_injective hinj
  let c := ‖inner ℂ (HilbertSchmidt.lpBasis Nat.Primes p)
    (C (HilbertSchmidt.lpBasis Nat.Primes p))‖
  have hc : 0 < c := by
    apply norm_pos_iff.mpr
    intro hzero
    have hreal : (inner ℂ (HilbertSchmidt.lpBasis Nat.Primes p)
        (C (HilbertSchmidt.lpBasis Nat.Primes p))).re = 0 := by
      rw [hzero]
      rfl
    linarith
  have hentry (n : ℕ) :
      inner ℂ (b (n, p)) (recurrentConstantBlockLift C (b (n, p))) =
        inner ℂ (HilbertSchmidt.lpBasis Nat.Primes p)
          (C (HilbertSchmidt.lpBasis Nat.Primes p)) := by
    change inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
        (recurrentConstantBlockLift C
          (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))) = _
    rw [← inner_basis_recurrentGradeCompression]
    rw [recurrentGradeCompression_recurrentConstantBlockLift]
  have hconst : Summable fun _ : ℕ => c := by
    refine hsub.congr (fun n => ?_)
    rw [hentry]
  have hzero : Tendsto (fun _ : ℕ => c) atTop (nhds 0) :=
    hconst.tendsto_atTop_zero
  have hsame : Tendsto (fun _ : ℕ => c) atTop (nhds c) := tendsto_const_nhds
  have hczero : (0 : ℝ) = c := tendsto_nhds_unique hzero hsame
  linarith

theorem commonRadialPrimeSourceHistoryCompletion_remainder_not_memSchattenClass_one
    (a : {d : ℝ // 0 < d}) :
    ¬ MemSchattenClass 1
      (commonRadialPrimeSourceHistoryCompletion a).remainder := by
  rw [commonRadialPrimeSourceHistoryCompletion_remainder]
  let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  exact recurrentConstantBlockLift_not_memSchattenClass_one_of_pos_diagonal p2
    (re_inner_basis_commonRadialPrimeSourceSymbol_pos a p2 p2)

theorem commonRadialPrimeSourceHistoryCompletion_boundaryExcessTerm_pos
    (a : {d : ℝ // 0 < d}) (p : Nat.Primes) :
    0 < recurrentPrimeBoundaryExcessTerm a
      (commonRadialPrimeSourceHistoryCompletion a).operator p := by
  let X := commonRadialPrimeSourceHistoryCompletion a
  rw [X.boundaryExcessTerm_eq_diagonal]
  rw [← inner_basis_recurrentGradeCompression]
  change 0 < (inner ℂ (HilbertSchmidt.lpBasis Nat.Primes p)
    (recurrentGradeCompression
      (commonRadialPrimeSourceHistoryCompletion a).remainder 0
        (HilbertSchmidt.lpBasis Nat.Primes p))).re
  rw [commonRadialPrimeSourceHistoryCompletion_gradeCompression]
  exact re_inner_basis_commonRadialPrimeSourceSymbol_pos a p p

theorem commonRadialPrimeSourceHistoryCompletion_normalizedFiniteCompressionTrace_eq
    (a : {d : ℝ // 0 < d}) (N : RecurrentPositiveCutoff)
    (F : Finset Nat.Primes) :
    (1 / (N : ℝ)) * recurrentFiniteCompressionTrace
        (commonRadialPrimeSourceHistoryCompletion a).remainder N F =
      recurrentFiniteBoundaryExcess a
        (commonRadialPrimeSourceHistoryCompletion a).operator F :=
  (commonRadialPrimeSourceHistoryCompletion a).normalizedFiniteCompressionTrace_eq N F

/-- Every contractive common-radial sandwich gives a recurrent positive completion. -/
def commonRadialPrimeContractedHistoryCompletion
    (a : {d : ℝ // 0 < d}) (V : CommonRadialContraction) :
    RecurrentPrimePositiveCompletion a :=
  recurrentConstantBlockCompletion a (commonRadialPrimeContractedSymbol a V)
    (commonRadialPrimeContractedSymbol_isPositive a V)

theorem commonRadialPrimeContractedHistoryCompletion_gradeCompression
    (a : {d : ℝ // 0 < d}) (V : CommonRadialContraction) (n : ℕ) :
    recurrentGradeCompression
        (commonRadialPrimeContractedHistoryCompletion a V).remainder n =
      commonRadialPrimeContractedSymbol a V := by
  change recurrentGradeCompression
      (recurrentConstantBlockCompletion a (commonRadialPrimeContractedSymbol a V)
        (commonRadialPrimeContractedSymbol_isPositive a V)).remainder n = _
  rw [recurrentConstantBlockCompletion_remainder,
    recurrentGradeCompression_recurrentConstantBlockLift]

theorem commonRadialPrimeContractedHistoryCompletion_totalBoundaryExcess
    (a : {d : ℝ // 0 < d}) (V : CommonRadialContraction) :
    recurrentTotalBoundaryExcess a
        (commonRadialPrimeContractedHistoryCompletion a V).operator =
      (ContinuousLinearMap.opTrace
        (commonRadialPrimeContractedSymbol a V)).re := by
  let X := commonRadialPrimeContractedHistoryCompletion a V
  have htrace : MemSchattenClass 1
      (recurrentGradeCompression X.remainder 0) := by
    change MemSchattenClass 1
      (recurrentGradeCompression
        (commonRadialPrimeContractedHistoryCompletion a V).remainder 0)
    rw [commonRadialPrimeContractedHistoryCompletion_gradeCompression]
    exact commonRadialPrimeContractedSymbol_memSchattenClass_one a V
  rw [X.totalBoundaryExcess_eq_re_opTrace htrace]
  change (ContinuousLinearMap.opTrace
      (recurrentGradeCompression
        (commonRadialPrimeContractedHistoryCompletion a V).remainder 0)).re = _
  rw [commonRadialPrimeContractedHistoryCompletion_gradeCompression]

theorem commonRadialPrimeContractedHistoryCompletion_totalBoundaryExcess_le
    (a : {d : ℝ // 0 < d}) (V : CommonRadialContraction) :
    recurrentTotalBoundaryExcess a
        (commonRadialPrimeContractedHistoryCompletion a V).operator ≤
      ‖commonRadialPrimeReachability a‖ ^ 2 * ‖V.1‖ ^ 2 *
        routePPrimitiveBaseCauchyCubicTraceBudget := by
  rw [commonRadialPrimeContractedHistoryCompletion_totalBoundaryExcess]
  exact re_opTrace_commonRadialPrimeContractedSymbol_le a V

theorem commonRadialPrimeContractedHistoryCompletion_totalBoundaryExcess_lt_one
    (a : {d : ℝ // 0 < d}) (V : CommonRadialContraction) :
    recurrentTotalBoundaryExcess a
        (commonRadialPrimeContractedHistoryCompletion a V).operator < 1 := by
  rw [commonRadialPrimeContractedHistoryCompletion_totalBoundaryExcess]
  exact re_opTrace_commonRadialPrimeContractedSymbol_lt_one a V

theorem commonRadialPrimeContractedHistoryCompletion_normalizedFiniteCompressionTrace_eq
    (a : {d : ℝ // 0 < d}) (V : CommonRadialContraction)
    (N : RecurrentPositiveCutoff) (F : Finset Nat.Primes) :
    (1 / (N : ℝ)) * recurrentFiniteCompressionTrace
        (commonRadialPrimeContractedHistoryCompletion a V).remainder N F =
      recurrentFiniteBoundaryExcess a
        (commonRadialPrimeContractedHistoryCompletion a V).operator F :=
  (commonRadialPrimeContractedHistoryCompletion a V).normalizedFiniteCompressionTrace_eq N F

end
end RHTower

