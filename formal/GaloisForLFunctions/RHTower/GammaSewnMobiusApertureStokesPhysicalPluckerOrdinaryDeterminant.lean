import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPhysicalPluckerEntireDeterminant
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailMomentLogConvex
import GaloisForLFunctions.RHTower.NuclearRankOneTrace

/-!
# Trace restoration for the physical Pluecker determinant

The source-native physical Pluecker operator is trace class, but its regularized determinant
`det₂ (1 + uT)` has zero first derivative at the origin.  The completed-Xi square-coordinate
series has strictly positive first coefficient.  Thus a direct identification of the reflected
`det₂` with normalized completed Xi is impossible already at first order.

The obstruction forces the canonical trace counterterm.  Multiplication by
`exp (u * tr T)` restores the ordinary Fredholm determinant without changing its zeros.  This file
proves that the source trace is strictly positive, identifies it with the absolutely summable
coordinate diagonal, proves the exact finite-dimensional determinant formula, and transports
finite sections to the infinite ordinary determinant.

No Xi coefficient is fitted or inserted into the construction.  The remaining arithmetic gate is
the source identity `tr T = thetaCuspNormalizedEvenMoment 1 / 2`, followed by all higher Fredholm
coefficient identities.
-/

open Real Set Filter Topology Matrix
open scoped BigOperators InnerProductSpace ComplexOrder

noncomputable section

namespace RHTower.HedenmalmThetaSource

open HilbertSchmidt

/-- Regularization removes the linear trace term from the physical determinant. -/
theorem gammaSewnCriticalPhysicalPluckerEntireDet2_deriv_zero :
    deriv gammaSewnCriticalPhysicalPluckerEntireDet2 0 = 0 := by
  obtain ⟨_differentiable, r, hr, hrK, heq⟩ :=
    GaloisForLFunctions.HTGeometry.isRegularizedDet_entireDet2
      gammaSewnCriticalPhysicalPluckerKernel_isHS
  have hzero : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := by simpa using hr
  have hev : gammaSewnCriticalPhysicalPluckerEntireDet2 =ᶠ[nhds 0]
      HilbertSchmidt.fredholmDet gammaSewnCriticalPhysicalPluckerKernel := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzero] with z hz
    exact heq z hz
  rw [hev.deriv_eq]
  have hderiv := HilbertSchmidt.hasDerivAt_fredholmDet
    gammaSewnCriticalPhysicalPluckerKernel_isHS r hrK 0 hzero
  rw [hderiv.deriv]
  simp [HilbertSchmidt.resolventTrace]

theorem gammaSewnCriticalPhysicalPluckerStableEntireDet2_deriv_zero :
    deriv gammaSewnCriticalPhysicalPluckerStableEntireDet2 0 = 0 := by
  have hD : HasDerivAt gammaSewnCriticalPhysicalPluckerEntireDet2 0 0 :=
    differentiable_gammaSewnCriticalPhysicalPluckerEntireDet2.differentiableAt.hasDerivAt
      |>.congr_deriv gammaSewnCriticalPhysicalPluckerEntireDet2_deriv_zero
  have hneg : HasDerivAt (fun z : ℂ => -z) (-1) 0 := hasDerivAt_neg 0
  have hD' : HasDerivAt gammaSewnCriticalPhysicalPluckerEntireDet2 0 (-(0 : ℂ)) := by
    simpa using hD
  have hcomp := HasDerivAt.comp (0 : ℂ) hD' hneg
  change deriv (fun u : ℂ => gammaSewnCriticalPhysicalPluckerEntireDet2 (-u)) 0 = 0
  simpa [Function.comp_def] using hcomp.deriv

/-- The normalized completed-Xi square-coordinate series has nonzero linear coefficient. -/
theorem thetaCuspXiSquareFirstCoefficient_pos :
    0 < thetaCuspNormalizedEvenMoment 1 / 2 := by
  rw [thetaCuspNormalizedEvenMoment]
  exact div_pos
    (div_pos (thetaCuspRawEvenMoment_pos 1) thetaCuspRawEvenMoment_zero_pos)
    (by norm_num)

/-- First-jet no-go: reflected `det₂` cannot be normalized completed Xi in square coordinate. -/
theorem gammaSewnCriticalPhysicalPluckerStableEntireDet2_firstJet_ne_theta :
    deriv gammaSewnCriticalPhysicalPluckerStableEntireDet2 0 ≠
      ((thetaCuspNormalizedEvenMoment 1 / 2 : ℝ) : ℂ) := by
  rw [gammaSewnCriticalPhysicalPluckerStableEntireDet2_deriv_zero]
  exact (Complex.ofReal_ne_zero.mpr thetaCuspXiSquareFirstCoefficient_pos.ne').symm

/-- Canonical trace of the literal physical source operator. -/
def gammaSewnCriticalPhysicalPluckerSourceTrace : ℂ :=
  ContinuousLinearMap.opTrace gammaSewnCriticalPhysicalPluckerSpectralOperator

theorem gammaSewnCriticalPhysicalPluckerSourceTrace_eq_tsum_lpBasis :
    gammaSewnCriticalPhysicalPluckerSourceTrace =
      ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
        inner ℂ (HilbertSchmidt.lpBasis GammaSewnCriticalPhysicalPluckerIndex u)
          (gammaSewnCriticalPhysicalPluckerSpectralOperator
            (HilbertSchmidt.lpBasis GammaSewnCriticalPhysicalPluckerIndex u)) := by
  obtain ⟨S, U, hS, hU, hfactor⟩ :=
    gammaSewnCriticalPhysicalPluckerSpectralOperator_memSchattenClass_one.one_isTraceClass
  rw [gammaSewnCriticalPhysicalPluckerSourceTrace, hfactor]
  exact ContinuousLinearMap.opTrace_comp_eq_tsum_basis hS hU
    (HilbertSchmidt.lpBasis GammaSewnCriticalPhysicalPluckerIndex)

/-- Faithfulness upgrades every coordinate diagonal entry from nonnegative to positive. -/
theorem gammaSewnCriticalPhysicalPlucker_basis_quadratic_pos
    (u : GammaSewnCriticalPhysicalPluckerIndex) :
    0 < inner ℂ (HilbertSchmidt.lpBasis GammaSewnCriticalPhysicalPluckerIndex u)
      (gammaSewnCriticalPhysicalPluckerSpectralOperator
        (HilbertSchmidt.lpBasis GammaSewnCriticalPhysicalPluckerIndex u)) := by
  let e := HilbertSchmidt.lpBasis GammaSewnCriticalPhysicalPluckerIndex u
  have he0 : e ≠ 0 := by
    intro he
    have hnorm := (HilbertSchmidt.lpBasis
      GammaSewnCriticalPhysicalPluckerIndex).orthonormal.1 u
    change ‖e‖ = 1 at hnorm
    rw [he, norm_zero] at hnorm
    norm_num at hnorm
  have hnonneg :=
    gammaSewnCriticalPhysicalPluckerSpectralOperator_isPositive.inner_nonneg_right e
  apply lt_of_le_of_ne hnonneg
  intro hzero
  have hker :=
    gammaSewnCriticalPhysicalPluckerSpectralOperator_isPositive.apply_eq_zero_of_inner_eq_zero
      hzero.symm
  exact he0 (gammaSewnCriticalPhysicalPluckerSpectralOperator_injective (by simpa using hker))

/-- The source trace is strictly positive, so trace restoration is nontrivial. -/
theorem gammaSewnCriticalPhysicalPluckerSourceTrace_pos :
    0 < gammaSewnCriticalPhysicalPluckerSourceTrace := by
  rw [gammaSewnCriticalPhysicalPluckerSourceTrace_eq_tsum_lpBasis]
  have hsum :=
    gammaSewnCriticalPhysicalPluckerSpectralOperator_memSchattenClass_one
      |>.one_summable_inner_diag_basis
        (HilbertSchmidt.lpBasis GammaSewnCriticalPhysicalPluckerIndex)
  exact hsum.tsum_pos
    (fun u => (gammaSewnCriticalPhysicalPlucker_basis_quadratic_pos u).le) (0, 0)
    (gammaSewnCriticalPhysicalPlucker_basis_quadratic_pos (0, 0))

/-- Literal nuclear mass carried by the source-normalized positive rank-one expansion. -/
def gammaSewnCriticalPhysicalPluckerNuclearTraceMass : ℝ :=
  ∑' idx : (ℕ × ℕ) × Fin 6,
    gammaSewnCriticalAdjacentPrime_PluckerBlockWeight idx.1 *
      gammaSewnCriticalAdjacentPrime_PluckerProbability idx.1 idx.2 *
        ‖gammaSewnCriticalPhysicalPluckerCenteredVector idx.1 idx.2‖ ^ 2

theorem opTrace_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm
    (idx : (ℕ × ℕ) × Fin 6) :
    ContinuousLinearMap.opTrace
      (gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm idx) =
      ((gammaSewnCriticalAdjacentPrime_PluckerBlockWeight idx.1 *
        gammaSewnCriticalAdjacentPrime_PluckerProbability idx.1 idx.2 *
          ‖gammaSewnCriticalPhysicalPluckerCenteredVector idx.1 idx.2‖ ^ 2 : ℝ) : ℂ) := by
  rw [gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm,
    RHTower.opTrace_smul_rankOne_self]
  push_cast
  rfl

/-- Exact first-trace source formula: no spectral data remain hidden in `opTrace`. -/
theorem gammaSewnCriticalPhysicalPluckerSourceTrace_eq_nuclearTraceMass :
    gammaSewnCriticalPhysicalPluckerSourceTrace =
      (gammaSewnCriticalPhysicalPluckerNuclearTraceMass : ℂ) := by
  rw [gammaSewnCriticalPhysicalPluckerSourceTrace,
    gammaSewnCriticalPhysicalPluckerSpectralOperator,
    RHTower.opTrace_tsum_rankOneTerms_of_summable_norm
      gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm
      gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm_hasRankLE
      summable_norm_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm]
  simp_rw [opTrace_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm]
  rw [gammaSewnCriticalPhysicalPluckerNuclearTraceMass]
  exact (Complex.ofReal_tsum _).symm

/-- Squared norm of one four-cell centered source vector is its literal coordinate energy. -/
theorem norm_gammaSewnCriticalPhysicalPluckerCenteredVector_sq
    (z : ℕ × ℕ) (s : Fin 6) :
    ‖gammaSewnCriticalPhysicalPluckerCenteredVector z s‖ ^ 2 =
      ∑ i : Fin 4,
        gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s i ^ 2 := by
  have hortho : Orthonormal ℂ (fun i : Fin 4 =>
      gammaSewnCriticalPhysicalPluckerBasis
        (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i)) := by
    constructor
    · intro i
      exact norm_gammaSewnCriticalPhysicalPluckerBasis _
    · intro i j hij
      rw [inner_gammaSewnCriticalPhysicalPluckerBasis]
      simp [gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel_injective z |>.ne hij]
  have hsquare := hortho.orthogonalFamily.norm_sum
    (fun i : Fin 4 =>
      (gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s i : ℂ))
    Finset.univ
  simpa [gammaSewnCriticalPhysicalPluckerCenteredVector,
    LinearIsometry.toSpanSingleton_apply, Complex.norm_real, Real.norm_eq_abs,
    sq_abs] using hsquare

/-- One packet's nuclear mass is exactly the trace of its source spectral matrix. -/
theorem gammaSewnCriticalPhysicalPlucker_localNuclearTraceMass_eq_spectralTrace
    (z : ℕ × ℕ) :
    ∑ s : Fin 6,
      gammaSewnCriticalAdjacentPrime_PluckerProbability z s *
        ‖gammaSewnCriticalPhysicalPluckerCenteredVector z s‖ ^ 2 =
      ∑ i : Fin 4, gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z i i := by
  simp_rw [norm_gammaSewnCriticalPhysicalPluckerCenteredVector_sq,
    gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_eq_centered]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem summable_gammaSewnCriticalPhysicalPluckerNuclearTraceMass_terms :
    Summable (fun idx : (ℕ × ℕ) × Fin 6 =>
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight idx.1 *
        gammaSewnCriticalAdjacentPrime_PluckerProbability idx.1 idx.2 *
          ‖gammaSewnCriticalPhysicalPluckerCenteredVector idx.1 idx.2‖ ^ 2) := by
  exact summable_norm_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm.congr
    (fun idx => norm_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm idx)

/-- Global first trace is a normalized weighted average of explicit local `4 x 4` traces. -/
theorem gammaSewnCriticalPhysicalPluckerNuclearTraceMass_eq_tsum_spectralTrace :
    gammaSewnCriticalPhysicalPluckerNuclearTraceMass =
      ∑' z : ℕ × ℕ,
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
          (∑ i : Fin 4,
            gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z i i) := by
  rw [gammaSewnCriticalPhysicalPluckerNuclearTraceMass,
    summable_gammaSewnCriticalPhysicalPluckerNuclearTraceMass_terms.tsum_prod]
  apply tsum_congr
  intro z
  rw [tsum_fintype]
  calc
    ∑ s : Fin 6,
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
          gammaSewnCriticalAdjacentPrime_PluckerProbability z s *
            ‖gammaSewnCriticalPhysicalPluckerCenteredVector z s‖ ^ 2 =
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
          ∑ s : Fin 6,
            gammaSewnCriticalAdjacentPrime_PluckerProbability z s *
              ‖gammaSewnCriticalPhysicalPluckerCenteredVector z s‖ ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
    _ = _ := by
      rw [gammaSewnCriticalPhysicalPlucker_localNuclearTraceMass_eq_spectralTrace]

/-- Every diagonal entry of a physical packet is a reciprocal-gap node times the Bernoulli
variance of the corresponding coordinate's pair-inclusion event. -/
theorem gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_diag_eq_bernoulliVariance
    (z : ℕ × ℕ) (i : Fin 4) :
    gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z i i =
      gammaSewnCriticalPrimeDepthPacket_node z.1
          (gammaSewnCriticalAdjacentPrime_lower z.2)
          (gammaSewnCriticalAdjacentPrime_upper z.2) i *
        gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i *
          (1 - gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i) := by
  let n := gammaSewnCriticalPrimeDepthPacket_node z.1
    (gammaSewnCriticalAdjacentPrime_lower z.2)
    (gammaSewnCriticalAdjacentPrime_upper z.2) i
  have hn : 0 ≤ n :=
    (gammaSewnCriticalPrimeDepthPacket_node_pos z.1
      (gammaSewnCriticalAdjacentPrime_lower z.2)
      (gammaSewnCriticalAdjacentPrime_upper z.2) i).le
  rw [gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock,
    gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_apply]
  change Real.sqrt n *
      fourRatePluckerCovariance
        (gammaSewnCriticalAdjacentPrime_PluckerProbability z)
        (fourRateCoordinateDelta i) (fourRateCoordinateDelta i) *
        Real.sqrt n = _
  rw [fourRatePluckerCovariance_coordinateDelta_self_eq_bernoulliVariance]
  change Real.sqrt n *
      (gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i *
        (1 - gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i)) *
        Real.sqrt n = _
  have hsqrt : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn
  change Real.sqrt n *
      (gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i *
        (1 - gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i)) *
        Real.sqrt n =
      n * gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i *
        (1 - gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i)
  calc
    _ = (Real.sqrt n * Real.sqrt n) *
        (gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i *
          (1 - gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i)) := by ring
    _ = _ := by rw [hsqrt]; ring

/-- Packet trace after eliminating the full six-pair covariance matrix. -/
theorem gammaSewnCriticalPhysicalPlucker_localTrace_eq_bernoulliTrace
    (z : ℕ × ℕ) :
    (∑ i : Fin 4,
      gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z i i) =
      ∑ i : Fin 4,
        gammaSewnCriticalPrimeDepthPacket_node z.1
            (gammaSewnCriticalAdjacentPrime_lower z.2)
            (gammaSewnCriticalAdjacentPrime_upper z.2) i *
          gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i *
            (1 - gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i) := by
  apply Finset.sum_congr rfl
  intro i _
  exact
    gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_diag_eq_bernoulliVariance z i

/-- The repaired determinant's first derivative is an explicit normalized prime-depth average of
four reciprocal-gap Bernoulli variances per packet. -/
theorem gammaSewnCriticalPhysicalPluckerNuclearTraceMass_eq_tsum_bernoulliTrace :
    gammaSewnCriticalPhysicalPluckerNuclearTraceMass =
      ∑' z : ℕ × ℕ,
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
          (∑ i : Fin 4,
            gammaSewnCriticalPrimeDepthPacket_node z.1
                (gammaSewnCriticalAdjacentPrime_lower z.2)
                (gammaSewnCriticalAdjacentPrime_upper z.2) i *
              gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i *
                (1 - gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i)) := by
  rw [gammaSewnCriticalPhysicalPluckerNuclearTraceMass_eq_tsum_spectralTrace]
  apply tsum_congr
  intro z
  rw [gammaSewnCriticalPhysicalPlucker_localTrace_eq_bernoulliTrace]

/-- Ordinary Fredholm determinant in the reflected negative-zero convention. -/
def gammaSewnCriticalPhysicalPluckerOrdinaryStableEntireDet (u : ℂ) : ℂ :=
  Complex.exp (u * gammaSewnCriticalPhysicalPluckerSourceTrace) *
    gammaSewnCriticalPhysicalPluckerStableEntireDet2 u

theorem gammaSewnCriticalPhysicalPluckerOrdinaryStableEntireDet_zero_re_im {u : ℂ}
    (hu : gammaSewnCriticalPhysicalPluckerOrdinaryStableEntireDet u = 0) :
    u.re < 0 ∧ u.im = 0 := by
  have hstable : gammaSewnCriticalPhysicalPluckerStableEntireDet2 u = 0 :=
    (mul_eq_zero.mp hu).resolve_left (Complex.exp_ne_zero _)
  exact gammaSewnCriticalPhysicalPluckerStableEntireDet2_zero_re_im hstable

theorem differentiable_gammaSewnCriticalPhysicalPluckerOrdinaryStableEntireDet :
    Differentiable ℂ gammaSewnCriticalPhysicalPluckerOrdinaryStableEntireDet := by
  exact (Complex.differentiable_exp.comp
    (differentiable_id.mul_const gammaSewnCriticalPhysicalPluckerSourceTrace)).mul
      differentiable_gammaSewnCriticalPhysicalPluckerStableEntireDet2

theorem gammaSewnCriticalPhysicalPluckerStableEntireDet2_zero_value :
    gammaSewnCriticalPhysicalPluckerStableEntireDet2 0 = 1 := by
  rw [gammaSewnCriticalPhysicalPluckerStableEntireDet2, neg_zero]
  exact (GaloisForLFunctions.HTGeometry.isRegularizedDet_entireDet2
    gammaSewnCriticalPhysicalPluckerKernel_isHS).eq_one_at_zero

/-- Trace counterterm restores the missing first derivative exactly. -/
theorem gammaSewnCriticalPhysicalPluckerOrdinaryStableEntireDet_deriv_zero :
    deriv gammaSewnCriticalPhysicalPluckerOrdinaryStableEntireDet 0 =
      gammaSewnCriticalPhysicalPluckerSourceTrace := by
  have hexp : HasDerivAt
      (fun u : ℂ => Complex.exp (u * gammaSewnCriticalPhysicalPluckerSourceTrace))
      gammaSewnCriticalPhysicalPluckerSourceTrace 0 := by
    simpa using ((hasDerivAt_id (𝕜 := ℂ) 0).mul_const
      gammaSewnCriticalPhysicalPluckerSourceTrace).cexp
  have hstable :
      HasDerivAt gammaSewnCriticalPhysicalPluckerStableEntireDet2 0 0 :=
    differentiable_gammaSewnCriticalPhysicalPluckerStableEntireDet2.differentiableAt.hasDerivAt
      |>.congr_deriv gammaSewnCriticalPhysicalPluckerStableEntireDet2_deriv_zero
  change deriv
    ((fun u : ℂ => Complex.exp
      (u * gammaSewnCriticalPhysicalPluckerSourceTrace)) *
      gammaSewnCriticalPhysicalPluckerStableEntireDet2) 0 =
        gammaSewnCriticalPhysicalPluckerSourceTrace
  rw [deriv_mul hexp.differentiableAt hstable.differentiableAt,
    hexp.deriv, hstable.deriv]
  simp [gammaSewnCriticalPhysicalPluckerStableEntireDet2_zero_value]

/-- The repaired determinant's first Xi identity is exactly one explicit source-mass identity. -/
theorem gammaSewnCriticalPhysicalPluckerOrdinary_firstJet_eq_theta_iff :
    deriv gammaSewnCriticalPhysicalPluckerOrdinaryStableEntireDet 0 =
        ((thetaCuspNormalizedEvenMoment 1 / 2 : ℝ) : ℂ) ↔
      gammaSewnCriticalPhysicalPluckerNuclearTraceMass =
        thetaCuspNormalizedEvenMoment 1 / 2 := by
  rw [gammaSewnCriticalPhysicalPluckerOrdinaryStableEntireDet_deriv_zero,
    gammaSewnCriticalPhysicalPluckerSourceTrace_eq_nuclearTraceMass]
  exact Complex.ofReal_inj

/-- Trace of a finite physical coordinate compression. -/
def gammaSewnCriticalPhysicalPluckerFiniteTrace
    (s : Finset GammaSewnCriticalPhysicalPluckerIndex) : ℂ :=
  (HilbertSchmidt.blockMatrix gammaSewnCriticalPhysicalPluckerKernel s).trace

/-- Finite ordinary determinant, initially expressed by the same trace counterterm. -/
def gammaSewnCriticalPhysicalPluckerOrdinaryStableFiniteDet
    (s : Finset GammaSewnCriticalPhysicalPluckerIndex) (u : ℂ) : ℂ :=
  Complex.exp (u * gammaSewnCriticalPhysicalPluckerFiniteTrace s) *
    gammaSewnCriticalPhysicalPluckerStableFiniteDet2 s u

/-- At every finite stage the restored determinant is literally `det (1 + u T_s)`. -/
theorem gammaSewnCriticalPhysicalPluckerOrdinaryStableFiniteDet_eq_det
    (s : Finset GammaSewnCriticalPhysicalPluckerIndex) (u : ℂ) :
    gammaSewnCriticalPhysicalPluckerOrdinaryStableFiniteDet s u =
      (1 + u • HilbertSchmidt.blockMatrix
        gammaSewnCriticalPhysicalPluckerKernel s).det := by
  rw [gammaSewnCriticalPhysicalPluckerOrdinaryStableFiniteDet,
    gammaSewnCriticalPhysicalPluckerStableFiniteDet2,
    gammaSewnCriticalPhysicalPluckerFiniteDet2,
    GaloisForLFunctions.HTGeometry.finiteDet2]
  simp only [gammaSewnCriticalPhysicalPluckerFiniteTrace, neg_smul, smul_neg,
    neg_neg, Matrix.trace_neg]
  let M := HilbertSchmidt.blockMatrix gammaSewnCriticalPhysicalPluckerKernel s
  change Complex.exp (u * M.trace) *
      ((1 + u • M).det * Complex.exp (-(-u * -M.trace))) = (1 + u • M).det
  have harg : -(-u * -M.trace) = -(u * M.trace) := by ring
  rw [harg]
  calc
    _ = (1 + u • M).det *
        (Complex.exp (u * M.trace) * Complex.exp (-(u * M.trace))) := by ring
    _ = (1 + u • M).det * Complex.exp
        (u * M.trace + -(u * M.trace)) := by rw [Complex.exp_add]
    _ = _ := by simp

theorem gammaSewnCriticalPhysicalPluckerOrdinaryStableFiniteDet_zero_re_im
    (s : Finset GammaSewnCriticalPhysicalPluckerIndex) {u : ℂ}
    (hu : gammaSewnCriticalPhysicalPluckerOrdinaryStableFiniteDet s u = 0) :
    u.re < 0 ∧ u.im = 0 := by
  have hstable : gammaSewnCriticalPhysicalPluckerStableFiniteDet2 s u = 0 :=
    (mul_eq_zero.mp hu).resolve_left (Complex.exp_ne_zero _)
  exact gammaSewnCriticalPhysicalPluckerStableFiniteDet2_zero_re_im s hstable

theorem gammaSewnCriticalPhysicalPluckerSourceTrace_eq_tsum_kernel_diag :
    gammaSewnCriticalPhysicalPluckerSourceTrace =
      ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
        gammaSewnCriticalPhysicalPluckerKernel (u, u) := by
  rw [gammaSewnCriticalPhysicalPluckerSourceTrace_eq_tsum_lpBasis]
  apply tsum_congr
  intro u
  rw [← gammaSewnCriticalPhysicalPluckerKernel_toOperator]
  exact HilbertSchmidt.inner_lpBasis_toOperator
    gammaSewnCriticalPhysicalPluckerKernel_isHS u

theorem summable_gammaSewnCriticalPhysicalPluckerKernel_diag :
    Summable (fun u : GammaSewnCriticalPhysicalPluckerIndex =>
      gammaSewnCriticalPhysicalPluckerKernel (u, u)) := by
  have hsum :=
    gammaSewnCriticalPhysicalPluckerSpectralOperator_memSchattenClass_one
      |>.one_summable_inner_diag_basis
        (HilbertSchmidt.lpBasis GammaSewnCriticalPhysicalPluckerIndex)
  apply hsum.congr
  intro u
  rw [← gammaSewnCriticalPhysicalPluckerKernel_toOperator]
  exact HilbertSchmidt.inner_lpBasis_toOperator
    gammaSewnCriticalPhysicalPluckerKernel_isHS u

theorem gammaSewnCriticalPhysicalPluckerFiniteTrace_eq_sum
    (s : Finset GammaSewnCriticalPhysicalPluckerIndex) :
    gammaSewnCriticalPhysicalPluckerFiniteTrace s =
      ∑ u ∈ s, gammaSewnCriticalPhysicalPluckerKernel (u, u) := by
  simp [gammaSewnCriticalPhysicalPluckerFiniteTrace, Matrix.trace,
    HilbertSchmidt.blockMatrix]
  exact Finset.sum_attach s
    (fun u => gammaSewnCriticalPhysicalPluckerKernel (u, u))

/-- Cofinal finite traces recover the operator trace. -/
theorem tendsto_gammaSewnCriticalPhysicalPluckerFiniteTrace :
    Tendsto gammaSewnCriticalPhysicalPluckerFiniteTrace atTop
      (nhds gammaSewnCriticalPhysicalPluckerSourceTrace) := by
  rw [gammaSewnCriticalPhysicalPluckerSourceTrace_eq_tsum_kernel_diag]
  rw [show gammaSewnCriticalPhysicalPluckerFiniteTrace = fun s =>
      ∑ u ∈ s, gammaSewnCriticalPhysicalPluckerKernel (u, u) by
    funext s
    exact gammaSewnCriticalPhysicalPluckerFiniteTrace_eq_sum s]
  exact summable_gammaSewnCriticalPhysicalPluckerKernel_diag.hasSum

/-- Every finite ordinary determinant converges pointwise to the restored entire determinant. -/
theorem tendsto_gammaSewnCriticalPhysicalPluckerOrdinaryStableFiniteDet (u : ℂ) :
    Tendsto (fun s : Finset GammaSewnCriticalPhysicalPluckerIndex =>
      gammaSewnCriticalPhysicalPluckerOrdinaryStableFiniteDet s u) atTop
      (nhds (gammaSewnCriticalPhysicalPluckerOrdinaryStableEntireDet u)) := by
  apply Tendsto.mul
  · exact Complex.continuous_exp.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul tendsto_gammaSewnCriticalPhysicalPluckerFiniteTrace)
  · exact tendsto_gammaSewnCriticalPhysicalPluckerStableFiniteDet2 u

end RHTower.HedenmalmThetaSource
