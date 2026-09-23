import GaloisForLFunctions.RHTower.DeningerGammaSixCofinalSingularGraphSoninTransport
import GaloisForLFunctions.RHTower.MobiusThetaPhysicalParacyclicSourceNullHomology
import GaloisForLFunctions.RHTower.DeningerMeyerReflectedGaussianCompletedGreenDefect

/-!
# Cofinal Meyer--Tate boundary of the completed Xi Green fibre

The singular Gamma-six graph has a vertical generator, but graph density alone
does not make that generator an arithmetic boundary.  This module constructs
the missing finite differential from literal cofinal Tate naturality defects.
Each stage atom is the failure of the finite Tate forward arrow to commute
with zero extension.  A top-coordinate retraction proves that this
differential loses no cofinal coefficient.

Tensoring with the actual rational-adelic CCM degree-one cyclic source retains
ordinary-prime provenance.  Every ordinary-prime cycle atom has arithmetic
trace one, so its Meyer--Tate differential is exactly the Tate naturality
boundary.  Uniform source chains then converge after graph completion to the
vertical generator.

Finally the chains are weighted by the already constructed reflected-Gaussian
completed Green coefficient at an actual Xi divisor copy.  Their completed
differentials converge to a vertical class whose graph trace is exactly that
existing Green fibre and whose ambient `ell^(2 : ℕ)` projection is zero.  Actual
Gamma/Sonin transport of every finite chain and of its limit is the same
fixed physical receiver with that coefficient.

No boundary annihilation is asserted.  The final zero-set theorem shows that
annihilating this concrete completed arithmetic boundary is still exactly the
critical-line operation.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped TensorProduct ENNReal

namespace RHTower

noncomputable section

/-! ## Literal cofinal Tate naturality differential -/

/-- Disjoint union of the finite Tate boundary coordinates at all cofinal
stages. -/
abbrev DeningerGammaSixCofinalTateBoundaryIndex :=
  Sigma fun m : ℕ => Fin (m + 2)

/-- Algebraic direct sum of the literal finite Tate boundary stages. -/
abbrev DeningerGammaSixCofinalTateBoundaryCarrier :=
  DeningerGammaSixCofinalTateBoundaryIndex →₀ ℂ

/-- The outgoing top coordinate at cofinal stage `m`. -/
def deningerGammaSixCofinalTateNaturalityAtom
    (m : ℕ) : DeningerGammaSixCofinalTateBoundaryCarrier :=
  Finsupp.single ⟨m, Fin.last (m + 1)⟩ 1

/-- Cofinal differential assembled from the outgoing Tate naturality atoms. -/
def deningerGammaSixCofinalTateNaturalityDifferential :
    DeningerGammaSixCofinalFinitePacket →ₗ[ℂ]
      DeningerGammaSixCofinalTateBoundaryCarrier :=
  Finsupp.lsum ℂ fun m =>
    LinearMap.toSpanSingleton ℂ DeningerGammaSixCofinalTateBoundaryCarrier
      (deningerGammaSixCofinalTateNaturalityAtom m)

@[simp] theorem deningerGammaSixCofinalTateNaturalityDifferential_single
    (m : ℕ) (z : ℂ) :
    deningerGammaSixCofinalTateNaturalityDifferential
        (Finsupp.single m z) =
      z • deningerGammaSixCofinalTateNaturalityAtom m := by
  simp [deningerGammaSixCofinalTateNaturalityDifferential]

/-- Each direct-sum atom is not a formal basis declaration: on its finite
stage it is exactly the commutator of Tate forward transport with cofinal
zero extension. -/
theorem deningerGammaSixCofinalTateNaturalityAtom_stage
    (m : ℕ) (i : Fin (m + 2)) :
    deningerGammaSixCofinalTateNaturalityAtom m ⟨m, i⟩ =
      tateClockScaledForwardNaturalityDefect 1 m
        (tateClockFinIntervalBasis ℂ (Fin.last m)) i := by
  rw [tateClockScaledForwardNaturalityDefect_eq_topBoundary, one_smul,
    tateClockFinIntervalTopBoundary_basis_last]
  simp [deningerGammaSixCofinalTateNaturalityAtom,
    tateClockFinIntervalBasis, Finsupp.single_apply, Sigma.ext_iff,
    eq_comm]

/-- Read the new top coordinate at every Tate stage. -/
def deningerGammaSixCofinalTateTopReadout :
    DeningerGammaSixCofinalTateBoundaryCarrier →ₗ[ℂ]
      DeningerGammaSixCofinalFinitePacket :=
  Finsupp.lsum ℂ fun i =>
    LinearMap.toSpanSingleton ℂ DeningerGammaSixCofinalFinitePacket
      (if i.2 = Fin.last (i.1 + 1) then Finsupp.single i.1 1 else 0)

@[simp] theorem deningerGammaSixCofinalTateTopReadout_atom (m : ℕ) :
    deningerGammaSixCofinalTateTopReadout
        (deningerGammaSixCofinalTateNaturalityAtom m) =
      Finsupp.single m 1 := by
  simp [deningerGammaSixCofinalTateTopReadout,
    deningerGammaSixCofinalTateNaturalityAtom]

/-- Exact left inverse: the literal Tate differential retains every cofinal
depth coefficient. -/
theorem deningerGammaSixCofinalTateTopReadout_comp_naturalityDifferential :
    deningerGammaSixCofinalTateTopReadout.comp
        deningerGammaSixCofinalTateNaturalityDifferential =
      LinearMap.id := by
  apply Finsupp.lhom_ext
  intro m z
  simp

theorem deningerGammaSixCofinalTateNaturalityDifferential_injective :
    Function.Injective deningerGammaSixCofinalTateNaturalityDifferential := by
  intro c d h
  have h' := congrArg deningerGammaSixCofinalTateTopReadout h
  have hc :
      deningerGammaSixCofinalTateTopReadout
          (deningerGammaSixCofinalTateNaturalityDifferential c) = c := by
    exact LinearMap.congr_fun
      deningerGammaSixCofinalTateTopReadout_comp_naturalityDifferential c
  have hd :
      deningerGammaSixCofinalTateTopReadout
          (deningerGammaSixCofinalTateNaturalityDifferential d) = d := by
    exact LinearMap.congr_fun
      deningerGammaSixCofinalTateTopReadout_comp_naturalityDifferential d
  rwa [hc, hd] at h'

/-! ## Rational-adelic degree-one source and completed boundary -/

/-- Literal rational-adelic CCM degree-one cyclic source tensored with the
cofinal Tate depth packet. -/
abbrev DeningerGammaSixCofinalMeyerTateDegreeOneSource :=
  CCMRationalAdelicDegreeOneCyclicSource ⊗[ℂ]
    DeningerGammaSixCofinalFinitePacket

/-- Arithmetic degree-one differential: contract the actual CCM cyclic
source by its product trace and apply the literal Tate naturality
differential on the cofinal leg. -/
def deningerGammaSixCofinalMeyerTateDifferential :
    DeningerGammaSixCofinalMeyerTateDegreeOneSource →ₗ[ℂ]
      DeningerGammaSixCofinalTateBoundaryCarrier :=
  (TensorProduct.lid ℂ
      DeningerGammaSixCofinalTateBoundaryCarrier).toLinearMap.comp
    (TensorProduct.map ccmRationalAdelicDegreeOneTrace
      deningerGammaSixCofinalTateNaturalityDifferential)

@[simp] theorem deningerGammaSixCofinalMeyerTateDifferential_tmul
    (x : CCMRationalAdelicDegreeOneCyclicSource)
    (c : DeningerGammaSixCofinalFinitePacket) :
    deningerGammaSixCofinalMeyerTateDifferential (x ⊗ₜ[ℂ] c) =
      ccmRationalAdelicDegreeOneTrace x •
        deningerGammaSixCofinalTateNaturalityDifferential c := by
  simp [deningerGammaSixCofinalMeyerTateDifferential]

/-- Every literal ordinary-prime CCM cycle atom has trace one, so its
arithmetic differential is the full cofinal Tate boundary, without a scalar
loss. -/
@[simp] theorem deningerGammaSixCofinalMeyerTateDifferential_primeAtom
    (p : Nat.Primes) (c : DeningerGammaSixCofinalFinitePacket) :
    deningerGammaSixCofinalMeyerTateDifferential
        (ccmRationalAdelicOrdinaryPrimeCycleAtom p ⊗ₜ[ℂ] c) =
      deningerGammaSixCofinalTateNaturalityDifferential c := by
  rw [deningerGammaSixCofinalMeyerTateDifferential_tmul,
    ccmRationalAdelicOrdinaryPrimeCycleAtom_trace_eq_one, one_smul]

/-- Decode literal Tate top boundaries into the source-selected singular
Gamma graph. -/
def deningerGammaSixCofinalTateGraphBoundary :
    DeningerGammaSixCofinalTateBoundaryCarrier →ₗ[ℂ]
      DeningerGammaSixCofinalSingularGraph :=
  deningerGammaSixCofinalFiniteGraphAdmission.comp
    deningerGammaSixCofinalTateTopReadout

/-- Completed Meyer--Tate differential into the singular Gamma graph. -/
def deningerGammaSixCofinalMeyerTateCompletedDifferential :
    DeningerGammaSixCofinalMeyerTateDegreeOneSource →ₗ[ℂ]
      DeningerGammaSixCofinalSingularGraph :=
  deningerGammaSixCofinalTateGraphBoundary.comp
    deningerGammaSixCofinalMeyerTateDifferential

/-- Strict source-to-graph chain law on every ordinary-prime atom. -/
@[simp] theorem deningerGammaSixCofinalMeyerTateCompletedDifferential_primeAtom
    (p : Nat.Primes) (c : DeningerGammaSixCofinalFinitePacket) :
    deningerGammaSixCofinalMeyerTateCompletedDifferential
        (ccmRationalAdelicOrdinaryPrimeCycleAtom p ⊗ₜ[ℂ] c) =
      deningerGammaSixCofinalFiniteGraphAdmission c := by
  rw [deningerGammaSixCofinalMeyerTateCompletedDifferential,
    LinearMap.comp_apply,
    deningerGammaSixCofinalMeyerTateDifferential_primeAtom,
    deningerGammaSixCofinalTateGraphBoundary, LinearMap.comp_apply]
  have h := LinearMap.congr_fun
    deningerGammaSixCofinalTateTopReadout_comp_naturalityDifferential c
  exact congrArg deningerGammaSixCofinalFiniteGraphAdmission h

/-- The actual Meyer--Tate differential has dense range in the singular
graph: one fixed ordinary-prime atom already realizes every finite graph
packet. -/
theorem deningerGammaSixCofinalMeyerTateCompletedDifferential_dense :
    DenseRange deningerGammaSixCofinalMeyerTateCompletedDifferential := by
  apply deningerGammaSixCofinalFiniteGraphAdmission_dense.mono
  rintro z ⟨c, rfl⟩
  exact
    ⟨ccmRationalAdelicOrdinaryPrimeCycleAtom ⟨2, by norm_num⟩ ⊗ₜ[ℂ] c,
      deningerGammaSixCofinalMeyerTateCompletedDifferential_primeAtom
        ⟨2, by norm_num⟩ c⟩

/-- **Universal continuous-Stokes no-go.**  Since the arithmetic boundary
range is dense, any continuous graph reader annihilating every Meyer--Tate
boundary is the zero reader.  The required RH-bearing Stokes law must
therefore annihilate the distinguished Xi Green chain by extra arithmetic
structure; it cannot be universal continuous boundary-blindness on this
completion. -/
theorem continuousLinearMap_eq_zero_of_forall_meyerTateBoundary_eq_zero
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (F : DeningerGammaSixCofinalSingularGraph →L[ℂ] Y)
    (hF : ∀ x : DeningerGammaSixCofinalMeyerTateDegreeOneSource,
      F (deningerGammaSixCofinalMeyerTateCompletedDifferential x) = 0) :
    F = 0 := by
  apply DFunLike.coe_injective
  refine
    deningerGammaSixCofinalMeyerTateCompletedDifferential_dense.equalizer
      F.continuous
      (0 : DeningerGammaSixCofinalSingularGraph →L[ℂ] Y).continuous ?_
  funext x
  simpa using hF x

/-! ## Divisor- and multiplicity-faithful Xi Green boundary -/

/-- Vertical graph boundary carrying exactly the fixed reflected-Gaussian
completed Green coefficient at one actual divisor copy.  `XiZeroCopy`
retains divisor multiplicity. -/
def deningerGammaSixCofinalXiGreenVerticalBoundary
    (q : XiZeroCopy) : DeningerGammaSixCofinalSingularGraph :=
  DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance q •
    deningerGammaSixCofinalGraphSingularVector

/-- Explicit ordinary-prime, divisor-copy, and cofinal-depth source chain
whose boundary approaches the completed Xi Green vertical class. -/
def deningerGammaSixCofinalXiGreenDegreeOneChain
    (p : Nat.Primes) (q : XiZeroCopy) (n : ℕ) :
    DeningerGammaSixCofinalMeyerTateDegreeOneSource :=
  ccmRationalAdelicOrdinaryPrimeCycleAtom p ⊗ₜ[ℂ]
    (DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance q •
      deningerGammaSixCofinalAveragingPacket n)

/-- **Completed arithmetic-boundary production.**  Literal CCM prime-cycle
chains tensored with actual Tate naturality defects converge, after the
source-selected Gamma graph completion, to the vertical generator weighted
by the existing completed Xi Green fibre. -/
theorem tendsto_deningerGammaSixCofinalMeyerTateCompletedDifferential_xiGreenChain
    (p : Nat.Primes) (q : XiZeroCopy) :
    Tendsto
      (fun n => deningerGammaSixCofinalMeyerTateCompletedDifferential
        (deningerGammaSixCofinalXiGreenDegreeOneChain p q n))
      atTop (nhds (deningerGammaSixCofinalXiGreenVerticalBoundary q)) := by
  simpa [deningerGammaSixCofinalXiGreenDegreeOneChain,
    deningerGammaSixCofinalXiGreenVerticalBoundary, map_smul] using
    tendsto_deningerGammaSixCofinalFiniteGraphAdmission_averagingPacket.const_smul
      (DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance q)

/-- Singular trace of the completed boundary is exactly the already fixed
completed Xi Green fibre, not a newly declared quotient coefficient. -/
@[simp] theorem deningerGammaSixCofinalGraphTrace_xiGreenVerticalBoundary
    (q : XiZeroCopy) :
    deningerGammaSixCofinalGraphTrace
        (deningerGammaSixCofinalXiGreenVerticalBoundary q) =
      DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance q := by
  simp [deningerGammaSixCofinalXiGreenVerticalBoundary]

/-- The same completed boundary is invisible in the old ambient cofinal
`ell^(2 : ℕ)` carrier. -/
@[simp] theorem
    deningerGammaSixCofinalGraphAmbientProjection_xiGreenVerticalBoundary
    (q : XiZeroCopy) :
    deningerGammaSixCofinalGraphAmbientProjection
        (deningerGammaSixCofinalXiGreenVerticalBoundary q) = 0 := by
  simp [deningerGammaSixCofinalXiGreenVerticalBoundary]

/-- Exact pointwise radical of the existing completed Green coefficient. -/
theorem reflectedGaussianHorizonGreenProvenance_apply_eq_zero_iff
    (q : XiZeroCopy) :
    DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  change DeningerMeyerGaussianGreen.deningerArithmeticCompletedGreenProvenance
      DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2 q = 0 ↔ _
  rw [DeningerMeyerGaussianGreen.deningerArithmeticCompletedGreenProvenance_apply]
  have hhodge :
      deningerArithmeticOrientedHodgeLp
          (DeningerMeyerGaussianGreen.deningerArithmeticCompletedRieszConjugation
            DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2) q ≠ 0 := by
    rw [deningerArithmeticOrientedHodgeLp_apply,
      DeningerMeyerGaussianGreen.deningerArithmeticCompletedRieszConjugation_apply]
    apply mul_ne_zero
    · exact neg_ne_zero.mpr (deningerArithmeticFEOrientation_ne_zero q)
    · rw [starRingEnd_self_apply]
      exact DeningerMeyerGaussianGreen.reflectedGaussianHorizonGrade_ne_zero
        (xiZeroCopyReflectEquiv q)
  rw [mul_eq_zero]
  simp only [hhodge, or_false]
  exact xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff (q.1 : ℂ)

/-- The completed arithmetic boundary itself is zero exactly on the critical
line.  Completion has retained, rather than assumed away, the RH detector. -/
theorem deningerGammaSixCofinalXiGreenVerticalBoundary_eq_zero_iff
    (q : XiZeroCopy) :
    deningerGammaSixCofinalXiGreenVerticalBoundary q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [deningerGammaSixCofinalXiGreenVerticalBoundary, smul_eq_zero]
  simp only [deningerGammaSixCofinalGraphSingularVector_ne_zero, or_false]
  exact reflectedGaussianHorizonGreenProvenance_apply_eq_zero_iff q

/-! ## Strict actual-Gamma/Sonin transport -/

/-- Transport of the completed arithmetic boundary is exactly the fixed
Sonin receiver at the divisor's total horizontal grade, weighted by the
existing completed Green fibre. -/
@[simp] theorem deningerGammaSixCofinalGraphPhysicalTransport_xiGreenBoundary
    (q : XiZeroCopy) :
    deningerGammaSixCofinalGraphPhysicalTransport
        (2 * (q.1 : ℂ).re - 1)
        (deningerGammaSixCofinalXiGreenVerticalBoundary q) =
      DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance q •
        deningerGammaSixFixedSoninPhysicalReceiver
          (2 * (q.1 : ℂ).re - 1) := by
  rw [deningerGammaSixCofinalXiGreenVerticalBoundary, map_smul,
    deningerGammaSixCofinalGraphPhysicalTransport_singularVector]

/-- Every finite arithmetic chain already has exactly the same strict
actual-Gamma/Sonin value as its completed vertical limit. -/
theorem deningerGammaSixCofinalGraphPhysicalTransport_xiGreenFiniteChain
    (p : Nat.Primes) (q : XiZeroCopy) (n : ℕ) :
    deningerGammaSixCofinalGraphPhysicalTransport
        (2 * (q.1 : ℂ).re - 1)
        (deningerGammaSixCofinalMeyerTateCompletedDifferential
          (deningerGammaSixCofinalXiGreenDegreeOneChain p q n)) =
      DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance q •
        deningerGammaSixFixedSoninPhysicalReceiver
          (2 * (q.1 : ℂ).re - 1) := by
  rw [deningerGammaSixCofinalXiGreenDegreeOneChain,
    deningerGammaSixCofinalMeyerTateCompletedDifferential_primeAtom,
    map_smul, map_smul,
    deningerGammaSixCofinalGraphPhysicalTransport_finiteGraph,
    deningerGammaSixCofinalFiniteActualGammaTransport_averagingPacket]

/-- **Exact remaining wall.**  The strict physical image of the concrete
completed Meyer--Tate Xi Green boundary vanishes exactly on the critical
line.  A future source Stokes theorem annihilating this already-constructed
image would therefore be the genuine RH-bearing operation. -/
theorem deningerGammaSixCofinalGraphPhysicalTransport_xiGreenBoundary_eq_zero_iff
    (q : XiZeroCopy) :
    deningerGammaSixCofinalGraphPhysicalTransport
        (2 * (q.1 : ℂ).re - 1)
        (deningerGammaSixCofinalXiGreenVerticalBoundary q) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [deningerGammaSixCofinalGraphPhysicalTransport_xiGreenBoundary,
    smul_eq_zero, reflectedGaussianHorizonGreenProvenance_apply_eq_zero_iff,
    deningerGammaSixFixedSoninPhysicalReceiver_eq_zero_iff]
  have hgrade :
      2 * (q.1 : ℂ).re - 1 = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
    constructor <;> intro h <;> linarith
  rw [hgrade, or_self]

end

end RHTower
