import GaloisForLFunctions.HTGeometry.LowDegreeHochschildFaceFlatness
import GaloisForLFunctions.RHTower.DeningerCofinalCountercharacterTopBoundaryTransgression
import GaloisForLFunctions.RHTower.MobiusThetaSourceDaggerMinimalBoundaryLaw

/-!
# Cofinal source homology of the physical paracyclic defect

Ordinary positive-degree Hochschild homology is the wrong receiver for the
physical source--dagger defect.  Finite Boolean source packets are already
contractible, while their contracting homotopies fail cofinal naturality at
one new top coordinate.  This file constructs that coordinate as the
canonical relative cokernel

`(next Tate stage) / (old-stage image)`.

The cokernel is one-dimensional.  Its distinguished generator is exactly
the rank-one naturality defect of the finite Tate forward arrows.  A global,
pre-divisor CCM landing sends a literal cyclic source chain to the relative
flat-minus-raw cofinal defect.  After specialization to the first nonzero Xi
jet, its canonical quotient coordinate is exactly the previously constructed
physical paracyclic-defect residue.

Thus "source-null-homology" is no longer an unspecified homology theory.  It
is vanishing of one explicit cofinal Bockstein class.  On every ordinary-prime
source atom that class vanishes exactly on the critical line; global vanishing
is equivalent to RH.  No global vanishing or RH assertion is assumed.
-/

open Complex
open GaloisForLFunctions.HTGeometry
open scoped TensorProduct

namespace RHTower

noncomputable section

/-! ## Why the degree-one trace is not ordinary homology -/

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Product trace on ordinary degree-one Hochschild chains. -/
def hochschildDegreeOneProductTrace (tau : A →ₗ[R] R) :
    A ⊗[R] A →ₗ[R] R :=
  tau.comp (LinearMap.mul' R A)

/-- A degree-one product trace does not generally annihilate degree-two
Hochschild boundaries: it reads the total product. -/
theorem hochschildDegreeOneProductTrace_boundaryTwoPure
    (tau : A →ₗ[R] R) (htrace : ∀ a b, tau (a * b) = tau (b * a))
    (a b c : A) :
    hochschildDegreeOneProductTrace tau
        (hochschildBoundaryTwoPure (R := R) a b c) =
      tau ((a * b) * c) := by
  simp [hochschildDegreeOneProductTrace, hochschildBoundaryTwoPure,
    mul_assoc]
  rw [htrace c (a * b), mul_assoc]

/-- If the trace of the unit is nonzero, the degree-one product trace cannot
descend through the ordinary Hochschild boundary quotient. -/
theorem not_forall_hochschildDegreeOneProductTrace_boundaryTwoPure_eq_zero
    [Nontrivial A] (tau : A →ₗ[R] R)
    (htrace : ∀ a b, tau (a * b) = tau (b * a))
    (hone : tau 1 ≠ 0) :
    ¬ ∀ a b c : A,
      hochschildDegreeOneProductTrace tau
        (hochschildBoundaryTwoPure (R := R) a b c) = 0 := by
  intro hall
  have h := hall 1 1 1
  rw [hochschildDegreeOneProductTrace_boundaryTwoPure tau htrace] at h
  apply hone
  simpa using h

/-! ## The one-dimensional cofinal relative source homology -/

/-- Coordinate omitted by the old-stage zero extension. -/
def tateClockCofinalTopCoordinate (m : ℕ) :
    (Fin (m + 2) → ℂ) →ₗ[ℂ] ℂ where
  toFun v := v (Fin.last (m + 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The old Tate stage is exactly the kernel of the new top-coordinate
reader. -/
theorem tateClockFinIntervalInclusion_range_eq_topCoordinate_ker (m : ℕ) :
    LinearMap.range (tateClockFinIntervalInclusion ℂ (m + 1)) =
      LinearMap.ker (tateClockCofinalTopCoordinate m) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simp [tateClockCofinalTopCoordinate,
      tateClockFinIntervalInclusion]
  · intro hy
    change y (Fin.last (m + 1)) = 0 at hy
    refine ⟨fun i => y i.castSucc, ?_⟩
    funext i
    by_cases hi : i.1 < m + 1
    · change (if h : i.1 < m + 1 then
          y (Fin.castSucc ⟨i.1, h⟩) else 0) = y i
      rw [dif_pos hi]
      congr 1
    · have hilast : i = Fin.last (m + 1) := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      subst i
      simp [tateClockFinIntervalInclusion, hy]

/-- Relative degree-one source homology created by adding one cofinal Tate
vertex.  The preceding theorem identifies its denominator with the literal
old-stage image. -/
abbrev TateClockCofinalRelativeH1 (m : ℕ) :=
  (Fin (m + 2) → ℂ) ⧸ LinearMap.ker (tateClockCofinalTopCoordinate m)

/-- The relative cofinal homology is canonically the omitted top-coordinate
line. -/
def tateClockCofinalRelativeH1Equiv (m : ℕ) :
    TateClockCofinalRelativeH1 m ≃ₗ[ℂ] ℂ :=
  (tateClockCofinalTopCoordinate m).quotKerEquivRange.trans
    (LinearEquiv.ofTop
      (LinearMap.range (tateClockCofinalTopCoordinate m))
      (LinearMap.range_eq_top.mpr (by
        intro z
        refine ⟨z • tateClockFinIntervalBasis ℂ
          (Fin.last (m + 1)), ?_⟩
        simp [tateClockCofinalTopCoordinate,
          tateClockFinIntervalBasis])))

@[simp]
theorem tateClockCofinalRelativeH1Equiv_mk
    (m : ℕ) (v : Fin (m + 2) → ℂ) :
    tateClockCofinalRelativeH1Equiv m (Submodule.Quotient.mk v) =
      v (Fin.last (m + 1)) := rfl

/-- Canonical cofinal Bockstein generator. -/
def tateClockCofinalRelativeGenerator
    (m : ℕ) : TateClockCofinalRelativeH1 m :=
  Submodule.Quotient.mk
    (tateClockFinIntervalTopBoundary ℂ m
      (tateClockFinIntervalBasis ℂ (Fin.last m)))

@[simp]
theorem tateClockCofinalRelativeH1Equiv_generator (m : ℕ) :
    tateClockCofinalRelativeH1Equiv m
      (tateClockCofinalRelativeGenerator m) = 1 := by
  simp [tateClockCofinalRelativeGenerator,
    tateClockFinIntervalTopBoundary_basis_last,
    tateClockFinIntervalBasis]

/-- The cofinal Bockstein generator is retained, not killed by the old-stage
image. -/
theorem tateClockCofinalRelativeGenerator_ne_zero (m : ℕ) :
    tateClockCofinalRelativeGenerator m ≠ 0 := by
  intro hzero
  have h := congrArg (tateClockCofinalRelativeH1Equiv m) hzero
  simp at h

/-! ## Actual cofinal naturality defect -/

/-- Naturality defect of a finite Tate forward arrow scaled by a complex
gain. -/
def tateClockScaledForwardNaturalityDefect
    (gain : ℂ) (m : ℕ) (f : Fin (m + 1) → ℂ) :
    Fin (m + 2) → ℂ :=
  (gain • tateClockFinIntervalForward ℂ (m + 1))
      (tateClockFinIntervalInclusion ℂ (m + 1) f) -
    tateClockFinIntervalInclusion ℂ (m + 1)
      ((gain • tateClockFinIntervalForward ℂ m) f)

/-- The scaled naturality defect is the scale times the literal rank-one top
boundary. -/
theorem tateClockScaledForwardNaturalityDefect_eq_topBoundary
    (gain : ℂ) (m : ℕ) (f : Fin (m + 1) → ℂ) :
    tateClockScaledForwardNaturalityDefect gain m f =
      gain • tateClockFinIntervalTopBoundary ℂ m f := by
  simp only [tateClockScaledForwardNaturalityDefect,
    LinearMap.smul_apply, map_smul]
  rw [tateClockFinIntervalForward_inclusion_defect]
  module

/-- Flat-minus-raw cofinal defect. -/
def tateClockFlatMinusRawCofinalDefect
    (gain : ℂ) (m : ℕ) (f : Fin (m + 1) → ℂ) :
    Fin (m + 2) → ℂ :=
  tateClockScaledForwardNaturalityDefect 1 m f -
    tateClockScaledForwardNaturalityDefect gain m f

/-- The flat-minus-raw defect has coefficient `1 - gain` on the retained
cofinal generator. -/
theorem tateClockFlatMinusRawCofinalDefect_eq_topBoundary
    (gain : ℂ) (m : ℕ) (f : Fin (m + 1) → ℂ) :
    tateClockFlatMinusRawCofinalDefect gain m f =
      (1 - gain) • tateClockFinIntervalTopBoundary ℂ m f := by
  rw [tateClockFlatMinusRawCofinalDefect,
    tateClockScaledForwardNaturalityDefect_eq_topBoundary,
    tateClockScaledForwardNaturalityDefect_eq_topBoundary]
  module

/-- The canonical cofinal generator is the quotient class of the unscaled
forward-arrow naturality defect. -/
theorem tateClockCofinalRelativeGenerator_eq_naturalityDefect
    (m : ℕ) :
    tateClockCofinalRelativeGenerator m =
      Submodule.Quotient.mk
        (tateClockScaledForwardNaturalityDefect 1 m
          (tateClockFinIntervalBasis ℂ (Fin.last m))) := by
  rw [tateClockScaledForwardNaturalityDefect_eq_topBoundary,
    one_smul]
  rfl

/-! ## Global arithmetic landing into cofinal relative homology -/

/-- Global pre-divisor landing of the literal CCM degree-one cyclic source
into cofinal relative source homology.  Jet grade `k`, Tate stage `m`, and
spectral parameter `w` remain independent. -/
def ccmMobiusThetaCofinalSourceHomologyLanding
    (n k m : ℕ) (s w : ℂ) :
    CCMRationalAdelicDegreeOneCyclicSource →ₗ[ℂ]
      TateClockCofinalRelativeH1 m where
  toFun x :=
    -(iteratedDeriv k XiC w * ccmRationalAdelicDegreeOneTrace x) •
      Submodule.Quotient.mk
        (tateClockFlatMinusRawCofinalDefect
          (deningerHalfDensityMateGain n s : ℂ) m
          (tateClockFinIntervalBasis ℂ (Fin.last m)))
  map_add' x y := by
    simp only [map_add, mul_add, neg_add_rev, add_smul]
    abel
  map_smul' c x := by
    simp only [map_smul, RingHom.id_apply, smul_eq_mul, smul_smul]
    congr 1
    ring

@[simp]
theorem ccmMobiusThetaCofinalSourceHomologyLanding_apply
    (n k m : ℕ) (s w : ℂ)
    (x : CCMRationalAdelicDegreeOneCyclicSource) :
    ccmMobiusThetaCofinalSourceHomologyLanding n k m s w x =
      -(iteratedDeriv k XiC w * ccmRationalAdelicDegreeOneTrace x) •
        Submodule.Quotient.mk
          (tateClockFlatMinusRawCofinalDefect
            (deningerHalfDensityMateGain n s : ℂ) m
            (tateClockFinIntervalBasis ℂ (Fin.last m))) := rfl

/-- **Cofinal source transgression law.**  The canonical coordinate of the
global relative homology class is the analytic monodromy defect times the
independently graded Xi jet and the literal arithmetic trace. -/
theorem ccmMobiusThetaCofinalSourceHomologyLanding_readout
    (n k m : ℕ) (s w : ℂ)
    (x : CCMRationalAdelicDegreeOneCyclicSource) :
    tateClockCofinalRelativeH1Equiv m
        (ccmMobiusThetaCofinalSourceHomologyLanding n k m s w x) =
      ((deningerHalfDensityMateGain n s : ℂ) - 1) *
        iteratedDeriv k XiC w * ccmRationalAdelicDegreeOneTrace x := by
  rw [ccmMobiusThetaCofinalSourceHomologyLanding_apply,
    map_smul, tateClockFlatMinusRawCofinalDefect_eq_topBoundary]
  simp [tateClockFinIntervalTopBoundary_basis_last,
    tateClockFinIntervalBasis]
  ring

/-- At the first nonzero Xi jet, the cofinal relative source-homology
coordinate is exactly the physical two-leg paracyclic-defect residue. -/
theorem ccmMobiusThetaCofinalSourceHomologyLanding_readout_eq_physicalDefect
    (n m : ℕ) (rho : XiDivisorSupport)
    (x : CCMRationalAdelicDegreeOneCyclicSource) :
    tateClockCofinalRelativeH1Equiv m
        (ccmMobiusThetaCofinalSourceHomologyLanding n
          (xiSupportMultiplicity rho) m (rho : ℂ)
          (xiSpectralPointSupport rho) x) =
      ccmRationalAdelicTwoLegCyclicResidue
        (cyclicParacyclicEquivarianceDefect
          ccmRationalAdelicDegreeOneCyclicRotation
          (sourceDaggerNormalizedDegreeOneRotationLinear n (rho : ℂ))
          (ccmMobiusThetaXiJetTwoLegLanding
            (xiSupportMultiplicity rho)
            (xiSpectralPointSupport rho)) x) := by
  rw [ccmMobiusThetaCofinalSourceHomologyLanding_readout,
    ccmMobiusThetaTwoLegParacyclicDefect_residue,
    thetaInternalJetLeadingSourceCoefficient_eq]

/-! ## Exact null-homology wall -/

/-- Mate gain is one exactly on the critical half-density line. -/
theorem deningerHalfDensityMateGain_eq_one_iff_re_eq_half
    {n : ℕ} (hn : 2 ≤ n) (s : ℂ) :
    deningerHalfDensityMateGain n s = 1 ↔ s.re = 1 / 2 := by
  constructor
  · intro hgain
    rw [deningerHalfDensityMateGain] at hgain
    have hexp := (Real.exp_eq_one_iff _).mp hgain
    have hlog : 0 < Real.log (n : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (lt_of_lt_of_le one_lt_two hn)
    rcases mul_eq_zero.mp hexp with hre | hnlog
    · linarith
    · exact False.elim (ne_of_gt hlog hnlog)
  · intro hline
    rw [deningerHalfDensityMateGain]
    have hre : 2 * s.re - 1 = 0 := by linarith
    rw [hre, zero_mul, Real.exp_zero]

/-- Meaning of source-null-homology for the physical ordinary-prime defect
in the canonical cofinal relative complex. -/
def CCMMobiusThetaPhysicalDefectSourceNullHomologous
    (n : ℕ) (rho : XiDivisorSupport) (p : Nat.Primes) (m : ℕ) : Prop :=
  ccmMobiusThetaCofinalSourceHomologyLanding n
      (xiSupportMultiplicity rho) m (rho : ℂ)
      (xiSpectralPointSupport rho)
      (ccmRationalAdelicOrdinaryPrimeCycleAtom p) = 0

/-- The constructed physical class is source-null-homologous exactly on the
critical line.  Finite cyclic exactness supplies no stronger annihilation. -/
theorem ccmMobiusThetaPhysicalDefectSourceNullHomologous_iff
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport)
    (p : Nat.Primes) (m : ℕ) :
    CCMMobiusThetaPhysicalDefectSourceNullHomologous n rho p m ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro hnull
    have hread := congrArg (tateClockCofinalRelativeH1Equiv m) hnull
    rw [ccmMobiusThetaCofinalSourceHomologyLanding_readout,
      ccmRationalAdelicOrdinaryPrimeCycleAtom_trace_eq_one,
      mul_one, map_zero] at hread
    have hjet := iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho
    have hgainC : (deningerHalfDensityMateGain n (rho : ℂ) : ℂ) - 1 = 0 :=
      (mul_eq_zero.mp hread).resolve_right hjet
    have hgain : deningerHalfDensityMateGain n (rho : ℂ) = 1 := by
      exact_mod_cast (sub_eq_zero.mp hgainC)
    exact (deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn _).mp hgain
  · intro hline
    have hgain :=
      (deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn (rho : ℂ)).2 hline
    rw [CCMMobiusThetaPhysicalDefectSourceNullHomologous,
      ccmMobiusThetaCofinalSourceHomologyLanding_apply,
      tateClockFlatMinusRawCofinalDefect_eq_topBoundary,
      hgain]
    norm_num

/-- Global source-null-homology of the physical ordinary-prime defect. -/
def CCMMobiusThetaEveryPhysicalDefectSourceNullHomologous
    (n : ℕ) (p : Nat.Primes) (m : ℕ) : Prop :=
  ∀ rho : XiDivisorSupport,
    CCMMobiusThetaPhysicalDefectSourceNullHomologous n rho p m

/-- **Exact frontier theorem.**  Global null-homology of the physical
paracyclic defect in the constructed cofinal relative source complex is
equivalent to RH.  The construction is unconditional; the global vanishing
side is not asserted. -/
theorem ccmMobiusThetaEveryPhysicalDefectSourceNullHomologous_iff_riemannHypothesis
    {n : ℕ} (hn : 2 ≤ n) (p : Nat.Primes) (m : ℕ) :
    CCMMobiusThetaEveryPhysicalDefectSourceNullHomologous n p m ↔
      RiemannHypothesis := by
  rw [← xiBoundaryCharacterNeutral_iff_riemannHypothesis]
  unfold CCMMobiusThetaEveryPhysicalDefectSourceNullHomologous
    XiBoundaryCharacterNeutral
  apply forall_congr'
  intro rho
  rw [ccmMobiusThetaPhysicalDefectSourceNullHomologous_iff hn]
  exact (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff (rho : ℂ)).symm

end

end RHTower
