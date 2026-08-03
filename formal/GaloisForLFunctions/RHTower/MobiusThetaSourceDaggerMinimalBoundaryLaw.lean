import GaloisForLFunctions.HTGeometry.CyclicParacyclicBoundaryDefectLaw
import GaloisForLFunctions.HTGeometry.GaussianSchwartz
import GaloisForLFunctions.RHTower.CCMRationalAdelicEpsilonZero
import GaloisForLFunctions.RHTower.CyclicBarTraceAugmentation
import GaloisForLFunctions.RHTower.FieldOneFiniteAdeleIntegralBruhatTest
import GaloisForLFunctions.RHTower.MobiusThetaInternalJetCofinalComplexLanding
import GaloisForLFunctions.RHTower.MobiusThetaInternalJetCompletedHellingerGammaIncidenceBridge
import GaloisForLFunctions.RHTower.SourceDaggerCyclicBoundaryDefectLaw

/-!
# Minimal source--dagger defect boundary

For any cyclic-to-paracyclic landing, there is a canonical smallest
target-stable boundary containing its equivariance defect: the sum of the
defect range and its first target-rotation image.  Every other admissible
boundary contains it.  Thus this minimal boundary gives the largest possible
quotient in which a landed atom could survive.

Away from unit monodromy the entire landing range lies in this minimal
boundary.  A surjective landing therefore makes it the whole target.  This is
an algebraic obstruction, independent of topology.

The second half instantiates the law with the already constructed first
nonzero Möbius--theta jet.  Its natural two-leg landing is nonzero and
surjective.  The canonical defect boundary is exactly bottom on the critical
line and exactly top off it.  Consequently its canonical atom survives in the
quotient exactly on the critical line.  This constructs the maximal boundary
candidate and proves that global quotient survival is precisely the remaining
RH-bearing statement; it does not assume that survival at all divisor points.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

variable {S V : Type*}
variable [AddCommGroup S] [Module ℂ S]
variable [AddCommGroup V] [Module ℂ V]

/-- Smallest candidate boundary: defect range plus its first target-rotation
image.  Under scalar-square target monodromy this sum is target-stable. -/
def cyclicParacyclicMinimalDefectBoundary
    (sourceRotate : S →ₗ[ℂ] S)
    (targetRotate : V →ₗ[ℂ] V)
    (land : S →ₗ[ℂ] V) : Submodule ℂ V :=
  LinearMap.range
      (cyclicParacyclicEquivarianceDefect sourceRotate targetRotate land) ⊔
    LinearMap.range
      (targetRotate.comp
        (cyclicParacyclicEquivarianceDefect sourceRotate targetRotate land))

/-- Every equivariance defect lies in the minimal defect boundary. -/
theorem cyclicParacyclicEquivarianceDefect_mem_minimalBoundary
    (sourceRotate : S →ₗ[ℂ] S)
    (targetRotate : V →ₗ[ℂ] V)
    (land : S →ₗ[ℂ] V) (x : S) :
    cyclicParacyclicEquivarianceDefect sourceRotate targetRotate land x ∈
      cyclicParacyclicMinimalDefectBoundary sourceRotate targetRotate land := by
  exact Submodule.mem_sup_left ⟨x, rfl⟩

/-- Scalar-square target rotation preserves the minimal defect boundary. -/
theorem cyclicParacyclicMinimalDefectBoundary_target_stable
    (sourceRotate : S →ₗ[ℂ] S)
    (targetRotate : V →ₗ[ℂ] V)
    (land : S →ₗ[ℂ] V) (delta : ℂ)
    (htarget : ∀ y, targetRotate (targetRotate y) = delta • y) :
    ∀ y ∈ cyclicParacyclicMinimalDefectBoundary sourceRotate targetRotate land,
      targetRotate y ∈
        cyclicParacyclicMinimalDefectBoundary sourceRotate targetRotate land := by
  intro y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add]
  apply Submodule.add_mem
  · obtain ⟨x, rfl⟩ := ha
    exact Submodule.mem_sup_right ⟨x, rfl⟩
  · obtain ⟨x, rfl⟩ := hb
    rw [LinearMap.comp_apply, htarget]
    exact Submodule.mem_sup_left
      ((LinearMap.range
        (cyclicParacyclicEquivarianceDefect sourceRotate targetRotate land)).smul_mem
          delta ⟨x, rfl⟩)

/-- Minimality: every target-stable submodule containing the defect contains
the canonical minimal boundary. -/
theorem cyclicParacyclicMinimalDefectBoundary_le
    (sourceRotate : S →ₗ[ℂ] S)
    (targetRotate : V →ₗ[ℂ] V)
    (land : S →ₗ[ℂ] V)
    (boundary : Submodule ℂ V)
    (hboundary : ∀ y ∈ boundary, targetRotate y ∈ boundary)
    (hdefect : ∀ x,
      cyclicParacyclicEquivarianceDefect sourceRotate targetRotate land x ∈ boundary) :
    cyclicParacyclicMinimalDefectBoundary sourceRotate targetRotate land ≤ boundary := by
  rw [cyclicParacyclicMinimalDefectBoundary, sup_le_iff]
  constructor
  · rintro y ⟨x, rfl⟩
    exact hdefect x
  · rintro y ⟨x, rfl⟩
    exact hboundary _ (hdefect x)

/-- The minimal boundary gives the maximal possible retained quotient: an
atom survives some admissible boundary exactly when it survives this one. -/
theorem not_mem_cyclicParacyclicMinimalDefectBoundary_iff_exists
    (sourceRotate : S →ₗ[ℂ] S)
    (targetRotate : V →ₗ[ℂ] V)
    (land : S →ₗ[ℂ] V) (delta : ℂ)
    (htarget : ∀ y, targetRotate (targetRotate y) = delta • y)
    (x : S) :
    land x ∉ cyclicParacyclicMinimalDefectBoundary sourceRotate targetRotate land ↔
      ∃ boundary : Submodule ℂ V,
        (∀ y ∈ boundary, targetRotate y ∈ boundary) ∧
        (∀ z, cyclicParacyclicEquivarianceDefect
          sourceRotate targetRotate land z ∈ boundary) ∧
        land x ∉ boundary := by
  constructor
  · intro hnot
    exact ⟨cyclicParacyclicMinimalDefectBoundary sourceRotate targetRotate land,
      cyclicParacyclicMinimalDefectBoundary_target_stable
        sourceRotate targetRotate land delta htarget,
      cyclicParacyclicEquivarianceDefect_mem_minimalBoundary
        sourceRotate targetRotate land, hnot⟩
  · rintro ⟨boundary, hstable, hdefect, hnot⟩ hmem
    exact hnot
      (cyclicParacyclicMinimalDefectBoundary_le sourceRotate targetRotate land
        boundary hstable hdefect hmem)

/-- Away from unit monodromy, every landed vector is already a boundary in
the canonical maximal quotient. -/
theorem land_mem_cyclicParacyclicMinimalDefectBoundary_of_monodromy_ne_one
    (sourceRotate : S →ₗ[ℂ] S)
    (targetRotate : V →ₗ[ℂ] V)
    (land : S →ₗ[ℂ] V) (delta : ℂ)
    (hsource : ∀ x, sourceRotate (sourceRotate x) = x)
    (htarget : ∀ y, targetRotate (targetRotate y) = delta • y)
    (hdelta : delta ≠ 1) (x : S) :
    land x ∈ cyclicParacyclicMinimalDefectBoundary sourceRotate targetRotate land := by
  by_contra hnot
  apply hdelta
  exact retainedCyclicClass_forces_monodromy_one
    sourceRotate targetRotate land
    (cyclicParacyclicMinimalDefectBoundary sourceRotate targetRotate land)
    delta hsource htarget
    (cyclicParacyclicMinimalDefectBoundary_target_stable
      sourceRotate targetRotate land delta htarget)
    (cyclicParacyclicEquivarianceDefect_mem_minimalBoundary
      sourceRotate targetRotate land) hnot

/-- If the landing is surjective, its minimal defect boundary is the whole
target away from unit monodromy. -/
theorem cyclicParacyclicMinimalDefectBoundary_eq_top_of_surjective
    (sourceRotate : S →ₗ[ℂ] S)
    (targetRotate : V →ₗ[ℂ] V)
    (land : S →ₗ[ℂ] V) (delta : ℂ)
    (hsource : ∀ x, sourceRotate (sourceRotate x) = x)
    (htarget : ∀ y, targetRotate (targetRotate y) = delta • y)
    (hland : Function.Surjective land)
    (hdelta : delta ≠ 1) :
    cyclicParacyclicMinimalDefectBoundary sourceRotate targetRotate land = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := hland y
  exact land_mem_cyclicParacyclicMinimalDefectBoundary_of_monodromy_ne_one
    sourceRotate targetRotate land delta hsource htarget hdelta x

end GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Degree-one cyclic source rotation on an ordered two-leg packet. -/
def sourceDaggerDegreeOneCyclicRotation : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) where
  toFun z := (z.2, z.1)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

@[simp]
theorem sourceDaggerDegreeOneCyclicRotation_apply (z : ℂ × ℂ) :
    sourceDaggerDegreeOneCyclicRotation z = (z.2, z.1) := rfl

@[simp]
theorem sourceDaggerDegreeOneCyclicRotation_sq (z : ℂ × ℂ) :
    sourceDaggerDegreeOneCyclicRotation
      (sourceDaggerDegreeOneCyclicRotation z) = z := by
  rfl

/-- Two-leg landing scaled by the already constructed first nonzero physical
Möbius--theta jet. -/
def thetaInternalJetLeadingTwoLegLanding
    (rho : XiDivisorSupport) : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) where
  toFun z := thetaInternalJetLeadingSourceCoefficient rho • z
  map_add' x y := by simp [smul_add]
  map_smul' c x := by
    ext <;> simp [smul_eq_mul] <;> ring

@[simp]
theorem thetaInternalJetLeadingTwoLegLanding_apply
    (rho : XiDivisorSupport) (z : ℂ × ℂ) :
    thetaInternalJetLeadingTwoLegLanding rho z =
      thetaInternalJetLeadingSourceCoefficient rho • z := rfl

/-- Physical first-jet scaling is surjective because its coefficient is the
first nonzero Xi jet. -/
theorem thetaInternalJetLeadingTwoLegLanding_surjective
    (rho : XiDivisorSupport) :
    Function.Surjective (thetaInternalJetLeadingTwoLegLanding rho) := by
  intro z
  refine ⟨(thetaInternalJetLeadingSourceCoefficient rho)⁻¹ • z, ?_⟩
  rw [thetaInternalJetLeadingTwoLegLanding_apply, smul_smul,
    mul_inv_cancel₀ (thetaInternalJetLeadingSourceCoefficient_ne_zero rho), one_smul]

/-- Canonical smallest source--dagger boundary for the physical two-leg
landing at one divisor fibre. -/
def thetaInternalJetSourceDaggerMinimalBoundary
    (n : ℕ) (rho : XiDivisorSupport) : Submodule ℂ (ℂ × ℂ) :=
  cyclicParacyclicMinimalDefectBoundary
    sourceDaggerDegreeOneCyclicRotation
    (sourceDaggerNormalizedDegreeOneRotationLinear n (rho : ℂ))
    (thetaInternalJetLeadingTwoLegLanding rho)

/-- Off the critical line, the canonical physical defect boundary is the
whole two-leg target. -/
theorem thetaInternalJetSourceDaggerMinimalBoundary_eq_top_of_re_ne_half
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport)
    (hoffline : (rho : ℂ).re ≠ 1 / 2) :
    thetaInternalJetSourceDaggerMinimalBoundary n rho = ⊤ := by
  apply cyclicParacyclicMinimalDefectBoundary_eq_top_of_surjective
    sourceDaggerDegreeOneCyclicRotation
    (sourceDaggerNormalizedDegreeOneRotationLinear n (rho : ℂ))
    (thetaInternalJetLeadingTwoLegLanding rho)
    (deningerHalfDensityMateGain n (rho : ℂ) : ℂ)
    sourceDaggerDegreeOneCyclicRotation_sq
    (sourceDaggerNormalizedDegreeOneRotationLinear_sq n (rho : ℂ))
    (thetaInternalJetLeadingTwoLegLanding_surjective rho)
  intro hgainC
  apply hoffline
  have hgain : deningerHalfDensityMateGain n (rho : ℂ) = 1 := by
    exact_mod_cast hgainC
  rw [deningerHalfDensityMateGain] at hgain
  have hexp := (Real.exp_eq_one_iff _).mp hgain
  have hlog : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le one_lt_two hn)
  rcases mul_eq_zero.mp hexp with hre | hnlog
  · linarith
  · exact False.elim (ne_of_gt hlog hnlog)

/-- On the critical line, target and source rotations agree, so the physical
defect boundary is zero. -/
theorem thetaInternalJetSourceDaggerMinimalBoundary_eq_bot_of_re_eq_half
    (n : ℕ) (rho : XiDivisorSupport)
    (hcritical : (rho : ℂ).re = 1 / 2) :
    thetaInternalJetSourceDaggerMinimalBoundary n rho = ⊥ := by
  have hgain : deningerHalfDensityMateGain n (rho : ℂ) = 1 := by
    rw [deningerHalfDensityMateGain, hcritical]
    norm_num
  have hrot : sourceDaggerNormalizedDegreeOneRotationLinear n (rho : ℂ) =
      sourceDaggerDegreeOneCyclicRotation := by
    apply LinearMap.ext
    intro z
    ext <;> simp [sourceDaggerNormalizedDegreeOneRotationLinear,
      sourceDaggerNormalizedDegreeOneRotation, hgain]
  rw [thetaInternalJetSourceDaggerMinimalBoundary, hrot]
  have hdefect :
      cyclicParacyclicEquivarianceDefect sourceDaggerDegreeOneCyclicRotation
        sourceDaggerDegreeOneCyclicRotation
        (thetaInternalJetLeadingTwoLegLanding rho) = 0 := by
    apply LinearMap.ext
    intro z
    ext <;> simp [cyclicParacyclicEquivarianceDefect,
      thetaInternalJetLeadingTwoLegLanding, sourceDaggerDegreeOneCyclicRotation]
  rw [cyclicParacyclicMinimalDefectBoundary, hdefect]
  simp

/-- Canonical first ordered source leg. -/
def thetaInternalJetLeadingSourceAtom : ℂ × ℂ := (1, 0)

/-- The canonical source atom remains nonzero under the physical first-jet
landing at every divisor. -/
theorem thetaInternalJetLeadingSourceAtom_landing_ne_zero
    (rho : XiDivisorSupport) :
    thetaInternalJetLeadingTwoLegLanding rho
        thetaInternalJetLeadingSourceAtom ≠ 0 := by
  intro h
  have hfirst := congrArg Prod.fst h
  apply thetaInternalJetLeadingSourceCoefficient_ne_zero rho
  simpa [thetaInternalJetLeadingTwoLegLanding,
    thetaInternalJetLeadingSourceAtom] using hfirst

/-- Exact physical classification: the canonical top-conormal source atom
survives the maximal admissible quotient exactly on the critical line. -/
theorem thetaInternalJetLeadingSourceAtom_not_mem_minimalBoundary_iff
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport) :
    thetaInternalJetLeadingTwoLegLanding rho thetaInternalJetLeadingSourceAtom ∉
        thetaInternalJetSourceDaggerMinimalBoundary n rho ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro hnot
    by_contra hoff
    rw [thetaInternalJetSourceDaggerMinimalBoundary_eq_top_of_re_ne_half hn rho hoff]
      at hnot
    exact hnot Submodule.mem_top
  · intro hcritical
    rw [thetaInternalJetSourceDaggerMinimalBoundary_eq_bot_of_re_eq_half n rho hcritical]
    simpa using thetaInternalJetLeadingSourceAtom_landing_ne_zero rho

/-- The literal maximal source--dagger quotient at one divisor fibre. -/
abbrev ThetaInternalJetSourceDaggerBoundaryQuotient
    (n : ℕ) (rho : XiDivisorSupport) :=
  (ℂ × ℂ) ⧸ thetaInternalJetSourceDaggerMinimalBoundary n rho

/-- Class of the canonical first physical source atom in the maximal
source--dagger quotient. -/
def thetaInternalJetLeadingSourceBoundaryClass
    (n : ℕ) (rho : XiDivisorSupport) :
    ThetaInternalJetSourceDaggerBoundaryQuotient n rho :=
  Submodule.Quotient.mk
    (thetaInternalJetLeadingTwoLegLanding rho thetaInternalJetLeadingSourceAtom)

/-- Quotient-class form of the exact classification. -/
theorem thetaInternalJetLeadingSourceBoundaryClass_ne_zero_iff
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport) :
    thetaInternalJetLeadingSourceBoundaryClass n rho ≠ 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro hne
    apply (thetaInternalJetLeadingSourceAtom_not_mem_minimalBoundary_iff hn rho).1
    intro hmem
    apply hne
    exact (Submodule.Quotient.mk_eq_zero _).2 hmem
  · intro hcritical hzero
    have hmem := (Submodule.Quotient.mk_eq_zero _).1 hzero
    exact (thetaInternalJetLeadingSourceAtom_not_mem_minimalBoundary_iff hn rho).2
      hcritical hmem

/-- The physical source landing retains its exact multiplicity grade: the
first coordinate of the canonical atom is the first nonzero Xi jet. -/
theorem thetaInternalJetLeadingSourceAtom_landing_eq_multiplicityJet
    (rho : XiDivisorSupport) :
    thetaInternalJetLeadingTwoLegLanding rho thetaInternalJetLeadingSourceAtom =
      (iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho), 0) := by
  rw [thetaInternalJetLeadingTwoLegLanding_apply,
    thetaInternalJetLeadingSourceCoefficient_eq]
  simp [thetaInternalJetLeadingSourceAtom]

/-- Global survival of the canonical physical boundary class at one fixed
integer clock. -/
def ThetaInternalJetSourceDaggerBoundaryClassSurvives (n : ℕ) : Prop :=
  ∀ rho : XiDivisorSupport,
    thetaInternalJetLeadingSourceBoundaryClass n rho ≠ 0

/-- Exact frontier: global survival of the constructed maximal physical
boundary class is equivalent to RH.  This theorem classifies the construction;
it does not prove either side. -/
theorem thetaInternalJetSourceDaggerBoundaryClassSurvives_iff_riemannHypothesis
    {n : ℕ} (hn : 2 ≤ n) :
    ThetaInternalJetSourceDaggerBoundaryClassSurvives n ↔ RiemannHypothesis := by
  rw [← xiBoundaryCharacterNeutral_iff_riemannHypothesis]
  unfold ThetaInternalJetSourceDaggerBoundaryClassSurvives
    XiBoundaryCharacterNeutral
  apply forall_congr'
  intro rho
  rw [thetaInternalJetLeadingSourceBoundaryClass_ne_zero_iff hn,
    xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff]

/-! ## Literal cyclic arithmetic source comparison

The comparison below starts with the genuine degree-one cyclic bar of the
rational adelic CCM source.  Its distinguished atom is supported on an
ordinary-prime scaling and its inverse.  The atom has trace exactly one by
the zero-adele fixed-point identity.  No divisor occurs in its definition.

Jet order remains an independent natural-number grade.  The finite physical
Möbius--theta landing is defined for every grade, rung, and spectral
parameter; only a later theorem specializes the grade to divisor
multiplicity.  The cyclic residue kills the literal cyclic comparison defect
but measures the physical paracyclic defect by the monodromy factor minus
one. -/

open Filter
open GaloisForLFunctions.RHTower
open scoped Topology

/-- Genuine degree-one cyclic tensor source of the rational adelic CCM
algebra. -/
abbrev CCMRationalAdelicDegreeOneCyclicSource :=
  CyclicBarTensor ℂ CCMRationalAdelicCyclicSourceAlgebra 1

/-- Literal degree-one cyclic rotation on the rational adelic bar source. -/
def ccmRationalAdelicDegreeOneCyclicRotation :
    CCMRationalAdelicDegreeOneCyclicSource →ₗ[ℂ]
      CCMRationalAdelicDegreeOneCyclicSource :=
  (cyclicBarRotate (R := ℂ)
    (A := CCMRationalAdelicCyclicSourceAlgebra) 1).toLinearMap

/-- Degree-one trace augmentation of the literal arithmetic cyclic source. -/
def ccmRationalAdelicDegreeOneTrace :
    CCMRationalAdelicDegreeOneCyclicSource →ₗ[ℂ] ℂ :=
  cyclicBarTraceAugmentation ccmRationalAdelicEpsilonZero 1

/-- The arithmetic trace is invariant under genuine cyclic rotation. -/
theorem ccmRationalAdelicDegreeOneTrace_rotate
    (x : CCMRationalAdelicDegreeOneCyclicSource) :
    ccmRationalAdelicDegreeOneTrace
        (ccmRationalAdelicDegreeOneCyclicRotation x) =
      ccmRationalAdelicDegreeOneTrace x := by
  have h := cyclicBarTraceAugmentation_comp_rotate
    ccmRationalAdelicEpsilonZero ccmRationalAdelicEpsilonZero_isTrace 1
  exact LinearMap.congr_fun h x

/-- Canonical zero-adele coefficient: Gaussian at the real place and the
integral characteristic function at all finite places. -/
def ccmRationalAdelicPrimeCycleCore :
    CCMRationalAdelicBruhatSimpleTensor :=
  GaloisForLFunctions.gaussianSchwartz ⊗ₜ[ℂ]
    fieldOneFiniteAdeleIntegralBruhatTest

@[simp]
theorem ccmRationalAdelicPrimeCycleCore_zeroEval :
    ccmRationalAdelicBruhatZeroEval ccmRationalAdelicPrimeCycleCore = 1 := by
  simp [ccmRationalAdelicPrimeCycleCore,
    ccmRationalAdelicBruhatZeroEval_tmul,
    GaloisForLFunctions.gaussReal]

/-- Rational adelic scaling supplied by an ordinary prime. -/
def ccmRationalAdelicPrimeScaling
    (p : Nat.Primes) : CCMRationalAdelicScaling :=
  ⟨Units.mk0 (p : ℚ) (by exact_mod_cast p.2.ne_zero)⟩

/-- Forward ordinary-prime crossed-product coefficient. -/
def ccmRationalAdelicPrimeCycleForward
    (p : Nat.Primes) : CCMRationalAdelicAlgebraicCrossedProduct :=
  Finsupp.single (ccmRationalAdelicPrimeScaling p)
    ccmRationalAdelicPrimeCycleCore

/-- Inverse ordinary-prime crossed-product coefficient. -/
def ccmRationalAdelicPrimeCycleBackward
    (p : Nat.Primes) : CCMRationalAdelicAlgebraicCrossedProduct :=
  Finsupp.single (ccmRationalAdelicPrimeScaling p)⁻¹
    ccmRationalAdelicPrimeCycleCore

/-- Literal degree-one arithmetic cycle carried by `p` and `p⁻¹`. -/
def ccmRationalAdelicOrdinaryPrimeCycleAtom
    (p : Nat.Primes) : CCMRationalAdelicDegreeOneCyclicSource :=
  PiTensorProduct.tprod ℂ (fun i : Fin 2 =>
    Fin.cases
      (ccmRationalAdelicPrimeCycleForward p :
        CCMRationalAdelicCyclicSourceAlgebra)
      (fun _ =>
        (ccmRationalAdelicPrimeCycleBackward p :
          CCMRationalAdelicCyclicSourceAlgebra)) i)

/-- **Independent ordinary-prime source identity.**  The literal cycle
`p ⊗ p⁻¹`, with its canonical zero-adele coefficient, has arithmetic cyclic
trace one. -/
theorem ccmRationalAdelicOrdinaryPrimeCycleAtom_trace_eq_one
    (p : Nat.Primes) :
    ccmRationalAdelicDegreeOneTrace
      (ccmRationalAdelicOrdinaryPrimeCycleAtom p) = 1 := by
  change ccmRationalAdelicEpsilonZero
    (cyclicBarDegreeZeroProduct
      (cyclicBarFace (R := ℂ)
        (A := CCMRationalAdelicCyclicSourceAlgebra)
        (0 : Fin 2) (ccmRationalAdelicOrdinaryPrimeCycleAtom p))) = 1
  rw [ccmRationalAdelicOrdinaryPrimeCycleAtom, cyclicBarFace_tprod,
    cyclicBarDegreeZeroProduct_tprod]
  change ccmRationalAdelicEpsilonZero
    ((ccmRationalAdelicPrimeCycleForward p :
        CCMRationalAdelicCyclicSourceAlgebra) *
      (ccmRationalAdelicPrimeCycleBackward p :
        CCMRationalAdelicCyclicSourceAlgebra)) = 1
  rw [ccmRationalAdelicCyclicSource_inr_mul]
  rw [ccmRationalAdelicPrimeCycleForward,
    ccmRationalAdelicPrimeCycleBackward,
    ccmRationalAdelicCrossedProduct_single_mul_single]
  rw [ccmRationalAdelicEpsilonZero_inr,
    ccmRationalAdelicEpsilonZeroNonunital_single]
  simp only [mul_inv_cancel, if_true]
  rw [ccmRationalAdelicBruhatZeroEval_mul,
    ccmRationalAdelicBruhatZeroEval_smul]
  simp

/-- Pre-divisor ordered comparison from the literal cyclic arithmetic source
to the first physical two-leg source coordinate. -/
def ccmRationalAdelicOrderedTwoLegComparison :
    CCMRationalAdelicDegreeOneCyclicSource →ₗ[ℂ] (ℂ × ℂ) where
  toFun x := (ccmRationalAdelicDegreeOneTrace x, 0)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

@[simp]
theorem ccmRationalAdelicOrderedTwoLegComparison_apply
    (x : CCMRationalAdelicDegreeOneCyclicSource) :
    ccmRationalAdelicOrderedTwoLegComparison x =
      (ccmRationalAdelicDegreeOneTrace x, 0) := rfl

/-- Every ordinary-prime cycle maps to the canonical ordered source atom. -/
theorem ccmRationalAdelicOrderedTwoLegComparison_primeCycle
    (p : Nat.Primes) :
    ccmRationalAdelicOrderedTwoLegComparison
        (ccmRationalAdelicOrdinaryPrimeCycleAtom p) =
      thetaInternalJetLeadingSourceAtom := by
  ext <;>
    simp [ccmRationalAdelicOrderedTwoLegComparison,
      thetaInternalJetLeadingSourceAtom,
      ccmRationalAdelicOrdinaryPrimeCycleAtom_trace_eq_one]

/-- Cyclic homology residue on the ordered two-leg target. -/
def ccmRationalAdelicTwoLegCyclicResidue : (ℂ × ℂ) →ₗ[ℂ] ℂ where
  toFun z := z.1 + z.2
  map_add' x y := by simp; ring
  map_smul' c x := by simp [smul_eq_mul]; ring

@[simp]
theorem ccmRationalAdelicTwoLegCyclicResidue_apply (z : ℂ × ℂ) :
    ccmRationalAdelicTwoLegCyclicResidue z = z.1 + z.2 := rfl

/-- Before analytic dagger twisting, the cyclic residue kills the exact
comparison defect. -/
theorem ccmRationalAdelicTwoLegCyclicResidue_cyclicDefect_eq_zero
    (x : CCMRationalAdelicDegreeOneCyclicSource) :
    ccmRationalAdelicTwoLegCyclicResidue
      (sourceDaggerDegreeOneCyclicRotation
          (ccmRationalAdelicOrderedTwoLegComparison x) -
        ccmRationalAdelicOrderedTwoLegComparison
          (ccmRationalAdelicDegreeOneCyclicRotation x)) = 0 := by
  simp [ccmRationalAdelicTwoLegCyclicResidue,
    ccmRationalAdelicOrderedTwoLegComparison,
    sourceDaggerDegreeOneCyclicRotation,
    ccmRationalAdelicDegreeOneTrace_rotate]

/-- Global finite-rung comparison.  It is defined for every jet grade `k`,
physical Möbius rung `m`, and spectral parameter `w`, before a divisor is
chosen. -/
def ccmMobiusThetaFilteredTwoLegLanding
    (k m : ℕ) (w : ℂ) :
    CCMRationalAdelicDegreeOneCyclicSource →ₗ[ℂ] (ℂ × ℂ) where
  toFun x := mobiusThetaInternalJetFourierLaplace k m w •
    ccmRationalAdelicOrderedTwoLegComparison x
  map_add' x y := by
    ext
    · simp [ccmRationalAdelicOrderedTwoLegComparison, mul_add]
    · simp [ccmRationalAdelicOrderedTwoLegComparison]
  map_smul' c x := by
    ext
    · simp [ccmRationalAdelicOrderedTwoLegComparison, smul_eq_mul]
      ring
    · simp [ccmRationalAdelicOrderedTwoLegComparison]

/-- Global completed jet comparison, still indexed by an independent grade
`k`; multiplicity is not part of its construction. -/
def ccmMobiusThetaXiJetTwoLegLanding
    (k : ℕ) (w : ℂ) :
    CCMRationalAdelicDegreeOneCyclicSource →ₗ[ℂ] (ℂ × ℂ) where
  toFun x := iteratedDeriv k XiC w •
    ccmRationalAdelicOrderedTwoLegComparison x
  map_add' x y := by
    ext
    · simp [ccmRationalAdelicOrderedTwoLegComparison, mul_add]
    · simp [ccmRationalAdelicOrderedTwoLegComparison]
  map_smul' c x := by
    ext
    · simp [ccmRationalAdelicOrderedTwoLegComparison, smul_eq_mul]
      ring
    · simp [ccmRationalAdelicOrderedTwoLegComparison]

/-- Physical provenance: every independently graded finite-rung comparison
converges to the corresponding completed Xi-jet comparison at every divisor
point. -/
theorem tendsto_ccmMobiusThetaFilteredTwoLegLanding_primeCycle_at_divisor
    (k K : ℕ) (rho : XiDivisorSupport) (p : Nat.Primes) :
    Tendsto
      (fun N : ℕ =>
        ccmMobiusThetaFilteredTwoLegLanding k (K + N)
          (xiSpectralPointSupport rho)
          (ccmRationalAdelicOrdinaryPrimeCycleAtom p))
      atTop
      (𝓝 (ccmMobiusThetaXiJetTwoLegLanding k
        (xiSpectralPointSupport rho)
        (ccmRationalAdelicOrdinaryPrimeCycleAtom p))) := by
  have h := tendsto_mobiusThetaInternalJetFourierLaplace_cofinal_at_divisor
    k K rho
  simpa [ccmMobiusThetaFilteredTwoLegLanding,
    ccmMobiusThetaXiJetTwoLegLanding,
    ccmRationalAdelicOrderedTwoLegComparison,
    ccmRationalAdelicOrdinaryPrimeCycleAtom_trace_eq_one]
    using h.prodMk_nhds tendsto_const_nhds

/-- After specialization of the still-separate grade to actual
multiplicity, the global comparison is exactly the physical two-leg landing
of (6.8) composed with the literal arithmetic comparison. -/
theorem ccmMobiusThetaXiJetTwoLegLanding_eq_physicalLeadingLanding
    (rho : XiDivisorSupport)
    (x : CCMRationalAdelicDegreeOneCyclicSource) :
    ccmMobiusThetaXiJetTwoLegLanding (xiSupportMultiplicity rho)
        (xiSpectralPointSupport rho) x =
      thetaInternalJetLeadingTwoLegLanding rho
        (ccmRationalAdelicOrderedTwoLegComparison x) := by
  ext <;>
    simp [ccmMobiusThetaXiJetTwoLegLanding,
      thetaInternalJetLeadingTwoLegLanding,
      thetaInternalJetLeadingSourceCoefficient_eq]

/-- Separate filtered-channel law: every grade below divisor multiplicity
has zero arithmetic residue. -/
theorem ccmMobiusThetaXiJetTwoLegResidue_eq_zero_before_supportMultiplicity
    {k : ℕ} (rho : XiDivisorSupport) (p : Nat.Primes)
    (hk : k < xiSupportMultiplicity rho) :
    ccmRationalAdelicTwoLegCyclicResidue
      (ccmMobiusThetaXiJetTwoLegLanding k
        (xiSpectralPointSupport rho)
        (ccmRationalAdelicOrdinaryPrimeCycleAtom p)) = 0 := by
  simp [ccmMobiusThetaXiJetTwoLegLanding,
    ccmRationalAdelicOrderedTwoLegComparison,
    ccmRationalAdelicTwoLegCyclicResidue,
    iteratedDeriv_XiC_eq_zero_before_supportMultiplicity rho hk]

/-- At the first nonzero multiplicity grade, every ordinary-prime cycle is
detected by the source residue. -/
theorem ccmMobiusThetaXiJetTwoLegResidue_ne_zero_at_supportMultiplicity
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    ccmRationalAdelicTwoLegCyclicResidue
      (ccmMobiusThetaXiJetTwoLegLanding (xiSupportMultiplicity rho)
        (xiSpectralPointSupport rho)
        (ccmRationalAdelicOrdinaryPrimeCycleAtom p)) ≠ 0 := by
  simpa [ccmRationalAdelicTwoLegCyclicResidue,
    ccmMobiusThetaXiJetTwoLegLanding,
    ccmRationalAdelicOrderedTwoLegComparison,
    ccmRationalAdelicOrdinaryPrimeCycleAtom_trace_eq_one] using
      (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)

/-- Equivalent physical form: the independent ordinary-prime trace-one
identity sends its source atom to `x₀`, and the residue detects
`Lρ(x₀)`. -/
theorem ccmRationalAdelicTwoLegCyclicResidue_physicalPrimeCycle_ne_zero
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    ccmRationalAdelicTwoLegCyclicResidue
      (thetaInternalJetLeadingTwoLegLanding rho
        (ccmRationalAdelicOrderedTwoLegComparison
          (ccmRationalAdelicOrdinaryPrimeCycleAtom p))) ≠ 0 := by
  rw [ccmRationalAdelicOrderedTwoLegComparison_primeCycle]
  simpa [ccmRationalAdelicTwoLegCyclicResidue,
    thetaInternalJetLeadingTwoLegLanding,
    thetaInternalJetLeadingSourceAtom] using
      thetaInternalJetLeadingSourceCoefficient_ne_zero rho

/-- Exact transgression formula.  Analytic dagger twisting changes the
source-cyclic residue of the comparison defect by `δ-1`; no square or norm
erases its orientation. -/
theorem ccmMobiusThetaTwoLegParacyclicDefect_residue
    (n : ℕ) (rho : XiDivisorSupport)
    (x : CCMRationalAdelicDegreeOneCyclicSource) :
    ccmRationalAdelicTwoLegCyclicResidue
      (cyclicParacyclicEquivarianceDefect
        ccmRationalAdelicDegreeOneCyclicRotation
        (sourceDaggerNormalizedDegreeOneRotationLinear n (rho : ℂ))
        (ccmMobiusThetaXiJetTwoLegLanding (xiSupportMultiplicity rho)
          (xiSpectralPointSupport rho)) x) =
      ((deningerHalfDensityMateGain n (rho : ℂ) : ℂ) - 1) *
        thetaInternalJetLeadingSourceCoefficient rho *
          ccmRationalAdelicDegreeOneTrace x := by
  rw [thetaInternalJetLeadingSourceCoefficient_eq]
  simp [cyclicParacyclicEquivarianceDefect,
    sourceDaggerNormalizedDegreeOneRotationLinear,
    sourceDaggerNormalizedDegreeOneRotation,
    ccmMobiusThetaXiJetTwoLegLanding,
    ccmRationalAdelicOrderedTwoLegComparison,
    ccmRationalAdelicTwoLegCyclicResidue,
    ccmRationalAdelicDegreeOneTrace_rotate, smul_eq_mul]
  ring

/-- The source-defined residue family is constant in the divisor parameter;
the parameter only records the target stalk at which it is read. -/
def ccmMobiusThetaSourceResidue (_rho : XiDivisorSupport) :
    (ℂ × ℂ) →ₗ[ℂ] ℂ :=
  ccmRationalAdelicTwoLegCyclicResidue

/-- Meaning of annihilating the already constructed physical minimal defect
boundary. -/
def CCMMobiusThetaSourceResidueAnnihilatesMinimalBoundary
    (n : ℕ) (rho : XiDivisorSupport) : Prop :=
  ∀ y ∈ thetaInternalJetSourceDaggerMinimalBoundary n rho,
    ccmMobiusThetaSourceResidue rho y = 0

/-- Exact pointwise obstruction: the constructed source residue annihilates
the physical minimal boundary exactly on the critical line. -/
theorem ccmMobiusThetaSourceResidueAnnihilatesMinimalBoundary_iff
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport) :
    CCMMobiusThetaSourceResidueAnnihilatesMinimalBoundary n rho ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro hann
    by_contra hoff
    have htop :=
      thetaInternalJetSourceDaggerMinimalBoundary_eq_top_of_re_ne_half
        hn rho hoff
    have hzero := hann (1, 0) (by rw [htop]; exact Submodule.mem_top)
    simp [ccmMobiusThetaSourceResidue,
      ccmRationalAdelicTwoLegCyclicResidue] at hzero
  · intro hcritical y hy
    have hbot :=
      thetaInternalJetSourceDaggerMinimalBoundary_eq_bot_of_re_eq_half
        n rho hcritical
    rw [hbot] at hy
    have hyzero : y = 0 := by simpa using hy
    subst y
    simp [ccmMobiusThetaSourceResidue]

/-- Universal obstruction independent of the chosen residue: annihilating
the canonical physical boundary while detecting the landed ordered atom
forces the critical line. -/
theorem re_eq_half_of_residue_annihilates_minimalBoundary_and_detects
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport)
    (residue : (ℂ × ℂ) →ₗ[ℂ] ℂ)
    (hann : ∀ y ∈ thetaInternalJetSourceDaggerMinimalBoundary n rho,
      residue y = 0)
    (hdetect : residue
      (thetaInternalJetLeadingTwoLegLanding rho
        thetaInternalJetLeadingSourceAtom) ≠ 0) :
    (rho : ℂ).re = 1 / 2 := by
  by_contra hoff
  have htop :=
    thetaInternalJetSourceDaggerMinimalBoundary_eq_top_of_re_ne_half
      hn rho hoff
  apply hdetect
  exact hann _ (by rw [htop]; exact Submodule.mem_top)

/-- Global annihilation by the literal source residue. -/
def CCMMobiusThetaSourceResidueAnnihilatesEveryMinimalBoundary
    (n : ℕ) : Prop :=
  ∀ rho : XiDivisorSupport,
    CCMMobiusThetaSourceResidueAnnihilatesMinimalBoundary n rho

/-- **Exact closure of the requested construction.**  Physical provenance,
ordinary-prime detection, and the full multiplicity filtration are
unconditional above.  The remaining demand that the source residue
annihilate every physical minimal boundary is equivalent to RH. -/
theorem ccmMobiusThetaSourceResidueAnnihilatesEveryMinimalBoundary_iff_riemannHypothesis
    {n : ℕ} (hn : 2 ≤ n) :
    CCMMobiusThetaSourceResidueAnnihilatesEveryMinimalBoundary n ↔
      RiemannHypothesis := by
  rw [← thetaInternalJetSourceDaggerBoundaryClassSurvives_iff_riemannHypothesis hn]
  unfold CCMMobiusThetaSourceResidueAnnihilatesEveryMinimalBoundary
    ThetaInternalJetSourceDaggerBoundaryClassSurvives
  apply forall_congr'
  intro rho
  rw [ccmMobiusThetaSourceResidueAnnihilatesMinimalBoundary_iff hn,
    thetaInternalJetLeadingSourceBoundaryClass_ne_zero_iff hn]

end

end RHTower
