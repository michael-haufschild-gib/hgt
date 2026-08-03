import GaloisForLFunctions.HTGeometry.CyclicParacyclicBoundaryDefectLaw
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

end

end RHTower
