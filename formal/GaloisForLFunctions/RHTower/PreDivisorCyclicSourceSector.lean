import GaloisForLFunctions.RHTower.MobiusThetaPhysicalParacyclicSourceNullHomology
import GaloisForLFunctions.RHTower.PreDivisorTransverseDualNumberFormalNeighborhood

/-!
# Pre-divisor cyclic source sector

The cyclic source exists before selecting an Xi divisor, whereas the analytic dagger rotation
depends on the spectral parameter.  Their canonical minimal defect quotient therefore defines a
whole-plane source sector.  Off the critical line its boundary is the whole target, so the sector
is zero.  On the line the boundary is zero and the ordered source atom survives.

The physical Xi source-dagger boundary is proved below to be the specialization of this universal
boundary.  Hence divisor multiplicity supplies the nonzero longitudinal payload but does not
create the transverse admissibility locus.
-/

open Complex

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Divisor-independent identity landing of the two cyclic source orientations. -/
def preDivisorCyclicSourceLanding : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) where
  toFun z := z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem preDivisorCyclicSourceLanding_apply (z : ℂ × ℂ) :
    preDivisorCyclicSourceLanding z = z := rfl

/-- Whole-plane obstruction boundary for descent from cyclic source rotation to the
spectral-parameter-dependent paracyclic target rotation. -/
def preDivisorCyclicSourceMinimalBoundary
    (n : ℕ) (s : ℂ) : Submodule ℂ (ℂ × ℂ) :=
  cyclicParacyclicMinimalDefectBoundary
    sourceDaggerDegreeOneCyclicRotation
    (sourceDaggerNormalizedDegreeOneRotationLinear n s)
    preDivisorCyclicSourceLanding

/-- Off the critical line, the universal source-sector boundary consumes the whole target. -/
theorem preDivisorCyclicSourceMinimalBoundary_eq_top_of_re_ne_half
    {n : ℕ} (hn : 2 ≤ n) (s : ℂ) (hoff : s.re ≠ 1 / 2) :
    preDivisorCyclicSourceMinimalBoundary n s = ⊤ := by
  apply cyclicParacyclicMinimalDefectBoundary_eq_top_of_surjective
    sourceDaggerDegreeOneCyclicRotation
    (sourceDaggerNormalizedDegreeOneRotationLinear n s)
    preDivisorCyclicSourceLanding
    (deningerHalfDensityMateGain n s : ℂ)
    sourceDaggerDegreeOneCyclicRotation_sq
    (sourceDaggerNormalizedDegreeOneRotationLinear_sq n s)
    (fun z => ⟨z, rfl⟩)
  intro hgain
  apply hoff
  exact (deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn s).1
    (by exact_mod_cast hgain)

/-- On the critical line, cyclic source and analytic target rotations coincide, so no
source state is declared a descent boundary. -/
theorem preDivisorCyclicSourceMinimalBoundary_eq_bot_of_re_eq_half
    {n : ℕ} (hn : 2 ≤ n) (s : ℂ) (hwall : s.re = 1 / 2) :
    preDivisorCyclicSourceMinimalBoundary n s = ⊥ := by
  have hgain : deningerHalfDensityMateGain n s = 1 :=
    (deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn s).2 hwall
  have hrotate :
      sourceDaggerNormalizedDegreeOneRotationLinear n s =
        sourceDaggerDegreeOneCyclicRotation := by
    apply LinearMap.ext
    intro z
    ext <;>
      simp [sourceDaggerNormalizedDegreeOneRotation,
        sourceDaggerDegreeOneCyclicRotation, hgain]
  rw [preDivisorCyclicSourceMinimalBoundary, hrotate]
  have hdefect :
      cyclicParacyclicEquivarianceDefect
          sourceDaggerDegreeOneCyclicRotation
          sourceDaggerDegreeOneCyclicRotation
          preDivisorCyclicSourceLanding = 0 := by
    apply LinearMap.ext
    intro z
    simp [cyclicParacyclicEquivarianceDefect]
  rw [cyclicParacyclicMinimalDefectBoundary, hdefect]
  simp

/-- Universal ordered source atom, defined before any divisor or multiplicity is selected. -/
def preDivisorCyclicSourceAtom : ℂ × ℂ := (1, 0)

/-- Maximal cyclic source-sector quotient at a whole-plane spectral parameter. -/
abbrev PreDivisorCyclicSourceSector
    (n : ℕ) (s : ℂ) :=
  (ℂ × ℂ) ⧸ preDivisorCyclicSourceMinimalBoundary n s

/-- Universal source atom in the whole-plane cyclic source-sector quotient. -/
def preDivisorCyclicSourceSectorClass
    (n : ℕ) (s : ℂ) : PreDivisorCyclicSourceSector n s :=
  Submodule.Quotient.mk
    (preDivisorCyclicSourceLanding preDivisorCyclicSourceAtom)

/-- Exact support law: the divisor-independent cyclic source state survives precisely on the
critical line.  Off-line monodromy does not merely deform the state; it kills the whole quotient. -/
theorem preDivisorCyclicSourceSectorClass_ne_zero_iff
    {n : ℕ} (hn : 2 ≤ n) (s : ℂ) :
    preDivisorCyclicSourceSectorClass n s ≠ 0 ↔ s.re = 1 / 2 := by
  constructor
  · intro hne
    by_contra hoff
    apply hne
    apply (Submodule.Quotient.mk_eq_zero _).2
    rw [preDivisorCyclicSourceMinimalBoundary_eq_top_of_re_ne_half hn s hoff]
    exact Submodule.mem_top
  · intro hwall hzero
    have hmem := (Submodule.Quotient.mk_eq_zero _).1 hzero
    rw [preDivisorCyclicSourceMinimalBoundary_eq_bot_of_re_eq_half hn s hwall] at hmem
    have hatom : preDivisorCyclicSourceLanding preDivisorCyclicSourceAtom = 0 := by
      simpa using hmem
    have hfirst := congrArg Prod.fst hatom
    norm_num [preDivisorCyclicSourceAtom] at hfirst

/-- Cyclic state survival and disappearance of the transverse ramification class are the same
whole-plane locus. -/
theorem preDivisorCyclicSourceSectorClass_ne_zero_iff_formallyUnramified
    {n : ℕ} (hn : 2 ≤ n) (s : ℂ) :
    preDivisorCyclicSourceSectorClass n s ≠ 0 ↔
      Algebra.FormallyUnramified ℂ (PreDivisorTransverseArcAlgebra s) := by
  rw [preDivisorCyclicSourceSectorClass_ne_zero_iff hn,
    preDivisorTransverseArcAlgebra_formallyUnramified_iff]

/-- The physical Xi source-dagger boundary is not created after divisor selection: it is the
specialization of the universal whole-plane source-sector boundary. -/
theorem thetaInternalJetSourceDaggerMinimalBoundary_eq_preDivisor
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport) :
    thetaInternalJetSourceDaggerMinimalBoundary n rho =
      preDivisorCyclicSourceMinimalBoundary n (rho : ℂ) := by
  by_cases hwall : (rho : ℂ).re = 1 / 2
  · rw [thetaInternalJetSourceDaggerMinimalBoundary_eq_bot_of_re_eq_half n rho hwall,
      preDivisorCyclicSourceMinimalBoundary_eq_bot_of_re_eq_half hn (rho : ℂ) hwall]
  · rw [thetaInternalJetSourceDaggerMinimalBoundary_eq_top_of_re_ne_half hn rho hwall,
      preDivisorCyclicSourceMinimalBoundary_eq_top_of_re_ne_half hn (rho : ℂ) hwall]

end

end RHTower
