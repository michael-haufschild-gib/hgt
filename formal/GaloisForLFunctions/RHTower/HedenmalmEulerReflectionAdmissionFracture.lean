import GaloisForLFunctions.RHTower.EulerPrimitiveCommonTestPolarizedReflectionRigidity
import GaloisForLFunctions.RHTower.XiHedenmalmThetaBorelHilbert

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Reflection-odd Hedenmalm source vector before passage to its `L²` class. -/
def hedenmalmBorelReflectionOddFun (a x t : ℝ) : ℂ :=
  hedenmalmBorelHolonomyFun ((a : ℂ) * I) x t -
    hedenmalmBorelHolonomyFun (-((a : ℂ) * I)) x t

/-- Every nonzero reflected Hedenmalm pair in the centered open half-strip remains in the
ordinary Borel source Hilbert space. -/
theorem memLp_hedenmalmBorelReflectionOddFun
    {a : ℝ} (ha : |a| < 1 / 2) (x : ℝ) :
    MemLp (hedenmalmBorelReflectionOddFun a x) 2
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hplus : |(((a : ℂ) * I).im)| < 1 / 2 := by
    simpa using ha
  have hminus : |((-((a : ℂ) * I)).im)| < 1 / 2 := by
    simpa using ha
  change MemLp
    (hedenmalmBorelHolonomyFun ((a : ℂ) * I) x -
      hedenmalmBorelHolonomyFun (-((a : ℂ) * I)) x) 2
      (volume.restrict (Ioi (0 : ℝ)))
  exact
    (memLp_hedenmalmBorelHolonomyFun hplus x).sub
      (memLp_hedenmalmBorelHolonomyFun hminus x)

/-- Finite-energy displacement spectrum of the Hedenmalm Borel reflection family. -/
def hedenmalmBorelReflectionAdmissionSpectrum (x : ℝ) : Set ℝ :=
  {a | MemLp (hedenmalmBorelReflectionOddFun a x) 2
    (volume.restrict (Ioi (0 : ℝ)))}

/-- Finite-energy displacement spectrum of the polarized Euler/Hardy reflection family. -/
def eulerPrimitiveReflectionAdmissionSpectrum : Set ℝ :=
  {a | IntegrableOn
    (fun t : ℝ =>
      eulerPrimitiveBoundaryTailWeight t *
        Complex.normSq
          ((eulerPrimitiveBoundaryPolarizedReflectionOddProfile a).2 t))
    (Ioi 0)}

/-- The Euler/Hardy reflection profile with its actual tail weight absorbed into the vector. -/
def eulerPrimitiveWeightedReflectionOddFun (a t : ℝ) : ℂ :=
  ((Real.sqrt (eulerPrimitiveBoundaryTailWeight t) : ℝ) : ℂ) *
    (eulerPrimitiveBoundaryPolarizedReflectionOddProfile a).2 t

theorem continuous_eulerPrimitiveWeightedReflectionOddFun (a : ℝ) :
    Continuous (eulerPrimitiveWeightedReflectionOddFun a) := by
  unfold eulerPrimitiveWeightedReflectionOddFun
    eulerPrimitiveBoundaryTailWeight
    eulerPrimitiveBoundaryPolarizedReflectionOddProfile
    eulerPrimitiveBoundaryPolarizedTest
  fun_prop

theorem norm_sq_eulerPrimitiveWeightedReflectionOddFun
    (a : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖eulerPrimitiveWeightedReflectionOddFun a t‖ ^ 2 =
      eulerPrimitiveBoundaryTailWeight t *
        Complex.normSq
          ((eulerPrimitiveBoundaryPolarizedReflectionOddProfile a).2 t) := by
  rw [eulerPrimitiveWeightedReflectionOddFun, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (eulerPrimitiveBoundaryTailWeight_pos ht).le,
    Complex.sq_norm]

/-- Weighted Euler reflection is in the ordinary fixed `L²` space exactly at zero displacement. -/
theorem memLp_eulerPrimitiveWeightedReflectionOddFun_iff (a : ℝ) :
    MemLp (eulerPrimitiveWeightedReflectionOddFun a) 2
        (volume.restrict (Ioi (0 : ℝ))) ↔
      a = 0 := by
  rw [memLp_two_iff_integrable_sq_norm
    (continuous_eulerPrimitiveWeightedReflectionOddFun a).aestronglyMeasurable]
  rw [← integrableOn_eulerPrimitiveBoundaryPolarizedReflectionOddProfile_tail_iff a]
  constructor
  · intro h
    refine h.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_sq_eulerPrimitiveWeightedReflectionOddFun a (mem_Ioi.mp ht)
  · intro h
    refine h.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (norm_sq_eulerPrimitiveWeightedReflectionOddFun a (mem_Ioi.mp ht)).symm

/-- The Hedenmalm spectrum contains the whole centered open half-strip. -/
theorem Ioo_subset_hedenmalmBorelReflectionAdmissionSpectrum (x : ℝ) :
    Ioo (-(1 / 2 : ℝ)) (1 / 2) ⊆
      hedenmalmBorelReflectionAdmissionSpectrum x := by
  intro a ha
  exact memLp_hedenmalmBorelReflectionOddFun (abs_lt.mpr ha) x

/-- The polarized Euler/Hardy finite-energy spectrum is exactly zero displacement. -/
theorem eulerPrimitiveReflectionAdmissionSpectrum_eq_singleton :
    eulerPrimitiveReflectionAdmissionSpectrum = {0} := by
  ext a
  exact
    integrableOn_eulerPrimitiveBoundaryPolarizedReflectionOddProfile_tail_iff a

/-- The two independently constructed arithmetic source carriers have different reflection
admission spectra at every Borel basepoint. -/
theorem hedenmalmBorelReflectionAdmissionSpectrum_ne_eulerPrimitive
    (x : ℝ) :
    hedenmalmBorelReflectionAdmissionSpectrum x ≠
      eulerPrimitiveReflectionAdmissionSpectrum := by
  intro heq
  have hH : (1 / 4 : ℝ) ∈ hedenmalmBorelReflectionAdmissionSpectrum x :=
    Ioo_subset_hedenmalmBorelReflectionAdmissionSpectrum x (by norm_num)
  have hE : (1 / 4 : ℝ) ∈ eulerPrimitiveReflectionAdmissionSpectrum := by
    rw [← heq]
    exact hH
  rw [eulerPrimitiveReflectionAdmissionSpectrum_eq_singleton] at hE
  norm_num at hE

/-- A raw-profile transport is finite-energy faithful at one reflection parameter when it
intertwines the actual source profiles and preserves their two admission predicates. -/
def HedenmalmEulerReflectionFiniteEnergyFaithfulAt
    (T : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ)) (x a : ℝ) : Prop :=
  T (hedenmalmBorelReflectionOddFun a x) =
      (eulerPrimitiveBoundaryPolarizedReflectionOddProfile a).2 ∧
    (MemLp (hedenmalmBorelReflectionOddFun a x) 2
        (volume.restrict (Ioi (0 : ℝ))) ↔
      IntegrableOn
        (fun t : ℝ =>
          eulerPrimitiveBoundaryTailWeight t *
            Complex.normSq
              (T (hedenmalmBorelReflectionOddFun a x) t))
        (Ioi 0))

/-- A regular raw-profile transport at one parameter intertwines the actual weighted profiles and
maps the admitted Hedenmalm vector into the fixed target `L²` space. -/
def HedenmalmEulerReflectionL2TransportAt
    (T : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ)) (x a : ℝ) : Prop :=
  T (hedenmalmBorelReflectionOddFun a x) =
      eulerPrimitiveWeightedReflectionOddFun a ∧
    (MemLp (hedenmalmBorelReflectionOddFun a x) 2
        (volume.restrict (Ioi (0 : ℝ))) →
      MemLp (T (hedenmalmBorelReflectionOddFun a x)) 2
        (volume.restrict (Ioi (0 : ℝ))))

/-- No domain-preserving Hilbert transport can intertwine the two source families at a nonzero
centered-strip displacement.  Injectivity, boundedness, and a reverse map are not needed. -/
theorem not_hedenmalmEulerReflectionL2TransportAt
    (x : ℝ) {a : ℝ} (ha : |a| < 1 / 2) (ha0 : a ≠ 0) :
    ¬ ∃ T : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ),
      HedenmalmEulerReflectionL2TransportAt T x a := by
  rintro ⟨T, hintertwine, hregular⟩
  have hH := memLp_hedenmalmBorelReflectionOddFun ha x
  have hE := hregular hH
  rw [hintertwine] at hE
  exact ha0 ((memLp_eulerPrimitiveWeightedReflectionOddFun_iff a).mp hE)

/-- **Hedenmalm--Euler admission fracture.**  At every nonzero centered-strip displacement there
is no finite-energy-faithful linear transport intertwining the Borel and polarized Hardy
reflection families.  Any bridge must change domain or lose source information. -/
theorem not_hedenmalmEulerReflectionFiniteEnergyFaithfulAt
    (x : ℝ) {a : ℝ} (ha : |a| < 1 / 2) (ha0 : a ≠ 0) :
    ¬ ∃ T : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ),
      HedenmalmEulerReflectionFiniteEnergyFaithfulAt T x a := by
  rintro ⟨T, hintertwine, hfaithful⟩
  have hH := memLp_hedenmalmBorelReflectionOddFun ha x
  have hE := hfaithful.mp hH
  rw [hintertwine] at hE
  exact ha0
    ((integrableOn_eulerPrimitiveBoundaryPolarizedReflectionOddProfile_tail_iff a).mp hE)

end

end RHTower
