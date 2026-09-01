import GaloisForLFunctions.HTGeometry.ComplexGramPlucker
import GaloisForLFunctions.HTGeometry.DeterminantLine
import GaloisForLFunctions.HTGeometry.DirectionalKaehlerWedge
import GaloisForLFunctions.HTGeometry.ExteriorPowerDirectLimit
import GaloisForLFunctions.HTGeometry.TopExteriorPowerDeterminant

/-!
# Range-relative determinant-line formation

An injective finite-rank formation need not land in a one-dimensional ambient exterior power.
Nevertheless, its actual range has a canonical one-dimensional top exterior carrier. This module
constructs that carrier, proves exact factorization through it, and identifies its ambient image
with the Pluecker line of any independent frame.
-/

namespace GaloisForLFunctions.HTGeometry

open Module Set

noncomputable section

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Degree-`n` exterior carrier of the actual range of a formation map. It becomes the
range-relative determinant line when the injective source has dimension `n`. -/
abbrev rangeDeterminantLine (n : ℕ) (f : V →ₗ[K] W) : Type _ :=
  ⋀[K]^n (LinearMap.range f)

/-- Exterior formation from the source to the actual range. -/
def sourceExteriorToRange (n : ℕ) (f : V →ₗ[K] W) :
    ⋀[K]^n V →ₗ[K] rangeDeterminantLine n f :=
  exteriorPower.map n f.rangeRestrict

/-- Inclusion of the range-relative exterior carrier into the ambient exterior power. -/
def rangeDeterminantToAmbient (n : ℕ) (f : V →ₗ[K] W) :
    rangeDeterminantLine n f →ₗ[K] ⋀[K]^n W :=
  exteriorPower.map n (LinearMap.range f).subtype

/-- An injective `n`-dimensional formation has a one-dimensional range-relative determinant
carrier. -/
theorem finrank_rangeDeterminantLine_of_injective [FiniteDimensional K V]
    (n : ℕ) (f : V →ₗ[K] W) (hf : Function.Injective f)
    (hdim : finrank K V = n) :
    finrank K (rangeDeterminantLine n f) = 1 := by
  rw [exteriorPower.finrank_eq, LinearMap.finrank_range_of_inj hf, hdim, Nat.choose_self]

/-- The range-relative exterior carrier embeds faithfully in the ambient exterior power. -/
theorem rangeDeterminantToAmbient_injective (n : ℕ) (f : V →ₗ[K] W) :
    Function.Injective (rangeDeterminantToAmbient n f) :=
  exteriorPower_map_injective n (LinearMap.range f).subtype_injective

/-- Source-to-range exterior formation is injective when formation is injective. -/
theorem sourceExteriorToRange_injective (n : ℕ) (f : V →ₗ[K] W)
    (hf : Function.Injective f) :
    Function.Injective (sourceExteriorToRange n f) := by
  apply exteriorPower_map_injective
  intro x y hxy
  apply hf
  exact congrArg Subtype.val hxy

/-- Source determinant line and range-relative determinant line are canonically equivalent for an
injective `n`-dimensional formation. -/
noncomputable def sourceDeterminantRangeEquiv [FiniteDimensional K V]
    (n : ℕ) (f : V →ₗ[K] W) (hf : Function.Injective f)
    (hdim : finrank K V = n) :
    ⋀[K]^n V ≃ₗ[K] rangeDeterminantLine n f := by
  let g := sourceExteriorToRange n f
  apply g.linearEquivOfInjective (sourceExteriorToRange_injective n f hf)
  rw [exteriorPower.finrank_eq, hdim, Nat.choose_self,
    finrank_rangeDeterminantLine_of_injective n f hf hdim]

@[simp] theorem sourceDeterminantRangeEquiv_apply [FiniteDimensional K V]
    (n : ℕ) (f : V →ₗ[K] W) (hf : Function.Injective f)
    (hdim : finrank K V = n) (x : ⋀[K]^n V) :
    sourceDeterminantRangeEquiv n f hf hdim x = sourceExteriorToRange n f x := rfl

/-- Exact factorization of exterior formation through the exterior carrier of the actual range. -/
theorem exteriorPower_formation_factorization (n : ℕ) (f : V →ₗ[K] W) :
    exteriorPower.map n f =
      (rangeDeterminantToAmbient n f).comp (sourceExteriorToRange n f) := by
  rw [rangeDeterminantToAmbient, sourceExteriorToRange, ← exteriorPower.map_comp]
  congr

/-- Changing source gauge scales top exterior formation by the determinant character. -/
theorem exteriorPower_sourceGauge_covariance
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : Basis ι K V) (f : V →ₗ[K] W) (a : V →ₗ[K] V) :
    exteriorPower.map (Fintype.card ι) (f.comp a) =
      LinearMap.det a • exteriorPower.map (Fintype.card ι) f := by
  rw [exteriorPower.map_comp, exteriorPower_map_card_eq_det_smul b a]
  apply LinearMap.ext
  intro x
  simp

section Frame

variable {d : ℕ}

/-- Synthesis map of a finite frame. -/
def frameSynthesis (v : Fin d → W) : (Fin d → K) →ₗ[K] W :=
  Fintype.linearCombination K v

/-- Standard coordinate frame in `K^d`. -/
def standardCoordinateFrame (i : Fin d) : Fin d → K := Pi.single i 1

theorem frameSynthesis_standardCoordinateFrame (v : Fin d → W) (i : Fin d) :
    frameSynthesis (K := K) v (standardCoordinateFrame (K := K) i) = v i := by
  classical
  simp [frameSynthesis, standardCoordinateFrame, Fintype.linearCombination_apply]

/-- Canonical generator in the range determinant carrier of a finite frame. -/
def rangePluckerGenerator (v : Fin d → W) :
    rangeDeterminantLine d (frameSynthesis (K := K) v) :=
  exteriorPower.ιMulti K d
    (fun i => (frameSynthesis (K := K) v).rangeRestrict
      (standardCoordinateFrame (K := K) i))

/-- Canonical range generator reconstructs the ambient Pluecker vector exactly. -/
theorem rangeDeterminantToAmbient_rangePluckerGenerator (v : Fin d → W) :
    rangeDeterminantToAmbient d (frameSynthesis (K := K) v)
        (rangePluckerGenerator (K := K) v) =
      exteriorPower.ιMulti K d v := by
  rw [rangeDeterminantToAmbient, rangePluckerGenerator, exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  exact frameSynthesis_standardCoordinateFrame v i

/-- Canonical range generator is nonzero for a linearly independent frame. -/
theorem rangePluckerGenerator_ne_zero (v : Fin d → W) (hv : LinearIndependent K v) :
    rangePluckerGenerator (K := K) v ≠ 0 := by
  intro hzero
  have hmap := congrArg
    (rangeDeterminantToAmbient d (frameSynthesis (K := K) v)) hzero
  rw [rangeDeterminantToAmbient_rangePluckerGenerator, map_zero] at hmap
  exact (exteriorPower_ιMulti_ne_zero_of_linearIndependent v hv) hmap

/-- A frame is linearly independent exactly in the direction needed for its synthesis map to be
injective. -/
theorem frameSynthesis_injective (v : Fin d → W) (hv : LinearIndependent K v) :
    Function.Injective (frameSynthesis (K := K) v) := by
  intro c e hce
  apply funext
  intro i
  have hzero : ∑ j, (c - e) j • v j = 0 := by
    have hcomb : ∑ j, c j • v j = ∑ j, e j • v j := by
      simpa [frameSynthesis, Fintype.linearCombination_apply] using hce
    simp [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hcomb]
  have hi := Fintype.linearIndependent_iff.1 hv (c - e) hzero i
  exact sub_eq_zero.mp hi

/-- Every vector in the range determinant carrier is a scalar multiple of its canonical generator
for a linearly independent frame. -/
theorem exists_smul_rangePluckerGenerator (v : Fin d → W) (hv : LinearIndependent K v)
    (x : rangeDeterminantLine d (frameSynthesis (K := K) v)) :
    ∃ c : K, c • rangePluckerGenerator (K := K) v = x := by
  have hdim : finrank K (Fin d → K) = d := by simp
  exact (finrank_eq_one_iff_of_nonzero' (rangePluckerGenerator (K := K) v)
    (rangePluckerGenerator_ne_zero (K := K) v hv)).mp
      (finrank_rangeDeterminantLine_of_injective d (frameSynthesis (K := K) v)
        (frameSynthesis_injective v hv) hdim) x

/-- Included range determinant carrier is exactly the Pluecker line in the ambient exterior
space. -/
theorem range_rangeDeterminantToAmbient_eq_span_plucker (v : Fin d → W)
    (hv : LinearIndependent K v) :
    LinearMap.range (rangeDeterminantToAmbient d (frameSynthesis (K := K) v)) =
      K ∙ exteriorPower.ιMulti K d v := by
  have htop : K ∙ rangePluckerGenerator (K := K) v = ⊤ :=
    (finrank_eq_one_iff_of_nonzero (rangePluckerGenerator (K := K) v)
      (rangePluckerGenerator_ne_zero (K := K) v hv)).mp (by
        have hdim : finrank K (Fin d → K) = d := by simp
        exact finrank_rangeDeterminantLine_of_injective d (frameSynthesis (K := K) v)
          (frameSynthesis_injective v hv) hdim)
  rw [LinearMap.range_eq_map, ← htop, Submodule.map_span]
  simp [rangeDeterminantToAmbient_rangePluckerGenerator]

section ComplexCoordinate

variable {κ : Type*}

/-- In complex coordinates the included canonical range generator is exactly the corpus Pluecker
vector. -/
theorem complex_rangeGenerator_eq_hermFeatureWedge (v : Fin d → κ → ℂ) :
    rangeDeterminantToAmbient d (frameSynthesis (K := ℂ) v)
        (rangePluckerGenerator (K := ℂ) v) = hermFeatureWedge v :=
  rangeDeterminantToAmbient_rangePluckerGenerator v

end ComplexCoordinate

end Frame

end

end GaloisForLFunctions.HTGeometry
