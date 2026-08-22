/-
# Every algebraic matroid over `ℂ` is a Gaussian linear matroid

The algebraic matroid of a finite family in a field extension of `ℂ` is realized by a finite
complex vector configuration: its Kähler differentials give a coordinate representation over the
extension, and the Nullstellensatz descends that representation to `ℂ` without changing any
independence.

Consequently the matroid is also the algebraic matroid of the corresponding homogeneous linear
forms, and the deterministic linear relations of the standard complex Gaussian observables built
from the configuration are exactly the linear relations of the configuration.  An undecorated
algebraic matroid therefore records nothing that a family of Gaussian linear observables does not
already record.
-/
import GaloisForLFunctions.HTGeometry.ComplexCoordinateDescent
import GaloisForLFunctions.HTGeometry.ComplexGaussianObservables
import GaloisForLFunctions.HTGeometry.DifferentialOperatorMatroid

open MeasureTheory
open scoped Classical

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The algebraic matroid of a family in a field extension. -/
def algebraicFamilyMatroid (K : Type*) {L ι : Type*} [CommRing K] [CommRing L] [Algebra K L]
    [FaithfulSMul K L] [NoZeroDivisors L] (x : ι → L) : Matroid ι :=
  (AlgebraicIndependent.matroid K L).comap x

@[simp]
theorem algebraicFamilyMatroid_ground (K : Type*) {L ι : Type*} [CommRing K] [CommRing L]
    [Algebra K L] [FaithfulSMul K L] [NoZeroDivisors L] (x : ι → L) :
    (algebraicFamilyMatroid K x).E = Set.univ := by
  simp [algebraicFamilyMatroid]

theorem algebraicFamilyMatroid_indep_iff (K : Type*) {L ι : Type*} [CommRing K] [Nontrivial K]
    [CommRing L] [Algebra K L] [FaithfulSMul K L] [NoZeroDivisors L] (x : ι → L) (I : Set ι) :
    (algebraicFamilyMatroid K x).Indep I ↔ AlgebraicIndependent K (fun i : I => x (i : ι)) := by
  rw [algebraicFamilyMatroid, Matroid.comap_indep_iff, AlgebraicIndependent.matroid_indep_iff]
  constructor
  · rintro ⟨himage, hinj⟩
    have himage' : AlgebraicIndependent K (fun p : x '' I => (p : L)) := by
      simpa [AlgebraicIndepOn] using himage
    exact (algebraicIndependent_image (R := K) hinj).mpr himage'
  · intro hfamily
    have hinj : Set.InjOn x I := by
      intro a ha b hb hab
      exact congrArg Subtype.val
        (hfamily.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)
    have himage : AlgebraicIndependent K (fun p : x '' I => (p : L)) :=
      (algebraicIndependent_image (R := K) hinj).mp hfamily
    exact ⟨by simpa [AlgebraicIndepOn] using himage, hinj⟩

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem linearIndependent_toFinset_iff {R M : Type*} [DivisionRing R] [AddCommGroup M]
    [Module R M] (f : ι → M) (I : Set ι) :
    LinearIndependent R (fun i : {a // a ∈ I.toFinset} => f (i : ι)) ↔
      LinearIndependent R (fun i : I => f (i : ι)) := by
  classical
  let e : {a // a ∈ I.toFinset} ≃ I := Equiv.subtypeEquivRight (fun a => Set.mem_toFinset)
  constructor
  · intro h
    have h' := h.comp e.symm e.symm.injective
    exact h'
  · intro h
    have h' := h.comp e e.injective
    exact h'

omit [DecidableEq ι] in
theorem algebraicIndependent_toFinset_iff {K L : Type*} [CommRing K] [CommRing L] [Algebra K L]
    (f : ι → L) (I : Set ι) :
    AlgebraicIndependent K (fun i : {a // a ∈ I.toFinset} => f (i : ι)) ↔
      AlgebraicIndependent K (fun i : I => f (i : ι)) := by
  classical
  let e : {a // a ∈ I.toFinset} ≃ I := Equiv.subtypeEquivRight (fun a => Set.mem_toFinset)
  constructor
  · intro h
    exact h.comp e.symm e.symm.injective
  · intro h
    exact h.comp e e.injective

/-- **Complex model of an algebraic matroid.**  A finite family in a field extension of `ℂ` has a
finite complex coordinate model whose linear independence pattern on every subfamily is exactly
algebraic independence over `ℂ`. -/
theorem exists_complexModel {L : Type*} [Field L] [Algebra ℂ L] (x : ι → L) :
    ∃ (r : ℕ) (w : ι → Fin r → ℂ), ∀ I : Set ι,
      (LinearIndependent ℂ (fun i : I => w (i : ι)) ↔
        AlgebraicIndependent ℂ (fun i : I => x (i : ι))) := by
  obtain ⟨r, v, hv⟩ := exists_kaehlerCoords x
  obtain ⟨w, hw⟩ := exists_complexCoords v
  refine ⟨r, w, fun I => ?_⟩
  rw [← linearIndependent_toFinset_iff, ← algebraicIndependent_toFinset_iff]
  exact (hw I.toFinset).trans (hv I.toFinset)

/-- The Gaussian linear observable attached to a coefficient row. -/
def gaussianObservable {r : ℕ} (w : ι → Fin r → ℂ) (i : ι) (g : Fin r → ℂ) : ℂ :=
  ∑ j : Fin r, w i j * g j

/-- **Gaussian mimicry of an algebraic matroid.**  Every algebraic matroid of a finite family in a
field extension of `ℂ` is the linear matroid of a finite complex vector configuration, hence the
algebraic matroid of the corresponding homogeneous linear forms, and the deterministic linear
relations of the associated standard complex Gaussian observables are exactly the linear relations
of that configuration. -/
theorem exists_gaussianModel {L : Type*} [Field L] [Algebra ℂ L] (x : ι → L) :
    ∃ (r : ℕ) (w : ι → Fin r → ℂ),
      algebraicFamilyMatroid ℂ x = linearFamilyMatroid w ∧
      linearFamilyMatroid w
        = algebraicFamilyMatroid ℂ (fun i => linearFormPolynomial (w i)) ∧
      ∀ (a : ι → ℂ) (J : Finset ι),
        ((∀ᵐ g ∂(complexGaussian (Fin r)), ∑ i ∈ J, a i * gaussianObservable w i g = 0) ↔
          ∑ i ∈ J, a i • w i = 0) := by
  obtain ⟨r, w, hw⟩ := exists_complexModel x
  refine ⟨r, w, ?_, rfl, ?_⟩
  · refine Matroid.ext_indep (by simp) ?_
    intro I _
    rw [algebraicFamilyMatroid_indep_iff, linearFamilyMatroid_indep_iff]
    exact (hw I).symm
  · intro a J
    exact ae_gaussian_linearCombination_eq_zero_iff w a J

end

end GaloisForLFunctions.HTGeometry
