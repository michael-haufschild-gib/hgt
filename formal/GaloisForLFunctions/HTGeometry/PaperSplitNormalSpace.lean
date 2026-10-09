import GaloisForLFunctions.HTGeometry.PaperSplitIdealContraction
import GaloisForLFunctions.HTGeometry.PaperHomogeneousGeneratorIdeal
import GaloisForLFunctions.HTGeometry.PaperNativeReesHomogeneousInitial

/-!
# Actual normal coordinates from a split coefficient ring

The source Rees coefficient kernel applies to generator families of unequal
ambient degrees. A coefficient-ring retraction pays every ideal-power
contraction, leaving polynomially independent actual initial classes.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable (K R ι : Type*) [CommRing K] [CommRing R] [Algebra K R]

/-- Generator data with a proved splitting of its polynomial coefficient ring. -/
structure PaperSplitNormalData where
  generator : ι → R
  retraction : PaperIdealRetraction (aeval (R := K) generator).toRingHom

variable {K R ι}

/-- The actual ideal of the specified generators. -/
def PaperSplitNormalData.ideal (D : PaperSplitNormalData K R ι) : Ideal R :=
  Ideal.span (Set.range D.generator)

/-- The native generator ideal is the extension of the coefficient-variable ideal. -/
theorem PaperSplitNormalData.ideal_eq_map (D : PaperSplitNormalData K R ι) :
    D.ideal = (paperHomogeneousGeneratorIdeal (X : ι → MvPolynomial ι K)).map
      (aeval (R := K) D.generator).toRingHom := by
  rw [PaperSplitNormalData.ideal, paperHomogeneousGeneratorIdeal, Ideal.map_span]
  apply congrArg Ideal.span
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨X i, ⟨i, rfl⟩, aeval_X (R := K) D.generator i⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (aeval_X (R := K) D.generator i).symm⟩

/-- Each generator comes with its actual ideal membership. -/
def PaperSplitNormalData.idealElements (D : PaperSplitNormalData K R ι) : ι → D.ideal :=
  fun i => ⟨D.generator i, Ideal.subset_span ⟨i, rfl⟩⟩

/-- Substitute actual degree-one initial classes into the coefficient polynomial ring. -/
def PaperSplitNormalData.polynomialMap (D : PaperSplitNormalData K R ι) :
    MvPolynomial ι K →+* PaperIdealAssociatedGraded D.ideal :=
  paperNativeReesMvPolynomialSpecialization D.ideal D.idealElements

/-- A homogeneous coefficient polynomial can gain ideal order only by being zero. -/
theorem PaperSplitNormalData.homogeneous_mem_succ_iff
    (D : PaperSplitNormalData K R ι) (p : MvPolynomial ι K) (n : ℕ) (hp : p.IsHomogeneous n) :
    aeval D.generator p ∈ D.ideal ^ (n + 1) ↔ p = 0 := by
  rw [D.ideal_eq_map]
  apply (D.retraction.mem_map_pow_iff
    (paperHomogeneousGeneratorIdeal (X : ι → MvPolynomial ι K)) (n + 1) p).trans
  have h := (paperHomogeneousGeneratorNormalPresentation (X : ι → MvPolynomial ι K)
    1 Nat.zero_lt_one (isHomogeneous_X K)).homogeneous_mem_succ_iff p n hp
  change aeval (X : ι → MvPolynomial ι K) p ∈
    paperHomogeneousGeneratorIdeal X ^ (n + 1) ↔ aeval (X : ι → MvPolynomial ι K) p = 0 at h
  simpa only [aeval_X_left_apply] using h

/-- The source coefficient-kernel theorem gives an exact vanishing criterion. -/
theorem PaperSplitNormalData.polynomialMap_eq_zero_iff
    (D : PaperSplitNormalData K R ι) (p : MvPolynomial ι K) :
    D.polynomialMap p = 0 ↔ p = 0 := by
  constructor
  · intro h
    have hc := (paperNativeReesMvPolynomialSpecialization_eq_zero_iff D.ideal D.idealElements p).mp h
    apply MvPolynomial.ext
    intro d
    have hz := (D.homogeneous_mem_succ_iff _ d.degree
      (homogeneousComponent_isHomogeneous d.degree p)).mp (hc d.degree)
    have he := congrArg (coeff d) hz
    simpa only [coeff_homogeneousComponent, ↓reduceIte, coeff_zero] using he
  · intro h
    rw [h, map_zero]

/-- The original polynomial coefficient ring embeds into the actual normal ring. -/
theorem PaperSplitNormalData.polynomialMap_injective (D : PaperSplitNormalData K R ι) :
    Function.Injective D.polynomialMap := by
  intro p q h
  apply sub_eq_zero.mp
  apply (D.polynomialMap_eq_zero_iff _).mp
  rw [map_sub, h, sub_self]

/-- The formal variables are the actual source initial classes of the native generators. -/
theorem PaperSplitNormalData.polynomialMap_X (D : PaperSplitNormalData K R ι) (i : ι) :
    D.polynomialMap (X i) = paperNativeReesSpecialization D.ideal
      (ReesGrading.mono D.ideal 1 (D.generator i)
        (by rw [pow_one]; exact Ideal.subset_span ⟨i, rfl⟩)) :=
  paperNativeReesMvPolynomialSpecialization_X D.ideal D.idealElements i

/-- Homogeneous coefficient expressions have the indicated actual ideal membership. -/
theorem PaperSplitNormalData.homogeneous_evaluation_mem
    (D : PaperSplitNormalData K R ι) (p : MvPolynomial ι K) (n : ℕ) (hp : p.IsHomogeneous n) :
    aeval D.generator p ∈ D.ideal ^ n :=
  paperNativeReesMvPolynomial_homogeneous_mem D.ideal D.idealElements p n hp

/-- Homogeneous coefficient expressions map to their actual initial classes. -/
theorem PaperSplitNormalData.polynomialMap_homogeneous
    (D : PaperSplitNormalData K R ι) (p : MvPolynomial ι K) (n : ℕ) (hp : p.IsHomogeneous n) :
    D.polynomialMap p = paperNativeReesSpecialization D.ideal
      (ReesGrading.mono D.ideal n (aeval D.generator p)
        (D.homogeneous_evaluation_mem p n hp)) :=
  paperNativeReesMvPolynomialSpecialization_homogeneous D.ideal D.idealElements p n hp

end

end GaloisForLFunctions.HTGeometry
