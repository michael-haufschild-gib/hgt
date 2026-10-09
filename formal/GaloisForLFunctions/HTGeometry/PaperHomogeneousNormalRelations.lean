import GaloisForLFunctions.HTGeometry.PaperHomogeneousSubstitutionComponents
import GaloisForLFunctions.HTGeometry.PaperNativeReesMvPolynomial
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Exact preservation of polynomial relations in normal coordinates

Apply the paper's coefficient-kernel and nonnegative-weight theorems to
generators of a common positive degree. Their scalar polynomial relations
are exactly the relations among their actual initial classes. Independence
of the generators is not required. Concrete applications pay all data.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- Fully specified homogeneous ideal data, allowing arbitrary relations among generators. -/
structure PaperHomogeneousNormalPresentationData (K σ ι : Type*) [CommRing K]
    (I : Ideal (MvPolynomial σ K)) where
  generator : ι → MvPolynomial σ K
  degree : ℕ
  degree_pos : 0 < degree
  generator_mem : ∀ i, generator i ∈ I
  homogeneous : ∀ i, (generator i).IsHomogeneous degree
  order_bound : I ≤ paperWeightOrderIdeal (fun _ : σ => (1 : ℤ)) (by intro _; exact zero_le_one) degree

variable {K σ ι : Type*} [CommRing K] {I : Ideal (MvPolynomial σ K)}

/-- The specified generators as elements of the actual native ideal. -/
def PaperHomogeneousNormalPresentationData.idealElements
    (D : PaperHomogeneousNormalPresentationData K σ ι I) : ι → I :=
  fun i => ⟨D.generator i, D.generator_mem i⟩

/-- Simultaneous substitution into the actual initial classes of all generators. -/
def PaperHomogeneousNormalPresentationData.polynomialMap
    (D : PaperHomogeneousNormalPresentationData K σ ι I) :
    MvPolynomial ι K →+* PaperIdealAssociatedGraded I :=
  paperNativeReesMvPolynomialSpecialization I D.idealElements

/-- A homogeneous evaluated polynomial gains an ideal order exactly when its value vanishes. -/
theorem PaperHomogeneousNormalPresentationData.homogeneous_mem_succ_iff
    (D : PaperHomogeneousNormalPresentationData K σ ι I)
    (p : MvPolynomial ι K) (n : ℕ) (hp : p.IsHomogeneous n) :
    MvPolynomial.aeval D.generator p ∈ I ^ (n + 1) ↔ MvPolynomial.aeval D.generator p = 0 := by
  constructor
  · intro h
    by_contra he0
    have hh : (MvPolynomial.aeval D.generator p).IsWeightedHomogeneous
        (fun _ => (1 : ℤ)) ((D.degree * n : ℕ) : ℤ) :=
      paperIsWeightedHomogeneous_int (hp.aeval D.generator D.homogeneous)
    have hd : (0 : ℤ) < D.degree := by exact_mod_cast D.degree_pos
    have hlt : ((D.degree * n : ℕ) : ℤ) < ((n + 1 : ℕ) : ℤ) * D.degree := by
      push_cast
      nlinarith
    exact paperWeightOrderIdeal_not_mem_of_homogeneous _ _ hh he0 hlt
      (paperWeightOrderIdeal_pow_le _ _ I _ D.order_bound (n + 1) h)
  · intro h
    rw [h]
    exact (I ^ (n + 1)).zero_mem

/-- The source coefficient kernel preserves exactly all scalar polynomial relations. -/
theorem PaperHomogeneousNormalPresentationData.polynomialMap_eq_zero_iff
    (D : PaperHomogeneousNormalPresentationData K σ ι I) (p : MvPolynomial ι K) :
    D.polynomialMap p = 0 ↔ MvPolynomial.aeval D.generator p = 0 := by
  change paperNativeReesMvPolynomialSpecialization I D.idealElements p = 0 ↔ _
  rw [paperNativeReesMvPolynomialSpecialization_eq_zero_iff,
    paperHomogeneousSubstitution_eq_zero_iff D.generator D.degree D.degree_pos D.homogeneous p]
  apply forall_congr'
  intro n
  exact D.homogeneous_mem_succ_iff _ n (MvPolynomial.homogeneousComponent_isHomogeneous n p)

/-- The normal presentation and the ordinary generator presentation have identical relation ideals. -/
theorem PaperHomogeneousNormalPresentationData.kernel_eq
    (D : PaperHomogeneousNormalPresentationData K σ ι I) :
    RingHom.ker D.polynomialMap = RingHom.ker (MvPolynomial.aeval (R := K) D.generator).toRingHom := by
  ext p
  exact D.polynomialMap_eq_zero_iff p

/-- The coordinate ring of the actual generator family maps into the native associated graded ring. -/
def PaperHomogeneousNormalPresentationData.relationQuotientMap
    (D : PaperHomogeneousNormalPresentationData K σ ι I) :
    (MvPolynomial ι K ⧸ RingHom.ker (MvPolynomial.aeval (R := K) D.generator).toRingHom) →+*
      PaperIdealAssociatedGraded I :=
  Ideal.Quotient.lift _ D.polynomialMap
    (fun p hp => (D.polynomialMap_eq_zero_iff p).mpr (RingHom.mem_ker.mp hp))

/-- Quotienting by the original relations gives an actual embedding into the normal cone ring. -/
theorem PaperHomogeneousNormalPresentationData.relationQuotientMap_injective
    (D : PaperHomogeneousNormalPresentationData K σ ι I) :
    Function.Injective D.relationQuotientMap := by
  apply RingHom.lift_injective_of_ker_le_ideal
  exact le_of_eq D.kernel_eq

/-- The quotient embedding retains the specified normal representative of every polynomial. -/
theorem PaperHomogeneousNormalPresentationData.relationQuotientMap_mk
    (D : PaperHomogeneousNormalPresentationData K σ ι I) (p : MvPolynomial ι K) :
    D.relationQuotientMap (Ideal.Quotient.mk _ p) = D.polynomialMap p :=
  Ideal.Quotient.lift_mk _ _ _

/-- The native subring generated by the original polynomials embeds in their normal cone ring. -/
def PaperHomogeneousNormalPresentationData.generatorRingEmbedding
    (D : PaperHomogeneousNormalPresentationData K σ ι I) :
    (MvPolynomial.aeval (R := K) D.generator).toRingHom.range →+* PaperIdealAssociatedGraded I :=
  D.relationQuotientMap.comp
    (RingHom.quotientKerEquivRange (MvPolynomial.aeval (R := K) D.generator).toRingHom).symm.toRingHom

/-- No original generator-ring element is lost in normal coordinates. -/
theorem PaperHomogeneousNormalPresentationData.generatorRingEmbedding_injective
    (D : PaperHomogeneousNormalPresentationData K σ ι I) :
    Function.Injective D.generatorRingEmbedding :=
  D.relationQuotientMap_injective.comp
    (RingHom.quotientKerEquivRange (MvPolynomial.aeval (R := K) D.generator).toRingHom).symm.injective

/-- The normal polynomial map uses the actual degree-one initial classes. -/
theorem PaperHomogeneousNormalPresentationData.polynomialMap_X
    (D : PaperHomogeneousNormalPresentationData K σ ι I) (i : ι) :
    D.polynomialMap (MvPolynomial.X i : MvPolynomial ι K) =
      paperNativeReesSpecialization I
        (ReesGrading.mono I 1 (D.generator i) (by simpa only [pow_one] using D.generator_mem i)) :=
  paperNativeReesMvPolynomialSpecialization_X I D.idealElements i

end

end GaloisForLFunctions.HTGeometry
