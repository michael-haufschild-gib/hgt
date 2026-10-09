import GaloisForLFunctions.HTGeometry.PaperNativeReesSpecialization
import GaloisForLFunctions.HTGeometry.PaperWeightOrderIdeals
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.LaurentWeightedMap
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Multivariable polynomial coordinates in the native Rees special fibre

Apply OpenAI/math's `LaurentWeightedMap.evaluate_homogeneous` and coefficient
kernel theorem to arbitrary families of actual ideal elements. The coefficient
of Rees degree `n` is precisely the evaluation of the input's degree-`n`
homogeneous component. No scalar-tower assumptions on the quotient are needed.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial StableCoordinate

noncomputable section

variable {K R ι : Type*} [CommRing K] [CommRing R] [Algebra K R]
variable (I : Ideal R) (c : ι → I)

/-- Simultaneously lift any family of ideal elements to degree one of the native Rees algebra. -/
def paperNativeReesMvPolynomialMap : MvPolynomial ι K →+* reesAlgebra I :=
  MvPolynomial.eval₂Hom ((algebraMap R (reesAlgebra I)).comp (algebraMap K R))
    (fun i => ReesGrading.mono I 1 (c i) (by simpa only [pow_one] using (c i).property))

/-- The inverse-Laurent representative is exactly the source's weighted evaluation. -/
theorem paperNativeReesMvPolynomialMap_laurent (p : MvPolynomial ι K) :
    paperInverseLaurentPolynomial (paperNativeReesMvPolynomialMap I c p : Polynomial R) =
      LaurentWeightedMap.evaluate (fun _ => (1 : ℤ)) (fun i => (c i : R)) p := by
  have h : paperInverseLaurentPolynomial.toRingHom.comp
      ((reesAlgebra I).val.toRingHom.comp (paperNativeReesMvPolynomialMap (K := K) I c)) =
      (LaurentWeightedMap.evaluate (k := K) (fun _ => (1 : ℤ)) (fun i => (c i : R))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [paperNativeReesMvPolynomialMap, LaurentWeightedMap.evaluate,
        paperInverseLaurentPolynomial, LaurentPolynomial.algebraMap_apply]
    · intro i
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        paperNativeReesMvPolynomialMap, MvPolynomial.eval₂Hom_X',
        LaurentWeightedMap.evaluate_X]
      change paperInverseLaurentPolynomial (Polynomial.monomial 1 (c i : R)) = _
      simp [paperInverseLaurentPolynomial, Polynomial.toLaurent_C_mul_T]
  exact RingHom.congr_fun h p

/-- Homogeneous inputs give single native Rees coefficients, by the paper's weighted map theorem. -/
theorem paperNativeReesMvPolynomialMap_homogeneous
    (p : MvPolynomial ι K) (n : ℕ) (hp : p.IsHomogeneous n) :
    (paperNativeReesMvPolynomialMap I c p : Polynomial R) =
      Polynomial.monomial n (MvPolynomial.aeval (fun i => (c i : R)) p) := by
  apply Polynomial.toLaurent_injective
  apply LaurentPolynomial.invert.injective
  change paperInverseLaurentPolynomial _ = paperInverseLaurentPolynomial _
  have hh : p.IsWeightedHomogeneous (fun _ => (1 : ℤ)) (n : ℤ) :=
    paperIsWeightedHomogeneous_int hp
  rw [paperNativeReesMvPolynomialMap_laurent,
    LaurentWeightedMap.evaluate_homogeneous _ _ hh]
  change _ = LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.monomial n _))
  rw [Polynomial.toLaurent_C_mul_T, map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]

/-- Every native Rees coefficient is the evaluation of the corresponding homogeneous component. -/
theorem paperNativeReesMvPolynomialMap_coeff (p : MvPolynomial ι K) (n : ℕ) :
    (paperNativeReesMvPolynomialMap I c p : Polynomial R).coeff n =
      MvPolynomial.aeval (fun i => (c i : R)) (MvPolynomial.homogeneousComponent n p) := by
  classical
  have he : (paperNativeReesMvPolynomialMap I c p : Polynomial R) =
      ∑ j ∈ Finset.range (p.totalDegree + 1),
        Polynomial.monomial j
          (MvPolynomial.aeval (fun i => (c i : R)) (MvPolynomial.homogeneousComponent j p)) := by
    calc
      _ = (reesAlgebra I).val (paperNativeReesMvPolynomialMap I c
          (∑ j ∈ Finset.range (p.totalDegree + 1), MvPolynomial.homogeneousComponent j p)) := by
        rw [MvPolynomial.sum_homogeneousComponent]
        rfl
      _ = _ := by
        rw [map_sum, map_sum]
        apply Finset.sum_congr rfl
        intro j _
        exact paperNativeReesMvPolynomialMap_homogeneous I c _ j
          (MvPolynomial.homogeneousComponent_isHomogeneous j p)
  rw [he, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hn
  · rfl
  · rw [MvPolynomial.homogeneousComponent_eq_zero n p (by simpa using hn), map_zero]

/-- Simultaneous polynomial evaluation in the actual associated graded ring. -/
def paperNativeReesMvPolynomialSpecialization :
    MvPolynomial ι K →+* PaperIdealAssociatedGraded I :=
  (paperNativeReesSpecialization I).toRingHom.comp (paperNativeReesMvPolynomialMap I c)

/-- Each variable is the actual initial class of its chosen ideal element. -/
theorem paperNativeReesMvPolynomialSpecialization_X (i : ι) :
    paperNativeReesMvPolynomialSpecialization I c (MvPolynomial.X i : MvPolynomial ι K) =
      paperNativeReesSpecialization I
        (ReesGrading.mono I 1 (c i) (by simpa only [pow_one] using (c i).property)) := by
  simp [paperNativeReesMvPolynomialSpecialization, paperNativeReesMvPolynomialMap]

/-- The source coefficient kernel becomes an exact homogeneous-component test. -/
theorem paperNativeReesMvPolynomialSpecialization_eq_zero_iff (p : MvPolynomial ι K) :
    paperNativeReesMvPolynomialSpecialization I c p = 0 ↔
      ∀ n : ℕ, MvPolynomial.aeval (fun i => (c i : R))
        (MvPolynomial.homogeneousComponent n p) ∈ I ^ (n + 1) := by
  change paperNativeReesSpecialization I (paperNativeReesMvPolynomialMap I c p) = 0 ↔ _
  rw [paperNativeReesSpecialization_eq_zero_iff_coeff]
  simp only [paperNativeReesMvPolynomialMap_coeff]

end

end GaloisForLFunctions.HTGeometry
