import GaloisForLFunctions.HTGeometry.NonconstantMvPolynomialRoot
import GaloisForLFunctions.HTGeometry.ScalarExtendedPolynomialRegular

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A nonconstant complex polynomial remains a nonunit after scalar extension to every nontrivial
complex algebra. -/
theorem mvPolynomial_map_algebraMap_not_isUnit_of_not_constant
    {A σ : Type*} [CommRing A] [Nontrivial A] [Algebra ℂ A]
    (P : MvPolynomial σ ℂ) (hP : ¬ IsConstantMvPolynomial P) :
    ¬ IsUnit (MvPolynomial.map (algebraMap ℂ A) P) := by
  obtain ⟨x, hx⟩ := exists_mvPolynomial_eval_eq_zero_of_not_constant hP
  let φ : MvPolynomial σ A →+* A :=
    MvPolynomial.eval₂Hom (RingHom.id A) (fun i => algebraMap ℂ A (x i))
  intro hunit
  have hmapunit := hunit.map φ
  have hzero : φ (MvPolynomial.map (algebraMap ℂ A) P) = 0 := by
    change MvPolynomial.eval₂ (RingHom.id A) (fun i => algebraMap ℂ A (x i))
      (MvPolynomial.map (algebraMap ℂ A) P) = 0
    rw [MvPolynomial.eval₂_map]
    simp only [RingHom.id_comp]
    rw [MvPolynomial.eval₂_eq_eval_map]
    have hmap := congrArg (algebraMap ℂ A) hx
    rw [MvPolynomial.map_eval] at hmap
    simpa [Function.comp_def] using hmap
  rw [hzero] at hmapunit
  exact not_isUnit_zero hmapunit

/-- The principal hypersurface ideal of a nonconstant scalar polynomial is proper after arbitrary
nontrivial complex scalar extension. -/
theorem scalarExtendedPolynomial_span_ne_top_of_not_constant
    {A σ : Type*} [CommRing A] [Nontrivial A] [Algebra ℂ A]
    (P : MvPolynomial σ ℂ) (hP : ¬ IsConstantMvPolynomial P) :
    Ideal.span {MvPolynomial.map (algebraMap ℂ A) P} ≠ ⊤ :=
  Ideal.span_singleton_ne_top
    (mvPolynomial_map_algebraMap_not_isUnit_of_not_constant P hP)

/-- The scalar-extended hypersurface coordinate ring of a nonconstant complex polynomial is
nontrivial over every nontrivial complex coefficient algebra. -/
theorem scalarExtendedPolynomial_quotient_nontrivial_of_not_constant
    {A σ : Type*} [CommRing A] [Nontrivial A] [Algebra ℂ A]
    (P : MvPolynomial σ ℂ) (hP : ¬ IsConstantMvPolynomial P) :
    Nontrivial
      ((MvPolynomial σ A) ⧸ Ideal.span {MvPolynomial.map (algebraMap ℂ A) P}) :=
  Ideal.Quotient.nontrivial_iff.mpr
    (scalarExtendedPolynomial_span_ne_top_of_not_constant P hP)

end
end GaloisForLFunctions.HTGeometry
