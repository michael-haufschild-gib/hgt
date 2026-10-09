import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Topology.Algebra.MvPolynomial
import GaloisForLFunctions.HTGeometry.AlgebraSpectrumIntegralSurjective
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Compact complex algebraic sets are finite

Noether normalization and extension of complex points exclude positive-dimensional
normalizations of a compact point space. Finite-dimensional algebras then have finitely
many complex points. A quotient-point adapter applies this to compact affine zero loci.
No reducedness assumption is needed.
-/

open Set Topology
namespace GaloisForLFunctions.HTGeometry.AlgSpec
noncomputable section

/-- A finitely generated complex algebra with compact complex-point space has only finitely
many complex points, with no reducedness assumption. -/
theorem finite_of_compactSpace (A : Type*) [CommRing A] [Nontrivial A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] [CompactSpace (AlgSpec A)] : Finite (AlgSpec A) := by
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ A
  letI : Algebra (MvPolynomial (Fin s) ℂ) A := g.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ (MvPolynomial (Fin s) ℂ) A :=
    IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  haveI : Module.Finite (MvPolynomial (Fin s) ℂ) A := hfin
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) ℂ) A := Algebra.IsIntegral.of_finite _ _
  haveI : FaithfulSMul (MvPolynomial (Fin s) ℂ) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hg
  have hs : s = 0 := by
    by_contra hs
    let j : Fin s := ⟨0, Nat.pos_of_ne_zero hs⟩
    have hsurj : Function.Surjective (fun χ : AlgSpec A => χ (g (MvPolynomial.X j))) := by
      intro z
      let φ : AlgSpec (MvPolynomial (Fin s) ℂ) := MvPolynomial.aeval (fun _ => z)
      obtain ⟨χ, hχ⟩ := surjective_precomp_of_isIntegral
        (A := MvPolynomial (Fin s) ℂ) (B := A) φ
      refine ⟨χ, ?_⟩
      have he := DFunLike.congr_fun hχ (MvPolynomial.X j)
      change χ (g (MvPolynomial.X j)) = φ (MvPolynomial.X j) at he
      exact he.trans (MvPolynomial.aeval_X (fun _ : Fin s => z) j)
    have hc : IsCompact (Set.univ : Set ℂ) := by
      have h := (isCompact_univ : IsCompact (Set.univ : Set (AlgSpec A))).image
        (continuous_eval (g (MvPolynomial.X j)))
      rwa [Set.image_univ, hsurj.range_eq] at h
    exact noncompact_univ ℂ hc
  subst s
  haveI : Module.Finite ℂ (MvPolynomial (Fin 0) ℂ) :=
    Module.Finite.equiv (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0)).symm.toLinearEquiv
  haveI : Module.Finite ℂ A := Module.Finite.trans (MvPolynomial (Fin 0) ℂ) A
  exact inferInstanceAs (Finite (A →ₐ[ℂ] ℂ))

end
end GaloisForLFunctions.HTGeometry.AlgSpec


open Set Topology
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- A compact affine complex algebraic set is finite, including nonreduced presentations. -/
theorem finite_zeroLocus_of_isCompact {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hcompact : IsCompact (MvPolynomial.zeroLocus ℂ J)) :
    (MvPolynomial.zeroLocus ℂ J).Finite := by
  classical
  by_cases hJ : J = ⊤
  · subst J
    simp
  let R := MvPolynomial (Fin n) ℂ
  let A := R ⧸ J
  letI : Nontrivial A := Ideal.Quotient.nontrivial_iff.mpr hJ
  let point : MvPolynomial.zeroLocus ℂ J → AlgSpec A := fun x =>
    Ideal.Quotient.liftₐ J (MvPolynomial.aeval x.val) x.property
  have hpoint (x : MvPolynomial.zeroLocus ℂ J) (p : R) :
      point x (Ideal.Quotient.mkₐ ℂ J p) = MvPolynomial.eval x.val p := by
    change (Ideal.Quotient.liftₐ J (MvPolynomial.aeval x.val) x.property)
      (Ideal.Quotient.mkₐ ℂ J p) = _
    simp only [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.lift_mk]
    exact congrFun (MvPolynomial.aeval_eq_eval x.val) p
  have hinj : Function.Injective point := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have h := DFunLike.congr_fun hxy (Ideal.Quotient.mkₐ ℂ J (MvPolynomial.X i))
    simpa only [hpoint, MvPolynomial.eval_X] using h
  have hsurj : Function.Surjective point := by
    intro χ
    let θ : Fin n → ℂ := fun i => χ (Ideal.Quotient.mkₐ ℂ J (MvPolynomial.X i))
    have he : (χ : A →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ J) = MvPolynomial.aeval θ := by
      apply MvPolynomial.algHom_ext
      intro i
      change θ i = (MvPolynomial.aeval θ) (MvPolynomial.X i)
      exact (MvPolynomial.aeval_X θ i).symm
    have hp (p : R) : χ (Ideal.Quotient.mkₐ ℂ J p) = MvPolynomial.aeval θ p :=
      DFunLike.congr_fun he p
    have hθ : θ ∈ MvPolynomial.zeroLocus ℂ J := by
      intro p hpJ
      rw [← hp]
      have hz : Ideal.Quotient.mkₐ ℂ J p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hpJ
      rw [hz, map_zero]
    refine ⟨⟨θ, hθ⟩, ?_⟩
    apply DFunLike.ext
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ J a
    rw [hpoint, hp]
    exact (congrFun (MvPolynomial.aeval_eq_eval θ) p).symm
  have hcont : Continuous point := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ J a
    change Continuous fun x : MvPolynomial.zeroLocus ℂ J => point x (Ideal.Quotient.mkₐ ℂ J p)
    exact ((MvPolynomial.continuous_eval p).comp continuous_subtype_val).congr
      (fun x => (hpoint x p).symm)
  letI : CompactSpace (MvPolynomial.zeroLocus ℂ J) := isCompact_iff_compactSpace.mp hcompact
  letI : CompactSpace (AlgSpec A) := by
    constructor
    have hc := (isCompact_univ : IsCompact (Set.univ : Set (MvPolynomial.zeroLocus ℂ J))).image hcont
    rwa [Set.image_univ, hsurj.range_eq] at hc
  letI : Finite (AlgSpec A) := AlgSpec.finite_of_compactSpace A
  exact Set.finite_coe_iff.mp (Finite.of_injective point hinj)

end
end GaloisForLFunctions.HTGeometry
