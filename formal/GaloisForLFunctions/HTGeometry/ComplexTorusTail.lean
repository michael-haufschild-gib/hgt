import GaloisForLFunctions.HTGeometry.EntireDenseInvariant
import GaloisForLFunctions.HTGeometry.MultiReparametrizationAutomorphism

/-!
# The phase tail of a complex torus protocol

On the generic reparametrisation of the entire fraction field of a complex space, an element
invariant under a dense set of deck translations is a ratio of jet polynomials with constant
coefficients: no position survives, and only the Maurer–Cartan velocities remain.

Over `ℂ` every connected commutative algebraic group is `ℂ^n / Λ`, so this is the deck-closure
statement for the whole class at once, in every dimension.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- **Translation commutes with every directional derivation of the entire fraction field.** -/
theorem fieldTranslateEquiv_dirDerivation (t v : V) (x : EntireField V) :
    fieldTranslateEquiv t (fieldDirDerivation v x)
      = fieldDirDerivation v (fieldTranslateEquiv t x) := by
  have hconj : (Derivation.mk'
      (({ toFun := fun z => (fieldTranslateEquiv t).symm
            (fieldDirDerivation v (fieldTranslateEquiv t z))
          map_zero' := by simp
          map_add' := by intro x y; simp } : EntireField V →+ EntireField V)).toIntLinearMap
      (by
        intro x y
        show (fieldTranslateEquiv t).symm (fieldDirDerivation v (fieldTranslateEquiv t (x * y)))
          = x • (fieldTranslateEquiv t).symm (fieldDirDerivation v (fieldTranslateEquiv t y))
            + y • (fieldTranslateEquiv t).symm (fieldDirDerivation v (fieldTranslateEquiv t x))
        rw [map_mul, Derivation.leibniz]
        simp only [smul_eq_mul, map_add, map_mul, RingEquiv.symm_apply_apply]))
      = fieldDirDerivation v := by
    refine GaloisForLFunctions.fractionRing_derivation_ext (A := entireSubring V) _ _ ?_
    intro a
    show (fieldTranslateEquiv t).symm (fieldDirDerivation v (fieldTranslateEquiv t
      (algebraMap (entireSubring V) (EntireField V) a))) = _
    rw [fieldTranslateEquiv_algebraMap]
    have h1 : fieldDirDerivation v (algebraMap (entireSubring V) (EntireField V)
        (entireTranslate t a))
        = algebraMap (entireSubring V) (EntireField V) (entireDirDeriv v (entireTranslate t a)) :=
      GaloisForLFunctions.fractionRingDerivation_algebraMap (entireDirDerivationField v) _
    have h2 : fieldDirDerivation v (algebraMap (entireSubring V) (EntireField V) a)
        = algebraMap (entireSubring V) (EntireField V) (entireDirDeriv v a) :=
      GaloisForLFunctions.fractionRingDerivation_algebraMap (entireDirDerivationField v) a
    rw [h1, h2, ← entireTranslate_dirDeriv, ← fieldTranslateEquiv_algebraMap,
      RingEquiv.symm_apply_apply]
  have hx := congrArg (fun D => D x) hconj
  rw [← hx]
  exact (fieldTranslateEquiv t).apply_symm_apply _

variable {n : ℕ}

/-- **The phase tail of a complex torus protocol has constant coefficients.**  An element of the
generic reparametrisation invariant under a dense set of deck translations is a ratio of jet
polynomials whose coefficients are complex constants. -/
theorem exists_const_coeff_representation_of_dense_translation_fixed
    {S : Set V} (hS : Dense S) (x : MultiReparamField (EntireField V) n)
    (hx : ∀ t ∈ S, MultiReparamField.fieldEquiv (n := n) (fieldTranslateEquiv t) x = x) :
    ∃ p q : MultiReparamPoly (EntireField V) n, q ≠ 0 ∧
      (∀ m, MvPolynomial.coeff m p ∈ (constEntire V).fieldRange) ∧
      (∀ m, MvPolynomial.coeff m q ∈ (constEntire V).fieldRange) ∧
      algebraMap (MultiReparamPoly (EntireField V) n) (MultiReparamField (EntireField V) n) q * x
        = algebraMap (MultiReparamPoly (EntireField V) n)
            (MultiReparamField (EntireField V) n) p := by
  classical
  set G : Set (EntireField V ≃+* EntireField V) :=
    {e | ∃ t ∈ S, e = fieldTranslateEquiv t} with hG
  have hxG : ∀ e ∈ G, MultiReparamField.fieldEquiv (n := n) e x = x := by
    rintro e ⟨t, ht, rfl⟩
    exact hx t ht
  have hSfix : ∀ a : EntireField V, (∀ e ∈ G, e a = a) → a ∈ (constEntire V).fieldRange := by
    intro a ha
    obtain ⟨c, hc⟩ := eq_constEntire_of_dense_translation_invariant hS
      (x := a) (fun t ht => ha _ ⟨t, ht, rfl⟩)
    exact ⟨c, hc.symm⟩
  exact MultiReparamField.exists_representation_coeff_mem G (constEntire V).fieldRange hSfix x hxG

end GaloisForLFunctions.HTGeometry
