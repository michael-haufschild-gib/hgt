import Mathlib.Algebra.Polynomial.Div
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! A proper scheme over a field with an affine principal cover is finite over the field. -/

open AlgebraicGeometry CategoryTheory Polynomial TopologicalSpace

namespace GlobalTheory.MulFinite

private theorem exists_pow_mul_eq_zero {K B : Type} [CommRing K] [CommRing B] (hK : IsField K)
    (φ : K →+* B) (a : B) (ha : φ.IsIntegralElem a) :
    ∃ (m : ℕ) (c b : B), IsUnit c ∧ a ^ m * (c + a * b) = 0 := by
  letI := hK.toField
  obtain ⟨p, hp, h₀⟩ := ha
  obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp.ne_zero 0
  rw [map_zero, sub_zero] at hq hnd
  rw [X_dvd_iff] at hnd
  refine ⟨p.rootMultiplicity 0, φ (q.coeff 0), q.divX.eval₂ φ a, (Ne.isUnit hnd).map φ, ?_⟩
  rw [hq, ← X_mul_divX_add q, eval₂_mul, eval₂_pow, eval₂_X, eval₂_add, eval₂_mul, eval₂_X,
    eval₂_C] at h₀
  rw [add_comm]
  exact h₀

/-- A global function on a universally closed scheme over a field has clopen nonvanishing locus. -/
theorem isClosed_basicOpen {Z : Scheme.{0}} {K : Type} [Field K] (f : Z ⟶ Spec (.of K))
    [UniversallyClosed f] (a : Γ(Z, ⊤)) : IsClosed (Z.basicOpen a : Set Z) := by
  have hK : IsField Γ(Spec (.of K), ⊤) :=
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)
  obtain ⟨m, c, b, hc, e⟩ := exists_pow_mul_eq_zero hK _ a (isIntegral_appTop_of_universallyClosed f a)
  have he : (Z.basicOpen a : Set Z) = (Z.basicOpen (c + a * b) : Set Z)ᶜ := by
    ext z
    simp only [Set.mem_compl_iff, SetLike.mem_coe]
    rw [Scheme.mem_basicOpen Z a z trivial, Scheme.mem_basicOpen Z (c + a * b) z trivial]
    let G : Γ(Z, ⊤) →+* Z.presheaf.stalk z := (Z.presheaf.germ ⊤ z trivial).hom
    change IsUnit (G a) ↔ ¬ IsUnit (G (c + a * b))
    have e' : G a ^ m * G (c + a * b) = 0 := by rw [← map_pow, ← map_mul, e, map_zero]
    constructor
    · intro ha hd
      exact ((ha.pow m).mul hd).ne_zero e'
    · intro hd
      have hc' : IsUnit (G (c + a * b) + (- (G a * G b))) := by
        simpa using hc.map G
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hc' with h | h
      · exact (hd h).elim
      · exact isUnit_of_mul_isUnit_left ((IsUnit.neg_iff _).1 h)
  rw [he]
  exact (Z.basicOpen _).isOpen.isClosed_compl

/-- On a proper scheme over a field, an affine principal cover consists of finite schemes. -/
theorem locallyQuasiFinite_of_basicOpen_cover {Z : Scheme.{0}} {K : Type} [Field K]
    (f : Z ⟶ Spec (.of K)) [IsProper f] {I : Type} (a : I → Γ(Z, ⊤))
    (hcov : ⨆ i, Z.basicOpen (a i) = ⊤) (ha : ∀ i, IsAffineOpen (Z.basicOpen (a i))) :
    LocallyQuasiFinite f := by
  letI : IsZariskiLocalAtSource @LocallyQuasiFinite.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyQuasiFinite.{0}) _ hcov fun i => ?_
  haveI : IsClosedImmersion (Z.basicOpen (a i)).ι :=
    .of_isPreimmersion _ (by simpa using isClosed_basicOpen f (a i))
  haveI : IsAffine (Z.basicOpen (a i)).toScheme := ha i
  haveI : IsFinite ((Z.basicOpen (a i)).ι ≫ f) :=
    IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  infer_instance

/-- The inverse image of any target open in a residue-field spectrum is empty or the whole spectrum. -/
theorem isAffineHom_fromSpecResidueField (Y : Scheme.{0}) (y : Y) :
    IsAffineHom (Y.fromSpecResidueField y) := by
  refine ⟨fun U _ => ?_⟩
  by_cases hy : y ∈ U
  · have e : Y.fromSpecResidueField y ⁻¹ᵁ U = ⊤ := by
      ext x
      simpa using hy
    rw [e]
    exact isAffineOpen_top _
  · have e : Y.fromSpecResidueField y ⁻¹ᵁ U = ⊥ := by
      ext x
      simpa using hy
    rw [e]
    exact isAffineOpen_bot _

end GlobalTheory.MulFinite
