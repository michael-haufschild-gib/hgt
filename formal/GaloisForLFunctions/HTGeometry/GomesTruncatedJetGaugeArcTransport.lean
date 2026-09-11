import GaloisForLFunctions.HTGeometry.GomesTruncatedJetGaugeCharacter

/-!
# Transporting actual gauge symmetries into the existing truncated arc geometry

The classified joint algebra embeds in the corpus's literal truncated arc
algebra. This embeds its entire gauge group into arc units, retaining both the
actual matrix and the geometric augmentation. Existing arc theorems can thus
be applied to these symmetries through a faithful concrete map.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The existing arc augmentation is the actual diagonal observation under the clock equivalence. -/
theorem gomesFiniteFockArcEquiv_diagonal (n : ℕ) (a : TruncatedArcAlgebra ℂ n)
    (i : Fin (n + 1)) :
    (gomesFiniteFockArcEquiv n a).val i i = truncatedArcAugmentation ℂ n a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [truncatedArcAugmentation_mk, ← Polynomial.coeff_zero_eq_eval_zero]
  exact gomesFiniteFockPolynomialHom_diagonal (n + 1) p i

/-- Every joint matrix symmetry determines an element of the existing truncated arc algebra. -/
def gomesTruncatedJetArcEmbedding (n : ℕ) (z : ℂ) :
    gomesTruncatedJetJointAlgebra n z →ₐ[ℂ] TruncatedArcAlgebra ℂ n :=
  (gomesFiniteFockArcEquiv n).symm.toAlgHom.comp
    (Subalgebra.inclusion (gomesTruncatedJetJointAlgebra_le_clock n z))

/-- The geometric arc embedding retains the literal matrix of every joint symmetry. -/
theorem gomesTruncatedJetArcEmbedding_matrix (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetJointAlgebra n z) :
    (gomesFiniteFockArcEquiv n (gomesTruncatedJetArcEmbedding n z E)).val = E.val := by
  change (gomesFiniteFockArcEquiv n ((gomesFiniteFockArcEquiv n).symm
    (Subalgebra.inclusion (gomesTruncatedJetJointAlgebra_le_clock n z) E))).val = E.val
  rw [AlgEquiv.apply_symm_apply]
  rfl

/-- Distinct actual joint symmetries remain distinct in the existing arc geometry. -/
theorem gomesTruncatedJetArcEmbedding_injective (n : ℕ) (z : ℂ) :
    Function.Injective (gomesTruncatedJetArcEmbedding n z) := by
  intro E F h
  apply Subtype.ext
  have hm := congrArg (fun a => (gomesFiniteFockArcEquiv n a).val) h
  simpa only [gomesTruncatedJetArcEmbedding_matrix] using hm

/-- The geometric arc augmentation agrees with the literal scalar coordinate. -/
theorem gomesTruncatedJetArcEmbedding_augmentation (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetJointAlgebra n z) :
    truncatedArcAugmentation ℂ n (gomesTruncatedJetArcEmbedding n z E) =
      gomesTruncatedJetAugmentation n z E := by
  rw [← gomesFiniteFockArcEquiv_diagonal n _ 0, gomesTruncatedJetArcEmbedding_matrix]
  rfl

/-- Every actual gauge transformation gives a unit of the existing geometric arc algebra. -/
def gomesTruncatedJetGaugeArcHom (n : ℕ) (z : ℂ) :
    gomesTruncatedJetGaugeGroup n z →* (TruncatedArcAlgebra ℂ n)ˣ :=
  (Units.map (gomesTruncatedJetArcEmbedding n z).toMonoidHom).comp
    (gomesTruncatedJetInternalUnitsEquiv n z).symm.toMonoidHom

/-- The transported arc unit acts by exactly the original gauge matrix. -/
theorem gomesTruncatedJetGaugeArcHom_matrix (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetGaugeGroup n z) :
    (gomesFiniteFockArcEquiv n (gomesTruncatedJetGaugeArcHom n z u).val).val = u.val.val :=
  gomesTruncatedJetArcEmbedding_matrix n z ((gomesTruncatedJetInternalUnitsEquiv n z).symm u).val

/-- The full matrix gauge group embeds faithfully in the existing arc unit group. -/
theorem gomesTruncatedJetGaugeArcHom_injective (n : ℕ) (z : ℂ) :
    Function.Injective (gomesTruncatedJetGaugeArcHom n z) := by
  intro u v h
  apply Subtype.ext
  apply Units.ext
  have hm := congrArg (fun a : (TruncatedArcAlgebra ℂ n)ˣ => (gomesFiniteFockArcEquiv n a.val).val) h
  simpa only [gomesTruncatedJetGaugeArcHom_matrix] using hm

/-- The actual gauge character is the existing geometric augmentation of its transported arc unit. -/
theorem gomesTruncatedJetGaugeArcHom_augmentation (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetGaugeGroup n z) :
    truncatedArcAugmentation ℂ n (gomesTruncatedJetGaugeArcHom n z u).val =
      (gomesTruncatedJetGaugeCharacter n z u).val :=
  gomesTruncatedJetArcEmbedding_augmentation n z ((gomesTruncatedJetInternalUnitsEquiv n z).symm u).val

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
