import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.LinearMomentQuotient
import GaloisForLFunctions.HTGeometry.ShiftTranslateFiltration

/-!
# Affine moment levels preserve the neutral degree filtration

A moment level is a linear functional on the relation space `L ≤ K^ι`.
Extending this functional to `K^ι` supplies an actual point realizing the
level. Translation by that point identifies the affine moment quotient with
the homogeneous quotient, hence with a polynomial ring in `|ι| - dim L`
variables. Both translations preserve total degree exactly.

Thus the algebraic mechanism of Brown's moment-map reduction extends to every
linear moment level. At nonzero levels the relevant structure is the image
of the degree filtration; the equations need not be homogeneous.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module
variable {ι : Type*} (K : Type*) [Field K]

/-- The existing translation filtration bound applies to the coordinate algebra equivalence. -/
theorem momentTranslation_totalDegree_le (a : ι → K) (f : MvPolynomial ι K) :
    (mvPolynomialBaseTranslation a f).totalDegree ≤ f.totalDegree :=
  totalDegree_bind₁_translatedVariable_le a f

/-- Negating the translation vector gives the inverse coordinate change. -/
theorem momentTranslation_neg (a : ι → K) :
    mvPolynomialBaseTranslation (-a) = (mvPolynomialBaseTranslation a).symm := by
  ext i
  simp [mvPolynomialBaseTranslation, sub_eq_add_neg]

/-- Translation preserves total degree exactly, over an arbitrary field. -/
theorem momentTranslation_totalDegree (a : ι → K) (f : MvPolynomial ι K) :
    (mvPolynomialBaseTranslation a f).totalDegree = f.totalDegree := by
  apply le_antisymm (momentTranslation_totalDegree_le K a f)
  have h := momentTranslation_totalDegree_le K (-a) (mvPolynomialBaseTranslation a f)
  rwa [momentTranslation_neg, AlgEquiv.symm_apply_apply] at h

/-- Translation maps each bounded-degree subspace onto itself. -/
theorem momentTranslation_restrictTotalDegree (a : ι → K) (D : ℕ) :
    (restrictTotalDegree ι K D).map (mvPolynomialBaseTranslation a).toLinearMap =
      restrictTotalDegree ι K D := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [mem_restrictTotalDegree]
    change (mvPolynomialBaseTranslation a g).totalDegree ≤ D
    rw [momentTranslation_totalDegree]
    exact (mem_restrictTotalDegree _ _ _).mp hg
  · intro hf
    refine ⟨(mvPolynomialBaseTranslation a).symm f, ?_, AlgEquiv.apply_symm_apply _ _⟩
    rw [← momentTranslation_neg]
    apply (mem_restrictTotalDegree _ _ _).mpr
    rw [momentTranslation_totalDegree]
    exact (mem_restrictTotalDegree _ _ _).mp hf

variable [Fintype ι]

theorem eval_momentLinearForm (a c : ι → K) :
    eval a (momentLinearForm K c) = ∑ i, c i * a i := by
  simp [momentLinearForm_apply, smul_eq_C_mul]

/-- Every level is realized by a coordinate point, obtained by extending its linear functional. -/
theorem exists_momentLevelPoint (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) :
    ∃ a : ι → K, ∀ c : L, eval a (momentLinearForm K c.1) = ℓ c := by
  classical
  obtain ⟨g, hg⟩ := ℓ.exists_extend
  refine ⟨fun i => g (Pi.basisFun K ι i), ?_⟩
  intro c
  rw [eval_momentLinearForm]
  have he : ∑ i, c.1 i • Pi.basisFun K ι i = c.1 := by
    simpa using (Pi.basisFun K ι).sum_repr c.1
  calc
    ∑ i, c.1 i * g (Pi.basisFun K ι i) = g (∑ i, c.1 i • Pi.basisFun K ι i) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = g c.1 := congrArg g he
    _ = ℓ c := DFunLike.congr_fun hg c

/-- A point realizing all moment equations simultaneously. -/
def momentLevelPoint (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) : ι → K :=
  Classical.choose (exists_momentLevelPoint K L ℓ)

theorem momentLevelPoint_spec (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) (c : L) :
    eval (momentLevelPoint K L ℓ) (momentLinearForm K c.1) = ℓ c :=
  Classical.choose_spec (exists_momentLevelPoint K L ℓ) c

/-- The affine equations prescribed by a linear functional on the relation space. -/
def affineMomentIdeal (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) : Ideal (MvPolynomial ι K) :=
  Ideal.span (Set.range (fun c : L => momentLinearForm K c.1 - C (ℓ c)))

/-- Translating a linear form adds its value at the translation point. -/
theorem momentTranslation_linearForm (a c : ι → K) :
    mvPolynomialBaseTranslation a (momentLinearForm K c) =
      momentLinearForm K c + C (eval a (momentLinearForm K c)) := by
  simp only [momentLinearForm_apply, map_sum, map_smul,
    mvPolynomialBaseTranslation_X, smul_add, Finset.sum_add_distrib]
  congr 1
  simp [smul_eq_C_mul]

theorem momentTranslation_neg_linearForm (a c : ι → K) :
    mvPolynomialBaseTranslation (-a) (momentLinearForm K c) =
      momentLinearForm K c - C (eval a (momentLinearForm K c)) := by
  rw [momentTranslation_linearForm]
  simp only [eval_momentLinearForm, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib,
    map_neg, sub_eq_add_neg]

/-- The affine ideal is the inverse translate of the homogeneous moment ideal. -/
theorem affineMomentIdeal_eq_map_neg (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) :
    affineMomentIdeal K L ℓ = (momentLinearIdeal K L).map
      (mvPolynomialBaseTranslation (-momentLevelPoint K L ℓ)).toRingHom := by
  have h (c : L) : mvPolynomialBaseTranslation (-momentLevelPoint K L ℓ)
      (momentLinearForm K c.1) = momentLinearForm K c.1 - C (ℓ c) := by
    rw [momentTranslation_neg_linearForm, momentLevelPoint_spec]
  rw [affineMomentIdeal, momentLinearIdeal, Ideal.map_span]
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨momentLinearForm K c.1, ⟨c.1, c.2, rfl⟩, h c⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨⟨c, hc⟩, (h ⟨c, hc⟩).symm⟩

/-- Neutral substitution gives the actual affine bilinear moment equations. -/
theorem affineMomentIdeal_extended (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) :
    (affineMomentIdeal K L ℓ).map (invariantSubstitution K) =
      Ideal.span (Set.range (fun c : L =>
        (∑ i, C (c.1 i) * (X (Sum.inl i) * X (Sum.inr i))) - C (ℓ c))) := by
  have h (c : L) : invariantSubstitution K (momentLinearForm K c.1 - C (ℓ c)) =
      (∑ i, C (c.1 i) * (X (Sum.inl i) * X (Sum.inr i))) - C (ℓ c) := by
    simp [momentLinearForm_apply, smul_eq_C_mul, invariantSubstitution]
  rw [affineMomentIdeal, Ideal.map_span]
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, (h c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨c, rfl⟩, h c⟩

/-- Translation by the realizing point removes every affine moment constant. -/
theorem affineMomentIdeal_translate (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) :
    (affineMomentIdeal K L ℓ).map
      (mvPolynomialBaseTranslation (momentLevelPoint K L ℓ)).toRingHom = momentLinearIdeal K L := by
  have h (c : L) : mvPolynomialBaseTranslation (momentLevelPoint K L ℓ)
      (momentLinearForm K c.1 - C (ℓ c)) = momentLinearForm K c.1 := by
    rw [map_sub, momentTranslation_linearForm, momentLevelPoint_spec]
    have hc : mvPolynomialBaseTranslation (momentLevelPoint K L ℓ) (C (ℓ c)) = C (ℓ c) :=
      (mvPolynomialBaseTranslation (momentLevelPoint K L ℓ)).commutes (ℓ c)
    rw [hc, add_sub_cancel_right]
  rw [affineMomentIdeal, Ideal.map_span, momentLinearIdeal]
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    change mvPolynomialBaseTranslation (momentLevelPoint K L ℓ)
      (momentLinearForm K c.1 - C (ℓ c)) ∈ _
    rw [h]
    exact ⟨c.1, c.2, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, ⟨⟨c, hc⟩, rfl⟩, h ⟨c, hc⟩⟩

/-- Translation identifies any affine neutral quotient with its zero-level counterpart. -/
def affineMomentQuotientEquiv (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) :
    (MvPolynomial ι K ⧸ affineMomentIdeal K L ℓ) ≃ₐ[K]
      (MvPolynomial ι K ⧸ momentLinearIdeal K L) :=
  Ideal.quotientEquivAlg _ _ (mvPolynomialBaseTranslation (momentLevelPoint K L ℓ))
    (affineMomentIdeal_translate K L ℓ).symm

/-- Every moment level has the same number of surviving polynomial coordinates. -/
def affineMomentPolynomialEquiv (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) :
    (MvPolynomial ι K ⧸ affineMomentIdeal K L ℓ) ≃ₐ[K]
      MvPolynomial (Fin (Module.finrank K ((ι → K) ⧸ L))) K :=
  (affineMomentQuotientEquiv K L ℓ).trans (momentQuotientPolynomialEquiv K L)

/-- Translate to zero level, then use polynomial coordinates on the homogeneous quotient. -/
def affineMomentCoordinateMap (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) :
    MvPolynomial ι K →ₐ[K] MvPolynomial (Fin (Module.finrank K ((ι → K) ⧸ L))) K :=
  (momentCoordinateMap K L).comp (mvPolynomialBaseTranslation (momentLevelPoint K L ℓ)).toAlgHom

/-- The coordinate map factors through the actual affine quotient. -/
theorem affineMomentCoordinateMap_mk (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K)
    (f : MvPolynomial ι K) :
    affineMomentPolynomialEquiv K L ℓ (Ideal.Quotient.mk (affineMomentIdeal K L ℓ) f) =
      affineMomentCoordinateMap K L ℓ f := rfl

/-- Polynomial coordinates identify the full bounded-degree images at every moment level. -/
theorem affineMomentCoordinateMap_restrictTotalDegree
    (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) (D : ℕ) :
    (restrictTotalDegree ι K D).map (affineMomentCoordinateMap K L ℓ).toLinearMap =
      restrictTotalDegree (Fin (Module.finrank K ((ι → K) ⧸ L))) K D := by
  change (restrictTotalDegree ι K D).map
    ((momentCoordinateMap K L).toLinearMap.comp
      (mvPolynomialBaseTranslation (momentLevelPoint K L ℓ)).toLinearMap) = _
  rw [Submodule.map_comp, momentTranslation_restrictTotalDegree,
    momentCoordinateMap_restrictTotalDegree]

/-- Every linear moment level gives a nonzero neutral quotient. -/
theorem affineMomentIdeal_ne_top (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) :
    affineMomentIdeal K L ℓ ≠ ⊤ := by
  intro h
  have h1 : (1 : MvPolynomial ι K) ∈ affineMomentIdeal K L ℓ := by rw [h]; trivial
  have hz : (1 : MvPolynomial ι K ⧸ affineMomentIdeal K L ℓ) = 0 := by
    simpa only [map_one] using Ideal.Quotient.eq_zero_iff_mem.mpr h1
  have he := congrArg (affineMomentPolynomialEquiv K L ℓ) hz
  exact one_ne_zero (by simpa only [map_one, map_zero] using he)

/-- Every minimal weight monomial survives at every linear moment level. -/
theorem affineMoment_minimalWeight_ne_zero (q : ι → ℤ)
    (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) :
    Ideal.Quotient.mk ((affineMomentIdeal K L ℓ).map (invariantSubstitution K))
      (monomial (normalWeightExponent q 0) (1 : K)) ≠ 0 :=
  (minimalWeight_mk_ne_zero_iff K q _).mpr (affineMomentIdeal_ne_top K L ℓ)

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.affineMomentPolynomialEquiv
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.affineMomentCoordinateMap_restrictTotalDegree
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.affineMoment_minimalWeight_ne_zero
