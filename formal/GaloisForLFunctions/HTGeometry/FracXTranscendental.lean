import GaloisForLFunctions.HTGeometry.FreeParameterBaseChange
import GaloisForLFunctions.HTGeometry.TranscendentalBaseChangeLattice

/-!
# The free parameter of the rational-function model

In `FractionRing (Polynomial E)` the variable is transcendental over `E`, and together with `E` it
generates everything.  These are the two hypotheses the base-change lattice theorem needs, in the
model where the free parameter is a formal variable rather than a coordinate of an ambient field.

With them the transfer of primitivity along a free parameter is available for any finite Galois
extension: no field lies strictly between `F(T)` and `J(T)` as soon as none lies strictly between
`F` and `J`.
-/

open IntermediateField

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The evaluation of a polynomial at the free parameter is its image in the fraction field. -/
theorem aeval_fracX (p : Polynomial E) :
    Polynomial.aeval (fracX E) p
      = algebraMap (Polynomial E) (FractionRing (Polynomial E)) p := by
  have hX : Polynomial.aeval (fracX E) (Polynomial.X : Polynomial E) = fracX E := by
    simp
  have h := Polynomial.algHom_ext (f := (Polynomial.aeval (fracX E) :
      Polynomial E →ₐ[E] FractionRing (Polynomial E)))
    (g := IsScalarTower.toAlgHom E (Polynomial E) (FractionRing (Polynomial E))) ?_
  · exact congrFun (congrArg (fun f : Polynomial E →ₐ[E] FractionRing (Polynomial E) =>
      (f : Polynomial E → FractionRing (Polynomial E))) h) p
  · rw [hX]
    rfl

/-- **The free parameter is transcendental over the coefficient field.** -/
theorem transcendental_fracX : Transcendental E (fracX E) := by
  rw [transcendental_iff]
  intro p hp
  rw [aeval_fracX] at hp
  exact IsFractionRing.injective (Polynomial E) (FractionRing (Polynomial E))
    (by rw [hp, _root_.map_zero])

/-- The coefficient field, inside the rational functions, as an intermediate field over the base. -/
def fracCoeffField (F E : Type*) [Field F] [Field E] [Algebra F E] :
    IntermediateField F (FractionRing (Polynomial E)) :=
  (IsScalarTower.toAlgHom F E (FractionRing (Polynomial E))).fieldRange

theorem mem_fracCoeffField (a : E) :
    algebraMap E (FractionRing (Polynomial E)) a ∈ fracCoeffField F E :=
  ⟨a, rfl⟩

/-- **The coefficient field and the free parameter generate the rational functions.** -/
theorem fracCoeffField_sup_adjoin_fracX_eq_top :
    fracCoeffField F E ⊔ F⟮fracX E⟯ = ⊤ := by
  refine eq_top_of_mem_of_mem (S := fracCoeffField F E ⊔ F⟮fracX E⟯) ?_ ?_
  · intro a
    exact le_sup_left (α := IntermediateField F (FractionRing (Polynomial E)))
      (mem_fracCoeffField a)
  · exact le_sup_right (α := IntermediateField F (FractionRing (Polynomial E)))
      (IntermediateField.mem_adjoin_simple_self F (fracX E))

/-- The coefficient field is isomorphic to its copy inside the rational functions. -/
noncomputable def fracCoeffFieldEquiv : E ≃ₐ[F] ↥(fracCoeffField F E) :=
  AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E (FractionRing (Polynomial E)))

instance fracCoeffField_finiteDimensional [FiniteDimensional F E] :
    FiniteDimensional F ↥(fracCoeffField F E) :=
  Module.Finite.equiv (fracCoeffFieldEquiv (F := F) (E := E)).toLinearEquiv

instance fracCoeffField_isGalois [FiniteDimensional F E] [IsGalois F E] :
    IsGalois F ↥(fracCoeffField F E) :=
  IsGalois.of_algEquiv (fracCoeffFieldEquiv (F := F) (E := E))

/-- The free parameter is transcendental over the copy of the coefficient field. -/
theorem transcendental_fracX_over_fracCoeffField :
    Transcendental (↥(fracCoeffField F E)) (fracX E) := by
  rw [transcendental_iff]
  intro p hp
  set e : E ≃ₐ[F] ↥(fracCoeffField F E) := fracCoeffFieldEquiv with he
  set φ : ↥(fracCoeffField F E) →+* E := (e.symm : ↥(fracCoeffField F E) →ₐ[F] E).toRingHom with hφ
  have hcomp : ((algebraMap E (FractionRing (Polynomial E))).comp φ)
      = algebraMap (↥(fracCoeffField F E)) (FractionRing (Polynomial E)) := by
    ext y
    show algebraMap E (FractionRing (Polynomial E)) (e.symm y)
      = (y : FractionRing (Polynomial E))
    exact congrArg (fun z : ↥(fracCoeffField F E) => (z : FractionRing (Polynomial E)))
      (e.apply_symm_apply y)
  have haeval : Polynomial.aeval (fracX E) (p.map φ) = Polynomial.aeval (fracX E) p := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.aeval_def]
  have hq : p.map φ = 0 :=
    transcendental_iff.1 (transcendental_fracX (E := E)) (p.map φ) (by rw [haeval, hp])
  have hinj : Function.Injective φ := by
    rw [hφ]
    exact (e.symm : ↥(fracCoeffField F E) →ₐ[F] E).toRingHom.injective
  exact (Polynomial.map_eq_zero_iff hinj).1 hq

theorem transcendental_fracX_over_base : Transcendental F (fracX E) := by
  intro halg
  exact transcendental_fracX_over_fracCoeffField (F := F) (E := E)
    (halg.tower_top (↥(fracCoeffField F E)))

/-- **Free-parameter base change preserves primitivity.**  If no field lies strictly between `F` and
`J` inside the rational functions, then none lies strictly between `F(T)` and `J(T)`. -/
theorem eq_bot_or_eq_adjoin_fracX_of_primitive
    [FiniteDimensional F E] [IsGalois F E]
    (J : IntermediateField F (FractionRing (Polynomial E))) (hJ : J ≤ fracCoeffField F E)
    (hprim : ∀ P : IntermediateField F (FractionRing (Polynomial E)), P ≤ J → P = ⊥ ∨ P = J)
    (M : IntermediateField (↥F⟮fracX E⟯) (FractionRing (Polynomial E)))
    (hM : M ≤ IntermediateField.adjoin (↥F⟮fracX E⟯)
      (J : Set (FractionRing (Polynomial E)))) :
    M = ⊥ ∨ M = IntermediateField.adjoin (↥F⟮fracX E⟯)
      (J : Set (FractionRing (Polynomial E))) :=
  eq_bot_or_eq_adjoin_of_primitive_base_change (fracCoeffField F E) (fracX E)
    transcendental_fracX_over_base transcendental_fracX_over_fracCoeffField
    fracCoeffField_sup_adjoin_fracX_eq_top J hJ hprim M hM

/-! ### The rational functions realize any simple transcendental extension -/

section Realize

variable {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω]

theorem aeval_injective_of_transcendental {t : Ω} (ht : Transcendental E t) :
    Function.Injective (Polynomial.aeval t : Polynomial E →ₐ[E] Ω) := by
  intro p q hpq
  have hzero : Polynomial.aeval t (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  exact sub_eq_zero.mp (transcendental_iff.1 ht (p - q) hzero)

/-- The embedding of the rational functions determined by a transcendental element. -/
noncomputable def fracRealize {t : Ω} (ht : Transcendental E t) :
    FractionRing (Polynomial E) →ₐ[E] Ω :=
  IsFractionRing.liftAlgHom (A := Polynomial E) (K := FractionRing (Polynomial E))
    (g := (Polynomial.aeval t : Polynomial E →ₐ[E] Ω)) (aeval_injective_of_transcendental ht)

@[simp] theorem fracRealize_algebraMap {t : Ω} (ht : Transcendental E t) (p : Polynomial E) :
    fracRealize ht (algebraMap (Polynomial E) (FractionRing (Polynomial E)) p)
      = Polynomial.aeval t p := by
  rw [fracRealize, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

theorem fracRealize_fracX {t : Ω} (ht : Transcendental E t) :
    fracRealize ht (fracX E) = t := by
  rw [fracX, fracRealize_algebraMap]
  simp

/-- **The image of the rational functions is the simple transcendental extension.** -/
theorem fieldRange_fracRealize {t : Ω} (ht : Transcendental E t) :
    (fracRealize ht).fieldRange = IntermediateField.adjoin E {t} := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, rfl⟩
    obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := Polynomial E) x
    show fracRealize ht ((algebraMap (Polynomial E) (FractionRing (Polynomial E)) p) /
        (algebraMap (Polynomial E) (FractionRing (Polynomial E)) q))
      ∈ IntermediateField.adjoin E {t}
    rw [map_div₀, fracRealize_algebraMap, fracRealize_algebraMap]
    have hmem : ∀ r : Polynomial E,
        Polynomial.aeval t r ∈ IntermediateField.adjoin E {t} := by
      intro r
      exact IntermediateField.algebra_adjoin_le_adjoin E {t}
        (Polynomial.aeval_mem_adjoin_singleton E t)
    exact div_mem (hmem p) (hmem q)
  · refine IntermediateField.adjoin_le_iff.2 ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨fracX E, fracRealize_fracX ht⟩

end Realize

/-! ### Functoriality of the rational-function model -/

section Functorial

variable {F A B : Type*} [Field F] [Field A] [Field B] [Algebra F A] [Algebra F B]

/-- The map on rational functions induced by an embedding of coefficient fields. -/
noncomputable def fracMap (φ : A →ₐ[F] B) :
    FractionRing (Polynomial A) →ₐ[F] FractionRing (Polynomial B) := by
  refine IsFractionRing.liftAlgHom (R := F) (A := Polynomial A)
    (K := FractionRing (Polynomial A)) (L := FractionRing (Polynomial B))
    (g := (IsScalarTower.toAlgHom F (Polynomial B) (FractionRing (Polynomial B))).comp
      (Polynomial.mapAlgHom φ)) ?_
  have h1 : Function.Injective ⇑(Polynomial.mapAlgHom φ) :=
    Polynomial.map_injective (φ : A →+* B) φ.toRingHom.injective
  have h2 : Function.Injective
      ⇑(IsScalarTower.toAlgHom F (Polynomial B) (FractionRing (Polynomial B))) :=
    IsFractionRing.injective (Polynomial B) (FractionRing (Polynomial B))
  exact h2.comp h1

@[simp] theorem fracMap_algebraMap (φ : A →ₐ[F] B) (p : Polynomial A) :
    fracMap φ (algebraMap (Polynomial A) (FractionRing (Polynomial A)) p)
      = algebraMap (Polynomial B) (FractionRing (Polynomial B)) (p.map (φ : A →+* B)) := by
  rw [fracMap, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

theorem fracMap_fracX (φ : A →ₐ[F] B) : fracMap φ (fracX A) = fracX B := by
  rw [fracX, fracMap_algebraMap, Polynomial.map_X]
  rfl

theorem fracMap_injective (φ : A →ₐ[F] B) : Function.Injective (fracMap φ) :=
  (fracMap φ).toRingHom.injective

theorem fracMap_fracMap_ofId (φ : A →ₐ[F] B) (u : FractionRing (Polynomial F)) :
    fracMap φ (fracMap (Algebra.ofId F A) u) = fracMap (Algebra.ofId F B) u := by
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := Polynomial F) u
  have hmap : ∀ r : Polynomial F,
      (r.map (Algebra.ofId F A : F →+* A)).map (φ : A →+* B)
        = r.map (Algebra.ofId F B : F →+* B) := by
    intro r
    rw [Polynomial.map_map]
    congr 1
    ext a
    exact φ.commutes a
  simp only [map_div₀, fracMap_algebraMap, hmap]

/-- **The base rational functions are the field generated by the base and the parameter.** -/
theorem fieldRange_fracMap_ofId :
    (fracMap (Algebra.ofId F B)).fieldRange = IntermediateField.adjoin F {fracX B} := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, rfl⟩
    obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := Polynomial F) x
    show fracMap (Algebra.ofId F B)
        ((algebraMap (Polynomial F) (FractionRing (Polynomial F)) p) /
          (algebraMap (Polynomial F) (FractionRing (Polynomial F)) q))
      ∈ IntermediateField.adjoin F {fracX B}
    rw [map_div₀, fracMap_algebraMap, fracMap_algebraMap]
    have hmem : ∀ r : Polynomial F,
        algebraMap (Polynomial B) (FractionRing (Polynomial B))
            (r.map (Algebra.ofId F B : F →+* B))
          ∈ IntermediateField.adjoin F {fracX B} := by
      intro r
      have hC : ∀ a : F, algebraMap (Polynomial B) (FractionRing (Polynomial B))
          (Polynomial.C (algebraMap F B a)) = algebraMap F (FractionRing (Polynomial B)) a := by
        intro a
        rw [IsScalarTower.algebraMap_apply F B (FractionRing (Polynomial B)),
          IsScalarTower.algebraMap_apply B (Polynomial B) (FractionRing (Polynomial B))]
        rfl
      have hval : algebraMap (Polynomial B) (FractionRing (Polynomial B))
          (r.map (Algebra.ofId F B : F →+* B)) = Polynomial.aeval (fracX B) r := by
        rw [← fracMap_algebraMap (Algebra.ofId F B) r]
        rw [fracX]
        induction r using Polynomial.induction_on with
        | C a => simp [fracMap_algebraMap, Polynomial.aeval_C, hC]
        | add p q hp hq => simp [map_add, hp, hq]
        | monomial k a hk =>
            simp [fracMap_algebraMap, hC]
      rw [hval]
      exact IntermediateField.algebra_adjoin_le_adjoin F {fracX B}
        (Polynomial.aeval_mem_adjoin_singleton F (fracX B))
    exact div_mem (hmem p) (hmem q)
  · refine IntermediateField.adjoin_le_iff.2 ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨fracX F, fracMap_fracX (Algebra.ofId F B)⟩

/-- A polynomial whose coefficients lie in an intermediate field containing the parameter has its
image there too. -/
theorem algebraMap_polynomial_mem_of_coeffs {F' : Type*} [Field F']
    [Algebra F' (FractionRing (Polynomial B))]
    {S : IntermediateField F' (FractionRing (Polynomial B))} (hX : fracX B ∈ S) {r : Polynomial B}
    (hr : ∀ i, algebraMap B (FractionRing (Polynomial B)) (r.coeff i) ∈ S) :
    algebraMap (Polynomial B) (FractionRing (Polynomial B)) r ∈ S := by
  have himg : algebraMap (Polynomial B) (FractionRing (Polynomial B)) r =
      ∑ i ∈ r.support,
        algebraMap B (FractionRing (Polynomial B)) (r.coeff i) * (fracX B) ^ i := by
    conv_lhs => rw [Polynomial.as_sum_support_C_mul_X_pow r]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow]
    congr 1
  rw [himg]
  exact sum_mem fun i _ => mul_mem (hr i) (pow_mem hX i)

/-- **The image of the bridge lands in the field generated by the parameter and the coefficient
range.** -/
theorem fracMap_mem_adjoin (φ : A →ₐ[F] B) (x : FractionRing (Polynomial A)) :
    fracMap φ x ∈ IntermediateField.adjoin
      ↥(IntermediateField.adjoin F {fracX B})
      (((φ.fieldRange : IntermediateField F B).map
        (IsScalarTower.toAlgHom F B (FractionRing (Polynomial B)))) :
        Set (FractionRing (Polynomial B))) := by
  classical
  set S : IntermediateField ↥(IntermediateField.adjoin F {fracX B})
      (FractionRing (Polynomial B)) :=
    IntermediateField.adjoin ↥(IntermediateField.adjoin F {fracX B})
      (((φ.fieldRange : IntermediateField F B).map
        (IsScalarTower.toAlgHom F B (FractionRing (Polynomial B)))) :
        Set (FractionRing (Polynomial B))) with hS
  have hX : fracX B ∈ S := by
    have hbot : fracX B ∈ (⊥ : IntermediateField ↥(IntermediateField.adjoin F {fracX B})
        (FractionRing (Polynomial B))) :=
      ⟨⟨fracX B, IntermediateField.mem_adjoin_simple_self F (fracX B)⟩, rfl⟩
    exact (bot_le : (⊥ : IntermediateField ↥(IntermediateField.adjoin F {fracX B})
      (FractionRing (Polynomial B))) ≤ S) hbot
  have hcoeff : ∀ p : Polynomial A, ∀ i,
      algebraMap B (FractionRing (Polynomial B)) ((p.map (φ : A →+* B)).coeff i) ∈ S := by
    intro p i
    refine IntermediateField.subset_adjoin _ _ ?_
    refine ⟨(p.map (φ : A →+* B)).coeff i, ?_, rfl⟩
    rw [Polynomial.coeff_map]
    exact ⟨p.coeff i, rfl⟩
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := Polynomial A) x
  rw [map_div₀, fracMap_algebraMap, fracMap_algebraMap]
  exact div_mem (algebraMap_polynomial_mem_of_coeffs hX (hcoeff p))
    (algebraMap_polynomial_mem_of_coeffs hX (hcoeff q))

/-- **The induced map reflects the base rational functions.** -/
theorem mem_fieldRange_of_fracMap_mem (φ : A →ₐ[F] B) (x : FractionRing (Polynomial A))
    (hx : fracMap φ x ∈ (fracMap (Algebra.ofId F B)).fieldRange) :
    x ∈ (fracMap (Algebra.ofId F A)).fieldRange := by
  obtain ⟨u, hu⟩ := hx
  refine ⟨u, ?_⟩
  exact fracMap_injective φ ((fracMap_fracMap_ofId φ u).trans hu)

end Functorial

/-! ### The bridge: a simple transcendental extension into rational functions over a bigger field -/

section Bridge

variable {A Ω : Type*} [Field A] [Field Ω] [Algebra A Ω]

/-- The rational functions over `A` are the simple transcendental extension `A(t)`. -/
noncomputable def fracRealizeEquiv {t : Ω} (ht : Transcendental A t) :
    FractionRing (Polynomial A) ≃ₐ[A] ↥(IntermediateField.adjoin A {t}) :=
  (AlgEquiv.ofInjectiveField (fracRealize ht)).trans
    (IntermediateField.equivOfEq (fieldRange_fracRealize ht))

theorem fracRealizeEquiv_apply {t : Ω} (ht : Transcendental A t)
    (x : FractionRing (Polynomial A)) :
    ((fracRealizeEquiv ht x : ↥(IntermediateField.adjoin A {t})) : Ω) = fracRealize ht x := rfl

variable {F B : Type*} [Field F] [Field B] [Algebra F A] [Algebra F B] [Algebra F Ω]
  [IsScalarTower F A Ω]

theorem transcendental_of_tower {t : Ω} (ht : Transcendental A t) : Transcendental F t := by
  intro halg
  exact ht (halg.tower_top A)

/-- Realizing the base rational functions inside `Ω` is the same before and after enlarging the
coefficient field. -/
theorem fracRealize_fracMap_ofId {t : Ω} (ht : Transcendental A t)
    (u : FractionRing (Polynomial F)) :
    fracRealize ht (fracMap (Algebra.ofId F A) u)
      = fracRealize (transcendental_of_tower (A := A) ht) u := by
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := Polynomial F) u
  have hpoly : ∀ r : Polynomial F,
      Polynomial.aeval t (r.map (Algebra.ofId F A : F →+* A)) = Polynomial.aeval t r := by
    intro r
    have hcoe : ((Algebra.ofId F A : F →ₐ[F] A) : F →+* A) = algebraMap F A := rfl
    rw [hcoe, Polynomial.aeval_map_algebraMap]
  simp only [map_div₀, fracMap_algebraMap, fracRealize_algebraMap, hpoly]

/-- **The bridge.**  A simple transcendental extension embeds into the rational functions over any
bigger coefficient field, carrying the transcendental to the free parameter. -/
noncomputable def adjoinToFrac (φ : A →ₐ[F] B) {t : Ω} (ht : Transcendental A t) :
    ↥(IntermediateField.adjoin A {t}) →ₐ[F] FractionRing (Polynomial B) :=
  (fracMap φ).comp ((fracRealizeEquiv ht).symm.restrictScalars F).toAlgHom

theorem adjoinToFrac_injective (φ : A →ₐ[F] B) {t : Ω} (ht : Transcendental A t) :
    Function.Injective (adjoinToFrac φ ht) :=
  (adjoinToFrac φ ht).toRingHom.injective

/-- **The escape survives the bridge.** -/
theorem adjoinToFrac_notMem_of_notMem (φ : A →ₐ[F] B) {t : Ω} (ht : Transcendental A t)
    (y : ↥(IntermediateField.adjoin A {t}))
    (hy : (y : Ω) ∉ IntermediateField.adjoin F {t}) :
    adjoinToFrac φ ht y ∉ (fracMap (Algebra.ofId F B)).fieldRange := by
  intro hmem
  refine hy ?_
  have hx : fracMap φ ((fracRealizeEquiv ht).symm y) ∈ (fracMap (Algebra.ofId F B)).fieldRange :=
    hmem
  obtain ⟨u, hu⟩ := mem_fieldRange_of_fracMap_mem φ ((fracRealizeEquiv ht).symm y) hx
  rw [← fieldRange_fracRealize (transcendental_of_tower (A := A) ht)]
  refine ⟨u, ?_⟩
  show fracRealize (transcendental_of_tower (A := A) ht) u = (y : Ω)
  have hu' : fracMap (Algebra.ofId F A) u = (fracRealizeEquiv ht).symm y := hu
  have hback : fracRealize ht ((fracRealizeEquiv ht).symm y) = (y : Ω) := by
    rw [← fracRealizeEquiv_apply ht ((fracRealizeEquiv ht).symm y), AlgEquiv.apply_symm_apply]
  rw [← fracRealize_fracMap_ofId ht u, hu', hback]

theorem adjoinToFrac_apply_self (φ : A →ₐ[F] B) {t : Ω} (ht : Transcendental A t) :
    adjoinToFrac φ ht ⟨t, IntermediateField.mem_adjoin_simple_self A t⟩ = fracX B := by
  rw [adjoinToFrac]
  have hx : (fracRealizeEquiv ht).symm
      (⟨t, IntermediateField.mem_adjoin_simple_self A t⟩ :
        ↥(IntermediateField.adjoin A {t})) = fracX A := by
    refine (fracRealizeEquiv ht).injective ?_
    rw [AlgEquiv.apply_symm_apply]
    refine Subtype.ext ?_
    rw [fracRealizeEquiv_apply, fracRealize_fracX]
  show fracMap φ ((fracRealizeEquiv ht).symm _) = _
  rw [hx, fracMap_fracX]

end Bridge

end GaloisForLFunctions.HTGeometry

end
