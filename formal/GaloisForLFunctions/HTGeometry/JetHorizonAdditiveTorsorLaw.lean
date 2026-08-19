import GaloisForLFunctions.HTGeometry.ScalarAdditiveDifferentialTorsor

/-!
# The successive-torsor law for a jet horizon, over an arbitrary base

Between two consecutive layers of a derivative horizon of a differential-generic point on an
additive cylinder, exactly the lower jets of the cylinder coordinates are forgotten.  This file
computes the differential Galois group of one such layer *in the rank the card requires* and
*over a base which need not be constant*:

for a differentially independent family `q : ι → T` generating `T` over a differential field `F`
which shares its constants with `T`, the group of derivation-preserving automorphisms of `T` over
`L = F⟨q′⟩` is exactly the additive group `(differentialConstants F) ^ ι`, i.e. `G_a^r` with
`r = #ι`.

The existing `ScalarAdditiveDifferentialTorsor` computes the same group for `ι = Unit` under the
extra hypothesis that *every* element of the base is a constant.  The layers of a jet horizon sit
over `C⟨z⟩`, where `z` is the reduced (non-cylinder) part of the generic point, and that field
carries a nonzero derivation; so the constancy hypothesis has to go, and the rank has to be
arbitrary.  Both are removed here.
-/

open scoped Differential Polynomial

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {F T : Type*} [Field F] [Field T] [Algebra F T]
  [Differential F] [Differential T] [DifferentialAlgebra F T]

/-! ### The constant subfield of a differential field -/

/-- The subfield of constants of a differential field. -/
def differentialConstants (F : Type*) [Field F] [Differential F] : Subfield F where
  carrier := {c | c′ = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [Derivation.leibniz]
    simp [ha, hb]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    exact Derivation.map_one_eq_zero _
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add, ha, hb, add_zero]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    exact map_zero _
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_neg, ha, neg_zero]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rcases eq_or_ne a 0 with rfl | ha0
    · simp
    · have h1 : (a * a⁻¹)′ = 0 := by
        rw [mul_inv_cancel₀ ha0]; exact Derivation.map_one_eq_zero _
      rw [Derivation.leibniz] at h1
      simp only [smul_eq_mul, ha, mul_zero, add_zero] at h1
      exact (mul_eq_zero.mp h1).resolve_left ha0

@[simp]
theorem mem_differentialConstants_iff {c : F} :
    c ∈ differentialConstants F ↔ c′ = 0 := Iff.rfl

theorem deriv_coe_differentialConstants (c : differentialConstants F) : (c : F)′ = 0 := c.2

/-! ### The derivative field of a family -/

variable {ι : Type*}

/-- The differential field generated over `F` by the derivatives of a family: the lower layer of
one step of a derivative horizon. -/
def vectorDerivativeField (F : Type*) {T ι : Type*} [Field F] [Field T]
    [Algebra F T] [Differential T] (q : ι → T) : IntermediateField F T :=
  differentialAdjoin F (Set.range fun i => (q i)′)

omit [Differential F] [DifferentialAlgebra F T] in
theorem deriv_mem_vectorDerivativeField (q : ι → T) (i : ι) :
    (q i)′ ∈ vectorDerivativeField F q :=
  subset_differentialAdjoin F _ (Set.mem_range_self i)

omit [Differential F] [DifferentialAlgebra F T] in
theorem differentialJet_succ_mem_vectorDerivativeField (q : ι → T) (i : ι) (n : ℕ) :
    differentialJet (n + 1) (q i) ∈ vectorDerivativeField F q := by
  have h : differentialJet (n + 1) (q i) = differentialJet n ((q i)′) := by
    simpa using differentialJet_add n 1 (q i)
  rw [h]
  exact differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n

omit [Differential F] [DifferentialAlgebra F T] in
/-- **Exact additive reconstruction.**  The full differential field is generated *ordinarily* over
its derivative field by the family itself. -/
theorem vectorDerivativeField_adjoin_eq_top (q : ι → T)
    (hgen : differentialAdjoin F (Set.range q) = ⊤) :
    IntermediateField.adjoin (vectorDerivativeField F q) (Set.range q) = ⊤ := by
  let L : IntermediateField F T := vectorDerivativeField F q
  let A : IntermediateField L T := IntermediateField.adjoin L (Set.range q)
  let B : IntermediateField F T := A.restrictScalars F
  have hle : differentialAdjoin F (Set.range q) ≤ B := by
    rw [differentialAdjoin, IntermediateField.adjoin_le_iff]
    rintro w ⟨x, ⟨i, rfl⟩, n, rfl⟩
    rcases n with _ | n
    · have hmem : q i ∈ A :=
        IntermediateField.subset_adjoin L (Set.range q) (Set.mem_range_self i)
      have hz : differentialJet 0 (q i) = q i := by simp
      rw [hz]
      exact hmem
    · exact A.algebraMap_mem
        ⟨differentialJet (n + 1) (q i),
          differentialJet_succ_mem_vectorDerivativeField q i n⟩
  apply top_unique
  intro w _
  exact hle (by rw [hgen]; trivial)

omit [Differential F] [DifferentialAlgebra F T] in
/-- Automorphisms over the derivative field are determined by their values on the family. -/
theorem vectorDerivativeAlgEquiv_ext (q : ι → T)
    (hgen : differentialAdjoin F (Set.range q) = ⊤)
    {sigma tau : T ≃ₐ[vectorDerivativeField F q] T}
    (hqeq : ∀ i, sigma (q i) = tau (q i)) : sigma = tau := by
  let L : IntermediateField F T := vectorDerivativeField F q
  have htop : IntermediateField.adjoin L (Set.range q) = ⊤ :=
    vectorDerivativeField_adjoin_eq_top q hgen
  apply AlgEquiv.ext
  intro w
  have hw : w ∈ IntermediateField.adjoin L (Set.range q) := by rw [htop]; trivial
  apply IntermediateField.adjoin_induction L
    (s := Set.range q) (p := fun v _ => sigma v = tau v)
  · rintro v ⟨i, rfl⟩
    exact hqeq i
  · intro a
    exact (sigma.commutes a).trans (tau.commutes a).symm
  · intro a b _ _ ha hb
    rw [map_add, map_add, ha, hb]
  · intro a _ ha
    rw [map_inv₀, map_inv₀, ha]
  · intro a b _ _ ha hb
    rw [map_mul, map_mul, ha, hb]
  · exact hw

/-! ### Translation by a vector of base constants -/

private theorem vectorTranslation_data (q : ι → T)
    (hq : DifferentialIndependent F q)
    (hgen : differentialAdjoin F (Set.range q) = ⊤) (c : ι → F) :
    DifferentialIndependent F (fun i => q i + algebraMap F T (c i)) ∧
      differentialAdjoin F (Set.range fun i => q i + algebraMap F T (c i)) = ⊤ := by
  refine ⟨hq.addBase c, ?_⟩
  have heq := differentialAdjoin_addOfJetsInBase (F := F) q
    (fun i => algebraMap F T (c i))
    (by
      intro i n
      exact ⟨differentialJet n (c i), differentialJet_algebraMap_apply n (c i)⟩)
  rw [show (fun i => q i + algebraMap F T (c i)) =
      fun i => q i + (fun j => algebraMap F T (c j)) i from rfl, heq, hgen]

/-- Translation of a free differential family by a vector of base scalars, as a differential
`F`-automorphism.  Existence is stated so that the universal-property construction does not have
to be unfolded downstream. -/
theorem exists_vectorTranslationEquiv (q : ι → T)
    (hq : DifferentialIndependent F q)
    (hgen : differentialAdjoin F (Set.range q) = ⊤) (c : ι → F) :
    ∃ sigma : T ≃ₐ[F] T,
      (∀ i, sigma (q i) = q i + algebraMap F T (c i)) ∧
        ∀ z : T, sigma z′ = (sigma z)′ := by
  obtain ⟨hy, hytop⟩ := vectorTranslation_data q hq hgen c
  refine ⟨differentialIndependentTopAlgEquiv q
      (fun i => q i + algebraMap F T (c i)) hq hy hgen hytop, ?_, ?_⟩
  · intro i
    exact differentialIndependentTopAlgEquiv_apply q
      (fun i => q i + algebraMap F T (c i)) hq hy hgen hytop i
  · intro z
    exact differentialIndependentTopAlgEquiv_deriv q
      (fun i => q i + algebraMap F T (c i)) hq hy hgen hytop z

/-- Translation of a free differential family by a vector of base scalars. -/
def vectorTranslationEquiv (q : ι → T)
    (hq : DifferentialIndependent F q)
    (hgen : differentialAdjoin F (Set.range q) = ⊤) (c : ι → F) : T ≃ₐ[F] T :=
  (exists_vectorTranslationEquiv q hq hgen c).choose

@[simp]
theorem vectorTranslationEquiv_apply (q : ι → T)
    (hq : DifferentialIndependent F q)
    (hgen : differentialAdjoin F (Set.range q) = ⊤) (c : ι → F) (i : ι) :
    vectorTranslationEquiv q hq hgen c (q i) = q i + algebraMap F T (c i) :=
  (exists_vectorTranslationEquiv q hq hgen c).choose_spec.1 i

theorem vectorTranslationEquiv_deriv (q : ι → T)
    (hq : DifferentialIndependent F q)
    (hgen : differentialAdjoin F (Set.range q) = ⊤) (c : ι → F) (z : T) :
    vectorTranslationEquiv q hq hgen c z′ =
      (vectorTranslationEquiv q hq hgen c z)′ :=
  (exists_vectorTranslationEquiv q hq hgen c).choose_spec.2 z

/-- **Constant translation fixes the derivative layer.**  Only constancy of the translating vector
is used; the base `F` may carry a nonzero derivation. -/
theorem vectorTranslationEquiv_fixes_vectorDerivativeField (q : ι → T)
    (hq : DifferentialIndependent F q)
    (hgen : differentialAdjoin F (Set.range q) = ⊤) {c : ι → F}
    (hc : ∀ i, (c i)′ = 0) (z : vectorDerivativeField F q) :
    vectorTranslationEquiv q hq hgen c z.1 = z.1 := by
  let sigma := vectorTranslationEquiv q hq hgen c
  have hP : ∀ i, sigma ((q i)′) = (q i)′ := by
    intro i
    rw [vectorTranslationEquiv_deriv, vectorTranslationEquiv_apply, map_add,
      deriv_algebraMap, hc, map_zero, add_zero]
  have hjet : ∀ (i : ι) (n : ℕ),
      sigma (differentialJet n ((q i)′)) = differentialJet n ((q i)′) := by
    intro i n
    induction n with
    | zero => simpa using hP i
    | succ n ih =>
        rw [differentialJet_succ, vectorTranslationEquiv_deriv]
        exact congrArg Differential.deriv ih
  change sigma z.1 = z.1
  have hz : z.1 ∈ IntermediateField.adjoin F
      (differentialJetSet (Set.range fun i => (q i)′)) := z.2
  apply IntermediateField.adjoin_induction F
    (s := differentialJetSet (Set.range fun i => (q i)′))
    (p := fun w _ => sigma w = w)
  · rintro w ⟨v, ⟨i, rfl⟩, n, rfl⟩
    exact hjet i n
  · intro a
    exact sigma.commutes a
  · intro a b _ _ ha hb
    rw [map_add, ha, hb]
  · intro a _ ha
    rw [map_inv₀, ha]
  · intro a b _ _ ha hb
    rw [map_mul, ha, hb]
  · exact hz

/-- Translation by a vector of base constants, re-based over the derivative field. -/
def vectorConstTranslationEquiv (q : ι → T)
    (hq : DifferentialIndependent F q)
    (hgen : differentialAdjoin F (Set.range q) = ⊤)
    (c : ι → differentialConstants F) :
    T ≃ₐ[vectorDerivativeField F q] T where
  toRingEquiv :=
    (vectorTranslationEquiv q hq hgen (fun i => (c i : F))).toRingEquiv
  commutes' z := vectorTranslationEquiv_fixes_vectorDerivativeField q hq hgen
    (fun i => (c i).2) z

@[simp]
theorem vectorConstTranslationEquiv_apply (q : ι → T)
    (hq : DifferentialIndependent F q)
    (hgen : differentialAdjoin F (Set.range q) = ⊤)
    (c : ι → differentialConstants F) (i : ι) :
    vectorConstTranslationEquiv q hq hgen c (q i) = q i + algebraMap F T (c i : F) :=
  vectorTranslationEquiv_apply q hq hgen (fun i => (c i : F)) i

theorem vectorConstTranslationEquiv_deriv (q : ι → T)
    (hq : DifferentialIndependent F q)
    (hgen : differentialAdjoin F (Set.range q) = ⊤)
    (c : ι → differentialConstants F) (z : T) :
    vectorConstTranslationEquiv q hq hgen c z′ =
      (vectorConstTranslationEquiv q hq hgen c z)′ :=
  vectorTranslationEquiv_deriv q hq hgen (fun i => (c i : F)) z

theorem vectorConstTranslationEquiv_zero (q : ι → T)
    (hq : DifferentialIndependent F q)
    (hgen : differentialAdjoin F (Set.range q) = ⊤) :
    vectorConstTranslationEquiv q hq hgen 0 = 1 := by
  apply vectorDerivativeAlgEquiv_ext q hgen
  intro i
  rw [vectorConstTranslationEquiv_apply]
  simp

theorem vectorConstTranslationEquiv_add (q : ι → T)
    (hq : DifferentialIndependent F q)
    (hgen : differentialAdjoin F (Set.range q) = ⊤)
    (c d : ι → differentialConstants F) :
    vectorConstTranslationEquiv q hq hgen (c + d) =
      vectorConstTranslationEquiv q hq hgen c *
        vectorConstTranslationEquiv q hq hgen d := by
  apply vectorDerivativeAlgEquiv_ext q hgen
  intro i
  simp only [AlgEquiv.mul_apply, vectorConstTranslationEquiv_apply]
  have hdL : algebraMap F T (d i : F) ∈ vectorDerivativeField F q :=
    (vectorDerivativeField F q).algebraMap_mem (d i : F)
  have hfixd : vectorConstTranslationEquiv q hq hgen c (algebraMap F T (d i : F)) =
      algebraMap F T (d i : F) :=
    (vectorConstTranslationEquiv q hq hgen c).commutes
      ⟨algebraMap F T (d i : F), hdL⟩
  have hcd : (((c + d) i : differentialConstants F) : F) = (c i : F) + (d i : F) := rfl
  calc
    q i + algebraMap F T (((c + d) i : differentialConstants F) : F) =
        (q i + algebraMap F T (c i : F)) + algebraMap F T (d i : F) := by
          rw [hcd, map_add]; abel
    _ = vectorConstTranslationEquiv q hq hgen c (q i) +
        vectorConstTranslationEquiv q hq hgen c (algebraMap F T (d i : F)) := by
          rw [vectorConstTranslationEquiv_apply, hfixd]
    _ = vectorConstTranslationEquiv q hq hgen c (q i + algebraMap F T (d i : F)) := by
          rw [map_add]

/-- **The additive gauge action of one horizon layer.**  The vector group of base constants acts on
the layer by translating the forgotten jets. -/
def vectorConstTranslationAction (q : ι → T)
    (hq : DifferentialIndependent F q)
    (hgen : differentialAdjoin F (Set.range q) = ⊤) :
    Multiplicative (ι → differentialConstants F) →*
      derivationPreservingAut (vectorDerivativeField F q) T where
  toFun c := ⟨vectorConstTranslationEquiv q hq hgen c.toAdd,
    vectorConstTranslationEquiv_deriv q hq hgen c.toAdd⟩
  map_one' := Subtype.ext (vectorConstTranslationEquiv_zero q hq hgen)
  map_mul' c d := Subtype.ext (vectorConstTranslationEquiv_add q hq hgen c.toAdd d.toAdd)

@[simp]
theorem vectorConstTranslationAction_apply (q : ι → T)
    (hq : DifferentialIndependent F q)
    (hgen : differentialAdjoin F (Set.range q) = ⊤)
    (c : Multiplicative (ι → differentialConstants F)) (i : ι) :
    (vectorConstTranslationAction q hq hgen c).1 (q i) =
      q i + algebraMap F T ((c.toAdd i : differentialConstants F) : F) :=
  vectorConstTranslationEquiv_apply q hq hgen c.toAdd i

/-- The layer gauge action is faithful. -/
theorem vectorConstTranslationAction_injective (q : ι → T)
    (hq : DifferentialIndependent F q)
    (hgen : differentialAdjoin F (Set.range q) = ⊤) :
    Function.Injective (vectorConstTranslationAction q hq hgen) := by
  intro c d hcd
  apply Multiplicative.toAdd.injective
  funext i
  have hqeq := congrArg
    (fun sigma : derivationPreservingAut (vectorDerivativeField F q) T => sigma.1 (q i)) hcd
  have hcoeff : algebraMap F T ((c.toAdd i : differentialConstants F) : F) =
      algebraMap F T ((d.toAdd i : differentialConstants F) : F) := by
    apply add_left_cancel
    simpa only [vectorConstTranslationAction_apply] using hqeq
  exact Subtype.ext ((algebraMap F T).injective hcoeff)

/-- **Surjectivity of the layer gauge action.**  Every derivation-preserving automorphism of the
layer over the derivative field is translation by a vector of constants of the base. -/
theorem vectorConstTranslationAction_surjective (q : ι → T)
    (hq : DifferentialIndependent F q)
    (hgen : differentialAdjoin F (Set.range q) = ⊤)
    [Differential.ContainConstants F T] :
    Function.Surjective (vectorConstTranslationAction q hq hgen) := by
  classical
  intro sigma
  have hdisp : ∀ i : ι, ∃ c : differentialConstants F,
      sigma.1 (q i) = q i + algebraMap F T (c : F) := by
    intro i
    have hfixP : sigma.1 ((q i)′) = (q i)′ :=
      sigma.1.commutes ⟨(q i)′, deriv_mem_vectorDerivativeField q i⟩
    have hdiffDeriv : (sigma.1 (q i) - q i)′ = 0 := by
      rw [map_sub, ← sigma.2 (q i), hfixP, sub_self]
    obtain ⟨c, hc⟩ := mem_range_of_deriv_eq_zero F hdiffDeriv
    have hcconst : c′ = 0 := by
      have h1 : algebraMap F T (c′) = algebraMap F T (0 : F) := by
        rw [← deriv_algebraMap, hc, hdiffDeriv, map_zero]
      exact (algebraMap F T).injective h1
    exact ⟨⟨c, hcconst⟩, by rw [hc]; ring⟩
  choose c hc using hdisp
  refine ⟨Multiplicative.ofAdd c, ?_⟩
  apply Subtype.ext
  apply vectorDerivativeAlgEquiv_ext q hgen
  intro i
  simp only [vectorConstTranslationAction_apply, toAdd_ofAdd]
  exact (hc i).symm

/-- **The successive-torsor law.**  For a differentially independent family `q` generating `T` over
a differential base field `F` which shares its constants with `T`, the group of
derivation-preserving automorphisms of `T` over the derivative field `F⟨q′⟩` is exactly the
additive group of constant vectors — the group `G_a^r` of the card's equation (7), with `r` the
number of cylinder coordinates.  No constancy of the base is assumed. -/
def vectorAdditiveGaloisGroupEquiv (q : ι → T)
    (hq : DifferentialIndependent F q)
    (hgen : differentialAdjoin F (Set.range q) = ⊤)
    [Differential.ContainConstants F T] :
    Multiplicative (ι → differentialConstants F) ≃*
      derivationPreservingAut (vectorDerivativeField F q) T :=
  MulEquiv.ofBijective (vectorConstTranslationAction q hq hgen)
    ⟨vectorConstTranslationAction_injective q hq hgen,
      vectorConstTranslationAction_surjective q hq hgen⟩

/-! ### The group of the layer, named -/

variable {C : Type*} [Field C] [Algebra C F] [Differential C] [DifferentialAlgebra C F]

/-- **Constants do not grow.**  If `F` shares its constants with a field of constants `C`, the
constant subfield of `F` is exactly the image of `C`. -/
theorem coe_differentialConstants_eq_range (hC : ∀ c : C, c′ = 0)
    [Differential.ContainConstants C F] :
    ((differentialConstants F : Subfield F) : Set F) = Set.range (algebraMap C F) := by
  ext x
  constructor
  · intro hx
    exact mem_range_of_deriv_eq_zero C (by simpa using hx)
  · rintro ⟨c, rfl⟩
    show (algebraMap C F c)′ = 0
    rw [deriv_algebraMap, hC, map_zero]

theorem algebraMap_mem_differentialConstants (hC : ∀ c : C, c′ = 0) (c : C) :
    algebraMap C F c ∈ differentialConstants F := by
  show (algebraMap C F c)′ = 0
  rw [deriv_algebraMap, hC, map_zero]

/-- The field of constants of the base, identified with the constant subfield of the base. -/
def constantFieldRingEquiv (hC : ∀ c : C, c′ = 0)
    [Differential.ContainConstants C F] :
    C ≃+* differentialConstants F :=
  RingEquiv.ofBijective
    ((algebraMap C F).codRestrict (differentialConstants F)
      (algebraMap_mem_differentialConstants hC))
    ⟨fun a b hab => (algebraMap C F).injective (congrArg Subtype.val hab),
      by
        rintro ⟨x, hx⟩
        have hxr : x ∈ Set.range (algebraMap C F) := by
          rw [← coe_differentialConstants_eq_range (C := C) hC]
          exact hx
        obtain ⟨c, rfl⟩ := hxr
        exact ⟨c, rfl⟩⟩

/-- **The successive-torsor law with its group named.**  For a differentially independent family
`q` generating `T` over `F`, with `C` a field of constants sharing its constants with `F` and `F`
sharing its constants with `T`, the derivation-preserving automorphism group of one horizon layer
is exactly the additive group `G_a^ι(C)`.

With `q = δ^j a` the cylinder coordinates of a differential-generic point, `F = C⟨z⟩` its reduced
part and `T = H_j`, this is equation (7): the layer `H_j / H_{j+1}` is the additive torsor of
`δ X = δ^{j+1} a` with differential Galois group `G_a^r`, `r` the cylinder dimension. -/
def vectorAdditiveGaloisGroupEquivConstantField (q : ι → T)
    (hq : DifferentialIndependent F q)
    (hgen : differentialAdjoin F (Set.range q) = ⊤)
    (hC : ∀ c : C, c′ = 0)
    [Differential.ContainConstants C F] [Differential.ContainConstants F T] :
    Multiplicative (ι → C) ≃*
      derivationPreservingAut (vectorDerivativeField F q) T :=
  (AddEquiv.toMultiplicative
      (AddEquiv.piCongrRight fun _ : ι => (constantFieldRingEquiv (F := F) hC).toAddEquiv)).trans
    (vectorAdditiveGaloisGroupEquiv q hq hgen)


end

end GaloisForLFunctions.HTGeometry
