import GaloisForLFunctions.HTGeometry.FaceLayerDescendingUnion

/-!
# Translate families versus defect families

A translation orbit `{sigma_c F}` and the family consisting of `F` together with its displacements
`sigma_c F - F` differ by an invertible *shear* of the free differential polynomial ring: adding the
distinguished jet variable to every other jet variable of the same order.  Differential
independence is therefore the same for both.

* **`optionShearAlgHom`** — the shear substitution of the free jet polynomial ring, with inverse the
  opposite shear;
* **`differentialIndependent_option_add_base`** and **`..._iff`** — a family `(v, (v + x i))` is
  differentially independent exactly when `(v, (x i))` is.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

/-! ## The shear substitution -/

/-- The shear substitution of the free jet polynomial ring: it adds `eps` times the distinguished
jet variable to every other jet variable of the same order. -/
def optionShearAlgHom {B κ : Type*} [CommRing B] (eps : B) :
    MvPolynomial (Option κ × ℕ) B →ₐ[B] MvPolynomial (Option κ × ℕ) B :=
  MvPolynomial.aeval fun p : Option κ × ℕ =>
    match p.1 with
    | none => MvPolynomial.X p
    | some _ =>
        MvPolynomial.X p + MvPolynomial.C eps * MvPolynomial.X ((none : Option κ), p.2)

@[simp] theorem optionShearAlgHom_X_none {B κ : Type*} [CommRing B] (eps : B) (n : ℕ) :
    optionShearAlgHom (κ := κ) eps (MvPolynomial.X ((none : Option κ), n)) =
      MvPolynomial.X ((none : Option κ), n) := by
  simp [optionShearAlgHom]

@[simp] theorem optionShearAlgHom_X_some {B κ : Type*} [CommRing B] (eps : B) (i : κ) (n : ℕ) :
    optionShearAlgHom eps (MvPolynomial.X ((some i, n) : Option κ × ℕ)) =
      MvPolynomial.X ((some i, n) : Option κ × ℕ) +
        MvPolynomial.C eps * MvPolynomial.X ((none : Option κ), n) := by
  simp [optionShearAlgHom]

@[simp] theorem optionShearAlgHom_C {B κ : Type*} [CommRing B] (eps c : B) :
    optionShearAlgHom (κ := κ) eps (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [optionShearAlgHom]

theorem optionShearAlgHom_comp {B κ : Type*} [CommRing B] (eps : B) :
    (optionShearAlgHom (κ := κ) (-eps)).comp (optionShearAlgHom (κ := κ) eps) =
      AlgHom.id B (MvPolynomial (Option κ × ℕ) B) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨o, n⟩
  cases o with
  | none => simp
  | some i =>
      rw [AlgHom.comp_apply, optionShearAlgHom_X_some, map_add, map_mul,
        optionShearAlgHom_C, optionShearAlgHom_X_some, optionShearAlgHom_X_none,
        AlgHom.id_apply, map_neg]
      ring

theorem optionShearAlgHom_injective {B κ : Type*} [CommRing B] (eps : B) :
    Function.Injective (optionShearAlgHom (κ := κ) eps) := by
  intro p q hpq
  have hp : optionShearAlgHom (κ := κ) (-eps) (optionShearAlgHom (κ := κ) eps p) = p := by
    have h := optionShearAlgHom_comp (κ := κ) eps
    calc optionShearAlgHom (κ := κ) (-eps) (optionShearAlgHom (κ := κ) eps p)
        = ((optionShearAlgHom (κ := κ) (-eps)).comp (optionShearAlgHom (κ := κ) eps)) p := rfl
      _ = AlgHom.id B (MvPolynomial (Option κ × ℕ) B) p := by rw [h]
      _ = p := rfl
  have hq : optionShearAlgHom (κ := κ) (-eps) (optionShearAlgHom (κ := κ) eps q) = q := by
    have h := optionShearAlgHom_comp (κ := κ) eps
    calc optionShearAlgHom (κ := κ) (-eps) (optionShearAlgHom (κ := κ) eps q)
        = ((optionShearAlgHom (κ := κ) (-eps)).comp (optionShearAlgHom (κ := κ) eps)) q := rfl
      _ = AlgHom.id B (MvPolynomial (Option κ × ℕ) B) q := by rw [h]
      _ = q := rfl
  rw [← hp, ← hq, hpq]

/-! ## Independence of a translated family -/

/-- **Adding the distinguished member preserves differential independence.**  If `v` together with
a family `x` is differentially independent, so is `v` together with the translated family
`v + x i`. -/
theorem differentialIndependent_option_add_base
    {B L κ : Type*} [Field B] [Field L] [Algebra B L] [Differential L]
    (v : L) (x : κ → L)
    (h : DifferentialIndependent B (fun o : Option κ => o.elim v x)) :
    DifferentialIndependent B (fun o : Option κ => o.elim v (fun i => v + x i)) := by
  classical
  unfold DifferentialIndependent at h ⊢
  rw [algebraicIndependent_iff] at h ⊢
  intro p hp
  have hcomp : (MvPolynomial.aeval (R := B)
        (fun q : Option κ × ℕ =>
          differentialJet q.2 ((fun o : Option κ => o.elim v (fun i => v + x i)) q.1))) =
      (MvPolynomial.aeval (R := B)
        (fun q : Option κ × ℕ =>
          differentialJet q.2 ((fun o : Option κ => o.elim v x) q.1))).comp
        (optionShearAlgHom (1 : B)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨o, n⟩
    cases o with
    | none => simp
    | some i =>
        rw [AlgHom.comp_apply, optionShearAlgHom_X_some]
        simp only [map_add, MvPolynomial.aeval_X, Option.elim, map_one, one_mul]
        rw [differentialJet_additive]
        ring
  rw [hcomp] at hp
  have hzero : optionShearAlgHom (κ := κ) (1 : B) p = 0 := h _ hp
  exact optionShearAlgHom_injective (κ := κ) (1 : B) (by simpa using hzero)

/-- **Subtracting the distinguished member preserves differential independence.** -/
theorem differentialIndependent_option_sub_base
    {B L κ : Type*} [Field B] [Field L] [Algebra B L] [Differential L]
    (v : L) (x : κ → L)
    (h : DifferentialIndependent B (fun o : Option κ => o.elim v x)) :
    DifferentialIndependent B (fun o : Option κ => o.elim v (fun i => x i - v)) := by
  classical
  unfold DifferentialIndependent at h ⊢
  rw [algebraicIndependent_iff] at h ⊢
  intro p hp
  have hcomp : (MvPolynomial.aeval (R := B)
        (fun q : Option κ × ℕ =>
          differentialJet q.2 ((fun o : Option κ => o.elim v (fun i => x i - v)) q.1))) =
      (MvPolynomial.aeval (R := B)
        (fun q : Option κ × ℕ =>
          differentialJet q.2 ((fun o : Option κ => o.elim v x) q.1))).comp
        (optionShearAlgHom (-1 : B)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨o, n⟩
    cases o with
    | none => simp
    | some i =>
        rw [AlgHom.comp_apply, optionShearAlgHom_X_some]
        simp only [map_add, map_mul, MvPolynomial.aeval_X, Option.elim, map_neg, map_one]
        rw [differentialJet_sub]
        ring
  rw [hcomp] at hp
  have hzero : optionShearAlgHom (κ := κ) (-1 : B) p = 0 := h _ hp
  exact optionShearAlgHom_injective (κ := κ) (-1 : B) (by simpa using hzero)

/-- **A family is independent together with its distinguished member exactly when its translates
are.** -/
theorem differentialIndependent_option_add_base_iff
    {B L κ : Type*} [Field B] [Field L] [Algebra B L] [Differential L]
    (v : L) (x : κ → L) :
    DifferentialIndependent B (fun o : Option κ => o.elim v (fun i => v + x i)) ↔
      DifferentialIndependent B (fun o : Option κ => o.elim v x) := by
  constructor
  · intro h
    have h' := differentialIndependent_option_sub_base (B := B) v (fun i => v + x i) h
    have hfun : (fun o : Option κ => o.elim v (fun i => (v + x i) - v)) =
        fun o : Option κ => o.elim v x := by
      funext o
      cases o with
      | none => rfl
      | some i => simp
    rwa [hfun] at h'
  · exact differentialIndependent_option_add_base v x

/-! ## From an independent family to its independent range -/

/-- **A differentially independent family has a differentially independent range.**  A section of
the parametrization is injective, so the value family is an injectively indexed subfamily. -/
theorem diffIndepOn_range_of_differentialIndependent
    {B L ι : Type*} [Field B] [Field L] [Algebra B L] [Differential L]
    {f : ι → L} (h : DifferentialIndependent B f) :
    DiffIndepOn B (Set.range f) := by
  classical
  have hval : (Subtype.val : ↥(Set.range f) → L) = f ∘ Set.rangeSplitting f := by
    funext y
    exact (Set.apply_rangeSplitting f y).symm
  unfold DiffIndepOn
  rw [hval]
  exact h.comp (Set.rangeSplitting f) (Set.rangeSplitting_injective f)

/-- A hypertranscendental element over a generated differential field does not belong to the
generating set. -/
theorem notMem_of_hypertranscendentalOver_differentialAdjoin
    {k K : Type*} [Field k] [Field K] [Algebra k K] [Differential K]
    {B : Set K} {x : K}
    (h : HypertranscendentalOver ↥(differentialAdjoin k B) x) : x ∉ B := by
  intro hxB
  exact h (HTGeometry.differentialAlgebraicOver_algebraMap
    (E := K) (⟨x, subset_differentialAdjoin k B hxB⟩ : ↥(differentialAdjoin k B)))

/-! ## The set-level shear -/

/-- **Translating a set by an independent extra member preserves independence.**  If `insert v S`
is differentially independent then so is `insert v ((v + ·) '' S)`, the translation orbit shape. -/
theorem diffIndepOn_insert_translate
    {B L : Type*} [Field B] [Field L] [Algebra B L] [Differential L]
    (v : L) (S : Set L) (hv : v ∉ S) (h : DiffIndepOn B (insert v S)) :
    DiffIndepOn B (insert v ((fun s => v + s) '' S)) := by
  classical
  let incl : Option ↥S → ↥(insert v S) := fun o =>
    o.elim ⟨v, Set.mem_insert v S⟩ fun s => ⟨(s : L), Set.mem_insert_of_mem v s.2⟩
  have hinj : Function.Injective incl := by
    rintro (_ | a) (_ | b) hab
    · rfl
    · exfalso
      have hval : v = (b : L) := congrArg Subtype.val hab
      exact hv (by rw [hval]; exact b.2)
    · exfalso
      have hval : (a : L) = v := congrArg Subtype.val hab
      exact hv (by rw [← hval]; exact a.2)
    · have hval : (a : L) = (b : L) :=
        congrArg (fun w : ↥(insert v S) => (w : L)) hab
      exact congrArg some (Subtype.ext hval)
  have hfun : (Subtype.val : ↥(insert v S) → L) ∘ incl =
      fun o : Option ↥S => o.elim v fun s => (s : L) := by
    funext o
    cases o with
    | none => rfl
    | some s => rfl
  have hfam : DifferentialIndependent B
      (fun o : Option ↥S => o.elim v fun s => (s : L)) := by
    have hcomp := h.comp incl hinj
    rwa [hfun] at hcomp
  have hshear := differentialIndependent_option_add_base v (fun s : ↥S => (s : L)) hfam
  have hrange := diffIndepOn_range_of_differentialIndependent hshear
  have hset : Set.range (fun o : Option ↥S => o.elim v fun s => v + (s : L)) =
      insert v ((fun s => v + s) '' S) := by
    ext y
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | none => exact Set.mem_insert _ _
      | some s => exact Set.mem_insert_of_mem _ ⟨(s : L), s.2, rfl⟩
    · rintro (rfl | ⟨s, hs, rfl⟩)
      · exact ⟨none, rfl⟩
      · exact ⟨some ⟨s, hs⟩, rfl⟩
  rwa [hset] at hrange

end

end GaloisForLFunctions
