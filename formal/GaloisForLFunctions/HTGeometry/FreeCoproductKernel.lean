import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# The kernel of a map of free objects induced by a map of index sets is free

An object is *free over* a chosen object `R` when it is a coproduct of copies of `R`.  A function
between index types induces a map between such coproducts, and the kernel of that map is again free:
choosing one preimage in every nonempty fibre splits the coproduct over the source into the copies
sitting over the chosen preimages and the differences of the remaining ones with their chosen
partner.  The splitting is explicit, so no exactness of coproducts is used anywhere.

This is the algebra behind the statement that the first homology of an order complex covered by
contractible pieces is free: the Mayer--Vietoris connecting map identifies it with such a kernel.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- An object is free over `R` when it is a coproduct of copies of `R`. -/
def IsFreeOver (R Z : C) : Prop := ∃ B : Type w, Nonempty (Z ≅ ∐ fun _ : B => R)

omit [Preadditive C] in
theorem IsFreeOver.of_iso {R Z Z' : C} (h : IsFreeOver.{v, u, w} R Z) (e : Z' ≅ Z) :
    IsFreeOver.{v, u, w} R Z' := by
  obtain ⟨B, ⟨f⟩⟩ := h
  exact ⟨B, ⟨e ≪≫ f⟩⟩

omit [Preadditive C] in
theorem isFreeOver_sigma (R : C) (B : Type w) : IsFreeOver.{v, u, w} R (∐ fun _ : B => R) :=
  ⟨B, ⟨Iso.refl _⟩⟩

/-! ## Maps of coproducts induced by maps of index types -/

variable {A B : Type w} (u : A → B) (R : C)

/-- The map of coproducts of copies of `R` induced by a function of index types. -/
noncomputable def sigmaMapFun : (∐ fun _ : A => R) ⟶ (∐ fun _ : B => R) :=
  Sigma.desc fun a => Sigma.ι (fun _ : B => R) (u a)

omit [Preadditive C] in
@[reassoc (attr := simp)]
theorem ι_sigmaMapFun (a : A) :
    Sigma.ι (fun _ : A => R) a ≫ sigmaMapFun u R = Sigma.ι (fun _ : B => R) (u a) :=
  Sigma.ι_desc _ _

omit [Preadditive C] in
theorem sigmaMapFun_comp {D : Type w} (t : B → D) :
    sigmaMapFun u R ≫ sigmaMapFun t R = sigmaMapFun (t ∘ u) R := by
  refine Sigma.hom_ext _ _ fun a => ?_
  rw [← Category.assoc, ι_sigmaMapFun, ι_sigmaMapFun, ι_sigmaMapFun]
  rfl

omit [Preadditive C] in
theorem sigmaMapFun_id : sigmaMapFun (id : A → A) R = 𝟙 _ := by
  refine Sigma.hom_ext _ _ fun a => ?_
  rw [ι_sigmaMapFun, Category.comp_id]
  rfl

/-! ## The splitting attached to a choice of preimages -/

/-- A chosen preimage of an element of the image of `u`. -/
noncomputable def sigmaPick (b : {b : B // ∃ a, u a = b}) : A := b.2.choose

theorem u_sigmaPick (b : {b : B // ∃ a, u a = b}) : u (sigmaPick u b) = (b : B) := b.2.choose_spec

/-- The chosen preimage of the value of an element. -/
noncomputable def sigmaSection (a : A) : A := sigmaPick u ⟨u a, ⟨a, rfl⟩⟩

variable {u}

theorem u_sigmaSection (a : A) : u (sigmaSection u a) = u a := u_sigmaPick u _

theorem sigmaSection_congr {a a' : A} (h : u a = u a') : sigmaSection u a = sigmaSection u a' :=
  congrArg (sigmaPick u) (Subtype.ext h)

theorem sigmaSection_idem (a : A) : sigmaSection u (sigmaSection u a) = sigmaSection u a :=
  sigmaSection_congr (u_sigmaSection a)

/-- The index set of the kernel: the elements that are not the chosen preimage of their value. -/
abbrev sigmaKerIndex (u : A → B) : Type w := {a : A // sigmaSection u a ≠ a}

variable (u)

/-- The inclusion of the kernel index into the source: an element minus the chosen preimage of its
value. -/
noncomputable def sigmaKerIncl : (∐ fun _ : sigmaKerIndex u => R) ⟶ (∐ fun _ : A => R) :=
  Sigma.desc fun k =>
    Sigma.ι (fun _ : A => R) (k : A) - Sigma.ι (fun _ : A => R) (sigmaSection u (k : A))

open scoped Classical in
/-- The retraction onto the kernel index: forget the chosen preimages. -/
noncomputable def sigmaKerRetract : (∐ fun _ : A => R) ⟶ (∐ fun _ : sigmaKerIndex u => R) :=
  Sigma.desc fun a =>
    if h : sigmaSection u a ≠ a then Sigma.ι (fun _ : sigmaKerIndex u => R) ⟨a, h⟩ else 0

/-- The projection onto the chosen preimages, read inside the source. -/
noncomputable def sigmaKerProj : (∐ fun _ : A => R) ⟶ (∐ fun _ : A => R) :=
  Sigma.desc fun a => Sigma.ι (fun _ : A => R) (sigmaSection u a)

open scoped Classical in
/-- Send a value to its chosen preimage. -/
noncomputable def sigmaChosen : (∐ fun _ : B => R) ⟶ (∐ fun _ : A => R) :=
  Sigma.desc fun b =>
    if h : ∃ a, u a = b then Sigma.ι (fun _ : A => R) (sigmaPick u ⟨b, h⟩) else 0

@[reassoc]
theorem ι_sigmaKerIncl (k : sigmaKerIndex u) :
    Sigma.ι (fun _ : sigmaKerIndex u => R) k ≫ sigmaKerIncl u R
      = Sigma.ι (fun _ : A => R) (k : A)
        - Sigma.ι (fun _ : A => R) (sigmaSection u (k : A)) :=
  Sigma.ι_desc _ _

@[reassoc]
theorem ι_sigmaKerRetract_of_ne (a : A) (h : sigmaSection u a ≠ a) :
    Sigma.ι (fun _ : A => R) a ≫ sigmaKerRetract u R
      = Sigma.ι (fun _ : sigmaKerIndex u => R) ⟨a, h⟩ := by
  classical
  rw [sigmaKerRetract, Sigma.ι_desc, dif_pos h]

@[reassoc]
theorem ι_sigmaKerRetract_of_eq (a : A) (h : sigmaSection u a = a) :
    Sigma.ι (fun _ : A => R) a ≫ sigmaKerRetract u R = 0 := by
  classical
  rw [sigmaKerRetract, Sigma.ι_desc, dif_neg (by simpa using h)]

omit [Preadditive C] in
@[reassoc]
theorem ι_sigmaKerProj (a : A) :
    Sigma.ι (fun _ : A => R) a ≫ sigmaKerProj u R
      = Sigma.ι (fun _ : A => R) (sigmaSection u a) :=
  Sigma.ι_desc _ _

theorem sigmaKerIncl_comp_sigmaKerRetract : sigmaKerIncl u R ≫ sigmaKerRetract u R = 𝟙 _ := by
  refine Sigma.hom_ext _ _ fun k => ?_
  rw [← Category.assoc, ι_sigmaKerIncl, Preadditive.sub_comp, Category.comp_id,
    ι_sigmaKerRetract_of_ne u R (k : A) k.2,
    ι_sigmaKerRetract_of_eq u R (sigmaSection u (k : A)) (sigmaSection_idem (k : A)), sub_zero]

theorem sigmaKerRetract_comp_sigmaKerIncl_add_proj :
    sigmaKerRetract u R ≫ sigmaKerIncl u R + sigmaKerProj u R = 𝟙 _ := by
  refine Sigma.hom_ext _ _ fun a => ?_
  rw [Preadditive.comp_add, Category.comp_id, ← Category.assoc, ι_sigmaKerProj]
  by_cases h : sigmaSection u a = a
  · rw [ι_sigmaKerRetract_of_eq u R a h, Limits.zero_comp, zero_add, h]
  · rw [ι_sigmaKerRetract_of_ne u R a h, ι_sigmaKerIncl, sub_add_cancel]

theorem sigmaKerIncl_comp_sigmaMapFun : sigmaKerIncl u R ≫ sigmaMapFun u R = 0 := by
  refine Sigma.hom_ext _ _ fun k => ?_
  rw [← Category.assoc, ι_sigmaKerIncl, Preadditive.sub_comp, ι_sigmaMapFun, ι_sigmaMapFun,
    u_sigmaSection (u := u) (k : A), sub_self, Limits.comp_zero]

/-- The projection onto the chosen preimages factors through the map itself. -/
theorem sigmaMapFun_comp_sigmaChosen : sigmaMapFun u R ≫ sigmaChosen u R = sigmaKerProj u R := by
  classical
  refine Sigma.hom_ext _ _ fun a => ?_
  rw [← Category.assoc, ι_sigmaMapFun, sigmaChosen, Sigma.ι_desc, dif_pos ⟨a, rfl⟩,
    ι_sigmaKerProj, sigmaSection]

/-- **The inclusion of the kernel index is a kernel of the induced map.** -/
noncomputable def isLimitKernelForkSigmaKerIncl :
    IsLimit (KernelFork.ofι (sigmaKerIncl u R) (sigmaKerIncl_comp_sigmaMapFun u R)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {T} t ht => t ≫ sigmaKerRetract u R)
    (fun {T} t ht => by
      have hproj : t ≫ sigmaKerProj u R = 0 := by
        rw [← sigmaMapFun_comp_sigmaChosen u R, ← Category.assoc, ht, Limits.zero_comp]
      have := congrArg (fun m : (∐ fun _ : A => R) ⟶ (∐ fun _ : A => R) => t ≫ m)
        (sigmaKerRetract_comp_sigmaKerIncl_add_proj u R)
      simp only [Preadditive.comp_add, Category.comp_id, ← Category.assoc, hproj, add_zero] at this
      exact this)
    (fun {T} t ht m hm => by
      have hmono : Mono (sigmaKerIncl u R) :=
        ⟨fun {_} g h heq => by
          have := congrArg (fun x => x ≫ sigmaKerRetract u R) heq
          simpa only [Category.assoc, sigmaKerIncl_comp_sigmaKerRetract, Category.comp_id]
            using this⟩
      rw [← hm, Category.assoc, sigmaKerIncl_comp_sigmaKerRetract, Category.comp_id])

/-- **The kernel of a map induced by a function of index types, with its index set.** -/
noncomputable def kernelIsoSigmaKerIndex {Z : C} (k : Z ⟶ ∐ fun _ : A => R)
    (w : k ≫ sigmaMapFun u R = 0) (hk : IsLimit (KernelFork.ofι k w)) :
    Z ≅ ∐ fun _ : sigmaKerIndex u => R :=
  IsLimit.conePointUniqueUpToIso hk (isLimitKernelForkSigmaKerIncl u R)

/-- **The kernel of a map induced by a function of index types is free.**  Any object equipped with a
kernel structure for that map is a coproduct of copies of `R`. -/
theorem isFreeOver_of_isLimit_kernelFork {Z : C} (k : Z ⟶ ∐ fun _ : A => R)
    (w : k ≫ sigmaMapFun u R = 0) (hk : IsLimit (KernelFork.ofι k w)) :
    IsFreeOver.{v, u, w} R Z :=
  ⟨sigmaKerIndex u, ⟨kernelIsoSigmaKerIndex u R k w hk⟩⟩

omit [Preadditive C] [HasCoproducts C] in
/-- **A two-element source over a one-element target leaves a one-element kernel index.** -/
theorem nonempty_unique_sigmaKerIndex {A B : Type w} (u : A → B) [Subsingleton B] {a₀ a₁ : A}
    (hne : a₀ ≠ a₁) (hall : ∀ a : A, a = a₀ ∨ a = a₁) : Nonempty (Unique (sigmaKerIndex u)) := by
  have hsec : ∀ a : A, sigmaSection u a = sigmaSection u a₀ :=
    fun a => sigmaSection_congr (Subsingleton.elim (u a) (u a₀))
  rcases hall (sigmaSection u a₀) with h | h
  · refine ⟨⟨⟨⟨a₁, ?_⟩⟩, ?_⟩⟩
    · rw [hsec a₁, h]
      exact hne
    · rintro ⟨a, ha⟩
      rcases hall a with rfl | rfl
      · exact absurd h ha
      · rfl
  · refine ⟨⟨⟨⟨a₀, ?_⟩⟩, ?_⟩⟩
    · rw [h]
      exact fun hcon => hne hcon.symm
    · rintro ⟨a, ha⟩
      rcases hall a with rfl | rfl
      · rfl
      · exact absurd ((hsec a).trans h) ha

/-! ## Reindexing -/

omit [Preadditive C] in
/-- A bijection of index types gives an isomorphism of coproducts. -/
noncomputable def sigmaIsoOfEquiv {A B : Type w} (e : A ≃ B) (R : C) :
    (∐ fun _ : A => R) ≅ (∐ fun _ : B => R) where
  hom := sigmaMapFun e R
  inv := sigmaMapFun e.symm R
  hom_inv_id := by
    rw [sigmaMapFun_comp, ← sigmaMapFun_id R]
    exact congrArg (fun t => sigmaMapFun t R) (funext fun a => e.symm_apply_apply a)
  inv_hom_id := by
    rw [sigmaMapFun_comp, ← sigmaMapFun_id R]
    exact congrArg (fun t => sigmaMapFun t R) (funext fun b => e.apply_symm_apply b)

omit [Preadditive C] in
/-- A coproduct of copies of `R` over a one-element index is `R`. -/
noncomputable def sigmaUniqueIso {A : Type w} [Unique A] (R : C) :
    (∐ fun _ : A => R) ≅ R where
  hom := Sigma.desc fun _ => 𝟙 R
  inv := Sigma.ι (fun _ : A => R) default
  hom_inv_id := by
    refine Sigma.hom_ext _ _ fun a => ?_
    rw [← Category.assoc, Sigma.ι_desc, Category.id_comp, Category.comp_id, Unique.eq_default a]
  inv_hom_id := by rw [Sigma.ι_desc]

end GaloisForLFunctions.HTGeometry
