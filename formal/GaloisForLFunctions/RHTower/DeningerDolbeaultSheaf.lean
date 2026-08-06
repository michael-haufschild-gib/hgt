import GaloisForLFunctions.RHTower.DeningerDomainSpace

/-!
# The sheaves of smooth `(0,q)`-forms on an open subset of `ℂ^n`

A section of the sheaf of smooth `(0,q)`-forms over an open set of the domain is a family of
coefficients indexed by the sets of `q` coordinate directions which, near every point, agrees with a
globally smooth form on `ℂ^n`.  Stating smoothness through a global model rather than through local
differentiability is what makes the whole Dolbeault theory of the corpus — which is written for
globally smooth forms — directly usable: the differential, its square, and the local and global
solvability of `∂̄ u = f` all transfer verbatim.

* `RHTower.DeningerFormPred` : the local predicate cutting out the smooth forms of a given degree.
* `RHTower.deningerFormSheaf` : the sheaf of smooth `(0,q)`-forms.
-/

namespace RHTower

open CategoryTheory TopologicalSpace Opposite TopCat Complex HTGeometry

variable {n : ℕ}

/-- The coefficient space of a form: one complex number for each set of directions. -/
abbrev DeningerFormVal (n : ℕ) : Type := Finset (Fin n) → ℂ

/-- The set-indexed form attached to a function into the coefficient space. -/
def deningerFlip (F : (Fin n → ℂ) → DeningerFormVal n) : SetForm n := fun S z => F z S

@[simp] theorem deningerFlip_apply (F : (Fin n → ℂ) → DeningerFormVal n) (S : Finset (Fin n))
    (z : Fin n → ℂ) : deningerFlip F S z = F z S := rfl

section Predicate

variable {Ω : Opens (Fin n → ℂ)}

/-- A section is a smooth form of degree `q` when its coefficients vanish outside the sets of `q`
directions and it agrees, near every point, with a globally smooth form of that degree. -/
def DeningerFormPred (q : ℕ) {U : Opens (deningerSpace Ω)} (f : ↥U → DeningerFormVal n) : Prop :=
  (∀ (x : ↥U) (S : Finset (Fin n)), S.card ≠ q → f x S = 0) ∧
    ∀ x : ↥U, ∃ g : SetForm n, SmoothSetForm g ∧
      ∀ᶠ z in nhds (x.1.1 : Fin n → ℂ), ∀ S, deningerExtend f z S = g S z

theorem DeningerFormPred.res (q : ℕ) {U W : Opens (deningerSpace Ω)} (h : W ≤ U)
    {f : ↥U → DeningerFormVal n} (hf : DeningerFormPred q f) :
    DeningerFormPred q (fun x : ↥W => f ⟨x.1, h x.2⟩) := by
  refine ⟨fun x S hS => hf.1 ⟨x.1, h x.2⟩ S hS, fun x => ?_⟩
  obtain ⟨g, hg, hgeq⟩ := hf.2 ⟨x.1, h x.2⟩
  refine ⟨g, hg, ?_⟩
  have hmem : (x.1.1 : Fin n → ℂ) ∈ deningerAmb W := deningerAmb_mem_of_mem x
  filter_upwards [hgeq, deningerExtend_eventuallyEq (V := DeningerFormVal n) h f hmem] with
    z hz hres
  intro S
  rw [hres]
  exact hz S

theorem DeningerFormPred.locality (q : ℕ) {U : Opens (deningerSpace Ω)}
    (f : ↥U → DeningerFormVal n)
    (hloc : ∀ x : ↥U, ∃ (W : Opens (deningerSpace Ω)) (hW : W ≤ U), x.1 ∈ W ∧
      DeningerFormPred q (fun y : ↥W => f ⟨y.1, hW y.2⟩)) :
    DeningerFormPred q f := by
  constructor
  · intro x S hS
    obtain ⟨W, hW, hxW, hpred, -⟩ := hloc x
    exact hpred ⟨x.1, hxW⟩ S hS
  · intro x
    obtain ⟨W, hW, hxW, -, hsm⟩ := hloc x
    obtain ⟨g, hg, hgeq⟩ := hsm ⟨x.1, hxW⟩
    refine ⟨g, hg, ?_⟩
    have hmem : (x.1.1 : Fin n → ℂ) ∈ deningerAmb W := ⟨x.1, hxW, rfl⟩
    filter_upwards [hgeq, deningerExtend_eventuallyEq (V := DeningerFormVal n) hW f hmem] with
      z hz hres
    intro S
    rw [← hres]
    exact hz S

theorem DeningerFormPred.zero (q : ℕ) (U : Opens (deningerSpace Ω)) :
    DeningerFormPred q (fun _ : ↥U => (0 : DeningerFormVal n)) := by
  refine ⟨fun _ _ _ => rfl, fun x => ⟨fun _ _ => 0, fun _ => contDiff_const, ?_⟩⟩
  filter_upwards with z
  intro S
  rw [deningerExtend_zero (V := DeningerFormVal n)]
  rfl

theorem DeningerFormPred.add (q : ℕ) {U : Opens (deningerSpace Ω)}
    {f g : ↥U → DeningerFormVal n} (hf : DeningerFormPred q f) (hg : DeningerFormPred q g) :
    DeningerFormPred q (fun x => f x + g x) := by
  refine ⟨fun x S hS => ?_, fun x => ?_⟩
  · show f x S + g x S = 0
    rw [hf.1 x S hS, hg.1 x S hS, add_zero]
  · obtain ⟨a, ha, haeq⟩ := hf.2 x
    obtain ⟨b, hb, hbeq⟩ := hg.2 x
    refine ⟨fun S z => a S z + b S z, fun S => (ha S).add (hb S), ?_⟩
    filter_upwards [haeq, hbeq] with z hza hzb
    intro S
    rw [deningerExtend_add (V := DeningerFormVal n) f g]
    show deningerExtend f z S + deningerExtend g z S = a S z + b S z
    rw [hza S, hzb S]

theorem DeningerFormPred.neg (q : ℕ) {U : Opens (deningerSpace Ω)}
    {f : ↥U → DeningerFormVal n} (hf : DeningerFormPred q f) :
    DeningerFormPred q (fun x => -f x) := by
  refine ⟨fun x S hS => ?_, fun x => ?_⟩
  · show -f x S = 0
    rw [hf.1 x S hS, neg_zero]
  · obtain ⟨a, ha, haeq⟩ := hf.2 x
    refine ⟨fun S z => -a S z, fun S => (ha S).neg, ?_⟩
    filter_upwards [haeq] with z hza
    intro S
    rw [deningerExtend_neg (V := DeningerFormVal n) f]
    show -deningerExtend f z S = -a S z
    rw [hza S]

/-- The local predicate cutting out the smooth forms of degree `q`. -/
noncomputable def deningerFormLocalPredicate (Ω : Opens (Fin n → ℂ)) (q : ℕ) :
    TopCat.LocalPredicate (fun _ : (deningerSpace Ω : Type) => DeningerFormVal n) where
  pred {_} f := DeningerFormPred q f
  res {_ _} i _ hf := DeningerFormPred.res q i.le hf
  locality {_} f hf := by
    refine DeningerFormPred.locality q f fun x => ?_
    obtain ⟨W, hxW, i, hpred⟩ := hf x
    exact ⟨W, i.le, hxW, hpred⟩

/-- The data cutting out the sheaf of smooth `(0,q)`-forms. -/
noncomputable def deningerFormData (Ω : Opens (Fin n → ℂ)) (q : ℕ) :
    DeningerLocalGroupData (deningerSpace Ω) (DeningerFormVal n) where
  toLocalPredicate := deningerFormLocalPredicate Ω q
  pred_zero U := DeningerFormPred.zero q U
  pred_add _ _ _ hf hg := DeningerFormPred.add q hf hg
  pred_neg _ _ hf := DeningerFormPred.neg q hf

/-- **The sheaf of smooth `(0,q)`-forms.** -/
noncomputable def deningerFormSheaf (Ω : Opens (Fin n → ℂ)) (q : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace Ω) :=
  (deningerFormData Ω q).sheaf

/-- The differential of a section is computed by any of its local smooth models. -/
theorem deningerSetDbar_model {U : Opens (deningerSpace Ω)} {f : ↥U → DeningerFormVal n} {x : ↥U}
    {g : SetForm n}
    (hgeq : ∀ᶠ z in nhds (x.1.1 : Fin n → ℂ), ∀ S, deningerExtend f z S = g S z)
    (S : Finset (Fin n)) :
    setDbar (deningerFlip (deningerExtend f)) S (x.1.1 : Fin n → ℂ)
      = setDbar g S (x.1.1 : Fin n → ℂ) :=
  setDbar_congr_of_eventuallyEq (fun T => hgeq.mono fun _ hz => hz T) S

end Predicate

section Closed

variable {Ω : Opens (Fin n → ℂ)}

/-- A section is a closed smooth form of degree `q` when it is a smooth form of degree `q` whose
differential vanishes. -/
def DeningerClosedFormPred (q : ℕ) {U : Opens (deningerSpace Ω)}
    (f : ↥U → DeningerFormVal n) : Prop :=
  DeningerFormPred q f ∧ ∀ (x : ↥U) (S : Finset (Fin n)),
    setDbar (deningerFlip (deningerExtend f)) S (x.1.1 : Fin n → ℂ) = 0

theorem DeningerClosedFormPred.res (q : ℕ) {U W : Opens (deningerSpace Ω)} (h : W ≤ U)
    {f : ↥U → DeningerFormVal n} (hf : DeningerClosedFormPred q f) :
    DeningerClosedFormPred q (fun x : ↥W => f ⟨x.1, h x.2⟩) := by
  refine ⟨DeningerFormPred.res q h hf.1, fun x S => ?_⟩
  have hmem : (x.1.1 : Fin n → ℂ) ∈ deningerAmb W := deningerAmb_mem_of_mem x
  have hloc : setDbar (deningerFlip (deningerExtend (fun y : ↥W => f ⟨y.1, h y.2⟩))) S
      (x.1.1 : Fin n → ℂ) = setDbar (deningerFlip (deningerExtend f)) S (x.1.1 : Fin n → ℂ) :=
    setDbar_congr_of_eventuallyEq
      (fun T => (deningerExtend_eventuallyEq (V := DeningerFormVal n) h f hmem).mono
        fun z hz => congrFun hz T) S
  rw [hloc]
  exact hf.2 ⟨x.1, h x.2⟩ S

theorem DeningerClosedFormPred.locality (q : ℕ) {U : Opens (deningerSpace Ω)}
    (f : ↥U → DeningerFormVal n)
    (hloc : ∀ x : ↥U, ∃ (W : Opens (deningerSpace Ω)) (hW : W ≤ U), x.1 ∈ W ∧
      DeningerClosedFormPred q (fun y : ↥W => f ⟨y.1, hW y.2⟩)) :
    DeningerClosedFormPred q f := by
  refine ⟨DeningerFormPred.locality q f fun x => ?_, fun x S => ?_⟩
  · obtain ⟨W, hW, hxW, hpred⟩ := hloc x
    exact ⟨W, hW, hxW, hpred.1⟩
  · obtain ⟨W, hW, hxW, hpred⟩ := hloc x
    have hmem : (x.1.1 : Fin n → ℂ) ∈ deningerAmb W := ⟨x.1, hxW, rfl⟩
    have heq : setDbar (deningerFlip (deningerExtend (fun y : ↥W => f ⟨y.1, hW y.2⟩))) S
        (x.1.1 : Fin n → ℂ) = setDbar (deningerFlip (deningerExtend f)) S (x.1.1 : Fin n → ℂ) :=
      setDbar_congr_of_eventuallyEq
        (fun T => (deningerExtend_eventuallyEq (V := DeningerFormVal n) hW f hmem).mono
          fun z hz => congrFun hz T) S
    rw [← heq]
    exact hpred.2 ⟨x.1, hxW⟩ S

theorem DeningerClosedFormPred.zero (q : ℕ) (U : Opens (deningerSpace Ω)) :
    DeningerClosedFormPred q (fun _ : ↥U => (0 : DeningerFormVal n)) := by
  refine ⟨DeningerFormPred.zero q U, fun x S => ?_⟩
  refine deningerSetDbar_model (g := fun _ _ => 0) ?_ S |>.trans ?_
  · filter_upwards with z
    intro T
    rw [deningerExtend_zero (V := DeningerFormVal n)]
    rfl
  · refine Finset.sum_eq_zero fun k _ => ?_
    rw [show (fun _ _ => (0 : ℂ)) (S.erase k) = fun _ : Fin n → ℂ => (0 : ℂ) from rfl,
      dzbarAt_zero, mul_zero]

theorem DeningerClosedFormPred.add (q : ℕ) {U : Opens (deningerSpace Ω)}
    {f g : ↥U → DeningerFormVal n} (hf : DeningerClosedFormPred q f)
    (hg : DeningerClosedFormPred q g) :
    DeningerClosedFormPred q (fun x => f x + g x) := by
  refine ⟨DeningerFormPred.add q hf.1 hg.1, fun x S => ?_⟩
  obtain ⟨a, ha, haeq⟩ := hf.1.2 x
  obtain ⟨b, hb, hbeq⟩ := hg.1.2 x
  have hmodel : ∀ᶠ z in nhds (x.1.1 : Fin n → ℂ),
      ∀ T, deningerExtend (fun y => f y + g y) z T = setFormAdd a b T z := by
    filter_upwards [haeq, hbeq] with z hza hzb
    intro T
    rw [deningerExtend_add (V := DeningerFormVal n) f g]
    show deningerExtend f z T + deningerExtend g z T = a T z + b T z
    rw [hza T, hzb T]
  rw [deningerSetDbar_model hmodel S,
    setDbar_add ha hb S (x.1.1 : Fin n → ℂ),
    ← deningerSetDbar_model haeq S, ← deningerSetDbar_model hbeq S, hf.2 x S, hg.2 x S, add_zero]

theorem DeningerClosedFormPred.neg (q : ℕ) {U : Opens (deningerSpace Ω)}
    {f : ↥U → DeningerFormVal n} (hf : DeningerClosedFormPred q f) :
    DeningerClosedFormPred q (fun x => -f x) := by
  refine ⟨DeningerFormPred.neg q hf.1, fun x S => ?_⟩
  obtain ⟨a, ha, haeq⟩ := hf.1.2 x
  have hmodel : ∀ᶠ z in nhds (x.1.1 : Fin n → ℂ),
      ∀ T, deningerExtend (fun y => -f y) z T =
        setFormSub (fun (_ : Finset (Fin n)) (_ : Fin n → ℂ) => (0 : ℂ)) a T z := by
    filter_upwards [haeq] with z hza
    intro T
    rw [deningerExtend_neg (V := DeningerFormVal n) f]
    show -deningerExtend f z T = 0 - a T z
    rw [hza T, zero_sub]
  have hzero : SmoothSetForm (fun (_ : Finset (Fin n)) (_ : Fin n → ℂ) => (0 : ℂ)) :=
    fun _ => contDiff_const
  rw [deningerSetDbar_model hmodel S,
    setDbar_sub hzero ha S (x.1.1 : Fin n → ℂ), ← deningerSetDbar_model haeq S, hf.2 x S]
  have h0 : setDbar (fun (_ : Finset (Fin n)) (_ : Fin n → ℂ) => (0 : ℂ)) S
      (x.1.1 : Fin n → ℂ) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [show (fun (_ : Finset (Fin n)) (_ : Fin n → ℂ) => (0 : ℂ)) (S.erase k)
        = fun _ : Fin n → ℂ => (0 : ℂ) from rfl, dzbarAt_zero, mul_zero]
  rw [h0, sub_zero]

/-- The local predicate cutting out the closed smooth forms of degree `q`. -/
noncomputable def deningerClosedFormLocalPredicate (Ω : Opens (Fin n → ℂ)) (q : ℕ) :
    TopCat.LocalPredicate (fun _ : (deningerSpace Ω : Type) => DeningerFormVal n) where
  pred {_} f := DeningerClosedFormPred q f
  res {_ _} i _ hf := DeningerClosedFormPred.res q i.le hf
  locality {_} f hf := by
    refine DeningerClosedFormPred.locality q f fun x => ?_
    obtain ⟨W, hxW, i, hpred⟩ := hf x
    exact ⟨W, i.le, hxW, hpred⟩

/-- The data cutting out the sheaf of closed smooth `(0,q)`-forms. -/
noncomputable def deningerClosedFormData (Ω : Opens (Fin n → ℂ)) (q : ℕ) :
    DeningerLocalGroupData (deningerSpace Ω) (DeningerFormVal n) where
  toLocalPredicate := deningerClosedFormLocalPredicate Ω q
  pred_zero U := DeningerClosedFormPred.zero q U
  pred_add _ _ _ hf hg := DeningerClosedFormPred.add q hf hg
  pred_neg _ _ hf := DeningerClosedFormPred.neg q hf

/-- **The sheaf of closed smooth `(0,q)`-forms.**  For `q = 0` this is the sheaf of holomorphic
functions: a degree-zero form is a function, and its differential is the family of antiholomorphic
partial derivatives. -/
noncomputable def deningerClosedFormSheaf (Ω : Opens (Fin n → ℂ)) (q : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace Ω) :=
  (deningerClosedFormData Ω q).sheaf

end Closed

end RHTower
