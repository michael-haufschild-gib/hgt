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

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat Complex HTGeometry

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
    ∀ x : ↥U, ∃ g : SetForm n, SmoothSetForm g ∧ SetFormDeg q g ∧
      ∀ᶠ z in nhds (x.1.1 : Fin n → ℂ), ∀ S, deningerExtend f z S = g S z

theorem DeningerFormPred.res (q : ℕ) {U W : Opens (deningerSpace Ω)} (h : W ≤ U)
    {f : ↥U → DeningerFormVal n} (hf : DeningerFormPred q f) :
    DeningerFormPred q (fun x : ↥W => f ⟨x.1, h x.2⟩) := by
  refine ⟨fun x S hS => hf.1 ⟨x.1, h x.2⟩ S hS, fun x => ?_⟩
  obtain ⟨g, hg, hgd, hgeq⟩ := hf.2 ⟨x.1, h x.2⟩
  refine ⟨g, hg, hgd, ?_⟩
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
    obtain ⟨g, hg, hgd, hgeq⟩ := hsm ⟨x.1, hxW⟩
    refine ⟨g, hg, hgd, ?_⟩
    have hmem : (x.1.1 : Fin n → ℂ) ∈ deningerAmb W := ⟨x.1, hxW, rfl⟩
    filter_upwards [hgeq, deningerExtend_eventuallyEq (V := DeningerFormVal n) hW f hmem] with
      z hz hres
    intro S
    rw [← hres]
    exact hz S

theorem DeningerFormPred.zero (q : ℕ) (U : Opens (deningerSpace Ω)) :
    DeningerFormPred q (fun _ : ↥U => (0 : DeningerFormVal n)) := by
  refine ⟨fun _ _ _ => rfl,
    fun x => ⟨fun _ _ => 0, fun _ => contDiff_const, fun _ _ _ => rfl, ?_⟩⟩
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
  · obtain ⟨a, ha, had, haeq⟩ := hf.2 x
    obtain ⟨b, hb, hbd, hbeq⟩ := hg.2 x
    refine ⟨setFormAdd a b, ha.add hb, had.add hbd, ?_⟩
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
  · obtain ⟨a, ha, had, haeq⟩ := hf.2 x
    have hz0 : SmoothSetForm (fun (_ : Finset (Fin n)) (_ : Fin n → ℂ) => (0 : ℂ)) :=
      fun _ => contDiff_const
    have hd0 : SetFormDeg q (fun (_ : Finset (Fin n)) (_ : Fin n → ℂ) => (0 : ℂ)) :=
      fun _ _ _ => rfl
    refine ⟨setFormSub (fun _ _ => 0) a, hz0.sub ha, hd0.sub had, ?_⟩
    filter_upwards [haeq] with z hza
    intro S
    rw [deningerExtend_neg (V := DeningerFormVal n) f]
    show -deningerExtend f z S = 0 - a S z
    rw [hza S, zero_sub]

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
  obtain ⟨a, ha, had, haeq⟩ := hf.1.2 x
  obtain ⟨b, hb, hbd, hbeq⟩ := hg.1.2 x
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
  obtain ⟨a, ha, had, haeq⟩ := hf.1.2 x
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

section Maps

variable {Ω : Opens (Fin n → ℂ)}

/-- A local smooth model on an explicit open neighbourhood. -/
theorem DeningerFormPred.exists_model_open {q : ℕ} {U : Opens (deningerSpace Ω)}
    {f : ↥U → DeningerFormVal n} (hf : DeningerFormPred q f) (x : ↥U) :
    ∃ (g : SetForm n) (N : Set (Fin n → ℂ)), SmoothSetForm g ∧ SetFormDeg q g ∧ IsOpen N ∧
      (x.1.1 : Fin n → ℂ) ∈ N ∧ ∀ z ∈ N, ∀ S, deningerExtend f z S = g S z := by
  obtain ⟨g, hg, hgd, hgeq⟩ := hf.2 x
  obtain ⟨N, hNsub, hNopen, hxN⟩ := mem_nhds_iff.1 hgeq
  exact ⟨g, N, hg, hgd, hNopen, hxN, fun z hz => hNsub hz⟩

/-- The differential of a section. -/
noncomputable def deningerDbarSection {U : Opens (deningerSpace Ω)}
    (f : ↥U → DeningerFormVal n) : ↥U → DeningerFormVal n :=
  fun x S => setDbar (deningerFlip (deningerExtend f)) S (x.1.1 : Fin n → ℂ)

/-- The differential of a section is modelled by the differential of any local model. -/
theorem deningerDbar_model {q : ℕ} {U : Opens (deningerSpace Ω)}
    {f : ↥U → DeningerFormVal n} (hf : DeningerFormPred q f) (x : ↥U) :
    ∃ g : SetForm n, SmoothSetForm g ∧ SetFormDeg q g ∧
      ∀ᶠ z in nhds (x.1.1 : Fin n → ℂ), ∀ S,
        deningerExtend (deningerDbarSection f) z S = setDbar g S z := by
  obtain ⟨g, N, hg, hgd, hNopen, hxN, hNeq⟩ := hf.exists_model_open x
  refine ⟨g, hg, hgd, ?_⟩
  have hmem : N ∩ (deningerAmb U : Set (Fin n → ℂ)) ∈ nhds (x.1.1 : Fin n → ℂ) :=
    (hNopen.inter (deningerAmb U).2).mem_nhds ⟨hxN, deningerAmb_mem_of_mem x⟩
  filter_upwards [hmem] with z hz
  intro S
  rw [deningerExtend_of_mem _ hz.2]
  show setDbar (deningerFlip (deningerExtend f)) S ((deningerPt hz.2).1.1 : Fin n → ℂ) = _
  rw [deningerPt_val hz.2]
  exact setDbar_congr_on_isOpen hNopen (fun T y hy => hNeq y hy T) hz.1 S

/-- **The differential of a smooth form of degree `q` is a closed smooth form of degree `q + 1`.** -/
theorem deningerDbarSection_pred {q : ℕ} {U : Opens (deningerSpace Ω)}
    {f : ↥U → DeningerFormVal n} (hf : DeningerFormPred q f) :
    DeningerClosedFormPred (q + 1) (deningerDbarSection f) := by
  refine ⟨⟨fun x S hS => ?_, fun x => ?_⟩, fun x S => ?_⟩
  · obtain ⟨g, hg, hgd, hgeq⟩ := hf.2 x
    show setDbar (deningerFlip (deningerExtend f)) S (x.1.1 : Fin n → ℂ) = 0
    rw [deningerSetDbar_model hgeq S]
    exact setDbar_deg hgd S hS _
  · obtain ⟨g, hg, hgd, hgeq⟩ := deningerDbar_model hf x
    exact ⟨setDbar g, setDbar_smooth hg, setDbar_deg hgd, hgeq⟩
  · obtain ⟨g, hg, hgd, hgeq⟩ := deningerDbar_model hf x
    rw [deningerSetDbar_model hgeq S,
      setDbar_setDbar_eq_zero (fun T => (hg T).of_le (by decide)) S]

/-- The differential commutes with restriction. -/
theorem deningerDbarSection_res {U W : Opens (deningerSpace Ω)} (h : W ≤ U)
    (f : ↥U → DeningerFormVal n) (x : ↥W) :
    deningerDbarSection (fun y : ↥W => f ⟨y.1, h y.2⟩) x
      = deningerDbarSection f ⟨x.1, h x.2⟩ := by
  funext S
  have hmem : (x.1.1 : Fin n → ℂ) ∈ deningerAmb W := deningerAmb_mem_of_mem x
  exact setDbar_congr_of_eventuallyEq
    (fun T => (deningerExtend_eventuallyEq (V := DeningerFormVal n) h f hmem).mono
      fun z hz => congrFun hz T) S

/-- The differential of the zero section vanishes. -/
theorem deningerDbarSection_zero {U : Opens (deningerSpace Ω)} (x : ↥U) :
    deningerDbarSection (fun _ : ↥U => (0 : DeningerFormVal n)) x = 0 := by
  funext S
  have h0 : deningerFlip (deningerExtend (fun _ : ↥U => (0 : DeningerFormVal n)))
      = fun (_ : Finset (Fin n)) (_ : Fin n → ℂ) => (0 : ℂ) := by
    funext T z
    show deningerExtend (fun _ : ↥U => (0 : DeningerFormVal n)) z T = 0
    rw [deningerExtend_zero (V := DeningerFormVal n)]
    rfl
  show setDbar (deningerFlip (deningerExtend (fun _ : ↥U => (0 : DeningerFormVal n)))) S
      (x.1.1 : Fin n → ℂ) = 0
  rw [h0]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [show (fun (_ : Finset (Fin n)) (_ : Fin n → ℂ) => (0 : ℂ)) (S.erase k)
      = fun _ : Fin n → ℂ => (0 : ℂ) from rfl, dzbarAt_zero, mul_zero]

/-- The differential is additive. -/
theorem deningerDbarSection_add {q : ℕ} {U : Opens (deningerSpace Ω)}
    {f g : ↥U → DeningerFormVal n} (hf : DeningerFormPred q f) (hg : DeningerFormPred q g)
    (x : ↥U) : deningerDbarSection (fun y => f y + g y) x
      = deningerDbarSection f x + deningerDbarSection g x := by
  funext S
  obtain ⟨a, ha, had, haeq⟩ := hf.2 x
  obtain ⟨b, hb, hbd, hbeq⟩ := hg.2 x
  have hmodel : ∀ᶠ z in nhds (x.1.1 : Fin n → ℂ),
      ∀ T, deningerExtend (fun y => f y + g y) z T = setFormAdd a b T z := by
    filter_upwards [haeq, hbeq] with z hza hzb
    intro T
    rw [deningerExtend_add (V := DeningerFormVal n) f g]
    show deningerExtend f z T + deningerExtend g z T = a T z + b T z
    rw [hza T, hzb T]
  show setDbar (deningerFlip (deningerExtend (fun y => f y + g y))) S (x.1.1 : Fin n → ℂ) = _
  rw [deningerSetDbar_model hmodel S, setDbar_add ha hb S (x.1.1 : Fin n → ℂ),
    ← deningerSetDbar_model haeq S, ← deningerSetDbar_model hbeq S]
  rfl

/-- **The inclusion of the closed forms into all forms.** -/
noncomputable def deningerFormIncl (Ω : Opens (Fin n → ℂ)) (q : ℕ) :
    deningerClosedFormSheaf Ω q ⟶ deningerFormSheaf Ω q :=
  ⟨{ app := fun _ => AddCommGrpCat.ofHom
      { toFun := fun f => ⟨f.1, f.2.1⟩
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
     naturality := fun _ _ _ => rfl }⟩

/-- **The Dolbeault differential, from the smooth forms of degree `q` to the closed smooth forms of
degree `q + 1`.** -/
noncomputable def deningerFormDbar (Ω : Opens (Fin n → ℂ)) (q : ℕ) :
    deningerFormSheaf Ω q ⟶ deningerClosedFormSheaf Ω (q + 1) :=
  ⟨{ app := fun U => AddCommGrpCat.ofHom
      { toFun := fun f => ⟨deningerDbarSection f.1, deningerDbarSection_pred f.2⟩
        map_zero' := Subtype.ext (funext fun x => deningerDbarSection_zero x)
        map_add' := fun a b =>
          Subtype.ext (funext fun x => deningerDbarSection_add a.2 b.2 x) }
     naturality := fun U W i => by
       ext f
       exact Subtype.ext (funext fun x => deningerDbarSection_res i.unop.le f.1 x) }⟩

/-- The composite of the inclusion and the differential vanishes: a closed form has zero
differential. -/
theorem deningerFormIncl_comp_dbar (Ω : Opens (Fin n → ℂ)) (q : ℕ) :
    deningerFormIncl Ω q ≫ deningerFormDbar Ω q = 0 := by
  refine CategoryTheory.ObjectProperty.hom_ext _ ?_
  ext U f
  exact Subtype.ext (funext fun x => funext fun S => f.2.2 x S)

/-- The `q`-th step of the Dolbeault resolution. -/
noncomputable def deningerFormStep (Ω : Opens (Fin n → ℂ)) (q : ℕ) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace Ω)) :=
  ShortComplex.mk (deningerFormIncl Ω q) (deningerFormDbar Ω q) (deningerFormIncl_comp_dbar Ω q)

instance deningerFormIncl_mono (Ω : Opens (Fin n → ℂ)) (q : ℕ) :
    Mono (deningerFormIncl Ω q) := by
  haveI : ∀ U, Mono ((deningerFormIncl Ω q).1.app U) := by
    intro U
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b hab
    have h : (ConcreteCategory.hom ((deningerFormIncl Ω q).1.app U) a).1
        = (ConcreteCategory.hom ((deningerFormIncl Ω q).1.app U) b).1 := by rw [hab]
    exact Subtype.ext h
  haveI : Mono (deningerFormIncl Ω q).1 := NatTrans.mono_of_mono_app _
  exact CategoryTheory.Sheaf.Hom.mono_of_presheaf_mono _ _ _

/-- A section whose image under a map with vanishing differential is taken is closed. -/
theorem deningerKernelLift_pred {Ω : Opens (Fin n → ℂ)} {q : ℕ}
    {T : TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace Ω)} (k : T ⟶ deningerFormSheaf Ω q)
    (hk : k ≫ deningerFormDbar Ω q = 0) (U : (Opens (deningerSpace Ω))ᵒᵖ)
    (t : ToType (T.1.obj U)) :
    DeningerClosedFormPred q (ConcreteCategory.hom (k.1.app U) t).1 := by
  refine ⟨(ConcreteCategory.hom (k.1.app U) t).2, fun x S => ?_⟩
  have h0 := congrArg
    (fun ψ : T ⟶ deningerClosedFormSheaf Ω (q + 1) => ConcreteCategory.hom (ψ.1.app U) t) hk
  have h1 : deningerDbarSection (ConcreteCategory.hom (k.1.app U) t).1
      = (0 : ↥(unop U) → DeningerFormVal n) := Subtype.ext_iff.1 h0
  have h2 : deningerDbarSection (ConcreteCategory.hom (k.1.app U) t).1 x S = 0 := by
    rw [h1]
    rfl
  exact h2

/-- A map into the smooth forms whose differential vanishes lands in the closed forms. -/
noncomputable def deningerKernelLift {Ω : Opens (Fin n → ℂ)} {q : ℕ}
    {T : TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace Ω)} (k : T ⟶ deningerFormSheaf Ω q)
    (hk : k ≫ deningerFormDbar Ω q = 0) : T ⟶ deningerClosedFormSheaf Ω q :=
  ⟨{ app := fun U => AddCommGrpCat.ofHom
      { toFun := fun t => ⟨(ConcreteCategory.hom (k.1.app U) t).1,
          deningerKernelLift_pred k hk U t⟩
        map_zero' := by
          refine Subtype.ext ?_
          have h : ConcreteCategory.hom (k.1.app U) 0 = 0 := map_zero _
          show (ConcreteCategory.hom (k.1.app U) 0).1 = _
          rw [h]
          rfl
        map_add' := fun a b => by
          refine Subtype.ext ?_
          have h : ConcreteCategory.hom (k.1.app U) (a + b)
              = ConcreteCategory.hom (k.1.app U) a + ConcreteCategory.hom (k.1.app U) b :=
            map_add _ a b
          show (ConcreteCategory.hom (k.1.app U) (a + b)).1 = _
          rw [h]
          rfl }
     naturality := fun U W i => by
       ext t
       refine Subtype.ext ?_
       have h := CategoryTheory.NatTrans.naturality_apply k.1 i t
       show (ConcreteCategory.hom (k.1.app W) (ConcreteCategory.hom (T.1.map i) t)).1 = _
       rw [h]
       rfl }⟩

@[simp] theorem deningerKernelLift_apply {Ω : Opens (Fin n → ℂ)} {q : ℕ}
    {T : TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace Ω)} (k : T ⟶ deningerFormSheaf Ω q)
    (hk : k ≫ deningerFormDbar Ω q = 0) (U : (Opens (deningerSpace Ω))ᵒᵖ)
    (t : ToType (T.1.obj U)) :
    (ConcreteCategory.hom ((deningerKernelLift k hk).1.app U) t).1
      = (ConcreteCategory.hom (k.1.app U) t).1 := rfl

/-- **The closed forms are the kernel of the differential.** -/
noncomputable def deningerFormStep_isKernel (Ω : Opens (Fin n → ℂ)) (q : ℕ) :
    IsLimit (KernelFork.ofι (deningerFormIncl Ω q) (deningerFormIncl_comp_dbar Ω q)) := by
  refine KernelFork.IsLimit.ofι _ _ (fun {T} k hk => deningerKernelLift k hk) ?_ ?_
  · intro T k hk
    refine CategoryTheory.ObjectProperty.hom_ext _ ?_
    ext U t
    show ConcreteCategory.hom ((deningerKernelLift k hk).1.app U ≫
      (deningerFormIncl Ω q).1.app U) t = _
    rw [ConcreteCategory.comp_apply]
    exact Subtype.ext rfl
  · intro T k hk m hm
    refine CategoryTheory.ObjectProperty.hom_ext _ ?_
    ext U t
    refine Subtype.ext ?_
    have h' : (ConcreteCategory.hom ((m ≫ deningerFormIncl Ω q).1.app U) t).1
        = (ConcreteCategory.hom (k.1.app U) t).1 := by rw [hm]
    have hcomp : (ConcreteCategory.hom ((m ≫ deningerFormIncl Ω q).1.app U) t).1
        = (ConcreteCategory.hom (m.1.app U) t).1 := by
      show (ConcreteCategory.hom ((m.1.app U) ≫ (deningerFormIncl Ω q).1.app U) t).1 = _
      rw [ConcreteCategory.comp_apply]
      rfl
    show (ConcreteCategory.hom (m.1.app U) t).1 = (ConcreteCategory.hom (k.1.app U) t).1
    rw [← hcomp]
    exact h'

theorem deningerFormStep_exact (Ω : Opens (Fin n → ℂ)) (q : ℕ) :
    (deningerFormStep Ω q).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (deningerFormStep_isKernel Ω q)

end Maps

section Epi

variable {Ω : Opens (Fin n → ℂ)}

/-- The open set of the domain cut out by an ambient open set. -/
def deningerRestrictOpen (Ω : Opens (Fin n → ℂ)) (W : Opens (Fin n → ℂ)) :
    Opens (deningerSpace Ω) :=
  ⟨Subtype.val ⁻¹' (W : Set (Fin n → ℂ)), W.2.preimage continuous_subtype_val⟩

theorem deningerAmb_restrictOpen_le {W : Opens (Fin n → ℂ)} {U : Opens (deningerSpace Ω)} :
    deningerAmb (deningerRestrictOpen Ω W ⊓ U) ≤ W := by
  rintro z ⟨y, hy, rfl⟩
  exact hy.1

theorem deningerAmb_restrictOpen_le_amb {W : Opens (Fin n → ℂ)} {U : Opens (deningerSpace Ω)} :
    deningerAmb (deningerRestrictOpen Ω W ⊓ U) ≤ deningerAmb U := deningerAmb_mono inf_le_right

/-- **The Dolbeault differential is locally surjective**: a closed smooth form of degree `q + 1` is
locally the differential of a smooth form of degree `q`, by the `∂̄`-lemma on a polydisc. -/
theorem deningerFormDbar_locallySurjective (Ω : Opens (Fin n → ℂ)) (q : ℕ) :
    TopCat.Presheaf.IsLocallySurjective (deningerFormDbar Ω q).1 := by
  refine (TopCat.Presheaf.isLocallySurjective_iff _).2 ?_
  intro U h x hx
  set c : Fin n → ℂ := (x.1 : Fin n → ℂ) with hc
  obtain ⟨g, N, hg, hgd, hNopen, hxN, hNeq⟩ := h.2.1.exists_model_open ⟨x, hx⟩
  -- the model is closed on the ambient open set
  have hclosed : ∀ (S : Finset (Fin n)), ∀ z ∈ N ∩ (deningerAmb U : Set (Fin n → ℂ)),
      setDbar g S z = 0 := by
    intro S z hz
    have hloc : setDbar (deningerFlip (deningerExtend h.1)) S z = setDbar g S z :=
      setDbar_congr_on_isOpen hNopen (fun T y hy => hNeq y hy T) hz.1 S
    rw [← hloc]
    have := h.2.2 (deningerPt hz.2) S
    rwa [deningerPt_val hz.2] at this
  -- a polydisc inside the ambient open set
  have hopen : IsOpen (N ∩ (deningerAmb U : Set (Fin n → ℂ))) := hNopen.inter (deningerAmb U).2
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen c ⟨hxN, deningerAmb_mem_of_mem ⟨x, hx⟩⟩
  have hpoly : polydisc c (fun _ => ε) ⊆ N ∩ (deningerAmb U : Set (Fin n → ℂ)) := by
    intro z hz
    refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm]
    refine (pi_norm_lt_iff hε).2 fun i => ?_
    have := hz i
    rwa [Metric.mem_ball, dist_eq_norm] at this
  obtain ⟨u, hCu, hud, hu⟩ :=
    setDbar_polydisc_solve (c := c) (ρ := fun _ => ε / 2) (r := fun _ => ε)
      (fun _ => by positivity) (fun _ => by linarith) hg (hgd.empty (Nat.succ_ne_zero q)) hgd
      (fun S z hz => hclosed S z (hpoly hz))
  -- the local primitive as a section
  set P : Opens (Fin n → ℂ) := ⟨polydisc c (fun _ => ε / 2), isOpen_polydisc _ _⟩ with hP
  set V : Opens (deningerSpace Ω) := deningerRestrictOpen Ω P ⊓ U with hV
  have hxV : x ∈ V := by
    refine ⟨?_, hx⟩
    show (x.1 : Fin n → ℂ) ∈ polydisc c (fun _ => ε / 2)
    intro i
    rw [Metric.mem_ball, dist_self]
    linarith
  refine ⟨V, inf_le_right, ⟨⟨fun y => fun S => u S (y.1.1 : Fin n → ℂ), ?_⟩, ?_⟩, hxV⟩
  · refine ⟨fun y S hS => hud S hS _, fun y => ⟨u, hCu, hud, ?_⟩⟩
    filter_upwards [(deningerAmb V).2.mem_nhds (deningerAmb_mem_of_mem y)] with z hz
    intro S
    rw [deningerExtend_of_mem _ hz]
    rfl
  · refine Subtype.ext (funext fun y => funext fun S => ?_)
    have hmodel : ∀ᶠ z in nhds ((y.1.1 : Fin n → ℂ)),
        ∀ S, deningerExtend (fun w : ↥V => fun S => u S (w.1.1 : Fin n → ℂ)) z S = u S z := by
      filter_upwards [(deningerAmb V).2.mem_nhds (deningerAmb_mem_of_mem y)] with z hz
      intro S
      rw [deningerExtend_of_mem _ hz]
      rfl
    have hyP : (y.1.1 : Fin n → ℂ) ∈ polydisc c (fun _ => ε / 2) :=
      deningerAmb_restrictOpen_le (deningerAmb_mem_of_mem y)
    have hyN : (y.1.1 : Fin n → ℂ) ∈ N :=
      (hpoly (fun i => Metric.ball_subset_ball (by linarith) (hyP i))).1
    show setDbar (deningerFlip (deningerExtend
      (fun w : ↥V => fun S => u S (w.1.1 : Fin n → ℂ)))) S (y.1.1 : Fin n → ℂ) = _
    rw [deningerSetDbar_model hmodel S, hu S _ hyP]
    have hyU : (y.1.1 : Fin n → ℂ) ∈ deningerAmb U :=
      deningerAmb_restrictOpen_le_amb (deningerAmb_mem_of_mem y)
    have : deningerExtend h.1 (y.1.1 : Fin n → ℂ) S = g S (y.1.1 : Fin n → ℂ) := hNeq _ hyN S
    rw [← this, deningerExtend_of_mem _ hyU]
    congr 1

instance deningerFormDbar_epi (Ω : Opens (Fin n → ℂ)) (q : ℕ) :
    Epi (deningerFormDbar Ω q) :=
  (TopCat.Sheaf.isLocallySurjective_iff_epi _).1 (deningerFormDbar_locallySurjective Ω q)

/-- **The `q`-th step of the Dolbeault resolution is short exact.** -/
theorem deningerFormStep_shortExact (Ω : Opens (Fin n → ℂ)) (q : ℕ) :
    (deningerFormStep Ω q).ShortExact where
  exact := deningerFormStep_exact Ω q
  mono_f := deningerFormIncl_mono Ω q
  epi_g := deningerFormDbar_epi Ω q

end Epi

end RHTower
