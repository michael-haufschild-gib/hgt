import Mathlib.CategoryTheory.Category.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
# Split-formation corner flatness and the vertical normal form

Split formations over a common recovered object are flat: the canonical comparisons
`T_{ji} = f_j p_i` compose strictly, so no canonical loop carries holonomy — every loop is the
local corner idempotent.  In the linear chart a split formation is canonically `X ⊕ ker p`, every
base-compatible comparison is uniquely the identity on the base together with a vertical transport,
every triangle defect is purely vertical and invisible to every reporter factoring through
recovery, and four organs obey an exact associativity conservation identity.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ## Arbitrary-category split formations -/

section Categorical

open CategoryTheory

variable {C : Type*} [Category C] {X : C} {ι : Type*} {Z : ι → C}
  (f : ∀ i, X ⟶ Z i) (p : ∀ i, Z i ⟶ X) (hsplit : ∀ i, f i ≫ p i = 𝟙 X)

/-- **`(SFH.2)`.**  The local corner idempotent of a split formation. -/
def cornerIdem (i : ι) : Z i ⟶ Z i := p i ≫ f i

/-- **`(SFH.2)`.**  The canonical comparison: recover, then re-form. -/
def cornerTransport (i j : ι) : Z i ⟶ Z j := p i ≫ f j

include hsplit

/-- **Theorem 1.1 `(SFH.3)`.** -/
theorem cornerIdem_idem (i : ι) :
    cornerIdem f p i ≫ cornerIdem f p i = cornerIdem f p i := by
  show (p i ≫ f i) ≫ (p i ≫ f i) = p i ≫ f i
  rw [Category.assoc, ← Category.assoc (f i) (p i) (f i), hsplit i, Category.id_comp]

/-- **Theorem 1.1 `(SFH.4)`.**  Canonical comparisons compose strictly: the corner is flat. -/
theorem cornerTransport_comp (i j k : ι) :
    cornerTransport f p i j ≫ cornerTransport f p j k = cornerTransport f p i k := by
  show (p i ≫ f j) ≫ (p j ≫ f k) = p i ≫ f k
  rw [Category.assoc, ← Category.assoc (f j) (p j) (f k), hsplit j, Category.id_comp]

/-- **Theorem 1.1 `(SFH.5)`.**  Every canonical loop is the local corner identity. -/
theorem cornerTransport_loop (i j : ι) :
    cornerTransport f p i j ≫ cornerTransport f p j i = cornerIdem f p i :=
  cornerTransport_comp f p hsplit i j i

/-- **Theorem 1.1 `(SFH.6)`.** -/
theorem cornerIdem_comp_cornerTransport (i j : ι) :
    cornerIdem f p i ≫ cornerTransport f p i j = cornerTransport f p i j := by
  show (p i ≫ f i) ≫ (p i ≫ f j) = p i ≫ f j
  rw [Category.assoc, ← Category.assoc (f i) (p i) (f j), hsplit i, Category.id_comp]

/-- **Theorem 1.1 `(SFH.6)`.** -/
theorem cornerTransport_comp_cornerIdem (i j : ι) :
    cornerTransport f p i j ≫ cornerIdem f p j = cornerTransport f p i j := by
  show (p i ≫ f j) ≫ (p j ≫ f j) = p i ≫ f j
  rw [Category.assoc, ← Category.assoc (f j) (p j) (f j), hsplit j, Category.id_comp]

end Categorical

/-! ## The linear split chart -/

section LinearChart

variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
  {Z : Type*} [AddCommGroup Z] [Module K Z]

/-- **`(SFH.7)`.**  The vertical fibre of a recovery map. -/
abbrev vertical (p : Z →ₗ[K] X) : Submodule K Z := LinearMap.ker p

variable (f : X →ₗ[K] Z) (p : Z →ₗ[K] X)

/-- **`(SFH.8)`.**  Assembling a base datum and a vertical datum. -/
def splitAssemble : (X × ↥(vertical p)) →ₗ[K] Z :=
  f.coprod (vertical p).subtype

@[simp] theorem splitAssemble_apply (t : X × ↥(vertical p)) :
    splitAssemble f p t = f t.1 + (t.2 : Z) := rfl

variable (hfp : p.comp f = LinearMap.id)

include hfp

theorem recover_form (x : X) : p (f x) = x := by
  have := congrArg (fun g : X →ₗ[K] X => g x) hfp
  exact this

/-- **`(SFH.9)`.**  Splitting a formed datum into base and vertical parts. -/
def splitSplit : Z →ₗ[K] (X × ↥(vertical p)) :=
  p.prod (LinearMap.codRestrict (vertical p) (LinearMap.id - f.comp p) (fun z => by
    show p (z - f (p z)) = 0
    rw [map_sub, recover_form f p hfp, sub_self]))

@[simp] theorem splitSplit_fst (z : Z) : (splitSplit f p hfp z).1 = p z := rfl

@[simp] theorem splitSplit_snd (z : Z) : ((splitSplit f p hfp z).2 : Z) = z - f (p z) := rfl

theorem splitAssemble_splitSplit (z : Z) : splitAssemble f p (splitSplit f p hfp z) = z := by
  rw [splitAssemble_apply, splitSplit_fst, splitSplit_snd]
  abel

theorem splitSplit_splitAssemble (t : X × ↥(vertical p)) :
    splitSplit f p hfp (splitAssemble f p t) = t := by
  refine Prod.ext ?_ (Subtype.ext ?_)
  · show p (f t.1 + (t.2 : Z)) = t.1
    have h0 : p (t.2 : Z) = 0 := t.2.2
    rw [map_add, recover_form f p hfp, h0, add_zero]
  · show (f t.1 + (t.2 : Z)) - f (p (f t.1 + (t.2 : Z))) = (t.2 : Z)
    have h0 : p (t.2 : Z) = 0 := t.2.2
    rw [map_add, recover_form f p hfp, h0, add_zero]
    abel

/-- **Lemma 2.1.**  A split formation is canonically the direct sum of base and vertical data. -/
def splitChart : Z ≃ₗ[K] (X × ↥(vertical p)) :=
  LinearEquiv.ofLinear (splitSplit f p hfp) (splitAssemble f p)
    (LinearMap.ext (splitSplit_splitAssemble f p hfp))
    (LinearMap.ext (splitAssemble_splitSplit f p hfp))

@[simp] theorem splitChart_apply (z : Z) : splitChart f p hfp z = splitSplit f p hfp z := rfl

end LinearChart

/-! ## Base-compatible comparisons and their vertical normal form -/

section Comparison

variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
  {Zi Zj Zk Zl : Type*}
  [AddCommGroup Zi] [Module K Zi] [AddCommGroup Zj] [Module K Zj]
  [AddCommGroup Zk] [Module K Zk] [AddCommGroup Zl] [Module K Zl]

/-- **`(SFH.11)`.**  A comparison preserving recovery and already-formed source data. -/
structure BaseCompatible (fi : X →ₗ[K] Zi) (pi : Zi →ₗ[K] X)
    (fj : X →ₗ[K] Zj) (pj : Zj →ₗ[K] X) (Cji : Zi →ₗ[K] Zj) : Prop where
  recover : pj.comp Cji = pi
  form : Cji.comp fi = fj

/-- The vertical projection of a split formation. -/
def verticalProj (f : X →ₗ[K] Zi) (p : Zi →ₗ[K] X) (hfp : p.comp f = LinearMap.id) :
    Zi →ₗ[K] ↥(vertical p) :=
  (LinearMap.snd K X ↥(vertical p)).comp (splitSplit f p hfp)

@[simp] theorem verticalProj_coe (f : X →ₗ[K] Zi) (p : Zi →ₗ[K] X)
    (hfp : p.comp f = LinearMap.id) (z : Zi) :
    ((verticalProj f p hfp z : ↥(vertical p)) : Zi) = z - f (p z) := rfl

variable {fi : X →ₗ[K] Zi} {pi : Zi →ₗ[K] X} {fj : X →ₗ[K] Zj} {pj : Zj →ₗ[K] X}
  {fk : X →ₗ[K] Zk} {pk : Zk →ₗ[K] X} {fl : X →ₗ[K] Zl} {pl : Zl →ₗ[K] X}

theorem BaseCompatible.recover_apply {Cji : Zi →ₗ[K] Zj}
    (h : BaseCompatible fi pi fj pj Cji) (z : Zi) : pj (Cji z) = pi z :=
  congrArg (fun g : Zi →ₗ[K] X => g z) h.recover

theorem BaseCompatible.form_apply {Cji : Zi →ₗ[K] Zj}
    (h : BaseCompatible fi pi fj pj Cji) (x : X) : Cji (fi x) = fj x :=
  congrArg (fun g : X →ₗ[K] Zj => g x) h.form

/-- **`(SFH.12)`.**  The vertical transport of a base-compatible comparison. -/
def verticalTransport {Cji : Zi →ₗ[K] Zj} (h : BaseCompatible fi pi fj pj Cji) :
    ↥(vertical pi) →ₗ[K] ↥(vertical pj) :=
  LinearMap.codRestrict (vertical pj) (Cji.comp (vertical pi).subtype)
    (fun v => by
      show pj (Cji (v : Zi)) = 0
      rw [h.recover_apply]
      exact v.2)

@[simp] theorem verticalTransport_coe {Cji : Zi →ₗ[K] Zj}
    (h : BaseCompatible fi pi fj pj Cji) (v : ↥(vertical pi)) :
    ((verticalTransport h v : ↥(vertical pj)) : Zj) = Cji (v : Zi) := rfl

/-- **Theorem 3.1 `(SFH.13)`.**  In the split charts, a base-compatible comparison is the identity
on the base together with its vertical transport. -/
theorem splitChart_comparison (hi : pi.comp fi = LinearMap.id) (hj : pj.comp fj = LinearMap.id)
    {Cji : Zi →ₗ[K] Zj} (h : BaseCompatible fi pi fj pj Cji) (x : X) (v : ↥(vertical pi)) :
    splitChart fj pj hj (Cji (splitAssemble fi pi (x, v))) = (x, verticalTransport h v) := by
  have hCz : Cji (fi x + (v : Zi)) = fj x + (Cji (v : Zi)) := by
    rw [map_add, h.form_apply]
  have hp : pj (Cji (fi x + (v : Zi))) = x := by
    rw [h.recover_apply, map_add, recover_form fi pi hi]
    have h0 : pi (v : Zi) = 0 := v.2
    rw [h0, add_zero]
  refine Prod.ext ?_ (Subtype.ext ?_)
  · exact hp
  · show Cji (fi x + (v : Zi)) - fj (pj (Cji (fi x + (v : Zi)))) = Cji (v : Zi)
    rw [hp, hCz]
    abel

/-- **Theorem 3.1, uniqueness.**  Any vertical map realizing the normal form is the restriction. -/
theorem verticalTransport_unique (hi : pi.comp fi = LinearMap.id)
    (hj : pj.comp fj = LinearMap.id) {Cji : Zi →ₗ[K] Zj} (h : BaseCompatible fi pi fj pj Cji)
    (L : ↥(vertical pi) →ₗ[K] ↥(vertical pj))
    (hL : ∀ x v, splitChart fj pj hj (Cji (splitAssemble fi pi (x, v))) = (x, L v)) :
    L = verticalTransport h := by
  refine LinearMap.ext fun v => ?_
  have h1 := hL 0 v
  have h2 := splitChart_comparison hi hj h 0 v
  rw [h1] at h2
  simpa using (Prod.ext_iff.mp h2).2

/-- **Corollary 3.2.**  A comparison is the canonical recover-then-form map exactly when its
vertical transport vanishes. -/
theorem verticalTransport_eq_zero_iff (hi : pi.comp fi = LinearMap.id)
    {Cji : Zi →ₗ[K] Zj} (h : BaseCompatible fi pi fj pj Cji) :
    verticalTransport h = 0 ↔ Cji = fj.comp pi := by
  constructor
  · intro hzero
    refine LinearMap.ext fun z => ?_
    have hv : Cji (z - fi (pi z)) = 0 := by
      have hmem : z - fi (pi z) ∈ vertical pi := by
        show pi (z - fi (pi z)) = 0
        rw [map_sub, recover_form fi pi hi, sub_self]
      have := congrArg (fun g : ↥(vertical pi) →ₗ[K] ↥(vertical pj) => (g ⟨_, hmem⟩ : Zj)) hzero
      exact this
    have hz : Cji z = Cji (fi (pi z)) := by
      have := congrArg (fun w => w + Cji (fi (pi z))) hv
      rw [← map_add] at this
      simpa using this
    rw [hz, h.form_apply]
    rfl
  · intro hC
    refine LinearMap.ext fun v => Subtype.ext ?_
    show Cji (v : Zi) = 0
    rw [hC]
    have h0 : pi (v : Zi) = 0 := v.2
    show fj (pi (v : Zi)) = 0
    rw [h0, map_zero]

/-- Base-compatible comparisons compose. -/
theorem BaseCompatible.comp {Cji : Zi →ₗ[K] Zj} {Ckj : Zj →ₗ[K] Zk}
    (hji : BaseCompatible fi pi fj pj Cji) (hkj : BaseCompatible fj pj fk pk Ckj) :
    BaseCompatible fi pi fk pk (Ckj.comp Cji) := by
  constructor
  · refine LinearMap.ext fun z => ?_
    show pk (Ckj (Cji z)) = pi z
    rw [hkj.recover_apply, hji.recover_apply]
  · refine LinearMap.ext fun x => ?_
    show Ckj (Cji (fi x)) = fk x
    rw [hji.form_apply, hkj.form_apply]

/-- The identity is base-compatible. -/
theorem baseCompatible_id : BaseCompatible fi pi fi pi (LinearMap.id : Zi →ₗ[K] Zi) :=
  ⟨LinearMap.comp_id _, LinearMap.id_comp _⟩

/-- **Corollary 4.2 `(SFH.17)`.**  Vertical transport is functorial, so along any loop of
base-compatible comparisons the recovered base returns exactly and the vertical part is the
ordered product of the edge transports. -/
theorem verticalTransport_comp {Cji : Zi →ₗ[K] Zj} {Ckj : Zj →ₗ[K] Zk}
    (hji : BaseCompatible fi pi fj pj Cji) (hkj : BaseCompatible fj pj fk pk Ckj) :
    verticalTransport (hji.comp hkj)
      = (verticalTransport hkj).comp (verticalTransport hji) :=
  LinearMap.ext fun _ => Subtype.ext rfl

theorem verticalTransport_id :
    verticalTransport (baseCompatible_id (fi := fi) (pi := pi)) = LinearMap.id :=
  LinearMap.ext fun _ => Subtype.ext rfl

/-! ## Three-organ fusion defect -/

/-- **`(SFH.14)`.**  The triangle defect of three comparisons. -/
def fusionDefect (Cji : Zi →ₗ[K] Zj) (Ckj : Zj →ₗ[K] Zk) (Cki : Zi →ₗ[K] Zk) :
    Zi →ₗ[K] Zk := Ckj.comp Cji - Cki

/-- **Theorem 4.1 `(SFH.16)`.**  The defect is invisible to recovery. -/
theorem recover_comp_fusionDefect {Cji : Zi →ₗ[K] Zj} {Ckj : Zj →ₗ[K] Zk} {Cki : Zi →ₗ[K] Zk}
    (hji : BaseCompatible fi pi fj pj Cji) (hkj : BaseCompatible fj pj fk pk Ckj)
    (hki : BaseCompatible fi pi fk pk Cki) :
    pk.comp (fusionDefect Cji Ckj Cki) = 0 := by
  refine LinearMap.ext fun z => ?_
  show pk (Ckj (Cji z) - Cki z) = 0
  rw [map_sub, hkj.recover_apply, hji.recover_apply, hki.recover_apply, sub_self]

/-- **Theorem 4.1 `(SFH.16)`.**  The defect annihilates already-formed source data. -/
theorem fusionDefect_comp_form {Cji : Zi →ₗ[K] Zj} {Ckj : Zj →ₗ[K] Zk} {Cki : Zi →ₗ[K] Zk}
    (hji : BaseCompatible fi pi fj pj Cji) (hkj : BaseCompatible fj pj fk pk Ckj)
    (hki : BaseCompatible fi pi fk pk Cki) :
    (fusionDefect Cji Ckj Cki).comp fi = 0 := by
  refine LinearMap.ext fun x => ?_
  show Ckj (Cji (fi x)) - Cki (fi x) = 0
  rw [hji.form_apply, hkj.form_apply, hki.form_apply, sub_self]

/-- **Theorem 4.1.**  Every reporter factoring through recovery annihilates the defect. -/
theorem reporter_comp_fusionDefect {W : Type*} [AddCommGroup W] [Module K W]
    {Cji : Zi →ₗ[K] Zj} {Ckj : Zj →ₗ[K] Zk} {Cki : Zi →ₗ[K] Zk}
    (hji : BaseCompatible fi pi fj pj Cji) (hkj : BaseCompatible fj pj fk pk Ckj)
    (hki : BaseCompatible fi pi fk pk Cki) (rbar : X →ₗ[K] W) :
    (rbar.comp pk).comp (fusionDefect Cji Ckj Cki) = 0 := by
  rw [LinearMap.comp_assoc, recover_comp_fusionDefect hji hkj hki, LinearMap.comp_zero]

/-- **Theorem 4.1 `(SFH.15)`.**  In the split charts the defect is purely vertical, with vertical
part the associativity defect of the vertical transports. -/
theorem splitChart_fusionDefect (hi : pi.comp fi = LinearMap.id)
    (hk : pk.comp fk = LinearMap.id) (hj : pj.comp fj = LinearMap.id)
    {Cji : Zi →ₗ[K] Zj} {Ckj : Zj →ₗ[K] Zk} {Cki : Zi →ₗ[K] Zk}
    (hji : BaseCompatible fi pi fj pj Cji) (hkj : BaseCompatible fj pj fk pk Ckj)
    (hki : BaseCompatible fi pi fk pk Cki) (x : X) (v : ↥(vertical pi)) :
    splitChart fk pk hk (fusionDefect Cji Ckj Cki (splitAssemble fi pi (x, v)))
      = (0, verticalTransport hkj (verticalTransport hji v) - verticalTransport hki v) := by
  have hcomp := splitChart_comparison hi hj hji x v
  have hz : Cji (splitAssemble fi pi (x, v)) = splitAssemble fj pj (x, verticalTransport hji v) := by
    have hcast := congrArg (splitAssemble fj pj) hcomp
    rw [splitChart_apply, splitAssemble_splitSplit fj pj hj] at hcast
    exact hcast
  have h1 := splitChart_comparison hj hk hkj x (verticalTransport hji v)
  rw [← hz] at h1
  have h2 := splitChart_comparison hi hk hki x v
  refine Prod.ext ?_ (Subtype.ext ?_)
  · show pk (Ckj (Cji (splitAssemble fi pi (x, v))) - Cki (splitAssemble fi pi (x, v))) = 0
    rw [map_sub]
    have e1 : pk (Ckj (Cji (splitAssemble fi pi (x, v)))) = x := (Prod.ext_iff.mp h1).1
    have e2 : pk (Cki (splitAssemble fi pi (x, v))) = x := (Prod.ext_iff.mp h2).1
    rw [e1, e2, sub_self]
  · have e1 : pk (Ckj (Cji (splitAssemble fi pi (x, v)))) = x := (Prod.ext_iff.mp h1).1
    have e2 : pk (Cki (splitAssemble fi pi (x, v))) = x := (Prod.ext_iff.mp h2).1
    show (Ckj (Cji (splitAssemble fi pi (x, v))) - Cki (splitAssemble fi pi (x, v)))
      - fk (pk (Ckj (Cji (splitAssemble fi pi (x, v))) - Cki (splitAssemble fi pi (x, v))))
      = Ckj (Cji (v : Zi)) - Cki (v : Zi)
    rw [map_sub, e1, e2, sub_self, map_zero, sub_zero]
    have s1 : Ckj (Cji (splitAssemble fi pi (x, v))) = fk x + Ckj (Cji (v : Zi)) := by
      have := (Prod.ext_iff.mp h1).2
      have hval := congrArg (fun w : ↥(vertical pk) => (w : Zk)) this
      show Ckj (Cji (splitAssemble fi pi (x, v))) = fk x + Ckj (Cji (v : Zi))
      simp only [splitChart, LinearEquiv.ofLinear_apply, splitSplit_snd,
        verticalTransport_coe] at hval
      rw [e1] at hval
      linear_combination (norm := abel) hval
    have s2 : Cki (splitAssemble fi pi (x, v)) = fk x + Cki (v : Zi) := by
      have := (Prod.ext_iff.mp h2).2
      have hval := congrArg (fun w : ↥(vertical pk) => (w : Zk)) this
      simp only [splitChart, LinearEquiv.ofLinear_apply, splitSplit_snd,
        verticalTransport_coe] at hval
      rw [e2] at hval
      linear_combination (norm := abel) hval
    rw [s1, s2]
    abel

/-! ## Four-organ conservation -/

/-- **Theorem 5.1 `(SFH.18)`.**  Once three triangle defects and the edge transports are fixed,
the fourth defect is constrained. -/
theorem fourOrgan_conservation (Cji : Zi →ₗ[K] Zj) (Ckj : Zj →ₗ[K] Zk) (Cki : Zi →ₗ[K] Zk)
    (Clk : Zk →ₗ[K] Zl) (Clj : Zj →ₗ[K] Zl) (Cli : Zi →ₗ[K] Zl) :
    Clk.comp (fusionDefect Cji Ckj Cki) + fusionDefect Cki Clk Cli
      = (fusionDefect Ckj Clk Clj).comp Cji + fusionDefect Cji Clj Cli := by
  refine LinearMap.ext fun z => ?_
  show Clk (Ckj (Cji z) - Cki z) + (Clk (Cki z) - Cli z)
    = (Clk (Ckj (Cji z)) - Clj (Cji z)) + (Clj (Cji z) - Cli z)
  rw [map_sub]
  abel

/-! ## Realizing an arbitrary vertical transport -/

/-- A comparison with prescribed vertical transport. -/
def comparisonOfVertical (fj : X →ₗ[K] Zj) (hi : pi.comp fi = LinearMap.id)
    (L : ↥(vertical pi) →ₗ[K] ↥(vertical pj)) : Zi →ₗ[K] Zj :=
  fj.comp pi + (vertical pj).subtype.comp (L.comp (verticalProj fi pi hi))

theorem baseCompatible_comparisonOfVertical (hi : pi.comp fi = LinearMap.id)
    (hj : pj.comp fj = LinearMap.id) (L : ↥(vertical pi) →ₗ[K] ↥(vertical pj)) :
    BaseCompatible fi pi fj pj (comparisonOfVertical fj hi L) := by
  constructor
  · refine LinearMap.ext fun z => ?_
    show pj (fj (pi z) + ((L (verticalProj fi pi hi z) : ↥(vertical pj)) : Zj)) = pi z
    have h0 : pj ((L (verticalProj fi pi hi z) : ↥(vertical pj)) : Zj) = 0 :=
      (L (verticalProj fi pi hi z)).2
    rw [map_add, recover_form fj pj hj, h0, add_zero]
  · refine LinearMap.ext fun x => ?_
    show fj (pi (fi x)) + ((L (verticalProj fi pi hi (fi x)) : ↥(vertical pj)) : Zj) = fj x
    have hv : verticalProj fi pi hi (fi x) = 0 := by
      refine Subtype.ext ?_
      show fi x - fi (pi (fi x)) = 0
      rw [recover_form fi pi hi, sub_self]
    rw [hv, map_zero, recover_form fi pi hi]
    show fj x + ((0 : ↥(vertical pj)) : Zj) = fj x
    rw [ZeroMemClass.coe_zero, add_zero]

/-- **Loop E.**  Every vertical transport is realized, so vertical holonomy alone selects
nothing. -/
theorem verticalTransport_comparisonOfVertical (hi : pi.comp fi = LinearMap.id)
    (hj : pj.comp fj = LinearMap.id) (L : ↥(vertical pi) →ₗ[K] ↥(vertical pj)) :
    verticalTransport (baseCompatible_comparisonOfVertical hi hj L) = L := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  show fj (pi (v : Zi)) + ((L (verticalProj fi pi hi (v : Zi)) : ↥(vertical pj)) : Zj)
    = ((L v : ↥(vertical pj)) : Zj)
  have h0 : pi (v : Zi) = 0 := v.2
  have hv : verticalProj fi pi hi (v : Zi) = v := by
    refine Subtype.ext ?_
    show (v : Zi) - fi (pi (v : Zi)) = (v : Zi)
    rw [h0, map_zero, sub_zero]
  rw [hv, h0, map_zero, zero_add]

end Comparison

end GaloisForLFunctions.HTGeometry
