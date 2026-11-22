import GaloisForLFunctions.HTGeometry.FinsetCechDatum
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! Čech cochains of fixed degree form a cochain complex of abelian groups. -/

noncomputable section

open CategoryTheory HTGeometry

namespace HTGeometry.FinsetCechDatum

universe v

variable {ι : Type v} [DecidableEq ι] [LinearOrder ι]

/-- Cochains supported on the intersections indexed by subsets of size `n+1`. -/
def degreeCochains (D : FinsetCechDatum.{v} ι) (n : ℕ) : AddSubgroup D.Cochain where
  carrier := {c | D.IsDeg c n}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro c b hc hb a ha
    change c a + b a = 0
    rw [hc a ha, hb a ha, zero_add]
  neg_mem' := by
    intro c hc a ha
    change -(c a) = 0
    rw [hc a ha, neg_zero]

private def degreeDifferential (D : FinsetCechDatum.{v} ι) (n : ℕ) :
    AddCommGrpCat.of (D.degreeCochains n) ⟶ AddCommGrpCat.of (D.degreeCochains (n + 1)) :=
  AddCommGrpCat.ofHom
    { toFun := fun c => ⟨D.d c.1, D.d_isDeg c.2⟩
      map_zero' := Subtype.ext D.d_zero
      map_add' := fun c b => Subtype.ext (D.d_add c.1 b.1) }

/-- The unaugmented cochain complex associated to the Čech datum. -/
def cochainComplex (D : FinsetCechDatum.{v} ι) : CochainComplex AddCommGrpCat.{v} ℕ :=
  CochainComplex.of (fun n => AddCommGrpCat.of (D.degreeCochains n)) (degreeDifferential D) (by
    intro n
    apply AddCommGrpCat.ext
    intro c
    exact Subtype.ext (D.d_d c.1))

theorem cochainComplex_d_apply (D : FinsetCechDatum.{v} ι) (n : ℕ) (c : D.degreeCochains n) :
    D.cochainComplex.d n (n + 1) c = ⟨D.d c.1, D.d_isDeg c.2⟩ := by
  change CochainComplex.of.d _ (degreeDifferential D) n (n + 1) c = _
  rw [CochainComplex.of_d]
  rfl

variable {D E : FinsetCechDatum.{v} ι}

private def Hom.degreeMap (φ : D.Hom E) (n : ℕ) :
    AddCommGrpCat.of (D.degreeCochains n) ⟶ AddCommGrpCat.of (E.degreeCochains n) :=
  AddCommGrpCat.ofHom
    { toFun := fun c => ⟨φ.onCochain c.1, φ.onCochain_isDeg c.2⟩
      map_zero' := Subtype.ext (funext fun a => map_zero (φ.app a))
      map_add' := fun c b => Subtype.ext (funext fun a => map_add (φ.app a) (c.1 a) (b.1 a)) }

/-- A morphism of Čech data induces a morphism of their cochain complexes. -/
def Hom.cochainMap (φ : D.Hom E) : D.cochainComplex ⟶ E.cochainComplex :=
  CochainComplex.ofHom (φ.degreeMap) (by
    intro n
    change φ.degreeMap n ≫ CochainComplex.of.d _ (degreeDifferential E) n (n + 1) =
      CochainComplex.of.d _ (degreeDifferential D) n (n + 1) ≫ φ.degreeMap (n + 1)
    rw [CochainComplex.of_d, CochainComplex.of_d]
    apply AddCommGrpCat.ext
    intro c
    exact Subtype.ext (φ.d_onCochain c.1))

theorem cochainComplex_exactAt (D : FinsetCechDatum.{v} ι) {n : ℕ}
    (h : D.ExactAt (n + 1)) : D.cochainComplex.ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  apply (ShortComplex.ab_exact_iff_function_exact _).mpr
  intro c
  constructor
  · intro hc
    change D.cochainComplex.d (n + 1) (n + 2) c = 0 at hc
    rw [cochainComplex_d_apply] at hc
    have hc' : D.d c.1 = 0 := congrArg Subtype.val hc
    obtain ⟨b, hb, he⟩ := h c.1 c.2 hc'
    refine ⟨⟨b, hb⟩, ?_⟩
    change D.cochainComplex.d n (n + 1) ⟨b, hb⟩ = c
    rw [cochainComplex_d_apply]
    exact Subtype.ext he
  · rintro ⟨b, rfl⟩
    change D.cochainComplex.d (n + 1) (n + 2) (D.cochainComplex.d n (n + 1) b) = 0
    rw [cochainComplex_d_apply, cochainComplex_d_apply]
    exact Subtype.ext (D.d_d b.1)

variable {Q : FinsetCechDatum.{v} ι}

/-- Short exactness on nonempty intersections gives a short exact sequence of complexes. -/
theorem shortExact_cochainMap (f : D.Hom E) (g : E.Hom Q)
    (hcomp : ∀ a (x : D.obj a), g.app a (f.app a x) = 0)
    (hinj : ∀ a, a.Nonempty → Function.Injective (f.app a))
    (hexact : ∀ a, a.Nonempty → Function.Exact (f.app a) (g.app a))
    (hsurj : ∀ a, a.Nonempty → Function.Surjective (g.app a)) :
    (ShortComplex.mk f.cochainMap g.cochainMap (by
      ext n c
      exact Subtype.ext (funext fun a => hcomp a (c.1 a)))).ShortExact := by
  classical
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine ShortComplex.ShortExact.mk' ((ShortComplex.ab_exact_iff_function_exact _).mpr ?_)
    ((AddCommGrpCat.mono_iff_injective _).mpr ?_) ((AddCommGrpCat.epi_iff_surjective _).mpr ?_)
  · intro c
    constructor
    · intro hc
      have h (a : Finset ι) (ha : a.card = n + 1) : ∃ b, f.app a b = c.1 a :=
        (hexact a (Finset.card_pos.mp (by omega)) _).mp
          (congrFun (congrArg Subtype.val hc) a)
      choose b hb using h
      let x : D.Cochain := fun a => if ha : a.card = n + 1 then b a ha else 0
      refine ⟨⟨x, fun a ha => dif_neg ha⟩, Subtype.ext (funext fun a => ?_)⟩
      change f.app a (x a) = c.1 a
      by_cases ha : a.card = n + 1
      · simpa only [x, dif_pos ha] using hb a ha
      · simp only [x, dif_neg ha, map_zero, c.2 a ha]
    · rintro ⟨b, rfl⟩
      exact Subtype.ext (funext fun a => hcomp a (b.1 a))
  · intro b c h
    apply Subtype.ext
    funext a
    by_cases ha : a.card = n + 1
    · exact hinj a (Finset.card_pos.mp (by omega)) (congrFun (congrArg Subtype.val h) a)
    · rw [b.2 a ha, c.2 a ha]
  · intro c
    have h (a : Finset ι) (ha : a.card = n + 1) : ∃ b, g.app a b = c.1 a :=
      hsurj a (Finset.card_pos.mp (by omega)) _
    choose b hb using h
    let x : E.Cochain := fun a => if ha : a.card = n + 1 then b a ha else 0
    refine ⟨⟨x, fun a ha => dif_neg ha⟩, Subtype.ext (funext fun a => ?_)⟩
    change g.app a (x a) = c.1 a
    by_cases ha : a.card = n + 1
    · simpa only [x, dif_pos ha] using hb a ha
    · simp only [x, dif_neg ha, map_zero, c.2 a ha]

end HTGeometry.FinsetCechDatum
