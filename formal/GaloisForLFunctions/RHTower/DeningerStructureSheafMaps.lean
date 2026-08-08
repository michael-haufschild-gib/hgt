import GaloisForLFunctions.RHTower.DeningerDivisorInclusion
import GaloisForLFunctions.RHTower.DeningerDolbeaultSheaf

/-!
# Multiplication by a coordinate and restriction to its divisor

Two morphisms of the structure sheaf of a domain carry the whole content of the ideal sequence of a
coordinate divisor.  Multiplication by a coordinate is an endomorphism of the sheaf of holomorphic
functions, because the coordinate is holomorphic and the Dolbeault operator obeys the Leibniz rule.
Restriction to the divisor of that coordinate is a morphism to the direct image of the structure
sheaf of the divisor, because appending a zero commutes with the coordinate slices and so carries
local smooth models to local smooth models.

Their composite vanishes: a function multiplied by a coordinate vanishes on the divisor of that
coordinate.

* `RHTower.deningerCoordMul` : multiplication by a coordinate.
* `RHTower.deningerDivisorInclusion` : the divisor of the last coordinate, as a map of spaces.
* `RHTower.deningerDivisorRestrict` : restriction to the divisor.
* `RHTower.deningerCoordMul_comp_restrict` : the composite vanishes.
-/

namespace RHTower

open CategoryTheory TopologicalSpace Opposite TopCat Complex HTGeometry

section CoordinateMultiplication

variable {n : ℕ} {Ω : Opens (Fin n → ℂ)}

/-- Multiplication of a section by a coordinate. -/
def deningerCoordSection (i : Fin n) {U : Opens (deningerSpace Ω)}
    (f : ↥U → DeningerFormVal n) : ↥U → DeningerFormVal n :=
  fun x S => (x.1.1 : Fin n → ℂ) i * f x S

theorem deningerExtend_coordSection (i : Fin n) {U : Opens (deningerSpace Ω)}
    (f : ↥U → DeningerFormVal n) (z : Fin n → ℂ) (S : Finset (Fin n)) :
    deningerExtend (deningerCoordSection i f) z S = z i * deningerExtend f z S := by
  by_cases hz : z ∈ deningerAmb U
  · rw [deningerExtend_of_mem _ hz, deningerExtend_of_mem f hz]
    rfl
  · rw [deningerExtend, dif_neg hz, deningerExtend, dif_neg hz]
    show (0 : ℂ) = z i * 0
    rw [mul_zero]

theorem deningerFlip_extend_coordSection (i : Fin n) {U : Opens (deningerSpace Ω)}
    (f : ↥U → DeningerFormVal n) :
    deningerFlip (deningerExtend (deningerCoordSection i f))
      = coordSetForm i (deningerFlip (deningerExtend f)) :=
  funext fun S => funext fun z => deningerExtend_coordSection i f z S

theorem DeningerFormPred.coord {q : ℕ} (i : Fin n) {U : Opens (deningerSpace Ω)}
    {f : ↥U → DeningerFormVal n} (hf : DeningerFormPred q f) :
    DeningerFormPred q (deningerCoordSection i f) := by
  refine ⟨fun x S hS => ?_, fun x => ?_⟩
  · show (x.1.1 : Fin n → ℂ) i * f x S = 0
    rw [hf.1 x S hS, mul_zero]
  · obtain ⟨g, hg, hgd, hgeq⟩ := hf.2 x
    refine ⟨coordSetForm i g, hg.coord i, hgd.coord i, ?_⟩
    filter_upwards [hgeq] with z hz
    intro S
    rw [deningerExtend_coordSection, hz S]
    rfl

theorem DeningerClosedFormPred.coord {q : ℕ} (i : Fin n) {U : Opens (deningerSpace Ω)}
    {f : ↥U → DeningerFormVal n} (hf : DeningerClosedFormPred q f) :
    DeningerClosedFormPred q (deningerCoordSection i f) := by
  refine ⟨hf.1.coord i, fun x S => ?_⟩
  obtain ⟨g, hg, hgd, hgeq⟩ := hf.1.2 x
  have hcoordeq : ∀ᶠ z in nhds (x.1.1 : Fin n → ℂ), ∀ S,
      deningerExtend (deningerCoordSection i f) z S = coordSetForm i g S z := by
    filter_upwards [hgeq] with z hz
    intro S
    rw [deningerExtend_coordSection, hz S]
    rfl
  rw [deningerSetDbar_model hcoordeq S, setDbar_coordSetForm hg i S,
    coordSetForm_apply, ← deningerSetDbar_model hgeq S, hf.2 x S, mul_zero]

/-- **Multiplication by a coordinate, as an endomorphism of the sheaf of holomorphic functions.**
The coordinate is holomorphic, so the Leibniz rule makes the product of a holomorphic function with
it holomorphic again. -/
noncomputable def deningerCoordMul (Ω : Opens (Fin n → ℂ)) (q : ℕ) (i : Fin n) :
    deningerClosedFormSheaf Ω q ⟶ deningerClosedFormSheaf Ω q :=
  ⟨{ app := fun _ => AddCommGrpCat.ofHom
      { toFun := fun f => ⟨deningerCoordSection i f.1, f.2.coord i⟩
        map_zero' := Subtype.ext (funext fun x => funext fun S => by
          show (x.1.1 : Fin n → ℂ) i * 0 = 0
          rw [mul_zero])
        map_add' := fun a b => Subtype.ext (funext fun x => funext fun S => by
          show (x.1.1 : Fin n → ℂ) i * (a.1 x S + b.1 x S)
            = (x.1.1 : Fin n → ℂ) i * a.1 x S + (x.1.1 : Fin n → ℂ) i * b.1 x S
          rw [mul_add]) }
     naturality := fun _ _ _ => rfl }⟩

@[simp] theorem deningerCoordMul_app (Ω : Opens (Fin n → ℂ)) (q : ℕ) (i : Fin n)
    (U : Opens (deningerSpace Ω)) (f : ToType ((deningerClosedFormSheaf Ω q).1.obj (op U)))
    (x : ↥U) (S : Finset (Fin n)) :
    (((deningerCoordMul Ω q i).1.app (op U)) f).1 x S = (x.1.1 : Fin n → ℂ) i * f.1 x S := rfl

end CoordinateMultiplication

end RHTower

namespace RHTower

open CategoryTheory TopologicalSpace Opposite TopCat Complex HTGeometry

section DivisorRestriction

variable {n : ℕ} {Ω : Opens (Fin (n + 1) → ℂ)} {Ω' : Opens (Fin n → ℂ)}
  (hmap : ∀ w ∈ Ω', deningerDivisorMap w ∈ Ω)

/-- **The divisor of the last coordinate, as a map of spaces.** -/
noncomputable def deningerDivisorInclusion : deningerSpace Ω' ⟶ deningerSpace Ω :=
  TopCat.ofHom
    ⟨fun w => ⟨deningerDivisorMap w.1, hmap w.1 w.2⟩,
      Continuous.subtype_mk (continuous_deningerDivisorMap.comp continuous_subtype_val) _⟩

@[simp] theorem deningerDivisorInclusion_apply (w : deningerSpace Ω') :
    ((deningerDivisorInclusion hmap) w : Fin (n + 1) → ℂ) = deningerDivisorMap w.1 := rfl

/-- The value of a form on the divisor: only the empty index survives in degree zero. -/
def deningerRestrictVal (v : DeningerFormVal (n + 1)) : DeningerFormVal n :=
  fun S => if S = ∅ then v ∅ else 0

@[simp] theorem deningerRestrictVal_empty (v : DeningerFormVal (n + 1)) :
    deningerRestrictVal v ∅ = v ∅ := if_pos rfl

@[simp] theorem deningerRestrictVal_ne (v : DeningerFormVal (n + 1)) {S : Finset (Fin n)}
    (hS : S ≠ ∅) : deningerRestrictVal v S = 0 := if_neg hS

theorem deningerRestrictVal_zero :
    deningerRestrictVal (0 : DeningerFormVal (n + 1)) = 0 := by
  funext S
  by_cases hS : S = ∅
  · subst hS
    rw [deningerRestrictVal_empty]
    rfl
  · rw [deningerRestrictVal_ne _ hS]
    rfl

theorem deningerRestrictVal_add (v v' : DeningerFormVal (n + 1)) :
    deningerRestrictVal (v + v') = deningerRestrictVal v + deningerRestrictVal v' := by
  funext S
  by_cases hS : S = ∅
  · subst hS
    rw [deningerRestrictVal_empty]
    show v ∅ + v' ∅ = deningerRestrictVal v ∅ + deningerRestrictVal v' ∅
    rw [deningerRestrictVal_empty, deningerRestrictVal_empty]
  · rw [deningerRestrictVal_ne _ hS]
    show (0 : ℂ) = deningerRestrictVal v S + deningerRestrictVal v' S
    rw [deningerRestrictVal_ne _ hS, deningerRestrictVal_ne _ hS, add_zero]

/-- The restriction of a section to the divisor. -/
noncomputable def deningerRestrictSection {U : Opens (deningerSpace Ω)}
    (f : ↥U → DeningerFormVal (n + 1)) :
    ↥((Opens.map (deningerDivisorInclusion hmap)).obj U) → DeningerFormVal n :=
  fun y => deningerRestrictVal (f ⟨(deningerDivisorInclusion hmap) y.1, y.2⟩)

theorem deningerDivisorAmb_mem {U : Opens (deningerSpace Ω)} {w : Fin n → ℂ}
    (hw : w ∈ deningerAmb ((Opens.map (deningerDivisorInclusion hmap)).obj U)) :
    deningerDivisorMap w ∈ deningerAmb U := by
  obtain ⟨hwΩ, hwU⟩ := mem_deningerAmb.1 hw
  exact mem_deningerAmb.2 ⟨hmap w hwΩ, hwU⟩

theorem deningerExtend_restrictSection {U : Opens (deningerSpace Ω)}
    (f : ↥U → DeningerFormVal (n + 1)) {w : Fin n → ℂ}
    (hw : w ∈ deningerAmb ((Opens.map (deningerDivisorInclusion hmap)).obj U)) :
    deningerExtend (deningerRestrictSection hmap f) w
      = deningerRestrictVal (deningerExtend f (deningerDivisorMap w)) := by
  rw [deningerExtend_of_mem _ hw,
    deningerExtend_of_mem f (deningerDivisorAmb_mem hmap hw)]
  rfl

/-- A local model of a section pulls back to a local model of its restriction. -/
theorem deningerRestrictSection_model {U : Opens (deningerSpace Ω)}
    {f : ↥U → DeningerFormVal (n + 1)} {g : SetForm (n + 1)}
    (y : ↥((Opens.map (deningerDivisorInclusion hmap)).obj U))
    (hgeq : ∀ᶠ z in nhds (deningerDivisorMap (y.1.1 : Fin n → ℂ)), ∀ S,
      deningerExtend f z S = g S z) :
    ∀ᶠ w in nhds (y.1.1 : Fin n → ℂ), ∀ S,
      deningerExtend (deningerRestrictSection hmap f) w S = deningerDivisorPullback g S w := by
  have hopen : ∀ᶠ w in nhds (y.1.1 : Fin n → ℂ),
      w ∈ deningerAmb ((Opens.map (deningerDivisorInclusion hmap)).obj U) :=
    Filter.eventually_of_mem
      ((deningerAmb ((Opens.map (deningerDivisorInclusion hmap)).obj U)).2.mem_nhds
        (deningerAmb_mem_of_mem y)) fun _ hz => hz
  have hpull : ∀ᶠ w in nhds (y.1.1 : Fin n → ℂ), ∀ S,
      deningerExtend f (deningerDivisorMap w) S = g S (deningerDivisorMap w) :=
    (continuous_deningerDivisorMap.continuousAt).eventually hgeq
  filter_upwards [hopen, hpull] with w hwamb hwg
  intro S
  rw [deningerExtend_restrictSection hmap f hwamb]
  by_cases hS : S = ∅
  · subst hS
    rw [deningerRestrictVal_empty, deningerDivisorPullback_empty, hwg ∅]
  · rw [deningerRestrictVal_ne _ hS, deningerDivisorPullback_ne g hS]

theorem DeningerFormPred.divisorRestrict {U : Opens (deningerSpace Ω)}
    {f : ↥U → DeningerFormVal (n + 1)} (hf : DeningerFormPred 0 f) :
    DeningerFormPred 0 (deningerRestrictSection hmap f) := by
  refine ⟨fun y S hS => ?_, fun y => ?_⟩
  · exact deningerRestrictVal_ne _ (fun h => hS (by rw [h]; rfl))
  · obtain ⟨g, hg, hgd, hgeq⟩ := hf.2 ⟨(deningerDivisorInclusion hmap) y.1, y.2⟩
    exact ⟨deningerDivisorPullback g, deningerDivisorPullback_smooth hg,
      deningerDivisorPullback_deg g, deningerRestrictSection_model hmap y hgeq⟩

theorem DeningerClosedFormPred.divisorRestrict {U : Opens (deningerSpace Ω)}
    {f : ↥U → DeningerFormVal (n + 1)} (hf : DeningerClosedFormPred 0 f) :
    DeningerClosedFormPred 0 (deningerRestrictSection hmap f) := by
  refine ⟨hf.1.divisorRestrict hmap, fun y S => ?_⟩
  obtain ⟨g, hg, hgd, hgeq⟩ := hf.1.2 ⟨(deningerDivisorInclusion hmap) y.1, y.2⟩
  have hzero : ∀ k : Fin (n + 1),
      dzbarAt (g ∅) k (deningerDivisorMap (y.1.1 : Fin n → ℂ)) = 0 := by
    intro k
    have hmodel := deningerSetDbar_model hgeq {k}
    have hval : setDbar g {k} (deningerDivisorMap (y.1.1 : Fin n → ℂ)) = 0 := by
      have h0 := hf.2 ⟨(deningerDivisorInclusion hmap) y.1, y.2⟩ {k}
      rw [hmodel] at h0
      exact h0
    have hsum : setDbar g {k} (deningerDivisorMap (y.1.1 : Fin n → ℂ))
        = dzbarAt (g ∅) k (deningerDivisorMap (y.1.1 : Fin n → ℂ)) := by
      show (∑ j ∈ ({k} : Finset (Fin (n + 1))), insertSign j (({k} : Finset (Fin (n + 1))).erase j)
        * dzbarAt (g (({k} : Finset (Fin (n + 1))).erase j)) j
          (deningerDivisorMap (y.1.1 : Fin n → ℂ))) = _
      rw [Finset.sum_singleton, Finset.erase_singleton]
      show insertSign k (∅ : Finset (Fin (n + 1))) * _ = _
      rw [show insertSign k (∅ : Finset (Fin (n + 1))) = 1 from by
        show ((-1 : ℂ)) ^ ((∅ : Finset (Fin (n + 1))).filter (fun j => j < k)).card = 1
        rw [Finset.filter_empty, Finset.card_empty, pow_zero], one_mul]
    rw [hsum] at hval
    exact hval
  rw [deningerSetDbar_model (deningerRestrictSection_model hmap y hgeq) S,
    setDbar_deningerDivisorPullback]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : S.erase k = ∅
  · rw [if_pos hk, hzero k.castSucc, mul_zero]
  · rw [if_neg hk, mul_zero]

end DivisorRestriction

end RHTower

namespace RHTower

open CategoryTheory TopologicalSpace Opposite TopCat Complex HTGeometry

section RestrictMorphism

variable {n : ℕ} {Ω : Opens (Fin (n + 1) → ℂ)} {Ω' : Opens (Fin n → ℂ)}
  (hmap : ∀ w ∈ Ω', deningerDivisorMap w ∈ Ω)

/-- **Restriction to the divisor of the last coordinate**, as a morphism of the structure sheaf of
the domain to the direct image of the structure sheaf of the divisor. -/
noncomputable def deningerDivisorRestrict :
    deningerClosedFormSheaf Ω 0
      ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0}
          (deningerDivisorInclusion hmap)).obj (deningerClosedFormSheaf Ω' 0) :=
  ⟨{ app := fun _ => AddCommGrpCat.ofHom
      { toFun := fun f => ⟨deningerRestrictSection hmap f.1, f.2.divisorRestrict hmap⟩
        map_zero' := Subtype.ext (funext fun _ => deningerRestrictVal_zero)
        map_add' := fun _ _ => Subtype.ext (funext fun _ => deningerRestrictVal_add _ _) }
     naturality := fun _ _ _ => rfl }⟩

@[simp] theorem deningerDivisorRestrict_app (U : Opens (deningerSpace Ω))
    (f : ToType ((deningerClosedFormSheaf Ω 0).1.obj (op U)))
    (y : ↥((Opens.map (deningerDivisorInclusion hmap)).obj U)) (S : Finset (Fin n)) :
    (((deningerDivisorRestrict hmap).1.app (op U)) f).1 y S
      = deningerRestrictVal (f.1 ⟨(deningerDivisorInclusion hmap) y.1, y.2⟩) S := rfl

/-- **A function multiplied by the last coordinate vanishes on the divisor of that coordinate.**
This is the composite of the two morphisms of the ideal sequence. -/
theorem deningerCoordMul_comp_restrict :
    deningerCoordMul Ω 0 (Fin.last n) ≫ deningerDivisorRestrict hmap = 0 := by
  refine CategoryTheory.ObjectProperty.hom_ext _ ?_
  ext U f
  refine Subtype.ext (funext fun y => funext fun S => ?_)
  show deningerRestrictVal
      (deningerCoordSection (Fin.last n) f.1 ⟨(deningerDivisorInclusion hmap) y.1, y.2⟩) S = 0
  by_cases hS : S = ∅
  · subst hS
    rw [deningerRestrictVal_empty]
    show (deningerDivisorMap (y.1.1 : Fin n → ℂ)) (Fin.last n)
      * f.1 ⟨(deningerDivisorInclusion hmap) y.1, y.2⟩ ∅ = 0
    rw [deningerDivisorMap_last, zero_mul]
  · rw [deningerRestrictVal_ne _ hS]

end RestrictMorphism

end RHTower

namespace RHTower

open CategoryTheory TopologicalSpace Opposite TopCat Complex HTGeometry

section CoordinateMono

variable {n : ℕ} {Ω : Opens (Fin n → ℂ)}

/-- **A form killed by multiplication by a coordinate vanishes.**  Off the zero set of the
coordinate this is immediate; on it the value is a limit of values off it, because a form is
continuous. -/
theorem deningerCoordSection_eq_zero {q : ℕ} {i : Fin n} {U : Opens (deningerSpace Ω)}
    {f : ↥U → DeningerFormVal n} (hf : DeningerFormPred q f)
    (h0 : ∀ (x : ↥U) (S : Finset (Fin n)), (x.1.1 : Fin n → ℂ) i * f x S = 0)
    (x : ↥U) (S : Finset (Fin n)) : f x S = 0 := by
  by_cases hxi : (x.1.1 : Fin n → ℂ) i = 0
  · obtain ⟨g, N, hg, hgd, hNopen, hxN, hNeq⟩ := hf.exists_model_open x
    set c : Fin n → ℂ := (x.1.1 : Fin n → ℂ) with hc
    have hgz : ∀ z ∈ N ∩ (deningerAmb U : Set (Fin n → ℂ)), z i ≠ 0 → g S z = 0 := by
      intro z hz hzi
      have hval := hNeq z hz.1 S
      rw [← hval, deningerExtend_of_mem f hz.2]
      have hzero := h0 (deningerPt hz.2) S
      rw [deningerPt_val hz.2] at hzero
      exact (mul_eq_zero.1 hzero).resolve_left hzi
    have hupd : Function.update c i 0 = c := by
      funext k
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self, hxi]
      · rw [Function.update_of_ne hk]
    have hcontupd : Continuous (fun t : ℂ => Function.update c i t) :=
      continuous_const.update i continuous_id
    have hopen : IsOpen (N ∩ (deningerAmb U : Set (Fin n → ℂ))) :=
      hNopen.inter (deningerAmb U).2
    have hpre : ∀ᶠ t in nhds (0 : ℂ),
        Function.update c i t ∈ N ∩ (deningerAmb U : Set (Fin n → ℂ)) := by
      refine hcontupd.continuousAt.eventually_mem ?_
      rw [hupd]
      exact hopen.mem_nhds ⟨hxN, deningerAmb_mem_of_mem x⟩
    have hev : (fun _ : ℂ => (0 : ℂ))
        =ᶠ[nhdsWithin (0 : ℂ) {0}ᶜ] fun t => g S (Function.update c i t) := by
      filter_upwards [nhdsWithin_le_nhds hpre, self_mem_nhdsWithin] with t ht ht0
      refine (hgz _ ht ?_).symm
      rw [Function.update_self]
      exact ht0
    have h1 : Filter.Tendsto (fun t : ℂ => g S (Function.update c i t))
        (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds (g S c)) := by
      have hcw : ContinuousWithinAt (fun t : ℂ => g S (Function.update c i t)) {0}ᶜ 0 :=
        (((hg S).continuous.comp hcontupd).continuousAt).continuousWithinAt
      simpa only [ContinuousWithinAt, hupd] using hcw
    have h2 : Filter.Tendsto (fun t : ℂ => g S (Function.update c i t))
        (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds 0) := Filter.Tendsto.congr' hev tendsto_const_nhds
    have hgc : g S c = 0 := tendsto_nhds_unique h1 h2
    have hfx : deningerExtend f c S = g S c := hNeq c hxN S
    rw [deningerExtend_apply f x] at hfx
    rw [hfx, hgc]
  · exact (mul_eq_zero.1 (h0 x S)).resolve_left hxi

instance deningerCoordMul_mono (Ω : Opens (Fin n → ℂ)) (q : ℕ) (i : Fin n) :
    Mono (deningerCoordMul Ω q i) := by
  haveI : ∀ U, Mono ((deningerCoordMul Ω q i).1.app U) := by
    intro U
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b hab
    have h : ∀ (x : ↥(unop U)) (S : Finset (Fin n)),
        (x.1.1 : Fin n → ℂ) i * (a.1 x S - b.1 x S) = 0 := by
      intro x S
      have h1 : (ConcreteCategory.hom ((deningerCoordMul Ω q i).1.app U) a).1
          = (ConcreteCategory.hom ((deningerCoordMul Ω q i).1.app U) b).1 := by rw [hab]
      have h2 : (x.1.1 : Fin n → ℂ) i * a.1 x S = (x.1.1 : Fin n → ℂ) i * b.1 x S :=
        congrFun (congrFun h1 x) S
      rw [mul_sub, h2, sub_self]
    refine Subtype.ext (funext fun x => funext fun S => ?_)
    have hsub : (fun x : ↥(unop U) => fun S => a.1 x S - b.1 x S) = fun x => a.1 x - b.1 x := rfl
    have hpred : DeningerFormPred q (fun x : ↥(unop U) => a.1 x - b.1 x) := by
      have := DeningerFormPred.add q a.2.1 (DeningerFormPred.neg q b.2.1)
      exact this
    have := deningerCoordSection_eq_zero (i := i) (q := q) hpred (by
      intro x S
      exact h x S) x S
    have hzero : a.1 x S - b.1 x S = 0 := this
    exact sub_eq_zero.1 hzero
  haveI : Mono (deningerCoordMul Ω q i).1 := NatTrans.mono_of_mono_app _
  exact CategoryTheory.Sheaf.Hom.mono_of_presheaf_mono _ _ _

end CoordinateMono

end RHTower
