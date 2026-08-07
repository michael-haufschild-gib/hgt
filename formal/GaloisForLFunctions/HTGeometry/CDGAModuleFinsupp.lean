import GaloisForLFunctions.HTGeometry.CDGACellInvariance
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Direct sums of copies of a differential graded module

The finitely supported functions from an index type into a differential graded module form a
differential graded module, with every structure map applied coefficientwise.  A morphism which is a
full quasi-isomorphism induces one on the direct sums: the conditions are coefficientwise, and a
choice of witness which vanishes on the zero coefficient keeps the supports finite.

* `HTGeometry.finsuppModule` : the direct sum.
* `HTGeometry.finsuppMap` : functoriality.
* `HTGeometry.finsuppMap_isQuasiIsoFull` : a direct sum of full quasi-isomorphisms.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]

/-- A choice of witness which sends zero to zero. -/
noncomputable def pick {α : Type*} {β : Type*} [Zero α] [Zero β] (Rel : α → β → Prop)
    (a : α) : β :=
  open scoped Classical in
  if a = 0 then 0 else if h : ∃ b, Rel a b then Classical.choose h else 0

@[simp] theorem pick_zero {α β : Type*} [Zero α] [Zero β] (Rel : α → β → Prop) :
    pick Rel (0 : α) = 0 := by
  rw [pick, if_pos rfl]

theorem pick_spec {α β : Type*} [Zero α] [Zero β] {Rel : α → β → Prop} {a : α}
    (h : ∃ b, Rel a b) (h0 : Rel 0 0) : Rel a (pick Rel a) := by
  by_cases ha : a = 0
  · subst ha
    rw [pick_zero]
    exact h0
  · classical
    rw [pick, if_neg ha, dif_pos h]
    exact Classical.choose_spec h

section Module

variable (P : CDGAModuleStructure A M) (κ : Type w)

/-- **The direct sum of copies of a differential graded module.**  Every structure map is applied
coefficientwise. -/
noncomputable def finsuppModule : CDGAModuleStructure A (fun n => κ →₀ M n) where
  act h x z := Finsupp.mapRange.linearMap (P.actₗ h x) z
  d n z := Finsupp.mapRange.linearMap (P.dₗ n) z
  act_add_left h x x' z := by
    refine Finsupp.ext fun i => ?_
    show P.act h (x + x') (z i) = P.act h x (z i) + P.act h x' (z i)
    exact P.act_add_left h x x' (z i)
  act_add_right h x z z' := map_add _ z z'
  act_smul_left h c x z := by
    refine Finsupp.ext fun i => ?_
    show P.act h (c • x) (z i) = c • P.act h x (z i)
    exact P.act_smul_left h c x (z i)
  act_smul_right h c x z := map_smul _ c z
  act_assoc h₁ h₂ h₃ h₄ x y z := by
    refine Finsupp.ext fun i => ?_
    show P.act h₂ (A.mul h₁ x y) (z i) = P.act h₄ x (P.act h₃ y (z i))
    exact P.act_assoc h₁ h₂ h₃ h₄ x y (z i)
  d_add n z z' := map_add _ z z'
  d_smul n c z := map_smul _ c z
  d_d n z := by
    refine Finsupp.ext fun i => ?_
    show P.d (n + 1) (P.d n (z i)) = 0
    exact P.d_d n (z i)
  d_act h x z := by
    refine Finsupp.ext fun i => ?_
    show P.d _ (P.act h x (z i))
      = P.act _ (A.d _ x) (z i) + (((-1 : R)) ^ _ • Finsupp.mapRange.linearMap
        (P.actₗ (show _ + (_ + 1) = _ + 1 by omega) x)
        (Finsupp.mapRange.linearMap (P.dₗ _) z)) i
    rw [P.d_act h x (z i)]
    rfl

@[simp] theorem finsuppModule_d (n : ℕ) (z : κ →₀ M n) (i : κ) :
    ((finsuppModule P κ).d n z) i = P.d n (z i) := rfl

@[simp] theorem finsuppModule_act {a b n : ℕ} (h : a + b = n) (x : X a) (z : κ →₀ M b) (i : κ) :
    ((finsuppModule P κ).act h x z) i = P.act h x (z i) := rfl

/-- A finitely supported family is a cocycle exactly when each coefficient is. -/
theorem mem_finsupp_cocycles {n : ℕ} {z : κ →₀ M n} :
    z ∈ (finsuppModule P κ).cocycles n ↔ ∀ i, z i ∈ P.cocycles n := by
  constructor
  · intro hz i
    have h : (finsuppModule P κ).d n z = 0 := hz
    show P.d n (z i) = 0
    rw [← finsuppModule_d P κ n z i, h]
    rfl
  · intro hz
    show (finsuppModule P κ).d n z = 0
    refine Finsupp.ext fun i => ?_
    exact hz i

end Module

section Functoriality

variable {P : CDGAModuleStructure A M} {P' : CDGAModuleStructure A M'}

/-- **The direct sum is functorial.** -/
noncomputable def finsuppMap (φ : CDGAModuleHom P P') (κ : Type w) :
    CDGAModuleHom (finsuppModule P κ) (finsuppModule P' κ) where
  toFun n z := Finsupp.mapRange.linearMap (φ.mapₗ n) z
  map_add n z z' := map_add _ z z'
  map_smul n c z := map_smul _ c z
  map_act h x z := by
    refine Finsupp.ext fun i => ?_
    show φ.toFun _ (P.act h x (z i)) = P'.act h x (φ.toFun _ (z i))
    exact φ.map_act h x (z i)
  map_d n z := by
    refine Finsupp.ext fun i => ?_
    show φ.toFun (n + 1) (P.d n (z i)) = P'.d n (φ.toFun n (z i))
    exact φ.map_d n (z i)

@[simp] theorem finsuppMap_apply (φ : CDGAModuleHom P P') (κ : Type w) (n : ℕ) (z : κ →₀ M n)
    (i : κ) : ((finsuppMap φ κ).toFun n z) i = φ.toFun n (z i) := rfl

end Functoriality

section QuasiIso

variable {P : CDGAModuleStructure A M} {P' : CDGAModuleStructure A M'}
  (φ : CDGAModuleHom P P') (κ : Type w)

/-- Coefficientwise cocycles assemble into a cocycle. -/
theorem finsupp_cocycle_of_forall {n : ℕ} (z : κ →₀ M n) (hz : ∀ i, P.d n (z i) = 0) :
    z ∈ (finsuppModule P κ).cocycles n :=
  (mem_finsupp_cocycles P κ).2 hz

theorem finsuppMap_cocyclesMap_zero_bijective (hφ : φ.IsQuasiIsoFull) :
    Function.Bijective ((finsuppMap φ κ).cocyclesMap 0) := by
  constructor
  · intro z z' hzz
    refine Subtype.ext (Finsupp.ext fun i => ?_)
    have h : φ.toFun 0 ((z : κ →₀ M 0) i) = φ.toFun 0 ((z' : κ →₀ M 0) i) :=
      congrFun (congrArg (fun y : κ →₀ M' 0 => (y : κ → M' 0)) (congrArg Subtype.val hzz)) i
    have hz := (mem_finsupp_cocycles P κ).1 z.2 i
    have hz' := (mem_finsupp_cocycles P κ).1 z'.2 i
    exact congrArg Subtype.val (hφ.1.1 (a₁ := ⟨_, hz⟩) (a₂ := ⟨_, hz'⟩) (Subtype.ext h))
  · intro w
    classical
    set Rel : M' 0 → M 0 → Prop :=
      fun y m => m ∈ P.cocycles 0 ∧ φ.toFun 0 m = y with hRel
    have h0 : Rel 0 0 := ⟨(P.dₗ 0).map_zero, (φ.mapₗ 0).map_zero⟩
    have hex : ∀ i, Rel ((w : κ →₀ M' 0) i) (pick Rel ((w : κ →₀ M' 0) i)) := by
      intro i
      refine pick_spec ?_ h0
      obtain ⟨m, hm⟩ := hφ.1.2 ⟨(w : κ →₀ M' 0) i, (mem_finsupp_cocycles P' κ).1 w.2 i⟩
      exact ⟨(m : M 0), m.2, congrArg Subtype.val hm⟩
    refine ⟨⟨Finsupp.mapRange (pick Rel) (pick_zero Rel) (w : κ →₀ M' 0),
      (mem_finsupp_cocycles P κ).2 fun i => ?_⟩, ?_⟩
    · rw [Finsupp.mapRange_apply]
      exact (hex i).1
    · refine Subtype.ext (Finsupp.ext fun i => ?_)
      show φ.toFun 0 (Finsupp.mapRange (pick Rel) (pick_zero Rel) (w : κ →₀ M' 0) i) = _
      rw [Finsupp.mapRange_apply]
      exact (hex i).2

theorem finsuppMap_isQuasiIso (hφ : φ.IsQuasiIsoFull) : (finsuppMap φ κ).IsQuasiIso := by
  intro n
  classical
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun c hc => ?_
    refine Quotient.inductionOn' c ?_ hc
    intro z hz
    obtain ⟨w, hw⟩ : ∃ w : κ →₀ M' n,
        ((finsuppMap φ κ).toFun (n + 1) (z : κ →₀ M (n + 1))) = (finsuppModule P' κ).d n w :=
      (Submodule.Quotient.mk_eq_zero _).1 hz
    have hzc := (mem_finsupp_cocycles P κ).1 z.2
    have hcob : ∀ i, ∃ y : M n, (z : κ →₀ M (n + 1)) i = P.d n y := by
      intro i
      have him : φ.toFun (n + 1) ((z : κ →₀ M (n + 1)) i) = P'.d n (w i) :=
        congrFun (congrArg (fun y : κ →₀ M' (n + 1) => (y : κ → M' (n + 1))) hw) i
      have hclass : φ.cohomologyMap n
          (Submodule.Quotient.mk ⟨(z : κ →₀ M (n + 1)) i, hzc i⟩) = 0 := by
        refine (Submodule.Quotient.mk_eq_zero _).2 ?_
        exact ⟨w i, him⟩
      have := (injective_iff_map_eq_zero _).1 (hφ.2 n).1 _ hclass
      exact (Submodule.Quotient.mk_eq_zero _).1 this
    set Rel : M (n + 1) → M n → Prop := fun a y => a = P.d n y with hRel
    have h0 : Rel 0 0 := ((P.dₗ n).map_zero).symm
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    refine ⟨Finsupp.mapRange (pick Rel) (pick_zero Rel) (z : κ →₀ M (n + 1)), ?_⟩
    refine Finsupp.ext fun i => ?_
    show (z : κ →₀ M (n + 1)) i
      = P.d n (Finsupp.mapRange (pick Rel) (pick_zero Rel) (z : κ →₀ M (n + 1)) i)
    rw [Finsupp.mapRange_apply]
    exact pick_spec (hcob i) h0
  · intro c
    refine Quotient.inductionOn' c fun w => ?_
    set Rel : M' (n + 1) → M (n + 1) → Prop :=
      fun y m => m ∈ P.cocycles (n + 1) ∧ ∃ v : M' n, φ.toFun (n + 1) m - y = P'.d n v
      with hRel
    have h0 : Rel 0 0 :=
      ⟨(P.dₗ (n + 1)).map_zero, 0, by
        show φ.toFun (n + 1) 0 - 0 = P'.d n 0
        rw [show φ.toFun (n + 1) (0 : M (n + 1)) = 0 from (φ.mapₗ (n + 1)).map_zero, sub_zero,
          show P'.d n (0 : M' n) = 0 from (P'.dₗ n).map_zero]⟩
    have hwc := (mem_finsupp_cocycles P' κ).1 w.2
    have hex : ∀ i, Rel ((w : κ →₀ M' (n + 1)) i) (pick Rel ((w : κ →₀ M' (n + 1)) i)) := by
      intro i
      refine pick_spec ?_ h0
      obtain ⟨a, ha⟩ := (hφ.2 n).2 (Submodule.Quotient.mk ⟨(w : κ →₀ M' (n + 1)) i, hwc i⟩)
      refine Quotient.inductionOn' a ?_ ha
      intro m hm
      obtain ⟨v, hv⟩ := (Submodule.Quotient.eq _).1 hm
      exact ⟨(m : M (n + 1)), m.2, v, hv⟩
    refine ⟨Submodule.Quotient.mk ⟨Finsupp.mapRange (pick Rel) (pick_zero Rel)
      (w : κ →₀ M' (n + 1)), (mem_finsupp_cocycles P κ).2 fun i => ?_⟩, ?_⟩
    · rw [Finsupp.mapRange_apply]
      exact (hex i).1
    · refine (Submodule.Quotient.eq _).2 ?_
      set RelD : M' (n + 1) → M' n → Prop := fun a v => a = P'.d n v with hRelD
      have hD0 : RelD 0 0 := ((P'.dₗ n).map_zero).symm
      have hdiff : ∀ i, ∃ v : M' n,
          ((finsuppMap φ κ).toFun (n + 1) (Finsupp.mapRange (pick Rel) (pick_zero Rel)
            (w : κ →₀ M' (n + 1))) - (w : κ →₀ M' (n + 1))) i = P'.d n v := by
        intro i
        obtain ⟨v, hv⟩ := (hex i).2
        refine ⟨v, ?_⟩
        show φ.toFun (n + 1) (Finsupp.mapRange (pick Rel) (pick_zero Rel)
          (w : κ →₀ M' (n + 1)) i) - (w : κ →₀ M' (n + 1)) i = P'.d n v
        rw [Finsupp.mapRange_apply]
        exact hv
      refine ⟨Finsupp.mapRange (pick RelD) (pick_zero RelD)
        ((finsuppMap φ κ).toFun (n + 1) (Finsupp.mapRange (pick Rel) (pick_zero Rel)
          (w : κ →₀ M' (n + 1))) - (w : κ →₀ M' (n + 1))), ?_⟩
      refine Finsupp.ext fun i => ?_
      show ((finsuppMap φ κ).toFun (n + 1) (Finsupp.mapRange (pick Rel) (pick_zero Rel)
          (w : κ →₀ M' (n + 1))) - (w : κ →₀ M' (n + 1))) i
        = P'.d n (Finsupp.mapRange (pick RelD) (pick_zero RelD) _ i)
      rw [Finsupp.mapRange_apply]
      exact pick_spec (hdiff i) hD0

/-- **A direct sum of full quasi-isomorphisms is a full quasi-isomorphism.** -/
theorem finsuppMap_isQuasiIsoFull (hφ : φ.IsQuasiIsoFull) : (finsuppMap φ κ).IsQuasiIsoFull :=
  ⟨finsuppMap_cocyclesMap_zero_bijective φ κ hφ, finsuppMap_isQuasiIso φ κ hφ⟩

end QuasiIso

end GaloisForLFunctions.HTGeometry
