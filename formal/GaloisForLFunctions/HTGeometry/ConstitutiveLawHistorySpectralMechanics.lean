import GaloisForLFunctions.HTGeometry.ConstitutiveObstructionFiltration

/-!
# Finite law-history spectral mechanics

An admitted finite linear history carries a future-tail survival filtration.  Every adjacent stage
is the primary/secondary carrier cell of `ConstitutiveObstructionFiltration`.  Refactoring one
stage inserts a short exact refinement, while a split inclusion--retraction history exhibits exact
local cancellation through a canonical cokernel-to-kernel transgression.
-/

namespace GaloisForLFunctions.HTGeometry.LawHistorySpectralMechanics

open CategoryTheory

noncomputable section

universe u v

variable {k : Type u} [Field k]

/-! ## Functorial finite histories and survival filtration -/

/-- Complete future tail from stage `i` to the endpoint. -/
def tail {m : ℕ} (H : Fin (m + 1) ⥤ ModuleCat.{v} k) (i : Fin (m + 1)) :
    H.obj i →ₗ[k] H.obj (Fin.last m) :=
  (H.map (homOfLE (Fin.le_last i))).hom

/-- Total endpoint defect of a finite history. -/
abbrev totalDefect {m : ℕ} (H : Fin (m + 1) ⥤ ModuleCat.{v} k) :=
  H.obj (Fin.last m) ⧸ LinearMap.range (tail H 0)

/-- Earlier future-tail ranges lie in every later future-tail range. -/
theorem range_tail_mono {m : ℕ} (H : Fin (m + 1) ⥤ ModuleCat.{v} k)
    {i j : Fin (m + 1)} (hij : i ≤ j) :
    LinearMap.range (tail H i) ≤ LinearMap.range (tail H j) := by
  rintro y ⟨x, rfl⟩
  refine ⟨(H.map (homOfLE hij)) x, ?_⟩
  change (H.map (homOfLE (Fin.le_last j))) ((H.map (homOfLE hij)) x) =
    (H.map (homOfLE (Fin.le_last i))) x
  rw [← ModuleCat.comp_apply, ← H.map_comp]
  congr 2

/-- Quotient transition from total defect to the defect seen after stage `i`. -/
def transition {m : ℕ} (H : Fin (m + 1) ⥤ ModuleCat.{v} k) (i : Fin (m + 1)) :
    totalDefect H →ₗ[k] (H.obj (Fin.last m) ⧸ LinearMap.range (tail H i)) :=
  Submodule.factor (range_tail_mono H (Fin.zero_le i))

/-- Classes of the total defect already attained by stage `i`. -/
def layer {m : ℕ} (H : Fin (m + 1) ⥤ ModuleCat.{v} k) (i : Fin (m + 1)) :
    Submodule k (totalDefect H) :=
  LinearMap.ker (transition H i)

/-- Survival layers are monotone along every finite history. -/
theorem layer_mono {m : ℕ} (H : Fin (m + 1) ⥤ ModuleCat.{v} k) :
    Monotone (layer H) := by
  intro i j hij x hx
  rw [layer, LinearMap.mem_ker] at hx ⊢
  induction x using Submodule.Quotient.induction_on with | _ y => ?_
  change (LinearMap.range (tail H j)).mkQ y = 0
  change (LinearMap.range (tail H i)).mkQ y = 0 at hx
  change Submodule.Quotient.mk y = 0 at hx ⊢
  rw [Submodule.Quotient.mk_eq_zero] at hx ⊢
  exact range_tail_mono H hij hx

/-- The initial survival layer is zero. -/
theorem layer_zero {m : ℕ} (H : Fin (m + 1) ⥤ ModuleCat.{v} k) :
    layer H 0 = ⊥ := by
  ext x
  rw [layer, LinearMap.mem_ker]
  induction x using Submodule.Quotient.induction_on with | _ y => ?_
  change (LinearMap.range (tail H 0)).mkQ y = 0 ↔ _
  simp

/-- The future tail at the endpoint is the identity. -/
theorem tail_last {m : ℕ} (H : Fin (m + 1) ⥤ ModuleCat.{v} k) :
    tail H (Fin.last m) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change (H.map (homOfLE (Fin.le_last (Fin.last m)))) x = x
  rw [show homOfLE (Fin.le_last (Fin.last m)) = 𝟙 _ from Subsingleton.elim _ _]
  simp

/-- The endpoint survival layer is the entire total defect. -/
theorem layer_last {m : ℕ} (H : Fin (m + 1) ⥤ ModuleCat.{v} k) :
    layer H (Fin.last m) = ⊤ := by
  ext x
  rw [layer, LinearMap.mem_ker]
  induction x using Submodule.Quotient.induction_on with | _ y => ?_
  change (LinearMap.range (tail H (Fin.last m))).mkQ y = 0 ↔ _
  rw [tail_last]
  simp

/-- Unconditional finite-history filtration capstone. -/
theorem finiteFiltration_closed {m : ℕ} (H : Fin (m + 1) ⥤ ModuleCat.{v} k) :
    layer H 0 = ⊥ ∧ layer H (Fin.last m) = ⊤ ∧ Monotone (layer H) :=
  ⟨layer_zero H, layer_last H, layer_mono H⟩

/-! ## Every adjacent stage is the future-tail survivor quotient -/

/-- Prefix from the initial object to the source of stage `i`. -/
def stagePrefix {m : ℕ} (H : Fin (m + 1) ⥤ ModuleCat.{v} k) (i : Fin m) :
    H.obj 0 →ₗ[k] H.obj i.castSucc :=
  (H.map (homOfLE (Fin.zero_le i.castSucc))).hom

/-- The `i`-th adjacent stage map. -/
def stageMap {m : ℕ} (H : Fin (m + 1) ⥤ ModuleCat.{v} k) (i : Fin m) :
    H.obj i.castSucc →ₗ[k] H.obj i.succ :=
  (H.map (homOfLE (show i.castSucc ≤ i.succ from Fin.castSucc_lt_succ.le))).hom

/-- Complete future tail after the `i`-th adjacent stage. -/
def stageTail {m : ℕ} (H : Fin (m + 1) ⥤ ModuleCat.{v} k) (i : Fin m) :
    H.obj i.succ →ₗ[k] H.obj (Fin.last m) :=
  tail H i.succ

/-- An adjacent stage followed by its future tail is the previous future tail. -/
theorem stageTail_comp_stageMap {m : ℕ}
    (H : Fin (m + 1) ⥤ ModuleCat.{v} k) (i : Fin m) :
    (stageTail H i).comp (stageMap H i) = tail H i.castSucc := by
  apply LinearMap.ext
  intro x
  change (H.map (homOfLE (Fin.le_last i.succ)))
      ((H.map (homOfLE (show i.castSucc ≤ i.succ from Fin.castSucc_lt_succ.le))) x) =
    (H.map (homOfLE (Fin.le_last i.castSucc))) x
  rw [← ModuleCat.comp_apply, ← H.map_comp]
  congr 2

/-- Prefix, adjacent stage, and future tail compose to the total history. -/
theorem stageTotal_eq_tail_zero {m : ℕ}
    (H : Fin (m + 1) ⥤ ModuleCat.{v} k) (i : Fin m) :
    ((stageTail H i).comp (stageMap H i)).comp (stagePrefix H i) = tail H 0 := by
  apply LinearMap.ext
  intro x
  change (H.map (homOfLE (Fin.le_last i.succ)))
      ((H.map (homOfLE (show i.castSucc ≤ i.succ from Fin.castSucc_lt_succ.le)))
        ((H.map (homOfLE (Fin.zero_le i.castSucc))) x)) =
    (H.map (homOfLE (Fin.le_last (0 : Fin (m + 1))))) x
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← H.map_comp, ← H.map_comp]
  congr 2

/-- The associated grade of any adjacent finite-history stage is local failure modulo its incoming
range and the kernel of its complete future tail. -/
def stageSurvivorEquiv {m : ℕ}
    (H : Fin (m + 1) ⥤ ModuleCat.{v} k) (i : Fin m) :
    (GaloisForLFunctions.HTGeometry.tripleCarrierSecondFiltration
        (stagePrefix H i) (stageMap H i) (stageTail H i) ⧸
      LinearMap.ker
        (GaloisForLFunctions.HTGeometry.tripleCarrierMiddleLayerMap
          (stagePrefix H i) (stageMap H i) (stageTail H i))) ≃ₗ[k]
      (H.obj i.succ ⧸
        GaloisForLFunctions.HTGeometry.secondaryCarrierSubmodule
          (stageMap H i) (stageTail H i)) :=
  GaloisForLFunctions.HTGeometry.tripleCarrierMiddleGradedEquiv
    (stagePrefix H i) (stageMap H i) (stageTail H i)

/-- Unconditional adjacent-stage survivor capstone. -/
theorem finiteHistoryStage_closed {m : ℕ}
    (H : Fin (m + 1) ⥤ ModuleCat.{v} k) (i : Fin m) :
    (stageTail H i).comp (stageMap H i) = tail H i.castSucc ∧
      ((stageTail H i).comp (stageMap H i)).comp (stagePrefix H i) = tail H 0 ∧
      Nonempty ((GaloisForLFunctions.HTGeometry.tripleCarrierSecondFiltration
          (stagePrefix H i) (stageMap H i) (stageTail H i) ⧸
        LinearMap.ker
          (GaloisForLFunctions.HTGeometry.tripleCarrierMiddleLayerMap
            (stagePrefix H i) (stageMap H i) (stageTail H i))) ≃ₗ[k]
        (H.obj i.succ ⧸
          GaloisForLFunctions.HTGeometry.secondaryCarrierSubmodule
            (stageMap H i) (stageTail H i))) :=
  ⟨stageTail_comp_stageMap H i, stageTotal_eq_tail_zero H i, ⟨stageSurvivorEquiv H i⟩⟩

/-! ## Exact refactorization -/

section Refactorization

variable {U W V A : Type*}
variable [AddCommGroup U] [Module k U]
variable [AddCommGroup W] [Module k W]
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup A] [Module k A]

/-- First refined grade: failure of `g` modulo erasure by the complete refined future. -/
def refactorInnerSubmodule (g : U →ₗ[k] W) (h : W →ₗ[k] V) (T : V →ₗ[k] A) :
    Submodule k W :=
  LinearMap.range g ⊔ LinearMap.ker (T.comp h)

/-- Coarse grade before inserting the factorization `h ∘ g`. -/
def refactorCoarseSubmodule (g : U →ₗ[k] W) (h : W →ₗ[k] V) (T : V →ₗ[k] A) :
    Submodule k V :=
  LinearMap.range (h.comp g) ⊔ LinearMap.ker T

/-- Second refined grade: failure of `h` modulo erasure by `T`. -/
def refactorOuterSubmodule (h : W →ₗ[k] V) (T : V →ₗ[k] A) :
    Submodule k V :=
  LinearMap.range h ⊔ LinearMap.ker T

/-- Representative map from the first refined carrier into the coarse quotient. -/
def refactorInnerMap (g : U →ₗ[k] W) (h : W →ₗ[k] V) (T : V →ₗ[k] A) :
    W →ₗ[k] (V ⧸ refactorCoarseSubmodule g h T) :=
  (refactorCoarseSubmodule g h T).mkQ.comp h

theorem ker_refactorInnerMap (g : U →ₗ[k] W) (h : W →ₗ[k] V) (T : V →ₗ[k] A) :
    LinearMap.ker (refactorInnerMap g h T) = refactorInnerSubmodule g h T := by
  ext w
  rw [LinearMap.mem_ker]
  change (refactorCoarseSubmodule g h T).mkQ (h w) = 0 ↔ _
  change Submodule.Quotient.mk (h w) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rw [refactorCoarseSubmodule, refactorInnerSubmodule, Submodule.mem_sup,
    Submodule.mem_sup]
  constructor
  · rintro ⟨v, ⟨u, hu⟩, n, hn, hvn⟩
    refine ⟨g u, ⟨u, rfl⟩, w - g u, ?_, ?_⟩
    · rw [LinearMap.mem_ker, LinearMap.comp_apply, map_sub]
      have hhgu : h (g u) = v := by
        simpa only [LinearMap.comp_apply] using hu
      rw [hhgu]
      have hhv : h w = v + n := hvn.symm
      rw [hhv, show v + n - v = n by abel, LinearMap.mem_ker.mp hn]
    · abel
  · rintro ⟨w', ⟨u, rfl⟩, n, hn, hsum⟩
    refine ⟨h (g u), ⟨u, rfl⟩, h n, ?_, ?_⟩
    · rw [LinearMap.mem_ker, ← LinearMap.comp_apply]
      exact LinearMap.mem_ker.mp hn
    · rw [← map_add, ← hsum]

/-- Inclusion of the first refined grade into the coarse grade. -/
def refactorInnerToCoarse (g : U →ₗ[k] W) (h : W →ₗ[k] V) (T : V →ₗ[k] A) :
    (W ⧸ refactorInnerSubmodule g h T) →ₗ[k]
      (V ⧸ refactorCoarseSubmodule g h T) :=
  Submodule.liftQ (refactorInnerSubmodule g h T) (refactorInnerMap g h T) (by
    rw [← ker_refactorInnerMap g h T])

@[simp]
theorem refactorInnerToCoarse_mkQ
    (g : U →ₗ[k] W) (h : W →ₗ[k] V) (T : V →ₗ[k] A) (w : W) :
    refactorInnerToCoarse g h T ((refactorInnerSubmodule g h T).mkQ w) =
      (refactorCoarseSubmodule g h T).mkQ (h w) :=
  rfl

theorem refactorInnerToCoarse_injective
    (g : U →ₗ[k] W) (h : W →ₗ[k] V) (T : V →ₗ[k] A) :
    Function.Injective (refactorInnerToCoarse g h T) := by
  intro x y hxy
  induction x using Submodule.Quotient.induction_on with | _ w => ?_
  induction y using Submodule.Quotient.induction_on with | _ w' => ?_
  apply (Submodule.Quotient.eq _).2
  rw [← ker_refactorInnerMap g h T, LinearMap.mem_ker]
  change (refactorCoarseSubmodule g h T).mkQ (h (w - w')) = 0
  rw [map_sub, map_sub]
  change (refactorCoarseSubmodule g h T).mkQ (h w) =
    (refactorCoarseSubmodule g h T).mkQ (h w') at hxy
  rw [hxy, sub_self]

theorem refactorCoarse_le_outer
    (g : U →ₗ[k] W) (h : W →ₗ[k] V) (T : V →ₗ[k] A) :
    refactorCoarseSubmodule g h T ≤ refactorOuterSubmodule h T := by
  rw [refactorCoarseSubmodule, refactorOuterSubmodule]
  exact sup_le (le_sup_of_le_left (LinearMap.range_comp_le_range g h)) le_sup_right

/-- Quotient from the coarse grade to the second refined grade. -/
def refactorCoarseToOuter
    (g : U →ₗ[k] W) (h : W →ₗ[k] V) (T : V →ₗ[k] A) :
    (V ⧸ refactorCoarseSubmodule g h T) →ₗ[k]
      (V ⧸ refactorOuterSubmodule h T) :=
  Submodule.factor (refactorCoarse_le_outer g h T)

theorem refactorCoarseToOuter_surjective
    (g : U →ₗ[k] W) (h : W →ₗ[k] V) (T : V →ₗ[k] A) :
    Function.Surjective (refactorCoarseToOuter g h T) :=
  Submodule.factor_surjective (refactorCoarse_le_outer g h T)

theorem range_refactorInnerToCoarse_eq_ker
    (g : U →ₗ[k] W) (h : W →ₗ[k] V) (T : V →ₗ[k] A) :
    LinearMap.range (refactorInnerToCoarse g h T) =
      LinearMap.ker (refactorCoarseToOuter g h T) := by
  ext x
  induction x using Submodule.Quotient.induction_on with | _ v => ?_
  constructor
  · rintro ⟨z, hz⟩
    induction z using Submodule.Quotient.induction_on with | _ w => ?_
    rw [LinearMap.mem_ker]
    change (refactorOuterSubmodule h T).mkQ v = 0
    change (refactorCoarseSubmodule g h T).mkQ (h w) =
      (refactorCoarseSubmodule g h T).mkQ v at hz
    have hv := congrArg (refactorCoarseToOuter g h T) hz
    change (refactorOuterSubmodule h T).mkQ (h w) =
      (refactorOuterSubmodule h T).mkQ v at hv
    have hzero : (refactorOuterSubmodule h T).mkQ (h w) = 0 := by
      change Submodule.Quotient.mk (h w) = 0
      rw [Submodule.Quotient.mk_eq_zero, refactorOuterSubmodule]
      apply Submodule.mem_sup_left
      exact ⟨w, rfl⟩
    rw [hzero] at hv
    exact hv.symm
  · intro hx
    rw [LinearMap.mem_ker] at hx
    change (refactorOuterSubmodule h T).mkQ v = 0 at hx
    change Submodule.Quotient.mk v = 0 at hx
    rw [Submodule.Quotient.mk_eq_zero, refactorOuterSubmodule,
      Submodule.mem_sup] at hx
    obtain ⟨v', ⟨w, hw⟩, n, hn, hv⟩ := hx
    refine ⟨(refactorInnerSubmodule g h T).mkQ w, ?_⟩
    rw [refactorInnerToCoarse_mkQ]
    apply (Submodule.Quotient.eq _).2
    change h w - v ∈ refactorCoarseSubmodule g h T
    have hv' : v = h w + n := by
      calc
        v = v' + n := hv.symm
        _ = h w + n := by rw [hw]
    rw [hv', sub_add_eq_sub_sub, sub_self, zero_sub]
    apply Submodule.mem_sup_right
    rw [LinearMap.mem_ker, map_neg, LinearMap.mem_ker.mp hn, neg_zero]

/-- Exact refactorization: the old grade is an extension of the two refined grades. -/
theorem refactorization_short_exact
    (g : U →ₗ[k] W) (h : W →ₗ[k] V) (T : V →ₗ[k] A) :
    Function.Injective (refactorInnerToCoarse g h T) ∧
      LinearMap.range (refactorInnerToCoarse g h T) =
        LinearMap.ker (refactorCoarseToOuter g h T) ∧
      Function.Surjective (refactorCoarseToOuter g h T) :=
  ⟨refactorInnerToCoarse_injective g h T,
    range_refactorInnerToCoarse_eq_ker g h T,
    refactorCoarseToOuter_surjective g h T⟩

end Refactorization

/-! ## Split local-cancellation transgression -/

section SplitTransgression

variable {X Y : Type*}
variable [AddCommGroup X] [Module k X]
variable [AddCommGroup Y] [Module k Y]

/-- Residual projection attached to a split inclusion--retraction pair. -/
def splitResidual (f : X →ₗ[k] Y) (g : Y →ₗ[k] X) : Y →ₗ[k] Y :=
  LinearMap.id - f.comp g

@[simp]
theorem splitResidual_apply (f : X →ₗ[k] Y) (g : Y →ₗ[k] X) (y : Y) :
    splitResidual f g y = y - f (g y) :=
  rfl

theorem splitResidual_lands_in_kernel
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] X) (hgf : g.comp f = LinearMap.id) (y : Y) :
    splitResidual f g y ∈ LinearMap.ker g := by
  rw [LinearMap.mem_ker, splitResidual_apply, map_sub]
  have hgf' : g (f (g y)) = g y := by
    have h := LinearMap.congr_fun hgf (g y)
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
  rw [hgf', sub_self]

def splitResidualToKernel
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] X) (hgf : g.comp f = LinearMap.id) :
    Y →ₗ[k] LinearMap.ker g :=
  (splitResidual f g).codRestrict (LinearMap.ker g)
    (splitResidual_lands_in_kernel f g hgf)

theorem range_f_le_ker_splitResidualToKernel
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] X) (hgf : g.comp f = LinearMap.id) :
    LinearMap.range f ≤ LinearMap.ker (splitResidualToKernel f g hgf) := by
  rintro y ⟨x, rfl⟩
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  change f x - f (g (f x)) = 0
  have h := LinearMap.congr_fun hgf x
  have h' : g (f x) = x := by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
  rw [h', sub_self]

/-- Canonical transgression from the local cokernel of `f` to the local kernel of `g`. -/
def splitTransgression
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] X) (hgf : g.comp f = LinearMap.id) :
    (Y ⧸ LinearMap.range f) →ₗ[k] LinearMap.ker g :=
  Submodule.liftQ (LinearMap.range f) (splitResidualToKernel f g hgf)
    (range_f_le_ker_splitResidualToKernel f g hgf)

@[simp]
theorem splitTransgression_mkQ
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] X) (hgf : g.comp f = LinearMap.id) (y : Y) :
    splitTransgression f g hgf ((LinearMap.range f).mkQ y) =
      ⟨y - f (g y), splitResidual_lands_in_kernel f g hgf y⟩ :=
  rfl

def splitKernelToCokernel (f : X →ₗ[k] Y) (g : Y →ₗ[k] X) :
    LinearMap.ker g →ₗ[k] (Y ⧸ LinearMap.range f) :=
  (LinearMap.range f).mkQ.comp (LinearMap.ker g).subtype

/-- Exact split-cancellation law: `coker f` is canonically the kernel of its retraction. -/
def splitTransgressionEquiv
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] X) (hgf : g.comp f = LinearMap.id) :
    (Y ⧸ LinearMap.range f) ≃ₗ[k] LinearMap.ker g where
  toFun := splitTransgression f g hgf
  invFun := splitKernelToCokernel f g
  left_inv q := by
    induction q using Submodule.Quotient.induction_on with | _ y => ?_
    change (LinearMap.range f).mkQ (y - f (g y)) =
      (LinearMap.range f).mkQ y
    apply (Submodule.Quotient.eq _).2
    change (y - f (g y)) - y ∈ LinearMap.range f
    refine ⟨-(g y), ?_⟩
    simp
  right_inv z := by
    apply Subtype.ext
    change z.1 - f (g z.1) = z.1
    rw [LinearMap.mem_ker.mp z.2, map_zero, sub_zero]
  map_add' x y := map_add (splitTransgression f g hgf) x y
  map_smul' c x := map_smul (splitTransgression f g hgf) c x

/-- One-dimensional split inclusion. -/
def scalarSplitInclusion : k →ₗ[k] k × k where
  toFun x := (x, 0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- Retraction of the one-dimensional split inclusion. -/
def scalarSplitProjection : (k × k) →ₗ[k] k where
  toFun x := x.1
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

@[simp]
theorem scalarSplitProjection_comp_inclusion :
    scalarSplitProjection.comp (scalarSplitInclusion (k := k)) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  rfl

theorem scalarSplitInclusion_not_surjective :
    ¬ Function.Surjective (scalarSplitInclusion (k := k)) := by
  intro hs
  obtain ⟨x, hx⟩ := hs (0, 1)
  have h := congrArg Prod.snd hx
  change (0 : k) = 1 at h
  exact zero_ne_one h

theorem scalarSplitProjection_not_injective :
    ¬ Function.Injective (scalarSplitProjection (k := k)) := by
  intro hi
  have h := hi (show scalarSplitProjection (k := k) (0, 0) =
    scalarSplitProjection (k := k) (0, 1) by rfl)
  have h' := congrArg Prod.snd h
  change (0 : k) = 1 at h'
  exact zero_ne_one h'

/-- Unconditional sharp split-cancellation capstone: both local maps fail to be equivalences while
their composite is the identity, and the local defects are canonically equivalent. -/
theorem splitTransgression_closed :
    Nonempty (((k × k) ⧸ LinearMap.range (scalarSplitInclusion (k := k))) ≃ₗ[k]
      LinearMap.ker (scalarSplitProjection (k := k))) ∧
      scalarSplitProjection.comp (scalarSplitInclusion (k := k)) = LinearMap.id ∧
      ¬ Function.Surjective (scalarSplitInclusion (k := k)) ∧
      ¬ Function.Injective (scalarSplitProjection (k := k)) := by
  have hcomp := scalarSplitProjection_comp_inclusion (k := k)
  refine ⟨⟨splitTransgressionEquiv
      (f := scalarSplitInclusion (k := k))
      (g := scalarSplitProjection (k := k)) hcomp⟩,
    hcomp, scalarSplitInclusion_not_surjective (k := k),
    scalarSplitProjection_not_injective (k := k)⟩

end SplitTransgression

end

end GaloisForLFunctions.HTGeometry.LawHistorySpectralMechanics
