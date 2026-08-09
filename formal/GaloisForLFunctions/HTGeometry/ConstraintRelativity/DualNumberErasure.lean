import Mathlib

/-!
# Dual-number static observer deformation erasure

A module over the dual numbers `k[ε]/(ε²)` is a vector space `V` together with a square-zero
endomorphism `N`; the forgetful observer to vector spaces keeps `V` and drops `N`.  The observer is
faithful, exact and conservative, yet it erases the deformation class: the two-dimensional
extension of the trivial law by the trivial law admits no invariant complement, while the same
sequence of vector spaces splits.  The classifying set of those extensions is exactly `k`, whereas
every short exact sequence of vector spaces splits.

The lost law is recovered by one mixed synchronization cell: square-zero endomorphisms of `V`
correspond bijectively to pairs `(F, θ)` with `F ⊆ V` a subspace and `θ : V/F → F` injective.
-/

namespace HTGeometry.ConstraintRelativity

open Submodule LinearMap

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-! ## Square-zero laws -/

/-- A square-zero law on `V`: the datum of a `k[ε]/(ε²)`-module structure with underlying space
`V`, given by the action of `ε`. -/
structure SquareZeroLaw (k V : Type*) [Field k] [AddCommGroup V] [Module k V] where
  /-- The action of `ε`. -/
  act : V →ₗ[k] V
  /-- The action squares to zero. -/
  sq_zero : act.comp act = 0

namespace SquareZeroLaw

variable (L : SquareZeroLaw k V)

@[simp]
theorem act_act (v : V) : L.act (L.act v) = 0 := by
  have := congrArg (fun f => f v) L.sq_zero
  simpa using this

/-- The kernel of the law: the subspace annihilated by `ε`. -/
def frame : Submodule k V := LinearMap.ker L.act

theorem range_le_frame : LinearMap.range L.act ≤ L.frame := by
  rintro _ ⟨v, rfl⟩
  simp [frame, LinearMap.mem_ker]

/-- The mixed synchronization cell `θ : V/F → F`, `[v] ↦ ε v`. -/
def cell : (V ⧸ L.frame) →ₗ[k] L.frame :=
  Submodule.liftQ L.frame (L.act.codRestrict L.frame fun v => L.range_le_frame ⟨v, rfl⟩)
    (fun v hv => by
      simp only [LinearMap.mem_ker]
      exact Subtype.ext hv)

@[simp]
theorem cell_mk (v : V) : (L.cell (Submodule.Quotient.mk v) : V) = L.act v := rfl

/-- The synchronization cell is injective. -/
theorem cell_injective : Function.Injective L.cell := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨v, rfl⟩ := L.frame.mkQ_surjective x
  have hv : L.act v = 0 := by
    have := congrArg (Subtype.val) hx
    simpa using this
  exact (Submodule.Quotient.mk_eq_zero _).2 hv

end SquareZeroLaw

/-! ## Reconstruction from a mixed cell -/

/-- The square-zero law rebuilt from a subspace and an injective synchronization cell. -/
def lawOfCell (F : Submodule k V) (θ : (V ⧸ F) →ₗ[k] F) : SquareZeroLaw k V where
  act := F.subtype.comp (θ.comp F.mkQ)
  sq_zero := by
    refine LinearMap.ext fun v => ?_
    have hz : (Submodule.Quotient.mk ((θ (Submodule.Quotient.mk v) : V)) : V ⧸ F) = 0 :=
      (Submodule.Quotient.mk_eq_zero F).2 (θ (Submodule.Quotient.mk v)).2
    show ((θ (Submodule.Quotient.mk ((θ (Submodule.Quotient.mk v) : V)))) : V) = 0
    rw [hz, map_zero]
    rfl

@[simp]
theorem lawOfCell_act (F : Submodule k V) (θ : (V ⧸ F) →ₗ[k] F) (v : V) :
    (lawOfCell F θ).act v = (θ (Submodule.Quotient.mk v) : V) := rfl

/-- The rebuilt law has the prescribed frame. -/
theorem lawOfCell_frame (F : Submodule k V) (θ : (V ⧸ F) →ₗ[k] F) (hθ : Function.Injective θ) :
    (lawOfCell F θ).frame = F := by
  refine le_antisymm ?_ ?_
  · intro v hv
    have h0 : θ (Submodule.Quotient.mk v) = 0 := by
      have : ((θ (Submodule.Quotient.mk v) : V)) = 0 := hv
      exact Subtype.ext this
    have : (Submodule.Quotient.mk v : V ⧸ F) = 0 := hθ (by simpa using h0)
    exact (Submodule.Quotient.mk_eq_zero _).1 this
  · intro v hv
    show (θ (Submodule.Quotient.mk v) : V) = 0
    rw [(Submodule.Quotient.mk_eq_zero F).2 hv]
    simp

/-- The rebuilt law has the prescribed synchronization cell. -/
theorem lawOfCell_cell (F : Submodule k V) (θ : (V ⧸ F) →ₗ[k] F) (v : V) :
    (((lawOfCell F θ).cell (Submodule.Quotient.mk v) : V))
      = ((θ (Submodule.Quotient.mk v) : V)) := rfl

/-- **Theorem 2, first direction.**  Rebuilding a law from its own frame and cell returns the
law. -/
theorem lawOfCell_frame_cell (L : SquareZeroLaw k V) :
    lawOfCell L.frame L.cell = L := by
  cases L with
  | mk act sq_zero => congr 1

/-! ## Erasure: the observer keeps `V` and drops the law -/

/-- The observer is conservative: a law morphism that is bijective has a law-morphism inverse. -/
theorem conservative {W : Type*} [AddCommGroup W] [Module k W] (L : SquareZeroLaw k V)
    (M : SquareZeroLaw k W) (f : V ≃ₗ[k] W) (hf : ∀ v, f (L.act v) = M.act (f v)) (w : W) :
    f.symm (M.act w) = L.act (f.symm w) := by
  have hw := hf (f.symm w)
  rw [f.apply_symm_apply] at hw
  rw [← hw, f.symm_apply_apply]

/-! ## The extension of the trivial law by the trivial law -/

/-- The trivial subspace `0 × k` of `k × k`. -/
def trivialFrame (k : Type*) [Field k] : Submodule k (k × k) :=
  LinearMap.ker (LinearMap.fst k k k)

/-- The trivial law, in which `ε` acts by zero. -/
def zeroLaw (k V : Type*) [Field k] [AddCommGroup V] [Module k V] : SquareZeroLaw k V where
  act := 0
  sq_zero := LinearMap.zero_comp 0

@[simp]
theorem zeroLaw_frame (k V : Type*) [Field k] [AddCommGroup V] [Module k V] :
    (zeroLaw k V).frame = ⊤ := by
  simp [SquareZeroLaw.frame, zeroLaw]

/-- The Jordan law: `ε · (x, y) = (0, x)`. -/
def jordanLaw (k : Type*) [Field k] : SquareZeroLaw k (k × k) where
  act := (0 : (k × k) →ₗ[k] k).prod (LinearMap.fst k k k)
  sq_zero := LinearMap.ext fun v => by simp [Prod.ext_iff]

@[simp]
theorem jordanLaw_act (k : Type*) [Field k] (v : k × k) :
    (jordanLaw k).act v = (0, v.1) := rfl

theorem jordanLaw_frame (k : Type*) [Field k] : (jordanLaw k).frame = trivialFrame k := by
  ext v
  simp [SquareZeroLaw.frame, trivialFrame, LinearMap.mem_ker, Prod.ext_iff]

/-- The observer keeps the underlying space and drops the law: two square-zero laws on `k × k`
with the same underlying space have different frames. -/
theorem law_not_determined_by_space (k : Type*) [Field k] :
    (zeroLaw k (k × k)).frame ≠ (jordanLaw k).frame := by
  rw [zeroLaw_frame, jordanLaw_frame]
  intro h
  have h1 : ((1 : k), (0 : k)) ∈ trivialFrame k := h ▸ Submodule.mem_top
  have : (1 : k) = 0 := h1
  exact one_ne_zero this

/-- **The sequence splits after forgetting the law.** -/
theorem trivialFrame_hasComplement (k : Type*) [Field k] :
    ∃ W : Submodule k (k × k), IsCompl (trivialFrame k) W :=
  ⟨LinearMap.ker (LinearMap.snd k k k), by
    constructor
    · rw [disjoint_iff]
      ext v
      simp [trivialFrame, LinearMap.mem_ker, Prod.ext_iff]
    · rw [codisjoint_iff]
      refine le_antisymm le_top fun v _ => ?_
      have : v = (0, v.2) + (v.1, 0) := by ext <;> simp
      rw [this]
      exact Submodule.add_mem_sup (by simp [trivialFrame, LinearMap.mem_ker])
        (by simp [LinearMap.mem_ker])⟩

/-- **The sequence is nonsplit as a law extension.**  No complement of the frame is invariant
under the Jordan law. -/
theorem jordanLaw_no_invariant_complement (k : Type*) [Field k] :
    ¬ ∃ W : Submodule k (k × k), IsCompl (trivialFrame k) W ∧
      ∀ w ∈ W, (jordanLaw k).act w ∈ W := by
  rintro ⟨W, hcompl, hinv⟩
  have hsup : trivialFrame k ⊔ W = ⊤ := hcompl.sup_eq_top
  have hmem : ((1 : k), (0 : k)) ∈ trivialFrame k ⊔ W := hsup ▸ Submodule.mem_top
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 hmem
  have hu1 : u.1 = 0 := hu
  have hw1 : w.1 = 1 := by
    have := congrArg Prod.fst huw
    simp only [Prod.fst_add] at this
    rw [hu1] at this
    simpa using this
  have hact : (jordanLaw k).act w ∈ W := hinv w hw
  rw [jordanLaw_act, hw1] at hact
  have hactF : ((0 : k), (1 : k)) ∈ trivialFrame k := by
    simp [trivialFrame, LinearMap.mem_ker]
  have hzero : ((0 : k), (1 : k)) = 0 :=
    (Submodule.mem_bot k).1 (hcompl.inf_eq_bot ▸ Submodule.mem_inf.2 ⟨hactF, hact⟩)
  have hone : (1 : k) = 0 := by
    exact congrArg Prod.snd hzero
  exact one_ne_zero hone

/-! ## The classifying set of extensions -/

/-- Extensions of the trivial law by the trivial law with middle term `k × k`: square-zero laws
whose range lies in the frame and which annihilate the frame. -/
def trivialExtension (k : Type*) [Field k] : Type _ :=
  {N : (k × k) →ₗ[k] (k × k) //
    LinearMap.range N ≤ trivialFrame k ∧ trivialFrame k ≤ LinearMap.ker N}

/-- **`Ext¹` over the dual numbers is `k`.**  The extensions of the trivial law by the trivial law
are classified by one scalar. -/
def trivialExtensionEquiv (k : Type*) [Field k] : trivialExtension k ≃ k where
  toFun N := (N.1 (1, 0)).2
  invFun c := ⟨(0 : (k × k) →ₗ[k] k).prod (c • LinearMap.fst k k k), by
    constructor
    · rintro _ ⟨v, rfl⟩
      simp [trivialFrame, LinearMap.mem_ker]
    · intro v hv
      have hv1 : v.1 = 0 := hv
      simp [LinearMap.mem_ker, hv1]⟩
  left_inv := by
    rintro ⟨N, hrange, hker⟩
    apply Subtype.ext
    refine LinearMap.ext fun v => ?_
    have hfst : (N v).1 = 0 := hrange ⟨v, rfl⟩
    have hker2 : N ((0 : k), (1 : k)) = 0 := hker (by simp [trivialFrame, LinearMap.mem_ker])
    have hsplit : v = v.1 • ((1 : k), (0 : k)) + v.2 • ((0 : k), (1 : k)) := by ext <;> simp
    have hNv : N v = v.1 • N ((1 : k), (0 : k)) := by
      conv_lhs => rw [hsplit]
      rw [map_add, map_smul, map_smul, hker2, smul_zero, add_zero]
    refine Prod.ext ?_ ?_
    · simp [hfst]
    · simp [hNv, mul_comm]
  right_inv c := by simp

/-- **`Ext¹` over the base field vanishes.**  Every short exact sequence of vector spaces splits. -/
theorem vectorSpace_extension_splits {W : Type*} [AddCommGroup W] [Module k W]
    (F : Submodule k W) : ∃ C : Submodule k W, IsCompl F C :=
  F.exists_isCompl

end HTGeometry.ConstraintRelativity
