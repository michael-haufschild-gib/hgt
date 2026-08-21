import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Logic.Relation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Abelian repair: the reduced Laplacian and its minimum principle

A finite sink-connected multigraph gives a reduced Laplacian on the non-sink vertices.  Its
quadratic form is a sum of edge differences and sink squares, so it is positive definite; its
inverse is entrywise nonnegative and sends the all-ones vector to a strictly positive potential.
That potential is what makes every legal repair execution terminate.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- The combinatorial data of a finite sink-connected multigraph, seen from its non-sink
vertices. -/
structure ReducedLaplacian (V : Type*) [Fintype V] [DecidableEq V] where
  /-- Edge multiplicity between two non-sink vertices. -/
  edge : V → V → ℕ
  /-- Edge multiplicity from a non-sink vertex to the sink. -/
  sinkEdge : V → ℕ
  /-- The multigraph is undirected. -/
  edge_symm : ∀ v w, edge v w = edge w v
  /-- There are no self-loops. -/
  edge_self : ∀ v, edge v v = 0
  /-- Every vertex reaches a sink-adjacent vertex through edges. -/
  reaches_sink : ∀ v : V, ∃ w : V,
    Relation.ReflTransGen (fun x y => 0 < edge x y) v w ∧ 0 < sinkEdge w

namespace ReducedLaplacian

variable {V : Type*} [Fintype V] [DecidableEq V] (L : ReducedLaplacian V)

/-- The degree of a non-sink vertex. -/
def deg (v : V) : ℕ := (∑ w, L.edge v w) + L.sinkEdge v

/-- The reduced Laplacian as an integer matrix. -/
def mat (v w : V) : ℤ := if v = w then (L.deg v : ℤ) else -(L.edge v w : ℤ)

/-- The reduced Laplacian acting on a real potential. -/
def act (h : V → ℝ) (v : V) : ℝ := ∑ w, (L.mat v w : ℝ) * h w

theorem act_apply (h : V → ℝ) (v : V) :
    L.act h v = (∑ w, (L.edge v w : ℝ) * (h v - h w)) + (L.sinkEdge v : ℝ) * h v := by
  rw [act]
  have hsplit : ∑ w, ((L.mat v w : ℤ) : ℝ) * h w
      = (L.deg v : ℝ) * h v - ∑ w ∈ univ.erase v, (L.edge v w : ℝ) * h w := by
    rw [← Finset.sum_erase_add univ _ (mem_univ v)]
    rw [mat, if_pos rfl]
    have hterm : ∀ w ∈ univ.erase v, ((L.mat v w : ℤ) : ℝ) * h w
        = -((L.edge v w : ℝ) * h w) := by
      intro w hw
      have hne : v ≠ w := fun hc => (Finset.mem_erase.1 hw).1 hc.symm
      rw [mat, if_neg hne]
      push_cast
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
    push_cast
    ring
  rw [hsplit, deg]
  have hedge : ∑ w, (L.edge v w : ℝ) * (h v - h w)
      = (∑ w, (L.edge v w : ℝ)) * h v - ∑ w, (L.edge v w : ℝ) * h w := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring
  have herase : ∑ w ∈ univ.erase v, (L.edge v w : ℝ) * h w
      = ∑ w, (L.edge v w : ℝ) * h w := by
    rw [← Finset.sum_erase_add univ _ (mem_univ v), L.edge_self v]
    simp
  rw [hedge, herase]
  push_cast
  ring

/-! ## The quadratic form and the minimum principle -/

/-- **(AR.4).**  The reduced Laplacian form is edge differences plus sink squares. -/
theorem two_mul_quadratic (x : V → ℝ) :
    2 * ∑ v, x v * L.act x v
      = (∑ v, ∑ w, (L.edge v w : ℝ) * (x v - x w) ^ 2)
        + 2 * ∑ v, (L.sinkEdge v : ℝ) * x v ^ 2 := by
  have hact : ∀ v, x v * L.act x v
      = (∑ w, (L.edge v w : ℝ) * (x v * (x v - x w))) + (L.sinkEdge v : ℝ) * x v ^ 2 := by
    intro v
    rw [act_apply, mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun w _ => ?_
      ring
    · ring
  rw [Finset.sum_congr rfl fun v _ => hact v, Finset.sum_add_distrib, mul_add]
  congr 1
  have hexpand : ∀ v, ∀ w, (L.edge v w : ℝ) * (x v - x w) ^ 2
      = (L.edge v w : ℝ) * (x v * (x v - x w)) + (L.edge v w : ℝ) * (x w * (x w - x v)) := by
    intro v w
    ring
  rw [Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => hexpand v w]
  rw [Finset.sum_congr rfl fun v _ => Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hswap : (∑ v, ∑ w, (L.edge v w : ℝ) * (x w * (x w - x v)))
      = ∑ v, ∑ w, (L.edge v w : ℝ) * (x v * (x v - x w)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
    rw [L.edge_symm w v]
  rw [hswap]
  ring

/-- **Minimum principle.**  A superharmonic potential on a sink-connected graph is nonnegative. -/
theorem nonneg_of_act_nonneg [Nonempty V] {h : V → ℝ} (hh : ∀ v, 0 ≤ L.act h v) (v : V) :
    0 ≤ h v := by
  by_contra hneg
  push Not at hneg
  obtain ⟨v₀, hv₀⟩ := Finite.exists_min h
  have hm : h v₀ < 0 := lt_of_le_of_lt (hv₀ v) hneg
  have hclosed : ∀ x, h x = h v₀ →
      (∀ y, 0 < L.edge x y → h y = h v₀) ∧ L.sinkEdge x = 0 := by
    intro x hx
    have hact := hh x
    rw [act_apply] at hact
    have hterms : ∀ y ∈ (univ : Finset V), (L.edge x y : ℝ) * (h x - h y) ≤ 0 := by
      intro y _
      have hxy : h x - h y ≤ 0 := by
        have := hv₀ y
        rw [hx]
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hxy
    have hsum : (∑ y, (L.edge x y : ℝ) * (h x - h y)) ≤ 0 := Finset.sum_nonpos hterms
    have hsink : (L.sinkEdge x : ℝ) * h x ≤ 0 := by
      rw [hx]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hm.le
    have hsumzero : (∑ y, (L.edge x y : ℝ) * (h x - h y)) = 0 := by linarith
    have hsinkzero : (L.sinkEdge x : ℝ) * h x = 0 := by linarith
    constructor
    · intro y hy
      have hzero := (Finset.sum_eq_zero_iff_of_nonpos hterms).1 hsumzero y (mem_univ y)
      have hne : (L.edge x y : ℝ) ≠ 0 := by
        exact_mod_cast hy.ne'
      have : h x - h y = 0 := by
        rcases mul_eq_zero.1 hzero with hc | hc
        · exact absurd hc hne
        · exact hc
      rw [← hx]
      linarith
    · have hxne : h x ≠ 0 := by
        rw [hx]
        exact hm.ne
      rcases mul_eq_zero.1 hsinkzero with hc | hc
      · exact_mod_cast hc
      · exact absurd hc hxne
  obtain ⟨w, hpath, hw⟩ := L.reaches_sink v₀
  have hS : ∀ y, Relation.ReflTransGen (fun a b => 0 < L.edge a b) v₀ y → h y = h v₀ := by
    intro y hy
    induction hy with
    | refl => rfl
    | tail _ hstep ih => exact (hclosed _ ih).1 _ hstep
  have hzero := (hclosed w (hS w hpath)).2
  omega

/-- The Laplacian action as a linear map. -/
def actMap : (V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun := L.act
  map_add' x y := by
    funext v
    show (∑ w, ((L.mat v w : ℤ) : ℝ) * (x w + y w))
      = (∑ w, ((L.mat v w : ℤ) : ℝ) * x w) + ∑ w, ((L.mat v w : ℤ) : ℝ) * y w
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    show ((L.mat v w : ℤ) : ℝ) * (x w + y w) = _
    ring
  map_smul' c x := by
    funext v
    show (∑ w, ((L.mat v w : ℤ) : ℝ) * (c * x w))
      = c * ∑ w, ((L.mat v w : ℤ) : ℝ) * x w
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    show ((L.mat v w : ℤ) : ℝ) * (c * x w) = c * (((L.mat v w : ℤ) : ℝ) * x w)
    ring

@[simp] theorem actMap_apply (h : V → ℝ) : L.actMap h = L.act h := rfl

theorem injective_actMap [Nonempty V] : Function.Injective L.actMap := by
  refine (injective_iff_map_eq_zero _).2 fun h hh => ?_
  funext v
  have hzero : ∀ u, L.act h u = 0 := by
    intro u
    have := congrFun hh u
    exact this
  have h1 : 0 ≤ h v := L.nonneg_of_act_nonneg (fun u => le_of_eq (hzero u).symm) v
  have hneg : ∀ u, 0 ≤ L.act (fun z => -h z) u := by
    intro u
    have hlin : L.act (fun z => -h z) u = -L.act h u := by
      show (∑ w, ((L.mat u w : ℤ) : ℝ) * (-h w)) = -∑ w, ((L.mat u w : ℤ) : ℝ) * h w
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      show ((L.mat u w : ℤ) : ℝ) * (-h w) = -(((L.mat u w : ℤ) : ℝ) * h w)
      ring
    rw [hlin, hzero u, neg_zero]
  have h2 : 0 ≤ -h v := L.nonneg_of_act_nonneg hneg v
  show h v = 0
  linarith

theorem surjective_actMap [Nonempty V] : Function.Surjective L.actMap :=
  LinearMap.surjective_of_injective L.injective_actMap

/-- The unit potential (AR.5). -/
noncomputable def potential [Nonempty V] : V → ℝ :=
  Classical.choose (L.surjective_actMap (fun _ => (1 : ℝ)))

theorem act_potential [Nonempty V] (v : V) : L.act L.potential v = 1 := by
  have h := Classical.choose_spec (L.surjective_actMap (fun _ => (1 : ℝ)))
  exact congrFun h v

theorem potential_pos [Nonempty V] (v : V) : 0 < L.potential v := by
  have hnn : ∀ u, 0 ≤ L.potential u :=
    L.nonneg_of_act_nonneg fun u => by rw [L.act_potential u]; norm_num
  rcases lt_or_eq_of_le (hnn v) with h | h
  · exact h
  · exfalso
    have hact := L.act_potential v
    rw [act_apply] at hact
    have hterms : ∀ y ∈ (univ : Finset V),
        (L.edge v y : ℝ) * (L.potential v - L.potential y) ≤ 0 := by
      intro y _
      refine mul_nonpos_of_nonneg_of_nonpos (by positivity) ?_
      have := hnn y
      linarith [h]
    have hsum : (∑ y, (L.edge v y : ℝ) * (L.potential v - L.potential y)) ≤ 0 :=
      Finset.sum_nonpos hterms
    have hsink : (L.sinkEdge v : ℝ) * L.potential v = 0 := by
      rw [← h]
      ring
    linarith

/-! ## Repair executions, termination and least action -/

theorem mat_symm (v w : V) : L.mat v w = L.mat w v := by
  rw [mat, mat]
  by_cases h : v = w
  · rw [if_pos h, if_pos h.symm, h]
  · rw [if_neg h, if_neg (Ne.symm h), L.edge_symm]

theorem mat_nonpos_of_ne {v w : V} (h : v ≠ w) : L.mat v w ≤ 0 := by
  rw [mat, if_neg h]
  simp

@[simp] theorem mat_self (v : V) : L.mat v v = (L.deg v : ℤ) := by
  rw [mat, if_pos rfl]

/-- The configuration obtained from an odometer. -/
def applyOdo (η u : V → ℤ) : V → ℤ := fun w => η w - ∑ v, L.mat w v * u v

/-- Toppling one vertex. -/
def topple (η : V → ℤ) (v : V) : V → ℤ := fun w => η w - L.mat w v

/-- A configuration is stable when no vertex can repair. -/
def Stable (η : V → ℤ) : Prop := ∀ v, η v < (L.deg v : ℤ)

/-- A legal repair execution. -/
def Legal (L : ReducedLaplacian V) (η : V → ℤ) : List V → Prop
  | [] => True
  | v :: rest => (L.deg v : ℤ) ≤ η v ∧ Legal L (L.topple η v) rest

@[simp] theorem Legal_nil (η : V → ℤ) : L.Legal η [] := trivial

@[simp] theorem Legal_cons (η : V → ℤ) (v : V) (rest : List V) :
    L.Legal η (v :: rest) ↔ (L.deg v : ℤ) ≤ η v ∧ L.Legal (L.topple η v) rest := by
  rw [Legal]

/-- The odometer of an execution list. -/
def odo (_L : ReducedLaplacian V) (l : List V) : V → ℤ := fun v => (l.count v : ℤ)

theorem odo_apply (l : List V) (v : V) : L.odo l v = (l.count v : ℤ) := rfl

theorem applyOdo_zero (η : V → ℤ) : L.applyOdo η (fun _ => 0) = η := by
  funext w
  rw [applyOdo]
  simp

theorem topple_eq_applyOdo (η : V → ℤ) (v : V) :
    L.topple η v = L.applyOdo η (fun z => if z = v then 1 else 0) := by
  funext w
  rw [topple, applyOdo]
  congr 1
  rw [Finset.sum_eq_single v]
  · rw [if_pos rfl, mul_one]
  · intro b _ hb
    rw [if_neg hb, mul_zero]
  · intro h
    exact absurd (mem_univ v) h

theorem applyOdo_applyOdo (η u u' : V → ℤ) :
    L.applyOdo (L.applyOdo η u) u' = L.applyOdo η (fun z => u z + u' z) := by
  funext w
  rw [applyOdo, applyOdo, applyOdo, sub_sub, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

theorem topple_nonneg {η : V → ℤ} (hη : ∀ w, 0 ≤ η w) {v : V} (hv : (L.deg v : ℤ) ≤ η v) :
    ∀ w, 0 ≤ L.topple η v w := by
  intro w
  rw [topple]
  by_cases h : w = v
  · subst h
    rw [mat_self]
    linarith
  · have := L.mat_nonpos_of_ne h
    have := hη w
    linarith

/-- The repair potential of a configuration. -/
noncomputable def work [Nonempty V] (η : V → ℤ) : ℝ := ∑ w, L.potential w * (η w : ℝ)

theorem work_nonneg [Nonempty V] {η : V → ℤ} (hη : ∀ w, 0 ≤ η w) : 0 ≤ L.work η := by
  refine Finset.sum_nonneg fun w _ => ?_
  have h1 := (L.potential_pos w).le
  have h2 : (0 : ℝ) ≤ (η w : ℝ) := by exact_mod_cast hη w
  positivity

/-- **(AR.8).**  Each legal repair spends exactly one unit of potential. -/
theorem work_topple [Nonempty V] (η : V → ℤ) (v : V) :
    L.work (L.topple η v) = L.work η - 1 := by
  have hsum : (∑ w, L.potential w * ((L.mat w v : ℤ) : ℝ)) = 1 := by
    have h := L.act_potential v
    rw [act] at h
    rw [← h]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [L.mat_symm w v]
    ring
  rw [work, work, ← hsum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [topple]
  push_cast
  ring

/-- **Theorem 3.1, termination.**  A legal execution is no longer than the initial potential. -/
theorem length_le_work [Nonempty V] {η : V → ℤ} (hη : ∀ w, 0 ≤ η w) {l : List V}
    (hl : L.Legal η l) : (l.length : ℝ) ≤ L.work η := by
  induction l generalizing η with
  | nil =>
      simpa using L.work_nonneg hη
  | cons v rest ih =>
      obtain ⟨hv, hrest⟩ := hl
      have hnn := L.topple_nonneg hη hv
      have := ih hnn hrest
      rw [work_topple] at this
      simp only [List.length_cons]
      push_cast
      linarith

/-- **Theorem 3.1, least action** (AR.7).  A legal odometer is dominated by every nonnegative
stabilizing vector. -/
theorem odo_le_of_legal {η : V → ℤ} {u : V → ℤ} (hu : ∀ v, 0 ≤ u v)
    (hstab : L.Stable (L.applyOdo η u)) {l : List V} (hl : L.Legal η l) :
    ∀ v, L.odo l v ≤ u v := by
  induction l generalizing η u with
  | nil =>
      intro v
      rw [odo_apply]
      simpa using hu v
  | cons a rest ih =>
      obtain ⟨ha, hrest⟩ := hl
      have hua : 1 ≤ u a := by
        by_contra hcon
        push Not at hcon
        have hu0 : u a = 0 := le_antisymm (by omega) (hu a)
        have hle : (∑ z, L.mat a z * u z) ≤ 0 := by
          refine Finset.sum_nonpos fun z _ => ?_
          by_cases hz : a = z
          · subst hz
            rw [hu0, mul_zero]
          · exact mul_nonpos_of_nonpos_of_nonneg (L.mat_nonpos_of_ne hz) (hu z)
        have hs := hstab a
        rw [applyOdo] at hs
        omega
      set u' : V → ℤ := fun z => u z - (if z = a then 1 else 0) with hu'
      have hu'nn : ∀ v, 0 ≤ u' v := by
        intro v
        rw [hu']
        by_cases hv : v = a
        · subst hv
          simp only []
          omega
        · simp only [if_neg hv]
          simpa using hu v
      have hcomp : L.applyOdo (L.topple η a) u' = L.applyOdo η u := by
        rw [topple_eq_applyOdo, applyOdo_applyOdo]
        congr 1
        funext z
        rw [hu']
        by_cases hz : z = a
        · subst hz
          ring
        · simp only [if_neg hz]
          ring
      have hstab' : L.Stable (L.applyOdo (L.topple η a) u') := by
        rw [hcomp]
        exact hstab
      have hIH := ih hu'nn hstab' hrest
      intro v
      have hv := hIH v
      rw [odo_apply, List.count_cons]
      rw [odo_apply] at hv
      rw [hu'] at hv
      by_cases hva : v = a
      · subst hva
        simp only [beq_self_eq_true, if_true] at hv ⊢
        push_cast
        omega
      · have hne : ¬ (a == v) = true := by
          simp [Ne.symm hva]
        simp only [if_neg hva] at hv
        rw [if_neg hne]
        push_cast at hv ⊢
        omega

/-- **Corollary 3.2** (conservative exactification).  The configuration decomposes as the applied
odometer plus the transported charge. -/
theorem applyOdo_add (η u : V → ℤ) (w : V) :
    L.applyOdo η u w + ∑ v, L.mat w v * u v = η w := by
  rw [applyOdo]
  ring

/-- **Theorem 3.1, abelian property.**  Any two legal executions reaching stable configurations
have the same odometer. -/
theorem odo_eq_of_legal_stable {η : V → ℤ} {l l' : List V}
    (hl : L.Legal η l) (hl' : L.Legal η l')
    (hs : L.Stable (L.applyOdo η (L.odo l))) (hs' : L.Stable (L.applyOdo η (L.odo l'))) :
    L.odo l = L.odo l' := by
  have hnn : ∀ (m : List V) (v : V), 0 ≤ L.odo m v := by
    intro m v
    rw [odo_apply]
    positivity
  funext v
  exact le_antisymm (L.odo_le_of_legal (hnn l') hs' hl v) (L.odo_le_of_legal (hnn l) hs hl' v)

/-! ## Stabilization -/

/-- The configuration reached after running an execution list. -/
def configAfter (L : ReducedLaplacian V) (η : V → ℤ) : List V → (V → ℤ)
  | [] => η
  | v :: rest => configAfter L (L.topple η v) rest

@[simp] theorem configAfter_nil (η : V → ℤ) : L.configAfter η [] = η := rfl

@[simp] theorem configAfter_cons (η : V → ℤ) (v : V) (rest : List V) :
    L.configAfter η (v :: rest) = L.configAfter (L.topple η v) rest := rfl

theorem configAfter_eq_applyOdo (η : V → ℤ) (l : List V) :
    L.configAfter η l = L.applyOdo η (L.odo l) := by
  induction l generalizing η with
  | nil =>
      rw [configAfter_nil]
      exact (L.applyOdo_zero η).symm
  | cons v rest ih =>
      rw [configAfter_cons, ih, topple_eq_applyOdo, applyOdo_applyOdo]
      congr 1
      funext z
      rw [odo_apply, odo_apply, List.count_cons]
      by_cases hz : z = v
      · subst hz
        simp only [beq_self_eq_true, if_true]
        push_cast
        ring
      · have hne : ¬ (v == z) = true := by simp [Ne.symm hz]
        rw [if_neg hne, if_neg hz]
        push_cast
        ring

theorem Legal_append_singleton (η : V → ℤ) (l : List V) (v : V) :
    L.Legal η (l ++ [v]) ↔ L.Legal η l ∧ (L.deg v : ℤ) ≤ L.configAfter η l v := by
  induction l generalizing η with
  | nil => simp [Legal]
  | cons a rest ih =>
      rw [List.cons_append, Legal_cons, Legal_cons, ih, configAfter_cons]
      tauto

theorem Legal_mono {η η' : V → ℤ} (hle : ∀ w, η w ≤ η' w) {l : List V} (hl : L.Legal η l) :
    L.Legal η' l := by
  induction l generalizing η η' with
  | nil => trivial
  | cons v rest ih =>
      obtain ⟨hv, hrest⟩ := hl
      refine ⟨le_trans hv (hle v), ih (fun w => ?_) hrest⟩
      rw [topple, topple]
      have := hle w
      omega

theorem configAfter_nonneg {η : V → ℤ} (hη : ∀ w, 0 ≤ η w) {l : List V} (hl : L.Legal η l) :
    ∀ w, 0 ≤ L.configAfter η l w := by
  induction l generalizing η with
  | nil => exact hη
  | cons v rest ih =>
      obtain ⟨hv, hrest⟩ := hl
      exact ih (L.topple_nonneg hη hv) hrest

/-- **Theorem 3.1, existence.**  Every nonnegative configuration has a legal execution reaching a
stable configuration. -/
theorem exists_legal_stable [Nonempty V] {η : V → ℤ} (hη : ∀ w, 0 ≤ η w) :
    ∃ l : List V, L.Legal η l ∧ L.Stable (L.applyOdo η (L.odo l)) := by
  classical
  set S : Set ℕ := {n | ∃ l : List V, l.length = n ∧ L.Legal η l} with hS
  have hne : S.Nonempty := ⟨0, [], rfl, trivial⟩
  have hbdd : ∀ n ∈ S, (n : ℝ) ≤ L.work η := by
    rintro n ⟨l, rfl, hl⟩
    exact L.length_le_work hη hl
  obtain ⟨N, hNbig⟩ := exists_nat_ge (L.work η)
  have hbddA : BddAbove S := ⟨N, fun n hn => Nat.cast_le.mp (le_trans (hbdd n hn) hNbig)⟩
  have hmem : sSup S ∈ S := Nat.sSup_mem hne hbddA
  obtain ⟨l, hlen, hl⟩ := hmem
  refine ⟨l, hl, ?_⟩
  intro v
  by_contra hcon
  push Not at hcon
  have hstep : L.Legal η (l ++ [v]) := by
    rw [Legal_append_singleton]
    refine ⟨hl, ?_⟩
    rw [configAfter_eq_applyOdo]
    exact hcon
  have hmem2 : (l ++ [v]).length ∈ S := ⟨l ++ [v], rfl, hstep⟩
  have hle := le_csSup hbddA hmem2
  rw [List.length_append, List.length_singleton, hlen] at hle
  omega

/-! ## The stabilization map and the exchange law -/

theorem configAfter_append (η : V → ℤ) (l m : List V) :
    L.configAfter η (l ++ m) = L.configAfter (L.configAfter η l) m := by
  induction l generalizing η with
  | nil => rfl
  | cons v rest ih =>
      rw [List.cons_append, configAfter_cons, configAfter_cons, ih]

theorem Legal_append (η : V → ℤ) (l m : List V) :
    L.Legal η (l ++ m) ↔ L.Legal η l ∧ L.Legal (L.configAfter η l) m := by
  induction l generalizing η with
  | nil => simp [Legal]
  | cons v rest ih =>
      rw [List.cons_append, Legal_cons, Legal_cons, ih, configAfter_cons]
      tauto

theorem applyOdo_add_const (η y u : V → ℤ) :
    L.applyOdo (fun w => η w + y w) u = fun w => L.applyOdo η u w + y w := by
  funext w
  rw [applyOdo, applyOdo]
  ring

/-- A legal execution list reaching a stable configuration. -/
noncomputable def stabList [Nonempty V] (η : V → ℤ) : List V :=
  if h : ∀ w, 0 ≤ η w then Classical.choose (L.exists_legal_stable h) else []

/-- The stabilization odometer. -/
noncomputable def stabOdo [Nonempty V] (η : V → ℤ) : V → ℤ := L.odo (L.stabList η)

/-- The stabilization of a configuration. -/
noncomputable def stab [Nonempty V] (η : V → ℤ) : V → ℤ := L.applyOdo η (L.stabOdo η)

theorem legal_stabList [Nonempty V] {η : V → ℤ} (hη : ∀ w, 0 ≤ η w) :
    L.Legal η (L.stabList η) := by
  rw [stabList, dif_pos hη]
  exact (Classical.choose_spec (L.exists_legal_stable hη)).1

theorem stable_stab [Nonempty V] {η : V → ℤ} (hη : ∀ w, 0 ≤ η w) : L.Stable (L.stab η) := by
  rw [stab, stabOdo, stabList, dif_pos hη]
  exact (Classical.choose_spec (L.exists_legal_stable hη)).2

/-- The stabilization is computed by any legal execution reaching a stable configuration. -/
theorem stabOdo_eq [Nonempty V] {η : V → ℤ} (hη : ∀ w, 0 ≤ η w) {l : List V}
    (hl : L.Legal η l) (hs : L.Stable (L.applyOdo η (L.odo l))) :
    L.stabOdo η = L.odo l := by
  refine L.odo_eq_of_legal_stable (L.legal_stabList hη) hl ?_ hs
  have := L.stable_stab hη
  rwa [stab, stabOdo] at this

theorem stab_eq [Nonempty V] {η : V → ℤ} (hη : ∀ w, 0 ≤ η w) {l : List V}
    (hl : L.Legal η l) (hs : L.Stable (L.applyOdo η (L.odo l))) :
    L.stab η = L.applyOdo η (L.odo l) := by
  rw [stab, L.stabOdo_eq hη hl hs]

theorem stab_nonneg [Nonempty V] {η : V → ℤ} (hη : ∀ w, 0 ≤ η w) (w : V) : 0 ≤ L.stab η w := by
  have hcfg := L.configAfter_nonneg hη (L.legal_stabList hη) w
  rwa [configAfter_eq_applyOdo] at hcfg

/-- **Lemma 4.1** (AR.15).  Formation and stabilization exchange. -/
theorem stab_stab_add [Nonempty V] {x y : V → ℤ} (hx : ∀ w, 0 ≤ x w) (hy : ∀ w, 0 ≤ y w) :
    L.stab (fun w => L.stab x w + y w) = L.stab (fun w => x w + y w) := by
  have hxy : ∀ w, 0 ≤ x w + y w := fun w => by
    have := hx w
    have := hy w
    omega
  have hsy : ∀ w, 0 ≤ L.stab x w + y w := fun w => by
    have := L.stab_nonneg hx w
    have := hy w
    omega
  set l : List V := L.stabList x with hl
  set m : List V := L.stabList (fun w => L.stab x w + y w) with hm
  have hlegall : L.Legal (fun w => x w + y w) l :=
    L.Legal_mono (fun w => by have := hy w; omega) (L.legal_stabList hx)
  have hcfgl : L.configAfter (fun w => x w + y w) l = fun w => L.stab x w + y w := by
    rw [configAfter_eq_applyOdo, applyOdo_add_const]
    rfl
  have hlegalm : L.Legal (fun w => L.stab x w + y w) m := L.legal_stabList hsy
  have hlegal : L.Legal (fun w => x w + y w) (l ++ m) := by
    rw [Legal_append]
    exact ⟨hlegall, by rw [hcfgl]; exact hlegalm⟩
  have hend : L.applyOdo (fun w => x w + y w) (L.odo (l ++ m))
      = L.stab (fun w => L.stab x w + y w) := by
    rw [← configAfter_eq_applyOdo, configAfter_append, hcfgl, configAfter_eq_applyOdo]
    rfl
  have hstable : L.Stable (L.applyOdo (fun w => x w + y w) (L.odo (l ++ m))) := by
    rw [hend]
    exact L.stable_stab hsy
  rw [L.stab_eq hxy hlegal hstable, hend]

/-! ## Green conservation and exact lineage work -/

section Green

variable [Nonempty V]

/-- The Laplacian as a linear equivalence. -/
noncomputable def actEquiv : (V → ℝ) ≃ₗ[ℝ] (V → ℝ) :=
  LinearEquiv.ofBijective L.actMap ⟨L.injective_actMap, L.surjective_actMap⟩

/-- The Green operator (AR.17). -/
noncomputable def green (b : V → ℝ) : V → ℝ := L.actEquiv.symm b

theorem act_green (b : V → ℝ) : L.act (L.green b) = b := by
  have := L.actEquiv.apply_symm_apply b
  rw [green]
  exact this

theorem green_act (h : V → ℝ) : L.green (L.act h) = h := by
  have := L.actEquiv.symm_apply_apply h
  rw [green]
  exact this

/-- The Green quadratic form. -/
noncomputable def greenForm (b : V → ℝ) : ℝ := ∑ v, b v * L.green b v

omit [Nonempty V] in
/-- **(AR.19).**  Exact balance: the transported charge is the source minus the endpoint. -/
theorem act_odo_eq (η u : V → ℤ) (w : V) :
    (∑ v, L.mat w v * u v) = η w - L.applyOdo η u w := by
  rw [applyOdo]
  ring

/-- The lineage work of an odometer (AR.18). -/
noncomputable def lineageWork (u : V → ℤ) : ℝ :=
  ∑ v, (u v : ℝ) * L.act (fun z => (u z : ℝ)) v

theorem sum_potential_mul_mat (v : V) :
    (∑ w, L.potential w * ((L.mat w v : ℤ) : ℝ)) = 1 := by
  have h := L.act_potential v
  rw [act] at h
  rw [← h]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [L.mat_symm w v]
  ring

/-- **(AR.20).**  Total-repair conservation: the number of repairs is the potential of the
transported charge. -/
theorem sum_odo_eq_potential_pairing (u : V → ℤ) :
    (∑ v, (u v : ℝ)) = ∑ w, L.potential w * L.act (fun z => (u z : ℝ)) w := by
  have hswap : (∑ w, L.potential w * L.act (fun z => (u z : ℝ)) w)
      = ∑ w, ∑ v, L.potential w * (((L.mat w v : ℤ) : ℝ) * (u v : ℝ)) := by
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [act, Finset.mul_sum]
  rw [hswap, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hfac : (∑ w, L.potential w * (((L.mat w v : ℤ) : ℝ) * (u v : ℝ)))
      = (∑ w, L.potential w * ((L.mat w v : ℤ) : ℝ)) * (u v : ℝ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring
  rw [hfac, L.sum_potential_mul_mat v, one_mul]

/-- **(AR.21).**  The lineage work is the Green form of the transported charge. -/
theorem lineageWork_eq_greenForm (u : V → ℤ) :
    L.lineageWork u = L.greenForm (L.act fun z => (u z : ℝ)) := by
  rw [lineageWork, greenForm]
  have hgreen : L.green (L.act fun z => (u z : ℝ)) = fun z => (u z : ℝ) :=
    L.green_act _
  rw [hgreen]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

end Green

/-! ## The sandpile observer group -/

/-- The lattice of transported charges. -/
def chargeLattice : Submodule ℤ (V → ℤ) :=
  Submodule.span ℤ (Set.range fun v : V => fun w : V => L.mat w v)

/-- The sandpile observer group (AR.23). -/
abbrev observerGroup : Type _ := (V → ℤ) ⧸ L.chargeLattice

theorem applyOdo_sub_mem_chargeLattice (η u : V → ℤ) :
    (fun w => η w - L.applyOdo η u w) ∈ L.chargeLattice := by
  classical
  have hrw : (fun w => η w - L.applyOdo η u w) = ∑ v, u v • fun w : V => L.mat w v := by
    funext w
    rw [applyOdo, Finset.sum_apply]
    have hterm : ∀ v : V, (u v • fun z : V => L.mat z v) w = L.mat w v * u v := by
      intro v
      rw [Pi.smul_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl fun v _ => hterm v]
    ring
  rw [hrw]
  refine Submodule.sum_mem _ fun v _ => ?_
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)

/-- **(AR.23).**  The observer class of a stabilization is unchanged. -/
theorem observer_class_applyOdo (η u : V → ℤ) :
    (Submodule.Quotient.mk (L.applyOdo η u) : L.observerGroup) = Submodule.Quotient.mk η := by
  rw [eq_comm, Submodule.Quotient.eq]
  exact L.applyOdo_sub_mem_chargeLattice η u

/-- **(AR.23).**  The observer class of a stabilized sum is the sum of classes. -/
theorem observer_class_stab [Nonempty V] (η : V → ℤ) :
    (Submodule.Quotient.mk (L.stab η) : L.observerGroup) = Submodule.Quotient.mk η := by
  rw [stab]
  exact L.observer_class_applyOdo η _

/-! ## Positive definiteness of the Green form -/

section Positivity

variable [Nonempty V]

omit [Nonempty V] in
/-- The Laplacian pairing is symmetric. -/
theorem act_pairing_symm (x y : V → ℝ) :
    (∑ v, x v * L.act y v) = ∑ v, y v * L.act x v := by
  have hL : ∀ z w : V → ℝ, (∑ v, z v * L.act w v)
      = ∑ v, ∑ u, z v * (((L.mat v u : ℤ) : ℝ) * w u) := by
    intro z w
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [act, Finset.mul_sum]
  rw [hL, hL, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
  rw [L.mat_symm u v]
  ring

omit [Nonempty V] in
/-- The reduced Laplacian form is nonnegative. -/
theorem quadratic_nonneg (x : V → ℝ) : 0 ≤ ∑ v, x v * L.act x v := by
  have h := L.two_mul_quadratic x
  have h1 : (0 : ℝ) ≤ ∑ v, ∑ w, (L.edge v w : ℝ) * (x v - x w) ^ 2 :=
    Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun w _ => by positivity
  have h2 : (0 : ℝ) ≤ ∑ v, (L.sinkEdge v : ℝ) * x v ^ 2 :=
    Finset.sum_nonneg fun v _ => by positivity
  linarith

/-- The Green form is nonnegative. -/
theorem greenForm_nonneg (b : V → ℝ) : 0 ≤ L.greenForm b := by
  have hq := L.quadratic_nonneg (L.green b)
  rw [greenForm]
  have hrw : (∑ v, b v * L.green b v) = ∑ v, L.green b v * L.act (L.green b) v := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [L.act_green b]
    ring
  rw [hrw]
  exact hq

omit [Nonempty V] in
/-- **Positive definiteness.**  The reduced Laplacian form vanishes only at zero. -/
theorem quadratic_pos {x : V → ℝ} (hx : ∃ v, x v ≠ 0) : 0 < ∑ v, x v * L.act x v := by
  have hnn : 0 ≤ ∑ v, x v * L.act x v := by
    have h := L.two_mul_quadratic x
    have h1 : (0 : ℝ) ≤ ∑ v, ∑ w, (L.edge v w : ℝ) * (x v - x w) ^ 2 :=
      Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun w _ => by positivity
    have h2 : (0 : ℝ) ≤ ∑ v, (L.sinkEdge v : ℝ) * x v ^ 2 :=
      Finset.sum_nonneg fun v _ => by positivity
    linarith
  rcases lt_or_eq_of_le hnn with h | h
  · exact h
  · exfalso
    obtain ⟨v₀, hv₀⟩ := hx
    have hq := L.two_mul_quadratic x
    rw [← h] at hq
    have h1 : (0 : ℝ) ≤ ∑ v, ∑ w, (L.edge v w : ℝ) * (x v - x w) ^ 2 :=
      Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun w _ => by positivity
    have h2 : (0 : ℝ) ≤ ∑ v, (L.sinkEdge v : ℝ) * x v ^ 2 :=
      Finset.sum_nonneg fun v _ => by positivity
    have hz1 : (∑ v, ∑ w, (L.edge v w : ℝ) * (x v - x w) ^ 2) = 0 := by linarith
    have hz2 : (∑ v, (L.sinkEdge v : ℝ) * x v ^ 2) = 0 := by linarith
    have hedge : ∀ v w, 0 < L.edge v w → x v = x w := by
      intro v w hvw
      have hinner : (∑ w, (L.edge v w : ℝ) * (x v - x w) ^ 2) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun v _ =>
          Finset.sum_nonneg fun w _ => by positivity)).1 hz1 v (mem_univ v)
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => by positivity)).1 hinner w
        (mem_univ w)
      have hne : (L.edge v w : ℝ) ≠ 0 := by exact_mod_cast hvw.ne'
      have hsq : (x v - x w) ^ 2 = 0 := by
        rcases mul_eq_zero.1 hterm with hc | hc
        · exact absurd hc hne
        · exact hc
      have : x v - x w = 0 := by
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
      linarith
    have hsink : ∀ v, 0 < L.sinkEdge v → x v = 0 := by
      intro v hv
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => by positivity)).1 hz2 v
        (mem_univ v)
      have hne : (L.sinkEdge v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
      have hsq : x v ^ 2 = 0 := by
        rcases mul_eq_zero.1 hterm with hc | hc
        · exact absurd hc hne
        · exact hc
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
    obtain ⟨w, hpath, hw⟩ := L.reaches_sink v₀
    have hconst : ∀ y, Relation.ReflTransGen (fun a b => 0 < L.edge a b) v₀ y → x y = x v₀ := by
      intro y hy
      induction hy with
      | refl => rfl
      | tail _ hstep ih => rw [← ih]; exact (hedge _ _ hstep).symm
    have : x v₀ = 0 := by
      rw [← hconst w hpath]
      exact hsink w hw
    exact hv₀ this

/-- The Green form is positive on nonzero sources. -/
theorem greenForm_pos {b : V → ℝ} (hb : ∃ v, b v ≠ 0) : 0 < L.greenForm b := by
  have hx : ∃ v, L.green b v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hzero : L.green b = fun _ => 0 := funext hcon
    have := L.act_green b
    rw [hzero] at this
    obtain ⟨v, hv⟩ := hb
    refine hv ?_
    rw [← this, act]
    simp
  have hq := L.quadratic_pos hx
  rw [greenForm]
  have hrw : (∑ v, b v * L.green b v) = ∑ v, L.green b v * L.act (L.green b) v := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [L.act_green b]
    ring
  rw [hrw]
  exact hq

end Positivity

/-! ## Green bilinearity -/

section Bilinear

variable [Nonempty V]

/-- The Green pairing. -/
noncomputable def greenPair (b c : V → ℝ) : ℝ := ∑ v, b v * L.green c v

theorem greenForm_eq_pair (b : V → ℝ) : L.greenForm b = L.greenPair b b := rfl

theorem green_add (b c : V → ℝ) : L.green (b + c) = L.green b + L.green c := by
  rw [green, green, green, map_add]

theorem green_smul (t : ℝ) (b : V → ℝ) : L.green (t • b) = t • L.green b := by
  rw [green, green, map_smul]

theorem greenPair_symm (b c : V → ℝ) : L.greenPair b c = L.greenPair c b := by
  have h := L.act_pairing_symm (L.green b) (L.green c)
  rw [L.act_green b, L.act_green c] at h
  rw [greenPair, greenPair]
  calc (∑ v, b v * L.green c v) = ∑ v, L.green c v * b v := by
        refine Finset.sum_congr rfl fun v _ => ?_
        ring
    _ = ∑ v, L.green b v * c v := h.symm
    _ = ∑ v, c v * L.green b v := by
        refine Finset.sum_congr rfl fun v _ => ?_
        ring

theorem greenPair_add_right (b c d : V → ℝ) :
    L.greenPair b (c + d) = L.greenPair b c + L.greenPair b d := by
  rw [greenPair, greenPair, greenPair, green_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  show b v * (L.green c v + L.green d v) = _
  ring

theorem greenPair_smul_right (t : ℝ) (b c : V → ℝ) :
    L.greenPair b (t • c) = t * L.greenPair b c := by
  rw [greenPair, greenPair, green_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  show b v * (t * L.green c v) = t * (b v * L.green c v)
  ring

theorem greenPair_smul_left (t : ℝ) (b c : V → ℝ) :
    L.greenPair (t • b) c = t * L.greenPair b c := by
  rw [greenPair_symm, greenPair_smul_right, greenPair_symm]

theorem greenPair_add_left (b c d : V → ℝ) :
    L.greenPair (b + c) d = L.greenPair b d + L.greenPair c d := by
  rw [greenPair_symm, greenPair_add_right, L.greenPair_symm b d, L.greenPair_symm c d]

/-- The exact expansion of the Green form on a sum. -/
theorem greenForm_add (b c : V → ℝ) :
    L.greenForm (b + c) = L.greenForm b + 2 * L.greenPair b c + L.greenForm c := by
  rw [greenForm_eq_pair, greenPair_add_left, greenPair_add_right, greenPair_add_right,
    L.greenPair_symm c b, greenForm_eq_pair, greenForm_eq_pair]
  ring

theorem greenForm_smul (t : ℝ) (b : V → ℝ) : L.greenForm (t • b) = t ^ 2 * L.greenForm b := by
  rw [greenForm_eq_pair, greenPair_smul_left, greenPair_smul_right, greenForm_eq_pair]
  ring

end Bilinear

/-! ## The source-driven sequence and global properness -/

section Sequence

variable [Nonempty V] (η a : V → ℤ)

/-- The configuration after `n` source additions (AR.14). -/
def sourceAdd (_L : ReducedLaplacian V) (η a : V → ℤ) (n : ℕ) : V → ℤ :=
  fun w => η w + (n : ℤ) * a w

omit [Nonempty V] in
theorem sourceAdd_apply (n : ℕ) (w : V) : L.sourceAdd η a n w = η w + (n : ℤ) * a w := rfl

/-- The `n`-th stabilized configuration (AR.14). -/
noncomputable def stabIter (n : ℕ) : V → ℤ := L.stab (L.sourceAdd η a n)

/-- The `n`-th odometer (AR.14). -/
noncomputable def odoIter (n : ℕ) : V → ℤ := L.stabOdo (L.sourceAdd η a n)

/-- The `n`-th lineage work (AR.18). -/
noncomputable def workIter (n : ℕ) : ℝ := L.lineageWork (L.odoIter η a n)

omit [Nonempty V] in
theorem sourceAdd_nonneg (hη : ∀ w, 0 ≤ η w) (ha : ∀ w, 0 ≤ a w) (n : ℕ) (w : V) :
    0 ≤ L.sourceAdd η a n w := by
  rw [sourceAdd_apply]
  have h1 := hη w
  have h2 := ha w
  positivity

theorem stabIter_stable (hη : ∀ w, 0 ≤ η w) (ha : ∀ w, 0 ≤ a w) (n : ℕ) :
    L.Stable (L.stabIter η a n) :=
  L.stable_stab (L.sourceAdd_nonneg η a hη ha n)

theorem stabIter_nonneg (hη : ∀ w, 0 ≤ η w) (ha : ∀ w, 0 ≤ a w) (n : ℕ) (w : V) :
    0 ≤ L.stabIter η a n w :=
  L.stab_nonneg (L.sourceAdd_nonneg η a hη ha n) w

/-- **(AR.19).**  Exact balance for the source-driven sequence. -/
theorem act_odoIter (n : ℕ) (w : V) :
    (∑ v, L.mat w v * L.odoIter η a n v) = L.sourceAdd η a n w - L.stabIter η a n w := by
  rw [odoIter, stabIter, stab]
  exact L.act_odo_eq _ _ w

theorem act_real_odoIter (n : ℕ) (w : V) :
    L.act (fun z => (L.odoIter η a n z : ℝ)) w
      = ((L.sourceAdd η a n w - L.stabIter η a n w : ℤ) : ℝ) := by
  rw [act, ← L.act_odoIter η a n w]
  have hstep : (∑ v, ((L.mat w v : ℤ) : ℝ) * ((L.odoIter η a n v : ℤ) : ℝ))
      = ∑ v, ((L.mat w v * L.odoIter η a n v : ℤ) : ℝ) := by
    refine Finset.sum_congr rfl fun v _ => ?_
    push_cast
    ring
  rw [hstep, ← Int.cast_sum]

/-- The real transported charge of the `n`-th step. -/
noncomputable def chargeIter (n : ℕ) : V → ℝ :=
  fun w => ((L.sourceAdd η a n w - L.stabIter η a n w : ℤ) : ℝ)

theorem chargeIter_apply (n : ℕ) (w : V) :
    L.chargeIter η a n w = ((L.sourceAdd η a n w - L.stabIter η a n w : ℤ) : ℝ) := rfl

/-- **(AR.21).**  The lineage work is the Green form of the transported charge. -/
theorem workIter_eq (n : ℕ) : L.workIter η a n = L.greenForm (L.chargeIter η a n) := by
  rw [workIter, L.lineageWork_eq_greenForm]
  congr 1
  funext w
  rw [L.act_real_odoIter η a n w, chargeIter_apply]

/-- The residual part of the transported charge. -/
noncomputable def residual (n : ℕ) : V → ℝ :=
  fun w => ((η w - L.stabIter η a n w : ℤ) : ℝ)

theorem residual_eq (n : ℕ) :
    L.residual η a n = fun w => ((η w - L.stabIter η a n w : ℤ) : ℝ) := rfl

theorem chargeIter_decomp (n : ℕ) :
    L.chargeIter η a n = (n : ℝ) • (fun w => (a w : ℝ)) + L.residual η a n := by
  funext w
  rw [chargeIter_apply, sourceAdd_apply]
  show ((η w + (n : ℤ) * a w - L.stabIter η a n w : ℤ) : ℝ)
    = (n : ℝ) * (a w : ℝ) + ((η w - L.stabIter η a n w : ℤ) : ℝ)
  push_cast
  ring

/-- **(AR.21) expanded.**  Exact quadratic expansion of the lineage work. -/
theorem workIter_expand (n : ℕ) :
    L.workIter η a n
      = (n : ℝ) ^ 2 * L.greenForm (fun w => (a w : ℝ))
        + 2 * ((n : ℝ) * L.greenPair (fun w => (a w : ℝ)) (L.residual η a n))
        + L.greenForm (L.residual η a n) := by
  rw [workIter_eq, chargeIter_decomp, greenForm_add, greenForm_smul, greenPair_smul_left]

omit [Nonempty V] in
/-- The finite set of stable configurations. -/
theorem finite_stableConfigs :
    {s : V → ℤ | ∀ v, 0 ≤ s v ∧ s v < (L.deg v : ℤ)}.Finite := by
  have hset : {s : V → ℤ | ∀ v, 0 ≤ s v ∧ s v < (L.deg v : ℤ)}
      = Set.pi Set.univ fun v => Set.Ico (0 : ℤ) (L.deg v) := by
    ext s
    simp [Set.mem_pi, Set.mem_Ico]
  rw [hset]
  exact Set.Finite.pi fun v => Set.finite_Ico _ _

theorem stabIter_mem (hη : ∀ w, 0 ≤ η w) (ha : ∀ w, 0 ≤ a w) (n : ℕ) :
    L.stabIter η a n ∈ {s : V → ℤ | ∀ v, 0 ≤ s v ∧ s v < (L.deg v : ℤ)} :=
  fun v => ⟨L.stabIter_nonneg η a hη ha n v, L.stabIter_stable η a hη ha n v⟩

/-- A uniform bound for the residual contributions. -/
theorem exists_residual_bound (hη : ∀ w, 0 ≤ η w) (ha : ∀ w, 0 ≤ a w) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
      |L.greenPair (fun w => (a w : ℝ)) (L.residual η a n)| ≤ M
        ∧ |L.greenForm (L.residual η a n)| ≤ M := by
  classical
  set F : (V → ℤ) → ℝ := fun s =>
    |L.greenPair (fun w => (a w : ℝ)) (fun w => ((η w - s w : ℤ) : ℝ))|
      + |L.greenForm (fun w => ((η w - s w : ℤ) : ℝ))| with hF
  have hfin := (L.finite_stableConfigs).image F
  obtain ⟨M₀, hM₀⟩ := hfin.bddAbove
  refine ⟨max M₀ 0, le_max_right _ _, fun n => ?_⟩
  have hmem : F (L.stabIter η a n) ∈ F '' {s : V → ℤ | ∀ v, 0 ≤ s v ∧ s v < (L.deg v : ℤ)} :=
    ⟨_, L.stabIter_mem η a hη ha n, rfl⟩
  have hle : F (L.stabIter η a n) ≤ M₀ := hM₀ hmem
  have hle' : F (L.stabIter η a n) ≤ max M₀ 0 := le_trans hle (le_max_left _ _)
  rw [hF] at hle'
  rw [L.residual_eq η a n]
  constructor
  · have hnn : 0 ≤ |L.greenForm (fun w => ((η w - L.stabIter η a n w : ℤ) : ℝ))| := abs_nonneg _
    linarith
  · have hnn : 0 ≤ |L.greenPair (fun w => (a w : ℝ))
        (fun w => ((η w - L.stabIter η a n w : ℤ) : ℝ))| := abs_nonneg _
    linarith

/-- **Theorem 6.1** (AR.27).  Bounded lineage work selects the neutral source. -/
theorem bddAbove_workIter_iff (hstab : L.Stable η) (hη : ∀ w, 0 ≤ η w) (ha : ∀ w, 0 ≤ a w) :
    BddAbove (Set.range (L.workIter η a)) ↔ a = 0 := by
  constructor
  · intro hbdd
    by_contra hne
    have hex : ∃ v, (a v : ℝ) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne (funext fun v => by exact_mod_cast hcon v)
    have hα : 0 < L.greenForm (fun w => (a w : ℝ)) := L.greenForm_pos hex
    obtain ⟨M, hM0, hM⟩ := L.exists_residual_bound η a hη ha
    have hlb : ∀ n : ℕ, (n : ℝ) ^ 2 * L.greenForm (fun w => (a w : ℝ)) - 2 * ((n : ℝ) * M) - M
        ≤ L.workIter η a n := by
      intro n
      rw [L.workIter_expand η a n]
      have h1 := (hM n).1
      have h2 := (hM n).2
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hb1 : -(M) ≤ L.greenPair (fun w => (a w : ℝ)) (L.residual η a n) :=
        neg_le_of_abs_le h1
      have hb2 : -(M) ≤ L.greenForm (L.residual η a n) := neg_le_of_abs_le h2
      nlinarith [hb1, hb2, hn, hM0]
    obtain ⟨B, hB⟩ := hbdd
    have hBle : ∀ n : ℕ, L.workIter η a n ≤ B := fun n => hB ⟨n, rfl⟩
    have hB0 : 0 ≤ B := by
      have h0 := hBle 0
      rw [L.workIter_eq η a 0] at h0
      exact le_trans (L.greenForm_nonneg _) h0
    set α : ℝ := L.greenForm (fun w => (a w : ℝ)) with hαdef
    obtain ⟨N, hN⟩ := exists_nat_ge (max 1 ((B + M + 2 * M + 1) / α))
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := le_trans (le_max_left _ _) hN
    have hNα : B + M + 2 * M + 1 ≤ (N : ℝ) * α := by
      have hle := le_trans (le_max_right 1 ((B + M + 2 * M + 1) / α)) hN
      rw [div_le_iff₀ hα] at hle
      linarith
    have hbig : B < (N : ℝ) ^ 2 * α - 2 * ((N : ℝ) * M) - M := by
      have hstep : B + M + 1 ≤ (N : ℝ) * α - 2 * M := by linarith
      have hpos : (0 : ℝ) < (N : ℝ) * α - 2 * M := by linarith
      have hmul : (1 : ℝ) * ((N : ℝ) * α - 2 * M) ≤ (N : ℝ) * ((N : ℝ) * α - 2 * M) :=
        mul_le_mul_of_nonneg_right hN1 hpos.le
      nlinarith [hmul, hstep, hM0, hB0]
    exact absurd (le_trans (hlb N) (hBle N)) (not_le.2 hbig)
  · rintro rfl
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    have hzeroFun : (0 : V → ℤ) = fun _ : V => (0 : ℤ) := rfl
    have hsrc : L.sourceAdd η (fun _ => 0) n = η := by
      funext w
      rw [sourceAdd_apply]
      ring
    have hodo : L.odoIter η (fun _ => 0) n = fun _ => 0 := by
      rw [odoIter, hsrc]
      refine L.stabOdo_eq hη (l := []) trivial ?_
      have hodozero : L.odo ([] : List V) = fun _ => 0 := by
        funext w
        rw [odo_apply]
        simp
      have : L.applyOdo η (L.odo ([] : List V)) = η := by
        rw [hodozero, L.applyOdo_zero]
      rw [this]
      exact hstab
    rw [hzeroFun, workIter, hodo, lineageWork]
    have hzero : L.act (fun z => ((0 : ℤ) : ℝ)) = fun _ => 0 := by
      funext w
      rw [act]
      simp
    rw [hzero]
    simp

end Sequence

/-! ## Recurrence and return holonomy -/

section Recurrence

variable [Nonempty V] (η a : V → ℤ)

/-- **(AR.16).**  The stabilized sequence is the orbit of one source-addition map. -/
theorem stabIter_succ (hη : ∀ w, 0 ≤ η w) (ha : ∀ w, 0 ≤ a w) (n : ℕ) :
    L.stabIter η a (n + 1) = L.stab (fun w => L.stabIter η a n w + a w) := by
  rw [stabIter, stabIter]
  have hx : ∀ w, 0 ≤ L.sourceAdd η a n w := L.sourceAdd_nonneg η a hη ha n
  have hexch := L.stab_stab_add hx ha
  rw [hexch]
  congr 1
  funext w
  rw [sourceAdd_apply, sourceAdd_apply]
  push_cast
  ring

/-- **(AR.23).**  The observer class advances by the source class. -/
theorem observer_class_stabIter (n : ℕ) :
    (Submodule.Quotient.mk (L.stabIter η a n) : L.observerGroup)
      = Submodule.Quotient.mk (L.sourceAdd η a n) :=
  L.observer_class_stab _

/-- **(AR.23).**  The stabilized sequence is eventually periodic. -/
theorem exists_eventual_period (hη : ∀ w, 0 ≤ η w) (ha : ∀ w, 0 ≤ a w) :
    ∃ m P : ℕ, 0 < P ∧ ∀ k, m ≤ k → L.stabIter η a (k + P) = L.stabIter η a k := by
  classical
  have hfin := L.finite_stableConfigs
  have hmaps : Set.MapsTo (fun n : ℕ => L.stabIter η a n) Set.univ
      {s : V → ℤ | ∀ v, 0 ≤ s v ∧ s v < (L.deg v : ℤ)} :=
    fun n _ => L.stabIter_mem η a hη ha n
  obtain ⟨i, _, j, _, hne, hval⟩ :=
    (Set.infinite_univ (α := ℕ)).exists_ne_map_eq_of_mapsTo hmaps hfin
  have hstep : ∀ p q : ℕ, p < q → L.stabIter η a p = L.stabIter η a q →
      ∃ m P : ℕ, 0 < P ∧ ∀ k, m ≤ k → L.stabIter η a (k + P) = L.stabIter η a k := by
    intro p q hpq heq
    refine ⟨p, q - p, by omega, ?_⟩
    intro k hk
    induction k with
    | zero =>
        have hp : p = 0 := by omega
        subst hp
        simpa [Nat.sub_zero] using heq.symm
    | succ k ih =>
        rcases Nat.lt_or_ge p (k + 1) with hkp | hkp
        · have hkk : p ≤ k := by omega
          have hprev := ih hkk
          rw [show k + 1 + (q - p) = (k + (q - p)) + 1 by omega,
            L.stabIter_succ η a hη ha, L.stabIter_succ η a hη ha, hprev]
        · have hkp' : p = k + 1 := by omega
          subst hkp'
          simpa [show k + 1 + (q - (k + 1)) = q by omega] using heq.symm
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hstep i j hlt hval
  · exact hstep j i hlt hval.symm

/-- **(AR.24).**  A return after `P` additions has odometer `P · G a`. -/
theorem return_odometer {z : V → ℤ} {P : ℕ}
    (hret : L.stab (fun w => z w + (P : ℤ) * a w) = z) :
    (fun w => (L.stabOdo (fun w => z w + (P : ℤ) * a w) w : ℝ))
      = (P : ℝ) • L.green (fun w => (a w : ℝ)) := by
  have hact : ∀ w, L.act (fun t => (L.stabOdo (fun w => z w + (P : ℤ) * a w) t : ℝ)) w
      = (P : ℝ) * (a w : ℝ) := by
    intro w
    have hbal := L.act_odo_eq (fun w => z w + (P : ℤ) * a w)
      (L.stabOdo fun w => z w + (P : ℤ) * a w) w
    rw [← stab, hret] at hbal
    have hbal' : (∑ v, L.mat w v * L.stabOdo (fun w => z w + (P : ℤ) * a w) v)
        = (P : ℤ) * a w := by
      rw [hbal]
      ring
    rw [act]
    have hcast : (∑ v, ((L.mat w v : ℤ) : ℝ)
        * ((L.stabOdo (fun w => z w + (P : ℤ) * a w) v : ℤ) : ℝ))
        = ∑ v, ((L.mat w v * L.stabOdo (fun w => z w + (P : ℤ) * a w) v : ℤ) : ℝ) := by
      refine Finset.sum_congr rfl fun v _ => ?_
      push_cast
      ring
    rw [hcast, ← Int.cast_sum, hbal']
    push_cast
    ring
  have hsm : (fun w => (P : ℝ) * (a w : ℝ)) = (P : ℝ) • fun w => (a w : ℝ) := rfl
  have hgreen : L.green ((P : ℝ) • fun w => (a w : ℝ))
      = fun t => (L.stabOdo (fun w => z w + (P : ℤ) * a w) t : ℝ) := by
    rw [← hsm, ← funext hact, L.green_act]
  rw [L.green_smul] at hgreen
  exact hgreen.symm

/-- **(AR.25).**  The closed-loop lineage work of a return is `P²` times the Green energy. -/
theorem return_work {z : V → ℤ} {P : ℕ}
    (hret : L.stab (fun w => z w + (P : ℤ) * a w) = z) :
    L.lineageWork (L.stabOdo (fun w => z w + (P : ℤ) * a w))
      = (P : ℝ) ^ 2 * L.greenForm (fun w => (a w : ℝ)) := by
  have hqr := L.return_odometer a hret
  have hpt : ∀ v, ((L.stabOdo (fun w => z w + (P : ℤ) * a w) v : ℤ) : ℝ)
      = (P : ℝ) * L.green (fun w => (a w : ℝ)) v := fun v => congrFun hqr v
  have hact : ∀ v, L.act (fun t => ((L.stabOdo (fun w => z w + (P : ℤ) * a w) t : ℤ) : ℝ)) v
      = (P : ℝ) * (a v : ℝ) := by
    intro v
    rw [hqr]
    have hlin : L.act ((P : ℝ) • L.green fun w => (a w : ℝ))
        = (P : ℝ) • L.act (L.green fun w => (a w : ℝ)) := L.actMap.map_smul _ _
    rw [hlin, L.act_green]
    rfl
  rw [lineageWork]
  have hsum : (∑ v, ((L.stabOdo (fun w => z w + (P : ℤ) * a w) v : ℤ) : ℝ)
      * L.act (fun t => ((L.stabOdo (fun w => z w + (P : ℤ) * a w) t : ℤ) : ℝ)) v)
      = ∑ v, ((P : ℝ) * L.green (fun w => (a w : ℝ)) v) * ((P : ℝ) * (a v : ℝ)) := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hpt v, hact v]
  rw [hsum, greenForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

end Recurrence

/-! ## The cofinal lineage limits -/

section Limits

open Filter
open scoped Topology

variable [Nonempty V] (η a : V → ℤ)

theorem odoIter_eq_green (n : ℕ) :
    (fun w => (L.odoIter η a n w : ℝ)) = L.green (L.chargeIter η a n) := by
  have hact : L.act (fun w => (L.odoIter η a n w : ℝ)) = L.chargeIter η a n := by
    funext w
    rw [L.act_real_odoIter η a n w, chargeIter_apply]
  rw [← hact, L.green_act]

/-- A uniform bound for the residual Green vector. -/
theorem exists_green_residual_bound (hη : ∀ w, 0 ≤ η w) (ha : ∀ w, 0 ≤ a w) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (v : V), |L.green (L.residual η a n) v| ≤ M := by
  classical
  set F : (V → ℤ) → ℝ := fun s =>
    ∑ v, |L.green (fun w => ((η w - s w : ℤ) : ℝ)) v| with hF
  have hfin := (L.finite_stableConfigs).image F
  obtain ⟨M₀, hM₀⟩ := hfin.bddAbove
  refine ⟨max M₀ 0, le_max_right _ _, fun n v => ?_⟩
  have hmem : F (L.stabIter η a n) ∈ F '' {s : V → ℤ | ∀ v, 0 ≤ s v ∧ s v < (L.deg v : ℤ)} :=
    ⟨_, L.stabIter_mem η a hη ha n, rfl⟩
  have hle : F (L.stabIter η a n) ≤ max M₀ 0 := le_trans (hM₀ hmem) (le_max_left _ _)
  rw [L.residual_eq η a n]
  refine le_trans ?_ hle
  rw [hF]
  refine Finset.single_le_sum (f := fun v => |L.green
    (fun w => ((η w - L.stabIter η a n w : ℤ) : ℝ)) v|) (fun i _ => abs_nonneg _) (mem_univ v)

theorem chargeIter_green_decomp (n : ℕ) (v : V) :
    (L.odoIter η a n v : ℝ)
      = (n : ℝ) * L.green (fun w => (a w : ℝ)) v + L.green (L.residual η a n) v := by
  have h := congrFun (L.odoIter_eq_green η a n) v
  rw [h, chargeIter_decomp, L.green_add, L.green_smul]
  rfl

/-- **(AR.22), first limit.**  The odometer grows linearly with Green slope. -/
theorem tendsto_odoIter_div (hη : ∀ w, 0 ≤ η w) (ha : ∀ w, 0 ≤ a w) (v : V) :
    Tendsto (fun n : ℕ => (L.odoIter η a n v : ℝ) / (n : ℝ)) atTop
      (𝓝 (L.green (fun w => (a w : ℝ)) v)) := by
  obtain ⟨M, hM0, hM⟩ := L.exists_green_residual_bound η a hη ha
  have hupper : Tendsto (fun n : ℕ => M / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat M
  have hlower : Tendsto (fun n : ℕ => -(M / (n : ℝ))) atTop (𝓝 0) := by
    have := hupper.neg
    rwa [neg_zero] at this
  have hb : ∀ n : ℕ, |L.green (L.residual η a n) v / (n : ℝ)| ≤ M / (n : ℝ) := by
    intro n
    rw [abs_div, Nat.abs_cast]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      gcongr
      exact hM n v
  have hzero : Tendsto (fun n : ℕ => L.green (L.residual η a n) v / (n : ℝ)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper (fun n => ?_) (fun n => ?_)
    · exact neg_le_of_abs_le (hb n)
    · exact le_of_abs_le (hb n)
  have heq : ∀ n : ℕ, 1 ≤ n →
      (L.odoIter η a n v : ℝ) / (n : ℝ)
        = L.green (fun w => (a w : ℝ)) v + L.green (L.residual η a n) v / (n : ℝ) := by
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    rw [L.chargeIter_green_decomp η a n v]
    field_simp
  have hlim : Tendsto (fun n : ℕ => L.green (fun w => (a w : ℝ)) v
      + L.green (L.residual η a n) v / (n : ℝ)) atTop
      (𝓝 (L.green (fun w => (a w : ℝ)) v + 0)) := tendsto_const_nhds.add hzero
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (heq n hn).symm

/-- **(AR.22), second limit.**  The lineage work grows quadratically with the Green energy. -/
theorem tendsto_workIter_div (hη : ∀ w, 0 ≤ η w) (ha : ∀ w, 0 ≤ a w) :
    Tendsto (fun n : ℕ => L.workIter η a n / (n : ℝ) ^ 2) atTop
      (𝓝 (L.greenForm (fun w => (a w : ℝ)))) := by
  obtain ⟨M, hM0, hM⟩ := L.exists_residual_bound η a hη ha
  have hupper : Tendsto (fun n : ℕ => (2 * M) / (n : ℝ) + M / (n : ℝ) ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (2 * M) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (2 * M)
    have h2 : Tendsto (fun n : ℕ => M / (n : ℝ) ^ 2) atTop (𝓝 0) := by
      have hsq : Tendsto (fun n : ℕ => ((n : ℝ)) ^ 2) atTop atTop := by
        have hb := (tendsto_natCast_atTop_atTop (R := ℝ))
        have := hb.atTop_mul_atTop₀ hb
        exact this.congr fun n => by ring
      have hinv := hsq.inv_tendsto_atTop.const_mul M
      rw [mul_zero] at hinv
      refine hinv.congr fun n => ?_
      show M * ((n : ℝ) ^ 2)⁻¹ = M / (n : ℝ) ^ 2
      rw [div_eq_mul_inv]
    have := h1.add h2
    rwa [add_zero] at this
  have hlower : Tendsto (fun n : ℕ => -((2 * M) / (n : ℝ) + M / (n : ℝ) ^ 2)) atTop (𝓝 0) := by
    have := hupper.neg
    rwa [neg_zero] at this
  have hb : ∀ n : ℕ, 1 ≤ n →
      |L.workIter η a n / (n : ℝ) ^ 2 - L.greenForm (fun w => (a w : ℝ))|
        ≤ (2 * M) / (n : ℝ) + M / (n : ℝ) ^ 2 := by
    intro n hn
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hexp := L.workIter_expand η a n
      have hdiv : L.workIter η a n / (n : ℝ) ^ 2 - L.greenForm (fun w => (a w : ℝ))
          = 2 * L.greenPair (fun w => (a w : ℝ)) (L.residual η a n) / (n : ℝ)
            + L.greenForm (L.residual η a n) / (n : ℝ) ^ 2 := by
        rw [hexp]
        field_simp
        ring
      rw [hdiv]
      refine le_trans (abs_add_le _ _) ?_
      have hA : |2 * L.greenPair (fun w => (a w : ℝ)) (L.residual η a n) / (n : ℝ)|
          ≤ (2 * M) / (n : ℝ) := by
        rw [abs_div, Nat.abs_cast, abs_mul]
        have h2 : |(2 : ℝ)| = 2 := by norm_num
        rw [h2]
        gcongr
        exact (hM n).1
      have hB : |L.greenForm (L.residual η a n) / (n : ℝ) ^ 2| ≤ M / (n : ℝ) ^ 2 := by
        rw [abs_div, abs_pow, Nat.abs_cast]
        gcongr
        exact (hM n).2
      linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun n : ℕ => L.greenForm (fun w => (a w : ℝ))
      - ((2 * M) / (n : ℝ) + M / (n : ℝ) ^ 2))
    (h := fun n : ℕ => L.greenForm (fun w => (a w : ℝ))
      + ((2 * M) / (n : ℝ) + M / (n : ℝ) ^ 2)) ?_ ?_ ?_ ?_
  · have := (tendsto_const_nhds (x := L.greenForm (fun w => (a w : ℝ)))
      (f := (atTop : Filter ℕ))).add hlower
    rw [add_zero] at this
    exact this.congr fun n => by ring
  · have := (tendsto_const_nhds (x := L.greenForm (fun w => (a w : ℝ)))
      (f := (atTop : Filter ℕ))).add hupper
    rwa [add_zero] at this
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have := neg_le_of_abs_le (hb n hn)
    linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have := le_of_abs_le (hb n hn)
    linarith

end Limits

end ReducedLaplacian

/-! ## The two-vertex prediction -/

namespace TwoVertex

open GaloisForLFunctions.HTGeometry.ReducedLaplacian

/-- Two non-sink vertices joined by one edge, each joined once to the sink (AR.28). -/
def pair : ReducedLaplacian (Fin 2) where
  edge i j := if i = j then 0 else 1
  sinkEdge _ := 1
  edge_symm i j := by
    by_cases h : i = j
    · subst h
      rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
  edge_self i := by rw [if_pos rfl]
  reaches_sink v := ⟨v, Relation.ReflTransGen.refl, by norm_num⟩

@[simp] theorem pair_deg (i : Fin 2) : pair.deg i = 2 := by
  rw [ReducedLaplacian.deg, Fin.sum_univ_two]
  fin_cases i <;> norm_num [pair]

theorem pair_mat (i j : Fin 2) : pair.mat i j = if i = j then 2 else -1 := by
  rw [ReducedLaplacian.mat]
  by_cases h : i = j
  · rw [if_pos h, if_pos h, pair_deg]
    norm_num
  · rw [if_neg h, if_neg h]
    show -((if i = j then 0 else 1 : ℕ) : ℤ) = -1
    rw [if_neg h]
    norm_num

/-- The source is one unit at the first vertex. -/
def src : Fin 2 → ℤ := fun i => if i = 0 then 1 else 0

/-- The holonomy odometer of the period-three cycle (AR.30). -/
def holonomy : Fin 2 → ℤ := fun i => if i = 0 then 2 else 1

/-- **(AR.29).**  Three copies of the source are the transported charge of `(2,1)`. -/
theorem pair_act_holonomy (w : Fin 2) :
    (∑ v, pair.mat w v * holonomy v) = 3 * src w := by
  rw [Fin.sum_univ_two]
  fin_cases w <;> simp [pair_mat, holonomy, src]

/-- The starting stable state. -/
def start : Fin 2 → ℤ := fun _ => 1

theorem start_stable : pair.Stable start := by
  intro v
  rw [start, pair_deg]
  norm_num

/-- The three-step legal execution of `start + 3 · src`. -/
def cycleList : List (Fin 2) := [0, 0, 1]

theorem cycle_legal : pair.Legal (fun w => start w + (3 : ℤ) * src w) cycleList := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pair_deg]
    show (2 : ℤ) ≤ start 0 + 3 * src 0
    norm_num [start, src]
  · rw [pair_deg]
    show (2 : ℤ) ≤ pair.topple (fun w => start w + (3 : ℤ) * src w) 0 0
    rw [ReducedLaplacian.topple, pair_mat]
    norm_num [start, src]
  · rw [pair_deg]
    show (2 : ℤ) ≤ pair.topple (pair.topple (fun w => start w + (3 : ℤ) * src w) 0) 0 1
    rw [ReducedLaplacian.topple, ReducedLaplacian.topple, pair_mat]
    norm_num [start, src, pair_mat]
  · trivial

theorem cycle_odo : pair.odo cycleList = holonomy := by
  funext v
  rw [ReducedLaplacian.odo_apply, holonomy, cycleList]
  fin_cases v <;> decide

theorem cycle_endpoint :
    pair.applyOdo (fun w => start w + (3 : ℤ) * src w) (pair.odo cycleList) = start := by
  funext w
  rw [ReducedLaplacian.applyOdo, cycle_odo, pair_act_holonomy]
  show start w + (3 : ℤ) * src w - 3 * src w = start w
  ring

/-- **(AR.30).**  Three source additions return the observer to `(1,1)` with odometer `(2,1)`. -/
theorem pair_return :
    pair.stab (fun w => start w + (3 : ℤ) * src w) = start
      ∧ pair.stabOdo (fun w => start w + (3 : ℤ) * src w) = holonomy := by
  have hnn : ∀ w, 0 ≤ start w + (3 : ℤ) * src w := by
    intro w
    show (0 : ℤ) ≤ start w + 3 * src w
    fin_cases w <;> norm_num [start, src]
  have hstable : pair.Stable
      (pair.applyOdo (fun w => start w + (3 : ℤ) * src w) (pair.odo cycleList)) := by
    rw [cycle_endpoint]
    exact start_stable
  refine ⟨?_, ?_⟩
  · rw [pair.stab_eq hnn cycle_legal hstable, cycle_endpoint]
  · rw [pair.stabOdo_eq hnn cycle_legal hstable, cycle_odo]

/-- **(AR.31).**  The fundamental-loop lineage work of the period-three observer is six. -/
theorem pair_cycle_work :
    pair.lineageWork holonomy = 6 := by
  rw [ReducedLaplacian.lineageWork]
  have hact : ∀ w : Fin 2, pair.act (fun z => (holonomy z : ℝ)) w = 3 * (src w : ℝ) := by
    intro w
    rw [ReducedLaplacian.act, Fin.sum_univ_two]
    fin_cases w <;> norm_num [pair_mat, holonomy, src]
  rw [Fin.sum_univ_two, hact, hact]
  norm_num [holonomy, src]

end TwoVertex

end GaloisForLFunctions.HTGeometry
