import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Logic.Relation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic

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

end ReducedLaplacian

end GaloisForLFunctions.HTGeometry
