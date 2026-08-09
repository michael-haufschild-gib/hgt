import Mathlib

/-!
# Quadratic proof filling, closed endpoint, and open history

In the presentation `⟨a, b | [a,b]⟩` of `ℤ²` the null words `w n = aⁿ bⁿ a⁻ⁿ b⁻ⁿ` return to the
identity endpoint and have length `4n`, while the minimal number of relator cells needed to fill
them grows quadratically.  This file certifies

`area (nullWord n) = n²`

together with the endpoint return, the word length, and the orientation-blindness of the unsigned
cost.

The lower bound uses the integer Heisenberg group: the free group maps onto it with the relator
going to a central generator, so any filling by `k` conjugates of `[a,b]^{±1}` sends `w n` to a
central element of exponent at most `k` in absolute value, while `w n` itself has central exponent
`n²`.  The upper bound is the explicit `n × n` grid, assembled from the two commutator expansion
identities.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The integer Heisenberg group `ℤ³` with `(x,y,z)·(x',y',z') = (x+x', y+y', z+z'+x y')`. -/
@[ext]
structure Heis where
  /-- First coordinate. -/
  x : ℤ
  /-- Second coordinate. -/
  y : ℤ
  /-- Central coordinate. -/
  z : ℤ

namespace Heis

instance : Mul Heis := ⟨fun p q => ⟨p.x + q.x, p.y + q.y, p.z + q.z + p.x * q.y⟩⟩
instance : One Heis := ⟨⟨0, 0, 0⟩⟩
instance : Inv Heis := ⟨fun p => ⟨-p.x, -p.y, -p.z + p.x * p.y⟩⟩

@[simp] theorem mul_x (p q : Heis) : (p * q).x = p.x + q.x := rfl
@[simp] theorem mul_y (p q : Heis) : (p * q).y = p.y + q.y := rfl
@[simp] theorem mul_z (p q : Heis) : (p * q).z = p.z + q.z + p.x * q.y := rfl
@[simp] theorem one_x : (1 : Heis).x = 0 := rfl
@[simp] theorem one_y : (1 : Heis).y = 0 := rfl
@[simp] theorem one_z : (1 : Heis).z = 0 := rfl
@[simp] theorem inv_x (p : Heis) : p⁻¹.x = -p.x := rfl
@[simp] theorem inv_y (p : Heis) : p⁻¹.y = -p.y := rfl
@[simp] theorem inv_z (p : Heis) : p⁻¹.z = -p.z + p.x * p.y := rfl

instance : Group Heis where
  mul := (· * ·)
  one := 1
  inv := (·⁻¹)
  div p q := p * q⁻¹
  mul_assoc p q r := by ext <;> simp <;> ring
  one_mul p := by ext <;> simp
  mul_one p := by ext <;> simp
  inv_mul_cancel p := by ext <;> simp

/-- The central element of exponent `m`. -/
def center (m : ℤ) : Heis := ⟨0, 0, m⟩

@[simp] theorem center_x (m : ℤ) : (center m).x = 0 := rfl
@[simp] theorem center_y (m : ℤ) : (center m).y = 0 := rfl
@[simp] theorem center_z (m : ℤ) : (center m).z = m := rfl

@[simp] theorem center_zero : center 0 = 1 := rfl

theorem center_mul (m m' : ℤ) : center m * center m' = center (m + m') := by
  ext <;> simp [center]

/-- The central subgroup really is central. -/
theorem center_comm (m : ℤ) (p : Heis) : center m * p = p * center m := by
  ext <;> simp [center, add_comm]

theorem conj_center (g : Heis) (m : ℤ) : g * center m * g⁻¹ = center m := by
  rw [← center_comm, mul_assoc, mul_inv_cancel, mul_one]

theorem center_injective : Function.Injective center := by
  intro m m' h
  simpa using congrArg Heis.z h

theorem center_inv (m : ℤ) : (center m)⁻¹ = center (-m) := by
  ext <;> simp [center]

end Heis

section Words

/-- The group commutator `x y x⁻¹ y⁻¹`. -/
def comm {G : Type*} [Group G] (x y : G) : G := x * y * x⁻¹ * y⁻¹

theorem comm_def {G : Type*} [Group G] (x y : G) : comm x y = x * y * x⁻¹ * y⁻¹ := rfl

/-- **Left expansion of a commutator.** -/
theorem comm_mul_left {G : Type*} [Group G] (x y z : G) :
    comm (x * y) z = x * comm y z * x⁻¹ * comm x z := by
  simp only [comm_def]
  group

/-- **Right expansion of a commutator.** -/
theorem comm_mul_right {G : Type*} [Group G] (x y z : G) :
    comm x (y * z) = comm x y * (y * comm x z * y⁻¹) := by
  simp only [comm_def]
  group

theorem comm_one_right {G : Type*} [Group G] (x : G) : comm x 1 = 1 := by
  simp [comm_def]

theorem comm_inv {G : Type*} [Group G] (x y : G) : (comm x y)⁻¹ = comm y x := by
  simp only [comm_def]
  group

/-- The first generator of the free group on two letters. -/
def genA : FreeGroup (Fin 2) := FreeGroup.of 0

/-- The second generator of the free group on two letters. -/
def genB : FreeGroup (Fin 2) := FreeGroup.of 1

/-- The relator `[a,b]` of the standard presentation of `ℤ²`. -/
def relator : FreeGroup (Fin 2) := comm genA genB

/-- The null word `w n = aⁿ bⁿ a⁻ⁿ b⁻ⁿ`. -/
def nullWord (n : ℕ) : FreeGroup (Fin 2) := comm (genA ^ n) (genB ^ n)

end Words

section Heisenberg

/-- The Heisenberg representation of the free group on two letters. -/
def heisLift : FreeGroup (Fin 2) →* Heis :=
  FreeGroup.lift ![(⟨1, 0, 0⟩ : Heis), (⟨0, 1, 0⟩ : Heis)]

@[simp] theorem heisLift_genA : heisLift genA = ⟨1, 0, 0⟩ := by
  simp [heisLift, genA]

@[simp] theorem heisLift_genB : heisLift genB = ⟨0, 1, 0⟩ := by
  simp [heisLift, genB]

theorem heisLift_genA_pow (n : ℕ) : heisLift (genA ^ n) = ⟨(n : ℤ), 0, 0⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ m ih =>
    rw [pow_succ, _root_.map_mul, ih, heisLift_genA]
    ext <;> push_cast <;> simp

theorem heisLift_genB_pow (n : ℕ) : heisLift (genB ^ n) = ⟨0, (n : ℤ), 0⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ m ih =>
    rw [pow_succ, _root_.map_mul, ih, heisLift_genB]
    ext <;> push_cast <;> simp

@[simp] theorem heisLift_relator : heisLift relator = Heis.center 1 := by
  rw [relator, comm_def, _root_.map_mul, _root_.map_mul, _root_.map_mul, map_inv, map_inv,
    heisLift_genA, heisLift_genB]
  ext <;> simp [Heis.center]

/-- **The Heisenberg exponent of the null word is `n²`.** -/
theorem heisLift_nullWord (n : ℕ) : heisLift (nullWord n) = Heis.center ((n : ℤ) ^ 2) := by
  rw [nullWord, comm_def, _root_.map_mul, _root_.map_mul, _root_.map_mul, map_inv, map_inv,
    heisLift_genA_pow, heisLift_genB_pow]
  ext <;> simp [Heis.center]
  ring

end Heisenberg

section Filling

variable {G : Type*} [Group G]

theorem prod_conj (g : G) (l : List G) :
    (l.map fun t => g * t * g⁻¹).prod = g * l.prod * g⁻¹ := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons, List.prod_cons, ih, List.prod_cons]
    group

theorem prod_inv_reverse_map (l : List G) :
    ((l.map fun t => t⁻¹).reverse).prod = l.prod⁻¹ := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp [ih, mul_inv_rev]

theorem comm_one_left (x : G) : comm (1 : G) x = 1 := by
  simp [comm_def]

/-- The word of a filling cell: a conjugate of the relator or of its inverse. -/
def cellWord (c : FreeGroup (Fin 2) × Bool) : FreeGroup (Fin 2) :=
  c.1 * (if c.2 then relator else relator⁻¹) * c.1⁻¹

/-- A van Kampen filling of `w` by the listed relator cells. -/
def IsFilling (cells : List (FreeGroup (Fin 2) × Bool)) (w : FreeGroup (Fin 2)) : Prop :=
  w = (cells.map cellWord).prod

theorem isFilling_nil : IsFilling [] 1 := by simp [IsFilling]

theorem isFilling_append {c₁ c₂ : List (FreeGroup (Fin 2) × Bool)} {u v : FreeGroup (Fin 2)}
    (h₁ : IsFilling c₁ u) (h₂ : IsFilling c₂ v) : IsFilling (c₁ ++ c₂) (u * v) := by
  rw [IsFilling, List.map_append, List.prod_append, ← h₁, ← h₂]

theorem isFilling_relator : IsFilling [(1, true)] relator := by
  simp [IsFilling, cellWord]

theorem cellWord_flip (c : FreeGroup (Fin 2) × Bool) :
    cellWord (c.1, !c.2) = (cellWord c)⁻¹ := by
  cases hc : c.2 <;> simp only [cellWord, hc, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, if_true, if_false] <;> group

theorem isFilling_conj {cells : List (FreeGroup (Fin 2) × Bool)} {w : FreeGroup (Fin 2)}
    (h : IsFilling cells w) (g : FreeGroup (Fin 2)) :
    IsFilling (cells.map fun c => (g * c.1, c.2)) (g * w * g⁻¹) := by
  have hmap : ((cells.map fun c => (g * c.1, c.2)).map cellWord)
      = (cells.map cellWord).map (fun t => g * t * g⁻¹) := by
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun c _ => ?_
    simp only [Function.comp_apply, cellWord]
    group
  rw [IsFilling, hmap, prod_conj, ← h]

theorem isFilling_inv {cells : List (FreeGroup (Fin 2) × Bool)} {w : FreeGroup (Fin 2)}
    (h : IsFilling cells w) :
    IsFilling ((cells.map fun c => (c.1, !c.2)).reverse) w⁻¹ := by
  have hmap : (((cells.map fun c => (c.1, !c.2)).reverse).map cellWord)
      = ((cells.map cellWord).map fun t => t⁻¹).reverse := by
    rw [List.map_reverse, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun c _ => ?_
    simpa using cellWord_flip c
  rw [IsFilling, hmap, prod_inv_reverse_map, ← h]

/-- `w` admits a van Kampen filling with at most `k` relator cells. -/
def Fillable (k : ℕ) (w : FreeGroup (Fin 2)) : Prop :=
  ∃ cells : List (FreeGroup (Fin 2) × Bool), cells.length ≤ k ∧ IsFilling cells w

theorem Fillable.mono {k l : ℕ} {w : FreeGroup (Fin 2)} (h : Fillable k w) (hkl : k ≤ l) :
    Fillable l w := by
  obtain ⟨cells, hlen, hfill⟩ := h
  exact ⟨cells, hlen.trans hkl, hfill⟩

theorem fillable_one : Fillable 0 1 := ⟨[], le_refl 0, isFilling_nil⟩

theorem fillable_mul {k l : ℕ} {u v : FreeGroup (Fin 2)} (hu : Fillable k u)
    (hv : Fillable l v) : Fillable (k + l) (u * v) := by
  obtain ⟨c₁, h₁, f₁⟩ := hu
  obtain ⟨c₂, h₂, f₂⟩ := hv
  exact ⟨c₁ ++ c₂, by simpa using Nat.add_le_add h₁ h₂, isFilling_append f₁ f₂⟩

theorem Fillable.conj {k : ℕ} {w : FreeGroup (Fin 2)} (h : Fillable k w) (g : FreeGroup (Fin 2)) :
    Fillable k (g * w * g⁻¹) := by
  obtain ⟨cells, hlen, hfill⟩ := h
  exact ⟨cells.map fun c => (g * c.1, c.2), by simpa using hlen, isFilling_conj hfill g⟩

theorem Fillable.inv {k : ℕ} {w : FreeGroup (Fin 2)} (h : Fillable k w) : Fillable k w⁻¹ := by
  obtain ⟨cells, hlen, hfill⟩ := h
  exact ⟨(cells.map fun c => (c.1, !c.2)).reverse, by simpa using hlen, isFilling_inv hfill⟩

theorem fillable_relator : Fillable 1 relator := ⟨[(1, true)], by simp, isFilling_relator⟩

/-- The van Kampen area: the least number of relator cells in a filling. -/
noncomputable def area (w : FreeGroup (Fin 2)) : ℕ := sInf {k | Fillable k w}

theorem area_le {k : ℕ} {w : FreeGroup (Fin 2)} (h : Fillable k w) : area w ≤ k :=
  Nat.sInf_le h

theorem fillable_area {w : FreeGroup (Fin 2)} (h : ∃ k, Fillable k w) : Fillable (area w) w :=
  Nat.sInf_mem h

end Filling

section UpperBound

/-- **One row of the grid.**  `[a, bᵐ]` is filled by `m` relator cells. -/
theorem fillable_comm_genA_genB_pow (m : ℕ) : Fillable m (comm genA (genB ^ m)) := by
  induction m with
  | zero => simpa [pow_zero, comm_one_right] using fillable_one
  | succ p ih =>
    have hsplit : comm genA (genB ^ (p + 1))
        = comm genA genB * (genB * comm genA (genB ^ p) * genB⁻¹) := by
      rw [pow_succ']
      exact comm_mul_right genA genB (genB ^ p)
    rw [hsplit, ← relator]
    have := fillable_mul fillable_relator (ih.conj genB)
    simpa [Nat.add_comm] using this

/-- **The `n × m` grid.**  `[aⁿ, bᵐ]` is filled by `n · m` relator cells. -/
theorem fillable_comm_pow (n m : ℕ) : Fillable (n * m) (comm (genA ^ n) (genB ^ m)) := by
  induction n with
  | zero => simpa [pow_zero, comm_one_left] using fillable_one
  | succ p ih =>
    have hsplit : comm (genA ^ (p + 1)) (genB ^ m)
        = genA * comm (genA ^ p) (genB ^ m) * genA⁻¹ * comm genA (genB ^ m) := by
      rw [pow_succ']
      exact comm_mul_left genA (genA ^ p) (genB ^ m)
    rw [hsplit]
    have := fillable_mul (ih.conj genA) (fillable_comm_genA_genB_pow m)
    simpa [Nat.succ_mul] using this

/-- **The grid upper bound.** -/
theorem fillable_nullWord (n : ℕ) : Fillable (n ^ 2) (nullWord n) := by
  rw [nullWord, pow_two]
  exact fillable_comm_pow n n

end UpperBound

section LowerBound

theorem heisLift_cellWord (c : FreeGroup (Fin 2) × Bool) :
    heisLift (cellWord c) = Heis.center (if c.2 then 1 else -1) := by
  cases hc : c.2
  · simp only [cellWord, hc, Bool.false_eq_true, if_false, _root_.map_mul, map_inv,
      heisLift_relator, Heis.center_inv]
    exact Heis.conj_center _ _
  · simp only [cellWord, hc, if_true, _root_.map_mul, map_inv, heisLift_relator]
    exact Heis.conj_center _ _

/-- **A filling of `k` cells has central exponent at most `k`.** -/
theorem heisLift_of_isFilling {cells : List (FreeGroup (Fin 2) × Bool)} {w : FreeGroup (Fin 2)}
    (h : IsFilling cells w) : ∃ s : ℤ, |s| ≤ (cells.length : ℤ) ∧ heisLift w = Heis.center s := by
  subst h
  induction cells with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons c tl ih =>
    obtain ⟨s, hs, hcen⟩ := ih
    refine ⟨(if c.2 then (1 : ℤ) else -1) + s, ?_, ?_⟩
    · have habs : |(if c.2 then (1 : ℤ) else -1)| = 1 := by cases c.2 <;> simp
      calc |(if c.2 then (1 : ℤ) else -1) + s|
          ≤ |(if c.2 then (1 : ℤ) else -1)| + |s| := abs_add_le _ _
        _ ≤ 1 + (tl.length : ℤ) := by rw [habs]; linarith
        _ = ((c :: tl).length : ℤ) := by rw [List.length_cons]; push_cast; ring
    · rw [List.map_cons, List.prod_cons, _root_.map_mul, heisLift_cellWord, hcen, Heis.center_mul]

end LowerBound

section Area

/-- **The van Kampen area of the null word is exactly `n²`.** -/
theorem area_nullWord (n : ℕ) : area (nullWord n) = n ^ 2 := by
  refine le_antisymm (area_le (fillable_nullWord n)) ?_
  obtain ⟨cells, hlen, hfill⟩ := fillable_area ⟨n ^ 2, fillable_nullWord n⟩
  obtain ⟨s, hs, hcen⟩ := heisLift_of_isFilling hfill
  have hsn : s = (n : ℤ) ^ 2 :=
    Heis.center_injective (by rw [← hcen, heisLift_nullWord])
  have h1 : ((n : ℤ) ^ 2) ≤ (cells.length : ℤ) := by
    rw [← hsn]
    exact le_trans (le_abs_self s) hs
  have h2 : n ^ 2 ≤ cells.length := by exact_mod_cast h1
  exact h2.trans hlen

theorem fillable_inv_iff (k : ℕ) (w : FreeGroup (Fin 2)) : Fillable k w⁻¹ ↔ Fillable k w :=
  ⟨fun h => by simpa using h.inv, fun h => h.inv⟩

/-- **Unsigned filling cost forgets orientation.** -/
theorem area_inv (w : FreeGroup (Fin 2)) : area w⁻¹ = area w := by
  unfold area
  congr 1
  ext k
  exact fillable_inv_iff k w

theorem area_nullWord_inv (n : ℕ) : area (nullWord n)⁻¹ = n ^ 2 := by
  rw [area_inv, area_nullWord]

end Area

section Endpoint

theorem cellWord_mem_normalClosure (c : FreeGroup (Fin 2) × Bool) :
    cellWord c ∈ Subgroup.normalClosure ({relator} : Set (FreeGroup (Fin 2))) := by
  have hr : relator ∈ Subgroup.normalClosure ({relator} : Set (FreeGroup (Fin 2))) :=
    Subgroup.subset_normalClosure rfl
  have hnormal : (Subgroup.normalClosure ({relator} : Set (FreeGroup (Fin 2)))).Normal :=
    Subgroup.normalClosure_normal
  cases hc : c.2
  · simp only [cellWord, hc, Bool.false_eq_true, if_false]
    exact hnormal.conj_mem _ (inv_mem hr) _
  · simp only [cellWord, hc, if_true]
    exact hnormal.conj_mem _ hr _

theorem mem_normalClosure_of_isFilling {cells : List (FreeGroup (Fin 2) × Bool)}
    {w : FreeGroup (Fin 2)} (h : IsFilling cells w) :
    w ∈ Subgroup.normalClosure ({relator} : Set (FreeGroup (Fin 2))) := by
  subst h
  induction cells with
  | nil => simp
  | cons c tl ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_mem (cellWord_mem_normalClosure c) ih

theorem nullWord_mem_normalClosure (n : ℕ) :
    nullWord n ∈ Subgroup.normalClosure ({relator} : Set (FreeGroup (Fin 2))) := by
  obtain ⟨cells, _, hfill⟩ := fillable_nullWord n
  exact mem_normalClosure_of_isFilling hfill

/-- **The endpoint observer is constantly the identity** in the presented group `⟨a,b | [a,b]⟩`. -/
theorem nullWord_eq_one_in_quotient (n : ℕ) :
    (QuotientGroup.mk (nullWord n) :
        FreeGroup (Fin 2) ⧸ Subgroup.normalClosure ({relator} : Set (FreeGroup (Fin 2)))) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (nullWord_mem_normalClosure n)

theorem comm_eq_one_of_commGroup {G : Type*} [CommGroup G] (x y : G) : comm x y = 1 := by
  rw [comm_def, mul_comm x y]
  group

theorem map_comm {G H : Type*} [Group G] [Group H] (f : G →* H) (x y : G) :
    f (comm x y) = comm (f x) (f y) := by
  rw [comm_def, comm_def, _root_.map_mul, _root_.map_mul, _root_.map_mul, map_inv, map_inv]

/-- The abelianized endpoint reader, landing in `ℤ²`. -/
def abelLift : FreeGroup (Fin 2) →* Multiplicative (ℤ × ℤ) :=
  FreeGroup.lift ![Multiplicative.ofAdd (1, 0), Multiplicative.ofAdd (0, 1)]

/-- **The null word returns to the identity of `ℤ²`.** -/
theorem abelLift_nullWord (n : ℕ) : abelLift (nullWord n) = 1 := by
  rw [nullWord, map_comm, comm_eq_one_of_commGroup]

end Endpoint

section Length

/-- Two adjacent letters that do not cancel. -/
def NoCancel (p q : Fin 2 × Bool) : Prop := ¬ (p.1 = q.1 ∧ p.2 = !q.2)

theorem noCancel_self (x : Fin 2 × Bool) : NoCancel x x := by
  rintro ⟨-, h⟩
  cases hb : x.2 <;> rw [hb] at h <;> simp at h

theorem noCancel_of_ne {p q : Fin 2 × Bool} (h : p.1 ≠ q.1) : NoCancel p q := fun hc => h hc.1

/-- A list with no adjacent cancelling pair is already reduced. -/
theorem reduce_eq_self_of_isChain :
    ∀ {L : List (Fin 2 × Bool)}, List.IsChain NoCancel L → FreeGroup.reduce L = L := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons hd tl ih =>
    intro h
    have hcons := List.isChain_cons.mp h
    have hred := ih hcons.2
    rw [FreeGroup.reduce.cons, hred]
    cases tl with
    | nil => rfl
    | cons hd2 tl2 =>
      exact if_neg (hcons.1 hd2 (by simp))

theorem head?_replicate_append {α : Type*} (n : ℕ) (x : α) (L : List α) :
    (List.replicate n x ++ L).head? = if n = 0 then L.head? else some x := by
  cases n with
  | zero => simp
  | succ m => simp [List.replicate_succ]

theorem isChain_replicate_append {α : Type*} {R : α → α → Prop} {x : α} {L : List α} (n : ℕ)
    (hx : R x x) (hL : List.IsChain R L) (hb : ∀ y ∈ L.head?, R x y) :
    List.IsChain R (List.replicate n x ++ L) := by
  induction n with
  | zero => simpa using hL
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append]
    refine List.isChain_cons.mpr ⟨?_, ih⟩
    intro y hy
    rw [head?_replicate_append] at hy
    by_cases hm : m = 0
    · rw [if_pos hm] at hy
      exact hb y hy
    · rw [if_neg hm] at hy
      simp only [Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact hx

/-- The defining letter word of `w n`. -/
def nullList (n : ℕ) : List (Fin 2 × Bool) :=
  List.replicate n ((0 : Fin 2), true) ++ (List.replicate n ((1 : Fin 2), true) ++
    (List.replicate n ((0 : Fin 2), false) ++ List.replicate n ((1 : Fin 2), false)))

theorem isChain_nullList (n : ℕ) : List.IsChain NoCancel (nullList n) := by
  have hD : List.IsChain NoCancel (List.replicate n ((1 : Fin 2), false)) := by
    simpa using
      isChain_replicate_append (R := NoCancel) (x := ((1 : Fin 2), false)) (L := []) n
        (noCancel_self _) List.isChain_nil (by simp)
  have hCD : List.IsChain NoCancel
      (List.replicate n ((0 : Fin 2), false) ++ List.replicate n ((1 : Fin 2), false)) := by
    refine isChain_replicate_append n (noCancel_self _) hD ?_
    intro y hy
    rw [List.head?_replicate] at hy
    by_cases hn : n = 0
    · rw [if_pos hn] at hy; simp at hy
    · rw [if_neg hn] at hy
      simp only [Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact noCancel_of_ne (by decide)
  have hBCD : List.IsChain NoCancel (List.replicate n ((1 : Fin 2), true) ++
      (List.replicate n ((0 : Fin 2), false) ++ List.replicate n ((1 : Fin 2), false))) := by
    refine isChain_replicate_append n (noCancel_self _) hCD ?_
    intro y hy
    rw [head?_replicate_append] at hy
    by_cases hn : n = 0
    · rw [if_pos hn, hn] at hy; simp at hy
    · rw [if_neg hn] at hy
      simp only [Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact noCancel_of_ne (by decide)
  refine isChain_replicate_append n (noCancel_self _) hBCD ?_
  intro y hy
  rw [head?_replicate_append] at hy
  by_cases hn : n = 0
  · rw [if_pos hn, hn] at hy
    simp at hy
  · rw [if_neg hn] at hy
    simp only [Option.mem_def, Option.some.injEq] at hy
    subst hy
    exact noCancel_of_ne (by decide)

theorem mk_replicate (x : Fin 2 × Bool) (n : ℕ) :
    FreeGroup.mk (List.replicate n x) = FreeGroup.mk [x] ^ n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, pow_succ', ← ih, FreeGroup.mul_mk]
    rfl

theorem mk_nullList (n : ℕ) : FreeGroup.mk (nullList n) = nullWord n := by
  have hA : FreeGroup.mk (List.replicate n ((0 : Fin 2), true)) = genA ^ n := by
    rw [mk_replicate]; rfl
  have hB : FreeGroup.mk (List.replicate n ((1 : Fin 2), true)) = genB ^ n := by
    rw [mk_replicate]; rfl
  have hAinv : FreeGroup.mk (List.replicate n ((0 : Fin 2), false)) = (genA ^ n)⁻¹ := by
    rw [mk_replicate, ← inv_pow]
    congr 1
  have hBinv : FreeGroup.mk (List.replicate n ((1 : Fin 2), false)) = (genB ^ n)⁻¹ := by
    rw [mk_replicate, ← inv_pow]
    congr 1
  rw [nullList, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, hA, hB, hAinv, hBinv,
    nullWord, comm_def]
  group

theorem toWord_nullWord (n : ℕ) : (nullWord n).toWord = nullList n := by
  rw [← mk_nullList, FreeGroup.toWord_mk, reduce_eq_self_of_isChain (isChain_nullList n)]

/-- **The null word has length `4n`.** -/
theorem length_nullWord (n : ℕ) : (nullWord n).toWord.length = 4 * n := by
  rw [toWord_nullWord, nullList]
  simp only [List.length_append, List.length_replicate]
  ring

end Length

section Capstone

/-- **Endpoint return with quadratic minimal proof history.**  The null word is trivial in the
presented group and in `ℤ²`, has length `4n`, and its minimal van Kampen filling uses exactly `n²`
relator cells — the same as for the reversed word, so the unsigned cost forgets orientation. -/
theorem quadratic_filling_law (n : ℕ) :
    (QuotientGroup.mk (nullWord n) :
        FreeGroup (Fin 2) ⧸ Subgroup.normalClosure ({relator} : Set (FreeGroup (Fin 2)))) = 1 ∧
      abelLift (nullWord n) = 1 ∧
      (nullWord n).toWord.length = 4 * n ∧
      area (nullWord n) = n ^ 2 ∧
      area (nullWord n)⁻¹ = n ^ 2 :=
  ⟨nullWord_eq_one_in_quotient n, abelLift_nullWord n, length_nullWord n, area_nullWord n,
    area_nullWord_inv n⟩

end Capstone

end GaloisForLFunctions.HTGeometry
