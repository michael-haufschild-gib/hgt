import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RightUnitriangularInduction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicInductionInStages

/-! The right unitriangular parabolic lies in the mirabolic subgroup when
its right block has positive rank. Removing the final row preserves its
upper-triangular conditions on the remaining rows. -/

noncomputable section
open GaloisForLFunctions WindowedLandauTheory.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.GLq

variable {g a b : ℕ} [Fact g.Prime]

/-- The right block and the zeros below it can be read from the ambient rows. -/
theorem mem_rightUnitriangularParabolic_rows (x : Gn g (a + b)) :
    x ∈ (rightUnitriangularParabolic g a b).map (twoBlockParabolic g a b).subtype ↔
      ∀ (i j : Fin (a + b)), a ≤ (i : ℕ) →
        (j < i → x.val i j = 0) ∧ (i = j → x.val i j = 1) := by
  have he :
      x ∈ (rightUnitriangularParabolic g a b).map (twoBlockParabolic g a b).subtype ↔
        InPar a x.val ∧ IsUniUp (br a b x.val) := by
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.property, hp⟩
    · rintro ⟨hp, hD⟩
      exact ⟨⟨x, hp⟩, hD, rfl⟩
  rw [he]
  constructor
  · rintro ⟨hp, hD⟩ i j hi
    have hn := i.isLt
    let u : Fin b := ⟨i.val - a, by omega⟩
    have hi' : Fin.natAdd a u = i := Fin.ext (Nat.add_sub_of_le hi)
    rw [← hi']
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · refine ⟨fun _ => hp _ _ j.isLt (by simp), fun hj => ?_⟩
      have hval : a + u.val = j.val := congrArg Fin.val hj
      have hlt := j.isLt
      omega
    · rw [← br_apply_add x.val u j]
      exact ⟨fun hj => (hD u j).1 (Nat.lt_of_add_lt_add_left hj),
        fun hj => (hD u j).2 ((Fin.natAdd_inj a).mp hj)⟩
  · intro h
    refine ⟨fun i j hj hi => (h i j hi).1 (hj.trans_le hi), fun i j => ?_⟩
    rw [br_apply_add]
    exact ⟨fun hj => (h _ _ (by simp)).1 (Nat.add_lt_add_left hj a),
      fun hj => (h _ _ (by simp)).2 (congrArg (Fin.natAdd a) hj)⟩

/-- An upper parabolic with a positive unitriangular right block fixes the final covector. -/
theorem rightUnitriangularParabolic_le_mirabolic :
    (rightUnitriangularParabolic g a (b + 1)).map (twoBlockParabolic g a (b + 1)).subtype ≤
      mirabolicSubgroup g (a + b) := by
  intro x hx
  rw [mem_mirabolicSubgroup_iff]
  have h := (mem_rightUnitriangularParabolic_rows x).mp hx
  intro j
  obtain rfl | hj := eq_or_lt_of_le (Fin.le_last j)
  · rw [Pi.single_eq_same]
    exact (h _ _ (Nat.le_add_right a b)).2 rfl
  · rw [Pi.single_eq_of_ne hj.ne]
    exact (h _ _ (Nat.le_add_right a b)).1 hj

/-- The right unitriangular parabolic viewed as a subgroup of the mirabolic group. -/
def mirabolicRightUnitriangular (g a b : ℕ) [Fact g.Prime] :
    Subgroup (mirabolicSubgroup g (a + b)) :=
  ((rightUnitriangularParabolic g a (b + 1)).map
    (twoBlockParabolic g a (b + 1)).subtype).comap (mirabolicSubgroup g (a + b)).subtype

/-- Inside the mirabolic group, the right-block condition reduces to that
condition on the leading block. -/
theorem mem_mirabolicRightUnitriangular_succ (u : mirabolicSubgroup g (a + (b + 1))) :
    u ∈ mirabolicRightUnitriangular g a (b + 1) ↔
      mirabolicLevi u ∈
        (rightUnitriangularParabolic g a (b + 1)).map (twoBlockParabolic g a (b + 1)).subtype := by
  obtain ⟨A, v, eq⟩ := exists_mirabolicBlock u.property
  rw [show u = mirabolicUnit A v from Subtype.ext eq, mirabolicLevi_unit]
  change mirabolicBlock A v ∈
      (rightUnitriangularParabolic g a (b + 1 + 1)).map (twoBlockParabolic g a (b + 1 + 1)).subtype ↔ _
  rw [mem_rightUnitriangularParabolic_rows, mem_rightUnitriangularParabolic_rows]
  have hA (i j : Fin (a + (b + 1))) :
      (mirabolicBlock A v).val i.castSucc j.castSucc = A.val i j := by
    change (upperBlockMatrix A.val (fun i (_ : Fin 1) => v i) 1)
        (Fin.castAdd 1 i) (Fin.castAdd 1 j) = _
    simp [upperBlockMatrix]
  have hlast := (mem_mirabolicSubgroup_iff (mirabolicBlock A v)).mp (mirabolicBlock_mem A v)
  constructor
  · intro h i j hi
    have hh := h i.castSucc j.castSucc hi
    rw [hA] at hh
    exact ⟨fun hij => hh.1 (show j.val < i.val from hij),
      fun hij => hh.2 (congrArg Fin.castSucc hij)⟩
  · intro h i j hi
    induction i using Fin.lastCases with
    | last =>
      exact ⟨fun hij => (hlast j).trans (by
          have hj : j ≠ Fin.last (a + (b + 1)) := hij.ne
          rw [Pi.single_eq_of_ne hj]),
        fun hij => (hlast j).trans (by
          have hj : j = Fin.last (a + (b + 1)) := hij.symm
          rw [hj, Pi.single_eq_same])⟩
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        exact ⟨fun hj => (not_lt_of_ge (Fin.castSucc_lt_last i).le hj).elim,
          fun hj => (Fin.castSucc_ne_last i hj).elim⟩
      | cast j =>
        rw [hA]
        exact ⟨fun hj => (h i j hi).1 (show j.val < i.val from hj),
          fun hj => (h i j hi).2
            (Fin.ext (congrArg (fun t : Fin (a + (b + 1) + 1) => t.val) hj))⟩

/-- A right block of size one gives the entire mirabolic subgroup. -/
theorem mirabolicRightUnitriangular_zero :
    mirabolicRightUnitriangular g a 0 = ⊤ := by
  ext u
  simp only [Subgroup.mem_top, iff_true]
  change u.val ∈ (rightUnitriangularParabolic g a 1).map (twoBlockParabolic g a 1).subtype
  rw [mem_rightUnitriangularParabolic_rows]
  intro i j hi
  have he : i = Fin.last a := Fin.ext (Nat.le_antisymm (Nat.le_of_lt_succ i.isLt) hi)
  subst i
  rw [(mem_mirabolicSubgroup_iff u.val).mp u.property j]
  exact ⟨fun h => by rw [Pi.single_eq_of_ne h.ne],
    fun h => by subst j; rw [Pi.single_eq_same]⟩

/-- Induction in stages pulls the right-block condition back along
the leading block of the inducing subgroup. -/
theorem mirabolicRightUnitriangular_succ :
    mirabolicRightUnitriangular g a (b + 1) =
      ((mirabolicRightUnitriangular g a b).comap
        (mirabolicInducingLevi (m := a + b))).map (mirabolicInducingSubgroup g (a + b)).subtype := by
  ext u
  rw [mem_mirabolicRightUnitriangular_succ]
  constructor
  · intro hu
    have hk : u ∈ mirabolicInducingSubgroup g (a + b) :=
      rightUnitriangularParabolic_le_mirabolic hu
    exact ⟨⟨u, hk⟩, hu, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact hx

end GlobalTheory.GLq
