import GaloisForLFunctions.HTGeometry.OneChannelRootProjection

/-! # Constructive solving through arbitrary repeated resonance

The iterated source readings conjugate the pencil on its full root block to
a nilpotent shift. Truncating and shifting those coordinates constructs the
exact defect projection and a preimage for every pencil power. The number
of independent compatibility readings is the smaller of the power and the
full root multiplicity; every solution is recovered modulo the actual kernel.
-/

noncomputable section
open Module Set

namespace HTGeometry.OneChannelParametrix
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (P : OneChannelParametrix K V) [FiniteDimensional K P.rootSpace]

theorem row_pencil_pow (n j : ℕ) (hj : j < P.rank) (x : V) :
    P.row j ((P.pencil^n) x) = if n ≤ j then P.row (j-n) x else 0 := by
  induction n generalizing j with
  | zero => simp only [pow_zero,Module.End.one_apply,Nat.zero_le,if_true,Nat.sub_zero]
  | succ n ih =>
      rw [pow_succ',Module.End.mul_apply]
      cases j with
      | zero => rw [row_zero,P.moment_range,if_neg (by omega : ¬n+1≤0)]
      | succ j =>
          rw [row_succ_pencil,P.obstruction_order.1 j (by change j<P.rank-1; omega),mul_zero,sub_zero,
            ih j (by omega)]
          simp only [Nat.succ_le_succ_iff,Nat.succ_sub_succ_eq_sub]

def headReadings (n : ℕ) : V →ₗ[K] (Fin P.rank → K) :=
  LinearMap.pi (fun j => if j.val<n then P.row j.val else 0)

def liftedReadings (n : ℕ) : V →ₗ[K] (Fin P.rank → K) :=
  LinearMap.pi (fun j => if j.val+n<P.rank then P.row (j.val+n) else 0)

def powerDefect (n : ℕ) : Module.End K V :=
  P.rootSpace.subtype.comp (P.rootCoordinates.symm.toLinearMap.comp (P.headReadings n))

def rootPowerLift (n : ℕ) : Module.End K V :=
  P.rootSpace.subtype.comp (P.rootCoordinates.symm.toLinearMap.comp (P.liftedReadings n))

theorem powerDefect_mem (n : ℕ) (x : V) : P.powerDefect n x ∈ P.rootSpace :=
  (P.rootCoordinates.symm (P.headReadings n x)).property

theorem rootPowerLift_mem (n : ℕ) (x : V) : P.rootPowerLift n x ∈ P.rootSpace :=
  (P.rootCoordinates.symm (P.liftedReadings n x)).property

theorem powerDefect_readings (n : ℕ) (x : V) (j : Fin P.rank) :
    P.row j.val (P.powerDefect n x) = if j.val<n then P.row j.val x else 0 := by
  have h := congrFun (P.rootCoordinates.apply_symm_apply (P.headReadings n x)) j
  change P.row j.val (P.powerDefect n x) = ((if j.val<n then P.row j.val else 0) x) at h
  split_ifs at h ⊢ <;> exact h

theorem rootPowerLift_readings (n : ℕ) (x : V) (j : Fin P.rank) :
    P.row j.val (P.rootPowerLift n x) = if j.val+n<P.rank then P.row (j.val+n) x else 0 := by
  have h := congrFun (P.rootCoordinates.apply_symm_apply (P.liftedReadings n x)) j
  change P.row j.val (P.rootPowerLift n x) = ((if j.val+n<P.rank then P.row (j.val+n) else 0) x) at h
  split_ifs at h ⊢ <;> exact h

omit [FiniteDimensional K P.rootSpace] in
theorem pencil_pow_mem_root (n : ℕ) {x : V} (hx : x ∈ P.rootSpace) :
    (P.pencil^n) x ∈ P.rootSpace := by
  induction n with
  | zero => exact hx
  | succ n ih =>
      rw [pow_succ',Module.End.mul_apply]
      exact P.pencil_mem_root ih

theorem rootPowerLift_equation (n : ℕ) (x : V) :
    (P.pencil^n) (P.rootPowerLift n x) = P.projection x-P.powerDefect n x := by
  apply congrArg Subtype.val (P.full_observations_injective (a₁ :=
    ⟨_,P.pencil_pow_mem_root n (P.rootPowerLift_mem n x)⟩) (a₂ :=
    ⟨_,P.rootSpace.sub_mem (P.projection_mem x) (P.powerDefect_mem n x)⟩) ?_)
  funext j
  change P.row j.val ((P.pencil^n) (P.rootPowerLift n x)) =
    P.row j.val (P.projection x-P.powerDefect n x)
  rw [P.row_pencil_pow n j.val j.isLt,map_sub,P.projection_readings x j,P.powerDefect_readings n x j]
  by_cases hn : n ≤ j.val
  · have hsum : j.val-n+n=j.val := Nat.sub_add_cancel hn
    rw [if_pos hn,P.rootPowerLift_readings n x ⟨j.val-n,by omega⟩,
      hsum,if_pos j.isLt,if_neg (by omega : ¬j.val<n),sub_zero]
  · rw [if_neg hn,if_pos (by omega : j.val<n),sub_self]

/-- A minimal finite source correction for each power, together with an actual preimage. -/
def powerSolver (n : ℕ) : Module.End K V :=
  (P.complementInverse^n).comp (1-P.projection)+P.rootPowerLift n

theorem powerSolver_equation (n : ℕ) (g : V) :
    (P.pencil^n) (P.powerSolver n g) = g-P.powerDefect n g := by
  change (P.pencil^n) ((P.complementInverse^n) (g-P.projection g)+P.rootPowerLift n g) = _
  rw [map_add,P.pencil_pow_complementInverse_pow n (P.remainder_mem g),P.rootPowerLift_equation]
  abel

theorem powerDefect_eq_zero_iff (n : ℕ) (g : V) :
    P.powerDefect n g = 0 ↔ ∀ j < min n P.rank, P.row j g = 0 := by
  constructor
  · intro hz j hj
    have he := P.powerDefect_readings n g ⟨j,lt_of_lt_of_le hj (min_le_right _ _)⟩
    rw [hz,map_zero,if_pos (lt_of_lt_of_le hj (min_le_left _ _))] at he
    exact he.symm
  · intro h
    apply P.root_complement_trivial (P.powerDefect_mem n g)
    apply (P.mem_complement _).mpr
    intro j hj
    rw [P.powerDefect_readings n g ⟨j,hj⟩]
    split_ifs with hn
    · exact h j (lt_min hn hj)
    · rfl

theorem powerDefect_idempotent (n : ℕ) (g : V) :
    P.powerDefect n (P.powerDefect n g) = P.powerDefect n g := by
  apply congrArg Subtype.val (P.full_observations_injective (a₁ :=
    ⟨_,P.powerDefect_mem n (P.powerDefect n g)⟩) (a₂ :=⟨_,P.powerDefect_mem n g⟩) ?_)
  funext j
  change P.row j.val (P.powerDefect n (P.powerDefect n g)) = P.row j.val (P.powerDefect n g)
  rw [P.powerDefect_readings,P.powerDefect_readings]
  split_ifs <;> rfl

/-- Exact repeated-resonance solvability, with every obstruction read from the original forcing. -/
theorem power_range_iff (n : ℕ) (g : V) :
    (∃ x, (P.pencil^n) x=g) ↔ ∀ j < min n P.rank, P.row j g=0 := by
  constructor
  · rintro ⟨x,rfl⟩ j hj
    rw [P.row_pencil_pow n j (lt_of_lt_of_le hj (min_le_right _ _)),if_neg (by omega)]
  · intro h
    refine ⟨P.powerSolver n g,?_⟩
    rw [P.powerSolver_equation,(P.powerDefect_eq_zero_iff n g).mpr h,sub_zero]

theorem power_all_solutions (n : ℕ) (g x : V) :
    (P.pencil^n) x=g ↔
      (∀ j < min n P.rank, P.row j g=0) ∧
      x-P.powerSolver n g ∈ LinearMap.ker (P.pencil^n) := by
  constructor
  · intro he
    have hh := (P.power_range_iff n g).mp ⟨x,he⟩
    refine ⟨hh,?_⟩
    change (P.pencil^n) (x-P.powerSolver n g)=0
    rw [map_sub,he,P.powerSolver_equation,(P.powerDefect_eq_zero_iff n g).mpr hh,sub_zero,sub_self]
  · rintro ⟨hh,hk⟩
    change (P.pencil^n) (x-P.powerSolver n g)=0 at hk
    rw [map_sub,P.powerSolver_equation,(P.powerDefect_eq_zero_iff n g).mpr hh,sub_zero] at hk
    exact sub_eq_zero.mp hk

end HTGeometry.OneChannelParametrix
