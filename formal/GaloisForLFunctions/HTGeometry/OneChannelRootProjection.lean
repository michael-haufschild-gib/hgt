import GaloisForLFunctions.HTGeometry.OneChannelRootObservability

/-! # Source-observed projection and exact complementary inversion

Iterated defect readings identify the full generalized kernel. Their inverse
defines a projection on the entire ambient space which commutes with the
original pencil. A single explicit kernel correction to the parametrix
inverts every power on the complementary invariant space.
-/

noncomputable section
open Module Set

namespace HTGeometry.OneChannelParametrix
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (P : OneChannelParametrix K V) [FiniteDimensional K P.rootSpace]

abbrev rank : ℕ := Module.finrank K P.rootSpace

theorem full_observations_injective : Function.Injective (P.rootObservations P.rank) := by
  have hi := P.rootObservations_injective (P.rank-1) P.obstruction_order.1 P.obstruction_order.2
  have he : P.rank-1+1 = P.rank := by have hp : 0 < P.rank := P.root_finrank_pos; omega
  rwa [he] at hi

/-- All source readings give exact coordinates on the complete generalized kernel. -/
def rootCoordinates : P.rootSpace ≃ₗ[K] (Fin P.rank → K) :=
  (P.rootObservations P.rank).linearEquivOfInjective P.full_observations_injective (by simp)

@[simp] theorem rootCoordinates_apply (x : P.rootSpace) (j : Fin P.rank) :
    P.rootCoordinates x j = P.row j.val x.val := rfl

def projection : Module.End K V :=
  P.rootSpace.subtype.comp (P.rootCoordinates.symm.toLinearMap.comp (P.observations P.rank))

theorem projection_mem (x : V) : P.projection x ∈ P.rootSpace :=
  (P.rootCoordinates.symm (P.observations P.rank x)).property

theorem projection_readings (x : V) (j : Fin P.rank) :
    P.row j.val (P.projection x) = P.row j.val x := by
  exact congrFun (P.rootCoordinates.apply_symm_apply (P.observations P.rank x)) j

theorem projection_eq_self {x : V} (hx : x ∈ P.rootSpace) : P.projection x = x := by
  exact congrArg Subtype.val (P.rootCoordinates.symm_apply_apply (⟨x,hx⟩ : P.rootSpace))

theorem projection_idempotent (x : V) : P.projection (P.projection x) = P.projection x :=
  P.projection_eq_self (P.projection_mem x)

theorem projection_range : LinearMap.range P.projection = P.rootSpace := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    exact P.projection_mem x
  · intro x hx
    exact ⟨x,P.projection_eq_self hx⟩

def complement : Submodule K V := LinearMap.ker (P.observations P.rank)

omit [FiniteDimensional K P.rootSpace] in
theorem mem_complement (x : V) : x ∈ P.complement ↔ ∀ j < P.rank, P.row j x = 0 := by
  change (fun j : Fin P.rank => P.row j.val x) = 0 ↔ _
  constructor
  · intro h j hj
    exact congrFun h ⟨j,hj⟩
  · intro h
    funext j
    exact h j.val j.isLt

theorem projection_eq_zero_iff (x : V) : P.projection x = 0 ↔ x ∈ P.complement := by
  constructor
  · intro h
    apply (P.mem_complement x).mpr
    intro j hj
    have hh := P.projection_readings x ⟨j,hj⟩
    rwa [h,map_zero,eq_comm] at hh
  · intro h
    change (P.rootCoordinates.symm (P.observations P.rank x)).val = 0
    rw [show P.observations P.rank x = 0 from h,map_zero]
    rfl

theorem remainder_mem (x : V) : x-P.projection x ∈ P.complement := by
  apply (P.mem_complement _).mpr
  intro j hj
  rw [map_sub,P.projection_readings x ⟨j,hj⟩,sub_self]

theorem pencil_mem_complement {x : V} (hx : x ∈ P.complement) :
    P.pencil x ∈ P.complement := by
  apply (P.mem_complement _).mpr
  intro j hj
  cases j with
  | zero => exact P.moment_range x
  | succ j =>
      rw [P.row_succ_pencil,P.obstruction_order.1 j (by change j < P.rank-1; omega),mul_zero,sub_zero]
      exact (P.mem_complement x).mp hx j (by omega)

theorem root_complement_trivial {x : V} (hr : x ∈ P.rootSpace) (hc : x ∈ P.complement) : x = 0 := by
  have he := P.projection_eq_self hr
  rw [(P.projection_eq_zero_iff x).mpr hc] at he
  exact he.symm

theorem projection_pencil (x : V) : P.projection (P.pencil x) = P.pencil (P.projection x) := by
  have hx := P.pencil_mem_complement (P.remainder_mem x)
  rw [map_sub] at hx
  have he := (P.projection_eq_zero_iff _).mpr hx
  rw [map_sub,P.projection_eq_self (P.pencil_mem_root (P.projection_mem x))] at he
  exact sub_eq_zero.mp he

/-- One finite source correction inverts the pencil on the full unobserved complement. -/
def complementInverse : Module.End K V :=
  P.partialInverse - (P.row P.rank).smulRight
    ((P.moment (P.chain (P.rank-1)))⁻¹ • P.mode)

omit [FiniteDimensional K P.rootSpace] in
@[simp] theorem complementInverse_apply (x : V) :
    P.complementInverse x = P.partialInverse x -
      (P.row P.rank x/P.moment (P.chain (P.rank-1))) • P.mode := by
  simp only [complementInverse,LinearMap.sub_apply,LinearMap.smulRight_apply,smul_smul,div_eq_mul_inv]

omit [FiniteDimensional K P.rootSpace] in
theorem row_partialInverse (n : ℕ) (x : V) : P.row n (P.partialInverse x) = P.row (n+1) x := by
  simp only [row,LinearMap.comp_apply,pow_succ,Module.End.mul_apply]

omit [FiniteDimensional K P.rootSpace] in
theorem row_mode (n : ℕ) : P.row n P.mode = P.moment (P.chain n) := rfl

theorem complementInverse_mem {x : V} (hx : x ∈ P.complement) :
    P.complementInverse x ∈ P.complement := by
  apply (P.mem_complement _).mpr
  intro j hj
  rw [complementInverse_apply,map_sub,map_smul,smul_eq_mul,row_partialInverse,row_mode]
  rcases lt_or_eq_of_le (show j ≤ P.rank-1 by omega) with hlt | heq
  · rw [P.obstruction_order.1 j hlt,mul_zero,sub_zero]
    exact (P.mem_complement x).mp hx (j+1) (by omega)
  · have hsucc : j+1=P.rank := by omega
    rw [hsucc,heq,div_mul_cancel₀ _ P.obstruction_order.2,sub_self]

theorem pencil_complementInverse {x : V} (hx : x ∈ P.complement) :
    P.pencil (P.complementInverse x) = x := by
  rw [complementInverse_apply,map_sub,map_smul,P.mode_kernel,smul_zero,sub_zero,P.right,
    show P.moment x = 0 from (P.mem_complement x).mp hx 0 P.root_finrank_pos,
    zero_smul,sub_zero]

theorem complementInverse_pencil {x : V} (hx : x ∈ P.complement) :
    P.complementInverse (P.pencil x) = x := by
  apply sub_eq_zero.mp
  apply P.root_complement_trivial
  · apply (P.mem_rootSpace _).mpr
    refine ⟨1,?_⟩
    rw [pow_one,map_sub,P.pencil_complementInverse (P.pencil_mem_complement hx),sub_self]
  · exact P.complement.sub_mem (P.complementInverse_mem (P.pencil_mem_complement hx)) hx

theorem complementInverse_pow_mem (n : ℕ) {x : V} (hx : x ∈ P.complement) :
    (P.complementInverse^n) x ∈ P.complement := by
  induction n with
  | zero => simpa only [pow_zero,Module.End.one_apply] using hx
  | succ n ih =>
      rw [pow_succ',Module.End.mul_apply]
      exact P.complementInverse_mem ih

theorem pencil_pow_complementInverse_pow (n : ℕ) {x : V} (hx : x ∈ P.complement) :
    (P.pencil^n) ((P.complementInverse^n) x) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ P.pencil,pow_succ' P.complementInverse,Module.End.mul_apply,
        Module.End.mul_apply,P.pencil_complementInverse (P.complementInverse_pow_mem n hx)]
      exact ih

theorem pencil_pow_injective_on_complement (n : ℕ) {x y : V}
    (hx : x ∈ P.complement) (hy : y ∈ P.complement)
    (he : (P.pencil^n) x = (P.pencil^n) y) : x=y := by
  apply sub_eq_zero.mp
  apply P.root_complement_trivial
  · exact (P.mem_rootSpace _).mpr ⟨n,by rw [map_sub,he,sub_self]⟩
  · exact P.complement.sub_mem hx hy

/-- Every forcing has a canonical solution after its complete root component is removed. -/
theorem projected_power_equation (n : ℕ) (g : V) :
    (P.pencil^n) ((P.complementInverse^n) (g-P.projection g)) = g-P.projection g ∧
      (P.complementInverse^n) (g-P.projection g) ∈ P.complement ∧
      ∀ x ∈ P.complement, (P.pencil^n) x = g-P.projection g →
        x = (P.complementInverse^n) (g-P.projection g) := by
  have hm := P.complementInverse_pow_mem n (P.remainder_mem g)
  have he := P.pencil_pow_complementInverse_pow n (P.remainder_mem g)
  exact ⟨he,hm,fun x hx hh => P.pencil_pow_injective_on_complement n hx hm (hh.trans he.symm)⟩

end HTGeometry.OneChannelParametrix
