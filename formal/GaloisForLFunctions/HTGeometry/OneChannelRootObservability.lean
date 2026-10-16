import GaloisForLFunctions.HTGeometry.LoweringChainIndependence
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Full root multiplicity from one actual defect channel

A trace-normalized parametrix produces a canonical iterated chain and
iterated source readings. The first nonzero reading of that chain occurs
exactly one step before the dimension of the whole generalized kernel.
Those readings separate every generalized mode, including all nilpotent
directions. No spectral contour or simple-root assumption is used.
-/

noncomputable section
open Module Set

namespace HTGeometry

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A two-sided parametrix with one source defect and one normalized kernel trace. -/
structure OneChannelParametrix (K V : Type*) [Field K] [AddCommGroup V] [Module K V] where
  pencil : Module.End K V
  partialInverse : Module.End K V
  source : V
  mode : V
  moment : V →ₗ[K] K
  trace : V →ₗ[K] K
  right : ∀ x, pencil (partialInverse x) = x - moment x • source
  left : ∀ x, partialInverse (pencil x) = x - trace x • mode
  mode_kernel : pencil mode = 0
  moment_range : ∀ x, moment (pencil x) = 0
  trace_mode : trace mode = 1

namespace OneChannelParametrix
variable (P : OneChannelParametrix K V)

def rootSpace : Submodule K V := P.pencil.maxGenEigenspace 0

theorem mem_rootSpace (x : V) : x ∈ P.rootSpace ↔ ∃ n : ℕ, (P.pencil ^ n) x = 0 := by
  simp only [rootSpace, Module.End.mem_maxGenEigenspace, zero_smul, sub_zero]

def chain (n : ℕ) : V := (P.partialInverse ^ n) P.mode

def row (n : ℕ) : V →ₗ[K] K := P.moment.comp (P.partialInverse ^ n)

@[simp] theorem chain_zero : P.chain 0 = P.mode := rfl
@[simp] theorem row_zero (x : V) : P.row 0 x = P.moment x := rfl

theorem chain_succ (n : ℕ) : P.chain (n+1) = P.partialInverse (P.chain n) := by
  simp only [chain, pow_succ', Module.End.mul_apply]

theorem row_succ_pencil (n : ℕ) (x : V) :
    P.row (n+1) (P.pencil x) = P.row n x - P.trace x * P.moment (P.chain n) := by
  simp only [row, LinearMap.comp_apply, pow_succ, Module.End.mul_apply, P.left,
    map_sub, map_smul, smul_eq_mul, chain]

theorem pencil_chain_succ (n : ℕ) :
    P.pencil (P.chain (n+1)) = P.chain n - P.moment (P.chain n) • P.source := by
  rw [chain_succ, P.right]

theorem mode_ne_zero : P.mode ≠ 0 := by
  intro h
  have ht := P.trace_mode
  rw [h, map_zero] at ht
  exact zero_ne_one ht

theorem chain_pow (n : ℕ) (h : ∀ j < n, P.moment (P.chain j) = 0) :
    (P.pencil ^ (n+1)) (P.chain n) = 0 := by
  induction n with
  | zero => simpa only [zero_add, pow_one, chain_zero] using P.mode_kernel
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, pencil_chain_succ, h n (Nat.lt_succ_self n),
        zero_smul, sub_zero]
      exact ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self n)))

theorem chain_independent (n : ℕ) (h : ∀ j < n, P.moment (P.chain j) = 0) :
    LinearIndependent K (fun j : Fin (n+1) => P.chain j.val) := by
  induction n with
  | zero =>
      change LinearIndependent K (fun j : Fin 1 => P.chain j.val)
      apply linearIndependent_unique_iff.mpr
      exact P.mode_ne_zero
  | succ n ih =>
      have hind := ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self n)))
      rw [Fintype.linearIndependent_iff] at hind ⊢
      intro c hc j
      have hc' := hc
      rw [Fin.sum_univ_succ] at hc'
      have hN := congrArg P.pencil hc'
      simp only [map_add, map_sum, map_smul, map_zero, Fin.val_zero,
        chain_zero, P.mode_kernel, smul_zero, zero_add, Fin.val_succ,
        pencil_chain_succ] at hN
      have hsmall (i : Fin (n+1)) : P.moment (P.chain i.val) = 0 := h i.val i.isLt
      simp only [hsmall, zero_smul, sub_zero] at hN
      have hcs (i : Fin (n+1)) : c i.succ = 0 := hind (fun i => c i.succ) hN i
      have hc0 : c 0 = 0 := by
        rw [Fin.sum_univ_succ] at hc
        simp only [hcs, zero_smul, Finset.sum_const_zero, add_zero, Fin.val_zero, chain_zero] at hc
        exact (smul_eq_zero.mp hc).resolve_right P.mode_ne_zero
      exact Fin.cases hc0 hcs j

theorem pencil_mem_root {x : V} (hx : x ∈ P.rootSpace) : P.pencil x ∈ P.rootSpace := by
  obtain ⟨n, hn⟩ := (P.mem_rootSpace x).mp hx
  apply (P.mem_rootSpace _).mpr
  refine ⟨n, ?_⟩
  rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply, hn, map_zero]

def observations (n : ℕ) : V →ₗ[K] (Fin n → K) := LinearMap.pi (fun j => P.row j.val)

def rootObservations (n : ℕ) : P.rootSpace →ₗ[K] (Fin n → K) :=
  (P.observations n).comp P.rootSpace.subtype

theorem zero_of_observations_of_pow (n : ℕ)
    (hprev : ∀ j < n, P.moment (P.chain j) = 0)
    (hlast : P.moment (P.chain n) ≠ 0) (k : ℕ) (x : V)
    (hx : (P.pencil ^ k) x = 0) (ho : ∀ j ≤ n, P.row j x = 0) : x = 0 := by
  induction k generalizing x with
  | zero => simpa only [pow_zero, Module.End.one_apply] using hx
  | succ k ih =>
      have hNx : P.pencil x = 0 := by
        apply ih (P.pencil x)
        · simpa only [pow_succ, Module.End.mul_apply] using hx
        · intro j hj
          cases j with
          | zero => exact P.moment_range x
          | succ j =>
              rw [row_succ_pencil, hprev j (by omega), mul_zero, sub_zero]
              exact ho j (by omega)
      have he : x = P.trace x • P.mode := by
        have hh := P.left x
        rw [hNx, map_zero] at hh
        exact sub_eq_zero.mp hh.symm
      have ht : P.trace x = 0 := by
        have hh := ho n le_rfl
        rw [he, map_smul, smul_eq_mul] at hh
        exact (mul_eq_zero.mp hh).resolve_right hlast
      rw [he, ht, zero_smul]

theorem rootObservations_injective (n : ℕ)
    (hprev : ∀ j < n, P.moment (P.chain j) = 0)
    (hlast : P.moment (P.chain n) ≠ 0) :
    Function.Injective (P.rootObservations (n+1)) := by
  intro x y hxy
  have hx := (P.mem_rootSpace (x.val-y.val)).mp (P.rootSpace.sub_mem x.property y.property)
  obtain ⟨k,hk⟩ := hx
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply P.zero_of_observations_of_pow n hprev hlast k (x.val-y.val) hk
  intro j hj
  have he := congrFun hxy ⟨j,by omega⟩
  change P.row j x.val = P.row j y.val at he
  rw [map_sub, he, sub_self]

variable [FiniteDimensional K P.rootSpace]

theorem exists_first_obstruction : ∃ n < Module.finrank K P.rootSpace,
    P.moment (P.chain n) ≠ 0 := by
  by_contra h
  push Not at h
  let m := Module.finrank K P.rootSpace
  have hc : ∀ j < m, P.moment (P.chain j) = 0 := h
  have hr (j : Fin (m+1)) : P.chain j.val ∈ P.rootSpace := by
    exact (P.mem_rootSpace _).mpr ⟨j.val+1,
      P.chain_pow j.val (fun i hi => hc i (by omega))⟩
  have hi : LinearIndependent K (fun j : Fin (m+1) => (⟨P.chain j.val,hr j⟩ : P.rootSpace)) := by
    apply LinearIndependent.of_comp P.rootSpace.subtype
    exact P.chain_independent m hc
  have hd := hi.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hd
  omega

/-- Iterating the actual source defect first detects precisely the full root multiplicity. -/
theorem obstruction_order :
    (∀ j < Module.finrank K P.rootSpace - 1, P.moment (P.chain j) = 0) ∧
      P.moment (P.chain (Module.finrank K P.rootSpace - 1)) ≠ 0 := by
  classical
  have hex : ∃ n, P.moment (P.chain n) ≠ 0 := by
    obtain ⟨n,_,hn⟩ := P.exists_first_obstruction
    exact ⟨n,hn⟩
  let n := Nat.find hex
  have hn : P.moment (P.chain n) ≠ 0 := Nat.find_spec hex
  have hp : ∀ j < n, P.moment (P.chain j) = 0 := by
    intro j hj
    exact not_ne_iff.mp (Nat.find_min hex hj)
  have hle := LinearMap.finrank_le_finrank_of_injective (P.rootObservations_injective n hp hn)
  have hdim : Module.finrank K (Fin (n+1) → K) = n+1 := by simp
  rw [hdim] at hle
  obtain ⟨r,hr,hrn⟩ := P.exists_first_obstruction
  have hnr : n ≤ r := Nat.find_min' hex hrn
  have heq : n = Module.finrank K P.rootSpace - 1 := by omega
  simpa only [heq] using And.intro hp hn

theorem root_finrank_pos : 0 < Module.finrank K P.rootSpace := by
  obtain ⟨n,hn,_⟩ := P.exists_first_obstruction
  omega

end OneChannelParametrix
end HTGeometry
