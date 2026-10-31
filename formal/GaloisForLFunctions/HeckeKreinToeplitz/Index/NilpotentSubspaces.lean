import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Abel

/-!
# Nilpotent operators with finite-dimensional kernel

Projection onto the kernel, applied along a finite nilpotent orbit, detects every
vector and bounds dimension by the nilpotence exponent times the kernel dimension.
In characteristic zero, a periodic vector in a unipotent orbit is fixed.
-/

open Module
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz

/-- A nilpotent operator with finite-dimensional kernel acts on a finite-dimensional space. -/
theorem finite_of_nilpotent_finite_kernel {K V : Type*} [Field K]
    [AddCommMonoid V] [Module K V] (N : End K V) {n : ℕ} (hn : N ^ n = 0)
    [Module.Finite K (LinearMap.ker N)] :
    Module.Finite K V ∧ Module.finrank K V ≤ n * Module.finrank K (LinearMap.ker N) := by
  classical
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  obtain ⟨Q, hQ⟩ := (LinearMap.ker N).exists_isCompl
  let P := (LinearMap.ker N).projectionOnto Q hQ
  let L : V →ₗ[K] (Fin n → LinearMap.ker N) :=
    LinearMap.pi (fun j => P.comp (N ^ (j : ℕ)))
  have hzero (x : V) (hx : L x = 0) : x = 0 := by
    have hstep (j : ℕ) (hj : j < n) (he : (N ^ (j + 1)) x = 0) : (N ^ j) x = 0 := by
      have hmem : (N ^ j) x ∈ LinearMap.ker N := by
        change N ((N ^ j) x) = 0
        change (N * N ^ j) x = 0
        rwa [← pow_succ']
      have hp : P ((N ^ j) x) = 0 := congrFun hx ⟨j, hj⟩
      have hp' := Submodule.projectionOnto_apply_of_mem_left hQ hmem
      change P ((N ^ j) x) = ⟨(N ^ j) x, hmem⟩ at hp'
      exact congrArg Subtype.val (hp'.symm.trans hp)
    have hdown (d : ℕ) (hd : d ≤ n) : (N ^ (n - d)) x = 0 := by
      induction d with
      | zero => simp only [Nat.sub_zero, hn, LinearMap.zero_apply]
      | succ d ih =>
          have hd' : d ≤ n := by omega
          have hprev := ih hd'
          have he : n - d = (n - (d + 1)) + 1 := by omega
          rw [he] at hprev
          exact hstep (n - (d + 1)) (by omega) hprev
    simpa only [Nat.sub_self, pow_zero, Module.End.one_apply] using hdown n le_rfl
  have hinj : Function.Injective L := by
    intro x y hxy
    have hz : L (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hzero (x - y) hz)
  letI : Module.Finite K V := Module.Finite.of_injective L hinj
  refine ⟨inferInstance, ?_⟩
  simpa only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using
    LinearMap.finrank_le_finrank_of_injective hinj

/-- A periodic vector in a unipotent orbit is fixed in characteristic zero. -/
theorem fixed_of_periodic_unipotent {K V : Type*} [Field K] [CharZero K]
    [AddCommMonoid V] [Module K V] (T : End K V) (x : V) {n m : ℕ}
    (hm : m ≠ 0) (hperiod : (T ^ m) x = x)
    (hnil : ((T + (-1 : K) • 1) ^ n) x = 0) : T x = x := by
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  change ((T - 1) ^ n) x = 0 at hnil
  induction n generalizing x with
  | zero =>
      have hx : x = 0 := by simpa only [pow_zero, Module.End.one_apply] using hnil
      rw [hx, map_zero]
  | succ n ih =>
      let N := T - 1
      have hcomm (j : ℕ) : T ^ j * N = N * T ^ j := by
        dsimp only [N]
        rw [mul_sub, sub_mul, mul_one, one_mul, ← pow_succ, ← pow_succ']
      have hnil' : (N ^ n) (N x) = 0 := by
        change (N ^ n * N) x = 0
        rw [← pow_succ]
        exact hnil
      have hperiod' : (T ^ m) (N x) = N x := by
        change (T ^ m * N) x = N x
        rw [hcomm, Module.End.mul_apply, hperiod]
      have hfix : T (N x) = N x := ih (N x) hperiod' hnil'
      have hx : T x = x + N x := by
        simp only [N, LinearMap.sub_apply, Module.End.one_apply]
        abel
      have hg (j : ℕ) : (T ^ j) x = x + (j : K) • N x := by
        induction j with
        | zero =>
            simp only [pow_zero, Module.End.one_apply, Nat.cast_zero, zero_smul, add_zero]
        | succ j hj =>
            rw [pow_succ', Module.End.mul_apply, hj, map_add, map_smul, hfix, hx,
              Nat.cast_add, Nat.cast_one, add_smul, one_smul]
            abel
      have hmul : (m : K) • N x = 0 := by
        apply add_left_cancel (a := x)
        simpa only [add_zero] using (hg m).symm.trans hperiod
      have hNx : N x = 0 := (smul_eq_zero.mp hmul).resolve_left (by exact_mod_cast hm)
      simpa only [hNx, add_zero] using hx

#print axioms finite_of_nilpotent_finite_kernel
#print axioms fixed_of_periodic_unipotent

end GaloisForLFunctions.HeckeKreinToeplitz
