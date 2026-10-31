import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnInertia
import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnProjections

/-!
# Positivity from dilation of periodic vectors

A group relation that contracts a finite translation period replicates every zero-mean vector
into orthogonal isometric copies. Finite negative index therefore forces its norm to be nonnegative.
-/

open Complex Finset Module
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [Group G]

/-- A periodic zero-mean orbit is nonnegative if a group element contracts its period.
Otherwise its dilation iterates form arbitrarily large orthogonal negative families. -/
theorem nonneg_of_periodic_dilation {k : G → ℂ} (hk : IsHermKernel k)
    {r : ℕ} (hi : negIndex k ≤ r) (t a : G) {m : ℕ} (hm : m ≠ 0)
    (ha : t * a = a * t ^ m) (x : kernelColumnSpan k)
    (hperiod : ((kernelColumnRepresentation k t) ^ m) x = x)
    (hmean : ∑ j ∈ range m, ((kernelColumnRepresentation k t) ^ j) x = 0) :
    0 ≤ (kernelColumnPairing k x x).re := by
  classical
  let T := kernelColumnRepresentation k t
  let U := kernelColumnRepresentation k a
  have hTU : T * U = U * T ^ m := by
    change kernelColumnRepresentation k t * kernelColumnRepresentation k a = _
    rw [← map_mul, ha, map_mul, map_pow]
  have hfixed_pow {y : kernelColumnSpan k} (hy : T y = y) (j : ℕ) : (T ^ j) y = y := by
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ, Module.End.mul_apply, hy, ih]
  have hfixed (j : ℕ) : T ((U ^ (j + 1)) x) = (U ^ (j + 1)) x := by
    induction j with
    | zero =>
      change (T * U) x = U x
      rw [hTU, Module.End.mul_apply, hperiod]
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply]
      change (T * U) ((U ^ (j + 1)) x) = U ((U ^ (j + 1)) x)
      rw [hTU, Module.End.mul_apply, hfixed_pow ih m]
  have horth (y : kernelColumnSpan k) (hy : T y = y) : kernelColumnPairing k x y = 0 := by
    have he : (m : ℂ) * kernelColumnPairing k x y = 0 := by
      rw [← kernelColumnPairing_orbit_sum_fixed hk t x y hy m, hmean]
      exact LinearMap.congr_fun (map_zero (kernelColumnSesquilinear k hk)) y
    exact (mul_eq_zero.mp he).resolve_left (Nat.cast_ne_zero.mpr hm)
  have hpair_lt (i j : ℕ) (hij : i < j) :
      kernelColumnPairing k ((U ^ i) x) ((U ^ j) x) = 0 := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, j = i + (n + 1) := by
      exact ⟨j - i - 1, by omega⟩
    rw [hn, pow_add, Module.End.mul_apply]
    have he := kernelColumnPairing_invariant hk (a ^ i) x ((U ^ (n + 1)) x)
    rw [map_pow] at he
    change kernelColumnPairing k ((U ^ i) x) ((U ^ i) ((U ^ (n + 1)) x)) = _ at he
    rw [he]
    exact horth _ (hfixed n)
  by_contra hnonneg
  have hneg := lt_of_not_ge hnonneg
  have hbound := card_le_index_of_orthogonal_negative_columns hk hi
    (fun i : Fin (r + 1) => (U ^ i.val) x)
    (fun i => by
      have he := kernelColumnPairing_invariant hk (a ^ i.val) x x
      rw [map_pow] at he
      change kernelColumnPairing k ((U ^ i.val) x) ((U ^ i.val) x) = _ at he
      rw [he]
      exact hneg)
    (fun i j hij => by
      have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
      rcases lt_or_gt_of_ne hval with hlt | hgt
      · exact hpair_lt i.val j.val hlt
      · rw [kernelColumnPairing_conj_symm hk, hpair_lt j.val i.val hgt, map_zero])
  simp only [Fintype.card_fin] at hbound
  omega

/-- A difference along a finite orbit has zero orbit average. -/
theorem sum_periodic_difference {K V : Type*} [Field K] [AddCommMonoid V] [Module K V]
    (T : End K V) {m : ℕ} {y : V} (hy : (T ^ m) y = y) :
    ∑ j ∈ range m, (T ^ j) ((T + (-1 : K) • 1) y) = 0 := by
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  change ∑ j ∈ range m, (T ^ j) ((T - 1) y) = 0
  rw [← LinearMap.sum_apply]
  change (((∑ j ∈ range m, T ^ j) * (T - 1)) y) = 0
  rw [geom_sum_mul, LinearMap.sub_apply, Module.End.one_apply, hy, sub_self]

#print axioms nonneg_of_periodic_dilation
#print axioms sum_periodic_difference
end GaloisForLFunctions.HeckeKreinToeplitz
