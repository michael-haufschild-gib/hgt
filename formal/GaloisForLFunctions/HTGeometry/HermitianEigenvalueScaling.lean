/-
# Scaling a Hermitian matrix scales its spectrum

The eigenvalue function of a Hermitian matrix is a choice, so scaling the matrix need not scale it
pointwise; but the *multiset* of eigenvalues does scale, because every power trace scales, and a
multiset of reals is determined by its power sums.  Simplicity of the spectrum is therefore a
scale-invariant property: it is the nodup-ness of that multiset, and multiplying by a nonzero
constant is injective.

Main results:
* `injective_iff_nodup_map` — injectivity of a function on a finite type is nodup-ness of its value
  multiset.
* `multiset_map_eigenvalues_smul` — **the eigenvalue multiset of `tA` is `t` times that of `A`**.
* `injective_eigenvalues_smul_iff` — **a simple spectrum is a scale-invariant property**.
-/
import GaloisForLFunctions.HTGeometry.RankEnergyPowerSum
import GaloisForLFunctions.HTGeometry.MultisetNewtonSolve

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem injective_iff_nodup_map (f : ι → ℝ) :
    Function.Injective f ↔ (Multiset.map f (Finset.univ : Finset ι).val).Nodup := by
  rw [Multiset.nodup_map_iff_inj_on (Finset.univ (α := ι)).nodup]
  constructor
  · intro h x _ y _ hxy
    exact h hxy
  · intro h x y hxy
    exact h x (Finset.mem_univ x) y (Finset.mem_univ y) hxy

/-- **The eigenvalue multiset of a scaled Hermitian matrix is the scaled multiset.** -/
theorem multiset_map_eigenvalues_smul {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (t : ℝ)
    (hA' : (((t : ℂ)) • A).IsHermitian) :
    Multiset.map hA'.eigenvalues (Finset.univ : Finset ι).val
      = Multiset.map (fun i => t * hA.eigenvalues i) (Finset.univ : Finset ι).val := by
  refine multiset_eq_of_powerSum_eq fun p => ?_
  rw [Multiset.map_map, Multiset.map_map]
  have hcomplex : (((((t : ℂ)) • A) ^ p).trace) = ((t : ℂ)) ^ p * ((A ^ p).trace) := by
    rw [smul_pow, Matrix.trace_smul, smul_eq_mul]
  have h1 := trace_pow_eq_sum_eigenvalues_pow hA' p
  have h2 := trace_pow_eq_sum_eigenvalues_pow hA p
  have hkey : (∑ i, ((hA'.eigenvalues i : ℂ)) ^ p)
      = ((t : ℂ)) ^ p * ∑ i, ((hA.eigenvalues i : ℂ)) ^ p := by
    rw [← h1, ← h2, hcomplex]
  have hreal : (∑ i, (hA'.eigenvalues i) ^ p) = ∑ i, (t * hA.eigenvalues i) ^ p := by
    have hexp : (∑ i, (t * hA.eigenvalues i) ^ p) = t ^ p * ∑ i, (hA.eigenvalues i) ^ p := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_pow]
    rw [hexp]
    exact_mod_cast hkey
  exact hreal

/-- **A simple spectrum is a scale-invariant property.** -/
theorem injective_eigenvalues_smul_iff {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {t : ℝ}
    (ht : t ≠ 0) (hA' : (((t : ℂ)) • A).IsHermitian) :
    Function.Injective hA'.eigenvalues ↔ Function.Injective hA.eigenvalues := by
  rw [injective_iff_nodup_map, injective_iff_nodup_map, multiset_map_eigenvalues_smul hA t hA']
  have hmap : Multiset.map (fun i => t * hA.eigenvalues i) (Finset.univ : Finset ι).val
      = Multiset.map (fun x : ℝ => t * x)
        (Multiset.map hA.eigenvalues (Finset.univ : Finset ι).val) := by
    rw [Multiset.map_map]
    rfl
  rw [hmap]
  constructor
  · exact fun h => h.of_map _
  · exact fun h => h.map (mul_right_injective₀ ht)

end

end GaloisForLFunctions.HTGeometry
