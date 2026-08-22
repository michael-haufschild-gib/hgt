import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Linear independence of a square family survives a field extension

A family of `n` vectors in `Kⁿ` is linearly independent exactly when its matrix is nonsingular, and
a determinant is preserved by a ring homomorphism.  So a *square* independent family stays
independent after any field embedding of the coefficients.  This is the base change used to move a
cyclicity statement about a rational matrix to the same statement over `ℂ`.

## Main results

* `linearIndependent_map_algebraMap_square` — a square independent family stays independent.
* `linearIndependent_map_algebraMap_of_equiv` — the same for a family indexed by an equivalent type.
* `linearIndependent_krylov_map` — **the Krylov family of a matrix stays independent over any field
  extension.**
-/

open Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

namespace BaseChange

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A square linearly independent family stays independent over a field extension.** -/
theorem linearIndependent_map_algebraMap_square {x : ι → (ι → K)} (h : LinearIndependent K x) :
    LinearIndependent L (fun k => fun i => algebraMap K L (x k i)) := by
  classical
  set A : Matrix ι ι K := Matrix.of fun i r => x r i with hA
  have hmulVec : ∀ w : ι → K, ∀ i, (A *ᵥ w) i = (∑ k, w k • x k) i := by
    intro w i
    show ∑ r, A i r * w r = (∑ k, w k • x k) i
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun r _ => by
      rw [Pi.smul_apply, smul_eq_mul]
      show x r i * w r = w r * x r i
      ring
  have hAdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hcomb : ∑ k, w k • x k = 0 := by
      funext i
      rw [← hmulVec w i, hw]
    exact hw0 (funext fun k => Fintype.linearIndependent_iff.mp h w hcomb k)
  set B : Matrix ι ι L := A.map (algebraMap K L) with hB
  have hBdet : B.det ≠ 0 := by
    rw [hB, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact fun h0 => hAdet ((map_eq_zero_iff _ (algebraMap K L).injective).mp h0)
  have hmulVecB : ∀ c : ι → L, ∀ i,
      (B *ᵥ c) i = (∑ k, c k • fun j => algebraMap K L (x k j)) i := by
    intro c i
    show ∑ r, B i r * c r = (∑ k, c k • fun j => algebraMap K L (x k j)) i
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun r _ => by
      rw [Pi.smul_apply, smul_eq_mul]
      show algebraMap K L (x r i) * c r = c r * algebraMap K L (x r i)
      ring
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  obtain ⟨k₀, hk₀⟩ := hne
  refine hBdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨c, ?_, ?_⟩)
  · intro h0
    exact hk₀ (congrFun h0 k₀)
  · funext i
    rw [hmulVecB c i, hc]

/-- The same statement for a family indexed by a type equivalent to the coordinate type. -/
theorem linearIndependent_map_algebraMap_of_equiv {m : Type*} (eqv : m ≃ ι)
    {x : m → (ι → K)} (h : LinearIndependent K x) :
    LinearIndependent L (fun k => fun i => algebraMap K L (x k i)) := by
  have h' : LinearIndependent K (fun r : ι => x (eqv.symm r)) :=
    h.comp eqv.symm eqv.symm.injective
  have h'' := (linearIndependent_map_algebraMap_square (L := L) h').comp eqv eqv.injective
  have heq : ((fun (r : ι) (i : ι) => algebraMap K L (x (eqv.symm r) i)) ∘ eqv)
      = fun (k : m) (i : ι) => algebraMap K L (x k i) := by
    funext k i
    simp
  rwa [heq] at h''

/-- **The Krylov family of a matrix stays independent over a field extension.** -/
theorem linearIndependent_krylov_map {A : Matrix ι ι K} {v : ι → K}
    (h : LinearIndependent K (fun k : Fin (Fintype.card ι) => A ^ (k : ℕ) *ᵥ v)) :
    LinearIndependent L (fun k : Fin (Fintype.card ι) =>
      (A.map (algebraMap K L)) ^ (k : ℕ) *ᵥ fun i => algebraMap K L (v i)) := by
  classical
  have hbase := linearIndependent_map_algebraMap_of_equiv (L := L)
    (Fintype.equivFin ι).symm h
  have hpow : ∀ n : ℕ, (A.map (algebraMap K L)) ^ n = (A ^ n).map (algebraMap K L) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_succ, ih, ← Matrix.map_mul]
  have heq : (fun (k : Fin (Fintype.card ι)) (i : ι) => algebraMap K L ((A ^ (k : ℕ) *ᵥ v) i))
      = fun (k : Fin (Fintype.card ι)) =>
        (A.map (algebraMap K L)) ^ (k : ℕ) *ᵥ fun i => algebraMap K L (v i) := by
    funext k i
    rw [hpow]
    show algebraMap K L (∑ j, (A ^ (k : ℕ)) i j * v j)
        = ∑ j, ((A ^ (k : ℕ)).map (algebraMap K L)) i j * algebraMap K L (v j)
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => map_mul _ _ _
  rwa [heq] at hbase

end BaseChange

end GaloisForLFunctions.HTGeometry
