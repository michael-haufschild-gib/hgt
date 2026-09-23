import GaloisForLFunctions.RHTower.Sieve.DirichletCubeConvolution
import Mathlib.Algebra.Order.Chebyshev

/-!
# The coefficients of the cube

Cauchy–Schwarz on each fibre bounds the `ℓ²` norm of the threefold convolution by the cube of the
`ℓ²` norm of the original coefficients, times the largest fibre size:

    ∑_{j ≤ N³} |b_j|² ≤ D · (∑_{n ≤ N} |a_n|²)³ ,   D = max_j #{(n,m,k) : nmk = j} .

The fibre size is the threefold divisor count restricted to `[1,N]³`; the crude universal bound
`D ≤ N²` holds because the first two factors determine the third.
-/

namespace RHTower.Sieve

open Finset

/-- The fibre of `cubeIdx` over an index. -/
noncomputable def cubeFibre (N : ℕ) (j : Fin (N ^ (3 : ℕ))) : Finset (Fin N × Fin N × Fin N) :=
  (Finset.univ : Finset (Fin N × Fin N × Fin N)).filter (fun p => cubeIdx p = j)

/-- The first two coordinates determine a point of a fibre. -/
theorem cubeFibre_card_le_sq (N : ℕ) (j : Fin (N ^ (3 : ℕ))) :
    (cubeFibre N j).card ≤ N ^ (2 : ℕ) := by
  classical
  have hinj : Set.InjOn (fun p : Fin N × Fin N × Fin N => (p.1, p.2.1)) (cubeFibre N j) := by
    intro p hp q hq hpq
    simp only [cubeFibre, Finset.coe_filter, Set.mem_setOf_eq] at hp hq
    have hp1 : ((p.1 : ℕ) + 1) * ((p.2.1 : ℕ) + 1) * ((p.2.2 : ℕ) + 1) = (j : ℕ) + 1 := by
      rw [← cubeIdx_val_add_one p, hp.2]
    have hq1 : ((q.1 : ℕ) + 1) * ((q.2.1 : ℕ) + 1) * ((q.2.2 : ℕ) + 1) = (j : ℕ) + 1 := by
      rw [← cubeIdx_val_add_one q, hq.2]
    have hpq' : (p.1, p.2.1) = (q.1, q.2.1) := hpq
    have h1 : p.1 = q.1 := congrArg (fun x : Fin N × Fin N => x.1) hpq'
    have h2 : p.2.1 = q.2.1 := congrArg (fun x : Fin N × Fin N => x.2) hpq'
    have hpos : 0 < ((p.1 : ℕ) + 1) * ((p.2.1 : ℕ) + 1) := by positivity
    have heq : ((p.1 : ℕ) + 1) * ((p.2.1 : ℕ) + 1) * ((p.2.2 : ℕ) + 1)
        = ((p.1 : ℕ) + 1) * ((p.2.1 : ℕ) + 1) * ((q.2.2 : ℕ) + 1) := by
      rw [hp1, h1, h2, hq1]
    have h3 : (p.2.2 : ℕ) + 1 = (q.2.2 : ℕ) + 1 :=
      Nat.eq_of_mul_eq_mul_left hpos heq
    have h3' : p.2.2 = q.2.2 := Fin.ext (by omega)
    exact Prod.ext h1 (Prod.ext h2 h3')
  have hcard := Finset.card_le_card_of_injOn
    (f := fun p : Fin N × Fin N × Fin N => (p.1, p.2.1))
    (s := cubeFibre N j) (t := (Finset.univ : Finset (Fin N × Fin N)))
    (fun p _ => Finset.mem_univ _) hinj
  simpa [Fintype.card_prod, sq] using hcard

/-- **The `ℓ²` norm of the threefold convolution.** -/
theorem sum_normSq_convCube_le (N : ℕ) (a : Fin N → ℂ) {D : ℝ}
    (hD : ∀ j : Fin (N ^ (3 : ℕ)), ((cubeFibre N j).card : ℝ) ≤ D) :
    ∑ j : Fin (N ^ (3 : ℕ)), ‖convCube N a j‖ ^ (2 : ℕ)
      ≤ D * (∑ n : Fin N, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
  classical
  set g : Fin N × Fin N × Fin N → ℝ := fun p => ‖a p.1 * a p.2.1 * a p.2.2‖ with hg
  have hfibre : ∀ j : Fin (N ^ (3 : ℕ)),
      ‖convCube N a j‖ ^ (2 : ℕ) ≤ D * ∑ p ∈ cubeFibre N j, g p ^ (2 : ℕ) := by
    intro j
    have hnorm : ‖convCube N a j‖ ≤ ∑ p ∈ cubeFibre N j, g p := by
      rw [convCube]
      exact norm_sum_le _ _
    have hnn : (0 : ℝ) ≤ ∑ p ∈ cubeFibre N j, g p :=
      Finset.sum_nonneg fun p _ => norm_nonneg _
    have hsq : ‖convCube N a j‖ ^ (2 : ℕ) ≤ (∑ p ∈ cubeFibre N j, g p) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hcs : (∑ p ∈ cubeFibre N j, g p) ^ (2 : ℕ)
        ≤ ((cubeFibre N j).card : ℝ) * ∑ p ∈ cubeFibre N j, g p ^ (2 : ℕ) :=
      sq_sum_le_card_mul_sum_sq
    have hsum0 : (0 : ℝ) ≤ ∑ p ∈ cubeFibre N j, g p ^ (2 : ℕ) :=
      Finset.sum_nonneg fun p _ => sq_nonneg _
    have hmul : ((cubeFibre N j).card : ℝ) * ∑ p ∈ cubeFibre N j, g p ^ (2 : ℕ)
        ≤ D * ∑ p ∈ cubeFibre N j, g p ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right (hD j) hsum0
    linarith
  have hsum : ∑ j : Fin (N ^ (3 : ℕ)), ‖convCube N a j‖ ^ (2 : ℕ)
      ≤ ∑ j : Fin (N ^ (3 : ℕ)), D * ∑ p ∈ cubeFibre N j, g p ^ (2 : ℕ) :=
    Finset.sum_le_sum fun j _ => hfibre j
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin N × Fin N × Fin N)))
    (t := (Finset.univ : Finset (Fin (N ^ (3 : ℕ))))) (g := fun p => cubeIdx p)
    (f := fun p : Fin N × Fin N × Fin N => g p ^ (2 : ℕ))
    (fun p _ => Finset.mem_univ _)
  have hcollect : ∑ j : Fin (N ^ (3 : ℕ)), D * ∑ p ∈ cubeFibre N j, g p ^ (2 : ℕ)
      = D * ∑ p : Fin N × Fin N × Fin N, g p ^ (2 : ℕ) := by
    simp only [cubeFibre]
    rw [← Finset.mul_sum, ← hfib]
  have hprod : ∑ p : Fin N × Fin N × Fin N, g p ^ (2 : ℕ)
      = (∑ n : Fin N, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
    have hpt : ∀ p : Fin N × Fin N × Fin N,
        g p ^ (2 : ℕ) = ‖a p.1‖ ^ (2 : ℕ) * (‖a p.2.1‖ ^ (2 : ℕ) * ‖a p.2.2‖ ^ (2 : ℕ)) := by
      intro p
      rw [hg]
      simp only [norm_mul]
      ring
    simp only [hpt, Fintype.sum_prod_type]
    rw [pow_three]
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    refine Finset.sum_congr rfl fun m _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hcollect, hprod] at hsum
  exact hsum

end RHTower.Sieve
