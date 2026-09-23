import GaloisForLFunctions.RHTower.Sieve.DirichletPoly

/-!
# The cube of a Dirichlet polynomial

`F(t) = ∑_{n ≤ N} a_n n^{it}` satisfies `F(t)³ = ∑_{j ≤ N³} b_j j^{it}` with `b` the threefold
Dirichlet convolution of `a`, because the phases multiply: `n^{it} m^{it} k^{it} = (nmk)^{it}`.

This is the device behind every sixth-moment large-values estimate: applying a mean-value theorem
to the cube converts a bound with `V²` into one with `V⁶`, at the cost of replacing the length `N`
by `N³` and the coefficient vector by its convolution square.
-/

namespace RHTower.Sieve

open Finset

/-- The index of a triple in `Fin (N³)`: the product of the three integers, shifted down by one. -/
def cubeIdx {N : ℕ} (p : Fin N × Fin N × Fin N) : Fin (N ^ (3 : ℕ)) :=
  ⟨((p.1 : ℕ) + 1) * ((p.2.1 : ℕ) + 1) * ((p.2.2 : ℕ) + 1) - 1, by
    have h1 : (p.1 : ℕ) + 1 ≤ N := p.1.isLt
    have h2 : (p.2.1 : ℕ) + 1 ≤ N := p.2.1.isLt
    have h3 : (p.2.2 : ℕ) + 1 ≤ N := p.2.2.isLt
    have hle : ((p.1 : ℕ) + 1) * ((p.2.1 : ℕ) + 1) * ((p.2.2 : ℕ) + 1) ≤ N * N * N :=
      Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    have hpos : 0 < ((p.1 : ℕ) + 1) * ((p.2.1 : ℕ) + 1) * ((p.2.2 : ℕ) + 1) := by positivity
    have hcube : N * N * N = N ^ (3 : ℕ) := by ring
    omega⟩

/-- The defining property of `cubeIdx`: it names the product. -/
theorem cubeIdx_val_add_one {N : ℕ} (p : Fin N × Fin N × Fin N) :
    ((cubeIdx p : ℕ) + 1)
      = ((p.1 : ℕ) + 1) * ((p.2.1 : ℕ) + 1) * ((p.2.2 : ℕ) + 1) := by
  have hpos : 0 < ((p.1 : ℕ) + 1) * ((p.2.1 : ℕ) + 1) * ((p.2.2 : ℕ) + 1) := by positivity
  simp only [cubeIdx]
  omega

/-- The threefold Dirichlet convolution of a coefficient vector, indexed by `Fin (N³)`. -/
noncomputable def convCube (N : ℕ) (a : Fin N → ℂ) : Fin (N ^ (3 : ℕ)) → ℂ := fun j =>
  ∑ p ∈ (Finset.univ : Finset (Fin N × Fin N × Fin N)).filter (fun p => cubeIdx p = j),
    a p.1 * a p.2.1 * a p.2.2

/-- The phase of a triple is the phase of its product. -/
theorem exp_phase_cubeIdx {N : ℕ} (t : ℝ) (p : Fin N × Fin N × Fin N) :
    Complex.exp (((t * Real.log ((p.1 : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((t * Real.log ((p.2.1 : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((t * Real.log ((p.2.2 : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((t * Real.log ((cubeIdx p : ℕ) + 1) : ℝ) : ℂ) * Complex.I) := by
  have h1 : ((p.1 : ℕ) + 1 : ℝ) ≠ 0 := by positivity
  have h2 : ((p.2.1 : ℕ) + 1 : ℝ) ≠ 0 := by positivity
  have h3 : ((p.2.2 : ℕ) + 1 : ℝ) ≠ 0 := by positivity
  have hcast : (((cubeIdx p : ℕ) + 1 : ℕ) : ℝ)
      = (((p.1 : ℕ) + 1 : ℕ) : ℝ) * (((p.2.1 : ℕ) + 1 : ℕ) : ℝ) * (((p.2.2 : ℕ) + 1 : ℕ) : ℝ) := by
    rw [cubeIdx_val_add_one]
    push_cast
    ring
  have hlog : Real.log ((cubeIdx p : ℕ) + 1)
      = Real.log ((p.1 : ℕ) + 1) + Real.log ((p.2.1 : ℕ) + 1) + Real.log ((p.2.2 : ℕ) + 1) := by
    have hc : ((cubeIdx p : ℕ) + 1 : ℝ)
        = (((p.1 : ℕ) + 1 : ℝ) * ((p.2.1 : ℕ) + 1 : ℝ)) * ((p.2.2 : ℕ) + 1 : ℝ) := by
      push_cast at hcast ⊢
      linarith [hcast]
    rw [hc, Real.log_mul (by positivity) h3, Real.log_mul h1 h2]
  rw [← Complex.exp_add, ← Complex.exp_add, hlog]
  congr 1
  push_cast
  ring

/-- **The cube of a Dirichlet polynomial is a Dirichlet polynomial.** -/
theorem dirPoly_convCube (N : ℕ) (a : Fin N → ℂ) (t : ℝ) :
    dirPoly (N ^ (3 : ℕ)) (convCube N a) t = (dirPoly N a t) ^ (3 : ℕ) := by
  classical
  set E : Fin N → ℂ := fun n =>
    Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I) with hE
  have hcube : (dirPoly N a t) ^ (3 : ℕ)
      = ∑ p : Fin N × Fin N × Fin N, (a p.1 * a p.2.1 * a p.2.2)
          * (E p.1 * E p.2.1 * E p.2.2) := by
    have hpoly : dirPoly N a t = ∑ n : Fin N, a n * E n := rfl
    simp only [Fintype.sum_prod_type]
    rw [hpoly, pow_three]
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    refine Finset.sum_congr rfl fun m _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hphase : ∀ p : Fin N × Fin N × Fin N,
      (a p.1 * a p.2.1 * a p.2.2) * (E p.1 * E p.2.1 * E p.2.2)
        = (a p.1 * a p.2.1 * a p.2.2)
            * Complex.exp (((t * Real.log ((cubeIdx p : ℕ) + 1) : ℝ) : ℂ) * Complex.I) := by
    intro p
    rw [hE]
    rw [exp_phase_cubeIdx t p]
  rw [hcube]
  simp only [hphase]
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin N × Fin N × Fin N)))
    (t := (Finset.univ : Finset (Fin (N ^ (3 : ℕ))))) (g := fun p => cubeIdx p)
    (f := fun p : Fin N × Fin N × Fin N => (a p.1 * a p.2.1 * a p.2.2)
      * Complex.exp (((t * Real.log ((cubeIdx p : ℕ) + 1) : ℝ) : ℂ) * Complex.I))
    (fun p _ => Finset.mem_univ _)
  rw [← hfib]
  have hpoly : dirPoly (N ^ (3 : ℕ)) (convCube N a) t
      = ∑ j : Fin (N ^ (3 : ℕ)), convCube N a j
          * Complex.exp (((t * Real.log ((j : ℕ) + 1) : ℝ) : ℂ) * Complex.I) := rfl
  rw [hpoly]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [convCube, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_filter] at hp
  rw [hp.2]

end RHTower.Sieve
