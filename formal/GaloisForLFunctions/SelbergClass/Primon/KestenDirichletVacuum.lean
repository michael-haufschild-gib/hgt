import GaloisForLFunctions.SelbergClass.Primon.KestenDirichletGreenKernel

/-!
# Exact vacuum truncation error

The Dirichlet vacuum response is
`q/(1+q) * (1-q^(2N+2))/(1-q^(2N+3))`. Its strictly positive deficit
and successive gains have closed formulas, giving monotone convergence
to the actual infinite vacuum response.
-/

open _root_.RHTower Filter Topology
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

private theorem denominator_pos (p : Nat.Primes) (n : ℕ) :
    0 < 1 - primeReciprocal p ^ (2 * n + 3) :=
  sub_pos.mpr (pow_lt_one₀ (primeReciprocal_pos p).le (primeReciprocal_lt_one p) (by omega))

private theorem one_add_ne (p : Nat.Primes) : 1 + primeReciprocal p ≠ 0 := by
  have := primeReciprocal_pos p
  positivity

private theorem vacuum_green (p : Nat.Primes) :
    kestenGreenEntry p 0 0 = primeReciprocal p / (1 + primeReciprocal p) := by
  rw [kestenGreenEntry_diagonal]
  simp only [Nat.mul_zero, zero_add, pow_one]
  have hgap : 1 - primeReciprocal p ^ 2 ≠ 0 :=
    (sub_pos.mpr (pow_lt_one₀ (primeReciprocal_pos p).le (primeReciprocal_lt_one p) (by decide))).ne'
  field_simp [hgap, one_add_ne p]
  ring

/-- Vacuum response with a Dirichlet boundary just beyond depth `n`. -/
def kestenDirichletVacuum (p : Nat.Primes) (n : ℕ) : ℝ := kestenDirichletGreen p n 0 0

/-- The exact rational vacuum approximation at every finite depth. -/
theorem kestenDirichletVacuum_eq (p : Nat.Primes) (n : ℕ) :
    kestenDirichletVacuum p n = primeReciprocal p / (1 + primeReciprocal p) *
      (1 - primeReciprocal p ^ (2 * n + 2)) / (1 - primeReciprocal p ^ (2 * n + 3)) := by
  rw [kestenDirichletVacuum, kestenDirichletGreen_entry_factor, vacuum_green]
  simp only [Fin.val_zero, max_self, Nat.sub_zero]
  rw [show 2 * (n + 1) = 2 * n + 2 by omega]

/-- The exact vacuum deficit decays with the squared geometric depth. -/
theorem kestenDirichletVacuum_defect (p : Nat.Primes) (n : ℕ) :
    primeReciprocal p / (1 + primeReciprocal p) - kestenDirichletVacuum p n =
      primeReciprocal p ^ (2 * n + 3) * (1 - primeReciprocal p) /
        ((1 + primeReciprocal p) * (1 - primeReciprocal p ^ (2 * n + 3))) := by
  rw [kestenDirichletVacuum_eq]
  field_simp [one_add_ne p, (denominator_pos p n).ne']
  rw [show 2 * n + 3 = (2 * n + 2) + 1 by omega, pow_succ]
  ring

theorem kestenDirichletVacuum_pos (p : Nat.Primes) (n : ℕ) : 0 < kestenDirichletVacuum p n :=
  kestenDirichletGreen_entry_pos p n 0 0

theorem kestenDirichletVacuum_lt_infinite (p : Nat.Primes) (n : ℕ) :
    kestenDirichletVacuum p n < primeReciprocal p / (1 + primeReciprocal p) := by
  rw [← vacuum_green]
  exact kestenDirichletGreen_entry_lt p n 0 0

/-- Adding one depth increases the vacuum response by an explicit positive amount. -/
theorem kestenDirichletVacuum_step (p : Nat.Primes) (n : ℕ) :
    kestenDirichletVacuum p (n + 1) - kestenDirichletVacuum p n =
      primeReciprocal p ^ (2 * n + 3) * (1 - primeReciprocal p) ^ 2 /
        ((1 - primeReciprocal p ^ (2 * n + 3)) *
          (1 - primeReciprocal p ^ (2 * (n + 1) + 3))) := by
  calc
    _ = (primeReciprocal p / (1 + primeReciprocal p) - kestenDirichletVacuum p n) -
        (primeReciprocal p / (1 + primeReciprocal p) - kestenDirichletVacuum p (n + 1)) := by ring
    _ = _ := by
      rw [kestenDirichletVacuum_defect, kestenDirichletVacuum_defect]
      field_simp [one_add_ne p, (denominator_pos p n).ne', (denominator_pos p (n + 1)).ne']
      rw [show 2 * (n + 1) + 3 = (2 * n + 3) + 2 by omega, pow_add]
      ring

theorem strictMono_kestenDirichletVacuum (p : Nat.Primes) : StrictMono (kestenDirichletVacuum p) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := div_pos (mul_pos (pow_pos (primeReciprocal_pos p) (2 * n + 3))
    (pow_pos (sub_pos.mpr (primeReciprocal_lt_one p)) 2))
      (mul_pos (denominator_pos p n) (denominator_pos p (n + 1)))
  rw [← kestenDirichletVacuum_step] at h
  exact sub_pos.mp h

/-- Finite vacuum responses increase to the actual prime vacuum Green value. -/
theorem tendsto_kestenDirichletVacuum (p : Nat.Primes) :
    Tendsto (kestenDirichletVacuum p) atTop (𝓝 (primeReciprocal p / (1 + primeReciprocal p))) := by
  simpa only [Nat.zero_add, kestenDirichletVacuum, vacuum_green] using
    tendsto_kestenDirichletGreen_fixedEntry p 0 0

end
end GaloisForLFunctions.SelbergClass.Primon

#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenDirichletVacuum_eq
#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenDirichletVacuum_defect
#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenDirichletVacuum_pos
#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenDirichletVacuum_lt_infinite
#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenDirichletVacuum_step
#print axioms GaloisForLFunctions.SelbergClass.Primon.strictMono_kestenDirichletVacuum
#print axioms GaloisForLFunctions.SelbergClass.Primon.tendsto_kestenDirichletVacuum
