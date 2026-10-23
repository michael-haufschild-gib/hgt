import GaloisForLFunctions.SignedArithmeticEnergyIncidence.SignedIncidenceForms
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Fin

/-!
# Cartesian products add ground energies

A train carried by several towers at once is a product of chains: its amplitude lives on a box,
and the lag charge of each prime runs along one coordinate.  The incidence form of such a train is
the **Cartesian product** of the one-tower forms (`cartesianCoupling`): an overlap along the first
factor at fixed second coordinate, or along the second factor at fixed first coordinate.

* **Energy splits along the factors** (`incidenceEnergy_cartesian`): the energy of a profile on
  `ι × κ` is the sum of the first-factor energies of its columns and the second-factor energies of
  its rows.
* **Ground energies add** (`cartesian_lower_bound`, `cartesian_attained`): if `λ₁ Σ g² ≤ E₁(g)` and
  `λ₂ Σ g² ≤ E₂(g)`, then `(λ₁ + λ₂) Σ f² ≤ E_{1□2}(f)`, and the product of two ground states attains
  the sum.

Iterating over a finite family of towers, the joint capacity of any number of multiplicatively
aligned towers is the sum of their single-tower capacities, attained by the product of their sine
trains (`TowerGridCapacitiesAdd` is the case of two towers): on aligned trains the primes never
cancel, whatever their number.
-/

open Finset

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The Cartesian product of two incidence forms. -/
def cartesianCoupling (c : ι → ι → ℝ) (d : κ → κ → ℝ) : ι × κ → ι × κ → ℝ := fun x y =>
  (if x.2 = y.2 then c x.1 y.1 else 0) + (if x.1 = y.1 then d x.2 y.2 else 0)

omit [Fintype ι] [Fintype κ] in
theorem IsSymmetricCoupling.cartesian {c : ι → ι → ℝ} {d : κ → κ → ℝ}
    (hc : IsSymmetricCoupling c) (hd : IsSymmetricCoupling d) :
    IsSymmetricCoupling (cartesianCoupling c d) := by
  intro x y
  simp only [cartesianCoupling, eq_comm (a := x.2), eq_comm (a := x.1), hc x.1 y.1, hd x.2 y.2]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Energy is quadratic in the profile. -/
theorem incidenceEnergy_smul {ι : Type*} [Fintype ι] (c : ι → ι → ℝ) (t : ℝ) (g : ι → ℝ) :
    incidenceEnergy c (fun i => t * g i) = t ^ 2 * incidenceEnergy c g := by
  unfold incidenceEnergy
  rw [mul_sum]
  exact sum_congr rfl fun i _ => by rw [mul_sum]; exact sum_congr rfl fun j _ => by ring

/-- **The energy of a product splits along the factors.** -/
theorem incidenceEnergy_cartesian (c : ι → ι → ℝ) (d : κ → κ → ℝ) (f : ι × κ → ℝ) :
    incidenceEnergy (cartesianCoupling c d) f =
      ∑ k, incidenceEnergy c (fun i => f (i, k)) + ∑ i, incidenceEnergy d (fun k => f (i, k)) := by
  unfold incidenceEnergy
  rw [Fintype.sum_prod_type]
  have hx : ∀ i k, ∑ y : ι × κ, cartesianCoupling c d (i, k) y * f (i, k) * f y =
      ∑ j, c i j * f (i, k) * f (j, k) + ∑ l, d k l * f (i, k) * f (i, l) := by
    intro i k
    rw [Fintype.sum_prod_type]
    simp only [cartesianCoupling, add_mul, sum_add_distrib, ite_mul, zero_mul]
    congr 1
    · exact sum_congr rfl fun j _ => by rw [Finset.sum_ite_eq]; simp
    · simp only [Finset.sum_ite_irrel, sum_const_zero]
      rw [Finset.sum_ite_eq]
      simp
  simp only [hx, sum_add_distrib]
  rw [Finset.sum_comm (f := fun i k => ∑ j, c i j * f (i, k) * f (j, k))]

/-- **Ground energies add** under Cartesian products. -/
theorem cartesian_lower_bound {c : ι → ι → ℝ} {d : κ → κ → ℝ} {l₁ l₂ : ℝ}
    (h₁ : ∀ g, l₁ * ∑ i, g i ^ 2 ≤ incidenceEnergy c g)
    (h₂ : ∀ g, l₂ * ∑ k, g k ^ 2 ≤ incidenceEnergy d g) (f : ι × κ → ℝ) :
    (l₁ + l₂) * ∑ x, f x ^ 2 ≤ incidenceEnergy (cartesianCoupling c d) f := by
  rw [incidenceEnergy_cartesian, Fintype.sum_prod_type, add_mul]
  have hcol : l₁ * ∑ i, ∑ k, f (i, k) ^ 2 ≤ ∑ k, incidenceEnergy c (fun i => f (i, k)) := by
    rw [sum_comm, mul_sum]
    exact sum_le_sum fun k _ => h₁ _
  have hrow : l₂ * ∑ i, ∑ k, f (i, k) ^ 2 ≤ ∑ i, incidenceEnergy d (fun k => f (i, k)) := by
    rw [mul_sum]
    exact sum_le_sum fun i _ => h₂ _
  linarith

/-- The product of two ground states attains the sum of the ground energies. -/
theorem cartesian_attained {c : ι → ι → ℝ} {d : κ → κ → ℝ} {l₁ l₂ : ℝ} {g₁ : ι → ℝ}
    {g₂ : κ → ℝ} (h₁ : incidenceEnergy c g₁ = l₁ * ∑ i, g₁ i ^ 2)
    (h₂ : incidenceEnergy d g₂ = l₂ * ∑ k, g₂ k ^ 2) :
    incidenceEnergy (cartesianCoupling c d) (fun x => g₁ x.1 * g₂ x.2) =
      (l₁ + l₂) * ∑ x : ι × κ, (g₁ x.1 * g₂ x.2) ^ 2 := by
  rw [incidenceEnergy_cartesian, Fintype.sum_prod_type]
  have hcol : ∀ k, incidenceEnergy c (fun i => g₁ i * g₂ k) = g₂ k ^ 2 * (l₁ * ∑ i, g₁ i ^ 2) := by
    intro k
    rw [← h₁, ← incidenceEnergy_smul]
    exact congrArg _ (funext fun i => by ring)
  have hrow : ∀ i, incidenceEnergy d (fun k => g₁ i * g₂ k) = g₁ i ^ 2 * (l₂ * ∑ k, g₂ k ^ 2) := by
    intro i
    rw [← h₂, ← incidenceEnergy_smul]
  simp only [hcol, hrow]
  simp only [mul_pow, ← sum_mul, ← mul_sum]
  ring

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
