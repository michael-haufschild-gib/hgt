import GaloisForLFunctions.RHTower.RouteEHardCorePrimitiveBridge

/-!
# The empty Walsh grade retains the Route E Möbius source

The source-faithful Radon amplifier does not suppress the zero interaction
grade. Its biased-Walsh coefficient is exactly a vacuum Euler product times
the primewise totient-weighted source sum. This identifies an arithmetic
obstruction in the spectral bridge; it does not bound that sum.
-/

open scoped BigOperators

namespace RHTower
open HTGeometry.ConstraintFrameRelativity
open GaloisForLFunctions.HTGeometry

noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Bernoulli vacuum mass of the critical one-leg field. -/
def routeEHardCoreVacuumWeight (p : ι → ℝ) : ℝ :=
  ∏ i, p i / (p i + 1)

/-- Primewise totient ratio on an occupied subset. -/
def routeEHardCoreTotientRatio (p : ι → ℝ) (S : Finset ι) : ℝ :=
  ∏ i, if i ∈ S then (p i - 1) / p i else 1

/-- The exact pointwise weight left after Radon amplification. -/
theorem routeEHardCoreWeightAmplifier_eq_vacuum_mul_totientRatio
    (p : ι → ℝ) (hp : ∀ i, p i ≠ 0)
    (hp1 : ∀ i, p i + 1 ≠ 0) (S : Finset ι) :
    bernoulliWeight (fun i => 1 / (p i + 1)) S *
      routeEHardCorePrimitiveAmplifier p S =
        routeEHardCoreVacuumWeight p * routeEHardCoreTotientRatio p S := by
  have hsplit (r : ι → ℝ) (U : Finset ι) :
      bernoulliWeight r U = ∏ i, if i ∈ U then r i else 1 - r i := by
    have hfilter : (Finset.univ.filter fun i => i ∉ U) = Uᶜ := by
      ext i
      simp
    simpa [bernoulliWeight, hfilter] using
      (Finset.prod_ite (s := Finset.univ) (p := fun i => i ∈ U)
        r (fun i => 1 - r i)).symm
  rw [hsplit]
  unfold routeEHardCorePrimitiveAmplifier routeEHardCoreVacuumWeight
    routeEHardCoreTotientRatio
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases his : i ∈ S
  · simp only [his, ite_true]
    field_simp [hp i, hp1 i]
  · simp only [his, ite_false, mul_one]
    field_simp [hp i, hp1 i]
    ring

/-- Exact zero-grade projection for every finite source observable. -/
theorem routeEHardCoreEmptyGrade_eq_totientWeightedSum
    (p : ι → ℝ) (hp : ∀ i, p i ≠ 0)
    (hp1 : ∀ i, p i + 1 ≠ 0) (a : Finset ι → ℝ) :
    biasedWalshCoefficient (fun i => 1 / (p i + 1))
        (fun S => routeEHardCorePrimitiveAmplifier p S * a S) ∅ =
      routeEHardCoreVacuumWeight p *
        ∑ S : Finset ι, routeEHardCoreTotientRatio p S * a S := by
  rw [biasedWalshCoefficient_empty]
  unfold bernoulliExp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  change bernoulliWeight (fun i => 1 / (p i + 1)) S *
    (routeEHardCorePrimitiveAmplifier p S * a S) = _
  calc
    _ = (bernoulliWeight (fun i => 1 / (p i + 1)) S *
          routeEHardCorePrimitiveAmplifier p S) * a S := by ring
    _ = (routeEHardCoreVacuumWeight p * routeEHardCoreTotientRatio p S) * a S := by
      rw [routeEHardCoreWeightAmplifier_eq_vacuum_mul_totientRatio p hp hp1 S]
    _ = routeEHardCoreVacuumWeight p *
          (routeEHardCoreTotientRatio p S * a S) := by ring

/-- Closed finite-prime zero-grade projection. -/
theorem routeEHardCorePrimeEmptyGrade_eq_totientWeightedSum
    (P : Finset Nat.Primes)
    (a : Finset {p : Nat.Primes // p ∈ P} → ℝ) :
    let v : {p : Nat.Primes // p ∈ P} → ℝ := fun i => ((i.1 : ℕ) : ℝ)
    biasedWalshCoefficient (fun i => 1 / (v i + 1))
        (fun S => routeEHardCorePrimitiveAmplifier v S * a S) ∅ =
      routeEHardCoreVacuumWeight v *
        ∑ S : Finset {p : Nat.Primes // p ∈ P},
          routeEHardCoreTotientRatio v S * a S := by
  classical
  exact routeEHardCoreEmptyGrade_eq_totientWeightedSum
    (p := fun i : {p : Nat.Primes // p ∈ P} => ((i.1 : ℕ) : ℝ))
    (fun i => ne_of_gt (by exact_mod_cast i.1.2.pos))
    (fun i => by
      have h : (0 : ℝ) < ((i.1 : ℕ) : ℝ) := by exact_mod_cast i.1.2.pos
      exact ne_of_gt (by linarith : (0 : ℝ) < ((i.1 : ℕ) : ℝ) + 1)) a

end
end RHTower
