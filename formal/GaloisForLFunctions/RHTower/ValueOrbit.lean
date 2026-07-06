/-
The value-orbit of a finite integer frequency set and its multiplicative-relation subtori.

For a finite family of positive reals `n j`, the map `t ↦ (n j ^ (−it))_j`, i.e.
`(exp(−i·t·log (n j)))_j`, traces a one-parameter subgroup of a torus — the joint phase of the
Dirichlet monomials at a moving height. The closure of that orbit is a subtorus whose codimension
is the rank of the multiplicative relation module of the `n j`; this file records its
codimension-1 face.

A multiplicative relation `∏ (n j)^(k j) = 1` forces the group character `x ↦ ∏ x_j^(k j)` to be
identically `1` along the orbit, so the orbit lies inside the subtorus that relation cuts out. The
bridge is elementary: `∏ (n j)^(k j) = 1` is equivalent to `∑ (k j)·log (n j) = 0` (logarithm of a
product), and that linear combination of logs is exactly the frequency of the orbit character
`∏ (·)^(k j)`.
-/
import Mathlib

open Real Complex BigOperators

noncomputable section

namespace RHTower

/-- A multiplicative relation among positive reals is a linear relation among their logs:
if `∏ (n j)^(k j) = 1` then `∑ (k j)·log (n j) = 0`. -/
theorem log_relation_of_mul_relation {ι : Type*} (s : Finset ι) (n : ι → ℝ) (k : ι → ℤ)
    (hn : ∀ j ∈ s, 0 < n j) (hrel : ∏ j ∈ s, (n j) ^ (k j) = 1) :
    ∑ j ∈ s, (k j : ℝ) * Real.log (n j) = 0 := by
  have h0 : ∀ j ∈ s, (n j) ^ (k j) ≠ 0 := fun j hj => zpow_ne_zero _ (hn j hj).ne'
  have hlog : Real.log (∏ j ∈ s, (n j) ^ (k j))
      = ∑ j ∈ s, (k j : ℝ) * Real.log (n j) := by
    rw [Real.log_prod h0]
    exact Finset.sum_congr rfl (fun j _ => Real.log_zpow (n j) (k j))
  rw [hrel, Real.log_one] at hlog
  exact hlog.symm

/-- **Single-relation orbit containment** (the rank–codimension law, codimension-1 face).
For a finite family of positive reals with a multiplicative relation `∏ (n j)^(k j) = 1`, the value
orbit `t ↦ (n j ^ (−it))_j = (exp(−i·t·log (n j)))_j` lies on the subtorus cut by that relation:
the character `∏ (·)^(k j)` equals `1` at every point of the orbit. Taking `n = ![2, 4]`,
`k = ![-2, 1]` (`4 = 2²`) recovers the value orbit lying on the curve `(z, z²)`. -/
theorem orbit_on_relation_subtorus {ι : Type*} (s : Finset ι) (n : ι → ℝ) (k : ι → ℤ)
    (hn : ∀ j ∈ s, 0 < n j) (hrel : ∏ j ∈ s, (n j) ^ (k j) = 1) (t : ℝ) :
    ∏ j ∈ s, (Complex.exp (-(t : ℂ) * (Real.log (n j) : ℂ) * Complex.I)) ^ (k j) = 1 := by
  have hlog := log_relation_of_mul_relation s n k hn hrel
  have step : ∀ j ∈ s,
      (Complex.exp (-(t : ℂ) * (Real.log (n j) : ℂ) * Complex.I)) ^ (k j)
        = Complex.exp ((k j : ℂ) * (-(t : ℂ) * (Real.log (n j) : ℂ) * Complex.I)) :=
    fun j _ => (Complex.exp_int_mul _ _).symm
  rw [Finset.prod_congr rfl step, ← Complex.exp_sum]
  have hsum : ∑ j ∈ s, (k j : ℂ) * (-(t : ℂ) * (Real.log (n j) : ℂ) * Complex.I)
      = -(t : ℂ) * Complex.I * ((∑ j ∈ s, (k j : ℝ) * Real.log (n j) : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hsum, hlog]
  simp

end RHTower
