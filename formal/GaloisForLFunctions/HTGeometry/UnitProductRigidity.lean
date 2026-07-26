import Mathlib

/-!
# A product of sub-unit factors equal to one forces every factor to be a unit

If finitely many complex numbers have modulus at most one and their product has modulus one, then
every one of them has modulus one.  Combined with the fact that an averaged exponential
`(1/2π)∫ exp(i f(θ)) dθ` has modulus one only when `f` is constant, this is the rigidity step that
turns an Euler product identity into the vanishing of every local factor.

The setting it abstracts: the characteristic function of the difference of two zero-counting
fluctuations is identically `1` (the difference is integer-valued), while an equidistribution
argument evaluates the same quantity as an Euler product of averaged exponentials.  Every local
factor must therefore be a unit, forcing every local oscillation — hence every coefficient
difference — to vanish.

Corpus check: `research "product of norms equal one implies each"` returns only unrelated
theta-tail and prime-coherence results; no duplication.
-/

open Finset

namespace HTGeometry

/-- **Unit-product rigidity.**  If each `‖a i‖ ≤ 1` and `∏ ‖a i‖ = 1`, then every `‖a i‖ = 1`. -/
theorem norm_eq_one_of_prod_norm_eq_one {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℂ)
    (hle : ∀ i ∈ s, ‖a i‖ ≤ 1) (hprod : ∏ i ∈ s, ‖a i‖ = 1) :
    ∀ i ∈ s, ‖a i‖ = 1 := by
  classical
  intro i hi
  by_contra hne
  have hlt : ‖a i‖ < 1 := lt_of_le_of_ne (hle i hi) hne
  have hnn : ∀ j ∈ s, 0 ≤ ‖a j‖ := fun j _ => norm_nonneg _
  have hrest : ∏ j ∈ s.erase i, ‖a j‖ ≤ 1 :=
    Finset.prod_le_one (fun j hj => hnn j (Finset.mem_of_mem_erase hj))
      (fun j hj => hle j (Finset.mem_of_mem_erase hj))
  have hsplit : ∏ j ∈ s, ‖a j‖ = ‖a i‖ * ∏ j ∈ s.erase i, ‖a j‖ :=
    (Finset.mul_prod_erase s _ hi).symm
  have hrestnn : 0 ≤ ∏ j ∈ s.erase i, ‖a j‖ :=
    Finset.prod_nonneg (fun j hj => hnn j (Finset.mem_of_mem_erase hj))
  rw [hsplit] at hprod
  nlinarith [hprod, hlt, hrest, hrestnn, norm_nonneg (a i)]

/-- The same conclusion stated for the product of the numbers themselves having modulus one. -/
theorem norm_eq_one_of_norm_prod_eq_one {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℂ)
    (hle : ∀ i ∈ s, ‖a i‖ ≤ 1) (hprod : ‖∏ i ∈ s, a i‖ = 1) :
    ∀ i ∈ s, ‖a i‖ = 1 := by
  refine norm_eq_one_of_prod_norm_eq_one s a hle ?_
  rw [← norm_prod]
  exact hprod

end HTGeometry
