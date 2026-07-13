import Mathlib

/-!
# The exact pairwise-dispersion moment identity

The algebraic core of the low-temperature curvature law
(`zeta-fisher-low-temperature-prime-gap-curvature`): for a finite weighted spectrum with weights `w i`
and energies `x i`, the moment combination `M₂M₄ − M₃²` (with `Mⱼ = ∑ᵢ wᵢ xᵢʲ`) is an exact
manifestly-nonnegative pairwise sum

`2 (M₂M₄ − M₃²) = ∑_{a,b} w_a w_b x_a² x_b² (x_a − x_b)²`.

This is a pure finite-sum identity over any commutative ring; when weights and energies are nonnegative
reals it exhibits `M₂M₄ − M₃²` as a nonnegative Gram-type dispersion (each summand a product of squares),
which is what drives the sign of the curvature `R = −(M₂M₄ − M₃²)/M₂³`.  It is the exact identity the card
invokes before taking the low-temperature (`β → ∞`) dominated-convergence limit.
-/

open scoped BigOperators

namespace ZetaFisher

/-- **Exact pairwise-dispersion identity.**  With `Mⱼ = ∑ᵢ∈s wᵢ xᵢʲ`,
`2 (M₂M₄ − M₃²) = ∑_{a,b∈s} w_a w_b x_a² x_b² (x_a − x_b)²`.  A pure symmetrization identity: each of
the two cross-term double sums is reindexed `a ↔ b` and combined into a perfect square. -/
theorem two_mul_dispersion {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι) (w x : ι → R) :
    2 * ((∑ i ∈ s, w i * x i ^ 2) * (∑ i ∈ s, w i * x i ^ 4) - (∑ i ∈ s, w i * x i ^ 3) ^ 2)
      = ∑ a ∈ s, ∑ b ∈ s, w a * w b * x a ^ 2 * x b ^ 2 * (x a - x b) ^ 2 := by
  set d : ι → ι → R := fun a b => w a * w b * x a ^ 2 * x b ^ 2 * (x b ^ 2 - x a * x b) with hd
  -- expand the two products of sums into double sums
  have hM24 : (∑ i ∈ s, w i * x i ^ 2) * (∑ i ∈ s, w i * x i ^ 4)
      = ∑ a ∈ s, ∑ b ∈ s, w a * w b * x a ^ 2 * x b ^ 4 := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
  have hM33 : (∑ i ∈ s, w i * x i ^ 3) ^ 2
      = ∑ a ∈ s, ∑ b ∈ s, w a * w b * x a ^ 3 * x b ^ 3 := by
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
  -- combine the cross-difference into a single double sum of `d`
  have key : (∑ a ∈ s, ∑ b ∈ s, w a * w b * x a ^ 2 * x b ^ 4)
           - (∑ a ∈ s, ∑ b ∈ s, w a * w b * x a ^ 3 * x b ^ 3)
           = ∑ a ∈ s, ∑ b ∈ s, d a b := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun b _ => by simp only [hd]; ring)
  have hswap : ∑ a ∈ s, ∑ b ∈ s, d a b = ∑ a ∈ s, ∑ b ∈ s, d b a := Finset.sum_comm
  rw [hM24, hM33, key]
  -- prove RHS = 2 * ∑∑ d via symmetrization, then flip
  refine (?_ : ∑ a ∈ s, ∑ b ∈ s, w a * w b * x a ^ 2 * x b ^ 2 * (x a - x b) ^ 2
      = 2 * ∑ a ∈ s, ∑ b ∈ s, d a b).symm
  calc ∑ a ∈ s, ∑ b ∈ s, w a * w b * x a ^ 2 * x b ^ 2 * (x a - x b) ^ 2
      = ∑ a ∈ s, ∑ b ∈ s, (d a b + d b a) := by
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
        simp only [hd]; ring
    _ = (∑ a ∈ s, ∑ b ∈ s, d a b) + (∑ a ∈ s, ∑ b ∈ s, d b a) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun a _ => Finset.sum_add_distrib)
    _ = (∑ a ∈ s, ∑ b ∈ s, d a b) + (∑ a ∈ s, ∑ b ∈ s, d a b) := by rw [← hswap]
    _ = 2 * ∑ a ∈ s, ∑ b ∈ s, d a b := (two_mul _).symm

/-- Nonnegativity form: over an ordered field with nonnegative weights, `M₂M₄ − M₃² ≥ 0`. -/
theorem dispersion_nonneg {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {ι : Type*} (s : Finset ι) (w x : ι → R) (hw : ∀ i ∈ s, 0 ≤ w i) :
    0 ≤ (∑ i ∈ s, w i * x i ^ 2) * (∑ i ∈ s, w i * x i ^ 4) - (∑ i ∈ s, w i * x i ^ 3) ^ 2 := by
  have h2 : (0 : R) ≤ 2 * ((∑ i ∈ s, w i * x i ^ 2) * (∑ i ∈ s, w i * x i ^ 4)
      - (∑ i ∈ s, w i * x i ^ 3) ^ 2) := by
    rw [two_mul_dispersion]
    refine Finset.sum_nonneg (fun a ha => Finset.sum_nonneg (fun b hb => ?_))
    have heq : w a * w b * x a ^ 2 * x b ^ 2 * (x a - x b) ^ 2
        = (w a * w b) * (x a * x b * (x a - x b)) ^ 2 := by ring
    rw [heq]
    exact mul_nonneg (mul_nonneg (hw a ha) (hw b hb)) (sq_nonneg _)
  linarith [h2]

end ZetaFisher
