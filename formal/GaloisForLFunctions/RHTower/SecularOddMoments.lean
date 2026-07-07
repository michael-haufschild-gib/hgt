/-
# Secular odd moments of ξ's zeros vanish (foundations §22, `τ_{2m+1}=0`, for the actual ξ)

`FunctionalEquationParity.fe_centered_odd_moment_vanish` proves the σ-parity for an abstract
FE-reflection-invariant multiset.  This file instantiates it on the genuine object: the zeros of `ξ`
inside any ball centered at the critical point `½` form an FE-reflection-invariant configuration
(`ξ(1−s)=ξ(s)`, and the ball is invariant under `ρ ↦ 1−ρ`), and the reflection preserves multiplicity
(`xi_orderAt_one_sub`).  Hence every multiplicity-weighted centered odd moment of those zeros vanishes.
-/
import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.RHTower.Reflection

open Complex

namespace RHTower

noncomputable section

/-- **Secular odd moments vanish (for the actual ξ).**  For every radius `R` and every `m`, the
multiplicity-weighted centered odd moment of `ξ`'s zeros in the ball `‖s − ½‖ < R` vanishes:
`∑_{ρ : ‖ρ−½‖<R, ξ(ρ)=0} ord_ρ(ξ) · (ρ − ½)^{2m+1} = 0`.  The functional equation pairs each `ρ` with
`1−ρ` (same multiplicity, reflected through `½`), and the odd power makes the two contributions
cancel; the fixed point `½` contributes `0`.  This is `τ_{2m+1}=0` for the genuine ξ-divisor. -/
theorem xi_secular_odd_moment_ball_eq_zero (R : ℝ) (m : ℕ) :
    ∑ ρ ∈ (xi_zeros_finite_ball (1 / 2) R).toFinset,
      ((analyticOrderAt xi ρ).toNat : ℂ) * (ρ - 1 / 2) ^ (2 * m + 1) = 0 := by
  refine Finset.sum_involution (fun ρ _ => 1 - ρ) ?_ ?_ ?_ ?_
  · -- pairing: f ρ + f (1−ρ) = 0
    intro ρ _
    have hord : analyticOrderAt xi (1 - ρ) = analyticOrderAt xi ρ := xi_orderAt_one_sub ρ
    have hodd : Odd (2 * m + 1) := ⟨m, by ring⟩
    have hpow : (1 - ρ - 1 / 2) ^ (2 * m + 1) = -((ρ - 1 / 2) ^ (2 * m + 1)) := by
      rw [show (1 - ρ - 1 / 2) = -(ρ - 1 / 2) by ring, hodd.neg_pow]
    rw [hord, hpow]; ring
  · -- if the term is nonzero, `ρ` is not a fixed point
    intro ρ _ hfne heq
    apply hfne
    have hhalf : ρ = 1 / 2 := by linear_combination (-1 / 2 : ℂ) * heq
    rw [hhalf]; simp
  · -- the reflection maps the zero-set to itself
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ ⊢
    obtain ⟨hball, hz⟩ := hρ
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq] at hball ⊢
      rwa [show (1 - ρ) - 1 / 2 = -(ρ - 1 / 2) by ring, norm_neg]
    · rw [xi_one_sub]; exact hz
  · -- the reflection is an involution
    intro ρ _; ring

end

end RHTower
