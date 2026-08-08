/-
# The prime resonance of a zero is transcendentally generic — and blind to the critical line

Attach to a point `s = σ + iτ` the *prime resonance*: the family of Euler phases
`{p^{-s}}_p = {exp(-s · log p)}_p`, indexed by the primes.  Its exponents are `{-s · log p}_p`.
This module isolates the transcendence structure of that family and extracts a no-go.

**Unconditional.**  For every nonzero scalar `α` the resonance exponents `{α · log p}_p` are
`ℚ`-linearly independent (`resonanceExponent_linearIndependent`).  The proof scales the unconditional
`ℤ`-independence of `{log p}` (`primeLog_linearIndependent`, unique factorization) up to `ℚ`, pushes
it along `ℝ ↪ ℂ`, and multiplies by the unit `α`.

**Given Schanuel.**  Since the exponents are `ℚ`-linearly independent, Schanuel's conjecture applies
to `x_i = α · log p_i` and produces an `n`-element algebraically independent subfamily drawn from the
exponents `{α · log p_i}` together with the values `{exp(α · log p_i)} = {p_i^{α}}`
(`resonance_schanuel_algIndep_subset`): the resonance data `{α log p_i, p_i^{α}}` has transcendence
degree at least `n`.

**The no-go (line-blindness).**  Both statements hypothesize only `α ≠ 0` — the real part `σ` never
enters.  So the transcendence type of the prime resonance is *uniform over the punctured plane*: it is
identical at a critical-line zero (`σ = ½`) and at any hypothetical off-line zero.  Consequently no
invariant built from the `ℚ`-linear — or, granting Schanuel, the algebraic-independence — type of the
prime-resonance exponents/values can detect an off-line zero.  A putative off-line obstruction must be
carried by the *analytic* vanishing relation `ζ(ρ) = 0` coupling an already-generic family, never by
the family's transcendence type.
-/
import GaloisForLFunctions.HTGeometry.WeldRateLattice
import GaloisForLFunctions.RHTower.SchanuelWeldApex

open Complex

namespace GaloisForLFunctions.RHTower

/-- **The resonance exponents of any nonzero scalar are `ℚ`-linearly independent.**  For `α ≠ 0`,
the family `p ↦ α · log p` (over the primes) satisfies no nontrivial finite `ℚ`-linear relation.
The real part of `α` plays no role: independence is uniform over `α ∈ ℂ \ {0}`.

Mechanism: `primeLog_linearIndependent` gives `ℤ`-linear independence of `{log p}` in `ℝ`; upgrading
scalars to `ℚ`, pushing along the `ℚ`-linear injection `ℝ ↪ ℂ`, and applying the injective `ℚ`-linear
multiplication `z ↦ α · z` (injective as `α ≠ 0` in the domain `ℂ`) preserves independence. -/
theorem resonanceExponent_linearIndependent (α : ℂ) (hα : α ≠ 0) :
    LinearIndependent ℚ (fun p : Nat.Primes => α * (Real.log (p : ℕ) : ℂ)) := by
  have hQ : LinearIndependent ℚ (fun p : Nat.Primes => (Real.log (p : ℕ) : ℝ)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp primeLog_linearIndependent
  -- Push `ℝ → ℂ` along the `ℚ`-linear (restricted-scalar) algebra map.
  let f : ℝ →ₗ[ℚ] ℂ := (Algebra.linearMap ℝ ℂ).restrictScalars ℚ
  have hfe : ∀ r : ℝ, f r = (r : ℂ) := fun _ => rfl
  have hfker : f.ker = ⊥ := LinearMap.ker_eq_bot.mpr
    (fun a b hab => Complex.ofReal_injective (by rw [hfe, hfe] at hab; exact hab))
  have hC : LinearIndependent ℚ (fun p : Nat.Primes => ((Real.log (p : ℕ) : ℝ) : ℂ)) := by
    have hmap := hQ.map' f hfker
    have hcomp : (⇑f ∘ (fun p : Nat.Primes => (Real.log (p : ℕ) : ℝ)))
        = (fun p : Nat.Primes => ((Real.log (p : ℕ) : ℝ) : ℂ)) := by funext p; exact hfe _
    rwa [hcomp] at hmap
  -- Multiply by the unit `α`.
  let g : ℂ →ₗ[ℚ] ℂ := LinearMap.mulLeft ℚ α
  have hge : ∀ z : ℂ, g z = α * z := fun _ => rfl
  have hgker : g.ker = ⊥ := LinearMap.ker_eq_bot.mpr
    (fun a b hab => by rw [hge, hge] at hab; exact mul_left_cancel₀ hα hab)
  have hmap2 := hC.map' g hgker
  have hcomp2 : (⇑g ∘ (fun p : Nat.Primes => ((Real.log (p : ℕ) : ℝ) : ℂ)))
      = (fun p : Nat.Primes => α * (Real.log (p : ℕ) : ℂ)) := by funext p; exact hge _
  rwa [hcomp2] at hmap2

/-- The finite-family form feeding Schanuel: for `α ≠ 0` and distinct primes `p₁, …, pₙ`, the
resonance exponents `i ↦ α · log pᵢ` are `ℚ`-linearly independent. -/
theorem resonanceExponent_linearIndependent_fin (α : ℂ) (hα : α ≠ 0) {n : ℕ}
    (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (hpinj : Function.Injective p) :
    LinearIndependent ℚ (fun i => α * (Real.log (p i) : ℂ)) := by
  let q : Fin n → Nat.Primes := fun i => ⟨p i, hp i⟩
  have hqinj : Function.Injective q := by
    intro i j h; apply hpinj
    have := congrArg (fun P : Nat.Primes => (P : ℕ)) h; simpa [q] using this
  have hcomp := (resonanceExponent_linearIndependent α hα).comp q hqinj
  have he : ((fun P : Nat.Primes => α * (Real.log (P : ℕ) : ℂ)) ∘ q)
      = (fun i => α * (Real.log (p i) : ℂ)) := by funext i; simp [q]
  rwa [he] at hcomp

/-- **The prime resonance has transcendence degree `≥ n`, given Schanuel.**  For `α ≠ 0` and distinct
primes `p₁, …, pₙ`, Schanuel's conjecture supplies an `n`-element algebraically independent family
drawn from the resonance exponents `{α · log pᵢ}` and the resonance values
`{exp(α · log pᵢ)} = {pᵢ^{α}}`.  Direct application of Schanuel to the `ℚ`-linearly independent
exponents (`resonanceExponent_linearIndependent_fin`).

The hypotheses never mention `Re α`, so the conclusion is uniform over the punctured plane: the
resonance transcendence degree at a critical-line zero equals that at any off-line zero. -/
theorem resonance_schanuel_algIndep_subset (hS : SchanuelConjecture) (α : ℂ) (hα : α ≠ 0)
    {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (hpinj : Function.Injective p) :
    ∃ t : Fin n → ℂ, Function.Injective t ∧
      (∀ i, t i ∈ Set.range (fun j => α * (Real.log (p j) : ℂ)) ∪
        Set.range (fun j => Complex.exp (α * (Real.log (p j) : ℂ)))) ∧
      AlgebraicIndependent ℚ t :=
  hS n (fun i => α * (Real.log (p i) : ℂ)) (resonanceExponent_linearIndependent_fin α hα p hp hpinj)

end GaloisForLFunctions.RHTower
