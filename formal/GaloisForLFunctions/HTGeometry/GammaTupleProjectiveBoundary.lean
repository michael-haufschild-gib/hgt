import GaloisForLFunctions.HTGeometry.GammaVerticalDecay
import Mathlib.Topology.Algebra.Polynomial

/-!
# The projective boundary of a finite tuple of Gamma-field elements

Two Gamma-field elements normalized by their dominant Gamma powers have a ratio which, in terms of
the vanishing quantity `Γ(σ+it)`, is a power of that quantity times a ratio of polynomial values.
If the valuations agree the power is trivial and the ratio converges to the quotient of the residues;
if one valuation is strictly larger the extra power drives the ratio to zero.

That is eq. (5): normalizing a finite coefficient tuple by a valuation-minimal member makes every
ratio converge, so the tuple has a single constant point at its upper vertical projective boundary.
-/

open Filter Topology

namespace GaloisForLFunctions

variable {γ : ℝ → ℂ}

/-- The ratio of two monomial-normalized rational expressions in a vanishing quantity. -/
theorem ratio_eventuallyEq (hγ : Tendsto γ atTop (nhdsWithin 0 {(0 : ℂ)}ᶜ))
    (Rα Sα Rβ Sβ : Polynomial ℂ) (uα vα uβ vβ k : ℕ)
    (hexp : uα + vβ = uβ + vα + k) :
    (fun t => ((γ t) ^ uα * Rα.eval (γ t)) / ((γ t) ^ vα * Sα.eval (γ t))
        / (((γ t) ^ uβ * Rβ.eval (γ t)) / ((γ t) ^ vβ * Sβ.eval (γ t))))
      =ᶠ[atTop] fun t => (γ t) ^ k * ((Rα.eval (γ t) * Sβ.eval (γ t))
        / (Sα.eval (γ t) * Rβ.eval (γ t))) := by
  have hne : ∀ᶠ t in atTop, γ t ≠ 0 := hγ.eventually self_mem_nhdsWithin
  filter_upwards [hne] with t ht
  have hpow : ∀ m : ℕ, (γ t) ^ m ≠ 0 := fun m => pow_ne_zero m ht
  field_simp
  have hpowsum : (γ t) ^ uα * (γ t) ^ vβ = (γ t) ^ uβ * (γ t) ^ vα * (γ t) ^ k := by
    rw [← pow_add, ← pow_add, ← pow_add, hexp]
  calc γ t ^ uα * Polynomial.eval (γ t) Rα * γ t ^ vβ * Polynomial.eval (γ t) Sβ
        / (Polynomial.eval (γ t) Sα * Polynomial.eval (γ t) Rβ)
      = ((γ t) ^ uα * (γ t) ^ vβ) * (Polynomial.eval (γ t) Rα * Polynomial.eval (γ t) Sβ)
        / (Polynomial.eval (γ t) Sα * Polynomial.eval (γ t) Rβ) := by ring
    _ = ((γ t) ^ uβ * (γ t) ^ vα * (γ t) ^ k)
        * (Polynomial.eval (γ t) Rα * Polynomial.eval (γ t) Sβ)
        / (Polynomial.eval (γ t) Sα * Polynomial.eval (γ t) Rβ) := by rw [hpowsum]
    _ = Polynomial.eval (γ t) Rα * γ t ^ vα * γ t ^ uβ * Polynomial.eval (γ t) Sβ * γ t ^ k
        / (Polynomial.eval (γ t) Sα * Polynomial.eval (γ t) Rβ) := by ring

theorem eval_tendsto (hγ : Tendsto γ atTop (nhdsWithin 0 {(0 : ℂ)}ᶜ)) (P : Polynomial ℂ) :
    Tendsto (fun t => P.eval (γ t)) atTop (nhds (P.eval 0)) := by
  have hγ' : Tendsto γ atTop (nhds (0 : ℂ)) := hγ.mono_right nhdsWithin_le_nhds
  exact (P.continuous_aeval.tendsto 0).comp hγ'

/-- **Equal valuations: the ratio tends to the residue quotient.** -/
theorem ratio_tendsto_residue (hγ : Tendsto γ atTop (nhdsWithin 0 {(0 : ℂ)}ᶜ))
    (Rα Sα Rβ Sβ : Polynomial ℂ) (uα vα uβ vβ : ℕ)
    (hSα : Sα.eval 0 ≠ 0) (hRβ : Rβ.eval 0 ≠ 0) (hexp : uα + vβ = uβ + vα) :
    Tendsto (fun t => ((γ t) ^ uα * Rα.eval (γ t)) / ((γ t) ^ vα * Sα.eval (γ t))
        / (((γ t) ^ uβ * Rβ.eval (γ t)) / ((γ t) ^ vβ * Sβ.eval (γ t))))
      atTop (nhds (Rα.eval 0 * Sβ.eval 0 / (Sα.eval 0 * Rβ.eval 0))) := by
  have hform := ratio_eventuallyEq hγ Rα Sα Rβ Sβ uα vα uβ vβ 0 (by omega)
  refine Tendsto.congr' hform.symm ?_
  have hlim : Tendsto (fun t => (Rα.eval (γ t) * Sβ.eval (γ t))
      / (Sα.eval (γ t) * Rβ.eval (γ t))) atTop
      (nhds (Rα.eval 0 * Sβ.eval 0 / (Sα.eval 0 * Rβ.eval 0))) := by
    refine Tendsto.div ((eval_tendsto hγ Rα).mul (eval_tendsto hγ Sβ))
      ((eval_tendsto hγ Sα).mul (eval_tendsto hγ Rβ)) ?_
    exact mul_ne_zero hSα hRβ
  simpa using hlim

/-- **Strictly larger valuation: the ratio tends to zero.** -/
theorem ratio_tendsto_zero (hγ : Tendsto γ atTop (nhdsWithin 0 {(0 : ℂ)}ᶜ))
    (Rα Sα Rβ Sβ : Polynomial ℂ) (uα vα uβ vβ k : ℕ)
    (hSα : Sα.eval 0 ≠ 0) (hRβ : Rβ.eval 0 ≠ 0) (hexp : uα + vβ = uβ + vα + k) (hk : k ≠ 0) :
    Tendsto (fun t => ((γ t) ^ uα * Rα.eval (γ t)) / ((γ t) ^ vα * Sα.eval (γ t))
        / (((γ t) ^ uβ * Rβ.eval (γ t)) / ((γ t) ^ vβ * Sβ.eval (γ t))))
      atTop (nhds 0) := by
  have hform := ratio_eventuallyEq hγ Rα Sα Rβ Sβ uα vα uβ vβ k hexp
  refine Tendsto.congr' hform.symm ?_
  have hγ' : Tendsto γ atTop (nhds (0 : ℂ)) := hγ.mono_right nhdsWithin_le_nhds
  have hpow : Tendsto (fun t => (γ t) ^ k) atTop (nhds 0) := by
    have := hγ'.pow k
    rwa [zero_pow hk] at this
  have hlim : Tendsto (fun t => (Rα.eval (γ t) * Sβ.eval (γ t))
      / (Sα.eval (γ t) * Rβ.eval (γ t))) atTop
      (nhds (Rα.eval 0 * Sβ.eval 0 / (Sα.eval 0 * Rβ.eval 0))) := by
    refine Tendsto.div ((eval_tendsto hγ Rα).mul (eval_tendsto hγ Sβ))
      ((eval_tendsto hγ Sα).mul (eval_tendsto hγ Rβ)) ?_
    exact mul_ne_zero hSα hRβ
  simpa using hpow.mul hlim

end GaloisForLFunctions
