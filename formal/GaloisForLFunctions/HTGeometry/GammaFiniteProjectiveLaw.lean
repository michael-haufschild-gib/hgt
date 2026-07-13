import GaloisForLFunctions.HTGeometry.GammaProjectiveBoundary

/-!
# The finite projective law: recurrence collapse and lowest-power domination

This file formalizes two further theorems of `gamma-projective-boundary-finite-phase-law.md` whose
deductive content is provable now, with the genuinely mathlib-absent analytic inputs (the one-point
projective boundary of the Gamma coefficient field and the Bohr return convergence) supplied as
explicit hypotheses rather than reproved from an unbuilt almost-periodic-hull theory.

* `polynomial_lowest_power_tendsto` / `..._ratio_tendsto` — the §4 mechanism behind the monomial
  valuation (eq. 3): when the transcendental Gamma element tends to `0`, the smallest Gamma power
  dominates a rational expression, and the residue is the ratio of leading `L`-coefficients.
* `recurrence_collapse_to_autonomous` — the §5 recurrence-to-autonomous step (eq. 27 → 29): a finite
  differential relation over the Gamma field, translated along Bohr return times and normalized by a
  projectively dominant coefficient, converges to a nontrivial constant-coefficient relation, so the
  recurrent solution satisfies an autonomous algebraic differential equation.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-- **Lowest-power domination (§4, algebraic core of eq. 3).**  If a polynomial factors as
`P = Xᵘ · R` with `R(0) ≠ 0`, then `P(g)/gᵘ → R(0)` as `g → 0` along the punctured neighbourhood.
This is the mechanism by which the smallest Gamma power dominates as `Γ → 0`. -/
theorem polynomial_lowest_power_tendsto (P R : Polynomial ℂ) (u : ℕ)
    (hPR : P = Polynomial.X ^ u * R) :
    Tendsto (fun g : ℂ => P.eval g / g ^ u) (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds (R.eval 0)) := by
  refine (((Polynomial.continuous R).tendsto 0).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with g hg
  have hg0 : g ≠ 0 := by simpa using hg
  rw [hPR]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  exact (mul_div_cancel_left₀ (R.eval g) (pow_ne_zero u hg0)).symm

/-- The projective ratio of two lowest-power normalizations converges to the ratio of leading
coefficients: `(P(g)/gᵘ)/(Q(g)/gᵛ) → R(0)/S(0)`.  This is the `L`-residue quotient of eq. (3), once
the exponential Gamma factor `Γ^{u−v}` is separated out. -/
theorem polynomial_lowest_power_ratio_tendsto (P Q R S : Polynomial ℂ) (u v : ℕ)
    (hP : P = Polynomial.X ^ u * R) (hQ : Q = Polynomial.X ^ v * S) (hS0 : S.eval 0 ≠ 0) :
    Tendsto (fun g : ℂ => (P.eval g / g ^ u) / (Q.eval g / g ^ v))
      (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds (R.eval 0 / S.eval 0)) :=
  (polynomial_lowest_power_tendsto P R u hP).div
    (polynomial_lowest_power_tendsto Q S v hQ) hS0

/-- **Recurrence collapse to an autonomous relation (§5, eq. 27 → 29).**  Suppose `f` satisfies a
finite differential relation `∑_{α∈E} F_α · M_α = 0` with coefficients `F_α` in the Gamma field and
differential monomials `M_α = ∏ⱼ (f⁽ʲ⁾)^{α_j}`.  Given return times `T_l → ∞` along which the
coefficient tuple has the one-point projective boundary (`F_α/F_β → d_α`, eq. 5) and each monomial
returns (`M_α(s₀+iT_l) → M_α(s₀)`, Bohr almost periodicity), the limiting relation
`∑_α d_α · M_α(s₀) = 0` holds with a nonzero constant coefficient vector (`d_β = 1`).  Thus `f`
satisfies a nontrivial autonomous algebraic differential relation. -/
theorem recurrence_collapse_to_autonomous {ι : Type*} (E : Finset ι)
    (F M : ι → ℂ → ℂ) (β : ι) (hβ : β ∈ E) (s₀ : ℂ) (T : ℕ → ℝ) (d : ι → ℂ)
    (hrel : ∀ s : ℂ, ∑ α ∈ E, F α s * M α s = 0)
    (hFβ : ∀ l : ℕ, F β (s₀ + (T l : ℂ) * Complex.I) ≠ 0)
    (hcoeff : ∀ α ∈ E, Tendsto
      (fun l => F α (s₀ + (T l : ℂ) * Complex.I) / F β (s₀ + (T l : ℂ) * Complex.I))
      atTop (nhds (d α)))
    (hmon : ∀ α ∈ E, Tendsto
      (fun l => M α (s₀ + (T l : ℂ) * Complex.I)) atTop (nhds (M α s₀))) :
    (∑ α ∈ E, d α * M α s₀ = 0) ∧ d β = 1 := by
  refine ⟨?_, ?_⟩
  · apply finiteProjectiveRelationCollapse E
      (fun l α => F α (s₀ + (T l : ℂ) * Complex.I) / F β (s₀ + (T l : ℂ) * Complex.I))
      (fun l α => M α (s₀ + (T l : ℂ) * Complex.I)) d (fun α => M α s₀) hcoeff hmon
    intro l
    have h := hrel (s₀ + (T l : ℂ) * Complex.I)
    have hsum :
        ∑ α ∈ E, F α (s₀ + (T l : ℂ) * Complex.I) / F β (s₀ + (T l : ℂ) * Complex.I)
            * M α (s₀ + (T l : ℂ) * Complex.I)
          = (∑ α ∈ E, F α (s₀ + (T l : ℂ) * Complex.I) * M α (s₀ + (T l : ℂ) * Complex.I))
            / F β (s₀ + (T l : ℂ) * Complex.I) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun α _ => by ring)
    rw [hsum, h, zero_div]
  · have hlim := hcoeff β hβ
    have h1 : (fun l => F β (s₀ + (T l : ℂ) * Complex.I) / F β (s₀ + (T l : ℂ) * Complex.I))
        = fun _ => (1 : ℂ) := by funext l; exact div_self (hFβ l)
    rw [h1] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- **Monomial-valuation residue on a vertical line (eq. 3, projective form).**  Composing the
lowest-power ratio with the exponential Gamma decay `Γ(σ+it) → 0` (and `Γ ≠ 0`), a Gamma-field
element `F = P(Γ)/Q(Γ)` normalized by its dominant Gamma powers converges to the `L`-residue
`R(0)/S(0)` as `Im s → +∞`.  The Gamma decay along the line is the single analytic input; it is the
`Γ(s) → 0` step of §4. -/
theorem gamma_monomial_valuation_residue (P Q R S : Polynomial ℂ) (u v : ℕ) (σ : ℝ)
    (hP : P = Polynomial.X ^ u * R) (hQ : Q = Polynomial.X ^ v * S) (hS0 : S.eval 0 ≠ 0)
    (hΓ0 : Tendsto (fun t : ℝ => Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhdsWithin 0 {(0 : ℂ)}ᶜ)) :
    Tendsto (fun t : ℝ =>
        (P.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))
            / (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ u)
          / (Q.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))
            / (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ v))
      atTop (nhds (R.eval 0 / S.eval 0)) :=
  (polynomial_lowest_power_ratio_tendsto P Q R S u v hP hQ hS0).comp hΓ0

end

end GaloisForLFunctions
