import GaloisForLFunctions.HTGeometry.DigammaFieldRatio

/-!
# The valuation of a quotient in the digamma field

An element of `ℂ(s)⟨ψ⟩` is a quotient of two expressions `R(s)·P(ψ, ψ′, …)`.  Each of them has, on a
vertical line, the asymptotic `c · s^{a} · L(t)^{b}` of eq. (19), where `L(t) = log t + iπ/2`.  When
the denominator's leading datum is nonzero the two asymptotics divide, so the quotient itself has the
asymptotic with data `(a₁ − a₂, b₁ − b₂)` and leading constant `c₁ / c₂`.

This carries eq. (19) from the ring `ℂ(s)[ψ, ψ′, …]` to the field it generates.
-/

open Filter Topology Complex Polynomial

namespace GaloisForLFunctions

variable {n N N₁ N₂ : ℕ}

/-- The value on a vertical line of the element `p(s)·P(ψ, ψ′, …) / q(s)` of `ℂ(s)⟨ψ⟩`. -/
noncomputable def digammaFieldElt (σ : ℝ) (p q : Polynomial ℂ) (d : Fin N → ℂ)
    (e : Fin N → Fin (n + 1) → ℕ) (t : ℝ) : ℂ :=
  (p.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
      * jetPoly d e (fun j : Fin (n + 1) => digammaJetLine σ (j : ℕ) t))
    / q.eval ((σ : ℂ) + (t : ℂ) * Complex.I)

/-- The normalization of `digammaFieldElt` by its own valuation datum `(deg p − deg q, D)`. -/
noncomputable def digammaFieldNorm (σ : ℝ) (p q : Polynomial ℂ) (d : Fin N → ℂ)
    (e : Fin N → Fin (n + 1) → ℕ) (D : ℕ) (t : ℝ) : ℂ :=
  (p.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
      * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ q.natDegree
      * jetPoly d e (fun j : Fin (n + 1) => digammaJetLine σ (j : ℕ) t))
    / (q.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p.natDegree * (vertLog t) ^ D)

/-- **Eq. (19) in normalized form.**  The normalized value of an element of `ℂ(s)⟨ψ⟩` converges to
the product of the leading coefficient ratio of its rational part with the coefficient of the pure
digamma monomial. -/
theorem tendsto_digammaFieldNorm {σ : ℝ} (hσ : 0 < σ)
    (p q : Polynomial ℂ) (hq : q ≠ 0) (d : Fin N → ℂ) (e : Fin N → Fin (n + 1) → ℕ)
    (D : ℕ) (β : Fin N) (hβpure : ∀ j : Fin n, e β j.succ = 0) (hβdeg : e β 0 = D)
    (hle : ∀ α, e α 0 ≤ D)
    (hother : ∀ α, α ≠ β → e α 0 < D ∨ ∃ j : Fin n, e α j.succ ≠ 0) :
    Tendsto (digammaFieldNorm σ p q d e D) atTop
      (nhds (p.leadingCoeff / q.leadingCoeff * d β)) :=
  tendsto_ratCoeff_jetPoly_vertical hσ p q hq d e D β hβpure hβdeg hle hother

/-- **Eq. (19) for the digamma field.**  The quotient of two elements of `ℂ(s)⟨ψ⟩`, normalized by the
difference of their valuation data, converges to the quotient of their leading constants, provided
the denominator's leading constant is nonzero. -/
theorem tendsto_ratio_digammaField_quotient {σ : ℝ} (hσ : 0 < σ)
    (p₁ q₁ p₂ q₂ : Polynomial ℂ) (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0)
    (d₁ : Fin N₁ → ℂ) (e₁ : Fin N₁ → Fin (n + 1) → ℕ) (D₁ : ℕ) (β₁ : Fin N₁)
    (hβ₁pure : ∀ j : Fin n, e₁ β₁ j.succ = 0) (hβ₁deg : e₁ β₁ 0 = D₁)
    (hle₁ : ∀ α, e₁ α 0 ≤ D₁)
    (hother₁ : ∀ α, α ≠ β₁ → e₁ α 0 < D₁ ∨ ∃ j : Fin n, e₁ α j.succ ≠ 0)
    (d₂ : Fin N₂ → ℂ) (e₂ : Fin N₂ → Fin (n + 1) → ℕ) (D₂ : ℕ) (β₂ : Fin N₂)
    (hβ₂pure : ∀ j : Fin n, e₂ β₂ j.succ = 0) (hβ₂deg : e₂ β₂ 0 = D₂)
    (hle₂ : ∀ α, e₂ α 0 ≤ D₂)
    (hother₂ : ∀ α, α ≠ β₂ → e₂ α 0 < D₂ ∨ ∃ j : Fin n, e₂ α j.succ ≠ 0)
    (hne : p₂.leadingCoeff / q₂.leadingCoeff * d₂ β₂ ≠ 0) :
    Tendsto (fun t : ℝ =>
        digammaFieldElt σ p₁ q₁ d₁ e₁ t / digammaFieldElt σ p₂ q₂ d₂ e₂ t
          * ((((σ : ℂ) + (t : ℂ) * Complex.I) ^ q₁.natDegree
                * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p₂.natDegree * (vertLog t) ^ D₂)
              / (((σ : ℂ) + (t : ℂ) * Complex.I) ^ p₁.natDegree
                * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ q₂.natDegree * (vertLog t) ^ D₁)))
      atTop (nhds ((p₁.leadingCoeff / q₁.leadingCoeff * d₁ β₁)
        / (p₂.leadingCoeff / q₂.leadingCoeff * d₂ β₂))) := by
  have h₁ := tendsto_digammaFieldNorm hσ p₁ q₁ hq₁ d₁ e₁ D₁ β₁ hβ₁pure hβ₁deg hle₁ hother₁
  have h₂ := tendsto_digammaFieldNorm hσ p₂ q₂ hq₂ d₂ e₂ D₂ β₂ hβ₂pure hβ₂deg hle₂ hother₂
  refine (h₁.div h₂ hne).congr' ?_
  filter_upwards [eventually_vertical_ne_zero σ, eventually_vertLog_ne_zero,
    eventually_eval_ne_zero σ hq₁, eventually_eval_ne_zero σ hq₂,
    h₂.eventually_ne hne] with t hs hL hQ₁ hQ₂ hE₂
  have hnum₂ : p₂.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
      * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ q₂.natDegree
      * jetPoly d₂ e₂ (fun j : Fin (n + 1) => digammaJetLine σ (j : ℕ) t) ≠ 0 := by
    intro h
    apply hE₂
    rw [digammaFieldNorm, h, zero_div]
  have hp₂ : p₂.eval ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    apply hnum₂
    rw [h]
    ring
  have hj₂ : jetPoly d₂ e₂ (fun j : Fin (n + 1) => digammaJetLine σ (j : ℕ) t) ≠ 0 := by
    intro h
    apply hnum₂
    rw [h]
    ring
  have hsp₁ : ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p₁.natDegree ≠ 0 := pow_ne_zero _ hs
  have hsq₂ : ((σ : ℂ) + (t : ℂ) * Complex.I) ^ q₂.natDegree ≠ 0 := pow_ne_zero _ hs
  have hL₁ : (vertLog t) ^ D₁ ≠ 0 := pow_ne_zero _ hL
  simp only [Pi.div_apply, digammaFieldElt, digammaFieldNorm]
  field_simp

end GaloisForLFunctions
