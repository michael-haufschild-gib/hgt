import GaloisForLFunctions.HTGeometry.GammaFieldRecurrenceCollapse
import GaloisForLFunctions.HTGeometry.JetMonomialAlmostPeriodic
import GaloisForLFunctions.HTGeometry.JetPolynomialDescent
import GaloisForLFunctions.HTGeometry.BohrMeanInvariance
import GaloisForLFunctions.HTGeometry.PolynomialRelationPhaseRank

/-!
# The finite-phase law over the Gamma field

The collapse can be run from every point of the vertical line: the coefficient ratios have the same
limit along the line whatever the starting height, the jet monomials stay almost periodic under
translation, and the normalizing coefficient stays eventually nonzero.  So the constant-coefficient
relation holds at every point of the line, hence — both sides being holomorphic — on the whole strip.

That relation is a nonzero polynomial in the jets whenever the monomials are distinct, so the descent
applies and the rational Bohr frequency rank of the line restriction is finite.  This is eq. (8) and
eq. (9) with the coefficients taken from the full field `ℂ(s)⟨Γ⟩` rather than its rational subfield.
-/

open Filter Topology Complex Polynomial

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- The point of the line at height `t₀ + t`. -/
theorem line_shift (m : ℕ) (t₀ t : ℝ) :
    ((1 / 2 + m : ℝ) : ℂ) + ((t₀ : ℝ) : ℂ) * Complex.I + (t : ℂ) * Complex.I
      = ((1 / 2 + m : ℝ) : ℂ) + ((t + t₀ : ℝ) : ℂ) * Complex.I := by
  push_cast
  ring

/-- **Eq. (8) over the Gamma field, on the line.**  Running the collapse from every point of the line
gives the constant-coefficient relation at every point of the line. -/
theorem gammaField_line_relation {n N m : ℕ} {Φ : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip (1 / 2 + m) R))
    (hap : IsStripAlmostPeriodic Φ (1 / 2 + m) R)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ)
    (j : Fin N → ℕ) (p q : Fin N → Polynomial ℂ) (D : Fin N → ℕ) (β : Fin N)
    (hp : ∀ α, p α ≠ 0) (hq : ∀ α, q α ≠ 0)
    (hF : ∀ (α : Fin N) (t : ℝ),
      F α (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        = gammaFieldElt m (j α) (p α) (q α) (D α) t)
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0)
    (hlex : ∀ α, j β < j α ∨ (j α = j β ∧
      ((p α * q β).natDegree < (q α * p β).natDegree ∨
        ((p α * q β).natDegree = (q α * p β).natDegree ∧ D α ≤ D β))))
    (t₀ : ℝ) :
    jetPoly (gammaFieldLimit j p q D β) e
      (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ
        (((1 / 2 + m : ℝ) : ℂ) + (t₀ : ℂ) * Complex.I)) = 0 := by
  classical
  set s₀ : ℂ := ((1 / 2 + m : ℝ) : ℂ) + ((t₀ : ℝ) : ℂ) * Complex.I with hs₀
  set M : Fin N → ℂ → ℂ := fun α s => ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i)
    with hM
  -- the jet monomials are continuous and almost periodic along the line
  have hjet : ∀ α : Fin N,
      Continuous (fun t : ℝ => M α (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)) ∧
      IsBohrAlmostPeriodic (fun t : ℝ => M α (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)) :=
    fun α => isBohrAlmostPeriodic_jetMonomial hR hΦ hap (e α)
  have hMcont : ∀ α : Fin N, Continuous fun t : ℝ => M α (s₀ + (t : ℂ) * Complex.I) := by
    intro α
    have hc := (hjet α).1
    have hfun : (fun t : ℝ => M α (s₀ + (t : ℂ) * Complex.I))
        = fun t : ℝ => (fun u : ℝ => M α (((1 / 2 + m : ℝ) : ℂ) + (u : ℂ) * Complex.I)) (t + t₀) := by
      funext t
      rw [hs₀, line_shift]
    rw [hfun]
    exact hc.comp (continuous_id.add continuous_const)
  have hMap : ∀ α : Fin N,
      IsBohrAlmostPeriodic fun t : ℝ => M α (s₀ + (t : ℂ) * Complex.I) := by
    intro α
    have ha := (hjet α).2
    have hfun : (fun t : ℝ => M α (s₀ + (t : ℂ) * Complex.I))
        = fun t : ℝ => (fun u : ℝ => M α (((1 / 2 + m : ℝ) : ℂ) + (u : ℂ) * Complex.I)) (t + t₀) := by
      funext t
      rw [hs₀, line_shift]
    rw [hfun]
    exact isBohrAlmostPeriodic_comp_add_const ha t₀
  -- the coefficient ratios converge along the shifted line
  have hshift : Tendsto (fun t : ℝ => t + t₀) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have hcoeff : ∀ α : Fin N, Tendsto (fun t : ℝ =>
      F α (s₀ + (t : ℂ) * Complex.I) / F β (s₀ + (t : ℂ) * Complex.I)) atTop
      (nhds (gammaFieldLimit j p q D β α)) := by
    intro α
    have hbase := (tendsto_ratio_gammaFieldElt_lex m (p α) (q α) (p β) (q β)
      (hq α) (hq β) (hp β) (ja := j α) (jb := j β) (Da := D α) (Db := D β) (hlex α)).comp hshift
    refine hbase.congr fun t => ?_
    simp only [Function.comp_apply]
    rw [hs₀, line_shift, hF α (t + t₀), hF β (t + t₀)]
  have hFβ : ∀ᶠ t : ℝ in atTop, F β (s₀ + (t : ℂ) * Complex.I) ≠ 0 := by
    have h := hshift.eventually (eventually_gammaFieldElt_ne_zero m (j β) (hp β) (hq β) (D β))
    filter_upwards [h] with t ht
    rw [hs₀, line_shift, hF β (t + t₀)]
    exact ht
  have hcollapse := recurrence_collapse_of_bohr_return F M β s₀
    (gammaFieldLimit j p q D β) hrel hMcont hMap hFβ hcoeff
  have hval := hcollapse.1
  simpa [jetPoly, hM, hs₀] using hval

theorem gammaFieldLimit_self {n : ℕ} (j : Fin n → ℕ) (p q : Fin n → Polynomial ℂ)
    (D : Fin n → ℕ) (β : Fin n) (hp : p β ≠ 0) (hq : q β ≠ 0) :
    gammaFieldLimit j p q D β β = 1 := by
  classical
  rw [gammaFieldLimit, if_pos ⟨rfl, by rw [mul_comm], rfl⟩, mul_comm (p β) (q β)]
  exact div_self (Polynomial.leadingCoeff_ne_zero.mpr (mul_ne_zero hq hp))

/-- **Eq. (8) over the Gamma field.**  The collapsed relation holds on the whole strip. -/
theorem gammaField_autonomous_relation {n N m : ℕ} {Φ : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip (1 / 2 + m) R))
    (hap : IsStripAlmostPeriodic Φ (1 / 2 + m) R)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ)
    (j : Fin N → ℕ) (p q : Fin N → Polynomial ℂ) (D : Fin N → ℕ) (β : Fin N)
    (hp : ∀ α, p α ≠ 0) (hq : ∀ α, q α ≠ 0)
    (hF : ∀ (α : Fin N) (t : ℝ),
      F α (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        = gammaFieldElt m (j α) (p α) (q α) (D α) t)
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0)
    (hlex : ∀ α, j β < j α ∨ (j α = j β ∧
      ((p α * q β).natDegree < (q α * p β).natDegree ∨
        ((p α * q β).natDegree = (q α * p β).natDegree ∧ D α ≤ D β))))
    {z : ℂ} (hz : z ∈ verticalStrip (1 / 2 + m) R) :
    jetPoly (gammaFieldLimit j p q D β) e
      (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ z) = 0 :=
  jetPoly_eqOn_zero_of_line hR hΦ _ e
    (fun t => gammaField_line_relation hR hΦ hap e F j p q D β hp hq hF hrel hlex t) hz

/-- **Eq. (9) over the Gamma field.**  A strip almost periodic holomorphic solution of a
differential relation with Gamma-field coefficients and distinct monomials has finite rational Bohr
frequency rank. -/
theorem rank_finite_of_gammaField_relation {n N m : ℕ} {Φ : ℂ → ℂ} {R r ρ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R) (hR : 0 < R)
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip (1 / 2 + m) R))
    (hap : IsStripAlmostPeriodic Φ (1 / 2 + m) R)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ)
    (j : Fin N → ℕ) (p q : Fin N → Polynomial ℂ) (D : Fin N → ℕ) (β : Fin N)
    (hp : ∀ α, p α ≠ 0) (hq : ∀ α, q α ≠ 0)
    (hF : ∀ (α : Fin N) (t : ℝ),
      F α (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        = gammaFieldElt m (j α) (p α) (q α) (D α) t)
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0)
    (hlex : ∀ α, j β < j α ∨ (j α = j β ∧
      ((p α * q β).natDegree < (q α * p β).natDegree ∨
        ((p α * q β).natDegree = (q α * p β).natDegree ∧ D α ≤ D β))))
    (he : Function.Injective e)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ (((1 / 2 + m : ℝ) : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)] :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  classical
  have hβ : gammaFieldLimit j p q D β β ≠ 0 := by
    rw [gammaFieldLimit_self j p q D β (hp β) (hq β)]
    exact one_ne_zero
  refine rank_finite_of_polynomial_relation hr hρ hrρ hΦ hap hf hfu hftb n _
    (monomialSum_ne_zero (gammaFieldLimit j p q D β) e he β hβ) ?_
  intro z hz
  rw [← jetPoly_eq_mvEval]
  exact gammaField_autonomous_relation hR hΦ hap e F j p q D β hp hq hF hrel hlex hz

end GaloisForLFunctions
