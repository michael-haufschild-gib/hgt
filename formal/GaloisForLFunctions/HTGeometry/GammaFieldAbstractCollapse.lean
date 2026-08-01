import GaloisForLFunctions.HTGeometry.GammaFieldFinitePhaseRank
import GaloisForLFunctions.HTGeometry.GammaFieldSumBoundary

/-!
# The collapse from abstract coefficient data

The collapse needs only two facts about the coefficients: their normalized ratios converge along the
line, and the normalizing coefficient is eventually nonzero.  Stated that way it applies to any
coefficient family with a projective boundary — single Gamma-field monomials, finite sums of them, or
anything else with the same two properties.

From those two hypotheses the constant-coefficient relation holds at every point of the line, hence on
the whole strip, and the descent turns it into finiteness of the rational Bohr frequency rank.  The
finite-sum case is recorded as the instance that covers all of `ℂ(s)[Γ, ψ]` in monomial expansion.
-/

open Filter Topology Complex Polynomial

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- **The collapse from abstract coefficient data.**  Whenever the normalized coefficients converge
along the line and the normalizing coefficient is eventually nonzero, the collapsed relation holds at
every point of the line. -/
theorem line_relation_of_coeff_limits {n N m : ℕ} {Φ : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip (1 / 2 + m) R))
    (hap : IsStripAlmostPeriodic Φ (1 / 2 + m) R)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ) (d : Fin N → ℂ) (β : Fin N)
    (hcoeff : ∀ α, Tendsto (fun t : ℝ =>
      F α (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        / F β (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds (d α)))
    (hFβ : ∀ᶠ t : ℝ in atTop, F β (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0)
    (t₀ : ℝ) :
    jetPoly d e
      (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ
        (((1 / 2 + m : ℝ) : ℂ) + (t₀ : ℂ) * Complex.I)) = 0 := by
  classical
  set s₀ : ℂ := ((1 / 2 + m : ℝ) : ℂ) + ((t₀ : ℝ) : ℂ) * Complex.I with hs₀
  set M : Fin N → ℂ → ℂ := fun α s => ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i)
    with hM
  have hjet : ∀ α : Fin N,
      Continuous (fun t : ℝ => M α (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)) ∧
      IsBohrAlmostPeriodic (fun t : ℝ => M α (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)) :=
    fun α => isBohrAlmostPeriodic_jetMonomial hR hΦ hap (e α)
  have hshift : Tendsto (fun t : ℝ => t + t₀) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have hfun : ∀ (g : ℂ → ℂ) (t : ℝ), g (s₀ + (t : ℂ) * Complex.I)
      = g (((1 / 2 + m : ℝ) : ℂ) + ((t + t₀ : ℝ) : ℂ) * Complex.I) := by
    intro g t
    rw [hs₀, line_shift]
  have hMcont : ∀ α : Fin N, Continuous fun t : ℝ => M α (s₀ + (t : ℂ) * Complex.I) := by
    intro α
    have hc := (hjet α).1
    have : (fun t : ℝ => M α (s₀ + (t : ℂ) * Complex.I))
        = fun t : ℝ => (fun u : ℝ => M α (((1 / 2 + m : ℝ) : ℂ) + (u : ℂ) * Complex.I)) (t + t₀) := by
      funext t
      exact hfun _ t
    rw [this]
    exact hc.comp (continuous_id.add continuous_const)
  have hMap : ∀ α : Fin N,
      IsBohrAlmostPeriodic fun t : ℝ => M α (s₀ + (t : ℂ) * Complex.I) := by
    intro α
    have ha := (hjet α).2
    have : (fun t : ℝ => M α (s₀ + (t : ℂ) * Complex.I))
        = fun t : ℝ => (fun u : ℝ => M α (((1 / 2 + m : ℝ) : ℂ) + (u : ℂ) * Complex.I)) (t + t₀) := by
      funext t
      exact hfun _ t
    rw [this]
    exact isBohrAlmostPeriodic_comp_add_const ha t₀
  have hcoeff' : ∀ α : Fin N, Tendsto (fun t : ℝ =>
      F α (s₀ + (t : ℂ) * Complex.I) / F β (s₀ + (t : ℂ) * Complex.I)) atTop (nhds (d α)) := by
    intro α
    have h := (hcoeff α).comp hshift
    refine h.congr fun t => ?_
    simp only [Function.comp_apply]
    rw [hfun (F α) t, hfun (F β) t]
  have hFβ' : ∀ᶠ t : ℝ in atTop, F β (s₀ + (t : ℂ) * Complex.I) ≠ 0 := by
    filter_upwards [hshift.eventually hFβ] with t ht
    rw [hfun (F β) t]
    exact ht
  have hcollapse := recurrence_collapse_of_bohr_return F M β s₀ d hrel hMcont hMap hFβ' hcoeff'
  have hval := hcollapse.1
  simpa [jetPoly, hM, hs₀] using hval

/-- **Eq. (8) from abstract coefficient data.** -/
theorem strip_relation_of_coeff_limits {n N m : ℕ} {Φ : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip (1 / 2 + m) R))
    (hap : IsStripAlmostPeriodic Φ (1 / 2 + m) R)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ) (d : Fin N → ℂ) (β : Fin N)
    (hcoeff : ∀ α, Tendsto (fun t : ℝ =>
      F α (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        / F β (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds (d α)))
    (hFβ : ∀ᶠ t : ℝ in atTop, F β (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0)
    {z : ℂ} (hz : z ∈ verticalStrip (1 / 2 + m) R) :
    jetPoly d e (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ z) = 0 :=
  jetPoly_eqOn_zero_of_line hR hΦ d e
    (fun t => line_relation_of_coeff_limits hR hΦ hap e F d β hcoeff hFβ hrel t) hz

/-- **Eq. (9) from abstract coefficient data.** -/
theorem rank_finite_of_coeff_limits {n N m : ℕ} {Φ : ℂ → ℂ} {R r ρ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R) (hR : 0 < R)
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip (1 / 2 + m) R))
    (hap : IsStripAlmostPeriodic Φ (1 / 2 + m) R)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ) (d : Fin N → ℂ) (β : Fin N)
    (hcoeff : ∀ α, Tendsto (fun t : ℝ =>
      F α (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        / F β (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds (d α)))
    (hFβ : ∀ᶠ t : ℝ in atTop, F β (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0)
    (he : Function.Injective e) (hdβ : d β ≠ 0)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ (((1 / 2 + m : ℝ) : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)] :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  refine rank_finite_of_polynomial_relation hr hρ hrρ hΦ hap hf hfu hftb n _
    (monomialSum_ne_zero d e he β hdβ) ?_
  intro z hz
  rw [← jetPoly_eq_mvEval]
  exact strip_relation_of_coeff_limits hR hΦ hap e F d β hcoeff hFβ hrel hz

/-- **Eq. (9) for coefficients that are finite sums of Gamma-field monomials.**  Every monomial of
every coefficient is dominated by one fixed monomial, and the normalizing coefficient has nonzero
limit constant; then a strip almost periodic holomorphic solution with distinct jet monomials has
finite rational Bohr frequency rank. -/
theorem rank_finite_of_gammaFieldSum_relation {n N k m : ℕ} {Φ : ℂ → ℂ} {R r ρ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R) (hR : 0 < R)
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip (1 / 2 + m) R))
    (hap : IsStripAlmostPeriodic Φ (1 / 2 + m) R)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ)
    (j : Fin N → Fin k → ℕ) (p q : Fin N → Fin k → Polynomial ℂ) (D : Fin N → Fin k → ℕ)
    (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hq : ∀ a i, q a i ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : ∀ a i, GammaMonomialDominates (j a i) (p a i) (q a i) (D a i) jb pb qb Db)
    (β : Fin N)
    (hc : (∑ i, gammaMonomialLimit (j β i) (p β i) (q β i) (D β i) jb pb qb Db) ≠ 0)
    (hF : ∀ (α : Fin N) (t : ℝ),
      F α (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        = ∑ i, gammaFieldElt m (j α i) (p α i) (q α i) (D α i) t)
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0)
    (he : Function.Injective e)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ (((1 / 2 + m : ℝ) : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)] :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  classical
  set d : Fin N → ℂ := fun α =>
    (∑ i, gammaMonomialLimit (j α i) (p α i) (q α i) (D α i) jb pb qb Db)
      / ∑ i, gammaMonomialLimit (j β i) (p β i) (q β i) (D β i) jb pb qb Db with hd
  have hcoeff : ∀ α : Fin N, Tendsto (fun t : ℝ =>
      F α (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        / F β (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds (d α)) := by
    intro α
    have h := tendsto_ratio_gammaFieldSum m j p q D jb pb qb Db hq hqb hpb hdom β hc α
    refine h.congr fun t => ?_
    rw [hF α t, hF β t]
  have hFβ : ∀ᶠ t : ℝ in atTop,
      F β (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    filter_upwards [eventually_sum_gammaFieldElt_ne_zero m (j β) (p β) (q β) (D β) jb pb qb Db
      (fun i => hq β i) hpb hqb (fun i => hdom β i) hc] with t ht
    rw [hF β t]
    exact ht
  have hdβ : d β ≠ 0 := by
    rw [hd]
    simp only
    rw [div_self hc]
    exact one_ne_zero
  exact rank_finite_of_coeff_limits hr hρ hrρ hR hΦ hap e F d β hcoeff hFβ hrel he hdβ hf hfu hftb

end GaloisForLFunctions
