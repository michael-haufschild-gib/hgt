/-
The certificate, activated: at every strip point of odd ξ-order the banked
Euler–Maclaurin annulus supply produces — unconditionally — an isolating
annulus, a truncation length, and an interior circle on which the completed EM
carrier dominates ξ; the periodic-mass stack then fires with no hypothesis
left: the carrier's root trace exists at that circle, EVERY such trace flips,
and every finitely-periodic probe is annihilated — the carrier's periodic mass
is zero.  The same activation runs at the reflected point across the critical
line, whose ξ-order agrees by the functional-equation and reality pairings: the
zero-mass circles come in mirror pairs, each with its own unconditional
certificate.

The negation of the base rung thereby produces, with no analytic interface
remaining, a concrete finite-object event: an explicit truncation of the
Euler–Maclaurin carrier whose square-root trace around an explicit circle is
orthogonal to every periodic voice.
-/
import GaloisForLFunctions.RHTower.MirrorTransport
import GaloisForLFunctions.RHTower.EMAnnulusSupply

noncomputable section

namespace RHTower

open Complex Metric Set

/-- **The activated certificate**: at any strip point of odd ξ-order there
exist an isolating annulus, an interior circle, and a truncation length such
that the completed EM carrier is nonvanishing on the annulus, carries a
continuous square-root trace along the circle, and EVERY such trace flips and
annihilates every finitely-periodic probe — the carrier's periodic mass at
that circle is zero, unconditionally. -/
theorem carrier_mass_zero_at_odd_xi_order {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    {m : ℕ} (hm : analyticOrderAt xi ρ = m) (hodd : Odd m) :
    ∃ (r₀ r R : ℝ) (N : ℕ), 0 < r₀ ∧ r₀ < r ∧ r < R ∧ 1 ≤ N ∧
      (∀ z ∈ ball ρ R \ closedBall ρ r₀, completedEM N z ≠ 0) ∧
      (∃ V : ℝ → ℂ,
        ContinuousOn V (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) ∧
        ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
          V θ ^ (2 : ℕ) = completedEM N (circleMap ρ r θ)) ∧
      ∀ V : ℝ → ℂ,
        ContinuousOn V (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) →
        (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
          V θ ^ (2 : ℕ) = completedEM N (circleMap ρ r θ)) →
        V (3 * Real.pi / 2) = -V (-(Real.pi / 2)) ∧
        ∀ p : ℝ → ℂ,
          ContinuousOn p
            (Icc (-(Real.pi / 2)) (3 * Real.pi / 2 + 2 * Real.pi)) →
          (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
            p (θ + 2 * Real.pi) = p θ) →
          ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2 + 2 * Real.pi),
            doubledTrace (-1) V θ * p θ = 0 := by
  obtain ⟨r₀, R, N, hr₀, hrR, hN1, hstrip, hiso, hdom⟩ :=
    exists_isolating_em_domination ρ h0 h1
  have hr₀r : r₀ < (r₀ + R) / 2 := by linarith
  have hrR' : (r₀ + R) / 2 < R := by linarith
  have hdom' : ∀ z ∈ ball ρ R \ closedBall ρ r₀,
      ‖xi z - completedEM N z‖ < ‖completedEM N z‖ := by
    intro z hz
    apply hdom
    rw [charts_union_eq_annulus ρ (le_of_lt hr₀)]
    exact hz
  have hF0 : ∀ z ∈ ball ρ R \ closedBall ρ r₀, completedEM N z ≠ 0 := by
    intro z hz hzero
    have h := hdom' z hz
    rw [hzero, sub_zero, norm_zero] at h
    exact absurd h (not_lt.mpr (norm_nonneg _))
  have hFan : AnalyticOnNhd ℂ (completedEM N)
      (ball ρ R \ closedBall ρ r₀) := fun z hz =>
    completedEM_analyticOnNhd_strip hN1 z (hstrip z hz.1)
  have hdomcircle : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      ‖xi (circleMap ρ ((r₀ + R) / 2) θ)
          - completedEM N (circleMap ρ ((r₀ + R) / 2) θ)‖
        < ‖completedEM N (circleMap ρ ((r₀ + R) / 2) θ)‖ := fun θ _ =>
    hdom' _ (circleMap_mem_annulus (le_of_lt hr₀) hr₀r hrR' θ)
  refine ⟨r₀, (r₀ + R) / 2, R, N, hr₀, hr₀r, hrR', hN1, hF0,
    exists_circle_trace hr₀ hr₀r hrR' hFan hF0, ?_⟩
  intro V hVc hVsq
  exact carrier_mass_zero_of_odd_isolated_zero hr₀ hr₀r hrR'
    (xi_analyticOnNhd _) hiso hm hodd hFan hF0 hdomcircle hVc hVsq

/-- The ξ-order at the reflected point across the critical line agrees with the
order at the point: the functional-equation and reality pairings compose. -/
theorem xi_orderAt_lineReflection (ρ : ℂ) :
    analyticOrderAt xi (lineReflection (1 / 2) ρ) = analyticOrderAt xi ρ := by
  rw [lineReflection_half, xi_orderAt_one_sub, xi_orderAt_conj]

/-- **The mirror pair, both activated**: at any strip point of odd ξ-order, the
zero-mass event fires at the point AND at its reflection across the critical
line, each with its own unconditional certificate — annulus, circle, truncation
length, existing trace, universal flip, universal probe annihilation. -/
theorem carrier_mass_zero_mirror_pair_at_odd_xi_order {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    {m : ℕ} (hm : analyticOrderAt xi ρ = m) (hodd : Odd m) :
    (∃ (r₀ r R : ℝ) (N : ℕ), 0 < r₀ ∧ r₀ < r ∧ r < R ∧ 1 ≤ N ∧
      (∀ z ∈ ball ρ R \ closedBall ρ r₀, completedEM N z ≠ 0) ∧
      (∃ V : ℝ → ℂ,
        ContinuousOn V (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) ∧
        ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
          V θ ^ (2 : ℕ) = completedEM N (circleMap ρ r θ)) ∧
      ∀ V : ℝ → ℂ,
        ContinuousOn V (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) →
        (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
          V θ ^ (2 : ℕ) = completedEM N (circleMap ρ r θ)) →
        V (3 * Real.pi / 2) = -V (-(Real.pi / 2)) ∧
        ∀ p : ℝ → ℂ,
          ContinuousOn p
            (Icc (-(Real.pi / 2)) (3 * Real.pi / 2 + 2 * Real.pi)) →
          (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
            p (θ + 2 * Real.pi) = p θ) →
          ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2 + 2 * Real.pi),
            doubledTrace (-1) V θ * p θ = 0) ∧
    (∃ (r₀ r R : ℝ) (N : ℕ), 0 < r₀ ∧ r₀ < r ∧ r < R ∧ 1 ≤ N ∧
      (∀ z ∈ ball (lineReflection (1 / 2) ρ) R
          \ closedBall (lineReflection (1 / 2) ρ) r₀,
        completedEM N z ≠ 0) ∧
      (∃ V : ℝ → ℂ,
        ContinuousOn V (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) ∧
        ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
          V θ ^ (2 : ℕ) = completedEM N
            (circleMap (lineReflection (1 / 2) ρ) r θ)) ∧
      ∀ V : ℝ → ℂ,
        ContinuousOn V (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) →
        (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
          V θ ^ (2 : ℕ) = completedEM N
            (circleMap (lineReflection (1 / 2) ρ) r θ)) →
        V (3 * Real.pi / 2) = -V (-(Real.pi / 2)) ∧
        ∀ p : ℝ → ℂ,
          ContinuousOn p
            (Icc (-(Real.pi / 2)) (3 * Real.pi / 2 + 2 * Real.pi)) →
          (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
            p (θ + 2 * Real.pi) = p θ) →
          ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2 + 2 * Real.pi),
            doubledTrace (-1) V θ * p θ = 0) := by
  constructor
  · exact carrier_mass_zero_at_odd_xi_order h0 h1 hm hodd
  · have h0' : 0 < (lineReflection (1 / 2) ρ).re := by
      rw [lineReflection_re]
      norm_num
      linarith
    have h1' : (lineReflection (1 / 2) ρ).re < 1 := by
      rw [lineReflection_re]
      norm_num
      linarith
    have hm' : analyticOrderAt xi (lineReflection (1 / 2) ρ) = m := by
      rw [xi_orderAt_lineReflection]
      exact hm
    exact carrier_mass_zero_at_odd_xi_order h0' h1' hm' hodd

end RHTower
