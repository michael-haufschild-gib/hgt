import GaloisForLFunctions.Bottcher.RelativeRigidityGlobalBranchEventual
import GaloisForLFunctions.Bottcher.ConnectedRepellingStrongRoots
import GaloisForLFunctions.Bottcher.InverseBranchPeriodic
import GaloisForLFunctions.Bottcher.CrossRatioSelectorBridge
import GaloisForLFunctions.Bottcher.NewtonPeriodic
import GaloisForLFunctions.Bottcher.NearReturnSelector

open Polynomial Filter Topology Set Metric

namespace Bottcher

variable {U : Set ℂ}

/-- Local strongly-repelling periodic witnesses imply density of the canonical nonresonant frontier
target set.  This packages the two dynamical upgrades needed by the nonresonant crossing endpoint:
strong orbit-product growth puts the periodic point on the frontier and implies derivative
nonresonance. -/
theorem dense_nonresonantPeriodic_of_forall_frontier_ball_strongly_repelling
    {c : ℂ}
    (hlocal : ∀ z ∈ frontier (filledJulia c), ∀ r : ℝ, 0 < r →
      ∃ y ∈ Metric.ball z r,
        ∃ q : ℕ,
          (quadratic c)^[q] y = y ∧
          (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] y‖) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} := by
  apply dense_nonresonantPeriodic_of_forall_frontier_ball
  intro z hzfront r hr
  obtain ⟨y, hyball, q, hper, hstrong⟩ := hlocal z hzfront r hr
  exact ⟨y, hyball,
    mem_frontier_of_strongly_repelling_periodic_orbitProduct hper hstrong, q, hper,
    deriv_nonresonant_of_strongly_repelling_periodic_orbitProduct hstrong⟩

/-- Exact periodic inverse-multiplier witnesses in every frontier ball imply density of the
canonical nonresonant frontier target set consumed by the q62 crossing endpoint. -/
theorem dense_nonresonantPeriodic_of_forall_frontier_ball_periodic_deriv_inv_norm_lt
    {c : ℂ}
    (hlocal : ∀ z ∈ frontier (filledJulia c), ∀ r : ℝ, 0 < r →
      ∃ y ∈ Metric.ball z r, ∃ q : ℕ,
        (quadratic c)^[q] y = y ∧
        deriv ((quadratic c)^[q]) y ≠ 0 ∧
        ‖(deriv ((quadratic c)^[q]) y)⁻¹‖ < ((2 ^ q : ℝ)⁻¹)) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} := by
  apply dense_nonresonantPeriodic_of_forall_frontier_ball_strongly_repelling
  intro z hzfront r hr
  obtain ⟨y, hyball, q, hper, hcrit, hinvnorm⟩ := hlocal z hzfront r hr
  exact ⟨y, hyball, q, hper, strong_orbitProduct_of_deriv_inv_norm_lt hcrit hinvnorm⟩

/-- Strongly-repelling periodic density implies density of the canonical nonresonant frontier
target set consumed by the q62 crossing endpoint. -/
theorem dense_nonresonantPeriodic_of_dense_strongly_repelling_periodic
    {c : ℂ}
    (hdense : frontier (filledJulia c) ⊆ closure
      {z : ℂ | ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] z‖}) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} := by
  intro z hz
  refine closure_mono ?_ (hdense hz)
  intro y hy
  obtain ⟨q, hper, hstrong⟩ := hy
  exact ⟨mem_frontier_of_strongly_repelling_periodic_orbitProduct hper hstrong,
    q, hper, deriv_nonresonant_of_strongly_repelling_periodic_orbitProduct hstrong⟩

/-- Periodic points avoiding every finite exceptional set, together with eventual finite
containment of all non-strong periodic roots, imply density of the canonical nonresonant frontier
target set. -/
theorem dense_nonresonantPeriodic_of_forall_frontier_ball_periodic_avoiding_eventually_nonStrong_subset
    {c : ℂ}
    (havoid : ∀ E : Finset ℂ, ∀ z ∈ frontier (filledJulia c), ∀ r : ℝ, 0 < r →
      ∃ y ∈ Metric.ball z r, ∃ q : ℕ,
        1 ≤ q ∧ (quadratic c)^[q] y = y ∧ y ∉ E)
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_dense_strongly_repelling_periodic
    (dense_strongly_repelling_periodic_of_forall_frontier_ball_periodic_avoiding_eventually_nonStrong_subset
      havoid hE)

/-- Perfect-frontier ordinary periodic density plus eventual finite containment of all non-strong
roots imply density of the canonical nonresonant frontier target set. -/
theorem dense_nonresonantPeriodic_of_perfect_frontier_forall_frontier_ball_periodic_eventually_nonStrong_subset
    {c : ℂ}
    (hfront : Perfect (frontier (filledJulia c)))
    (hperiodic : ∀ z ∈ frontier (filledJulia c), ∀ r : ℝ, 0 < r →
      ∃ y ∈ Metric.ball z r, ∃ q : ℕ,
        1 ≤ q ∧ (quadratic c)^[q] y = y)
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_dense_strongly_repelling_periodic
    (dense_strongly_repelling_periodic_of_perfect_frontier_forall_frontier_ball_periodic_eventually_nonStrong_subset
      hfront hperiodic hE)

/-- Connected empty-interior ordinary periodic density plus eventual finite containment of all
non-strong roots imply density of the canonical nonresonant frontier target set. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    {c : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hperiodic : ∀ z ∈ frontier (filledJulia c), ∀ r : ℝ, 0 < r →
      ∃ y ∈ Metric.ball z r, ∃ q : ℕ,
        1 ≤ q ∧ (quadratic c)^[q] y = y)
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_dense_strongly_repelling_periodic
    (dense_strongly_repelling_periodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
      hconn hempty hperiodic hE)

/-- Connected empty-interior q62 target density from the regular-hit off-ball selector lane.  The
remaining local task is exactly to convert regular positive-depth hits into positive periodic points;
the selector itself supplies positive depth and derivative nonvanishing by countable critical-orbit
avoidance. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_offBall_regular_hit_to_positive_periodic_half_eventually_nonStrong_subset
    {c : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hconvert : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
        ∃ T : Set ℂ,
          ¬ T.Countable ∧
          (∀ w ∈ T, w ∉ Metric.ball z₀ (R / 2)) ∧
          ∀ w ∈ T, ∀ n z,
            1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
            (quadratic c)^[n] z = w →
            deriv ((quadratic c)^[n]) z ≠ 0 →
            ∃ y ∈ Metric.ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y)
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_offBall_regular_hit_to_positive_periodic_half
      hconvert)
    hE

/-- Connected empty-interior q62 target density from regular off-ball selector hits plus the
local-inverse quantitative data needed by the IFT near-return splice. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_regular_hit_localInverse_half_eventually_nonStrong_subset
    {c : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hconvert : ∀ {ζ : ℂ} {ρ R : ℝ},
      ζ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
        ∃ T : Set ℂ,
          ¬ T.Countable ∧
          (∀ w ∈ T, w ∉ Metric.ball ζ (R / 2)) ∧
          ∀ w ∈ T, ∀ p z,
            1 ≤ p → z ∈ Metric.ball ζ (R / 2) →
            (quadratic c)^[p] z = w →
            deriv ((quadratic c)^[p]) z ≠ 0 →
            ∃ K : NNReal,
              K < 1 ∧
              ‖(deriv ((quadratic c)^[p]) z)⁻¹‖ < (K : ℝ) ∧
              (∀ (g : ℂ → ℂ) (r : ℝ), 0 < r →
                g ((quadratic c)^[p] z) = z →
                (∀ y ∈ Metric.closedBall ((quadratic c)^[p] z) r,
                  HasDerivAt g (deriv g y) y ∧ ‖deriv g y‖ ≤ (K : ℝ) ∧
                    (fun u => (quadratic c)^[p] (g u)) =ᶠ[𝓝 y] id) →
                dist z ((quadratic c)^[p] z) + (K : ℝ) * r ≤ r ∧
                  Metric.closedBall ((quadratic c)^[p] z) r ⊆ Metric.ball ζ R))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_regular_hit_localInverse_half hconvert)
    hE

/-- Concrete-target q62 density from regular off-ball selector hits plus local-inverse data.  The
selector target is fixed to `offBallRealSegment ζ R`, so the caller no longer supplies an auxiliary
uncountable off-ball target set. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_all_offBall_regular_hit_localInverse_half_eventually_nonStrong_subset
    {c : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hconvert : ∀ {ζ : ℂ} {ρ R : ℝ},
      ζ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
        ∀ w, w ∉ Metric.ball ζ (R / 2) →
          ∀ p z,
            1 ≤ p → z ∈ Metric.ball ζ (R / 2) →
            (quadratic c)^[p] z = w →
            deriv ((quadratic c)^[p]) z ≠ 0 →
            ∃ K : NNReal,
              K < 1 ∧
              ‖(deriv ((quadratic c)^[p]) z)⁻¹‖ < (K : ℝ) ∧
              (∀ (g : ℂ → ℂ) (r : ℝ), 0 < r →
                g ((quadratic c)^[p] z) = z →
                (∀ y ∈ Metric.closedBall ((quadratic c)^[p] z) r,
                  HasDerivAt g (deriv g y) y ∧ ‖deriv g y‖ ≤ (K : ℝ) ∧
                    (fun u => (quadratic c)^[p] (g u)) =ᶠ[𝓝 y] id) →
                dist z ((quadratic c)^[p] z) + (K : ℝ) * r ≤ r ∧
                  Metric.closedBall ((quadratic c)^[p] z) r ⊆ Metric.ball ζ R))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_all_offBall_regular_hit_localInverse_half hconvert)
    hE

/-- Connected empty-interior q62 target density from regular near-return selector hits plus
local-inverse quantitative data.  The selector now produces the approximate return internally:
`z ∈ ball ζ (R/4)` and `f^[p] z ∈ ball ζ (R/2)` with nonzero derivative. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_regular_near_return_localInverse_eventually_nonStrong_subset
    {c : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hconvert : ∀ {ζ : ℂ} {R : ℝ},
      ζ ∈ frontier (filledJulia c) → 0 < R →
      ∀ p z w,
        1 ≤ p → z ∈ Metric.ball ζ (R / 4) → w ∈ Metric.ball ζ (R / 2) →
        (quadratic c)^[p] z = w →
        deriv ((quadratic c)^[p]) z ≠ 0 →
        ∃ K : NNReal,
          K < 1 ∧
          ‖(deriv ((quadratic c)^[p]) z)⁻¹‖ < (K : ℝ) ∧
          (∀ (g : ℂ → ℂ) (r : ℝ), 0 < r →
            g ((quadratic c)^[p] z) = z →
            (∀ y ∈ Metric.closedBall ((quadratic c)^[p] z) r,
              HasDerivAt g (deriv g y) y ∧ ‖deriv g y‖ ≤ (K : ℝ) ∧
                (fun u => (quadratic c)^[p] (g u)) =ᶠ[𝓝 y] id) →
            dist z ((quadratic c)^[p] z) + (K : ℝ) * r ≤ r ∧
              Metric.closedBall ((quadratic c)^[p] z) r ⊆ Metric.ball ζ R))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_regular_near_return_localInverse hconvert)
    hE

/-- Connected empty-interior q62 target density from the positive fixed-anchor selector.  The only
remaining target-side dynamical input is the local conversion of a positive forward hit to either
fixed anchor into a positive periodic point in the same frontier ball. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_fixed_pair_hit_to_periodic_eventually_nonStrong_subset
    {c α β : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hαfix : quadratic c α = α) (hβfix : quadratic c β = β) (hαβ : α ≠ β)
    (hhit : ∀ {z₀ : ℂ} {ρ Rlift : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < Rlift / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ Rlift →
        ((quadratic c)^[n] z = α ∨ (quadratic c)^[n] z = β) →
        ∃ y ∈ Metric.ball z₀ Rlift, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y)
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_forward_hit_fixed_pair_to_positive_periodic
      hαfix hβfix hαβ hhit)
    hE

/-- Connected empty-interior q62 target density from the positive fixed-anchor selector and concrete
Newton contraction data at every forward hit to one of the two fixed anchors. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_fixed_pair_newton_eventually_nonStrong_subset
    {c α β : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hαfix : quadratic c α = α) (hβfix : quadratic c β = β) (hαβ : α ≠ β)
    (hnewton : ∀ {z₀ : ℂ} {ρ Rlift : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < Rlift / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ Rlift →
        ((quadratic c)^[n] z = α ∨ (quadratic c)^[n] z = β) →
        ∃ (q : ℕ) (r : ℝ) (A : ℂ) (K : NNReal),
          1 ≤ q ∧ A ≠ 0 ∧ 0 ≤ r ∧ K < 1 ∧
          Metric.closedBall z r ⊆ Metric.ball z₀ Rlift ∧
          dist (z - A * ((quadratic c)^[q] z - z)) z + (K : ℝ) * r ≤ r ∧
          ∀ y ∈ Metric.closedBall z r,
            ‖deriv (fun w => w - A * ((quadratic c)^[q] w - w)) y‖ ≤ (K : ℝ))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_forward_hit_fixed_pair_newton
      hαfix hβfix hαβ hnewton)
    hE

/-- Connected empty-interior q62 target density from the positive fixed-anchor selector and
chosen-radius Newton variation data.  This is the quantitative replacement for the qualitative
radius-package route: the caller must supply the radius, center fit, and derivative-variation bound
that make the Newton map contract. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_fixed_pair_newton_variation_eventually_nonStrong_subset
    {c α β : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hαfix : quadratic c α = α) (hβfix : quadratic c β = β) (hαβ : α ≠ β)
    (hnewton : ∀ {z₀ : ℂ} {ρ Rlift : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < Rlift / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ Rlift →
        ((quadratic c)^[n] z = α ∨ (quadratic c)^[n] z = β) →
        ∃ (q : ℕ) (r μ : ℝ) (K : NNReal),
          1 ≤ q ∧
          deriv ((quadratic c)^[q]) z ≠ 0 ∧
          0 ≤ r ∧ K < 1 ∧
          Metric.closedBall z r ⊆ Metric.ball z₀ Rlift ∧
          dist (z - (deriv ((quadratic c)^[q]) z)⁻¹ *
            ((quadratic c)^[q] z - z)) z ≤ (1 - (K : ℝ)) * r ∧
          (∀ y ∈ Metric.closedBall z r,
            ‖deriv ((quadratic c)^[q]) y - deriv ((quadratic c)^[q]) z‖ ≤ μ) ∧
          ‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * (μ + 1) ≤ (K : ℝ))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_forward_hit_fixed_pair_newton_variation
      hαfix hβfix hαβ hnewton)
    hE

/-- Connected empty-interior q62 target density from half-radius fixed-anchor hits and chosen-radius
Newton variation data.  Compared with
`dense_nonresonantPeriodic_of_preconnected_emptyInterior_fixed_pair_newton_variation_eventually_nonStrong_subset`,
the selector hit is produced in `ball z₀ (R/2)` and the caller only proves `r ≤ R/2`; containment in
`ball z₀ R` is supplied by the Newton margin lemma. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_fixed_pair_newton_variation_half_eventually_nonStrong_subset
    {c α β : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hαfix : quadratic c α = α) (hβfix : quadratic c β = β) (hαβ : α ≠ β)
    (hnewton : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        ((quadratic c)^[n] z = α ∨ (quadratic c)^[n] z = β) →
        ∃ (q : ℕ) (r μ : ℝ) (K : NNReal),
          1 ≤ q ∧
          deriv ((quadratic c)^[q]) z ≠ 0 ∧
          0 ≤ r ∧ r ≤ R / 2 ∧ K < 1 ∧
          dist (z - (deriv ((quadratic c)^[q]) z)⁻¹ *
            ((quadratic c)^[q] z - z)) z ≤ (1 - (K : ℝ)) * r ∧
          (∀ y ∈ Metric.closedBall z r,
            ‖deriv ((quadratic c)^[q]) y - deriv ((quadratic c)^[q]) z‖ ≤ μ) ∧
          ‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * (μ + 1) ≤ (K : ℝ))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_forward_hit_fixed_pair_newton_variation_half
      hαfix hβfix hαβ hnewton)
    hE

/-- Connected empty-interior q62 target density from repelling fixed-anchor selector hits and an
eventual half-radius Newton window.  This is the fixed-tail route: the repelling tail supplies the
center fit, while the caller supplies the genuine remaining quantitative window. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_fixed_pair_repelling_eventual_newton_window_half_eventually_nonStrong_subset
    {c α β : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hαfix : quadratic c α = α) (hβfix : quadratic c β = β) (hαβ : α ≠ β)
    (hαrep : 1 < ‖(2 : ℂ) * α‖) (hβrep : 1 < ‖(2 : ℂ) * β‖)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z γ, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) → (γ = α ∨ γ = β) →
        (quadratic c)^[n] z = γ →
        (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0 ∧
        ∃ δ : ℝ, 0 < δ ∧
          ∀ᶠ m : ℕ in atTop,
            ∃ (r M : ℝ) (K : NNReal),
              0 ≤ r ∧ r ≤ R / 2 ∧ 0 ≤ M ∧ K < 1 ∧
              δ ≤ (1 - (K : ℝ)) * r ∧
              (∀ y ∈ Metric.closedBall z r,
                ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ M) ∧
              ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (M * r + 1) ≤ (K : ℝ))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_forward_hit_fixed_pair_repelling_eventual_newton_window_half
      hαfix hβfix hαβ hαrep hβrep hwindow)
    hE

/-- No-precritical form of the fixed-tail/eventual-window q62 target-density reduction.  The
noncritical initial segment is expressed as avoidance of the critical point before the selector hit
reaches one of the fixed anchors. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_fixed_pair_repelling_eventual_newton_window_half_no_precritical_eventually_nonStrong_subset
    {c α β : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hαfix : quadratic c α = α) (hβfix : quadratic c β = β) (hαβ : α ≠ β)
    (hαrep : 1 < ‖(2 : ℂ) * α‖) (hβrep : 1 < ‖(2 : ℂ) * β‖)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z γ, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) → (γ = α ∨ γ = β) →
        (quadratic c)^[n] z = γ →
        (∀ k < n, (quadratic c)^[k] z ≠ 0) ∧
        ∃ δ : ℝ, 0 < δ ∧
          ∀ᶠ m : ℕ in atTop,
            ∃ (r M : ℝ) (K : NNReal),
              0 ≤ r ∧ r ≤ R / 2 ∧ 0 ≤ M ∧ K < 1 ∧
              δ ≤ (1 - (K : ℝ)) * r ∧
              (∀ y ∈ Metric.closedBall z r,
                ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ M) ∧
              ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (M * r + 1) ≤ (K : ℝ))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_forward_hit_fixed_pair_repelling_eventual_newton_window_half_no_precritical
      hαfix hβfix hαβ hαrep hβrep hwindow)
    hE

/-- Scaled no-precritical form of the fixed-tail/eventual-window q62 target-density reduction.  This
is the shrinking-radius fixed-tail interface: the remaining quantitative task is to produce the scale
`η m` and the matching second-derivative Newton window. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_fixed_pair_repelling_eventual_scaled_newton_window_half_no_precritical_eventually_nonStrong_subset
    {c α β : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hαfix : quadratic c α = α) (hβfix : quadratic c β = β) (hαβ : α ≠ β)
    (hαrep : 1 < ‖(2 : ℂ) * α‖) (hβrep : 1 < ‖(2 : ℂ) * β‖)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z γ, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) → (γ = α ∨ γ = β) →
        (quadratic c)^[n] z = γ →
        (∀ k < n, (quadratic c)^[k] z ≠ 0) ∧
        ∃ η : ℕ → ℝ,
          (∀ᶠ m : ℕ in atTop,
            ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ‖γ - z‖ ≤ η m) ∧
          ∀ᶠ m : ℕ in atTop,
            ∃ (r M : ℝ) (K : NNReal),
              0 ≤ r ∧ r ≤ R / 2 ∧ 0 ≤ M ∧ K < 1 ∧
              η m ≤ (1 - (K : ℝ)) * r ∧
              (∀ y ∈ Metric.closedBall z r,
                ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ M) ∧
              ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (M * r + 1) ≤ (K : ℝ))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_forward_hit_fixed_pair_repelling_eventual_scaled_newton_window_half_no_precritical
      hαfix hβfix hαβ hαrep hβrep hwindow)
    hE

/-- Explicit-scale no-precritical form of the fixed-tail q62 target-density reduction.  This removes
the auxiliary `η` choice from the q62-facing hypothesis: for a hit `f^[n] z = γ`, the center scale is
the concrete fixed-tail quantity `(|P_n(z)| |2γ|^m)⁻¹ |γ-z|`. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_fixed_pair_repelling_eventual_explicit_scaled_newton_window_half_no_precritical_eventually_nonStrong_subset
    {c α β : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hαfix : quadratic c α = α) (hβfix : quadratic c β = β) (hαβ : α ≠ β)
    (hαrep : 1 < ‖(2 : ℂ) * α‖) (hβrep : 1 < ‖(2 : ℂ) * β‖)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z γ, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) → (γ = α ∨ γ = β) →
        (quadratic c)^[n] z = γ →
        (∀ k < n, (quadratic c)^[k] z ≠ 0) ∧
        ∀ᶠ m : ℕ in atTop,
          ∃ (r M : ℝ) (K : NNReal),
            0 ≤ r ∧ r ≤ R / 2 ∧ 0 ≤ M ∧ K < 1 ∧
            (‖∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z‖ *
                ‖(2 : ℂ) * γ‖ ^ m)⁻¹ * ‖γ - z‖ ≤ (1 - (K : ℝ)) * r ∧
            (∀ y ∈ Metric.closedBall z r,
              ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ M) ∧
            ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (M * r + 1) ≤ (K : ℝ))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} := by
  apply dense_nonresonantPeriodic_of_preconnected_emptyInterior_fixed_pair_repelling_eventual_scaled_newton_window_half_no_precritical_eventually_nonStrong_subset
    hconn hempty hαfix hβfix hαβ hαrep hβrep
  · intro z₀ ρ R hzfront hρ0 hρR n z γ hn hz hγ hhit
    obtain ⟨hprecrit, hwin⟩ := hwindow hzfront hρ0 hρR n z γ hn hz hγ hhit
    refine ⟨hprecrit, fun m =>
      (‖∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z‖ *
        ‖(2 : ℂ) * γ‖ ^ m)⁻¹ * ‖γ - z‖, ?_, hwin⟩
    rcases hγ with rfl | rfl
    · exact Eventually.of_forall (fun m => by
        rw [deriv_fixed_tail_of_iterate_eq_fixed hhit hαfix m]
        rw [norm_inv, norm_mul, norm_pow])
    · exact Eventually.of_forall (fun m => by
        rw [deriv_fixed_tail_of_iterate_eq_fixed hhit hβfix m]
        rw [norm_inv, norm_mul, norm_pow])
  · exact hE

/-- **Connected q62 from dense nonresonant frontier targets and sparse fibre crossing.**

This removes the per-relation obligation to hand-select a separable nonresonant periodic fibre.
For each sparse relation, the caller supplies an analytic crossing region, one separable full-degree
witness in that region, and a filled-Julia seed point in the region.  Dense nonresonant frontier
targets plus connected empty-interior geometry produce an accumulating nonresonant target set in the
region; sparse crossing then selects a target where the fibre remains separable. -/
theorem q62_independence_connected_of_frontierAnalytic_eventualG_denseNonres_crossing
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne_params : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hdense : frontier (filledJulia c₁) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c₁) ∧ ∃ q : ℕ,
        (quadratic c₁)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c₁)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)})
    (hGinput : ∀ (P : Polynomial (Polynomial ℂ)) (_hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (_hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0)
        (_hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support,
            (R.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ (E F : Finset ℂ),
          (∀ᶠ p : ℕ in atTop,
            1 ≤ p ∧ multiplierOneFixedPointRoots c₂ p ⊆ F) ∧
          (∀ z ∈ F, ∃ Lz : ℕ, ∀ᶠ p : ℕ in atTop,
            1 ≤ p ∧
              analyticOrderAt (fun y : ℂ => (fixedPointPoly c₂ p).eval y) z ≤
                ((Lz + 1 : ℕ) : ℕ∞)) ∧
          (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c₂ p ⊆ E))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβfront : AnalyticOnNhd ℂ β (frontier (filledJulia c₁)))
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hcross : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsOpen Ω ∧ IsPreconnected Ω ∧ p ∈ filledJulia c₁ ∧ p ∈ Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact
    q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_frontier_derivNonres_separable_eventualG
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne_params hx₁ hx₂ hGinput β γ hβan
      hβfront hβesc hβmod hγan hγfront hγmatch (by
        intro Q s hnt hEqOn
        obtain ⟨N, Ω, w, p, hsupp, hN, hN1, hΩopen, hΩc, hpK, hpΩ, haΩ, hw,
          hleadw, hsepw⟩ := hcross Q s hnt hEqOn
        obtain ⟨z₁, S, hz₁Ω, hacc, hSgeom⟩ :=
          exists_accumulation_nonresonantPeriodic_of_frontier_dense_open
            (c := c₁) (p := p) (Ω := Ω) hKconn hempty hΩopen hpK hpΩ hdense
        have haccWithin : ∃ᶠ z in 𝓝[≠] z₁, z ∈ S := by
          rw [frequently_nhdsWithin_iff]
          exact (accPt_iff_frequently.mp hacc).mono (by
            intro z hz
            exact ⟨hz.2, hz.1⟩)
        obtain ⟨z₀, hz₀S, _hlead₀, hsep₀⟩ :=
          exists_sparse_fibre_separable_crossing
            (a := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z))
            (s := s) (N := N) hN1 hsupp hN hΩc haΩ hw hleadw hsepw hz₁Ω haccWithin
        obtain ⟨hzfront, q, hper, hnonres⟩ := hSgeom z₀ hz₀S
        exact ⟨z₀, q, hsep₀, hzfront, hper, hnonres⟩)

/-- Connected q62 from exact periodic inverse-multiplier witnesses in every frontier ball and sparse
fibre crossing.  This is the exact-return version of
`q62_independence_connected_of_frontierAnalytic_eventualG_denseNonres_crossing`; it derives the
dense nonresonant frontier target set internally from the inverse-multiplier condition. -/
theorem q62_independence_connected_of_frontierAnalytic_eventualG_periodicInvNorm_crossing
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne_params : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hlocal : ∀ z ∈ frontier (filledJulia c₁), ∀ r : ℝ, 0 < r →
      ∃ y ∈ Metric.ball z r, ∃ q : ℕ,
        (quadratic c₁)^[q] y = y ∧
        deriv ((quadratic c₁)^[q]) y ≠ 0 ∧
        ‖(deriv ((quadratic c₁)^[q]) y)⁻¹‖ < ((2 ^ q : ℝ)⁻¹))
    (hGinput : ∀ (P : Polynomial (Polynomial ℂ)) (_hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (_hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0)
        (_hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support,
            (R.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ (E F : Finset ℂ),
          (∀ᶠ p : ℕ in atTop,
            1 ≤ p ∧ multiplierOneFixedPointRoots c₂ p ⊆ F) ∧
          (∀ z ∈ F, ∃ Lz : ℕ, ∀ᶠ p : ℕ in atTop,
            1 ≤ p ∧
              analyticOrderAt (fun y : ℂ => (fixedPointPoly c₂ p).eval y) z ≤
                ((Lz + 1 : ℕ) : ℕ∞)) ∧
          (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c₂ p ⊆ E))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβfront : AnalyticOnNhd ℂ β (frontier (filledJulia c₁)))
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hcross : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsOpen Ω ∧ IsPreconnected Ω ∧ p ∈ filledJulia c₁ ∧ p ∈ Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact q62_independence_connected_of_frontierAnalytic_eventualG_denseNonres_crossing
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne_params hx₁ hx₂ hKconn hempty
    (dense_nonresonantPeriodic_of_forall_frontier_ball_periodic_deriv_inv_norm_lt hlocal)
    hGinput β γ hβan hβfront hβesc hβmod hγan hγfront hγmatch hcross

end Bottcher
