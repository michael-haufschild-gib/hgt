import GaloisForLFunctions.RHTower.SoninPrimeArchFiniteMomentTransfer

/-!
# One cofinal Sonin moment section to RH

The finite-block Sonin transfer permits a different aperture sequence for every cutoff.  A more
coherent source condition is one positive aperture sequence whose growing initial moment blocks
approximate the fixed prime--Gamma moment germ with one vanishing error.  Cofinality of the block
lengths then gives convergence of every fixed moment along that same sequence.

This is a source-to-source value relation.  It contains no Xi zero location, real-rootedness,
anti-Herglotz sign, or limiting divisor measure, and it does not assert that the required
approximation exists.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- One positive Sonin aperture sequence converges to every fixed prime--Gamma centered moment. -/
def SoninPrimeArchSingleMomentCoupling (aperture : ℕ → ℝ) : Prop :=
  (∀ j, 0 < aperture j) ∧
    ∀ r,
      Tendsto (fun j => soninAllPrimeEnergyMoment (aperture j) r) atTop
        (nhds ((normalizedPrimeArchMoment r : ℝ) : ℂ))

/-- A growing-block approximation by one Sonin aperture sequence.  The first `cutoff j` moments
are all within `error j` of the corresponding fixed prime--Gamma moments, the cutoffs tend to
infinity, and the common error tends to zero. -/
def SoninPrimeArchCofinalBlockApproximation
    (cutoff : ℕ → ℕ) (aperture error : ℕ → ℝ) : Prop :=
  (∀ j, 0 < aperture j) ∧
    Tendsto cutoff atTop atTop ∧
    (∀ j, 0 ≤ error j) ∧
    Tendsto error atTop (nhds 0) ∧
    ∀ j r, r < cutoff j →
      ‖soninAllPrimeEnergyMoment (aperture j) r -
        ((normalizedPrimeArchMoment r : ℝ) : ℂ)‖ ≤ error j

/-- A cofinal growing-block approximation supplies simultaneous convergence of every fixed moment
along the same aperture sequence. -/
theorem soninPrimeArchSingleMomentCoupling_of_cofinalBlockApproximation
    {cutoff : ℕ → ℕ} {aperture error : ℕ → ℝ}
    (h : SoninPrimeArchCofinalBlockApproximation cutoff aperture error) :
    SoninPrimeArchSingleMomentCoupling aperture := by
  refine ⟨h.1, fun r => ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hcut : ∀ᶠ j in atTop, r < cutoff j :=
    h.2.1 (eventually_gt_atTop r)
  have herr : ∀ᶠ j in atTop, error j < ε :=
    h.2.2.2.1.eventually (Iio_mem_nhds hε)
  obtain ⟨J₁, hJ₁⟩ := eventually_atTop.1 hcut
  obtain ⟨J₂, hJ₂⟩ := eventually_atTop.1 herr
  refine ⟨max J₁ J₂, fun j hj => ?_⟩
  rw [dist_eq_norm]
  exact (h.2.2.2.2 j r (hJ₁ j (le_trans (le_max_left _ _) hj))).trans_lt
    (hJ₂ j (le_trans (le_max_right _ _) hj))

/-- A single all-moment aperture sequence is, in particular, a compatible finite-moment coupling
at every cutoff; no per-cutoff choice remains. -/
theorem soninPrimeArchFiniteMomentCoupling_of_singleMomentCoupling
    {aperture : ℕ → ℝ}
    (h : SoninPrimeArchSingleMomentCoupling aperture) :
    SoninPrimeArchFiniteMomentCoupling (fun _ j => aperture j) := by
  exact ⟨fun _ j => h.1 j, fun _ r _ => h.2 r⟩

/-- Finite moment-block closure admits a uniform diagonal form: at stage `j`, choose one positive
aperture whose first `j + 1` moments lie within `1 / (j + 1)` of the prime--Gamma block.  Thus the
apparently unrelated finite-cutoff approximations assemble into one cofinal source section. -/
theorem exists_soninPrimeArchCofinalBlockApproximation_of_finiteMomentClosure
    (h : SoninPrimeArchFiniteMomentClosure) :
    ∃ aperture : ℕ → ℝ,
      SoninPrimeArchCofinalBlockApproximation
        (fun j => j + 1) aperture (fun j => 1 / ((j : ℝ) + 1)) := by
  have happ : ∀ j : ℕ, ∃ a : ℝ,
      0 < a ∧
        dist (primeArchMomentBlock (j + 1))
          (soninAllPrimeMomentBlock (j + 1) a) < 1 / ((j : ℝ) + 1) := by
    intro j
    obtain ⟨x, hx, hdist⟩ :=
      Metric.mem_closure_iff.mp (h (j + 1)) (1 / ((j : ℝ) + 1)) (by positivity)
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨a, ha, hdist⟩
  choose aperture hpos hdist using happ
  refine ⟨aperture, hpos, tendsto_add_atTop_nat 1, (fun j => by positivity),
    tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
  intro j r hr
  rw [← dist_eq_norm, dist_comm]
  have hcoord := dist_le_pi_dist
    (primeArchMomentBlock (j + 1)) (soninAllPrimeMomentBlock (j + 1) (aperture j))
    ⟨r, hr⟩
  exact hcoord.trans (hdist j).le

/-- The static finite-block value-locus condition therefore always has a one-sequence witness. -/
theorem exists_soninPrimeArchSingleMomentCoupling_of_finiteMomentClosure
    (h : SoninPrimeArchFiniteMomentClosure) :
    ∃ aperture : ℕ → ℝ, SoninPrimeArchSingleMomentCoupling aperture := by
  obtain ⟨aperture, happ⟩ :=
    exists_soninPrimeArchCofinalBlockApproximation_of_finiteMomentClosure h
  exact ⟨aperture,
    soninPrimeArchSingleMomentCoupling_of_cofinalBlockApproximation happ⟩

/-- Conversely, a single all-moment aperture section places every finite prime--Gamma moment block
in the closure of the corresponding positive Sonin moment curve. -/
theorem soninPrimeArchFiniteMomentClosure_of_singleMomentCoupling
    {aperture : ℕ → ℝ}
    (h : SoninPrimeArchSingleMomentCoupling aperture) :
    SoninPrimeArchFiniteMomentClosure := by
  intro N
  apply mem_closure_iff_seq_limit.mpr
  refine ⟨fun j => soninAllPrimeMomentBlock N (aperture j), ?_, ?_⟩
  · intro j
    exact ⟨aperture j, h.1 j, rfl⟩
  · apply tendsto_pi_nhds.mpr
    intro r
    simpa only [soninAllPrimeMomentBlock, primeArchMomentBlock] using h.2 r

/-- Finite blockwise closure is exactly the existence of one positive aperture sequence converging
coordinatewise to the entire prime--Gamma moment germ. -/
theorem soninPrimeArchFiniteMomentClosure_iff_exists_singleMomentCoupling :
    SoninPrimeArchFiniteMomentClosure ↔
      ∃ aperture : ℕ → ℝ, SoninPrimeArchSingleMomentCoupling aperture := by
  constructor
  · exact exists_soninPrimeArchSingleMomentCoupling_of_finiteMomentClosure
  · rintro ⟨aperture, h⟩
    exact soninPrimeArchFiniteMomentClosure_of_singleMomentCoupling h

/-- **One-section Sonin value chain to RH.**  One positive aperture sequence matching every fixed
Sonin moment to the prime--Gamma moment germ implies RH. -/
theorem riemannHypothesis_of_soninPrimeArchSingleMomentCoupling
    {aperture : ℕ → ℝ}
    (h : SoninPrimeArchSingleMomentCoupling aperture) :
    RiemannHypothesis :=
  riemannHypothesis_of_soninPrimeArchFiniteMomentCoupling
    (soninPrimeArchFiniteMomentCoupling_of_singleMomentCoupling h)

/-- **Cofinal block value chain to RH.**  Uniform approximation on growing Sonin moment blocks,
with a vanishing error and no divisor input, implies RH. -/
theorem riemannHypothesis_of_soninPrimeArchCofinalBlockApproximation
    {cutoff : ℕ → ℕ} {aperture error : ℕ → ℝ}
    (h : SoninPrimeArchCofinalBlockApproximation cutoff aperture error) :
    RiemannHypothesis :=
  riemannHypothesis_of_soninPrimeArchSingleMomentCoupling
    (soninPrimeArchSingleMomentCoupling_of_cofinalBlockApproximation h)

end

end RHTower
