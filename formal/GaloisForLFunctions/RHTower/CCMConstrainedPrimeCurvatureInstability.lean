import GaloisForLFunctions.RHTower.CCMFiniteSamplingGroundRigidity
import GaloisForLFunctions.RHTower.CCMPrimePoleCurvatureRankOne

/-!
# Prime curvature is unbounded on the exact constrained smooth source core

At aperture `log(21/10)`, the iterated prime energy at `log 2` reads six
strict-interior physical values. Exact finite interpolation in the pole-constrained
source core realizes every scalar multiple of a negative stencil with arbitrarily
small form norm and complete Weil quadratic. The reader retains the pole profile
and all actual prime rates; its pointwise curvature has no form-norm lower floor.
-/

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false

namespace RHTower.PrimeCurvatureCounterexample
open HTGeometry.JumpBochner

private theorem generator_row (f : ℝ → ℝ) (q : ℝ) :
    generator (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
      ccmPrimePoleJumpShift f (Real.log q) = row (fun y => f y - f (Real.log q)) q := rfl

private theorem energy_row (f g : ℝ → ℝ) (q : ℝ) :
    energyDensity (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
      ccmPrimePoleJumpShift f g (Real.log q) =
        row (fun y => (f y - f (Real.log q)) * (g y - g (Real.log q))) q / 2 := by
  simp only [energyDensity, row, difference, mul_assoc]

/-- Only six interior physical values enter the actual iterated prime energy at `log 2`. -/
theorem gammaTwo_six_sample_congr (f g : ℝ → ℝ)
    (h : ∀ q ∈ ({1 / 2, 2 / 3, 1, 4 / 3, 3 / 2, 2} : Finset ℝ),
      f (Real.log q) = g (Real.log q)) :
    gammaTwo (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
      ccmPrimePoleJumpShift f (Real.log 2) =
    gammaTwo (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
      ccmPrimePoleJumpShift g (Real.log 2) := by
  have hhalf := h (1 / 2) (by simp)
  have htwoThirds := h (2 / 3) (by simp)
  have hone := h 1 (by simp)
  have hfourThirds := h (4 / 3) (by simp)
  have hthreeHalves := h (3 / 2) (by simp)
  have htwo := h 2 (by simp)
  simp only [gammaTwo, generator_row, energy_row, row_two, row_one,
    row_two_thirds, row_half, hhalf, htwoThirds, hone, hfourThirds, hthreeHalves, htwo]

private theorem gammaTwo_const_mul (k : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    gammaTwo (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
      ccmPrimePoleJumpShift (fun y => k * f y) x =
      k ^ 2 * gammaTwo (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
        ccmPrimePoleJumpShift f x := by
  rw [gammaTwo_eq_pairSum, gammaTwo_eq_pairSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [difference]
  ring

private def sampleRatios : Finset ℝ := {1 / 2, 2 / 3, 1, 4 / 3, 3 / 2, 2}

private theorem sampleRatios_bounds {q : ℝ} (hq : q ∈ sampleRatios) :
    0 < q ∧ 10 / 21 < q ∧ q < 21 / 10 := by
  simp only [sampleRatios, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private theorem sample_log_interior {q : ℝ} (hq : q ∈ sampleRatios) :
    |Real.log q| < aperture.1 := by
  obtain ⟨hq0, hlo, hhi⟩ := sampleRatios_bounds hq
  change |Real.log q| < Real.log (21 / 10)
  rw [abs_lt]
  have hinv : Real.log (10 / 21 : ℝ) = -Real.log (21 / 10) := by
    rw [show (10 / 21 : ℝ) = (21 / 10)⁻¹ by norm_num, Real.log_inv]
  exact ⟨by rw [← hinv]; exact Real.log_lt_log (by norm_num) hlo,
    Real.log_lt_log hq0 hhi⟩

/-- The real pole-profile-normalized observable of a literal smooth physical source. -/
def sourceObservable (g : CCMComplexSmoothInteriorSource aperture) (x : ℝ) : ℝ :=
  (g x).re / primePoleProfile x

/-- Exact constrained sources realize arbitrary amplitudes of the negative prime stencil
while their form norm and complete signed Weil energy are arbitrarily small. -/
theorem exists_constrained_curvature_amplitude (k ε : ℝ) (hε : 0 < ε) :
    ∃ g : CCMComplexSmoothInteriorSource aperture,
      IsPolarConstrained aperture g.toCCMFormVector ∧
      ‖g.toCCMFormVector‖ < ε ∧
      |ccmRestrictedWeilSourceQuadratic aperture g.toCCMFormVector| < ε ∧
      gammaTwo (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
        ccmPrimePoleJumpShift (sourceObservable g) (Real.log 2) =
        k ^ 2 * gammaTwo (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
          ccmPrimePoleJumpShift witness (Real.log 2) := by
  classical
  let s := sampleRatios.image Real.log
  obtain ⟨g, hg, hgv, hgn, hgq⟩ := exists_ccmPolarConstrained_finite_interpolant_source_small
    aperture s (fun x => (primePoleProfile x * (k * witness x) : ℝ))
    (by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      exact sample_log_interior hq) ε hε
  refine ⟨g, hg, hgn, hgq, ?_⟩
  have hsamples : ∀ q ∈ sampleRatios,
      sourceObservable g (Real.log q) = k * witness (Real.log q) := by
    intro q hq
    have hv := hgv (Real.log q) (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
    rw [sourceObservable, hv, Complex.ofReal_re]
    exact mul_div_cancel_left₀ _ (primePoleProfile_pos _).ne'
  have hc := gammaTwo_six_sample_congr (sourceObservable g) (fun x => k * witness x) hsamples
  exact hc.trans (gammaTwo_const_mul k witness (Real.log 2))

/-- Prime curvature is unbounded below in every positive form-norm ball of the exact
pole-constrained smooth source core, with arbitrarily small full Weil quadratic. -/
theorem constrained_curvature_unbounded_below :
    ∀ M : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ g : CCMComplexSmoothInteriorSource aperture,
        IsPolarConstrained aperture g.toCCMFormVector ∧
        ‖g.toCCMFormVector‖ < ε ∧
        |ccmRestrictedWeilSourceQuadratic aperture g.toCCMFormVector| < ε ∧
        gammaTwo (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
          ccmPrimePoleJumpShift (sourceObservable g) (Real.log 2) < -M := by
  intro M ε hε
  let d := -gammaTwo (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
    ccmPrimePoleJumpShift witness (Real.log 2)
  have hd : 0 < d := neg_pos.mpr gammaTwo_witness_neg
  let k := |M| / d + 1
  have hk : 1 ≤ k := by
    dsimp [k]
    linarith [div_nonneg (abs_nonneg M) hd.le]
  have hkd : k * d = |M| + d := by
    dsimp [k]
    rw [add_mul, div_mul_cancel₀ _ hd.ne', one_mul]
  obtain ⟨g, hg, hgn, hgq, hcurv⟩ := exists_constrained_curvature_amplitude k ε hε
  refine ⟨g, hg, hgn, hgq, ?_⟩
  rw [hcurv]
  rw [show gammaTwo (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
    ccmPrimePoleJumpShift witness (Real.log 2) = -d by dsimp [d]; ring]
  have hs : k * d ≤ k ^ 2 * d := by
    have hp := mul_nonneg (sub_nonneg.mpr hk) (mul_nonneg (by linarith : 0 ≤ k) hd.le)
    nlinarith
  nlinarith [le_abs_self M]

private def extremalSamples (q : ℝ) : ℝ :=
  let C := -PrimeCurvatureRankOne.residualBC / (2 * PrimeCurvatureRankOne.delta)
  let A := -(PrimeCurvatureRankOne.crossAB + PrimeCurvatureRankOne.crossAC * C) /
    (2 * PrimeCurvatureRankOne.alpha)
  if q = 1 then A else if q = 2/3 then 1 else if q = 1/2 then C
    else if q = 4/3 then 2 else if q = 3/2 then 2 * C else 0

private def extremalObservable (x : ℝ) : ℝ := extremalSamples (Real.exp x)

private theorem extremal_curvature :
    PrimeCurvatureRankOne.curvatureAtTwo extremalObservable = -PrimeCurvatureRankOne.penalty := by
  rw [PrimeCurvatureRankOne.curvatureAtTwo_eq_four_squares]
  norm_num [PrimeCurvatureRankOne.sampleDelta, extremalObservable, extremalSamples,
    Real.exp_log (by norm_num : (0 : ℝ) < 1),
    Real.exp_log (by norm_num : (0 : ℝ) < 2/3),
    Real.exp_log (by norm_num : (0 : ℝ) < 1/2),
    Real.exp_log (by norm_num : (0 : ℝ) < 4/3),
    Real.exp_log (by norm_num : (0 : ℝ) < 3/2),
    Real.exp_log (by norm_num : (0 : ℝ) < 2), PrimeCurvatureRankOne.penalty]
  ring

/-- Exact sharp curvature is attained on arbitrarily small actual compact source vectors. -/
theorem exists_constrained_rankOne_curvature_extremizer (ε : ℝ) (hε : 0 < ε) :
    ∃ g : CCMComplexSmoothInteriorSource aperture,
      IsPolarConstrained aperture g.toCCMFormVector ∧
      ‖g.toCCMFormVector‖ < ε ∧
      |ccmRestrictedWeilSourceQuadratic aperture g.toCCMFormVector| < ε ∧
      PrimeCurvatureRankOne.sampleDelta (sourceObservable g) (2/3) = 1 ∧
      PrimeCurvatureRankOne.curvatureAtTwo (sourceObservable g) = -PrimeCurvatureRankOne.penalty := by
  classical
  let s := sampleRatios.image Real.log
  obtain ⟨g, hg, hgv, hgn, hgq⟩ := exists_ccmPolarConstrained_finite_interpolant_source_small
    aperture s (fun x => (primePoleProfile x * extremalObservable x : ℝ))
    (by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      exact sample_log_interior hq) ε hε
  have hsamples : ∀ q ∈ sampleRatios,
      sourceObservable g (Real.log q) = extremalObservable (Real.log q) := by
    intro q hq
    have hv := hgv (Real.log q) (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
    rw [sourceObservable, hv, Complex.ofReal_re]
    exact mul_div_cancel_left₀ _ (primePoleProfile_pos _).ne'
  refine ⟨g, hg, hgn, hgq, ?_, ?_⟩
  · rw [PrimeCurvatureRankOne.sampleDelta,
      hsamples (2/3) (by simp [sampleRatios]), hsamples 2 (by simp [sampleRatios])]
    norm_num [extremalObservable, extremalSamples,
      Real.exp_log (by norm_num : (0 : ℝ) < 2/3),
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  · exact (gammaTwo_six_sample_congr _ _ hsamples).trans extremal_curvature

/-- The one-direction coefficient is optimal even on every positive form-norm ball
of the exact constrained compact source core. -/
theorem constrained_rankOne_compensation_iff (c ε : ℝ) (hε : 0 < ε) :
    (∀ g : CCMComplexSmoothInteriorSource aperture,
      IsPolarConstrained aperture g.toCCMFormVector → ‖g.toCCMFormVector‖ < ε →
      -c * (PrimeCurvatureRankOne.sampleDelta (sourceObservable g) (2/3))^2 ≤
        PrimeCurvatureRankOne.curvatureAtTwo (sourceObservable g)) ↔
    PrimeCurvatureRankOne.penalty ≤ c := by
  constructor
  · intro h
    obtain ⟨g, hg, hgn, _, hB, hcurv⟩ := exists_constrained_rankOne_curvature_extremizer ε hε
    have hb := h g hg hgn
    rw [hB, hcurv] at hb
    norm_num at hb
    linarith
  · intro hc g _ _
    exact (mul_le_mul_of_nonneg_right (neg_le_neg hc) (sq_nonneg _)).trans
      (PrimeCurvatureRankOne.curvatureAtTwo_ge_rankOne (sourceObservable g))

/-- Nonnegative pointwise prime curvature still admits every near-ground Rayleigh value. -/
theorem exists_constrained_nonnegative_curvature_near_ground {ε : ℝ} (hε : 0 < ε) :
    ∃ g : CCMComplexSmoothInteriorSource aperture,
      IsPolarConstrained aperture g.toCCMFormVector ∧
      g (Real.log 2) = 0 ∧ g (Real.log (2/3)) = 0 ∧
      ccmArchimedeanFormToAperture aperture g.toCCMFormVector ≠ 0 ∧
      ccmRestrictedWeilSourceQuadratic aperture g.toCCMFormVector /
        ‖ccmArchimedeanFormToAperture aperture g.toCCMFormVector‖^2 <
          ccmRestrictedWeilPolarGroundEnergy aperture + ε ∧
      0 ≤ PrimeCurvatureRankOne.curvatureAtTwo (sourceObservable g) := by
  classical
  let s : Finset ℝ := {Real.log 2, Real.log (2/3)}
  have hs : ∀ x ∈ s, |x| < aperture.1 := by
    intro x hx
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact sample_log_interior (by simp [sampleRatios])
    · exact sample_log_interior (by simp [sampleRatios])
  obtain ⟨g, hg, hgv, hgne, hgR⟩ := exists_ccmPolarConstrained_sampled_rayleigh_lt
    aperture s (fun _ => 0) hs hε
  have h₂ : g (Real.log 2) = 0 := hgv _ (by simp [s])
  have h₃ : g (Real.log (2/3)) = 0 := hgv _ (by simp [s])
  refine ⟨g, hg, h₂, h₃, hgne, hgR, ?_⟩
  apply PrimeCurvatureRankOne.curvatureAtTwo_nonneg_of_sample_eq
  simp [sourceObservable, h₂, h₃]

end RHTower.PrimeCurvatureCounterexample
