import GaloisForLFunctions.RHTower.CCMPrimePoleCurvatureAperturePlateau

/-!
# Compact-source curvature at the first prime boundary

At aperture `log 2`, the closed prime cutoff has the same four curvature rows as the
strictly larger aperture band. Compact interior sources vanish at both endpoints, removing
the only negative direction of the six-sample quadratic. The remaining two-variable block
is positive definite by the exact inequalities `3 log 2 < 2 log 3` and `5 log 3 < 8 log 2`.
Its kernel is exactly the vanishing of the real source component at all six sample points.
Every strictly larger aperture in the band admits the sharp negative stencil in arbitrarily
small exactly pole-constrained source balls.
-/

open scoped BigOperators
noncomputable section
set_option autoImplicit false
namespace RHTower.PrimeCurvatureCompactOnset
open HTGeometry.JumpBochner PrimeCurvatureRankOne

/-- The first prime aperture, with its closed endpoint indicators. -/
def aperture : SuzukiPositiveAperture :=
  ⟨Real.log 2, Real.log_pos (by norm_num)⟩

theorem aperture_exp : Real.exp (2 * aperture.1) = 4 := by
  change Real.exp (2 * Real.log 2) = _
  rw [show 2 * Real.log 2 = Real.log 2 + Real.log 2 by ring,
    Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  ring

private theorem old_indices :
    ccmPrimePoleJumpIndices PrimeCurvatureCounterexample.aperture =
      (Finset.Icc 2 4).product Finset.univ := by
  rw [ccmPrimePoleJumpIndices, PrimeCurvatureCounterexample.aperture_exp]
  norm_num

/-- No prime-power index is lost at the closed boundary. -/
theorem aperture_indices_eq :
    ccmPrimePoleJumpIndices aperture =
      ccmPrimePoleJumpIndices PrimeCurvatureCounterexample.aperture := by
  rw [old_indices, ccmPrimePoleJumpIndices, aperture_exp]
  norm_num

private theorem rate_at_probe_eq {q : ℝ}
    (hq : q ∈ PrimeCurvatureAperturePlateau.probeRows) {j : ℕ × Bool}
    (hj : j ∈ ccmPrimePoleJumpIndices PrimeCurvatureCounterexample.aperture) :
    ccmPrimePoleJumpRate aperture j (Real.log q) =
      ccmPrimePoleJumpRate PrimeCurvatureCounterexample.aperture j (Real.log q) := by
  obtain ⟨n, b⟩ := j
  rw [old_indices] at hj
  have hn := (Finset.mem_product.mp hj).1
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ))
    (Finset.mem_Icc.mp hn).1
  have hq0 : 0 < q := by
    simp only [PrimeCurvatureAperturePlateau.probeRows, Finset.mem_insert,
      Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> norm_num
  rw [ccmPrimePoleJumpRate_log_cutoff aperture (by norm_num : (0 : ℝ) < 2)
    rfl hq0 hn0 b, PrimeCurvatureCounterexample.rate_at_log hq0 hn0 b]
  simp only [PrimeCurvatureAperturePlateau.probeRows, Finset.mem_insert,
    Finset.mem_singleton] at hq
  obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hn
  rcases hq with rfl | rfl | rfl | rfl <;> interval_cases n <;> cases b <;>
    norm_num [ccmPrimePoleMultiplicativeTarget]

private def row (F : ℝ → ℝ) (q : ℝ) : ℝ :=
  ∑ j ∈ ccmPrimePoleJumpIndices aperture,
    ccmPrimePoleJumpRate aperture j (Real.log q) * F (ccmPrimePoleJumpShift j (Real.log q))

private theorem row_eq_old (F : ℝ → ℝ) {q : ℝ}
    (hq : q ∈ PrimeCurvatureAperturePlateau.probeRows) :
    row F q = PrimeCurvatureCounterexample.row F q := by
  unfold row PrimeCurvatureCounterexample.row
  rw [aperture_indices_eq]
  apply Finset.sum_congr rfl
  intro j hj
  rw [rate_at_probe_eq hq hj]

private theorem generator_row (f : ℝ → ℝ) (q : ℝ) :
    generator (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
      ccmPrimePoleJumpShift f (Real.log q) = row (fun y => f y - f (Real.log q)) q := rfl

private theorem energy_row (f g : ℝ → ℝ) (q : ℝ) :
    energyDensity (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
      ccmPrimePoleJumpShift f g (Real.log q) =
        row (fun y => (f y - f (Real.log q)) * (g y - g (Real.log q))) q / 2 := by
  simp only [energyDensity, row, difference, mul_assoc]

private theorem generator_old_row (f : ℝ → ℝ) (q : ℝ) :
    generator (ccmPrimePoleJumpIndices PrimeCurvatureCounterexample.aperture)
      (ccmPrimePoleJumpRate PrimeCurvatureCounterexample.aperture)
      ccmPrimePoleJumpShift f (Real.log q) =
        PrimeCurvatureCounterexample.row (fun y => f y - f (Real.log q)) q := rfl

private theorem energy_old_row (f g : ℝ → ℝ) (q : ℝ) :
    energyDensity (ccmPrimePoleJumpIndices PrimeCurvatureCounterexample.aperture)
      (ccmPrimePoleJumpRate PrimeCurvatureCounterexample.aperture)
      ccmPrimePoleJumpShift f g (Real.log q) =
        PrimeCurvatureCounterexample.row
          (fun y => (f y - f (Real.log q)) * (g y - g (Real.log q))) q / 2 := by
  simp only [energyDensity, PrimeCurvatureCounterexample.row, difference, mul_assoc]

/-- The literal boundary curvature retains the full six-sample quadratic. -/
theorem gammaTwo_eq_fixed (f : ℝ → ℝ) :
    gammaTwo (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
      ccmPrimePoleJumpShift f (Real.log 2) = curvatureAtTwo f := by
  have h₂ (F : ℝ → ℝ) := row_eq_old F
    (show (2 : ℝ) ∈ PrimeCurvatureAperturePlateau.probeRows by
      simp [PrimeCurvatureAperturePlateau.probeRows])
  have h₁ (F : ℝ → ℝ) := row_eq_old F
    (show (1 : ℝ) ∈ PrimeCurvatureAperturePlateau.probeRows by
      simp [PrimeCurvatureAperturePlateau.probeRows])
  have h₃ (F : ℝ → ℝ) := row_eq_old F
    (show (2/3 : ℝ) ∈ PrimeCurvatureAperturePlateau.probeRows by
      simp [PrimeCurvatureAperturePlateau.probeRows])
  have h₄ (F : ℝ → ℝ) := row_eq_old F
    (show (1/2 : ℝ) ∈ PrimeCurvatureAperturePlateau.probeRows by
      simp [PrimeCurvatureAperturePlateau.probeRows])
  unfold curvatureAtTwo
  simp only [gammaTwo, generator_row, energy_row, generator_old_row, energy_old_row,
    h₂, h₁, h₃, h₄, PrimeCurvatureCounterexample.row_two, PrimeCurvatureCounterexample.row_one,
    PrimeCurvatureCounterexample.row_two_thirds, PrimeCurvatureCounterexample.row_half]

private theorem log_bounds :
    0 < Real.log 2 ∧ 0 < Real.log 3 ∧
      3 * Real.log 2 < 2 * Real.log 3 ∧ 5 * Real.log 3 < 8 * Real.log 2 := by
  refine ⟨Real.log_pos (by norm_num), Real.log_pos (by norm_num), ?_, ?_⟩
  · have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 2^3)
      (by norm_num : (2 : ℝ)^3 < 3^2)
    rw [Real.log_pow, Real.log_pow] at h
    norm_num at h
    exact h
  · have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 3^5)
      (by norm_num : (3 : ℝ)^5 < 2^8)
    rw [Real.log_pow, Real.log_pow] at h
    norm_num at h
    exact h

/-- The two-variable block remains strictly positive when both endpoint samples vanish. -/
theorem boundary_blockDet_pos : 0 < alpha * beta - crossAB^2 / 4 := by
  obtain ⟨hl, hm, hlo, hhi⟩ := log_bounds
  have hs : 0 < (Real.log 2)^2 := sq_pos_of_pos hl
  have hα : (7/10 : ℝ) * (Real.log 2)^2 < alpha := by
    have hp := mul_lt_mul_of_pos_left hhi hl
    dsimp [alpha]
    nlinarith
  have hfactor : beta - (25/72 : ℝ) * (Real.log 2)^2 =
      (Real.log 3 - 3 * Real.log 2 / 2) *
        (53 * Real.log 3 / 162 + 25 * Real.log 2 / 108) := by
    dsimp [beta]
    ring
  have hβ : (25/72 : ℝ) * (Real.log 2)^2 < beta := by
    have hp : 0 < (Real.log 3 - 3 * Real.log 2 / 2) *
        (53 * Real.log 3 / 162 + 25 * Real.log 2 / 108) :=
      mul_pos (by linarith) (by positivity)
    linarith [hfactor]
  have hprod₁ := mul_lt_mul_of_pos_left hβ alpha_pos
  have hprod₂ := mul_lt_mul_of_pos_right hα
    (by positivity : 0 < (25/72 : ℝ) * (Real.log 2)^2)
  have hprod := hprod₂.trans hprod₁
  have hb0 : 0 < crossAB := by dsimp [crossAB]; positivity
  have hb : crossAB < (16/27 : ℝ) * (Real.log 2)^2 := by
    have hp := mul_lt_mul_of_pos_left hhi hl
    dsimp [crossAB]
    nlinarith
  have hcross : crossAB^2 < ((16/27 : ℝ) * (Real.log 2)^2)^2 := by
    have hp := mul_pos (sub_pos.mpr hb)
      (show 0 < (16/27 : ℝ) * (Real.log 2)^2 + crossAB by positivity)
    nlinarith
  nlinarith [sq_pos_of_pos hs]

/-- The positive Schur pivot of the endpoint-restricted curvature. -/
def boundarySchur : ℝ := beta - crossAB^2 / (4 * alpha)

theorem boundarySchur_pos : 0 < boundarySchur := by
  have h := boundary_blockDet_pos
  have hα := alpha_pos
  have hden : 0 < 4 * alpha := by positivity
  unfold boundarySchur
  apply sub_pos.mpr
  apply (div_lt_iff₀ hden).mpr
  nlinarith

/-- Four positive squares describe the entire endpoint-restricted quadratic. -/
theorem curvatureAtTwo_eq_boundary_squares (f : ℝ → ℝ)
    (hC : sampleDelta f (1/2) = 0) :
    curvatureAtTwo f =
      (7 * Real.log 2 * Real.log 3 / 72) *
        (sampleDelta f (4/3) - 2 * sampleDelta f (2/3))^2 +
      (5 * Real.log 2 * Real.log 3 / 72) * (sampleDelta f (3/2))^2 +
      alpha * (sampleDelta f 1 + crossAB * sampleDelta f (2/3) / (2 * alpha))^2 +
      boundarySchur * (sampleDelta f (2/3))^2 := by
  rw [curvatureAtTwo_eq_reduced, hC]
  simp only [mul_zero, sub_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
  unfold boundarySchur
  field_simp [alpha_pos.ne']
  ring

private theorem four_squares_eq_zero_iff
    {a b c d x y z w : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    a*x^2 + b*y^2 + c*z^2 + d*w^2 = 0 ↔ x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by
  have hx := mul_nonneg ha.le (sq_nonneg x)
  have hy := mul_nonneg hb.le (sq_nonneg y)
  have hz := mul_nonneg hc.le (sq_nonneg z)
  have hw := mul_nonneg hd.le (sq_nonneg w)
  constructor
  · intro h
    have hax : a*x^2 = 0 := le_antisymm (by linarith) hx
    have hby : b*y^2 = 0 := le_antisymm (by linarith) hy
    have hcz : c*z^2 = 0 := le_antisymm (by linarith) hz
    have hdw : d*w^2 = 0 := le_antisymm (by linarith) hw
    exact ⟨sq_eq_zero_iff.mp ((mul_eq_zero.mp hax).resolve_left ha.ne'),
      sq_eq_zero_iff.mp ((mul_eq_zero.mp hby).resolve_left hb.ne'),
      sq_eq_zero_iff.mp ((mul_eq_zero.mp hcz).resolve_left hc.ne'),
      sq_eq_zero_iff.mp ((mul_eq_zero.mp hdw).resolve_left hd.ne')⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp

/-- The six physical sample ratios, including both boundary points. -/
def sampleRatios : Finset ℝ := {1/2, 2/3, 1, 4/3, 3/2, 2}

theorem curvatureAtTwo_nonneg_of_endpoints (f : ℝ → ℝ)
    (h₂ : f (Real.log 2) = 0) (hhalf : f (Real.log (1/2)) = 0) :
    0 ≤ curvatureAtTwo f := by
  have hC : sampleDelta f (1/2) = 0 := by simp only [sampleDelta, h₂, hhalf, sub_self]
  obtain ⟨hl, hm, _, _⟩ := log_bounds
  rw [curvatureAtTwo_eq_boundary_squares f hC]
  have hα := alpha_pos
  have hβ := boundarySchur_pos
  positivity

theorem curvatureAtTwo_eq_zero_iff_of_endpoints (f : ℝ → ℝ)
    (h₂ : f (Real.log 2) = 0) (hhalf : f (Real.log (1/2)) = 0) :
    curvatureAtTwo f = 0 ↔ ∀ q ∈ sampleRatios, f (Real.log q) = 0 := by
  have hC : sampleDelta f (1/2) = 0 := by simp only [sampleDelta, h₂, hhalf, sub_self]
  obtain ⟨hl, hm, _, _⟩ := log_bounds
  rw [curvatureAtTwo_eq_boundary_squares f hC,
    four_squares_eq_zero_iff (by positivity) (by positivity) alpha_pos boundarySchur_pos]
  simp only [sampleDelta, h₂, sub_zero]
  constructor
  · rintro ⟨hD, hE, hA, hB⟩ q hq
    simp only [sampleRatios, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hhalf
    · exact hB
    · simpa [hB] using hA
    · simpa [hB] using hD
    · exact hE
    · exact h₂
  · intro h
    have hA := h 1 (by simp [sampleRatios])
    have hB := h (2/3) (by simp [sampleRatios])
    have hD := h (4/3) (by simp [sampleRatios])
    have hE := h (3/2) (by simp [sampleRatios])
    rw [hA, hB, hD, hE]
    simp

/-- The real component read through the actual positive pole profile. -/
def sourceObservable (g : CCMComplexSmoothInteriorSource aperture) (x : ℝ) : ℝ :=
  (g x).re / primePoleProfile x

theorem source_endpoints_zero (g : CCMComplexSmoothInteriorSource aperture) :
    g (Real.log 2) = 0 ∧ g (Real.log (1/2)) = 0 := by
  have hright : g (Real.log 2) = 0 := by
    by_contra h
    have hx := g.support_subset (Function.mem_support.mpr h)
    exact (lt_irrefl (Real.log 2)) hx.2
  have hleft : g (-Real.log 2) = 0 := by
    by_contra h
    have hx := g.support_subset (Function.mem_support.mpr h)
    exact (lt_irrefl (-Real.log 2)) hx.1
  exact ⟨hright, by simpa only [one_div, Real.log_inv] using hleft⟩

/-- Every compact interior source has nonnegative literal prime curvature at the boundary. -/
theorem compact_source_gammaTwo_nonneg (g : CCMComplexSmoothInteriorSource aperture) :
    0 ≤ gammaTwo (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
      ccmPrimePoleJumpShift (sourceObservable g) (Real.log 2) := by
  rw [gammaTwo_eq_fixed]
  obtain ⟨h₂, hhalf⟩ := source_endpoints_zero g
  apply curvatureAtTwo_nonneg_of_endpoints
  · simp only [sourceObservable, h₂, Complex.zero_re, zero_div]
  · simp only [sourceObservable, hhalf, Complex.zero_re, zero_div]

/-- Zero boundary curvature is exactly the vanishing of all six real physical samples. -/
theorem compact_source_gammaTwo_eq_zero_iff (g : CCMComplexSmoothInteriorSource aperture) :
    gammaTwo (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
      ccmPrimePoleJumpShift (sourceObservable g) (Real.log 2) = 0 ↔
        ∀ q ∈ sampleRatios, (g (Real.log q)).re = 0 := by
  rw [gammaTwo_eq_fixed]
  obtain ⟨h₂, hhalf⟩ := source_endpoints_zero g
  rw [curvatureAtTwo_eq_zero_iff_of_endpoints (sourceObservable g)
    (by simp only [sourceObservable, h₂, Complex.zero_re, zero_div])
    (by simp only [sourceObservable, hhalf, Complex.zero_re, zero_div])]
  constructor
  · intro h q hq
    exact (div_eq_zero_iff.mp (h q hq)).resolve_right (primePoleProfile_pos _).ne'
  · intro h q hq
    simp only [sourceObservable, h q hq, zero_div]

/-- The complete intrinsic onset law, including every larger aperture in the plateau. -/
theorem compact_source_curvature_onset :
    (∀ g : CCMComplexSmoothInteriorSource aperture,
      0 ≤ gammaTwo (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
        ccmPrimePoleJumpShift (sourceObservable g) (Real.log 2) ∧
      (gammaTwo (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
        ccmPrimePoleJumpShift (sourceObservable g) (Real.log 2) = 0 ↔
          ∀ q ∈ sampleRatios, (g (Real.log q)).re = 0)) ∧
    (∀ (A : PrimeCurvatureAperturePlateau.Scale) (ε : {r : ℝ // 0 < r}),
      ∃ g : CCMComplexSmoothInteriorSource (PrimeCurvatureAperturePlateau.apertureFor A),
        IsPolarConstrained (PrimeCurvatureAperturePlateau.apertureFor A) g.toCCMFormVector ∧
        ‖g.toCCMFormVector‖ < ε.1 ∧
        |ccmRestrictedWeilSourceQuadratic (PrimeCurvatureAperturePlateau.apertureFor A)
          g.toCCMFormVector| < ε.1 ∧
        sampleDelta (PrimeCurvatureAperturePlateau.sourceObservable g) (2/3) = 1 ∧
        gammaTwo (ccmPrimePoleJumpIndices (PrimeCurvatureAperturePlateau.apertureFor A))
          (ccmPrimePoleJumpRate (PrimeCurvatureAperturePlateau.apertureFor A))
          ccmPrimePoleJumpShift (PrimeCurvatureAperturePlateau.sourceObservable g)
            (Real.log 2) = -penalty ∧
        gammaTwo (ccmPrimePoleJumpIndices (PrimeCurvatureAperturePlateau.apertureFor A))
          (ccmPrimePoleJumpRate (PrimeCurvatureAperturePlateau.apertureFor A))
          ccmPrimePoleJumpShift (PrimeCurvatureAperturePlateau.sourceObservable g)
            (Real.log 2) < 0) := by
  constructor
  · exact fun g => ⟨compact_source_gammaTwo_nonneg g, compact_source_gammaTwo_eq_zero_iff g⟩
  · intro A ε
    obtain ⟨g, hg, hgn, hgq, hB, hΓ⟩ :=
      PrimeCurvatureAperturePlateau.exists_constrained_rankOne_extremizer A ε.1 ε.2
    refine ⟨g, hg, hgn, hgq, hB, hΓ, ?_⟩
    rw [hΓ]
    linarith [penalty_pos]

end RHTower.PrimeCurvatureCompactOnset
