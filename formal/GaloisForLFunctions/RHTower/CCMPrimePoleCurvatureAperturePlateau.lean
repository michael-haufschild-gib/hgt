import GaloisForLFunctions.RHTower.CCMConstrainedPrimeCurvatureInstability

/-!
# Literal prime curvature remains fixed across an aperture band

For `2 < A < 5/2`, every index at least five has zero rate at the four
rows entering the iterated prime energy at `log 2`. The remaining rates
are exactly those at `log(21/10)`, including all endpoint indicators.
-/

open scoped BigOperators
noncomputable section
set_option autoImplicit false
namespace RHTower.PrimeCurvatureAperturePlateau
open HTGeometry.JumpBochner

abbrev Scale := {A : ℝ // 2 < A ∧ A < 5/2}

def apertureFor (A : Scale) : SuzukiPositiveAperture :=
  ⟨Real.log A.1, Real.log_pos (by linarith [A.2.1])⟩

private theorem scale_pos (A : Scale) : 0 < A.1 := by linarith [A.2.1]

private theorem inverse_bounds (A : Scale) : (2/5 : ℝ) < A.1⁻¹ ∧ A.1⁻¹ < 1/2 := by
  have hi : 0 < A.1⁻¹ := inv_pos.mpr (scale_pos A)
  have hlo := mul_lt_mul_of_pos_right A.2.2 hi
  have hhi := mul_lt_mul_of_pos_right A.2.1 hi
  rw [mul_inv_cancel₀ (scale_pos A).ne'] at hlo hhi
  constructor <;> linarith

private theorem aperture_exp (A : Scale) :
    Real.exp (2 * (apertureFor A).1) = A.1^2 := by
  change Real.exp (2 * Real.log A.1) = _
  rw [show 2 * Real.log A.1 = Real.log A.1 + Real.log A.1 by ring,
    Real.exp_add, Real.exp_log (scale_pos A)]
  ring

private theorem four_le_floor (A : Scale) : 4 ≤ ⌊A.1^2⌋₊ := by
  apply (Nat.le_floor_iff (sq_nonneg A.1)).mpr
  norm_num
  nlinarith [A.2.1, sq_nonneg (A.1 - 2)]

def probeRows : Finset ℝ := {2, 1, 2/3, 1/2}

private theorem probe_bounds {q : ℝ} (hq : q ∈ probeRows) : (1/2 : ℝ) ≤ q ∧ q ≤ 2 := by
  simp only [probeRows, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> norm_num

private theorem probe_inside (A : Scale) {q : ℝ} (hq : q ∈ probeRows) :
    A.1⁻¹ ≤ q ∧ q ≤ A.1 := by
  obtain ⟨hlo, hhi⟩ := probe_bounds hq
  exact ⟨(inverse_bounds A).2.le.trans hlo, hhi.trans A.2.1.le⟩

private theorem target_cutoff_iff (A : Scale) {q : ℝ} (hq : q ∈ probeRows)
    {n : ℕ} (hn : n ∈ Finset.Icc 2 4) (b : Bool) :
    (A.1⁻¹ ≤ ccmPrimePoleMultiplicativeTarget (n,b) q ∧
      ccmPrimePoleMultiplicativeTarget (n,b) q ≤ A.1) ↔
    ((10/21 : ℝ) ≤ ccmPrimePoleMultiplicativeTarget (n,b) q ∧
      ccmPrimePoleMultiplicativeTarget (n,b) q ≤ 21/10) := by
  have hAlo := A.2.1
  have hAhi := A.2.2
  obtain ⟨hilo, hihi⟩ := inverse_bounds A
  obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hn
  simp only [probeRows, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> interval_cases n <;> cases b <;>
    norm_num [ccmPrimePoleMultiplicativeTarget]
  all_goals first
    | constructor <;> linarith
    | intro ht; linarith

private theorem rate_small_eq (A : Scale) {q : ℝ} (hq : q ∈ probeRows)
    {n : ℕ} (hn : n ∈ Finset.Icc 2 4) (b : Bool) :
    ccmPrimePoleJumpRate (apertureFor A) (n,b) (Real.log q) =
      ccmPrimePoleJumpRate PrimeCurvatureCounterexample.aperture (n,b) (Real.log q) := by
  have hq0 : 0 < q := by linarith [(probe_bounds hq).1]
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) (Finset.mem_Icc.mp hn).1
  have hold : (10/21 : ℝ) ≤ q ∧ q ≤ 21/10 := by
    obtain ⟨hlo, hhi⟩ := probe_bounds hq
    constructor <;> linarith
  rw [ccmPrimePoleJumpRate_log_cutoff (apertureFor A) (scale_pos A) rfl hq0 hn0 b,
    PrimeCurvatureCounterexample.rate_at_log hq0 hn0 b,
    if_pos (probe_inside A hq), if_pos hold]
  simp only [target_cutoff_iff A hq hn b]

/-- Every higher index is invisible at each row in this exact curvature footprint. -/
theorem higher_rate_zero (A : Scale) {q : ℝ} (hq : q ∈ probeRows)
    {n : ℕ} (hn : 5 ≤ n) (b : Bool) :
    ccmPrimePoleJumpRate (apertureFor A) (n,b) (Real.log q) = 0 := by
  obtain ⟨hqlo, hqhi⟩ := probe_bounds hq
  have hq0 : 0 < q := by linarith
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num : 0 < (5 : ℕ)) hn
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hnR0 : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hback : q / (n : ℝ) ≤ 2/5 := (div_le_iff₀ hnR0).mpr (by linarith)
  have hforward : (5/2 : ℝ) ≤ q * n := by
    have h₁ := mul_le_mul_of_nonneg_right hqlo (by norm_num : (0 : ℝ) ≤ 5)
    have h₂ := mul_le_mul_of_nonneg_left hnR hq0.le
    nlinarith
  have hout : ¬ (A.1⁻¹ ≤ ccmPrimePoleMultiplicativeTarget (n,b) q ∧
      ccmPrimePoleMultiplicativeTarget (n,b) q ≤ A.1) := by
    obtain ⟨hilo, _⟩ := inverse_bounds A
    have hAhi := A.2.2
    cases b <;> simp only [ccmPrimePoleMultiplicativeTarget, Bool.false_eq_true, ↓reduceIte]
    · rintro ⟨hlo, _⟩; linarith
    · rintro ⟨_, hhi⟩; linarith
  rw [ccmPrimePoleJumpRate_log_cutoff (apertureFor A) (scale_pos A) rfl hq0 hn0 b,
    if_pos (probe_inside A hq), if_neg hout]

def rowFor (A : Scale) (F : ℝ → ℝ) (q : ℝ) : ℝ :=
  ∑ j ∈ ccmPrimePoleJumpIndices (apertureFor A),
    ccmPrimePoleJumpRate (apertureFor A) j (Real.log q) * F (ccmPrimePoleJumpShift j (Real.log q))

private theorem old_indices :
    ccmPrimePoleJumpIndices PrimeCurvatureCounterexample.aperture =
      (Finset.Icc 2 4).product Finset.univ := by
  rw [ccmPrimePoleJumpIndices, PrimeCurvatureCounterexample.aperture_exp]
  norm_num

/-- Exact equality of every row used by iterated prime energy, through all cutoff entries. -/
theorem rowFor_eq_old (A : Scale) (F : ℝ → ℝ) {q : ℝ} (hq : q ∈ probeRows) :
    rowFor A F q = PrimeCurvatureCounterexample.row F q := by
  classical
  have hsub : ccmPrimePoleJumpIndices PrimeCurvatureCounterexample.aperture ⊆
      ccmPrimePoleJumpIndices (apertureFor A) := by
    intro j hj
    rw [old_indices] at hj
    obtain ⟨hjn, hjb⟩ := Finset.mem_product.mp hj
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hjn
    rw [ccmPrimePoleJumpIndices, aperture_exp]
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hlo, hhi.trans (four_le_floor A)⟩, hjb⟩
  have hzero : ∀ j ∈ ccmPrimePoleJumpIndices (apertureFor A),
      j ∉ ccmPrimePoleJumpIndices PrimeCurvatureCounterexample.aperture →
      ccmPrimePoleJumpRate (apertureFor A) j (Real.log q) *
        F (ccmPrimePoleJumpShift j (Real.log q)) = 0 := by
    intro j hj hjnot
    have hlo : 2 ≤ j.1 := by
      rw [ccmPrimePoleJumpIndices, aperture_exp] at hj
      exact (Finset.mem_Icc.mp (Finset.mem_product.mp hj).1).1
    have hgt : 4 < j.1 := lt_of_not_ge (by
      intro hle
      apply hjnot
      rw [old_indices]
      exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hlo, hle⟩, Finset.mem_univ _⟩)
    rw [higher_rate_zero A hq (show 5 ≤ j.1 from hgt) j.2, zero_mul]
  have hs := Finset.sum_subset hsub hzero
  unfold rowFor
  rw [← hs]
  unfold PrimeCurvatureCounterexample.row
  apply Finset.sum_congr rfl
  intro j hj
  rw [old_indices] at hj
  rw [rate_small_eq A hq (Finset.mem_product.mp hj).1 j.2]

private theorem generator_new_row (A : Scale) (f : ℝ → ℝ) (q : ℝ) :
    generator (ccmPrimePoleJumpIndices (apertureFor A)) (ccmPrimePoleJumpRate (apertureFor A))
      ccmPrimePoleJumpShift f (Real.log q) = rowFor A (fun y => f y - f (Real.log q)) q := rfl

private theorem energy_new_row (A : Scale) (f g : ℝ → ℝ) (q : ℝ) :
    energyDensity (ccmPrimePoleJumpIndices (apertureFor A)) (ccmPrimePoleJumpRate (apertureFor A))
      ccmPrimePoleJumpShift f g (Real.log q) =
        rowFor A (fun y => (f y - f (Real.log q)) * (g y - g (Real.log q))) q / 2 := by
  simp only [energyDensity, rowFor, difference, mul_assoc]

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

/-- Literal iterated prime energy stays exactly fixed throughout the whole scale band. -/
theorem gammaTwo_eq_fixed (A : Scale) (f : ℝ → ℝ) :
    gammaTwo (ccmPrimePoleJumpIndices (apertureFor A)) (ccmPrimePoleJumpRate (apertureFor A))
      ccmPrimePoleJumpShift f (Real.log 2) = PrimeCurvatureRankOne.curvatureAtTwo f := by
  have h₂ (F : ℝ → ℝ) := rowFor_eq_old A F (show (2 : ℝ) ∈ probeRows by simp [probeRows])
  have h₁ (F : ℝ → ℝ) := rowFor_eq_old A F (show (1 : ℝ) ∈ probeRows by simp [probeRows])
  have h₃ (F : ℝ → ℝ) := rowFor_eq_old A F (show (2/3 : ℝ) ∈ probeRows by simp [probeRows])
  have h₄ (F : ℝ → ℝ) := rowFor_eq_old A F (show (1/2 : ℝ) ∈ probeRows by simp [probeRows])
  unfold PrimeCurvatureRankOne.curvatureAtTwo
  simp only [gammaTwo, generator_new_row, energy_new_row, generator_old_row, energy_old_row,
    h₂, h₁, h₃, h₄, PrimeCurvatureCounterexample.row_two, PrimeCurvatureCounterexample.row_one,
    PrimeCurvatureCounterexample.row_two_thirds, PrimeCurvatureCounterexample.row_half]

private def sampleRatios : Finset ℝ := {1/2, 2/3, 1, 4/3, 3/2, 2}

private theorem sample_bounds {q : ℝ} (hq : q ∈ sampleRatios) :
    (1/2 : ℝ) ≤ q ∧ q ≤ 2 := by
  simp only [sampleRatios, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private theorem sample_log_interior (A : Scale) {q : ℝ} (hq : q ∈ sampleRatios) :
    |Real.log q| < (apertureFor A).1 := by
  obtain ⟨hlo, hhi⟩ := sample_bounds hq
  have hq0 : 0 < q := by linarith
  have hleft : A.1⁻¹ < q := (inverse_bounds A).2.trans_le hlo
  have hright : q < A.1 := hhi.trans_lt A.2.1
  change |Real.log q| < Real.log A.1
  apply abs_lt.mpr
  constructor
  · simpa only [Real.log_inv] using Real.log_lt_log (inv_pos.mpr (scale_pos A)) hleft
  · exact Real.log_lt_log hq0 hright

def sourceObservable {A : Scale} (g : CCMComplexSmoothInteriorSource (apertureFor A))
    (x : ℝ) : ℝ := (g x).re / primePoleProfile x

/-- Every aperture in the band has the same sharp negative source stencil,
with arbitrarily small actual form norm and complete Weil quadratic. -/
theorem exists_constrained_rankOne_extremizer (A : Scale) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : CCMComplexSmoothInteriorSource (apertureFor A),
      IsPolarConstrained (apertureFor A) g.toCCMFormVector ∧
      ‖g.toCCMFormVector‖ < ε ∧
      |ccmRestrictedWeilSourceQuadratic (apertureFor A) g.toCCMFormVector| < ε ∧
      PrimeCurvatureRankOne.sampleDelta (sourceObservable g) (2/3) = 1 ∧
      gammaTwo (ccmPrimePoleJumpIndices (apertureFor A)) (ccmPrimePoleJumpRate (apertureFor A))
        ccmPrimePoleJumpShift (sourceObservable g) (Real.log 2) = -PrimeCurvatureRankOne.penalty := by
  classical
  obtain ⟨g₀, _, _, _, hB₀, hΓ₀⟩ :=
    PrimeCurvatureCounterexample.exists_constrained_rankOne_curvature_extremizer 1 (by norm_num)
  let f₀ := PrimeCurvatureCounterexample.sourceObservable g₀
  let s := sampleRatios.image Real.log
  obtain ⟨g, hg, hgv, hgn, hgq⟩ := exists_ccmPolarConstrained_finite_interpolant_source_small
    (apertureFor A) s (fun x => (primePoleProfile x * f₀ x : ℝ))
    (by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      exact sample_log_interior A hq) ε hε
  have hsamples : ∀ q ∈ sampleRatios,
      sourceObservable g (Real.log q) = f₀ (Real.log q) := by
    intro q hq
    have hv := hgv (Real.log q) (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
    rw [sourceObservable, hv, Complex.ofReal_re]
    exact mul_div_cancel_left₀ _ (primePoleProfile_pos _).ne'
  refine ⟨g, hg, hgn, hgq, ?_, ?_⟩
  · rw [PrimeCurvatureRankOne.sampleDelta,
      hsamples (2/3) (by simp [sampleRatios]), hsamples 2 (by simp [sampleRatios])]
    exact hB₀
  · rw [gammaTwo_eq_fixed]
    exact (PrimeCurvatureCounterexample.gammaTwo_six_sample_congr _ _ hsamples).trans hΓ₀

/-- Sharp compensation is independent of aperture throughout the plateau,
even on each arbitrarily small exact constrained source ball. -/
theorem constrained_rankOne_compensation_iff (A : Scale) (c ε : ℝ) (hε : 0 < ε) :
    (∀ g : CCMComplexSmoothInteriorSource (apertureFor A),
      IsPolarConstrained (apertureFor A) g.toCCMFormVector → ‖g.toCCMFormVector‖ < ε →
      -c * (PrimeCurvatureRankOne.sampleDelta (sourceObservable g) (2/3))^2 ≤
        gammaTwo (ccmPrimePoleJumpIndices (apertureFor A)) (ccmPrimePoleJumpRate (apertureFor A))
          ccmPrimePoleJumpShift (sourceObservable g) (Real.log 2)) ↔
    PrimeCurvatureRankOne.penalty ≤ c := by
  constructor
  · intro h
    obtain ⟨g, hg, hgn, _, hB, hΓ⟩ := exists_constrained_rankOne_extremizer A ε hε
    have hb := h g hg hgn
    rw [hB, hΓ] at hb
    norm_num at hb
    linarith
  · intro hc g _ _
    rw [gammaTwo_eq_fixed]
    exact (mul_le_mul_of_nonneg_right (neg_le_neg hc) (sq_nonneg _)).trans
      (PrimeCurvatureRankOne.curvatureAtTwo_ge_rankOne (sourceObservable g))

/-- Local nonnegative prime curvature leaves the actual ground floor accessible
at every aperture in the band. -/
theorem exists_nonnegative_curvature_near_ground (A : Scale) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : CCMComplexSmoothInteriorSource (apertureFor A),
      IsPolarConstrained (apertureFor A) g.toCCMFormVector ∧
      g (Real.log 2) = 0 ∧ g (Real.log (2/3)) = 0 ∧
      ccmArchimedeanFormToAperture (apertureFor A) g.toCCMFormVector ≠ 0 ∧
      ccmRestrictedWeilSourceQuadratic (apertureFor A) g.toCCMFormVector /
        ‖ccmArchimedeanFormToAperture (apertureFor A) g.toCCMFormVector‖^2 <
          ccmRestrictedWeilPolarGroundEnergy (apertureFor A) + ε ∧
      0 ≤ gammaTwo (ccmPrimePoleJumpIndices (apertureFor A))
        (ccmPrimePoleJumpRate (apertureFor A)) ccmPrimePoleJumpShift (sourceObservable g) (Real.log 2) := by
  classical
  let s : Finset ℝ := {Real.log 2, Real.log (2/3)}
  have hs : ∀ x ∈ s, |x| < (apertureFor A).1 := by
    intro x hx
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact sample_log_interior A (by simp [sampleRatios])
    · exact sample_log_interior A (by simp [sampleRatios])
  obtain ⟨g, hg, hgv, hgne, hgR⟩ := exists_ccmPolarConstrained_sampled_rayleigh_lt
    (apertureFor A) s (fun _ => 0) hs hε
  have h₂ : g (Real.log 2) = 0 := hgv _ (by simp [s])
  have h₃ : g (Real.log (2/3)) = 0 := hgv _ (by simp [s])
  refine ⟨g, hg, h₂, h₃, hgne, hgR, ?_⟩
  rw [gammaTwo_eq_fixed]
  apply PrimeCurvatureRankOne.curvatureAtTwo_nonneg_of_sample_eq
  simp [sourceObservable, h₂, h₃]

end RHTower.PrimeCurvatureAperturePlateau
