import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.OneCriticalMultiplePaysEveryWindow
import GaloisForLFunctions.WindowTowerOfSpecZ.TheExactPoleCapacityOfAWindow
import GaloisForLFunctions.SignedWindowCriticality.OnReflectionPairsTheCouplingIsTheSmoothedPrimeCount
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheHodgeIndexAtGrowingOverlap
import GaloisForLFunctions.ArchimedeanTateDomination.FirstFoldStageDomination

/-!
# The critical threshold of a window

Along the critical curve `c⁸ = R log N` a window test `H` with `Q(H) < 0` has the exact critical
multiple `R*(H) = 7J(1) M₈(H)/(a_φ |Q(H)|)`, `M₈(H) = ∫ e^{−8y} H²` (`criticalMultiple_exact`). The
**threshold** of the window `[−A, 0]` is `R₁(A) = inf R*(H)` over its tests with `Q(H) < 0`
(`windowThreshold`, `⊤` if there are none).

* **The threshold is the critical multiple of the window** (`pencil_pos_of_lt_windowThreshold`,
  `le_windowThreshold_of_pencil_pos`, `eventually_pos_of_lt_windowThreshold`,
  `exists_eventually_neg_of_windowThreshold_lt`). Below `R₁(A)` the pencil
  `a_φ Q(H) + (7J(1)/R) M₈(H)` is positive on every nonzero test and every horizon block of the window is
  eventually positive along the critical curve; above it some test of the window is eventually
  negative. A multiple at which the pencil is positive on the whole window is `≤ R₁(A)`.
* **Order** (`windowThreshold_antitone`). `R₁` is nonincreasing in `A`.
* **Positivity** (`windowThreshold_eq_top_iff`, `windowThreshold_eq_top_of_le_enlarged`). `R₁(A) = ⊤`
  iff `Q ≥ 0` on the window; this holds for every `A ≤ 2·enlargedWeilFloorAperture`, past `log 2`.
* **Floors** (`apertureIndependentThreshold_le_windowThreshold`,
  `sharpThreshold_le_windowThreshold`). `R₁(A) ≥ R₀ = 7J(1)/(a_φ C(8))` for every `A` (the
  aperture-independent floor), and `R₁(A) ≥ 7J(1)/(a_φ S(A))` (the sharp window floor
  `S(A) = deg K_A + 2 sinh(A/2) − A`).
* **RH** (`riemannHypothesis_iff_windowThreshold_eq_top`). RH holds iff `R₁(A) = ⊤` for every `A`.
-/

noncomputable section

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis CohomologyOfWindowsOfSpecZ WindowTowerOfSpecZ

/-- The atom normalization `a_φ = (∫φ)²/∫φ²` of the tilted spline. -/
def splineAtom : ℝ := (∫ u, tiltedUnitSpline u) ^ 2 / ∫ u, tiltedUnitSpline u ^ 2

theorem splineAtom_pos : 0 < splineAtom :=
  div_pos (pow_pos RenormalizedIntersectionTheory.integral_tiltedUnitSpline_pos 2)
    integral_tiltedUnitSpline_sq_pos

/-- The critical multiple of a test, `R*(H) = 7 J(1) M₈(H)/(a_φ (−Q(H)))`. -/
def testCriticalMultiple (H : ℝ → ℝ) : ℝ :=
  7 * tiltedJordanOne * exponentialMass 8 H / (splineAtom * -weilQuad H)

/-- **The critical threshold of the window `[−A, 0]`**: the infimum of `R*(H)` over its tests with
`Q(H) < 0`, and `⊤` if there are none. -/
def windowThreshold (A : ℝ) : EReal :=
  ⨅ (H : ℝ → ℝ) (_ : IsWindowTest A H) (_ : weilQuad H < 0), (testCriticalMultiple H : EReal)

/-- The aperture-independent multiple `R₀ = 7J(1)/(a_φ C(8))`. -/
def apertureIndependentThreshold : ℝ :=
  7 * tiltedJordanOne / (splineAtom * exponentialWeilFloor 8)

/-! ### Order and positivity -/

theorem windowThreshold_antitone {A B : ℝ} (hAB : A ≤ B) : windowThreshold B ≤ windowThreshold A :=
  le_iInf fun H => le_iInf fun hH => le_iInf fun hQ =>
    iInf_le_of_le H (iInf_le_of_le (hH.mono hAB) (iInf_le _ hQ))

theorem windowThreshold_eq_top_iff {A : ℝ} :
    windowThreshold A = ⊤ ↔ ∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ weilQuad H := by
  simp only [windowThreshold, iInf_eq_top, EReal.coe_ne_top, imp_false, not_lt]

/-- Windows of length at most `181/250` have threshold `⊤`. -/
theorem windowThreshold_eq_top_of_le {A : ℝ} (hA : A ≤ 181 / 250) : windowThreshold A = ⊤ :=
  windowThreshold_eq_top_iff.mpr fun _ hH =>
    SignedWindowCriticality.weilQuad_nonneg_of_short hH.contDiff hH.hasCompactSupport (c := 0) hA
      fun u hu => hH.vanish u (by simpa using hu)

/-- **Windows up to `2·enlargedWeilFloorAperture` have threshold `⊤`**: the strict floor `1/8000`
past the first prime. -/
theorem windowThreshold_eq_top_of_le_enlarged {A : ℝ}
    (hA : A ≤ 2 * ArithmeticIncidencePositivity.enlargedWeilFloorAperture) :
    windowThreshold A = ⊤ :=
  windowThreshold_eq_top_iff.mpr fun H hH => by
    have h := ArchimedeanTateDomination.weilQuad_ge_one_div_eightThousand_of_le_two_mul_enlargedAperture
      hA hH
    have h0 : 0 ≤ (1 / 8000 : ℝ) * ∫ u, H u ^ 2 :=
      mul_nonneg (by norm_num) (integral_nonneg fun u => sq_nonneg (H u))
    linarith

/-- **RH is the threshold `⊤` on every window.** -/
theorem riemannHypothesis_iff_windowThreshold_eq_top :
    RiemannHypothesis ↔ ∀ A : ℝ, 0 ≤ A → windowThreshold A = ⊤ := by
  rw [riemannHypothesis_iff_windowForm_nonneg]
  exact forall₂_congr fun _ _ => windowThreshold_eq_top_iff.symm

/-! ### Floors -/

/-- A linear floor `−Q ≤ F M₈` bounds the threshold below by `7J(1)/(a_φ F)`. -/
theorem le_windowThreshold_of_floor {A F : ℝ} (hF : 0 < F)
    (hfloor : ∀ H : ℝ → ℝ, IsWindowTest A H → -weilQuad H ≤ F * exponentialMass 8 H) :
    ((7 * tiltedJordanOne / (splineAtom * F) : ℝ) : EReal) ≤ windowThreshold A := by
  refine le_iInf fun H => le_iInf fun hH => le_iInf fun hQ => EReal.coe_le_coe_iff.mpr ?_
  have hq : 0 < -weilQuad H := neg_pos.mpr hQ
  have hM : 0 < exponentialMass 8 H := by
    have := hfloor H hH
    by_contra h
    rw [not_lt] at h
    nlinarith
  have hJ := tiltedJordanOne_pos
  have hκ := splineAtom_pos
  rw [testCriticalMultiple, div_le_div_iff₀ (mul_pos hκ hF) (mul_pos hκ hq)]
  have := hfloor H hH
  have h7 : 0 < 7 * tiltedJordanOne := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this (mul_pos h7 hκ).le]

/-- **The aperture-independent floor**: `R₁(A) ≥ R₀` on every window. -/
theorem apertureIndependentThreshold_le_windowThreshold (A : ℝ) :
    (apertureIndependentThreshold : EReal) ≤ windowThreshold A :=
  le_windowThreshold_of_floor (exponentialWeilFloor_pos (by norm_num)) fun _ hH => by
    linarith [weilQuad_ge_neg_exponentialMass hH (by norm_num : (1 : ℝ) < 8)]

/-- **The sharp floor**: `R₁(A) ≥ 7J(1)/(a_φ S(A))`. -/
theorem sharpThreshold_le_windowThreshold {A : ℝ} (hA : 0 ≤ A) :
    ((7 * tiltedJordanOne / (splineAtom * sharpWindowFloor A) : ℝ) : EReal) ≤ windowThreshold A := by
  have hS : 0 < sharpWindowFloor A := by
    have h := sinh_sub_self_nonneg (x := A / 2) (by linarith)
    have := canonicalDegree_pos A
    rw [sharpWindowFloor]
    linarith
  refine le_windowThreshold_of_floor hS fun H hH => ?_
  have h1 := weilQuad_ge_neg_sharpWindowFloor hH hA
  have h2 := integral_sq_le_exponentialMass hH (by norm_num : (0 : ℝ) ≤ 8)
  nlinarith [mul_le_mul_of_nonneg_left h2 hS.le]

/-! ### The threshold is the critical multiple of the window -/

/-- A nonzero window test has positive exponential mass. -/
theorem exponentialMass_pos {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) (hne : H ≠ 0) :
    0 < exponentialMass 8 H := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hne
  have hc : Continuous fun u => Real.exp (-(8 * u)) * H u ^ 2 := by
    have := hH.continuous; fun_prop
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x) ?_ (fun u => by positivity) ?_
  · exact HasCompactSupport.intro (isCompact_Icc (a := -A) (b := 0))
      fun u hu => by simp [hH.vanish u hu]
  · exact mul_ne_zero (Real.exp_pos _).ne' (pow_ne_zero 2 hx)

/-- The pencil at the multiple `R`. -/
def windowPencil (R : ℝ) (H : ℝ → ℝ) : ℝ :=
  splineAtom * weilQuad H + 7 * tiltedJordanOne / R * exponentialMass 8 H

/-- **Below the threshold the pencil is positive on the window.** -/
theorem pencil_pos_of_lt_windowThreshold {A R : ℝ} (hR : 0 < R)
    (hlt : (R : EReal) < windowThreshold A) {H : ℝ → ℝ} (hH : IsWindowTest A H) (hne : H ≠ 0) :
    0 < windowPencil R H := by
  have hM := exponentialMass_pos hH hne
  have hJ := tiltedJordanOne_pos
  have hκ := splineAtom_pos
  have hpos : 0 < 7 * tiltedJordanOne / R * exponentialMass 8 H := by positivity
  rw [windowPencil]
  by_cases hQ : weilQuad H < 0
  · have hle : windowThreshold A ≤ (testCriticalMultiple H : EReal) :=
      iInf_le_of_le H (iInf_le_of_le hH (iInf_le _ hQ))
    have hR' : R < testCriticalMultiple H := EReal.coe_lt_coe_iff.mp (hlt.trans_le hle)
    have hq : 0 < -weilQuad H := neg_pos.mpr hQ
    rw [testCriticalMultiple, lt_div_iff₀ (mul_pos hκ hq)] at hR'
    have : splineAtom * -weilQuad H < 7 * tiltedJordanOne / R * exponentialMass 8 H := by
      rw [div_mul_eq_mul_div, lt_div_iff₀ hR]; linarith
    linarith
  · rw [not_lt] at hQ
    nlinarith [mul_nonneg hκ.le hQ]

/-- **A multiple with positive pencil on the whole window is at most the threshold.** -/
theorem le_windowThreshold_of_pencil_pos {A R : ℝ} (hR : 0 < R)
    (hpos : ∀ H : ℝ → ℝ, IsWindowTest A H → H ≠ 0 → 0 < windowPencil R H) :
    (R : EReal) ≤ windowThreshold A := by
  refine le_iInf fun H => le_iInf fun hH => le_iInf fun hQ => EReal.coe_le_coe_iff.mpr ?_
  have hne : H ≠ 0 := by
    rintro rfl
    have hf := weilQuad_ge_neg_exponentialMass hH (by norm_num : (1 : ℝ) < 8)
    have h0 : exponentialMass 8 (0 : ℝ → ℝ) = 0 := by simp [exponentialMass]
    rw [h0, mul_zero, neg_zero] at hf
    linarith
  have hp := hpos H hH hne
  have hq : 0 < -weilQuad H := neg_pos.mpr hQ
  have hκ := splineAtom_pos
  rw [windowPencil] at hp
  rw [testCriticalMultiple, le_div_iff₀ (mul_pos hκ hq)]
  have h : splineAtom * -weilQuad H < 7 * tiltedJordanOne / R * exponentialMass 8 H := by linarith
  rw [div_mul_eq_mul_div, lt_div_iff₀ hR] at h
  linarith

/-- The window test `h = e^{−y/2} H`, whose half-weight is `H`. -/
theorem halfWeight_inv {H : ℝ → ℝ} : halfWeight (fun y => Real.exp (-(y / 2)) * H y) = H := by
  funext y
  rw [halfWeight, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

/-- **Below the threshold every horizon block of the window is eventually positive** along the
critical curve `c⁸/log N → R`. -/
theorem eventually_pos_of_lt_windowThreshold {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R)
    (hlt : (R : EReal) < windowThreshold A) {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hne : halfWeight h ≠ 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∀ᶠ N : ℕ in atTop, 0 < (c N)⁻¹ * (weilQuad (ArithmeticElectrostatics.atomicTest N
        (horizonWeights h N) (atomDilate tiltedUnitSpline (c N / N))) /
          ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2) := by
  have hH : IsWindowTest A (halfWeight h) :=
    ⟨contDiff_halfWeight hh, fun y hy => halfWeight_eq_zero_of_window hsupp y hy⟩
  have hp := pencil_pos_of_lt_windowThreshold hR hlt hH hne
  refine (criticalMultiple_exact hh hA hsupp hc1 hR hcrit).1 ?_
  rw [windowPencil, exponentialMass, splineAtom] at hp
  set κ := (∫ u, tiltedUnitSpline u) ^ 2 / ∫ u, tiltedUnitSpline u ^ 2
  set M := ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2
  have h1 : κ * -weilQuad (halfWeight h) < 7 * tiltedJordanOne / R * M := by linarith
  have h2 := mul_lt_mul_of_pos_left h1 hR
  have h3 : R * (7 * tiltedJordanOne / R * M) = 7 * tiltedJordanOne * M := by field_simp
  linarith

/-- **Above the threshold some test of the window is eventually negative** along the critical
curve. -/
theorem exists_eventually_neg_of_windowThreshold_lt {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R)
    (hlt : windowThreshold A < (R : EReal)) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∃ h : ℝ → ℝ, ContDiff ℝ 2 h ∧ (∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) ∧
      ∀ᶠ N : ℕ in atTop, (c N)⁻¹ * (weilQuad (ArithmeticElectrostatics.atomicTest N
        (horizonWeights h N) (atomDilate tiltedUnitSpline (c N / N))) /
          ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2) < 0 := by
  simp only [windowThreshold, iInf_lt_iff] at hlt
  obtain ⟨H, hH, hQ, hRH⟩ := hlt
  have hR' : testCriticalMultiple H < R := EReal.coe_lt_coe_iff.mp hRH
  set h : ℝ → ℝ := fun y => Real.exp (-(y / 2)) * H y
  have hh : ContDiff ℝ 2 h := (Real.contDiff_exp.comp (by fun_prop)).mul hH.contDiff
  have hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0 := fun y hy => by
    simp only [h, hH.vanish y hy, mul_zero]
  refine ⟨h, hh, hsupp, (criticalMultiple_exact hh hA hsupp hc1 hR hcrit).2 ?_⟩
  rw [show halfWeight h = H from halfWeight_inv]
  have hq : 0 < -weilQuad H := neg_pos.mpr hQ
  have hκ := splineAtom_pos
  rw [testCriticalMultiple, div_lt_iff₀ (mul_pos hκ hq)] at hR'
  rw [exponentialMass] at hR'
  unfold splineAtom at hR'
  linarith

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
