import GaloisForLFunctions.RHTower.CCMInwardRegularizationFloor
import GaloisForLFunctions.RHTower.SuzukiAdmissibleTwoShiftAffineSewing

/-!
# Transverse evacuation of every admissible Suzuki shift

Suzuki admissibility requires the shift to lie strictly below the restricted-Weil floor.  The
inward-regularization floor theorem therefore has an immediate but stronger consequence than the
known zero-shift criterion: under false RH every admissible shift schedule has arbitrarily late
negative excursions beyond every subcritical transverse power.  In particular, existence of an
eventually bounded-below admissible schedule is equivalent to RH.
-/

open Complex Filter Function Set
open scoped Topology

namespace RHTower

noncomputable section

/-- Pointwise Suzuki admissibility of a sampled shift below the sampled spectral floor. -/
def SuzukiSampledAdmissibleShift (floor shift : ℕ → ℝ) : Prop :=
  ∀ n, shift n < floor n

/-- A sampled shift schedule has one absolute lower bound on an aperture tail. -/
def SuzukiShiftEventuallyBoundedBelow (shift : ℕ → ℝ) : Prop :=
  ∃ B : ℝ, ∀ᶠ n : ℕ in atTop, B ≤ shift n

/-- **Quantitative evacuation.** Under false RH every admissible Suzuki shift schedule falls below
every subcritical negative transverse power at arbitrarily late logarithmic apertures. -/
theorem not_riemannHypothesis_implies_every_admissibleSuzukiShift_cofinally_below_neg_power
    {L alpha : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha)
    (hRH : ¬RiemannHypothesis) (halpha : alpha < xiRightTransverseSup)
    {N : ℕ} {floor shift : ℕ → ℝ}
    (henv : XiRestrictedWeilNegativeFloorEnvelope L N
      (inwardRestrictedWeilNegativeFloor floor))
    (hadmissible : SuzukiSampledAdmissibleShift floor shift) :
    ∀ C : ℝ, 0 ≤ C → ∀ N0 : ℕ, ∃ n : ℕ,
      N0 ≤ n ∧ L ≤ Real.log n / 2 ∧
        shift n < -(C * (n : ℝ) ^ alpha) := by
  intro C hC N0
  obtain ⟨n, hn0, hLa, hfloor⟩ :=
    not_riemannHypothesis_implies_inwardRestrictedWeilFloor_cofinally_exceeds_power
      hL halpha0 hRH halpha henv C hC N0
  refine ⟨n, hn0, hLa, ?_⟩
  have hpow0 : 0 ≤ C * (n : ℝ) ^ alpha :=
    mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg n) alpha)
  have hnegFloor : C * (n : ℝ) ^ alpha < -floor n := by
    rw [inwardRestrictedWeilNegativeFloor, negPart_def] at hfloor
    by_cases hf : 0 ≤ -floor n
    · simpa [max_eq_left hf] using hfloor
    · rw [max_eq_right (le_of_not_ge hf)] at hfloor
      linarith
  have hadm := hadmissible n
  linarith

/-- Inward regularization supplies the quantitative shift-evacuation law directly from the
variational definition of the sampled restricted-Weil floor. -/
theorem not_riemannHypothesis_implies_every_inwardAdmissibleSuzukiShift_cofinally_below_neg_power
    {L alpha : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha)
    (hRH : ¬RiemannHypothesis) (halpha : alpha < xiRightTransverseSup)
    {N : ℕ} {floor shift : ℕ → ℝ}
    (hvariational : ∀ n : ℕ, ∀ᶠ epsilon : ℝ in 𝓝[>] 0,
      floor n * inwardRegularizedTwoEdgeSquaredMass L epsilon ≤
        (xiWeilPolarization
          (inwardRegularizedXiTwoEdgeTransform L (Real.log n / 2) epsilon)
          (inwardRegularizedXiTwoEdgeTransform L (Real.log n / 2) epsilon)).re)
    (hadmissible : SuzukiSampledAdmissibleShift floor shift) :
    ∀ C : ℝ, 0 ≤ C → ∀ N0 : ℕ, ∃ n : ℕ,
      N0 ≤ n ∧ L ≤ Real.log n / 2 ∧
        shift n < -(C * (n : ℝ) ^ alpha) := by
  exact not_riemannHypothesis_implies_every_admissibleSuzukiShift_cofinally_below_neg_power
    hL halpha0 hRH halpha
      (xiRestrictedWeilNegativeFloorEnvelope_of_inwardRegularization
        hL N floor hvariational)
      hadmissible

/-- An eventually bounded-below admissible schedule contradicts false-RH floor amplification. -/
theorem riemannHypothesis_of_exists_eventuallyBoundedBelow_admissibleSuzukiShift
    {L : ℝ} (hL : 0 < L) {N : ℕ} {floor : ℕ → ℝ}
    (hvariational : ∀ n : ℕ, ∀ᶠ epsilon : ℝ in 𝓝[>] 0,
      floor n * inwardRegularizedTwoEdgeSquaredMass L epsilon ≤
        (xiWeilPolarization
          (inwardRegularizedXiTwoEdgeTransform L (Real.log n / 2) epsilon)
          (inwardRegularizedXiTwoEdgeTransform L (Real.log n / 2) epsilon)).re)
    (hexists : ∃ shift : ℕ → ℝ,
      SuzukiSampledAdmissibleShift floor shift ∧
        SuzukiShiftEventuallyBoundedBelow shift) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨shift, hadmissible, B, hbound⟩ := hexists
  rw [eventually_atTop] at hbound
  obtain ⟨N0, hbound⟩ := hbound
  have hne := nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
  let C : ℝ := max (-B) 0 + 1
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  obtain ⟨n, hn0, _hLa, hfloor⟩ :=
    not_riemannHypothesis_implies_inwardRestrictedWeilFloor_cofinally_exceeds_power
      hL (alpha := 0) le_rfl hRH (xiRightTransverseSup_pos hne)
      (xiRestrictedWeilNegativeFloorEnvelope_of_inwardRegularization
        hL N floor hvariational)
      C hC N0
  have hBfloor : B < floor n := lt_of_le_of_lt (hbound n hn0) (hadmissible n)
  have hmax : max (-floor n) 0 ≤ max (-B) 0 :=
    max_le_max (neg_le_neg hBfloor.le) le_rfl
  rw [inwardRestrictedWeilNegativeFloor, negPart_def] at hfloor
  simp only [Real.rpow_zero, mul_one] at hfloor
  dsimp only [C] at hfloor
  linarith

/-- **Bounded-shift completeness.** A bounded-below admissible Suzuki shift schedule exists exactly
under RH. Under RH the constant shift `-1` works; the converse is the evacuation theorem. -/
theorem riemannHypothesis_iff_exists_eventuallyBoundedBelow_admissibleSuzukiShift
    {L : ℝ} (hL : 0 < L) {N : ℕ} {floor : ℕ → ℝ}
    (hvariational : ∀ n : ℕ, ∀ᶠ epsilon : ℝ in 𝓝[>] 0,
      floor n * inwardRegularizedTwoEdgeSquaredMass L epsilon ≤
        (xiWeilPolarization
          (inwardRegularizedXiTwoEdgeTransform L (Real.log n / 2) epsilon)
          (inwardRegularizedXiTwoEdgeTransform L (Real.log n / 2) epsilon)).re)
    (hpositive : RiemannHypothesis → ∀ n, 0 ≤ floor n) :
    RiemannHypothesis ↔
      ∃ shift : ℕ → ℝ,
        SuzukiSampledAdmissibleShift floor shift ∧
          SuzukiShiftEventuallyBoundedBelow shift := by
  constructor
  · intro hRH
    refine ⟨fun _ => -1, ?_, ?_⟩
    · intro n
      linarith [hpositive hRH n]
    · refine ⟨-1, ?_⟩
      filter_upwards with n
      exact le_rfl
  · exact riemannHypothesis_of_exists_eventuallyBoundedBelow_admissibleSuzukiShift
      hL (N := N) hvariational

/-! ## Conditioning of the canonical two-shift affine reconstruction -/

/-- First canonical real shift one unit below an arbitrary spectral floor. -/
def suzukiCanonicalFirstShiftBelowFloor (floor : ℝ) : ℝ := floor - 1

/-- Second canonical real shift two units below an arbitrary spectral floor. -/
def suzukiCanonicalSecondShiftBelowFloor (floor : ℝ) : ℝ := floor - 2

theorem suzukiCanonicalFirstShiftBelowFloor_lt (floor : ℝ) :
    suzukiCanonicalFirstShiftBelowFloor floor < floor := by
  simp [suzukiCanonicalFirstShiftBelowFloor]

theorem suzukiCanonicalSecondShiftBelowFloor_lt (floor : ℝ) :
    suzukiCanonicalSecondShiftBelowFloor floor < floor := by
  simp [suzukiCanonicalSecondShiftBelowFloor]

/-- Lagrange coefficient of the first source quotient when the two canonical below-floor shifts
are affinely sewn to target shift zero. -/
def suzukiCanonicalFirstZeroTargetCoefficient (floor : ℝ) : ℂ :=
  suzukiCenteredShiftParameter (suzukiCanonicalSecondShiftBelowFloor floor) /
    (suzukiCenteredShiftParameter (suzukiCanonicalSecondShiftBelowFloor floor) -
      suzukiCenteredShiftParameter (suzukiCanonicalFirstShiftBelowFloor floor))

/-- Lagrange coefficient of the second source quotient in the same zero-target reconstruction. -/
def suzukiCanonicalSecondZeroTargetCoefficient (floor : ℝ) : ℂ :=
  -suzukiCenteredShiftParameter (suzukiCanonicalFirstShiftBelowFloor floor) /
    (suzukiCenteredShiftParameter (suzukiCanonicalSecondShiftBelowFloor floor) -
      suzukiCenteredShiftParameter (suzukiCanonicalFirstShiftBelowFloor floor))

/-- The canonical first affine coefficient has exact norm `|floor-2|`. -/
theorem norm_suzukiCanonicalFirstZeroTargetCoefficient (floor : ℝ) :
    ‖suzukiCanonicalFirstZeroTargetCoefficient floor‖ = |floor - 2| := by
  have hden :
      suzukiCenteredShiftParameter (suzukiCanonicalSecondShiftBelowFloor floor) -
          suzukiCenteredShiftParameter (suzukiCanonicalFirstShiftBelowFloor floor) = I := by
    simp only [suzukiCenteredShiftParameter, suzukiCanonicalSecondShiftBelowFloor,
      suzukiCanonicalFirstShiftBelowFloor]
    push_cast
    ring
  rw [suzukiCanonicalFirstZeroTargetCoefficient, hden, norm_div, norm_I, div_one]
  simp only [suzukiCenteredShiftParameter, suzukiCanonicalSecondShiftBelowFloor,
    norm_mul, norm_neg, norm_I, one_mul, norm_real, Real.norm_eq_abs]

/-- The canonical second affine coefficient has exact norm `|floor-1|`. -/
theorem norm_suzukiCanonicalSecondZeroTargetCoefficient (floor : ℝ) :
    ‖suzukiCanonicalSecondZeroTargetCoefficient floor‖ = |floor - 1| := by
  have hden :
      suzukiCenteredShiftParameter (suzukiCanonicalSecondShiftBelowFloor floor) -
          suzukiCenteredShiftParameter (suzukiCanonicalFirstShiftBelowFloor floor) = I := by
    simp only [suzukiCenteredShiftParameter, suzukiCanonicalSecondShiftBelowFloor,
      suzukiCanonicalFirstShiftBelowFloor]
    push_cast
    ring
  rw [suzukiCanonicalSecondZeroTargetCoefficient, hden, norm_div, norm_I, div_one]
  simp only [norm_neg, suzukiCenteredShiftParameter, suzukiCanonicalFirstShiftBelowFloor,
    norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs]

/-- **Affine extrapolation is transversely ill-conditioned under false RH.** Both canonical
zero-target Lagrange coefficients exceed every subcritical power scale at arbitrarily late
logarithmic apertures. -/
theorem not_riemannHypothesis_implies_canonicalSuzukiAffineCoefficients_cofinally_exceed_power
    {L alpha : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha)
    (hRH : ¬RiemannHypothesis) (halpha : alpha < xiRightTransverseSup)
    {N : ℕ} {floor : ℕ → ℝ}
    (henv : XiRestrictedWeilNegativeFloorEnvelope L N
      (inwardRestrictedWeilNegativeFloor floor)) :
    ∀ C : ℝ, 0 ≤ C → ∀ N0 : ℕ, ∃ n : ℕ,
      N0 ≤ n ∧ L ≤ Real.log n / 2 ∧
        C * (n : ℝ) ^ alpha <
          ‖suzukiCanonicalFirstZeroTargetCoefficient (floor n)‖ ∧
        C * (n : ℝ) ^ alpha <
          ‖suzukiCanonicalSecondZeroTargetCoefficient (floor n)‖ := by
  intro C hC N0
  obtain ⟨n, hn0, hLa, hfloor⟩ :=
    not_riemannHypothesis_implies_inwardRestrictedWeilFloor_cofinally_exceeds_power
      hL halpha0 hRH halpha henv C hC N0
  have hpow0 : 0 ≤ C * (n : ℝ) ^ alpha :=
    mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg n) alpha)
  have hnegFloor : C * (n : ℝ) ^ alpha < -floor n := by
    rw [inwardRestrictedWeilNegativeFloor, negPart_def] at hfloor
    by_cases hf : 0 ≤ -floor n
    · simpa [max_eq_left hf] using hfloor
    · rw [max_eq_right (le_of_not_ge hf)] at hfloor
      linarith
  refine ⟨n, hn0, hLa, ?_, ?_⟩
  · rw [norm_suzukiCanonicalFirstZeroTargetCoefficient]
    calc
      C * (n : ℝ) ^ alpha < -floor n := hnegFloor
      _ ≤ -(floor n - 2) := by linarith
      _ ≤ |floor n - 2| := neg_le_abs (floor n - 2)
  · rw [norm_suzukiCanonicalSecondZeroTargetCoefficient]
    calc
      C * (n : ℝ) ^ alpha < -floor n := hnegFloor
      _ ≤ -(floor n - 1) := by linarith
      _ ≤ |floor n - 1| := neg_le_abs (floor n - 1)

end

end RHTower
