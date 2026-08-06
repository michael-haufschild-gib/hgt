/-
The remaining method ceilings of the Lindelöf frontier, and the coincidences at `v = 1/8`.

Four independent constraints on a large-value exponent meet at the same point.

1. **Two large-value lines.**  The fourth moment gives `φ v ≥ 4v` and the twelfth moment gives
   `φ v ≥ 12v - 1`.  The two lines cross exactly at `v = 1/8`, where both equal `1/2` — the plateau
   value of the chord–pivot law.
2. **Halász–Montgomery at the self-dual block.**  At the length of the `ζ²` polynomial the amplitude
   demand `T^{4v}` meets the square-root size `T^{1/2}` of the Gram off-diagonal exactly at
   `v = 1/8`.
3. **The forced block size.**  A value `T^v` forces the critical Dirichlet block to have size
   `N^{1/2+2v}`, which is `N^{3/4}` exactly at `v = 1/8`.
4. **The chord–pivot plateau**, proved in `MomentChordPivot`.

Three further ceilings are recorded here.

* **Mean-value criticality.**  The `2k`-th moment is bounded by `T^{1+ε}` exactly from the abscissa
  `1 - 1/k`, and the pointwise exponent it yields there, `1/(2k)`, is *equal* to the
  Phragmén–Lindelöf value `(1-σ)/2` at that abscissa: the mean-value route traces the convexity line
  with no slack.
* **The Halász–Montgomery cap.**  Perfect square-root cancellation makes the measure exponent
  `1 - 4v`, which is the fourth-moment bound read backwards and nothing more.
* **Guth–Maynard inertness.**  At the self-dual block `β = 1` the two Guth–Maynard terms fall below
  the classical term exactly for `v ≥ 3/20`, and above it otherwise; so the Guth–Maynard maximum is
  never smaller than the classical bound, and the best available bound is the classical one at every
  `v`.  Since `β = 1` always binds, Guth–Maynard cannot move `φ`, any moment, or `μ`.
* **Heath-Brown's twelfth-moment window.**  The short second moment at length `G = T^{2v}` is
  available exactly on `T^{1/4} ≤ G ≤ T^{1/3}`, i.e. exactly on `v ∈ [1/8, 1/6]`, which is the
  window on which `m(6) = 2` is attained.

The module is source-independent: every statement is arithmetic of exponents.
-/
import GaloisForLFunctions.HTGeometry.MomentChordPivot
import GaloisForLFunctions.HTGeometry.ShiftAverageTransfer

namespace HTGeometry

/-! ### The four coincidences at `v = 1/8` -/

/-- Fourth-moment constraint on the large-value exponent. -/
noncomputable def fourthMomentPhi (v : ℝ) : ℝ := 4 * v

/-- Heath-Brown twelfth-moment constraint on the large-value exponent. -/
noncomputable def heathBrownPhi (v : ℝ) : ℝ := 12 * v - 1

theorem phi_lines_cross_iff (v : ℝ) : fourthMomentPhi v = heathBrownPhi v ↔ v = 1/8 := by
  unfold fourthMomentPhi heathBrownPhi
  constructor <;> intro h <;> linarith

theorem phi_lines_cross_value :
    fourthMomentPhi (1/8) = 1/2 ∧ heathBrownPhi (1/8) = 1/2 := by
  unfold fourthMomentPhi heathBrownPhi
  norm_num

/-- Below the pivot the twelfth-moment line is the weaker constraint; above it, the stronger. -/
theorem heathBrownPhi_lt_fourthMomentPhi_iff (v : ℝ) :
    heathBrownPhi v < fourthMomentPhi v ↔ v < 1/8 := by
  unfold fourthMomentPhi heathBrownPhi
  constructor <;> intro h <;> linarith

/-- The certified large-value exponent is the larger of the two lines. -/
noncomputable def certifiedPhi (v : ℝ) : ℝ := max (fourthMomentPhi v) (heathBrownPhi v)

theorem certifiedPhi_at_pivot : certifiedPhi (1/8) = 1/2 := by
  unfold certifiedPhi
  rw [phi_lines_cross_value.1, phi_lines_cross_value.2, max_self]

/-- The certified value at the pivot is exactly the chord–pivot plateau value. -/
theorem certifiedPhi_pivot_eq_plateau (A : ℝ) :
    certifiedPhi (1/8) = pivotGain momentChord A := by
  rw [certifiedPhi_at_pivot, pivotGain_momentChord]

/-- Amplitude exponent demanded by Halász–Montgomery at the self-dual block. -/
noncomputable def halaszAmplitude (v : ℝ) : ℝ := 4 * v

/-- Square-root cancellation size of the Gram off-diagonal at the self-dual length `N ≍ T`. -/
noncomputable def gramSquareRootSize : ℝ := 1/2

theorem halasz_selfDual_balance_iff (v : ℝ) :
    halaszAmplitude v = gramSquareRootSize ↔ v = 1/8 := by
  unfold halaszAmplitude gramSquareRootSize
  constructor <;> intro h <;> linarith

/-- Size exponent, in units of `log N`, forced on the critical Dirichlet block by a value `T^v`. -/
noncomputable def forcedBlockExponent (v : ℝ) : ℝ := 1/2 + 2 * v

/-- The Guth–Maynard threshold `N^{3/4}` is reached exactly at the pivot. -/
theorem forcedBlockExponent_threshold_iff (v : ℝ) :
    forcedBlockExponent v = 3/4 ↔ v = 1/8 := by
  unfold forcedBlockExponent
  constructor <;> intro h <;> linarith

/-- **The pivot is one point.**  The three numerical coincidences and the chord–pivot plateau are
constraints that all become critical at the same `v`, with the same value `1/2`. -/
theorem pivot_coincidences :
    (∀ v : ℝ, fourthMomentPhi v = heathBrownPhi v ↔ v = 1/8) ∧
    (∀ v : ℝ, halaszAmplitude v = gramSquareRootSize ↔ v = 1/8) ∧
    (∀ v : ℝ, forcedBlockExponent v = 3/4 ↔ v = 1/8) ∧
    certifiedPhi (1/8) = 1/2 ∧
    (∀ A : ℝ, pivotGain momentChord A = 1/2) :=
  ⟨phi_lines_cross_iff, halasz_selfDual_balance_iff, forcedBlockExponent_threshold_iff,
    certifiedPhi_at_pivot, pivotGain_momentChord⟩

/-! ### Mean-value criticality -/

/-- Phragmén–Lindelöf convexity value at abscissa `σ`. -/
noncomputable def convexityExponent (σ : ℝ) : ℝ := (1 - σ) / 2

/-- Abscissa from which the `2k`-th moment is bounded by `T^{1+ε}`. -/
noncomputable def meanValueAbscissa (k : ℝ) : ℝ := 1 - 1/k

/-- Pointwise exponent produced by a `T^{1+ε}` bound on the `2k`-th moment. -/
noncomputable def meanValueOutput (k : ℝ) : ℝ := 1 / (2*k)

/-- **Mean-value criticality.**  The pointwise exponent produced by the `2k`-th mean value at its
own abscissa is exactly the convexity value there: the route traces the Phragmén–Lindelöf line with
no slack, at every `k`. -/
theorem meanValue_traces_convexity {k : ℝ} (hk : k ≠ 0) :
    convexityExponent (meanValueAbscissa k) = meanValueOutput k := by
  unfold convexityExponent meanValueAbscissa meanValueOutput
  field_simp
  ring

/-- Off its own abscissa the mean-value route is strictly worse than convexity on the left and
strictly better on the right — so equality at the abscissa is not an artefact of the normalisation
but the unique crossing. -/
theorem meanValue_crosses_convexity_iff {k σ : ℝ} (hk : k ≠ 0) :
    convexityExponent σ = meanValueOutput k ↔ σ = meanValueAbscissa k := by
  unfold convexityExponent meanValueOutput meanValueAbscissa
  rw [div_eq_div_iff (by norm_num) (by simpa using mul_ne_zero two_ne_zero hk)]
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    subst h
    field_simp
    ring

/-! ### The Halász–Montgomery cap -/

/-- Measure exponent produced by Halász–Montgomery granting perfect square-root cancellation. -/
noncomputable def halaszMeasureExponent (v : ℝ) : ℝ := 1 - 4 * v

/-- **Halász–Montgomery cap.**  The exponent it produces is the fourth-moment large-value bound
read backwards, and nothing more. -/
theorem halasz_is_fourthMoment (v : ℝ) :
    halaszMeasureExponent v = 1 - fourthMomentPhi v := by
  unfold halaszMeasureExponent fourthMomentPhi
  ring

/-! ### Guth–Maynard inertness at the self-dual block -/

/-- First Guth–Maynard term at block length `N = T^β`. -/
noncomputable def gmFirst (β v : ℝ) : ℝ := 8*β/5 - 8*v

/-- Second Guth–Maynard term at block length `N = T^β`. -/
noncomputable def gmSecond (β v : ℝ) : ℝ := 1 + 2*β/5 - 8*v

/-- Classical large-value measure exponent. -/
noncomputable def classicalMeasureExponent (v : ℝ) : ℝ := 1 - 4*v

/-- The Guth–Maynard bound is the maximum of its own two terms and the classical term. -/
noncomputable def guthMaynardBound (β v : ℝ) : ℝ :=
  max (max (gmFirst β v) (gmSecond β v)) (classicalMeasureExponent v)

theorem gmSecond_le_gmFirst_selfDual (v : ℝ) : gmSecond 1 v ≤ gmFirst 1 v := by
  unfold gmSecond gmFirst
  linarith

theorem guthMaynardBound_selfDual (v : ℝ) :
    guthMaynardBound 1 v = max (gmFirst 1 v) (classicalMeasureExponent v) := by
  unfold guthMaynardBound
  rw [max_eq_left (gmSecond_le_gmFirst_selfDual v)]

/-- The Guth–Maynard terms fall below the classical term exactly from `v = 3/20`. -/
theorem gmFirst_le_classical_iff (v : ℝ) :
    gmFirst 1 v ≤ classicalMeasureExponent v ↔ 3/20 ≤ v := by
  unfold gmFirst classicalMeasureExponent
  constructor <;> intro h <;> linarith

/-- The Guth–Maynard bound never improves on the classical bound. -/
theorem classical_le_guthMaynardBound (β v : ℝ) :
    classicalMeasureExponent v ≤ guthMaynardBound β v :=
  le_max_right _ _

/-- **Guth–Maynard inertness.**  At the self-dual block the best available bound is the classical
one at every `v`: the Guth–Maynard maximum can only be larger. -/
theorem guthMaynard_inert (v : ℝ) :
    min (guthMaynardBound 1 v) (classicalMeasureExponent v) =
      classicalMeasureExponent v :=
  min_eq_right (classical_le_guthMaynardBound 1 v)

/-- Exactly on the range where its terms fall below the classical one, the Guth–Maynard bound *is*
the classical bound. -/
theorem guthMaynardBound_eq_classical_iff (v : ℝ) :
    guthMaynardBound 1 v = classicalMeasureExponent v ↔ 3/20 ≤ v := by
  rw [guthMaynardBound_selfDual]
  constructor
  · intro h
    refine (gmFirst_le_classical_iff v).1 ?_
    exact h ▸ le_max_left _ _
  · intro h
    exact max_eq_right ((gmFirst_le_classical_iff v).2 h)

/-! ### The twelfth-moment window -/

/-- Length exponent of the short second moment attached to a value `T^v`. -/
noncomputable def shortSecondMomentLength (v : ℝ) : ℝ := 2 * v

/-- **Heath-Brown's method sits at its input's ceiling.**  The short second moment is available at
length `G = T^{2v}` exactly for `T^{1/4} ≤ G ≤ T^{1/3}`, which is exactly the window
`v ∈ [1/8, 1/6]` on which the twelfth-moment bound is attained.  Its lower end is the pivot and is
sharp, because `E(T) = Ω(T^{1/4})` makes the short second moment fail below it. -/
theorem heathBrown_window_iff (v : ℝ) :
    (1/4 ≤ shortSecondMomentLength v ∧ shortSecondMomentLength v ≤ 1/3) ↔
      (1/8 ≤ v ∧ v ≤ 1/6) := by
  unfold shortSecondMomentLength
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- The lower end of the twelfth-moment window is the pivot. -/
theorem heathBrown_window_lower_is_pivot :
    shortSecondMomentLength (1/8) = 1/4 := by
  unfold shortSecondMomentLength
  norm_num

/-! ### The values the capped routes deliver -/

/-- A perfect fourth moment — the ceiling of the mean-value/large-sieve route and of
Halász–Montgomery — delivers `1/4`. -/
theorem meanValueOutput_two : meanValueOutput 2 = 1/4 := by
  unfold meanValueOutput; norm_num

/-- A perfect sixth moment — the ceiling of `GL(3)` subconvexity for `ζ³` — delivers `1/6`. -/
theorem meanValueOutput_three : meanValueOutput 3 = 1/6 := by
  unfold meanValueOutput; norm_num

/-- A perfect eighth moment — the first index above the neutrality threshold — delivers `1/8`. -/
theorem meanValueOutput_four : meanValueOutput 4 = 1/8 := by
  unfold meanValueOutput; norm_num

/-- The convexity value on the critical line is `1/4`: the mean-value route's own ceiling. -/
theorem convexityExponent_half : convexityExponent (1/2) = 1/4 := by
  unfold convexityExponent; norm_num

/-! ### The short-interval mean square is neutral at its optimum and worse away from it -/

/-- Ivić's proved short-interval variance `x h^{4/3}`, read in transfer coordinates. -/
noncomputable def shortIntervalVarianceInput : ℝ × ℝ := (2/3, 1)

theorem shortIntervalVariance_transfer_three :
    transferBound 3 (2/3) 1 = 4/3 := by
  unfold transferBound
  rw [max_eq_right (by norm_num)]
  norm_num

theorem shortIntervalVariance_transfer_six :
    transferBound 6 (2/3) 1 = 7/3 := by
  unfold transferBound
  rw [max_eq_right (by norm_num)]
  norm_num

theorem momentChord_six : momentChord (2*(3:ℝ)) = 5/4 := by
  unfold momentChord; norm_num

theorem momentChord_twelve : momentChord (2*(6:ℝ)) = 2 := by
  unfold momentChord; norm_num

/-- **The proved short-interval variance is strictly worse than the known envelope.**  Ivić's
`x h^{4/3}` yields `m(3) ≤ 4/3` and `m(6) ≤ 7/3`, both strictly above the chord values `5/4` and
`2`.  Its conjecturally optimal value `x h^{1+ε}` — which Ivić calls unattainable for `k > 2` —
reproduces the chord exactly and so would improve nothing. -/
theorem shortIntervalVariance_worse_than_chord :
    momentChord (2*(3:ℝ)) < transferBound 3 (2/3) 1 ∧
      momentChord (2*(6:ℝ)) < transferBound 6 (2/3) 1 := by
  rw [momentChord_six, momentChord_twelve, shortIntervalVariance_transfer_three,
    shortIntervalVariance_transfer_six]
  constructor <;> norm_num

/-! ### Capstone -/

/-- **The remaining method ceilings.**  Mean-value criticality traces the convexity line with no
slack; Halász–Montgomery reproduces the fourth-moment bound and nothing more; Guth–Maynard is inert
at the self-dual block; Heath-Brown's window is exactly `[1/8, 1/6]`, with its lower end at the
pivot. -/
theorem lindelof_remaining_ceilings :
    (∀ k : ℝ, k ≠ 0 → convexityExponent (meanValueAbscissa k) = meanValueOutput k) ∧
    (∀ v : ℝ, halaszMeasureExponent v = 1 - fourthMomentPhi v) ∧
    (∀ v : ℝ, min (guthMaynardBound 1 v) (classicalMeasureExponent v) =
      classicalMeasureExponent v) ∧
    (∀ v : ℝ, guthMaynardBound 1 v = classicalMeasureExponent v ↔ 3/20 ≤ v) ∧
    (∀ v : ℝ, (1/4 ≤ shortSecondMomentLength v ∧ shortSecondMomentLength v ≤ 1/3) ↔
      (1/8 ≤ v ∧ v ≤ 1/6)) ∧
    (∀ k : ℝ, 2 ≤ k → transferBound k (1/2) 1 = momentChord (2*k)) ∧
    (momentChord (2*(3:ℝ)) < transferBound 3 (2/3) 1 ∧
      momentChord (2*(6:ℝ)) < transferBound 6 (2/3) 1) ∧
    (meanValueOutput 2 = 1/4 ∧ meanValueOutput 3 = 1/6 ∧ meanValueOutput 4 = 1/8) :=
  ⟨fun _ hk => meanValue_traces_convexity hk, halasz_is_fourthMoment,
    guthMaynard_inert, guthMaynardBound_eq_classical_iff, heathBrown_window_iff,
    fun _ hk => transferBound_half_one hk, shortIntervalVariance_worse_than_chord,
    meanValueOutput_two, meanValueOutput_three, meanValueOutput_four⟩

end HTGeometry
