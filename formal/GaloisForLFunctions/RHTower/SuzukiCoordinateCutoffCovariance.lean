import GaloisForLFunctions.RHTower.SuzukiLocalizedOrbitLiftTrilemma

/-!
# Suzuki coordinate-cutoff covariance classification

The differentiated weighted valuation carrier contains prime shifts. A diagonal terminal cutoff
commutes with every active weighted shift exactly when its coordinate values agree along every
active edge. Equality then propagates along generator words. Consequently two orbit labels whose
validity thresholds differ by at least one cannot simultaneously carry transport-covariant adapted
cutoffs.

This is the unconditional algebraic/event-order core of the coordinate-cutoff obstruction. It
assumes neither RH nor the conjectural completed Suzuki carrier equation.
-/

namespace GaloisForLFunctions.RHTower

/-- Weighted pullback along one oriented orbit edge. -/
def weightedOrbitShift {ι : Type*} (next : ι → ι) (weight : ι → ℝ)
    (f : ι → ℝ) : ι → ℝ :=
  fun i => weight i * f (next i)

/-- Coordinate-diagonal scalar multiplier. -/
def orbitDiagonal {ι : Type*} (cutoff : ι → ℝ) (f : ι → ℝ) : ι → ℝ :=
  fun i => cutoff i * f i

/-- Exact commutator of a coordinate multiplier with one weighted orbit shift. -/
theorem orbitDiagonal_weightedOrbitShift_sub_apply
    {ι : Type*} (next : ι → ι) (weight cutoff f : ι → ℝ) (i : ι) :
    (orbitDiagonal cutoff (weightedOrbitShift next weight f) -
      weightedOrbitShift next weight (orbitDiagonal cutoff f)) i =
      weight i * (cutoff i - cutoff (next i)) * f (next i) := by
  simp [orbitDiagonal, weightedOrbitShift]
  ring

/-- For nonzero edge weights, a diagonal multiplier commutes with a weighted shift on every
profile exactly when its values agree across every edge. -/
theorem orbitDiagonal_commutes_weightedOrbitShift_iff
    {ι : Type*} (next : ι → ι) (weight cutoff : ι → ℝ)
    (hweight : ∀ i, weight i ≠ 0) :
    (∀ f, orbitDiagonal cutoff (weightedOrbitShift next weight f) =
      weightedOrbitShift next weight (orbitDiagonal cutoff f)) ↔
      ∀ i, cutoff i = cutoff (next i) := by
  constructor
  · intro h i
    have hi := congrFun (h (fun _ => 1)) i
    simp [orbitDiagonal, weightedOrbitShift] at hi
    exact (mul_left_cancel₀ (hweight i)) (by simpa [mul_comm] using hi)
  · intro h f
    funext i
    simp only [orbitDiagonal, weightedOrbitShift]
    rw [h i]
    ring

/-- Endpoint obtained by following a finite word of orbit generators. -/
def followOrbitWord {ι σ : Type*} (step : ι → σ → ι) (i : ι) (word : List σ) : ι :=
  word.foldl step i

/-- Edgewise equality propagates along every finite generator word. -/
theorem cutoff_eq_followOrbitWord
    {ι σ : Type*} (step : ι → σ → ι) (cutoff : ι → ℝ)
    (hstep : ∀ i s, cutoff i = cutoff (step i s))
    (i : ι) (word : List σ) :
    cutoff i = cutoff (followOrbitWord step i word) := by
  induction word generalizing i with
  | nil => rfl
  | cons s word ih =>
      exact (hstep i s).trans (by simpa [followOrbitWord] using ih (step i s))

/-- A unit-width terminal cutoff is zero through its validity threshold and one one unit later. -/
def EventAdaptedCutoff (cutoff : ℝ → ℝ) (threshold : ℝ) : Prop :=
  (∀ L, L ≤ threshold → cutoff L = 0) ∧
    ∀ L, threshold + 1 ≤ L → cutoff L = 1

/-- One scalar cutoff cannot be adapted to two thresholds separated by at least one. -/
theorem not_eventAdaptedCutoff_pair
    (cutoff : ℝ → ℝ) {threshold₀ threshold₁ : ℝ}
    (horder : threshold₀ + 1 ≤ threshold₁) :
    ¬(EventAdaptedCutoff cutoff threshold₀ ∧
      EventAdaptedCutoff cutoff threshold₁) := by
  rintro ⟨h₀, h₁⟩
  have hone : cutoff (threshold₀ + 1) = 1 := h₀.2 _ le_rfl
  have hzero : cutoff (threshold₀ + 1) = 0 := h₁.1 _ horder
  linarith

/-- **Transport-covariant adapted-cutoff obstruction.** If two labels are joined by active
generator edges and their validity thresholds differ by at least one, no cutoff family can both
be adapted at every label and remain invariant along every active edge. -/
theorem no_transportCovariant_eventAdapted_cutoff
    {ι σ : Type*} (step : ι → σ → ι) (cutoff : ι → ℝ → ℝ)
    (threshold : ι → ℝ) (i₀ i₁ : ι) (word : List σ)
    (hreaches : followOrbitWord step i₀ word = i₁)
    (hcov : ∀ i s L, cutoff i L = cutoff (step i s) L)
    (hadapted : ∀ i, EventAdaptedCutoff (cutoff i) (threshold i))
    (horder : threshold i₀ + 1 ≤ threshold i₁) : False := by
  let L := threshold i₀ + 1
  have heq : cutoff i₀ L = cutoff i₁ L := by
    have hpath := cutoff_eq_followOrbitWord step (fun i => cutoff i L)
      (fun i s => hcov i s L) i₀ word
    simpa [hreaches] using hpath
  have hone : cutoff i₀ L = 1 := (hadapted i₀).2 L (by simp [L])
  have hzero : cutoff i₁ L = 0 := (hadapted i₁).1 L (by simpa [L] using horder)
  linarith

end GaloisForLFunctions.RHTower
