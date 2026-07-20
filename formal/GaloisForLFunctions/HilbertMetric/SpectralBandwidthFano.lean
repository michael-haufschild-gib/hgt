import GaloisForLFunctions.HilbertMetric.GradedPartition

/-!
# Spectral-bandwidth Slater Fano law

For an orthonormal finite frame in a spectrally graded real Hilbert space, this module defines
the additive Slater mean and variance through the standard one-particle compression formula.  If
the one-particle spectrum is contained in `[lower, upper]`, it proves the universal bound

`card ι * (lower - (upper - lower - 1)^2 / 4) ≤ mean - variance`.

The bound is independent of ambient dimension.  Its nonnegative phase is controlled only by the
spectral bandwidth, and its positive integral specialization shows that every spectrum supported
in degrees one through four is sub-Poisson.  A separate endpoint-pair square law records the sharp
two-level extremizer.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Coordinate formulation of a finite orthonormal family in a real Euclidean space. -/
def IsOrthonormalCoordinateFrame (v : ι → κ → ℝ) : Prop :=
  ∀ i j, ∑ k, v i k * v j k = if i = j then 1 else 0

/-- Spectral mean of one occupied orbital. -/
def orbitalSpectralMean (v : ι → κ → ℝ) (energy : κ → ℝ) (i : ι) : ℝ :=
  ∑ k, energy k * v i k ^ 2

/-- Spectral second moment of one occupied orbital. -/
def orbitalSpectralSecondMoment
    (v : ι → κ → ℝ) (energy : κ → ℝ) (i : ι) : ℝ :=
  ∑ k, energy k ^ 2 * v i k ^ 2

/-- Squared Hilbert--Schmidt energy of the spectral observable compressed to the occupied frame. -/
def slaterCompressedSpectralEnergy
    (v : ι → κ → ℝ) (energy : κ → ℝ) : ℝ :=
  ∑ i, ∑ j, (∑ k, energy k * v i k * v j k) ^ 2

/-- Mean of the additive spectral observable in the Slater state of the occupied frame. -/
def slaterSpectralMean (v : ι → κ → ℝ) (energy : κ → ℝ) : ℝ :=
  ∑ i, orbitalSpectralMean v energy i

/-- Variance of the additive spectral observable in the Slater compression formula. -/
def slaterSpectralVariance (v : ι → κ → ℝ) (energy : κ → ℝ) : ℝ :=
  (∑ i, orbitalSpectralSecondMoment v energy i) -
    slaterCompressedSpectralEnergy v energy

/-- Mean-minus-variance margin of the additive Slater spectral observable. -/
def slaterSpectralFanoMargin (v : ι → κ → ℝ) (energy : κ → ℝ) : ℝ :=
  slaterSpectralMean v energy - slaterSpectralVariance v energy

/-- Failure of an occupied orbital to be supported on the two spectral endpoints. -/
def slaterSpectralSecantDefect
    (v : ι → κ → ℝ) (energy : κ → ℝ) (lower upper : ℝ) : ℝ :=
  ∑ i, ((lower + upper) * orbitalSpectralMean v energy i - lower * upper -
    orbitalSpectralSecondMoment v energy i)

/-- Squared displacement of the occupied spectral means from the extremal balancing energy. -/
def slaterSpectralCenteringDefect
    (v : ι → κ → ℝ) (energy : κ → ℝ) (lower upper : ℝ) : ℝ :=
  ∑ i, (orbitalSpectralMean v energy i - (lower + upper - 1) / 2) ^ 2

/-- Off-diagonal energy of the spectral observable compressed to the occupied frame. -/
def slaterSpectralCoherenceDefect
    (v : ι → κ → ℝ) (energy : κ → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i,
    (∑ k, energy k * v i k * v j k) ^ 2

/-- Small-band displacement defect from the lower spectral endpoint. -/
def slaterSpectralLowerEndpointDefect
    (v : ι → κ → ℝ) (energy : κ → ℝ) (lower upper : ℝ) : ℝ :=
  ∑ i, (orbitalSpectralMean v energy i - lower) *
    (orbitalSpectralMean v energy i - (upper - 1))

/-- Mean-minus-variance margin of a rank-one orbital supported on two spectral endpoints. -/
def endpointPairSpectralFanoMargin (lower upper p : ℝ) : ℝ :=
  let mean := lower * (1 - p) + upper * p
  let secondMoment := lower ^ 2 * (1 - p) + upper ^ 2 * p
  mean - (secondMoment - mean ^ 2)

/-- **Endpoint-pair square law.**  The exact remainder above the spectral-bandwidth constant is
one square. -/
theorem endpointPairSpectralFanoMargin_square (lower upper p : ℝ) :
    endpointPairSpectralFanoMargin lower upper p =
      lower - (upper - lower - 1) ^ 2 / 4 +
        ((upper - lower) * p - (upper - lower - 1) / 2) ^ 2 := by
  unfold endpointPairSpectralFanoMargin
  ring

/-- The two-endpoint mixture at the balancing phase attains the universal constant. -/
theorem endpointPairSpectralFanoMargin_at_optimal
    (lower upper : ℝ) (hdiff : upper - lower ≠ 0) :
    endpointPairSpectralFanoMargin lower upper
        ((upper - lower - 1) / (2 * (upper - lower))) =
      lower - (upper - lower - 1) ^ 2 / 4 := by
  rw [endpointPairSpectralFanoMargin_square]
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  field_simp
  ring

/-- The secant line through `(lower, lower^2)` and `(upper, upper^2)` dominates the square
function on the spectral interval. -/
theorem spectral_sq_le_secant
    {lower upper x : ℝ} (hlower : lower ≤ x) (hupper : x ≤ upper) :
    x ^ 2 ≤ (lower + upper) * x - lower * upper := by
  have hproduct : (x - lower) * (x - upper) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlower) (sub_nonpos.mpr hupper)
  nlinarith

omit [Fintype ι] in
/-- Every member of an orthonormal coordinate frame has unit squared norm. -/
theorem orthonormalCoordinateFrame_row_norm
    (v : ι → κ → ℝ) (hframe : IsOrthonormalCoordinateFrame v) (i : ι) :
    ∑ k, v i k ^ 2 = 1 := by
  have h := hframe i i
  simpa [pow_two] using h

omit [Fintype ι] in
/-- A spectral lower endpoint bounds the mean energy of every occupied orbital. -/
theorem lower_le_orbitalSpectralMean
    (v : ι → κ → ℝ) (energy : κ → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v)
    (lower : ℝ) (hlower : ∀ k, lower ≤ energy k) (i : ι) :
    lower ≤ orbitalSpectralMean v energy i := by
  have hsum : (∑ k, lower * v i k ^ 2) ≤
      ∑ k, energy k * v i k ^ 2 :=
    Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_right (hlower k) (sq_nonneg (v i k))
  rw [← Finset.mul_sum, orthonormalCoordinateFrame_row_norm v hframe i, mul_one] at hsum
  simpa [orbitalSpectralMean] using hsum

omit [Fintype ι] in
/-- Bhatia--Davis secant bound for the second moment of each occupied orbital. -/
theorem orbitalSpectralSecondMoment_le_secant
    (v : ι → κ → ℝ) (energy : κ → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v)
    (lower upper : ℝ)
    (hlower : ∀ k, lower ≤ energy k) (hupper : ∀ k, energy k ≤ upper)
    (i : ι) :
    orbitalSpectralSecondMoment v energy i ≤
      (lower + upper) * orbitalSpectralMean v energy i - lower * upper := by
  have hpoint : ∀ k,
      energy k ^ 2 * v i k ^ 2 ≤
        (((lower + upper) * energy k - lower * upper) * v i k ^ 2) := by
    intro k
    exact mul_le_mul_of_nonneg_right
      (spectral_sq_le_secant (hlower k) (hupper k)) (sq_nonneg (v i k))
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hpoint k
  rw [show
      (∑ k, ((lower + upper) * energy k - lower * upper) * v i k ^ 2) =
        (lower + upper) * orbitalSpectralMean v energy i -
          lower * upper * (∑ k, v i k ^ 2) by
    unfold orbitalSpectralMean
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring] at hsum
  rw [orthonormalCoordinateFrame_row_norm v hframe i] at hsum
  simpa [orbitalSpectralSecondMoment] using hsum

/-- The compression energy splits exactly into diagonal mean squares and occupied coherence. -/
theorem slaterCompressedSpectralEnergy_eq_diagonal_add_coherence
    (v : ι → κ → ℝ) (energy : κ → ℝ) :
    slaterCompressedSpectralEnergy v energy =
      (∑ i, orbitalSpectralMean v energy i ^ 2) +
        slaterSpectralCoherenceDefect v energy := by
  unfold slaterCompressedSpectralEnergy slaterSpectralCoherenceDefect
  calc
    (∑ i, ∑ j, (∑ k, energy k * v i k * v j k) ^ 2) =
        ∑ i, ((∑ k, energy k * v i k * v i k) ^ 2 +
          ∑ j ∈ Finset.univ.erase i,
            (∑ k, energy k * v i k * v j k) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_erase_add Finset.univ
        (fun j => (∑ k, energy k * v i k * v j k) ^ 2) (Finset.mem_univ i)]
      ring
    _ = (∑ i, orbitalSpectralMean v energy i ^ 2) +
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          (∑ k, energy k * v i k * v j k) ^ 2 := by
      rw [Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      unfold orbitalSpectralMean
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- Endpoint leakage is nonnegative for an orthonormal frame in the stated spectral band. -/
theorem slaterSpectralSecantDefect_nonneg
    (v : ι → κ → ℝ) (energy : κ → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v)
    (lower upper : ℝ)
    (hlower : ∀ k, lower ≤ energy k) (hupper : ∀ k, energy k ≤ upper) :
    0 ≤ slaterSpectralSecantDefect v energy lower upper := by
  unfold slaterSpectralSecantDefect
  exact Finset.sum_nonneg fun i _ => by
    have hsecond := orbitalSpectralSecondMoment_le_secant
      v energy hframe lower upper hlower hupper i
    linarith

omit [DecidableEq ι] in
/-- Spectral-centering energy is nonnegative. -/
theorem slaterSpectralCenteringDefect_nonneg
    (v : ι → κ → ℝ) (energy : κ → ℝ) (lower upper : ℝ) :
    0 ≤ slaterSpectralCenteringDefect v energy lower upper := by
  unfold slaterSpectralCenteringDefect
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- Occupied coherence energy is nonnegative. -/
theorem slaterSpectralCoherenceDefect_nonneg
    (v : ι → κ → ℝ) (energy : κ → ℝ) :
    0 ≤ slaterSpectralCoherenceDefect v energy := by
  unfold slaterSpectralCoherenceDefect
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg _

/-- In a band of width at most one, the lower-endpoint displacement defect is nonnegative. -/
theorem slaterSpectralLowerEndpointDefect_nonneg_of_width_le_one
    (v : ι → κ → ℝ) (energy : κ → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v)
    (lower upper : ℝ) (hlower : ∀ k, lower ≤ energy k)
    (hwidth : upper - lower ≤ 1) :
    0 ≤ slaterSpectralLowerEndpointDefect v energy lower upper := by
  unfold slaterSpectralLowerEndpointDefect
  exact Finset.sum_nonneg fun i _ => by
    have hmean := lower_le_orbitalSpectralMean v energy hframe lower hlower i
    have hother : upper - 1 ≤ orbitalSpectralMean v energy i := by linarith
    exact mul_nonneg (sub_nonneg.mpr hmean) (sub_nonneg.mpr hother)

omit [DecidableEq ι] in
/-- The full compression energy dominates the sum of its diagonal squares. -/
theorem sum_orbitalSpectralMean_sq_le_compressed
    (v : ι → κ → ℝ) (energy : κ → ℝ) :
    (∑ i, orbitalSpectralMean v energy i ^ 2) ≤
      slaterCompressedSpectralEnergy v energy := by
  classical
  rw [slaterCompressedSpectralEnergy_eq_diagonal_add_coherence]
  exact le_add_of_nonneg_right (slaterSpectralCoherenceDefect_nonneg v energy)

omit [DecidableEq ι] in
/-- The Slater margin dominates the sum of the diagonal one-orbital margins. -/
theorem sum_orbital_diagonalFano_le_slaterSpectralFanoMargin
    (v : ι → κ → ℝ) (energy : κ → ℝ) :
    (∑ i, (orbitalSpectralMean v energy i -
      orbitalSpectralSecondMoment v energy i +
        orbitalSpectralMean v energy i ^ 2)) ≤
      slaterSpectralFanoMargin v energy := by
  have hdiagonal := sum_orbitalSpectralMean_sq_le_compressed v energy
  unfold slaterSpectralFanoMargin slaterSpectralMean slaterSpectralVariance
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linarith

/-- **Three-defect spectral-bandwidth identity.**  The Slater Fano margin is exactly its universal
spectral-band floor plus endpoint leakage, spectral-centering energy, and occupied coherence. -/
theorem slaterSpectralFanoMargin_three_defect
    (v : ι → κ → ℝ) (energy : κ → ℝ) (lower upper : ℝ) :
    slaterSpectralFanoMargin v energy =
      (Fintype.card ι : ℝ) *
          (lower - (upper - lower - 1) ^ 2 / 4) +
        slaterSpectralSecantDefect v energy lower upper +
        slaterSpectralCenteringDefect v energy lower upper +
        slaterSpectralCoherenceDefect v energy := by
  have hmargin :
      slaterSpectralFanoMargin v energy =
        (∑ i, (orbitalSpectralMean v energy i -
          orbitalSpectralSecondMoment v energy i +
            orbitalSpectralMean v energy i ^ 2)) +
          slaterSpectralCoherenceDefect v energy := by
    unfold slaterSpectralFanoMargin slaterSpectralMean slaterSpectralVariance
    rw [slaterCompressedSpectralEnergy_eq_diagonal_add_coherence]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [hmargin]
  unfold slaterSpectralSecantDefect slaterSpectralCenteringDefect
  apply congrArg (fun x => x + slaterSpectralCoherenceDefect v energy)
  calc
    (∑ i, (orbitalSpectralMean v energy i -
        orbitalSpectralSecondMoment v energy i +
          orbitalSpectralMean v energy i ^ 2)) =
        ∑ i, ((lower - (upper - lower - 1) ^ 2 / 4) +
          ((lower + upper) * orbitalSpectralMean v energy i - lower * upper -
            orbitalSpectralSecondMoment v energy i) +
          (orbitalSpectralMean v energy i - (lower + upper - 1) / 2) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (Fintype.card ι : ℝ) *
          (lower - (upper - lower - 1) ^ 2 / 4) +
        (∑ i, ((lower + upper) * orbitalSpectralMean v energy i - lower * upper -
          orbitalSpectralSecondMoment v energy i)) +
        ∑ i, (orbitalSpectralMean v energy i - (lower + upper - 1) / 2) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Spectral-bandwidth Slater Fano law.**  The universal mean-minus-variance lower bound is
extensive in the occupied rank and independent of ambient dimension. -/
theorem slaterSpectralFanoMargin_lower_bound
    (v : ι → κ → ℝ) (energy : κ → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v)
    (lower upper : ℝ)
    (hlower : ∀ k, lower ≤ energy k) (hupper : ∀ k, energy k ≤ upper) :
    (Fintype.card ι : ℝ) *
        (lower - (upper - lower - 1) ^ 2 / 4) ≤
      slaterSpectralFanoMargin v energy := by
  rw [slaterSpectralFanoMargin_three_defect v energy lower upper]
  have hsecant := slaterSpectralSecantDefect_nonneg
    v energy hframe lower upper hlower hupper
  have hcenter := slaterSpectralCenteringDefect_nonneg v energy lower upper
  have hcoherence := slaterSpectralCoherenceDefect_nonneg v energy
  linarith

/-- **Lower-endpoint defect identity.**  In a narrow spectral band this is the exact decomposition
whose three remainders prove the sharper floor `card ι * lower`. -/
theorem slaterSpectralFanoMargin_lower_endpoint_defect
    (v : ι → κ → ℝ) (energy : κ → ℝ) (lower upper : ℝ) :
    slaterSpectralFanoMargin v energy =
      (Fintype.card ι : ℝ) * lower +
        slaterSpectralSecantDefect v energy lower upper +
        slaterSpectralLowerEndpointDefect v energy lower upper +
        slaterSpectralCoherenceDefect v energy := by
  have hmargin :
      slaterSpectralFanoMargin v energy =
        (∑ i, (orbitalSpectralMean v energy i -
          orbitalSpectralSecondMoment v energy i +
            orbitalSpectralMean v energy i ^ 2)) +
          slaterSpectralCoherenceDefect v energy := by
    unfold slaterSpectralFanoMargin slaterSpectralMean slaterSpectralVariance
    rw [slaterCompressedSpectralEnergy_eq_diagonal_add_coherence]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [hmargin]
  unfold slaterSpectralSecantDefect slaterSpectralLowerEndpointDefect
  apply congrArg (fun x => x + slaterSpectralCoherenceDefect v energy)
  calc
    (∑ i, (orbitalSpectralMean v energy i -
        orbitalSpectralSecondMoment v energy i +
          orbitalSpectralMean v energy i ^ 2)) =
        ∑ i, (lower +
          ((lower + upper) * orbitalSpectralMean v energy i - lower * upper -
            orbitalSpectralSecondMoment v energy i) +
          (orbitalSpectralMean v energy i - lower) *
            (orbitalSpectralMean v energy i - (upper - 1))) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (Fintype.card ι : ℝ) * lower +
        (∑ i, ((lower + upper) * orbitalSpectralMean v energy i - lower * upper -
          orbitalSpectralSecondMoment v energy i)) +
        ∑ i, (orbitalSpectralMean v energy i - lower) *
          (orbitalSpectralMean v energy i - (upper - 1)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- When the spectral width is at most one, the exact interval-only lower bound improves to
`card ι * lower`. -/
theorem slaterSpectralFanoMargin_lower_bound_of_width_le_one
    (v : ι → κ → ℝ) (energy : κ → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v)
    (lower upper : ℝ)
    (hlower : ∀ k, lower ≤ energy k) (hupper : ∀ k, energy k ≤ upper)
    (hwidth : upper - lower ≤ 1) :
    (Fintype.card ι : ℝ) * lower ≤ slaterSpectralFanoMargin v energy := by
  rw [slaterSpectralFanoMargin_lower_endpoint_defect v energy lower upper]
  have hsecant := slaterSpectralSecantDefect_nonneg
    v energy hframe lower upper hlower hupper
  have hlowerEndpoint := slaterSpectralLowerEndpointDefect_nonneg_of_width_le_one
    v energy hframe lower upper hlower hwidth
  have hcoherence := slaterSpectralCoherenceDefect_nonneg v energy
  linarith

/-- The exact bandwidth inequality `(upper - lower - 1)^2 ≤ 4 * lower` forces a nonnegative
Slater Fano margin in every occupied rank. -/
theorem slaterSpectralFanoMargin_nonnegative_of_bandwidth
    (v : ι → κ → ℝ) (energy : κ → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v)
    (lower upper : ℝ)
    (hlower : ∀ k, lower ≤ energy k) (hupper : ∀ k, energy k ≤ upper)
    (hthreshold : (upper - lower - 1) ^ 2 ≤ 4 * lower) :
    0 ≤ slaterSpectralFanoMargin v energy := by
  have hlowerBound := slaterSpectralFanoMargin_lower_bound
    v energy hframe lower upper hlower hupper
  have hfactor : 0 ≤ lower - (upper - lower - 1) ^ 2 / 4 := by nlinarith
  have hcard : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  exact le_trans (mul_nonneg hcard hfactor) hlowerBound

/-- A negative Slater Fano margin necessarily lies beyond the spectral-bandwidth threshold. -/
theorem slaterSpectralFanoMargin_negative_forces_bandwidth
    (v : ι → κ → ℝ) (energy : κ → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v)
    (lower upper : ℝ)
    (hlower : ∀ k, lower ≤ energy k) (hupper : ∀ k, energy k ≤ upper)
    (hnegative : slaterSpectralFanoMargin v energy < 0) :
    4 * lower < (upper - lower - 1) ^ 2 := by
  by_contra hnot
  have hthreshold : (upper - lower - 1) ^ 2 ≤ 4 * lower := le_of_not_gt hnot
  have hnonnegative := slaterSpectralFanoMargin_nonnegative_of_bandwidth
    v energy hframe lower upper hlower hupper hthreshold
  linarith

/-- Equality in the spectral-bandwidth lower bound holds exactly when endpoint leakage,
spectral-centering energy, and occupied coherence all vanish. -/
theorem slaterSpectralFanoMargin_eq_lower_bound_iff
    (v : ι → κ → ℝ) (energy : κ → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v)
    (lower upper : ℝ)
    (hlower : ∀ k, lower ≤ energy k) (hupper : ∀ k, energy k ≤ upper) :
    slaterSpectralFanoMargin v energy =
        (Fintype.card ι : ℝ) *
          (lower - (upper - lower - 1) ^ 2 / 4) ↔
      slaterSpectralSecantDefect v energy lower upper = 0 ∧
      slaterSpectralCenteringDefect v energy lower upper = 0 ∧
      slaterSpectralCoherenceDefect v energy = 0 := by
  have hsecant := slaterSpectralSecantDefect_nonneg
    v energy hframe lower upper hlower hupper
  have hcenter := slaterSpectralCenteringDefect_nonneg v energy lower upper
  have hcoherence := slaterSpectralCoherenceDefect_nonneg v energy
  rw [slaterSpectralFanoMargin_three_defect v energy lower upper]
  constructor
  · intro h
    constructor
    · linarith
    constructor <;> linarith
  · rintro ⟨hsecant0, hcenter0, hcoherence0⟩
    rw [hsecant0, hcenter0, hcoherence0]
    ring

/-- **Quartic Slater stability.**  Every real Slater frame supported in the spectral interval
`[1,4]` has nonnegative mean-minus-variance margin. -/
theorem quartic_slaterSpectralFanoMargin_nonnegative
    (v : ι → κ → ℝ) (energy : κ → ℝ)
    (hframe : IsOrthonormalCoordinateFrame v)
    (hlower : ∀ k, 1 ≤ energy k) (hupper : ∀ k, energy k ≤ 4) :
    0 ≤ slaterSpectralFanoMargin v energy := by
  apply slaterSpectralFanoMargin_nonnegative_of_bandwidth
    v energy hframe 1 4 hlower hupper
  norm_num

/-- Natural-degree form of quartic Slater stability. -/
theorem positiveQuarticDegree_slaterSpectralFanoMargin_nonnegative
    (v : ι → κ → ℝ) (degree : κ → ℕ)
    (hframe : IsOrthonormalCoordinateFrame v)
    (hpositive : ∀ k, 1 ≤ degree k) (hquartic : ∀ k, degree k ≤ 4) :
    0 ≤ slaterSpectralFanoMargin v (fun k => (degree k : ℝ)) := by
  apply quartic_slaterSpectralFanoMargin_nonnegative v _ hframe
  · intro k
    exact_mod_cast hpositive k
  · intro k
    exact_mod_cast hquartic k

end

end GaloisForLFunctions.HilbertMetric
