import GaloisForLFunctions.RHTower.GibbsCriticalDissipationAntiscaleResonance
import GaloisForLFunctions.RHTower.Sieve.MoebiusUniformFrequency
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSquareIndexPolarization

/-!
# Antiscale first-trace frame for Route E

Prime insertion is diagonal in the antiscale/same-sign coordinates: the
antiscale coordinate has coefficient one, while only the same-sign coordinate
is contracted.  Consequently every scalar normalization Bockstein restricts
to the identity on exact antiscale coherence.

The positive replacement is genuinely cross-prime.  The reciprocal-prime
sum of the squared same-sign Mellin seam factors is exactly twice the
Granville--Soundararajan distance from the constant prime value `-1` to the
character `n^(it)`.  The corpus's uniform frequency theorem therefore gives
an unconditional global harmonic frame lower bound.

The final section records the order-free finite weighted batch dispersion
which a source-specific Gibbs-to-frame handoff must control.  All statements
are finite or inherited from unconditional corpus theorems; no RH hypothesis
or computation is used.
-/

open scoped BigOperators

namespace RHTower.GibbsGas

noncomputable section

/-- Antiscale coordinate of a dilation pair. -/
def routeEAntiscaleCoordinate (x y : ℝ) : ℝ := (x - y) / 2

/-- Same-sign coordinate of a dilation pair. -/
def routeESameSignCoordinate (x y : ℝ) : ℝ := (x + y) / 2

/-- Abstract normalized signed insertion with forcing weight `beta`. -/
def routeESignedInsertion (beta x y : ℝ) : ℝ := x - beta * (x + y)

/-- **Exact two-channel insertion.**  The antiscale coordinate is transmitted
with coefficient one; only the same-sign coordinate sees `1 - 2 * beta`. -/
theorem routeESignedInsertion_eq_antiscale_add_sameSign
    (beta x y : ℝ) :
    routeESignedInsertion beta x y =
      routeEAntiscaleCoordinate x y +
        (1 - 2 * beta) * routeESameSignCoordinate x y := by
  simp [routeESignedInsertion, routeEAntiscaleCoordinate,
    routeESameSignCoordinate]
  ring

/-- The concrete Gibbs normalized current is the abstract signed insertion
with the exact partition hazard weight. -/
theorem normalizedGibbsCurrent_insert_eq_routeESignedInsertion
    (p : ℕ) (S : Finset ℕ) (hp : p ∉ S) (x : ℝ) :
    normalizedGibbsCurrent (insert p S) x =
      routeESignedInsertion (gibbsForcingWeight p S x)
        (normalizedGibbsCurrent S x)
        (normalizedGibbsCurrent S ((p : ℝ) * x)) := by
  rw [normalizedGibbsCurrent, normalizedGibbsCurrent,
    normalizedGibbsCurrent, gibbs_current_insert p S hp,
    gibbs_partition_insert p S hp]
  unfold routeESignedInsertion gibbsForcingWeight
  have hZx : gibbsDiag S x 1 ≠ 0 := ne_of_gt (gibbs_partition_pos S x)
  have hZpx : gibbsDiag S ((p : ℝ) * x) 1 ≠ 0 :=
    ne_of_gt (gibbs_partition_pos S ((p : ℝ) * x))
  have hZsum : gibbsDiag S x 1 + gibbsDiag S ((p : ℝ) * x) 1 ≠ 0 :=
    ne_of_gt (add_pos (gibbs_partition_pos S x)
      (gibbs_partition_pos S ((p : ℝ) * x)))
  field_simp [hZx, hZpx, hZsum]
  ring

/-- Concrete Gibbs insertion in its exact antiscale/same-sign eigenchannels. -/
theorem normalizedGibbsCurrent_insert_eq_antiscale_add_sameSign
    (p : ℕ) (S : Finset ℕ) (hp : p ∉ S) (x : ℝ) :
    normalizedGibbsCurrent (insert p S) x =
      routeEAntiscaleCoordinate
          (normalizedGibbsCurrent S x)
          (normalizedGibbsCurrent S ((p : ℝ) * x)) +
        gibbsContractionWeight p S x *
          routeESameSignCoordinate
            (normalizedGibbsCurrent S x)
            (normalizedGibbsCurrent S ((p : ℝ) * x)) := by
  rw [normalizedGibbsCurrent_insert_eq_routeESignedInsertion,
    routeESignedInsertion_eq_antiscale_add_sameSign,
    gibbsContractionWeight_eq_one_sub_two_mul_forcingWeight]
  exact hp

/-- Scalar first-normal difference across one normalized insertion. -/
def routeEScalarFirstTrace
    (lambda beta x y : ℝ) : ℝ :=
  (x - lambda * routeESignedInsertion beta x y) / (1 - lambda)

/-- **Scalar first-trace classification.**  Every scalar normalization changes
only the same-sign coordinate and leaves the antiscale coefficient equal to
one. -/
theorem routeEScalarFirstTrace_eq_antiscale_add_sameSign
    {lambda : ℝ} (hlambda : lambda ≠ 1) (beta x y : ℝ) :
    routeEScalarFirstTrace lambda beta x y =
      routeEAntiscaleCoordinate x y +
        ((1 - lambda * (1 - 2 * beta)) / (1 - lambda)) *
          routeESameSignCoordinate x y := by
  have hden : 1 - lambda ≠ 0 := sub_ne_zero.mpr (Ne.symm hlambda)
  rw [routeEScalarFirstTrace, routeESignedInsertion_eq_antiscale_add_sameSign]
  simp only [routeEAntiscaleCoordinate, routeESameSignCoordinate]
  field_simp [hden]
  ring

/-- Equivalent forcing-weight form of the scalar classification. -/
theorem routeEScalarFirstTrace_eq_current_add_sameSign
    {lambda : ℝ} (hlambda : lambda ≠ 1) (beta x y : ℝ) :
    routeEScalarFirstTrace lambda beta x y =
      x + (lambda * beta / (1 - lambda)) * (x + y) := by
  have hden : 1 - lambda ≠ 0 := sub_ne_zero.mpr (Ne.symm hlambda)
  unfold routeEScalarFirstTrace routeESignedInsertion
  field_simp [hden]
  ring

/-- **Scalar-normalization wall.**  On exact antiscale coherence every scalar
first-trace reader is literally the identity. -/
theorem routeEScalarFirstTrace_antiscale
    {lambda : ℝ} (hlambda : lambda ≠ 1) (beta x : ℝ) :
    routeEScalarFirstTrace lambda beta x (-x) = x := by
  rw [routeEScalarFirstTrace_eq_current_add_sameSign hlambda]
  ring

end

end RHTower.GibbsGas

namespace RHTower.Sieve

noncomputable section

/-- Reciprocal-prime energy of the same-sign Mellin seam factors. -/
def routeEAntiscaleFrameEnergy (P : Finset ℕ) (t : ℝ) : ℝ :=
  ∑ p ∈ P, Complex.normSq (1 + charFn t p) / (p : ℝ)

/-- Squared norm of one same-sign character seam. -/
theorem normSq_one_add_charFn (t : ℝ) (p : ℕ) :
    Complex.normSq (1 + charFn t p) =
      2 * (1 + Real.cos (t * Real.log (p : ℝ))) := by
  rw [charFn, show
    (1 : ℂ) + Complex.exp (((t * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I) =
      -((-1 : ℂ) -
        Complex.exp (((t * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I)) by ring,
    Complex.normSq_neg]
  have hlocal := RHTower.normSq_real_sub_exp_I_mul
    (-1 : ℝ) (t * Real.log (p : ℝ))
  rw [show Complex.normSq
      ((-1 : ℂ) -
        Complex.exp (((t * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I)) =
      (-1 : ℝ) ^ 2 - 2 * (-1 : ℝ) *
          Real.cos (t * Real.log (p : ℝ)) + 1 by
        simpa using hlocal]
  ring

/-- **Exact harmonic antiscale frame.**  Same-sign seam energy is twice the
distance from the constant prime value `-1` to the Mellin character. -/
theorem routeEAntiscaleFrameEnergy_eq_two_mulDistSqPair
    (P : Finset ℕ) (t : ℝ) :
    routeEAntiscaleFrameEnergy P t =
      2 * mulDistSqPair (fun _ : ℕ => (-1 : ℂ)) (charFn t) P := by
  rw [mulDistSqPair_neg_one_charFn (fun p hp => rfl) t,
    routeEAntiscaleFrameEnergy, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [normSq_one_add_charFn]
  ring

/-- **Uniform global antiscale frame bound.**  No common Mellin phase in the
frequency window can be antiscale-coherent across the full reciprocal-prime
packet. -/
theorem exists_routeEAntiscaleFrameEnergy_ge_uniform :
    ∃ C : ℝ, ∀ (z : ℕ) (T t : ℝ), 3 ≤ z → 9 ≤ T → |t| ≤ T →
      1 / Real.log z ≤ zetaLowerA / Real.log T ^ 9 →
      2 * (logLog z - 7 * Real.log (Real.log T) - C) ≤
        routeEAntiscaleFrameEnergy (Nat.primesLE z) t := by
  obtain ⟨C, hC⟩ := exists_mulDistSqPair_ge_uniform
  refine ⟨C, ?_⟩
  intro z T t hz hT htT hzt
  have hdist := hC (fun _ : ℕ => (-1 : ℂ)) z T t hz hT htT hzt
    (fun p hp => rfl)
  rw [routeEAntiscaleFrameEnergy_eq_two_mulDistSqPair]
  linarith

end

end RHTower.Sieve

namespace RHTower.GibbsGas

noncomputable section

/-- Total positive weight in a finite Route E batch. -/
def routeEBatchWeightMass {ι : Type*} (s : Finset ι) (w : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i

/-- Weighted leaf energy before the signed batch projection. -/
def routeEBatchLeafEnergy {ι : Type*}
    (s : Finset ι) (w value : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * value i ^ 2

/-- Squared energy of the rank-one signed batch projection. -/
def routeEBatchMeanEnergy {ι : Type*}
    (s : Finset ι) (w value : ι → ℝ) : ℝ :=
  (∑ i ∈ s, w i * value i) ^ 2 / routeEBatchWeightMass s w

/-- Ordered pairwise dispersion numerator of a finite batch. -/
def routeEBatchPairwiseDispersion {ι : Type*}
    (s : Finset ι) (w value : ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s,
    w i * w j * (value i - value j) ^ 2

/-- Normalized order-free batch residual. -/
def routeEBatchResidual {ι : Type*}
    (s : Finset ι) (w value : ι → ℝ) : ℝ :=
  routeEBatchPairwiseDispersion s w value /
    (2 * routeEBatchWeightMass s w)

/-- **Order-free batch polarization.**  Rank-one signed output plus pairwise
dispersion is exactly the full leaf energy. -/
theorem routeEBatchMeanEnergy_add_residual_eq_leafEnergy
    {ι : Type*} (s : Finset ι) (w value : ι → ℝ)
    (hmass : routeEBatchWeightMass s w ≠ 0) :
    routeEBatchMeanEnergy s w value + routeEBatchResidual s w value =
      routeEBatchLeafEnergy s w value := by
  have hvar := two_mul_weightedBilinear_eq_rankOne_add_pairwiseDispersion
    s w value value
  simp only [routeEBatchWeightMass] at hmass
  simp only [routeEBatchMeanEnergy, routeEBatchResidual,
    routeEBatchPairwiseDispersion, routeEBatchLeafEnergy,
    routeEBatchWeightMass, pow_two]
  field_simp [hmass]
  ring_nf at hvar ⊢
  exact hvar.symm

/-- Pairwise batch dispersion is nonnegative under nonnegative weights. -/
theorem routeEBatchPairwiseDispersion_nonneg
    {ι : Type*} (s : Finset ι) (w value : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    0 ≤ routeEBatchPairwiseDispersion s w value := by
  unfold routeEBatchPairwiseDispersion
  exact Finset.sum_nonneg fun i hi =>
    Finset.sum_nonneg fun j hj =>
      mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (sq_nonneg _)

/-- With positive weights, zero batch dispersion is exactly the checkerboard
coherence line: every signed leaf value agrees. -/
theorem routeEBatchPairwiseDispersion_eq_zero_iff_constant
    {ι : Type*} (s : Finset ι) (w value : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) :
    routeEBatchPairwiseDispersion s w value = 0 ↔
      ∀ i ∈ s, ∀ j ∈ s, value i = value j := by
  constructor
  · intro hzero i hi j hj
    have houter : ∀ a ∈ s,
        0 ≤ ∑ b ∈ s, w a * w b * (value a - value b) ^ 2 := by
      intro a ha
      exact Finset.sum_nonneg fun b hb =>
        mul_nonneg (mul_nonneg (hw a ha).le (hw b hb).le) (sq_nonneg _)
    have hiZero := (Finset.sum_eq_zero_iff_of_nonneg houter).mp hzero i hi
    have hinner : ∀ b ∈ s,
        0 ≤ w i * w b * (value i - value b) ^ 2 := by
      intro b hb
      exact mul_nonneg (mul_nonneg (hw i hi).le (hw b hb).le) (sq_nonneg _)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg hinner).mp hiZero j hj
    have hcoeff : w i * w j ≠ 0 := mul_ne_zero (hw i hi).ne' (hw j hj).ne'
    have hgap : (value i - value j) ^ 2 = 0 :=
      (mul_eq_zero.mp hij).resolve_left hcoeff
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hgap)
  · intro hconstant
    unfold routeEBatchPairwiseDispersion
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    rw [hconstant i hi j hj, sub_self, zero_pow (by norm_num), mul_zero]

/-- The normalized batch residual has the same exact null space. -/
theorem routeEBatchResidual_eq_zero_iff_constant
    {ι : Type*} (s : Finset ι) (w value : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (hne : s.Nonempty) :
    routeEBatchResidual s w value = 0 ↔
      ∀ i ∈ s, ∀ j ∈ s, value i = value j := by
  have hmassPos : 0 < routeEBatchWeightMass s w := by
    unfold routeEBatchWeightMass
    exact Finset.sum_pos (fun i hi => hw i hi) hne
  rw [routeEBatchResidual, div_eq_zero_iff]
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero,
    ne_of_gt hmassPos, or_false]
  exact routeEBatchPairwiseDispersion_eq_zero_iff_constant s w value hw

end

end RHTower.GibbsGas
