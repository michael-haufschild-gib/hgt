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

/-- The harmonic frame has a sharp coefficient-blind ceiling: its total
energy never exceeds four times reciprocal-prime mass. -/
theorem routeEAntiscaleFrameEnergy_le_four_mul_sum_inv
    (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (t : ℝ) :
    routeEAntiscaleFrameEnergy P t ≤
      4 * ∑ p ∈ P, 1 / (p : ℝ) := by
  rw [routeEAntiscaleFrameEnergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  rw [normSq_one_add_charFn]
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hP p hp
  have hcos : Real.cos (t * Real.log (p : ℝ)) ≤ 1 := Real.cos_le_one _
  have hnum : 2 * (1 + Real.cos (t * Real.log (p : ℝ))) ≤ 4 := by
    linarith
  calc
    2 * (1 + Real.cos (t * Real.log (p : ℝ))) / (p : ℝ) ≤
        4 / (p : ℝ) := div_le_div_of_nonneg_right hnum hpR.le
    _ = 4 * (1 / (p : ℝ)) := by ring

/-- The ceiling is attained by the trivial Mellin phase. -/
theorem routeEAntiscaleFrameEnergy_zero
    (P : Finset ℕ) :
    routeEAntiscaleFrameEnergy P 0 =
      4 * ∑ p ∈ P, 1 / (p : ℝ) := by
  rw [routeEAntiscaleFrameEnergy, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [normSq_one_add_charFn]
  simp
  ring

end

end RHTower.Sieve

namespace RHTower.GibbsGas

noncomputable section

/-- Multiplicative scale attached to one subset of a prime batch. -/
def routeEGibbsBatchScale (T : Finset ℕ) (x : ℝ) : ℝ :=
  (∏ p ∈ T, (p : ℝ)) * x

/-- Expansion of a Gibbs section over all leaves of a disjoint prime batch. -/
def routeEGibbsBatchLeafSum
    (S P : Finset ℕ) (x z : ℝ) : ℝ :=
  ∑ T ∈ P.powerset,
    z ^ T.card * gibbsDiag S (routeEGibbsBatchScale T x) z

/-- Adjoining one batch coordinate splits the leaf sum into the old scale and
the prime-dilated scale. -/
theorem routeEGibbsBatchLeafSum_insert
    (S P : Finset ℕ) {p : ℕ} (hp : p ∉ P) (x z : ℝ) :
    routeEGibbsBatchLeafSum S (insert p P) x z =
      routeEGibbsBatchLeafSum S P x z +
        z * routeEGibbsBatchLeafSum S P ((p : ℝ) * x) z := by
  classical
  have hdisj : Disjoint P.powerset (P.powerset.image (insert p)) := by
    rw [Finset.disjoint_left]
    intro T hT hT'
    rw [Finset.mem_powerset] at hT
    obtain ⟨T', _, rfl⟩ := Finset.mem_image.mp hT'
    exact hp (hT (Finset.mem_insert_self p T'))
  have hinj : ∀ T₁ ∈ P.powerset, ∀ T₂ ∈ P.powerset,
      insert p T₁ = insert p T₂ → T₁ = T₂ := by
    intro T₁ h₁ T₂ h₂ h
    rw [Finset.mem_powerset] at h₁ h₂
    have e₁ : (insert p T₁).erase p = T₁ :=
      Finset.erase_insert (fun hmem => hp (h₁ hmem))
    have e₂ : (insert p T₂).erase p = T₂ :=
      Finset.erase_insert (fun hmem => hp (h₂ hmem))
    rw [← e₁, ← e₂, h]
  rw [routeEGibbsBatchLeafSum, Finset.powerset_insert,
    Finset.sum_union hdisj, Finset.sum_image hinj]
  have hterm : ∀ T ∈ P.powerset,
      z ^ (insert p T).card *
          gibbsDiag S (routeEGibbsBatchScale (insert p T) x) z =
        z * (z ^ T.card *
          gibbsDiag S (routeEGibbsBatchScale T ((p : ℝ) * x)) z) := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    have hpT : p ∉ T := fun hmem => hp (hT hmem)
    rw [Finset.card_insert_of_notMem hpT, pow_succ]
    have hscale : routeEGibbsBatchScale (insert p T) x =
        routeEGibbsBatchScale T ((p : ℝ) * x) := by
      simp only [routeEGibbsBatchScale, Finset.prod_insert hpT]
      ring
    rw [hscale]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  rfl

/-- **Exact source batch expansion.**  A disjoint finite batch expands the
Gibbs section into all multiplicatively dilated leaves with the subset sign
encoded by `z ^ card`. -/
theorem gibbsDiag_union_eq_routeEGibbsBatchLeafSum
    (S P : Finset ℕ) (hdisj : Disjoint S P) (x z : ℝ) :
    gibbsDiag (S ∪ P) x z = routeEGibbsBatchLeafSum S P x z := by
  classical
  induction P using Finset.induction_on generalizing x with
  | empty =>
      simp [routeEGibbsBatchLeafSum, routeEGibbsBatchScale]
  | @insert p P hp ih =>
      have hpS : p ∉ S := by
        intro hpMem
        exact (Finset.disjoint_left.mp hdisj) hpMem
          (Finset.mem_insert_self p P)
      have hdisjP : Disjoint S P := by
        rw [Finset.disjoint_left]
        intro q hqS hqP
        exact (Finset.disjoint_left.mp hdisj) hqS
          (Finset.mem_insert_of_mem hqP)
      have hpUnion : p ∉ S ∪ P := by simp [hpS, hp]
      rw [show S ∪ insert p P = insert p (S ∪ P) by ext q; simp,
        gibbsDiag_insert p (S ∪ P) hpUnion,
        routeEGibbsBatchLeafSum_insert S P hp,
        ih hdisjP, ih hdisjP]

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

/-- Positive partition weight of one multiplicatively dilated Gibbs leaf. -/
def routeEGibbsBatchWeight
    (S : Finset ℕ) (x : ℝ) (T : Finset ℕ) : ℝ :=
  gibbsDiag S (routeEGibbsBatchScale T x) 1

/-- Checkerboard-signed normalized current on one batch leaf. -/
def routeEGibbsBatchSignedValue
    (S : Finset ℕ) (x : ℝ) (T : Finset ℕ) : ℝ :=
  (-1 : ℝ) ^ T.card *
    normalizedGibbsCurrent S (routeEGibbsBatchScale T x)

/-- Batch leaf weights sum to the enlarged positive partition. -/
theorem sum_routeEGibbsBatchWeight_eq_partition
    (S P : Finset ℕ) (hdisj : Disjoint S P) (x : ℝ) :
    (∑ T ∈ P.powerset, routeEGibbsBatchWeight S x T) =
      gibbsDiag (S ∪ P) x 1 := by
  rw [gibbsDiag_union_eq_routeEGibbsBatchLeafSum S P hdisj]
  simp [routeEGibbsBatchLeafSum, routeEGibbsBatchWeight]

/-- Weighted checkerboard leaves sum to the enlarged signed current. -/
theorem sum_routeEGibbsBatchWeight_mul_signedValue_eq_current
    (S P : Finset ℕ) (hdisj : Disjoint S P) (x : ℝ) :
    (∑ T ∈ P.powerset,
      routeEGibbsBatchWeight S x T *
        routeEGibbsBatchSignedValue S x T) =
      gibbsDiag (S ∪ P) x (-1) := by
  rw [gibbsDiag_union_eq_routeEGibbsBatchLeafSum S P hdisj]
  unfold routeEGibbsBatchLeafSum
  apply Finset.sum_congr rfl
  intro T hT
  unfold routeEGibbsBatchWeight routeEGibbsBatchSignedValue
  unfold normalizedGibbsCurrent
  have hZ : gibbsDiag S (routeEGibbsBatchScale T x) 1 ≠ 0 :=
    ne_of_gt (gibbs_partition_pos S (routeEGibbsBatchScale T x))
  field_simp [hZ]

/-- The abstract batch mean energy is exactly the enlarged Gibbs current
energy `J^(2 : ℕ) / Z`. -/
theorem routeEGibbsBatchMeanEnergy_eq_currentEnergy
    (S P : Finset ℕ) (hdisj : Disjoint S P) (x : ℝ) :
    routeEBatchMeanEnergy P.powerset
        (routeEGibbsBatchWeight S x)
        (routeEGibbsBatchSignedValue S x) =
      gibbsDiag (S ∪ P) x (-1) ^ 2 / gibbsDiag (S ∪ P) x 1 := by
  unfold routeEBatchMeanEnergy routeEBatchWeightMass
  rw [sum_routeEGibbsBatchWeight_mul_signedValue_eq_current S P hdisj,
    sum_routeEGibbsBatchWeight_eq_partition S P hdisj]

/-- **Source-specialized order-free batch polarization.**  Enlarged Gibbs
current energy plus checkerboard dispersion equals the complete common-prefix
leaf energy. -/
theorem routeEGibbsBatch_currentEnergy_add_residual_eq_leafEnergy
    (S P : Finset ℕ) (hdisj : Disjoint S P) (x : ℝ) :
    gibbsDiag (S ∪ P) x (-1) ^ 2 / gibbsDiag (S ∪ P) x 1 +
        routeEBatchResidual P.powerset
          (routeEGibbsBatchWeight S x)
          (routeEGibbsBatchSignedValue S x) =
      routeEBatchLeafEnergy P.powerset
        (routeEGibbsBatchWeight S x)
        (routeEGibbsBatchSignedValue S x) := by
  have hmass : routeEBatchWeightMass P.powerset
      (routeEGibbsBatchWeight S x) ≠ 0 := by
    unfold routeEBatchWeightMass
    rw [sum_routeEGibbsBatchWeight_eq_partition S P hdisj]
    exact ne_of_gt (gibbs_partition_pos (S ∪ P) x)
  rw [← routeEGibbsBatchMeanEnergy_eq_currentEnergy S P hdisj]
  exact routeEBatchMeanEnergy_add_residual_eq_leafEnergy
    P.powerset (routeEGibbsBatchWeight S x)
      (routeEGibbsBatchSignedValue S x) hmass

/-- **Exact batch escape mode.**  The source batch residual vanishes precisely
when one common prefix current follows the full subset checkerboard. -/
theorem routeEGibbsBatchResidual_eq_zero_iff_checkerboard
    (S P : Finset ℕ) (x : ℝ) :
    routeEBatchResidual P.powerset
        (routeEGibbsBatchWeight S x)
        (routeEGibbsBatchSignedValue S x) = 0 ↔
      ∀ T ∈ P.powerset, ∀ U ∈ P.powerset,
        routeEGibbsBatchSignedValue S x T =
          routeEGibbsBatchSignedValue S x U := by
  apply routeEBatchResidual_eq_zero_iff_constant
  · intro T hT
    exact gibbs_partition_pos S (routeEGibbsBatchScale T x)
  · exact ⟨∅, Finset.empty_mem_powerset P⟩

end

end RHTower.GibbsGas
