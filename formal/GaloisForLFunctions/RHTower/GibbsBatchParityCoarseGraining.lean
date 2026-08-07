import GaloisForLFunctions.RHTower.GibbsAntiscaleFirstTraceFrame

/-!
# Route E parity-coarse-grained batch rigidity

The order-free Gibbs batch residual splits exactly into three nonnegative
pieces: within-even dispersion, within-odd dispersion, and one coarse
even/odd antiscale defect.  Consequently every small-residual escape must be
simultaneously rigid inside both parity classes and nearly opposite between
their weighted means.
-/

open scoped BigOperators

namespace RHTower.GibbsGas

noncomputable section

/-- Positive mass carried by one class of a finite batch. -/
def routeEBatchClassMass {ι : Type*} (s : Finset ι) (c : ι → Prop)
    [DecidablePred c] (w : ι → ℝ) : ℝ :=
  routeEBatchWeightMass (s.filter c) w

/-- Weighted, unsigned numerator carried by one class of a finite batch. -/
def routeEBatchClassNumerator {ι : Type*} (s : Finset ι)
    (c : ι → Prop) [DecidablePred c] (w value : ι → ℝ) : ℝ :=
  ∑ i ∈ s.filter c, w i * value i

/-- Flip the value on the negative class. -/
def routeEBatchSignedByClass {ι : Type*} (c : ι → Prop)
    [DecidablePred c] (value : ι → ℝ) (i : ι) : ℝ :=
  if c i then value i else -value i

/-- Coarse antiscale defect between the two weighted class means. -/
def routeEBatchParityCoarseDefect {ι : Type*} (s : Finset ι)
    (c : ι → Prop) [DecidablePred c] (w value : ι → ℝ) : ℝ :=
  let Wp := routeEBatchClassMass s c w
  let Wn := routeEBatchClassMass s (fun i => ¬ c i) w
  let Kp := routeEBatchClassNumerator s c w value
  let Kn := routeEBatchClassNumerator s (fun i => ¬ c i) w value
  (Wn * Kp + Wp * Kn) ^ 2 / ((Wp + Wn) * Wp * Wn)

/-- Total mass in parity-class coordinates. -/
def routeEBatchParityTotalMass {ι : Type*} (s : Finset ι)
    (c : ι → Prop) [DecidablePred c] (w : ι → ℝ) : ℝ :=
  routeEBatchClassMass s c w +
    routeEBatchClassMass s (fun i => ¬ c i) w

/-- Unsigned value numerator in parity-class coordinates. -/
def routeEBatchParityUnsignedNumerator {ι : Type*} (s : Finset ι)
    (c : ι → Prop) [DecidablePred c] (w value : ι → ℝ) : ℝ :=
  routeEBatchClassNumerator s c w value +
    routeEBatchClassNumerator s (fun i => ¬ c i) w value

/-- Checkerboard-signed value numerator in parity-class coordinates. -/
def routeEBatchParitySignedNumerator {ι : Type*} (s : Finset ι)
    (c : ι → Prop) [DecidablePred c] (w value : ι → ℝ) : ℝ :=
  routeEBatchClassNumerator s c w value -
    routeEBatchClassNumerator s (fun i => ¬ c i) w value

/-- Difference between positive- and negative-class masses. -/
def routeEBatchParityMassImbalance {ι : Type*} (s : Finset ι)
    (c : ι → Prop) [DecidablePred c] (w : ι → ℝ) : ℝ :=
  routeEBatchClassMass s c w -
    routeEBatchClassMass s (fun i => ¬ c i) w

/-- Determinant detecting failure of opposite parity-class means. -/
def routeEBatchParityAntiscaleDeterminant {ι : Type*} (s : Finset ι)
    (c : ι → Prop) [DecidablePred c] (w value : ι → ℝ) : ℝ :=
  routeEBatchParityTotalMass s c w *
      routeEBatchParityUnsignedNumerator s c w value -
    routeEBatchParityMassImbalance s c w *
      routeEBatchParitySignedNumerator s c w value

/-- Companion determinant detecting inequality of the two unsigned
parity-class means; it vanishes for an exactly factorized class response. -/
def routeEBatchParityNonproductDeterminant {ι : Type*} (s : Finset ι)
    (c : ι → Prop) [DecidablePred c] (w value : ι → ℝ) : ℝ :=
  routeEBatchParityTotalMass s c w *
      routeEBatchParitySignedNumerator s c w value -
    routeEBatchParityMassImbalance s c w *
      routeEBatchParityUnsignedNumerator s c w value

/-- The antiscale determinant is twice the coarse same-direction numerator. -/
theorem routeEBatchParityAntiscaleDeterminant_eq
    {ι : Type*} (s : Finset ι) (c : ι → Prop) [DecidablePred c]
    (w value : ι → ℝ) :
    routeEBatchParityAntiscaleDeterminant s c w value =
      2 * (routeEBatchClassMass s (fun i => ¬ c i) w *
          routeEBatchClassNumerator s c w value +
        routeEBatchClassMass s c w *
          routeEBatchClassNumerator s (fun i => ¬ c i) w value) := by
  unfold routeEBatchParityAntiscaleDeterminant routeEBatchParityTotalMass
    routeEBatchParityUnsignedNumerator routeEBatchParityMassImbalance
    routeEBatchParitySignedNumerator
  ring

/-- The companion determinant is twice the cross-class mean-difference
numerator and vanishes when both unsigned class means agree. -/
theorem routeEBatchParityNonproductDeterminant_eq
    {ι : Type*} (s : Finset ι) (c : ι → Prop) [DecidablePred c]
    (w value : ι → ℝ) :
    routeEBatchParityNonproductDeterminant s c w value =
      2 * (routeEBatchClassMass s (fun i => ¬ c i) w *
          routeEBatchClassNumerator s c w value -
        routeEBatchClassMass s c w *
          routeEBatchClassNumerator s (fun i => ¬ c i) w value) := by
  unfold routeEBatchParityNonproductDeterminant routeEBatchParityTotalMass
    routeEBatchParityUnsignedNumerator routeEBatchParityMassImbalance
    routeEBatchParitySignedNumerator
  ring

/-- Scalar determinant form of the coarse antiscale defect. -/
theorem routeEScalarParityCoarseDeterminantIdentity
    (Wp Wn Kp Kn : ℝ) (hp : Wp ≠ 0) (hn : Wn ≠ 0)
    (hs : Wp + Wn ≠ 0) :
    (Wn * Kp + Wp * Kn) ^ 2 / ((Wp + Wn) * Wp * Wn) =
      ((Wp + Wn) * (Kp + Kn) - (Wp - Wn) * (Kp - Kn)) ^ 2 /
        ((Wp + Wn) * ((Wp + Wn) ^ 2 - (Wp - Wn) ^ 2)) := by
  have hdisc : (Wp + Wn) ^ 2 - (Wp - Wn) ^ 2 ≠ 0 := by
    have hfour : (4 : ℝ) * Wp * Wn ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hp) hn
    convert hfour using 1 <;> ring
  field_simp [hp, hn, hs, hdisc]
  ring

/-- The coarse defect is the squared antiscale determinant divided by the
exact parity-balance discriminant. -/
theorem routeEBatchParityCoarseDefect_eq_antiscaleDeterminant
    {ι : Type*} (s : Finset ι) (c : ι → Prop) [DecidablePred c]
    (w value : ι → ℝ)
    (hp : routeEBatchClassMass s c w ≠ 0)
    (hn : routeEBatchClassMass s (fun i => ¬ c i) w ≠ 0)
    (ht : routeEBatchParityTotalMass s c w ≠ 0) :
    routeEBatchParityCoarseDefect s c w value =
      routeEBatchParityAntiscaleDeterminant s c w value ^ 2 /
        (routeEBatchParityTotalMass s c w *
          (routeEBatchParityTotalMass s c w ^ 2 -
            routeEBatchParityMassImbalance s c w ^ 2)) := by
  simpa [routeEBatchParityCoarseDefect,
    routeEBatchParityAntiscaleDeterminant,
    routeEBatchParityTotalMass, routeEBatchParityUnsignedNumerator,
    routeEBatchParitySignedNumerator, routeEBatchParityMassImbalance] using
    routeEScalarParityCoarseDeterminantIdentity
      (routeEBatchClassMass s c w)
      (routeEBatchClassMass s (fun i => ¬ c i) w)
      (routeEBatchClassNumerator s c w value)
      (routeEBatchClassNumerator s (fun i => ¬ c i) w value)
      hp hn ht

/-- Scalar two-class polarization underlying the parity coarse graining. -/
theorem routeEScalarParityCoarseIdentity
    (Wp Wn Kp Kn : ℝ) (hp : Wp ≠ 0) (hn : Wn ≠ 0)
    (hs : Wp + Wn ≠ 0) :
    (Kp - Kn) ^ 2 / (Wp + Wn) +
        (Wn * Kp + Wp * Kn) ^ 2 / ((Wp + Wn) * Wp * Wn) =
      Kp ^ 2 / Wp + Kn ^ 2 / Wn := by
  field_simp [hp, hn, hs]
  ring

/-- **Exact two-class ANOVA.**  Signed mean energy, both within-class
residuals, and the coarse antiscale defect exhaust the unsigned leaf energy. -/
theorem routeEBatchMeanEnergy_add_withinClassResiduals_add_coarse_eq_leafEnergy
    {ι : Type*} (s : Finset ι) (c : ι → Prop) [DecidablePred c]
    (w value : ι → ℝ)
    (hp : routeEBatchClassMass s c w ≠ 0)
    (hn : routeEBatchClassMass s (fun i => ¬ c i) w ≠ 0)
    (ht : routeEBatchWeightMass s w ≠ 0) :
    routeEBatchMeanEnergy s w (routeEBatchSignedByClass c value) +
        routeEBatchResidual (s.filter c) w value +
        routeEBatchResidual (s.filter fun i => ¬ c i) w value +
        routeEBatchParityCoarseDefect s c w value =
      routeEBatchLeafEnergy s w (routeEBatchSignedByClass c value) := by
  classical
  have hmass :
      routeEBatchClassMass s c w +
          routeEBatchClassMass s (fun i => ¬ c i) w =
        routeEBatchWeightMass s w := by
    simpa [routeEBatchClassMass, routeEBatchWeightMass] using
      Finset.sum_filter_add_sum_filter_not s c w
  have hnum :
      (∑ i ∈ s, w i * routeEBatchSignedByClass c value i) =
        routeEBatchClassNumerator s c w value -
          routeEBatchClassNumerator s (fun i => ¬ c i) w value := by
    rw [← Finset.sum_filter_add_sum_filter_not s c
      (fun i => w i * routeEBatchSignedByClass c value i)]
    simp only [routeEBatchClassNumerator, routeEBatchSignedByClass]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_filter] at hi
      simp [hi.2]
    · rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_filter] at hi
      simp [hi.2]
  have hleaf :
      routeEBatchLeafEnergy s w (routeEBatchSignedByClass c value) =
        routeEBatchLeafEnergy (s.filter c) w value +
          routeEBatchLeafEnergy (s.filter fun i => ¬ c i) w value := by
    unfold routeEBatchLeafEnergy
    rw [← Finset.sum_filter_add_sum_filter_not s c
      (fun i => w i * routeEBatchSignedByClass c value i ^ 2)]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_filter] at hi
      simp [routeEBatchSignedByClass, hi.2]
    · apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_filter] at hi
      simp [routeEBatchSignedByClass, hi.2]
  have hpId := routeEBatchMeanEnergy_add_residual_eq_leafEnergy
    (s.filter c) w value hp
  have hnId := routeEBatchMeanEnergy_add_residual_eq_leafEnergy
    (s.filter fun i => ¬ c i) w value hn
  have hsum : routeEBatchClassMass s c w +
      routeEBatchClassMass s (fun i => ¬ c i) w ≠ 0 := by
    rw [hmass]
    exact ht
  have hcoarse :
      routeEBatchMeanEnergy s w (routeEBatchSignedByClass c value) +
          routeEBatchParityCoarseDefect s c w value =
        routeEBatchMeanEnergy (s.filter c) w value +
          routeEBatchMeanEnergy (s.filter fun i => ¬ c i) w value := by
    unfold routeEBatchMeanEnergy
    rw [hnum]
    rw [← hmass]
    simpa [routeEBatchParityCoarseDefect, routeEBatchClassMass,
      routeEBatchClassNumerator] using
      routeEScalarParityCoarseIdentity
        (routeEBatchClassMass s c w)
        (routeEBatchClassMass s (fun i => ¬ c i) w)
        (routeEBatchClassNumerator s c w value)
        (routeEBatchClassNumerator s (fun i => ¬ c i) w value)
        hp hn hsum
  calc
    routeEBatchMeanEnergy s w (routeEBatchSignedByClass c value) +
          routeEBatchResidual (s.filter c) w value +
          routeEBatchResidual (s.filter fun i => ¬ c i) w value +
          routeEBatchParityCoarseDefect s c w value =
        (routeEBatchMeanEnergy s w (routeEBatchSignedByClass c value) +
          routeEBatchParityCoarseDefect s c w value) +
          routeEBatchResidual (s.filter c) w value +
          routeEBatchResidual (s.filter fun i => ¬ c i) w value := by ring
    _ = (routeEBatchMeanEnergy (s.filter c) w value +
          routeEBatchMeanEnergy (s.filter fun i => ¬ c i) w value) +
          routeEBatchResidual (s.filter c) w value +
          routeEBatchResidual (s.filter fun i => ¬ c i) w value := by
      rw [hcoarse]
    _ = (routeEBatchMeanEnergy (s.filter c) w value +
          routeEBatchResidual (s.filter c) w value) +
        (routeEBatchMeanEnergy (s.filter fun i => ¬ c i) w value +
          routeEBatchResidual (s.filter fun i => ¬ c i) w value) := by ring
    _ = routeEBatchLeafEnergy (s.filter c) w value +
        routeEBatchLeafEnergy (s.filter fun i => ¬ c i) w value := by
      rw [hpId, hnId]
    _ = routeEBatchLeafEnergy s w (routeEBatchSignedByClass c value) :=
      hleaf.symm

/-- Residual form of the exact two-class decomposition. -/
theorem routeEBatchResidual_eq_withinClassResiduals_add_coarse
    {ι : Type*} (s : Finset ι) (c : ι → Prop) [DecidablePred c]
    (w value : ι → ℝ)
    (hp : routeEBatchClassMass s c w ≠ 0)
    (hn : routeEBatchClassMass s (fun i => ¬ c i) w ≠ 0)
    (ht : routeEBatchWeightMass s w ≠ 0) :
    routeEBatchResidual s w (routeEBatchSignedByClass c value) =
      routeEBatchResidual (s.filter c) w value +
        routeEBatchResidual (s.filter fun i => ¬ c i) w value +
          routeEBatchParityCoarseDefect s c w value := by
  have hfull := routeEBatchMeanEnergy_add_residual_eq_leafEnergy
    s w (routeEBatchSignedByClass c value) ht
  have hsplit :=
    routeEBatchMeanEnergy_add_withinClassResiduals_add_coarse_eq_leafEnergy
      s c w value hp hn ht
  linarith

/-- A finite positive-weight residual is nonnegative. -/
theorem routeEBatchResidual_nonneg
    {ι : Type*} (s : Finset ι) (w value : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hmass : 0 ≤ routeEBatchWeightMass s w) :
    0 ≤ routeEBatchResidual s w value := by
  unfold routeEBatchResidual
  exact div_nonneg
    (routeEBatchPairwiseDispersion_nonneg s w value hw)
    (mul_nonneg (by norm_num) hmass)

/-- The coarse parity defect is nonnegative for positive class masses. -/
theorem routeEBatchParityCoarseDefect_nonneg
    {ι : Type*} (s : Finset ι) (c : ι → Prop) [DecidablePred c]
    (w value : ι → ℝ)
    (hp : 0 < routeEBatchClassMass s c w)
    (hn : 0 < routeEBatchClassMass s (fun i => ¬ c i) w) :
    0 ≤ routeEBatchParityCoarseDefect s c w value := by
  unfold routeEBatchParityCoarseDefect
  positivity

/-- **Quantitative near-escape rigidity.**  A small signed residual forces
both within-class residuals and the coarse antiscale defect to be small. -/
theorem routeEBatchNearEscape_rigidity
    {ι : Type*} (s : Finset ι) (c : ι → Prop) [DecidablePred c]
    (w value : ι → ℝ) (eta : ℝ)
    (hw : ∀ i ∈ s, 0 < w i)
    (hpos : (s.filter c).Nonempty)
    (hneg : (s.filter fun i => ¬ c i).Nonempty)
    (hsmall : routeEBatchResidual s w
      (routeEBatchSignedByClass c value) ≤ eta) :
    routeEBatchResidual (s.filter c) w value ≤ eta ∧
      routeEBatchResidual (s.filter fun i => ¬ c i) w value ≤ eta ∧
        routeEBatchParityCoarseDefect s c w value ≤ eta := by
  have hp : 0 < routeEBatchClassMass s c w := by
    unfold routeEBatchClassMass routeEBatchWeightMass
    exact Finset.sum_pos
      (fun i hi => hw i (Finset.mem_filter.mp hi).1) hpos
  have hn : 0 < routeEBatchClassMass s (fun i => ¬ c i) w := by
    unfold routeEBatchClassMass routeEBatchWeightMass
    exact Finset.sum_pos
      (fun i hi => hw i (Finset.mem_filter.mp hi).1) hneg
  have ht : 0 < routeEBatchWeightMass s w := by
    have hs : s.Nonempty := by
      rcases hpos with ⟨i, hi⟩
      exact ⟨i, (Finset.mem_filter.mp hi).1⟩
    unfold routeEBatchWeightMass
    exact Finset.sum_pos hw hs
  have hdecomp := routeEBatchResidual_eq_withinClassResiduals_add_coarse
    s c w value hp.ne' hn.ne' ht.ne'
  have hposResidual :
      0 ≤ routeEBatchResidual (s.filter c) w value := by
    apply routeEBatchResidual_nonneg
    · intro i hi
      exact (hw i (Finset.mem_filter.mp hi).1).le
    · exact hp.le
  have hnegResidual :
      0 ≤ routeEBatchResidual (s.filter fun i => ¬ c i) w value := by
    apply routeEBatchResidual_nonneg
    · intro i hi
      exact (hw i (Finset.mem_filter.mp hi).1).le
    · exact hn.le
  have hcoarse := routeEBatchParityCoarseDefect_nonneg s c w value hp hn
  constructor
  · linarith
  constructor <;> linarith

/-- Exact three-term nullspace of the parity-coarse decomposition. -/
theorem routeEBatchResidual_eq_zero_iff_classResiduals_and_coarse
    {ι : Type*} (s : Finset ι) (c : ι → Prop) [DecidablePred c]
    (w value : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i)
    (hpos : (s.filter c).Nonempty)
    (hneg : (s.filter fun i => ¬ c i).Nonempty) :
    routeEBatchResidual s w (routeEBatchSignedByClass c value) = 0 ↔
      routeEBatchResidual (s.filter c) w value = 0 ∧
        routeEBatchResidual (s.filter fun i => ¬ c i) w value = 0 ∧
          routeEBatchParityCoarseDefect s c w value = 0 := by
  have hp : 0 < routeEBatchClassMass s c w := by
    unfold routeEBatchClassMass routeEBatchWeightMass
    exact Finset.sum_pos
      (fun i hi => hw i (Finset.mem_filter.mp hi).1) hpos
  have hn : 0 < routeEBatchClassMass s (fun i => ¬ c i) w := by
    unfold routeEBatchClassMass routeEBatchWeightMass
    exact Finset.sum_pos
      (fun i hi => hw i (Finset.mem_filter.mp hi).1) hneg
  have ht : 0 < routeEBatchWeightMass s w := by
    have hs : s.Nonempty := by
      rcases hpos with ⟨i, hi⟩
      exact ⟨i, (Finset.mem_filter.mp hi).1⟩
    unfold routeEBatchWeightMass
    exact Finset.sum_pos hw hs
  have hdecomp := routeEBatchResidual_eq_withinClassResiduals_add_coarse
    s c w value hp.ne' hn.ne' ht.ne'
  have hposResidual :
      0 ≤ routeEBatchResidual (s.filter c) w value := by
    apply routeEBatchResidual_nonneg
    · intro i hi
      exact (hw i (Finset.mem_filter.mp hi).1).le
    · exact hp.le
  have hnegResidual :
      0 ≤ routeEBatchResidual (s.filter fun i => ¬ c i) w value := by
    apply routeEBatchResidual_nonneg
    · intro i hi
      exact (hw i (Finset.mem_filter.mp hi).1).le
    · exact hn.le
  have hcoarse := routeEBatchParityCoarseDefect_nonneg s c w value hp hn
  constructor
  · intro hzero
    constructor
    · linarith
    constructor <;> linarith
  · rintro ⟨hplus, hminus, hcoarseZero⟩
    rw [hdecomp, hplus, hminus, hcoarseZero]
    ring

/-- Zero signed residual is exactly rigidity inside both classes together
with vanishing coarse antiscale defect. -/
theorem routeEBatchResidual_eq_zero_iff_classConstant_and_coarse
    {ι : Type*} (s : Finset ι) (c : ι → Prop) [DecidablePred c]
    (w value : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i)
    (hpos : (s.filter c).Nonempty)
    (hneg : (s.filter fun i => ¬ c i).Nonempty) :
    routeEBatchResidual s w (routeEBatchSignedByClass c value) = 0 ↔
      (∀ i ∈ s.filter c, ∀ j ∈ s.filter c, value i = value j) ∧
        (∀ i ∈ s.filter (fun i => ¬ c i),
          ∀ j ∈ s.filter (fun i => ¬ c i), value i = value j) ∧
        routeEBatchParityCoarseDefect s c w value = 0 := by
  rw [routeEBatchResidual_eq_zero_iff_classResiduals_and_coarse
    s c w value hw hpos hneg]
  rw [routeEBatchResidual_eq_zero_iff_constant
    (s.filter c) w value
    (fun i hi => hw i (Finset.mem_filter.mp hi).1) hpos]
  rw [routeEBatchResidual_eq_zero_iff_constant
    (s.filter fun i => ¬ c i) w value
    (fun i hi => hw i (Finset.mem_filter.mp hi).1) hneg]

/-- Unsigned common-prefix current observed at one multiplicative batch leaf. -/
def routeEGibbsBatchBaseValue
    (S : Finset ℕ) (x : ℝ) (T : Finset ℕ) : ℝ :=
  normalizedGibbsCurrent S (routeEGibbsBatchScale T x)

/-- Even/odd class signing is the Gibbs checkerboard sign. -/
theorem routeEGibbsBatchSignedByEven_eq_signedValue
    (S : Finset ℕ) (x : ℝ) :
    routeEBatchSignedByClass (fun T : Finset ℕ => Even T.card)
        (routeEGibbsBatchBaseValue S x) =
      routeEGibbsBatchSignedValue S x := by
  funext T
  simp [routeEBatchSignedByClass, routeEGibbsBatchBaseValue,
    routeEGibbsBatchSignedValue, neg_one_pow_eq_ite]

/-- The even Gibbs batch class has positive mass. -/
theorem routeEGibbsBatch_evenClassMass_pos
    (S P : Finset ℕ) (x : ℝ) :
    0 < routeEBatchClassMass P.powerset
      (fun T : Finset ℕ => Even T.card) (routeEGibbsBatchWeight S x) := by
  unfold routeEBatchClassMass routeEBatchWeightMass
  apply Finset.sum_pos
  · intro T hT
    exact gibbs_partition_pos S (routeEGibbsBatchScale T x)
  · exact ⟨∅, by simp⟩

/-- A nonempty prime batch has positive odd-class Gibbs mass. -/
theorem routeEGibbsBatch_oddClassMass_pos
    (S P : Finset ℕ) (hP : P.Nonempty) (x : ℝ) :
    0 < routeEBatchClassMass P.powerset
      (fun T : Finset ℕ => ¬ Even T.card) (routeEGibbsBatchWeight S x) := by
  unfold routeEBatchClassMass routeEBatchWeightMass
  apply Finset.sum_pos
  · intro T hT
    exact gibbs_partition_pos S (routeEGibbsBatchScale T x)
  · rcases hP with ⟨p, hp⟩
    exact ⟨{p}, by simp [hp]⟩

/-- **Source-specialized parity-coarse batch polarization.**  Gibbs current
energy plus even/odd within-class variation and the coarse antiscale defect
equals the complete unsigned common-prefix leaf energy. -/
theorem routeEGibbsBatch_currentEnergy_add_parityCoarse_eq_leafEnergy
    (S P : Finset ℕ) (hdisj : Disjoint S P) (hP : P.Nonempty) (x : ℝ) :
    gibbsDiag (S ∪ P) x (-1) ^ 2 / gibbsDiag (S ∪ P) x 1 +
        routeEBatchResidual
          (P.powerset.filter fun T : Finset ℕ => Even T.card)
          (routeEGibbsBatchWeight S x) (routeEGibbsBatchBaseValue S x) +
        routeEBatchResidual
          (P.powerset.filter fun T : Finset ℕ => ¬ Even T.card)
          (routeEGibbsBatchWeight S x) (routeEGibbsBatchBaseValue S x) +
        routeEBatchParityCoarseDefect P.powerset
          (fun T : Finset ℕ => Even T.card)
          (routeEGibbsBatchWeight S x) (routeEGibbsBatchBaseValue S x) =
      routeEBatchLeafEnergy P.powerset
        (routeEGibbsBatchWeight S x) (routeEGibbsBatchSignedValue S x) := by
  have hp := routeEGibbsBatch_evenClassMass_pos S P x
  have hn := routeEGibbsBatch_oddClassMass_pos S P hP x
  have ht : routeEBatchWeightMass P.powerset
      (routeEGibbsBatchWeight S x) ≠ 0 := by
    unfold routeEBatchWeightMass
    rw [sum_routeEGibbsBatchWeight_eq_partition S P hdisj]
    exact (gibbs_partition_pos (S ∪ P) x).ne'
  have h :=
    routeEBatchMeanEnergy_add_withinClassResiduals_add_coarse_eq_leafEnergy
      P.powerset (fun T : Finset ℕ => Even T.card)
      (routeEGibbsBatchWeight S x) (routeEGibbsBatchBaseValue S x)
      hp.ne' hn.ne' ht
  rw [routeEGibbsBatchSignedByEven_eq_signedValue S x] at h
  rw [routeEGibbsBatchMeanEnergy_eq_currentEnergy S P hdisj] at h
  exact h

/-- Source-level quantitative rigidity: any small Gibbs batch residual forces
both same-parity residuals and the coarse antiscale term below the same budget. -/
theorem routeEGibbsBatch_nearEscape_rigidity
    (S P : Finset ℕ) (hP : P.Nonempty) (x eta : ℝ)
    (hsmall : routeEBatchResidual P.powerset
      (routeEGibbsBatchWeight S x) (routeEGibbsBatchSignedValue S x) ≤ eta) :
    routeEBatchResidual
        (P.powerset.filter fun T : Finset ℕ => Even T.card)
        (routeEGibbsBatchWeight S x) (routeEGibbsBatchBaseValue S x) ≤ eta ∧
      routeEBatchResidual
        (P.powerset.filter fun T : Finset ℕ => ¬ Even T.card)
        (routeEGibbsBatchWeight S x) (routeEGibbsBatchBaseValue S x) ≤ eta ∧
      routeEBatchParityCoarseDefect P.powerset
        (fun T : Finset ℕ => Even T.card)
        (routeEGibbsBatchWeight S x) (routeEGibbsBatchBaseValue S x) ≤ eta := by
  rw [← routeEGibbsBatchSignedByEven_eq_signedValue S x] at hsmall
  apply routeEBatchNearEscape_rigidity
    P.powerset (fun T : Finset ℕ => Even T.card)
      (routeEGibbsBatchWeight S x) (routeEGibbsBatchBaseValue S x) eta
  · intro T hT
    exact gibbs_partition_pos S (routeEGibbsBatchScale T x)
  · exact ⟨∅, by simp⟩
  · rcases hP with ⟨p, hp⟩
    exact ⟨{p}, by simp [hp]⟩
  · exact hsmall

/-- Exact Gibbs escape classification after parity coarse graining. -/
theorem routeEGibbsBatchResidual_eq_zero_iff_parityRigidity
    (S P : Finset ℕ) (hP : P.Nonempty) (x : ℝ) :
    routeEBatchResidual P.powerset
        (routeEGibbsBatchWeight S x) (routeEGibbsBatchSignedValue S x) = 0 ↔
      (∀ T ∈ P.powerset.filter (fun T : Finset ℕ => Even T.card),
        ∀ U ∈ P.powerset.filter (fun T : Finset ℕ => Even T.card),
          routeEGibbsBatchBaseValue S x T = routeEGibbsBatchBaseValue S x U) ∧
      (∀ T ∈ P.powerset.filter (fun T : Finset ℕ => ¬ Even T.card),
        ∀ U ∈ P.powerset.filter (fun T : Finset ℕ => ¬ Even T.card),
          routeEGibbsBatchBaseValue S x T = routeEGibbsBatchBaseValue S x U) ∧
      routeEBatchParityCoarseDefect P.powerset
        (fun T : Finset ℕ => Even T.card)
        (routeEGibbsBatchWeight S x) (routeEGibbsBatchBaseValue S x) = 0 := by
  rw [← routeEGibbsBatchSignedByEven_eq_signedValue S x]
  apply routeEBatchResidual_eq_zero_iff_classConstant_and_coarse
  · intro T hT
    exact gibbs_partition_pos S (routeEGibbsBatchScale T x)
  · exact ⟨∅, by simp⟩
  · rcases hP with ⟨p, hp⟩
    exact ⟨{p}, by simp [hp]⟩

end

end RHTower.GibbsGas
