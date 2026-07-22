import GaloisForLFunctions.HilbertMetric.CCRDimensionFluctuation
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# CCR power-concavity and finite block completion

This module turns the finite CCR dimension--fluctuation identity into an exact curvature law.
For a smooth log-volume whose logarithmic-scale mean and variance are represented by a `d`-mode
CCR compression, the log-volume is convex in logarithmic scale and concave after the change of
variable `u = t ^ d`.  Its power-scale second derivative is not merely nonpositive: after the
dimension normalization it is exactly the negative sum of the mixed-commutator and traceless
leakage energies.

The first section also discharges the finite block connector.  A commuting full matrix tuple
satisfying the canonical commutation relations and preserving a coordinate summand automatically
produces the rectangular completion required by `CCRDimensionFluctuation`.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

variable {I n m : Type*} [Fintype I] [DecidableEq I]
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Upper-left compression block of a finite full operator tuple. -/
def fullCCRCompressionBlock
    (T : I → Matrix (n ⊕ m) (n ⊕ m) ℝ) (i : I) : Matrix n n ℝ :=
  fun a b => T i (Sum.inl a) (Sum.inl b)

/-- Upper-right leakage block of a finite full operator tuple. -/
def fullCCRLeakageBlock
    (T : I → Matrix (n ⊕ m) (n ⊕ m) ℝ) (i : I) : Matrix n m ℝ :=
  fun a b => T i (Sum.inl a) (Sum.inr b)

/-- The first coordinate summand is invariant under every full operator. -/
def IsInvariantFullCompression
    (T : I → Matrix (n ⊕ m) (n ⊕ m) ℝ) : Prop :=
  ∀ i a b, T i (Sum.inr a) (Sum.inl b) = 0

/-- Pairwise commutativity of the full operator tuple. -/
def IsCommutingFullTuple
    (T : I → Matrix (n ⊕ m) (n ⊕ m) ℝ) : Prop :=
  ∀ i j, T i * T j = T j * T i

/-- Exact canonical commutation relations for a finite full matrix tuple. -/
def IsFullCCRMatrixTuple
    (T : I → Matrix (n ⊕ m) (n ⊕ m) ℝ) : Prop :=
  ∀ i j, T i * (T j).transpose =
    (if i = j then 1 else 0) + (T j).transpose * T i

omit [Fintype I] [DecidableEq I] [DecidableEq n] [DecidableEq m] in
/-- Commutativity descends to the upper-left blocks of an invariant summand. -/
theorem fullCCRCompressionBlock_commutes
    (T : I → Matrix (n ⊕ m) (n ⊕ m) ℝ)
    (hinv : IsInvariantFullCompression T) (hcomm : IsCommutingFullTuple T) :
    IsCommutingCCRCompression (fullCCRCompressionBlock T) := by
  intro i j
  ext a b
  have h := congrArg (fun M : Matrix (n ⊕ m) (n ⊕ m) ℝ =>
    M (Sum.inl a) (Sum.inl b)) (hcomm i j)
  simp only [Matrix.mul_apply, Fintype.sum_sum_type] at h
  simp only [Matrix.mul_apply, fullCCRCompressionBlock]
  unfold IsInvariantFullCompression at hinv
  have hzero_i : (∑ x : m, T i (Sum.inl a) (Sum.inr x) *
      T j (Sum.inr x) (Sum.inl b)) = 0 := by simp [hinv]
  have hzero_j : (∑ x : m, T j (Sum.inl a) (Sum.inr x) *
      T i (Sum.inr x) (Sum.inl b)) = 0 := by simp [hinv]
  rw [hzero_i, hzero_j, add_zero, add_zero] at h
  exact h

omit [Fintype I] in
/-- The upper-right blocks supply the exact rectangular CCR completion of the compression. -/
theorem fullCCRLeakageBlock_isCCRCompletion
    (T : I → Matrix (n ⊕ m) (n ⊕ m) ℝ)
    (hinv : IsInvariantFullCompression T) (hccr : IsFullCCRMatrixTuple T) :
    IsCCRCompletion (fullCCRCompressionBlock T) (fullCCRLeakageBlock T) := by
  intro i j
  ext a b
  have h := congrArg (fun M : Matrix (n ⊕ m) (n ⊕ m) ℝ =>
    M (Sum.inl a) (Sum.inl b)) (hccr i j)
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.transpose_apply,
    Matrix.add_apply] at h
  simp only [Matrix.mul_apply, fullCCRCompressionBlock, fullCCRLeakageBlock,
    Matrix.transpose_apply, Matrix.add_apply, Matrix.sub_apply]
  unfold IsInvariantFullCompression at hinv
  have hzero : (∑ x : m, T j (Sum.inr x) (Sum.inl a) *
      T i (Sum.inr x) (Sum.inl b)) = 0 := by simp [hinv]
  rw [hzero, add_zero] at h
  by_cases hij : i = j
  · subst j
    simp only [if_pos, Matrix.one_apply] at h ⊢
    by_cases hab : a = b
    · subst b
      simp at h ⊢
      linarith
    · simp [hab] at h ⊢
      linarith
  · simp [hij] at h ⊢
    linarith

/-- Full finite CCR tuples obey the literal pairwise dimension--fluctuation identity on every
invariant coordinate summand. -/
theorem fullCCR_dimension_fluctuation_pairwise_identity
    (T : I → Matrix (n ⊕ m) (n ⊕ m) ℝ)
    (hinv : IsInvariantFullCompression T) (hcomm : IsCommutingFullTuple T)
    (hccr : IsFullCCRMatrixTuple T) :
    (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) + 1) *
        ((Fintype.card I : ℝ) * ccrMeanEnergy (fullCCRCompressionBlock T) -
          ccrNumberVariance (fullCCRCompressionBlock T) (fullCCRLeakageBlock T)) =
      (Fintype.card I : ℝ) ^ 2 *
          ccrPairwiseMixedCommutatorEnergy (fullCCRCompressionBlock T) +
        ccrScaledTracelessLeakageEnergy
          (fullCCRCompressionBlock T) (fullCCRLeakageBlock T) := by
  exact ccr_dimension_fluctuation_pairwise_identity
    (fullCCRCompressionBlock T) (fullCCRLeakageBlock T)
    (fullCCRCompressionBlock_commutes T hinv hcomm)
    (fullCCRLeakageBlock_isCCRCompletion T hinv hccr)

/-- The full-block variance is at most the number of modes times its compressed mean energy. -/
theorem fullCCR_numberVariance_le_card_mul_mean
    (T : I → Matrix (n ⊕ m) (n ⊕ m) ℝ)
    (hinv : IsInvariantFullCompression T) (hcomm : IsCommutingFullTuple T)
    (hccr : IsFullCCRMatrixTuple T) :
    ccrNumberVariance (fullCCRCompressionBlock T) (fullCCRLeakageBlock T) ≤
      (Fintype.card I : ℝ) * ccrMeanEnergy (fullCCRCompressionBlock T) := by
  exact ccr_numberVariance_le_card_mul_mean
    (fullCCRCompressionBlock T) (fullCCRLeakageBlock T)
    (fullCCRCompressionBlock_commutes T hinv hcomm)
    (fullCCRLeakageBlock_isCCRCompletion T hinv hccr)

/-- Equality for a full tuple is literal mixed normality plus pure-trace leakage. -/
theorem fullCCR_numberVariance_eq_card_mul_mean_literal_iff
    (T : I → Matrix (n ⊕ m) (n ⊕ m) ℝ)
    (hinv : IsInvariantFullCompression T) (hcomm : IsCommutingFullTuple T)
    (hccr : IsFullCCRMatrixTuple T) :
    ccrNumberVariance (fullCCRCompressionBlock T) (fullCCRLeakageBlock T) =
        (Fintype.card I : ℝ) * ccrMeanEnergy (fullCCRCompressionBlock T) ↔
      (∀ i j, ccrMixedCommutator (fullCCRCompressionBlock T) i j = 0) ∧
        ∀ i j, ccrScaledTracelessLeakage
          (fullCCRCompressionBlock T) (fullCCRLeakageBlock T) i j = 0 := by
  exact ccr_numberVariance_eq_card_mul_mean_literal_iff
    (fullCCRCompressionBlock T) (fullCCRLeakageBlock T)
    (fullCCRCompressionBlock_commutes T hinv hcomm)
    (fullCCRLeakageBlock_isCCRCompletion T hinv hccr)

/-- Strict full-block variance is equivalent to a literal mixed-normality or pure-trace leakage
defect. -/
theorem fullCCR_numberVariance_lt_card_mul_mean_literal_iff
    (T : I → Matrix (n ⊕ m) (n ⊕ m) ℝ)
    (hinv : IsInvariantFullCompression T) (hcomm : IsCommutingFullTuple T)
    (hccr : IsFullCCRMatrixTuple T) :
    ccrNumberVariance (fullCCRCompressionBlock T) (fullCCRLeakageBlock T) <
        (Fintype.card I : ℝ) * ccrMeanEnergy (fullCCRCompressionBlock T) ↔
      (∃ i j, ccrMixedCommutator (fullCCRCompressionBlock T) i j ≠ 0) ∨
        ∃ i j, ccrScaledTracelessLeakage
          (fullCCRCompressionBlock T) (fullCCRLeakageBlock T) i j ≠ 0 := by
  exact ccr_numberVariance_lt_card_mul_mean_literal_iff
    (fullCCRCompressionBlock T) (fullCCRLeakageBlock T)
    (fullCCRCompressionBlock_commutes T hinv hcomm)
    (fullCCRLeakageBlock_isCCRCompletion T hinv hccr)

/-- Reparametrize a smooth log-volume by the reciprocal dimension power `t = u^(1/d)`. -/
def dimensionPowerReparametrization (d : ℝ) (F : ℝ → ℝ) (u : ℝ) : ℝ :=
  F (u ^ (1 / d : ℝ))

/-- First derivative forced by the reciprocal-dimension power change of variables. -/
def dimensionPowerFirstDerivative (d : ℝ) (F₁ : ℝ → ℝ) (u : ℝ) : ℝ :=
  (1 / d) * u ^ (1 / d - 1 : ℝ) * F₁ (u ^ (1 / d : ℝ))

/-- Second derivative forced by the reciprocal-dimension power change of variables. -/
def dimensionPowerSecondDerivative
    (d : ℝ) (F₁ F₂ : ℝ → ℝ) (u : ℝ) : ℝ :=
  (1 / d) * (1 / d - 1) * u ^ (1 / d - 2 : ℝ) *
      F₁ (u ^ (1 / d : ℝ)) +
    (1 / d) ^ 2 * (u ^ (1 / d - 1 : ℝ)) ^ 2 *
      F₂ (u ^ (1 / d : ℝ))

/-- Chain rule for the reciprocal-dimension power reparametrization. -/
theorem hasDerivAt_dimensionPowerReparametrization
    {d u : ℝ} {F F₁ : ℝ → ℝ} (hu : 0 < u)
    (hF : HasDerivAt F (F₁ (u ^ (1 / d : ℝ))) (u ^ (1 / d : ℝ))) :
    HasDerivAt (dimensionPowerReparametrization d F)
      (dimensionPowerFirstDerivative d F₁ u) u := by
  have hpow := Real.hasDerivAt_rpow_const
    (p := (1 / d : ℝ)) (Or.inl hu.ne')
  have hcomp := hF.comp u hpow
  convert hcomp using 1
  simp only [dimensionPowerFirstDerivative]
  ring

/-- Second chain rule for the reciprocal-dimension power reparametrization. -/
theorem hasDerivAt_dimensionPowerFirstDerivative
    {d u : ℝ} {F₁ F₂ : ℝ → ℝ} (hu : 0 < u)
    (hF₁ : HasDerivAt F₁ (F₂ (u ^ (1 / d : ℝ))) (u ^ (1 / d : ℝ))) :
    HasDerivAt (dimensionPowerFirstDerivative d F₁)
      (dimensionPowerSecondDerivative d F₁ F₂ u) u := by
  have hpow := Real.hasDerivAt_rpow_const
    (p := (1 / d : ℝ)) (Or.inl hu.ne')
  have hpow' := Real.hasDerivAt_rpow_const
    (p := (1 / d - 1 : ℝ)) (Or.inl hu.ne')
  have hcomp := hF₁.comp u hpow
  have hmul := hpow'.mul hcomp
  have hscaled := hmul.const_mul (1 / d)
  convert hscaled using 1
  · funext y
    simp only [dimensionPowerFirstDerivative, Pi.mul_apply, Function.comp_apply]
    ring
  · simp only [dimensionPowerSecondDerivative, Function.comp_apply]
    ring

/-- Mean of a log-volume under logarithmic scale differentiation. -/
def logarithmicScaleMean (F₁ : ℝ → ℝ) (t : ℝ) : ℝ := t * F₁ t

/-- Variance/curvature of a log-volume under two logarithmic scale derivatives. -/
def logarithmicScaleVariance (F₁ F₂ : ℝ → ℝ) (t : ℝ) : ℝ :=
  t * F₁ t + t ^ 2 * F₂ t

/-- The log-volume viewed in logarithmic bandwidth. -/
def logarithmicReparametrization (F : ℝ → ℝ) (s : ℝ) : ℝ := F (Real.exp s)

/-- First derivative in logarithmic bandwidth. -/
def logarithmicFirstDerivative (F₁ : ℝ → ℝ) (s : ℝ) : ℝ :=
  Real.exp s * F₁ (Real.exp s)

/-- Second derivative in logarithmic bandwidth. -/
def logarithmicSecondDerivative (F₁ F₂ : ℝ → ℝ) (s : ℝ) : ℝ :=
  Real.exp s * F₁ (Real.exp s) + (Real.exp s) ^ 2 * F₂ (Real.exp s)

/-- Chain rule for logarithmic bandwidth. -/
theorem hasDerivAt_logarithmicReparametrization
    {s : ℝ} {F F₁ : ℝ → ℝ}
    (hF : HasDerivAt F (F₁ (Real.exp s)) (Real.exp s)) :
    HasDerivAt (logarithmicReparametrization F)
      (logarithmicFirstDerivative F₁ s) s := by
  have hcomp := hF.comp s (Real.hasDerivAt_exp s)
  convert hcomp using 1
  simp only [logarithmicFirstDerivative]
  ring

/-- Second chain rule for logarithmic bandwidth. -/
theorem hasDerivAt_logarithmicFirstDerivative
    {s : ℝ} {F₁ F₂ : ℝ → ℝ}
    (hF₁ : HasDerivAt F₁ (F₂ (Real.exp s)) (Real.exp s)) :
    HasDerivAt (logarithmicFirstDerivative F₁)
      (logarithmicSecondDerivative F₁ F₂ s) s := by
  have hcomp := hF₁.comp s (Real.hasDerivAt_exp s)
  have hmul := (Real.hasDerivAt_exp s).mul hcomp
  convert hmul using 1
  simp only [logarithmicSecondDerivative, Function.comp_apply]
  ring

theorem logarithmicSecondDerivative_eq_scaleVariance
    (F₁ F₂ : ℝ → ℝ) (s : ℝ) :
    logarithmicSecondDerivative F₁ F₂ s =
      logarithmicScaleVariance F₁ F₂ (Real.exp s) := rfl

/-- Nonnegative logarithmic-scale variance gives convexity in log bandwidth. -/
theorem logarithmicReparametrization_convexOn
    {F F₁ F₂ : ℝ → ℝ}
    (hF : ∀ t, 0 < t → HasDerivAt F (F₁ t) t)
    (hF₁ : ∀ t, 0 < t → HasDerivAt F₁ (F₂ t) t)
    (hvariance : ∀ t, 0 < t → 0 ≤ logarithmicScaleVariance F₁ F₂ t) :
    ConvexOn ℝ Set.univ (logarithmicReparametrization F) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
  · intro s _
    exact (hasDerivAt_logarithmicReparametrization
      (hF _ (Real.exp_pos s))).continuousAt.continuousWithinAt
  · intro s _
    exact (hasDerivAt_logarithmicReparametrization
      (hF _ (Real.exp_pos s))).hasDerivWithinAt
  · intro s _
    exact (hasDerivAt_logarithmicFirstDerivative
      (hF₁ _ (Real.exp_pos s))).hasDerivWithinAt
  · intro s _
    rw [logarithmicSecondDerivative_eq_scaleVariance]
    exact hvariance _ (Real.exp_pos s)

/-- Exact conversion of power-scale curvature into the fluctuation deficit
`variance - d * mean`. -/
theorem dimensionPowerSecondDerivative_eq_fluctuation_quotient
    {d u : ℝ} (hd : d ≠ 0) (hu : 0 < u) (F₁ F₂ : ℝ → ℝ) :
    dimensionPowerSecondDerivative d F₁ F₂ u =
      (logarithmicScaleVariance F₁ F₂ (u ^ (1 / d : ℝ)) -
          d * logarithmicScaleMean F₁ (u ^ (1 / d : ℝ))) /
        (d ^ 2 * u ^ 2) := by
  have hu0 : u ≠ 0 := hu.ne'
  have hsub1 := Real.rpow_sub hu (1 / d) 1
  have hsub2 := Real.rpow_sub hu (1 / d) 2
  rw [show u ^ (2 : ℝ) = u ^ 2 by norm_num [Real.rpow_two]] at hsub2
  rw [show u ^ (1 : ℝ) = u by simp] at hsub1
  unfold dimensionPowerSecondDerivative logarithmicScaleVariance logarithmicScaleMean
  rw [hsub2, hsub1]
  field_simp [hd, hu0]
  ring

/-- A fluctuation bound `variance ≤ d * mean` is exactly concavity after the `d`-power
reparametrization. -/
theorem dimensionPowerReparametrization_concaveOn
    {d : ℝ} (hd : 0 < d) {F F₁ F₂ : ℝ → ℝ}
    (hF : ∀ t, 0 < t → HasDerivAt F (F₁ t) t)
    (hF₁ : ∀ t, 0 < t → HasDerivAt F₁ (F₂ t) t)
    (hfluct : ∀ t, 0 < t →
      logarithmicScaleVariance F₁ F₂ t ≤ d * logarithmicScaleMean F₁ t) :
    ConcaveOn ℝ (Set.Ioi 0) (dimensionPowerReparametrization d F) := by
  have hd0 : d ≠ 0 := hd.ne'
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioi 0)
  · intro u hu
    have hut : 0 < u ^ (1 / d : ℝ) := Real.rpow_pos_of_pos hu (1 / d)
    exact (hasDerivAt_dimensionPowerReparametrization hu
      (hF _ hut)).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Ioi] at hu ⊢
    have hut : 0 < u ^ (1 / d : ℝ) := Real.rpow_pos_of_pos hu (1 / d)
    exact (hasDerivAt_dimensionPowerReparametrization hu (hF _ hut)).hasDerivWithinAt
  · intro u hu
    rw [interior_Ioi] at hu ⊢
    have hut : 0 < u ^ (1 / d : ℝ) := Real.rpow_pos_of_pos hu (1 / d)
    exact (hasDerivAt_dimensionPowerFirstDerivative hu (hF₁ _ hut)).hasDerivWithinAt
  · intro u hu
    rw [interior_Ioi] at hu
    rw [dimensionPowerSecondDerivative_eq_fluctuation_quotient hd0 hu]
    exact div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (hfluct _ (Real.rpow_pos_of_pos hu (1 / d))))
      (mul_nonneg (sq_nonneg d) (sq_nonneg u))

omit [DecidableEq m] in
/-- **Exact CCR power-curvature law.**  Dimension-normalized power-scale curvature is the
negative sum of the literal mixed-commutator and trace-free leakage energies. -/
theorem ccr_dimensionPowerSecondDerivative_sumOfSquares
    (A : I → Matrix n n ℝ) (B : I → Matrix n m ℝ)
    (hcomm : IsCommutingCCRCompression A) (hccr : IsCCRCompletion A B)
    (hI : 0 < Fintype.card I) {u : ℝ} (hu : 0 < u)
    (F₁ F₂ : ℝ → ℝ)
    (hmean : logarithmicScaleMean F₁ (u ^ (1 / (Fintype.card I : ℝ) : ℝ)) =
      ccrMeanEnergy A)
    (hvariance : logarithmicScaleVariance F₁ F₂
        (u ^ (1 / (Fintype.card I : ℝ) : ℝ)) = ccrNumberVariance A B) :
    (Fintype.card I : ℝ) ^ 3 * ((Fintype.card I : ℝ) + 1) * u ^ 2 *
        dimensionPowerSecondDerivative (Fintype.card I : ℝ) F₁ F₂ u =
      -((Fintype.card I : ℝ) ^ 2 * ccrPairwiseMixedCommutatorEnergy A +
        ccrScaledTracelessLeakageEnergy A B) := by
  have hd : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hI)
  rw [dimensionPowerSecondDerivative_eq_fluctuation_quotient hd hu,
    hvariance, hmean]
  have hid := ccr_dimension_fluctuation_pairwise_identity A B hcomm hccr
  field_simp
  nlinarith

omit [DecidableEq m] in
/-- A smooth family of finite CCR compressions has concave log-volume in the mode-cardinality
power scale. -/
theorem ccr_dimensionPowerReparametrization_concaveOn
    (A : ℝ → I → Matrix n n ℝ) (B : ℝ → I → Matrix n m ℝ)
    (hcomm : ∀ t, 0 < t → IsCommutingCCRCompression (A t))
    (hccr : ∀ t, 0 < t → IsCCRCompletion (A t) (B t))
    (hI : 0 < Fintype.card I) {F F₁ F₂ : ℝ → ℝ}
    (hF : ∀ t, 0 < t → HasDerivAt F (F₁ t) t)
    (hF₁ : ∀ t, 0 < t → HasDerivAt F₁ (F₂ t) t)
    (hmean : ∀ t, 0 < t → logarithmicScaleMean F₁ t = ccrMeanEnergy (A t))
    (hvariance : ∀ t, 0 < t →
      logarithmicScaleVariance F₁ F₂ t = ccrNumberVariance (A t) (B t)) :
    ConcaveOn ℝ (Set.Ioi 0)
      (dimensionPowerReparametrization (Fintype.card I : ℝ) F) := by
  apply dimensionPowerReparametrization_concaveOn (by exact_mod_cast hI) hF hF₁
  intro t ht
  rw [hvariance t ht, hmean t ht]
  exact ccr_numberVariance_le_card_mul_mean (A t) (B t)
    (hcomm t ht) (hccr t ht)

omit [DecidableEq I] [DecidableEq n] [DecidableEq m] in
/-- The same CCR family is convex in logarithmic scale because its scale curvature is a squared
Hilbert--Schmidt leakage energy. -/
theorem ccr_logarithmicReparametrization_convexOn
    (A : ℝ → I → Matrix n n ℝ) (B : ℝ → I → Matrix n m ℝ)
    {F F₁ F₂ : ℝ → ℝ}
    (hF : ∀ t, 0 < t → HasDerivAt F (F₁ t) t)
    (hF₁ : ∀ t, 0 < t → HasDerivAt F₁ (F₂ t) t)
    (hvariance : ∀ t, 0 < t →
      logarithmicScaleVariance F₁ F₂ t = ccrNumberVariance (A t) (B t)) :
    ConvexOn ℝ Set.univ (logarithmicReparametrization F) := by
  apply logarithmicReparametrization_convexOn hF hF₁
  intro t ht
  rw [hvariance t ht]
  exact rectangularMatrixHilbertSchmidtEnergy_nonneg _

omit [DecidableEq m] in
/-- **CCR scale-sandwich law.**  A smooth `d`-mode CCR log-volume is simultaneously convex in
logarithmic bandwidth and concave in the `d`-power bandwidth coordinate. -/
theorem ccr_logarithmicConvex_dimensionPowerConcave
    (A : ℝ → I → Matrix n n ℝ) (B : ℝ → I → Matrix n m ℝ)
    (hcomm : ∀ t, 0 < t → IsCommutingCCRCompression (A t))
    (hccr : ∀ t, 0 < t → IsCCRCompletion (A t) (B t))
    (hI : 0 < Fintype.card I) {F F₁ F₂ : ℝ → ℝ}
    (hF : ∀ t, 0 < t → HasDerivAt F (F₁ t) t)
    (hF₁ : ∀ t, 0 < t → HasDerivAt F₁ (F₂ t) t)
    (hmean : ∀ t, 0 < t → logarithmicScaleMean F₁ t = ccrMeanEnergy (A t))
    (hvariance : ∀ t, 0 < t →
      logarithmicScaleVariance F₁ F₂ t = ccrNumberVariance (A t) (B t)) :
    ConvexOn ℝ Set.univ (logarithmicReparametrization F) ∧
      ConcaveOn ℝ (Set.Ioi 0)
        (dimensionPowerReparametrization (Fintype.card I : ℝ) F) := by
  constructor
  · exact ccr_logarithmicReparametrization_convexOn A B hF hF₁ hvariance
  · exact ccr_dimensionPowerReparametrization_concaveOn
      A B hcomm hccr hI hF hF₁ hmean hvariance

/-- Full commuting CCR tuples preserving a finite summand satisfy the scale-sandwich law through
their literal compression and leakage blocks. -/
theorem fullCCR_logarithmicConvex_dimensionPowerConcave
    (T : ℝ → I → Matrix (n ⊕ m) (n ⊕ m) ℝ)
    (hinv : ∀ t, 0 < t → IsInvariantFullCompression (T t))
    (hcomm : ∀ t, 0 < t → IsCommutingFullTuple (T t))
    (hccr : ∀ t, 0 < t → IsFullCCRMatrixTuple (T t))
    (hI : 0 < Fintype.card I) {F F₁ F₂ : ℝ → ℝ}
    (hF : ∀ t, 0 < t → HasDerivAt F (F₁ t) t)
    (hF₁ : ∀ t, 0 < t → HasDerivAt F₁ (F₂ t) t)
    (hmean : ∀ t, 0 < t → logarithmicScaleMean F₁ t =
      ccrMeanEnergy (fullCCRCompressionBlock (T t)))
    (hvariance : ∀ t, 0 < t → logarithmicScaleVariance F₁ F₂ t =
      ccrNumberVariance (fullCCRCompressionBlock (T t)) (fullCCRLeakageBlock (T t))) :
    ConvexOn ℝ Set.univ (logarithmicReparametrization F) ∧
      ConcaveOn ℝ (Set.Ioi 0)
        (dimensionPowerReparametrization (Fintype.card I : ℝ) F) := by
  exact ccr_logarithmicConvex_dimensionPowerConcave
    (fun t => fullCCRCompressionBlock (T t))
    (fun t => fullCCRLeakageBlock (T t))
    (fun t ht => fullCCRCompressionBlock_commutes (T t) (hinv t ht) (hcomm t ht))
    (fun t ht => fullCCRLeakageBlock_isCCRCompletion (T t) (hinv t ht) (hccr t ht))
    hI hF hF₁ hmean hvariance

end

end GaloisForLFunctions.HilbertMetric
