import GaloisForLFunctions.RHTower.SoninPrimeGramCompression
import GaloisForLFunctions.RHTower.UniversalPhaseCoherenceTargetMeasure
import Mathlib.Topology.Order.IntermediateValue

/-!
# Projective weighted phase coherence

This file develops the source-independent finite geometry behind weighted
phase recurrence.  It records the exact weighted pairwise variance, the
positive-weight pivot forced by near coherence, and the water-level mass
identity used by the projective rate--distortion law.

The arithmetic frequency vector does not enter: these are universal finite
theorems for arbitrary positive phasor weights.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace RHTower

/-- A finite weighted complex phase amplitude. -/
def projectiveWeightedPhaseAmplitude {d : ℕ}
    (w : Fin d → ℝ) (phase : Fin d → ℂ) : ℂ :=
  ∑ i, (w i : ℂ) * phase i

/-- Ordered weighted pairwise squared phase distance. -/
def projectiveWeightedPairwiseEnergy {d : ℕ}
    (w : Fin d → ℝ) (phase : Fin d → ℂ) : ℝ :=
  ∑ i, ∑ j, w i * w j * ‖phase i - phase j‖ ^ 2

/-- Weighted squared distance from a selected projective pivot. -/
def projectiveWeightedPivotEnergy {d : ℕ}
    (w : Fin d → ℝ) (phase : Fin d → ℂ) (k : Fin d) : ℝ :=
  ∑ j, w j * ‖phase j - phase k‖ ^ 2

theorem projectiveWeightedPhaseAmplitude_eq_finiteWeightedMean
    {d : ℕ} (w : Fin d → ℝ) (phase : Fin d → ℂ) :
    projectiveWeightedPhaseAmplitude w phase = finiteWeightedMean w phase := by
  rfl

theorem projectiveWeightedPairwiseEnergy_eq_finiteWeightedDifferenceEnergy
    {d : ℕ} (w : Fin d → ℝ) (phase : Fin d → ℂ) :
    projectiveWeightedPairwiseEnergy w phase =
      finiteWeightedDifferenceEnergy w phase := by
  rfl

/-- **Weighted projective variance identity.**  For a probability vector and
unit phases, pairwise energy is exactly twice the fidelity deficit. -/
theorem projectiveWeightedPairwiseEnergy_eq_two_mul_fidelityDeficit
    {d : ℕ} (w : Fin d → ℝ) (phase : Fin d → ℂ)
    (hmass : ∑ i, w i = 1) (hphase : ∀ i, ‖phase i‖ = 1) :
    projectiveWeightedPairwiseEnergy w phase =
      2 * (1 - ‖projectiveWeightedPhaseAmplitude w phase‖ ^ 2) := by
  rw [projectiveWeightedPairwiseEnergy_eq_finiteWeightedDifferenceEnergy,
    finiteWeightedDifferenceEnergy_eq_variance]
  have hnorm : finiteWeightedNormSq w phase = 1 := by
    rw [finiteWeightedNormSq]
    simp_rw [hphase, one_pow, mul_one]
    exact hmass
  rw [finiteWeightMass, hmass, hnorm,
    ← projectiveWeightedPhaseAmplitude_eq_finiteWeightedMean]
  ring

/-- **Exact real projective covariance.**  The quadratic form obtained from
real phase coordinates is the weighted second moment minus the square of the
weighted mean.  In particular, it contains the projective covariance term
that a diagonal coordinate envelope must dominate rather than identify with
the intrinsic quotient metric. -/
theorem half_projectiveWeightedPairwiseEnergy_ofReal_eq_covariance
    {d : ℕ} (w theta : Fin d → ℝ) (hmass : ∑ i, w i = 1) :
    (1 / 2 : ℝ) *
        projectiveWeightedPairwiseEnergy w (fun i => (theta i : ℂ)) =
      (∑ i, w i * theta i ^ 2) - (∑ i, w i * theta i) ^ 2 := by
  rw [projectiveWeightedPairwiseEnergy_eq_finiteWeightedDifferenceEnergy,
    finiteWeightedDifferenceEnergy_eq_variance]
  simp only [finiteWeightMass, hmass, finiteWeightedNormSq,
    Complex.norm_real, Real.norm_eq_abs, sq_abs,
    finiteWeightedMean, Complex.ofReal_mul, Complex.ofReal_sum]
  ring

/-- The weighted average of the pivot energies is the pairwise energy. -/
theorem sum_weight_mul_projectiveWeightedPivotEnergy
    {d : ℕ} (w : Fin d → ℝ) (phase : Fin d → ℂ) :
    ∑ k, w k * projectiveWeightedPivotEnergy w phase k =
      projectiveWeightedPairwiseEnergy w phase := by
  unfold projectiveWeightedPivotEnergy projectiveWeightedPairwiseEnergy
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [norm_sub_rev]
  ring

/-- A nonnegative finite probability vector has a positive coordinate. -/
theorem exists_pos_weight_of_sum_eq_one
    {d : ℕ} (w : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hmass : ∑ i, w i = 1) :
    ∃ i, 0 < w i := by
  have hsum : 0 < ∑ i, w i := by rw [hmass]; norm_num
  rw [Finset.sum_pos_iff_of_nonneg (fun i _hi ↦ hw i)] at hsum
  rcases hsum with ⟨i, _hi, hwi⟩
  exact ⟨i, hwi⟩

/-- **Weighted projective pivot.**  Near-perfect weighted coherence forces a
positive-weight phase whose weighted squared distance from the whole packet
is at most `4 * η`. -/
theorem exists_positiveWeight_projectiveWeightedPivotEnergy_le
    {d : ℕ} (w : Fin d → ℝ) (phase : Fin d → ℂ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (hphase : ∀ i, ‖phase i‖ = 1)
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hcoh : 1 - η ≤ ‖projectiveWeightedPhaseAmplitude w phase‖) :
    ∃ k, 0 < w k ∧ projectiveWeightedPivotEnergy w phase k ≤ 4 * η := by
  have hsq : (1 - η) ^ 2 ≤
      ‖projectiveWeightedPhaseAmplitude w phase‖ ^ 2 := by
    exact (sq_le_sq₀ (sub_nonneg.mpr hη1) (norm_nonneg _)).2 hcoh
  have hpair : projectiveWeightedPairwiseEnergy w phase ≤ 4 * η := by
    rw [projectiveWeightedPairwiseEnergy_eq_two_mul_fidelityDeficit
      w phase hmass hphase]
    nlinarith [sq_nonneg η]
  obtain ⟨k0, hk0⟩ := exists_pos_weight_of_sum_eq_one w hw hmass
  by_contra h
  push Not at h
  have hterm : ∀ k, w k * (4 * η) ≤
      w k * projectiveWeightedPivotEnergy w phase k := by
    intro k
    by_cases hk : w k = 0
    · simp [hk]
    · exact mul_le_mul_of_nonneg_left (h k (lt_of_le_of_ne (hw k) (Ne.symm hk))).le
        (hw k)
  have hstrict : ∃ k ∈ (Finset.univ : Finset (Fin d)),
      w k * (4 * η) < w k * projectiveWeightedPivotEnergy w phase k := by
    refine ⟨k0, Finset.mem_univ _, ?_⟩
    exact mul_lt_mul_of_pos_left (h k0 hk0) hk0
  have hsumlt := Finset.sum_lt_sum
    (fun k _hk ↦ hterm k) hstrict
  have hleft : ∑ k, w k * (4 * η) = 4 * η := by
    rw [← Finset.sum_mul, hmass, one_mul]
  rw [hleft, sum_weight_mul_projectiveWeightedPivotEnergy] at hsumlt
  exact (not_lt_of_ge hpair) hsumlt

/-- The hard water-level mass of all nonpivot coordinates. -/
def projectiveWaterMass {d : ℕ}
    (w : Fin d → ℝ) (k : Fin d) (lam : ℝ) : ℝ :=
  ∑ j, if j = k then 0 else min (w j) (lam⁻¹)

/-- Projective hard water-filling entropy at a proposed water level. -/
def projectiveWaterEntropyAt {d : ℕ}
    (w : Fin d → ℝ) (k : Fin d) (lam : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ j, if j = k then 0 else
    Real.log (max 1 (lam * w j))

theorem projectiveWaterMass_one
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    projectiveWaterMass w k 1 = 1 - w k := by
  have hwi : ∀ i, w i ≤ 1 := by
    intro i
    have hsingle : w i ≤ ∑ j, w j :=
      Finset.single_le_sum (fun j _hj ↦ hw j) (Finset.mem_univ i)
    simpa only [hmass] using hsingle
  rw [projectiveWaterMass]
  simp only [inv_one]
  calc
    (∑ j, if j = k then 0 else min (w j) 1) =
        ∑ j, if j = k then 0 else w j := by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hj : j = k
      · simp [hj]
      · simp [hj, min_eq_left (hwi j)]
    _ = 1 - w k := by
      calc
        (∑ j, if j = k then 0 else w j) =
            ∑ j, (w j - if j = k then w j else 0) := by
          apply Finset.sum_congr rfl
          intro j _hj
          by_cases hj : j = k <;> simp [hj]
        _ = (∑ j, w j) - ∑ j, (if j = k then w j else 0) :=
          by rw [Finset.sum_sub_distrib]
        _ = 1 - w k := by simp [hmass]

theorem continuousOn_projectiveWaterMass
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) {a b : ℝ}
    (ha : 0 < a) :
    ContinuousOn (projectiveWaterMass w k) (Set.Icc a b) := by
  unfold projectiveWaterMass
  apply continuousOn_finset_sum
  intro j _hj
  by_cases hj : j = k
  · subst j
    simpa using
      ((continuous_const : Continuous (fun _x : ℝ ↦ (0 : ℝ))).continuousOn)
  · simp only [hj, ↓reduceIte]
    exact continuousOn_const.inf <|
      continuousOn_id.inv₀ fun x hx ↦ ne_of_gt (ha.trans_le hx.1)

/-- At level `d / η`, every nonpivot water contribution is at most
`η / d`, so the total mass is at most `η`. -/
theorem projectiveWaterMass_card_div_le
    {d : ℕ} (hd : 0 < d) (w : Fin d → ℝ) (k : Fin d)
    (hw : ∀ i, 0 ≤ w i) {η : ℝ} (hη : 0 < η) :
    projectiveWaterMass w k ((d : ℝ) / η) ≤ η := by
  have hlam : 0 < (d : ℝ) / η := by positivity
  rw [projectiveWaterMass]
  calc
    (∑ j, if j = k then 0 else min (w j) (((d : ℝ) / η)⁻¹)) ≤
        ∑ _j : Fin d, η / (d : ℝ) := by
      apply Finset.sum_le_sum
      intro j _hj
      by_cases hj : j = k
      · simp [hj]
        positivity
      · simp only [hj, ↓reduceIte]
        calc
          min (w j) (((d : ℝ) / η)⁻¹) ≤ (((d : ℝ) / η)⁻¹) := min_le_right _ _
          _ = η / (d : ℝ) := by field_simp
    _ = η := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp

/-- **Existence of the projective water level.**  If the requested distortion
lies below the total nonpivot mass, a finite positive water level realizes it
exactly. -/
theorem exists_projectiveWaterLevel
    {d : ℕ} (hd : 0 < d) (w : Fin d → ℝ) (k : Fin d)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    {η : ℝ} (hη : 0 < η) (hηtail : η < 1 - w k) :
    ∃ lam : ℝ, 1 ≤ lam ∧ lam ≤ (d : ℝ) / η ∧
      projectiveWaterMass w k lam = η := by
  have htop : 1 ≤ (d : ℝ) / η := by
    have hη1 : η < 1 := hηtail.trans_le (sub_le_self 1 (hw k))
    have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
    exact le_div_iff₀ hη |>.2 <| by nlinarith
  have hcont := continuousOn_projectiveWaterMass w k
    (a := (1 : ℝ)) (b := (d : ℝ) / η) (by norm_num)
  have hlow : η ≤ projectiveWaterMass w k 1 := by
    rw [projectiveWaterMass_one w k hw hmass]
    exact hηtail.le
  have hhigh : projectiveWaterMass w k ((d : ℝ) / η) ≤ η :=
    projectiveWaterMass_card_div_le hd w k hw hη
  have himage := intermediate_value_Icc' htop hcont ⟨hhigh, hlow⟩
  rcases himage with ⟨lam, hlam, hvalue⟩
  exact ⟨lam, hlam.1, hlam.2, hvalue⟩

/-- The water-level equation gives the universal active-coordinate budget. -/
theorem waterLevel_mul_eta_le_card_sub_one
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) {lam η : ℝ}
    (hlam : 0 < lam)
    (hlevel : projectiveWaterMass w k lam = η) :
    lam * η ≤ (d - 1 : ℕ) := by
  have hterm : ∀ j, lam *
      (if j = k then 0 else min (w j) lam⁻¹) ≤
        if j = k then 0 else 1 := by
    intro j
    by_cases hj : j = k
    · simp [hj]
    · simp only [hj, ↓reduceIte]
      calc
        lam * min (w j) lam⁻¹ ≤ lam * lam⁻¹ := by
          exact mul_le_mul_of_nonneg_left (min_le_right _ _) hlam.le
        _ = 1 := mul_inv_cancel₀ hlam.ne'
  calc
    lam * η = ∑ j, lam *
        (if j = k then 0 else min (w j) lam⁻¹) := by
      rw [← hlevel, projectiveWaterMass, Finset.mul_sum]
    _ ≤ ∑ j, if j = k then 0 else 1 := Finset.sum_le_sum fun j _hj ↦ hterm j
    _ = (d - 1 : ℕ) := by
      have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr fun hd0 ↦ by
        subst d
        exact Fin.elim0 k
      calc
        (∑ j, if j = k then 0 else (1 : ℝ)) =
            ∑ j, ((1 : ℝ) - if j = k then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro j _hj
          by_cases hj : j = k <;> simp [hj]
        _ = (∑ _j : Fin d, (1 : ℝ)) -
            ∑ j, (if j = k then (1 : ℝ) else 0) :=
          by rw [Finset.sum_sub_distrib]
        _ = (d : ℝ) - 1 := by simp
        _ = ((d - 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub hd]
          norm_num

/-! ## Weighted Haar target geometry -/

/-- Weighted pivot energy on the finite phase torus. -/
def torusProjectiveWeightedPivotEnergy {d : ℕ}
    (w : Fin d → ℝ) (k : Fin d) (x : Fin d → UnitAddCircle) : ℝ :=
  ∑ j, w j * ‖fourier 1 (x j) - fourier 1 (x k)‖ ^ 2

/-- Independent-coordinate weighted pivot energy after the projective shear. -/
def torusIndependentProjectiveWeightedPivotEnergy {d : ℕ}
    (w : Fin d → ℝ) (k : Fin d) (y : Fin d → UnitAddCircle) : ℝ :=
  ∑ j, if j = k then 0 else w j * ‖fourier 1 (y j) - 1‖ ^ 2

theorem continuous_torusProjectiveWeightedPivotEnergy
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) :
    Continuous (torusProjectiveWeightedPivotEnergy w k) := by
  unfold torusProjectiveWeightedPivotEnergy
  fun_prop

theorem torusIndependentProjectiveWeightedPivotEnergy_pivotDifferenceEquiv
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d)
    (x : Fin d → UnitAddCircle) :
    torusIndependentProjectiveWeightedPivotEnergy w k
        (pivotDifferenceEquiv k x) =
      torusProjectiveWeightedPivotEnergy w k x := by
  rw [torusIndependentProjectiveWeightedPivotEnergy,
    torusProjectiveWeightedPivotEnergy]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hjk : j = k
  · subst j
    simp
  · simp only [hjk, ↓reduceIte]
    rw [norm_pivot_fourier_sub_one k j hjk x]

/-- Exact weighted product factorization of the independent pivot-energy
Laplace transform. -/
theorem integral_exp_neg_torusIndependentProjectiveWeightedPivotEnergy
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) (lam : ℝ) :
    (∫ y : Fin d → UnitAddCircle,
      Real.exp (-lam *
        torusIndependentProjectiveWeightedPivotEnergy w k y)) =
      ∏ j, if j = k then 1 else
        circleChordExponentialMoment (lam * w j) := by
  have hfactor (y : Fin d → UnitAddCircle) :
      Real.exp (-lam *
          torusIndependentProjectiveWeightedPivotEnergy w k y) =
        ∏ j, if j = k then 1 else
          Real.exp (-(lam * w j) * ‖fourier 1 (y j) - 1‖ ^ 2) := by
    rw [torusIndependentProjectiveWeightedPivotEnergy]
    calc
      Real.exp (-lam * ∑ j, if j = k then 0 else
          w j * ‖fourier 1 (y j) - 1‖ ^ 2) =
          Real.exp (∑ j, -lam * (if j = k then 0 else
            w j * ‖fourier 1 (y j) - 1‖ ^ 2)) := by
              congr 1
              rw [← Finset.mul_sum]
      _ = ∏ j, Real.exp (-lam * (if j = k then 0 else
            w j * ‖fourier 1 (y j) - 1‖ ^ 2)) := Real.exp_sum _ _
      _ = ∏ j, if j = k then 1 else
          Real.exp (-(lam * w j) * ‖fourier 1 (y j) - 1‖ ^ 2) := by
            apply Finset.prod_congr rfl
            intro j _hj
            by_cases hjk : j = k <;> simp [hjk]
            ring_nf
  rw [integral_congr_ae (ae_of_all _ hfactor)]
  change (∫ y : Fin d → UnitAddCircle,
    ∏ j, (fun z : UnitAddCircle ↦ if j = k then 1 else
      Real.exp (-(lam * w j) * ‖fourier 1 z - 1‖ ^ 2)) (y j)) = _
  have hprod := integral_fintype_prod_volume_eq_prod
    (fun j : Fin d ↦ fun z : UnitAddCircle ↦ if j = k then 1 else
      Real.exp (-(lam * w j) * ‖fourier 1 z - 1‖ ^ 2))
  rw [hprod]
  apply Finset.prod_congr rfl
  intro j _hj
  by_cases hjk : j = k
  · subst j
    simp only [if_pos]
    rw [integral_const]
    rw [measureReal_def, UnitAddCircle.measure_univ]
    norm_num
  · simp [hjk, circleChordExponentialMoment]

/-- The unsheared weighted pivot energy has the same product Laplace
transform. -/
theorem integral_exp_neg_torusProjectiveWeightedPivotEnergy
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) (lam : ℝ) :
    (∫ x : Fin d → UnitAddCircle,
      Real.exp (-lam * torusProjectiveWeightedPivotEnergy w k x)) =
      ∏ j, if j = k then 1 else
        circleChordExponentialMoment (lam * w j) := by
  have hmp := measurePreserving_pivotDifferenceEquiv k
  have hmp' : MeasurePreserving (measurablePivotDifferenceEquiv k) := hmp
  have hchange := hmp'.integral_comp'
    (fun y : Fin d → UnitAddCircle ↦
      Real.exp (-lam *
        torusIndependentProjectiveWeightedPivotEnergy w k y))
  change (∫ x : Fin d → UnitAddCircle,
    Real.exp (-lam * torusIndependentProjectiveWeightedPivotEnergy w k
      (pivotDifferenceEquiv k x))) = _ at hchange
  calc
    (∫ x : Fin d → UnitAddCircle,
      Real.exp (-lam * torusProjectiveWeightedPivotEnergy w k x)) =
        ∫ x : Fin d → UnitAddCircle,
          Real.exp (-lam * torusIndependentProjectiveWeightedPivotEnergy w k
            (pivotDifferenceEquiv k x)) := by
              apply integral_congr_ae
              exact ae_of_all _ fun x ↦ congrArg
                (fun u : ℝ ↦ Real.exp (-lam * u))
                (torusIndependentProjectiveWeightedPivotEnergy_pivotDifferenceEquiv
                  w k x).symm
    _ = ∫ y : Fin d → UnitAddCircle,
      Real.exp (-lam *
        torusIndependentProjectiveWeightedPivotEnergy w k y) := hchange
    _ = ∏ j, if j = k then 1 else
        circleChordExponentialMoment (lam * w j) :=
      integral_exp_neg_torusIndependentProjectiveWeightedPivotEnergy w k lam

/-- Weighted pivot-energy sublevel target. -/
def torusProjectiveWeightedPivotTarget {d : ℕ}
    (w : Fin d → ℝ) (k : Fin d) (η : ℝ) :
    Set (Fin d → UnitAddCircle) :=
  {x | torusProjectiveWeightedPivotEnergy w k x ≤ 4 * η}

/-- Chernoff bound for one weighted pivot target. -/
theorem measureReal_torusProjectiveWeightedPivotTarget_le
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d)
    {η lam : ℝ} (hlam : 0 < lam) :
    volume.real (torusProjectiveWeightedPivotTarget w k η) ≤
      Real.exp (4 * lam * η) *
        ∏ j, if j = k then 1 else
          circleChordExponentialMoment (lam * w j) := by
  let f : (Fin d → UnitAddCircle) → ℝ := fun x ↦
    Real.exp (-lam * torusProjectiveWeightedPivotEnergy w k x)
  let eps : ℝ := Real.exp (-lam * (4 * η))
  have hfcont : Continuous f := by
    dsimp only [f]
    exact Real.continuous_exp.comp
      (continuous_const.mul
        (continuous_torusProjectiveWeightedPivotEnergy w k))
  have hfint : Integrable f := by
    rw [← integrableOn_univ]
    exact ContinuousOn.integrableOn_compact isCompact_univ hfcont.continuousOn
  have hfnonneg : ∀ᵐ _x ∂(volume : Measure (Fin d → UnitAddCircle)), 0 ≤ f _x :=
    Filter.Eventually.of_forall fun _x ↦ (Real.exp_pos _).le
  have hsubset : torusProjectiveWeightedPivotTarget w k η ⊆
      {x | eps ≤ f x} := by
    intro x hx
    rw [torusProjectiveWeightedPivotTarget, Set.mem_setOf_eq] at hx
    rw [Set.mem_setOf_eq]
    dsimp only [eps, f]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hfnonneg hfint eps
  have hmono : volume.real (torusProjectiveWeightedPivotTarget w k η) ≤
      volume.real {x | eps ≤ f x} := measureReal_mono hsubset
  have hmul : eps *
      volume.real (torusProjectiveWeightedPivotTarget w k η) ≤ ∫ x, f x :=
    (mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le).trans hmarkov
  have hdiv : volume.real (torusProjectiveWeightedPivotTarget w k η) ≤
      (∫ x, f x) / eps := by
    apply (le_div_iff₀ (Real.exp_pos _)).2
    simpa only [eps, mul_comm, mul_left_comm, mul_assoc] using hmul
  calc
    volume.real (torusProjectiveWeightedPivotTarget w k η) ≤
        (∫ x, f x) / eps := hdiv
    _ = Real.exp (4 * lam * η) *
        ∏ j, if j = k then 1 else
          circleChordExponentialMoment (lam * w j) := by
      rw [show (∫ x, f x) =
          ∏ j, if j = k then 1 else
            circleChordExponentialMoment (lam * w j) by
        simpa only [f] using
          integral_exp_neg_torusProjectiveWeightedPivotEnergy w k lam]
      dsimp only [eps]
      rw [show -lam * (4 * η) = -(4 * lam * η) by ring,
        Real.exp_neg, div_eq_mul_inv, inv_inv]
      ring

/-- Weighted Haar coherence target. -/
def torusProjectiveWeightedCoherenceTarget {d : ℕ}
    (w : Fin d → ℝ) (η : ℝ) : Set (Fin d → UnitAddCircle) :=
  {x | 1 - η ≤ ‖projectiveWeightedPhaseAmplitude w
    (fun j ↦ fourier 1 (x j))‖}

theorem torusProjectiveWeightedCoherenceTarget_subset_iUnion_pivotTarget
    {d : ℕ} (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    torusProjectiveWeightedCoherenceTarget w η ⊆
      ⋃ k, torusProjectiveWeightedPivotTarget w k η := by
  intro x hx
  rw [torusProjectiveWeightedCoherenceTarget, Set.mem_setOf_eq] at hx
  have hphase : ∀ j, ‖fourier 1 (x j)‖ = 1 := by
    intro j
    rw [fourier_apply, Circle.norm_coe]
  obtain ⟨k, _hwk, hk⟩ :=
    exists_positiveWeight_projectiveWeightedPivotEnergy_le
      w (fun j ↦ fourier 1 (x j)) hw hmass hphase hη0 hη1 hx
  rw [Set.mem_iUnion]
  refine ⟨k, ?_⟩
  change (∑ j, w j *
    ‖fourier 1 (x j) - fourier 1 (x k)‖ ^ 2) ≤ 4 * η at hk
  change (∑ j, w j *
    ‖fourier 1 (x j) - fourier 1 (x k)‖ ^ 2) ≤ 4 * η
  exact hk

/-- **Universal weighted target budget.**  Each pivot may use its own
positive Chernoff level. -/
theorem measureReal_torusProjectiveWeightedCoherenceTarget_le
    {d : ℕ} (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (lam : Fin d → ℝ) (hlam : ∀ k, 0 < lam k) :
    volume.real (torusProjectiveWeightedCoherenceTarget w η) ≤
      ∑ k, Real.exp (4 * lam k * η) *
        ∏ j, if j = k then 1 else
          circleChordExponentialMoment (lam k * w j) := by
  calc
    volume.real (torusProjectiveWeightedCoherenceTarget w η) ≤
        volume.real (⋃ k, torusProjectiveWeightedPivotTarget w k η) :=
      measureReal_mono
        (torusProjectiveWeightedCoherenceTarget_subset_iUnion_pivotTarget
          w hw hmass hη0 hη1)
    _ ≤ ∑ k, volume.real (torusProjectiveWeightedPivotTarget w k η) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ k, Real.exp (4 * lam k * η) *
        ∏ j, if j = k then 1 else
          circleChordExponentialMoment (lam k * w j) := by
      apply Finset.sum_le_sum
      intro k _hk
      exact measureReal_torusProjectiveWeightedPivotTarget_le
        w k (hlam k)

end RHTower
