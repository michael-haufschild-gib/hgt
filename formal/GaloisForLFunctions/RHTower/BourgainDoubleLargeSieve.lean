/-
# Bourgain's four-dimensional double large sieve

Exact box localization, integral Cauchy--Schwarz, the local-mass estimate,
and the Gaussian continuous large sieve combine here into an unconditional
double-large-sieve theorem.  Both sides use sharp weighted spacing energies.
The final theorem has the standard scale product

`∏ j, (1 + X j * Y j)`

and an explicit absolute constant.
-/
import GaloisForLFunctions.RHTower.BourgainBilinearLocalization
import GaloisForLFunctions.HTGeometry.HalfLineSteinRobertson

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

theorem measurableSet_bourgainFourCube :
    MeasurableSet bourgainFourCube := by
  unfold bourgainFourCube
  have hset :
      {x : BourgainPhaseSpace | ‖x‖ ≤ 1} =
        Metric.closedBall 0 1 := by
    ext x
    simp [Metric.mem_closedBall, dist_zero_right]
  rw [hset]
  exact measurableSet_closedBall

/-- Integral Cauchy--Schwarz after exact localization. -/
theorem bourgainBilinearForm_sq_le_l2
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {X Y : BourgainPhaseSpace}
    (x : ι → BourgainPhaseSpace) (y : κ → BourgainPhaseSpace)
    (a : ι → ℂ) (b : κ → ℂ)
    (hX : ∀ j, 0 < X j) (hY : ∀ j, 0 < Y j)
    (hx : ∀ q j, |x q j| ≤ X j)
    (hy : ∀ q j, |y q j| ≤ Y j) :
    ‖bourgainBilinearForm x y a b‖ ^ (2 : ℕ) ≤
      (∫ z : BourgainPhaseSpace,
        ‖bourgainLocalCoefficientSum Y
          (bourgainLocalizationScale X Y) x a z‖ ^ (2 : ℕ)) *
      (∫ z in bourgainFourCube,
        ‖bourgainWeightedFourierSum
          (bourgainLocalizationScale X Y) y
          (bourgainLocalizedFourierWeight Y
            (bourgainLocalizationScale X Y) y b) z‖ ^ (2 : ℕ)) := by
  let L := bourgainLocalizationScale X Y
  let F : BourgainPhaseSpace → ℂ :=
    bourgainLocalCoefficientSum Y L x a
  let G : BourgainPhaseSpace → ℂ :=
    bourgainWeightedFourierSum L y
      (bourgainLocalizedFourierWeight Y L y b)
  have hL : ∀ j, 0 < L j :=
    bourgainLocalizationScale_pos hX hY
  have hrecover :
      (∫ z : BourgainPhaseSpace, F z * G z) =
        bourgainBilinearForm x y a b :=
    integral_bourgainBilinearIntegrand x y a b hY hL hy
  have hFzero :
      ∀ z, z ∉ bourgainFourCube → F z = 0 := by
    intro z hz
    unfold F bourgainLocalCoefficientSum
    apply Finset.sum_eq_zero
    intro i hi
    have hnot :
        z ∉ bourgainLocalBox Y L (x i) := by
      intro hmem
      exact hz (bourgainLocalBox_subset_fourCube
        hX hY (hx i) hmem)
    simp [hnot]
  have hset :
      (∫ z in bourgainFourCube, F z * G z) =
        ∫ z : BourgainPhaseSpace, F z * G z := by
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by rw [hFzero z hz, zero_mul])
  have hFnormMeas :
      AEStronglyMeasurable (fun z => ‖F z‖)
        (volume.restrict bourgainFourCube) := by
    exact Measurable.aestronglyMeasurable
      (measurable_bourgainLocalCoefficientSum Y L x a).norm
  have hGcont : Continuous G := by
    unfold G bourgainWeightedFourierSum
      bourgainAdditiveCharacter bourgainCoordinateScale bourgainDot
      bourgainLocalizedFourierWeight
    fun_prop
  have hGnormMeas :
      AEStronglyMeasurable (fun z => ‖G z‖)
        (volume.restrict bourgainFourCube) :=
    hGcont.norm.measurable.aestronglyMeasurable
  have hFsqGlobal :
      Integrable (fun z => ‖F z‖ ^ (2 : ℕ)) :=
    integrable_norm_bourgainLocalCoefficientSum_sq Y L x a
  have hFsq :
      Integrable (fun z => ‖F z‖ ^ (2 : ℕ))
        (volume.restrict bourgainFourCube) :=
    hFsqGlobal.integrableOn
  have hcubeCompact : IsCompact bourgainFourCube := by
    unfold bourgainFourCube
    have hset :
        {x : BourgainPhaseSpace | ‖x‖ ≤ 1} =
          Metric.closedBall 0 1 := by
      ext x
      simp [Metric.mem_closedBall, dist_zero_right]
    rw [hset]
    exact isCompact_closedBall 0 1
  have hGsq :
      Integrable (fun z => ‖G z‖ ^ (2 : ℕ))
        (volume.restrict bourgainFourCube) := by
    exact (hGcont.norm.pow 2).continuousOn.integrableOn_compact
      hcubeCompact
  have hcs :=
    HTGeometry.sq_integral_mul_le_integral_sq_mul_integral_sq
      hFnormMeas hGnormMeas hFsq hGsq
  have hnormIntegral :
      ‖∫ z in bourgainFourCube, F z * G z‖ ≤
        ∫ z in bourgainFourCube, ‖F z‖ * ‖G z‖ := by
    calc
      ‖∫ z in bourgainFourCube, F z * G z‖ ≤
          ∫ z in bourgainFourCube, ‖F z * G z‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ z in bourgainFourCube, ‖F z‖ * ‖G z‖ := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [norm_mul]
  have hnormsq :
      ‖∫ z in bourgainFourCube, F z * G z‖ ^ (2 : ℕ) ≤
        (∫ z in bourgainFourCube, ‖F z‖ * ‖G z‖) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (norm_nonneg _) hnormIntegral 2
  have hFset_le :
      (∫ z in bourgainFourCube, ‖F z‖ ^ (2 : ℕ)) ≤
        ∫ z : BourgainPhaseSpace, ‖F z‖ ^ (2 : ℕ) :=
    setIntegral_le_integral hFsqGlobal
      (Filter.Eventually.of_forall fun z => by positivity)
  have hGset0 :
      0 ≤ ∫ z in bourgainFourCube, ‖G z‖ ^ (2 : ℕ) :=
    integral_nonneg fun z => by positivity
  calc
    ‖bourgainBilinearForm x y a b‖ ^ (2 : ℕ) =
        ‖∫ z in bourgainFourCube, F z * G z‖ ^ (2 : ℕ) := by
      rw [hset, hrecover]
    _ ≤ (∫ z in bourgainFourCube, ‖F z‖ * ‖G z‖) ^ (2 : ℕ) :=
      hnormsq
    _ ≤ (∫ z in bourgainFourCube, ‖F z‖ ^ (2 : ℕ)) *
        (∫ z in bourgainFourCube, ‖G z‖ ^ (2 : ℕ)) := hcs
    _ ≤ (∫ z : BourgainPhaseSpace, ‖F z‖ ^ (2 : ℕ)) *
        (∫ z in bourgainFourCube, ‖G z‖ ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_right hFset_le hGset0
    _ = _ := rfl

def bourgainLocalizationMultiplierBound
    (Y L : BourgainPhaseSpace) : ℝ :=
  ∏ j : Fin 4, (2 * Real.pi * Y j * L j)

theorem bourgainLocalizationMultiplierBound_nonneg
    {Y L : BourgainPhaseSpace}
    (hY : ∀ j, 0 < Y j) (hL : ∀ j, 0 < L j) :
    0 ≤ bourgainLocalizationMultiplierBound Y L := by
  unfold bourgainLocalizationMultiplierBound
  exact Finset.prod_nonneg fun j hj =>
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) Real.pi_pos.le) (hY j).le)
      (hL j).le

theorem bourgainScaledNear_mono
    {X L u v : BourgainPhaseSpace}
    (hX : ∀ j, 0 ≤ X j) (hXL : ∀ j, X j ≤ L j)
    (hnear : BourgainScaledNear L u v) :
    BourgainScaledNear X u v := by
  intro j
  calc
    |X j * (u j - v j)| =
        X j * |u j - v j| := by rw [abs_mul, abs_of_nonneg (hX j)]
    _ ≤ L j * |u j - v j| :=
      mul_le_mul_of_nonneg_right (hXL j) (abs_nonneg _)
    _ = |L j * (u j - v j)| := by
      rw [abs_mul, abs_of_nonneg (le_trans (hX j) (hXL j))]
    _ < 1 / 2 := hnear j

theorem norm_bourgainLocalizedFourierWeight_le
    {κ : Type*} [Fintype κ]
    {Y L : BourgainPhaseSpace} (y : κ → BourgainPhaseSpace)
    (b : κ → ℂ) (hY : ∀ j, 0 < Y j) (hL : ∀ j, 0 < L j)
    (hy : ∀ q j, |y q j| ≤ Y j) (q : κ) :
    ‖bourgainLocalizedFourierWeight Y L y b q‖ ≤
      bourgainLocalizationMultiplierBound Y L * ‖b q‖ := by
  unfold bourgainLocalizedFourierWeight
  rw [norm_mul]
  have hm :=
    norm_bourgainProductLocalizationMultiplier_le hY hL (hy q)
  unfold bourgainLocalizationMultiplierBound
  nlinarith [norm_nonneg (b q)]

theorem bourgainLocalizedWeight_scaledNearEnergy_le
    {κ : Type*} [Fintype κ]
    {X Y L : BourgainPhaseSpace}
    (y : κ → BourgainPhaseSpace) (b : κ → ℂ)
    (hX : ∀ j, 0 ≤ X j) (hY : ∀ j, 0 < Y j)
    (hL : ∀ j, 0 < L j) (hXL : ∀ j, X j ≤ L j)
    (hy : ∀ q j, |y q j| ≤ Y j) :
    bourgainWeightedScaledNearEnergy L y
        (fun q => ‖bourgainLocalizedFourierWeight Y L y b q‖) ≤
      bourgainLocalizationMultiplierBound Y L ^ (2 : ℕ) *
        bourgainWeightedScaledNearEnergy X y (fun q => ‖b q‖) := by
  classical
  let P := bourgainLocalizationMultiplierBound Y L
  have hP : 0 ≤ P :=
    bourgainLocalizationMultiplierBound_nonneg hY hL
  unfold bourgainWeightedScaledNearEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hnearL : BourgainScaledNear L (y i) (y j)
  · have hnearX : BourgainScaledNear X (y i) (y j) :=
      bourgainScaledNear_mono hX hXL hnearL
    simp only [hnearL, hnearX, ↓reduceIte]
    have hiw :=
      norm_bourgainLocalizedFourierWeight_le y b hY hL hy i
    have hjw :=
      norm_bourgainLocalizedFourierWeight_le y b hY hL hy j
    have hni : 0 ≤ ‖b i‖ := norm_nonneg _
    calc
      ‖bourgainLocalizedFourierWeight Y L y b i‖ *
          ‖bourgainLocalizedFourierWeight Y L y b j‖ ≤
        (P * ‖b i‖) * (P * ‖b j‖) :=
          mul_le_mul hiw hjw (norm_nonneg _)
            (mul_nonneg hP hni)
      _ = P ^ (2 : ℕ) * (‖b i‖ * ‖b j‖) := by ring
  · simp only [hnearL, ↓reduceIte]
    by_cases hnearX : BourgainScaledNear X (y i) (y j)
    · simp only [hnearX, ↓reduceIte]
      positivity
    · simp [hnearX]

theorem bourgainWeightedScaledNearEnergy_nonneg
    {ι : Type*} [Fintype ι]
    (X : BourgainPhaseSpace) (p : ι → BourgainPhaseSpace)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    0 ≤ bourgainWeightedScaledNearEnergy X p a := by
  classical
  unfold bourgainWeightedScaledNearEnergy
  exact Finset.sum_nonneg fun i hi =>
    Finset.sum_nonneg fun j hj => by
      split_ifs
      · exact mul_nonneg (ha i) (ha j)
      · exact le_rfl

theorem bourgainDoubleLargeSieve_factored
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {X Y : BourgainPhaseSpace}
    (x : ι → BourgainPhaseSpace) (y : κ → BourgainPhaseSpace)
    (a : ι → ℂ) (b : κ → ℂ)
    (hX : ∀ j, 0 < X j) (hY : ∀ j, 0 < Y j)
    (hx : ∀ q j, |x q j| ≤ X j)
    (hy : ∀ q j, |y q j| ≤ Y j) :
    ‖bourgainBilinearForm x y a b‖ ^ (2 : ℕ) ≤
      ((∏ j : Fin 4,
          (2 * bourgainLocalizationEpsilon (Y j) /
            bourgainLocalizationScale X Y j)) *
        bourgainWeightedScaledNearEnergy Y x (fun q => ‖a q‖)) *
      ((Real.exp (4 * Real.pi) * 331776) *
        (bourgainLocalizationMultiplierBound Y
          (bourgainLocalizationScale X Y) ^ (2 : ℕ) *
          bourgainWeightedScaledNearEnergy X y (fun q => ‖b q‖))) := by
  let L := bourgainLocalizationScale X Y
  let P := bourgainLocalizationMultiplierBound Y L
  let V := ∏ j : Fin 4,
    (2 * bourgainLocalizationEpsilon (Y j) / L j)
  let A := bourgainWeightedScaledNearEnergy Y x (fun q => ‖a q‖)
  let B := bourgainWeightedScaledNearEnergy X y (fun q => ‖b q‖)
  let FI := ∫ z : BourgainPhaseSpace,
    ‖bourgainLocalCoefficientSum Y L x a z‖ ^ (2 : ℕ)
  let GI := ∫ z in bourgainFourCube,
    ‖bourgainWeightedFourierSum L y
      (bourgainLocalizedFourierWeight Y L y b) z‖ ^ (2 : ℕ)
  have hL : ∀ j, 0 < L j :=
    bourgainLocalizationScale_pos hX hY
  have hXL : ∀ j, X j ≤ L j := by
    intro j
    unfold L bourgainLocalizationScale
    have heps : 0 < bourgainLocalizationEpsilon (Y j) := by
      unfold bourgainLocalizationEpsilon
      exact one_div_pos.mpr (mul_pos (by norm_num) (hY j))
    linarith
  have hbase :
      ‖bourgainBilinearForm x y a b‖ ^ (2 : ℕ) ≤ FI * GI :=
    bourgainBilinearForm_sq_le_l2 x y a b hX hY hx hy
  have hFI : FI ≤ V * A := by
    exact integral_norm_bourgainLocalCoefficientSum_sq_le
      x a hY hL
  have hGLS :
      GI ≤ (Real.exp (4 * Real.pi) * 331776) *
        bourgainWeightedScaledNearEnergy L y
          (fun q => ‖bourgainLocalizedFourierWeight Y L y b q‖) :=
    integral_bourgainFourCube_l2_le_scaledNear L y
      (bourgainLocalizedFourierWeight Y L y b)
  have henergy :
      bourgainWeightedScaledNearEnergy L y
          (fun q => ‖bourgainLocalizedFourierWeight Y L y b q‖) ≤
        P ^ (2 : ℕ) * B :=
    bourgainLocalizedWeight_scaledNearEnergy_le y b
      (fun j => (hX j).le) hY hL hXL hy
  have hGI :
      GI ≤ (Real.exp (4 * Real.pi) * 331776) *
        (P ^ (2 : ℕ) * B) := by
    calc
      GI ≤ (Real.exp (4 * Real.pi) * 331776) *
          bourgainWeightedScaledNearEnergy L y
            (fun q => ‖bourgainLocalizedFourierWeight Y L y b q‖) :=
        hGLS
      _ ≤ (Real.exp (4 * Real.pi) * 331776) *
          (P ^ (2 : ℕ) * B) := by
        exact mul_le_mul_of_nonneg_left henergy (by positivity)
  have hGI0 : 0 ≤ GI :=
    integral_nonneg fun z => by positivity
  have hV0 : 0 ≤ V := by
    unfold V
    exact Finset.prod_nonneg fun j hj => by
      have heps : 0 < bourgainLocalizationEpsilon (Y j) := by
        unfold bourgainLocalizationEpsilon
        exact one_div_pos.mpr (mul_pos (by norm_num) (hY j))
      exact div_nonneg (mul_nonneg (by norm_num) heps.le) (hL j).le
  have hA0 : 0 ≤ A :=
    bourgainWeightedScaledNearEnergy_nonneg Y x
      (fun q => ‖a q‖) (fun q => norm_nonneg _)
  have hVA0 : 0 ≤ V * A := mul_nonneg hV0 hA0
  calc
    ‖bourgainBilinearForm x y a b‖ ^ (2 : ℕ) ≤ FI * GI := hbase
    _ ≤ (V * A) * GI :=
      mul_le_mul_of_nonneg_right hFI hGI0
    _ ≤ (V * A) *
        ((Real.exp (4 * Real.pi) * 331776) *
          (P ^ (2 : ℕ) * B)) :=
      mul_le_mul_of_nonneg_left hGI hVA0
    _ = _ := rfl

theorem bourgainLocalizationVolume_mul_multiplier_sq
    {Y L : BourgainPhaseSpace}
    (hY : ∀ j, 0 < Y j) (hL : ∀ j, 0 < L j) :
    (∏ j : Fin 4,
        (2 * bourgainLocalizationEpsilon (Y j) / L j)) *
        bourgainLocalizationMultiplierBound Y L ^ (2 : ℕ) =
      ∏ j : Fin 4, (Real.pi ^ (2 : ℕ) * (Y j * L j)) := by
  unfold bourgainLocalizationMultiplierBound
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  unfold bourgainLocalizationEpsilon
  field_simp [(hY j).ne', (hL j).ne']
  ring

theorem bourgainDoubleLargeSieve
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {X Y : BourgainPhaseSpace}
    (x : ι → BourgainPhaseSpace) (y : κ → BourgainPhaseSpace)
    (a : ι → ℂ) (b : κ → ℂ)
    (hX : ∀ j, 0 < X j) (hY : ∀ j, 0 < Y j)
    (hx : ∀ q j, |x q j| ≤ X j)
    (hy : ∀ q j, |y q j| ≤ Y j) :
    ‖bourgainBilinearForm x y a b‖ ^ (2 : ℕ) ≤
      ((Real.exp (4 * Real.pi) * 331776) *
        (∏ j : Fin 4,
          (Real.pi ^ (2 : ℕ) *
            (Y j * bourgainLocalizationScale X Y j)))) *
      (bourgainWeightedScaledNearEnergy Y x (fun q => ‖a q‖) *
        bourgainWeightedScaledNearEnergy X y (fun q => ‖b q‖)) := by
  let L := bourgainLocalizationScale X Y
  let V := ∏ j : Fin 4,
    (2 * bourgainLocalizationEpsilon (Y j) / L j)
  let P := bourgainLocalizationMultiplierBound Y L
  let A := bourgainWeightedScaledNearEnergy Y x (fun q => ‖a q‖)
  let B := bourgainWeightedScaledNearEnergy X y (fun q => ‖b q‖)
  have hL : ∀ j, 0 < L j :=
    bourgainLocalizationScale_pos hX hY
  have hfact :=
    bourgainDoubleLargeSieve_factored x y a b hX hY hx hy
  have hVP :
      V * P ^ (2 : ℕ) =
        ∏ j : Fin 4, (Real.pi ^ (2 : ℕ) * (Y j * L j)) :=
    bourgainLocalizationVolume_mul_multiplier_sq hY hL
  calc
    ‖bourgainBilinearForm x y a b‖ ^ (2 : ℕ) ≤
        (V * A) *
          ((Real.exp (4 * Real.pi) * 331776) *
            (P ^ (2 : ℕ) * B)) := hfact
    _ = ((Real.exp (4 * Real.pi) * 331776) *
          (V * P ^ (2 : ℕ))) * (A * B) := by ring
    _ = ((Real.exp (4 * Real.pi) * 331776) *
          (∏ j : Fin 4,
            (Real.pi ^ (2 : ℕ) * (Y j * L j)))) *
          (A * B) := by rw [hVP]
    _ = _ := rfl

theorem bourgainLocalizationScale_product_le
    {X Y : BourgainPhaseSpace}
    (hX : ∀ j, 0 < X j) (hY : ∀ j, 0 < Y j) :
    (∏ j : Fin 4,
        (Real.pi ^ (2 : ℕ) *
          (Y j * bourgainLocalizationScale X Y j))) ≤
      ∏ j : Fin 4,
        (Real.pi ^ (2 : ℕ) * (1 + X j * Y j)) := by
  apply Finset.prod_le_prod
  · intro j hj
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg (hY j).le
        (bourgainLocalizationScale_pos hX hY j).le)
  · intro j hj
    have hscale :
        Y j * bourgainLocalizationScale X Y j =
          X j * Y j + 1 / 8 := by
      unfold bourgainLocalizationScale bourgainLocalizationEpsilon
      field_simp [(hY j).ne']
    rw [hscale]
    have hpi2 : 0 ≤ Real.pi ^ (2 : ℕ) := sq_nonneg _
    apply mul_le_mul_of_nonneg_left _ hpi2
    linarith

/-- Four-dimensional Bombieri--Iwaniec double large sieve with explicit
constant and standard scale product. -/
theorem bourgainDoubleLargeSieve_standardScale
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {X Y : BourgainPhaseSpace}
    (x : ι → BourgainPhaseSpace) (y : κ → BourgainPhaseSpace)
    (a : ι → ℂ) (b : κ → ℂ)
    (hX : ∀ j, 0 < X j) (hY : ∀ j, 0 < Y j)
    (hx : ∀ q j, |x q j| ≤ X j)
    (hy : ∀ q j, |y q j| ≤ Y j) :
    ‖bourgainBilinearForm x y a b‖ ^ (2 : ℕ) ≤
      ((Real.exp (4 * Real.pi) * 331776) *
        (∏ j : Fin 4,
          (Real.pi ^ (2 : ℕ) * (1 + X j * Y j)))) *
      (bourgainWeightedScaledNearEnergy Y x (fun q => ‖a q‖) *
        bourgainWeightedScaledNearEnergy X y (fun q => ‖b q‖)) := by
  have hdls := bourgainDoubleLargeSieve x y a b hX hY hx hy
  have hprod := bourgainLocalizationScale_product_le hX hY
  have hA :
      0 ≤ bourgainWeightedScaledNearEnergy Y x (fun q => ‖a q‖) :=
    bourgainWeightedScaledNearEnergy_nonneg Y x
      (fun q => ‖a q‖) (fun q => norm_nonneg _)
  have hB :
      0 ≤ bourgainWeightedScaledNearEnergy X y (fun q => ‖b q‖) :=
    bourgainWeightedScaledNearEnergy_nonneg X y
      (fun q => ‖b q‖) (fun q => norm_nonneg _)
  calc
    ‖bourgainBilinearForm x y a b‖ ^ (2 : ℕ) ≤
        ((Real.exp (4 * Real.pi) * 331776) *
          (∏ j : Fin 4,
            (Real.pi ^ (2 : ℕ) *
              (Y j * bourgainLocalizationScale X Y j)))) *
        (bourgainWeightedScaledNearEnergy Y x (fun q => ‖a q‖) *
          bourgainWeightedScaledNearEnergy X y (fun q => ‖b q‖)) :=
      hdls
    _ ≤ ((Real.exp (4 * Real.pi) * 331776) *
          (∏ j : Fin 4,
            (Real.pi ^ (2 : ℕ) * (1 + X j * Y j)))) *
        (bourgainWeightedScaledNearEnergy Y x (fun q => ‖a q‖) *
          bourgainWeightedScaledNearEnergy X y (fun q => ‖b q‖)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprod (by positivity))
        (mul_nonneg hA hB)

end

end RHTower
