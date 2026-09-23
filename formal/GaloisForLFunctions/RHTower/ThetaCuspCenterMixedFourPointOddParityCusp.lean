import GaloisForLFunctions.RHTower.HedenmalmCenterMixedSixthHankelClosure
import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedFourPointEvenParityCusp
import GaloisForLFunctions.HilbertMetric.FourPointOddParityCusp

/-!
# Center-mixed odd four-point cusp closure

Extends the literal center-mixture jet chain from order six to order eight, transfers the
strict second--sixth Hankel margin to the reflection-odd equispaced four-point wall, and combines
it with the existing even wall.  Every physical aperture therefore has a nontrivial right-hand
interval on which the actual four-node theta Gram matrix is positive definite.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

def thetaCuspCenterMixedDensitySeventhJet (a t : ℝ) : ℝ :=
  thetaCuspCenterMixedDerivativeProductIntegral 7 0 a t -
    7 * thetaCuspCenterMixedDerivativeProductIntegral 6 1 a t +
      21 * thetaCuspCenterMixedDerivativeProductIntegral 5 2 a t -
        35 * thetaCuspCenterMixedDerivativeProductIntegral 4 3 a t +
          35 * thetaCuspCenterMixedDerivativeProductIntegral 3 4 a t -
            21 * thetaCuspCenterMixedDerivativeProductIntegral 2 5 a t +
              7 * thetaCuspCenterMixedDerivativeProductIntegral 1 6 a t -
                thetaCuspCenterMixedDerivativeProductIntegral 0 7 a t

def thetaCuspCenterMixedDensityEighthJet (a t : ℝ) : ℝ :=
  thetaCuspCenterMixedDerivativeProductIntegral 8 0 a t -
    8 * thetaCuspCenterMixedDerivativeProductIntegral 7 1 a t +
      28 * thetaCuspCenterMixedDerivativeProductIntegral 6 2 a t -
        56 * thetaCuspCenterMixedDerivativeProductIntegral 5 3 a t +
          70 * thetaCuspCenterMixedDerivativeProductIntegral 4 4 a t -
            56 * thetaCuspCenterMixedDerivativeProductIntegral 3 5 a t +
              28 * thetaCuspCenterMixedDerivativeProductIntegral 2 6 a t -
                8 * thetaCuspCenterMixedDerivativeProductIntegral 1 7 a t +
                  thetaCuspCenterMixedDerivativeProductIntegral 0 8 a t

theorem hasDerivAt_thetaCuspCenterMixedDensitySixthJet
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (t : ℝ) :
    HasDerivAt (thetaCuspCenterMixedDensitySixthJet a)
      (thetaCuspCenterMixedDensitySeventhJet a t) t := by
  have h60 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 6 0 t
  have h51 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 5 1 t
  have h42 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 4 2 t
  have h33 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 3 3 t
  have h24 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 2 4 t
  have h15 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 1 5 t
  have h06 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 0 6 t
  unfold thetaCuspCenterMixedDensitySixthJet thetaCuspCenterMixedDensitySeventhJet
  convert ((((((h60.sub (h51.const_mul 6)).add (h42.const_mul 15)).sub
    (h33.const_mul 20)).add (h24.const_mul 15)).sub (h15.const_mul 6)).add h06) using 1
  all_goals first | rfl | ring

theorem hasDerivAt_thetaCuspCenterMixedDensitySeventhJet
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (t : ℝ) :
    HasDerivAt (thetaCuspCenterMixedDensitySeventhJet a)
      (thetaCuspCenterMixedDensityEighthJet a t) t := by
  have h70 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 7 0 t
  have h61 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 6 1 t
  have h52 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 5 2 t
  have h43 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 4 3 t
  have h34 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 3 4 t
  have h25 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 2 5 t
  have h16 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 1 6 t
  have h07 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 0 7 t
  unfold thetaCuspCenterMixedDensitySeventhJet thetaCuspCenterMixedDensityEighthJet
  convert (((((((h70.sub (h61.const_mul 7)).add (h52.const_mul 21)).sub
    (h43.const_mul 35)).add (h34.const_mul 35)).sub (h25.const_mul 21)).add
      (h16.const_mul 7)).sub h07) using 1
  all_goals first | rfl | ring

theorem continuous_thetaCuspCenterMixedDensityEighthJet
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    Continuous (thetaCuspCenterMixedDensityEighthJet a) := by
  have hcont (m n : ℕ) :
      Continuous (thetaCuspCenterMixedDerivativeProductIntegral m n a) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha m n t).continuousAt
  unfold thetaCuspCenterMixedDensityEighthJet
  fun_prop

private theorem contDiff_succ_of_hasDerivAt_eight
    {n : ℕ} {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ContDiff ℝ n f') :
    ContDiff ℝ (n + 1) f := by
  rw [contDiff_succ_iff_deriv]
  refine ⟨fun x => (hf x).differentiableAt, by simp, ?_⟩
  rw [show deriv f = f' by
    funext x
    exact (hf x).deriv]
  exact hf'

theorem contDiff_eight_thetaCuspCenterMixedDensity
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    ContDiff ℝ 8 (thetaCuspCenterMixedDensity a) := by
  have h8 : ContDiff ℝ 0 (thetaCuspCenterMixedDensityEighthJet a) :=
    contDiff_zero.mpr (continuous_thetaCuspCenterMixedDensityEighthJet ha0 ha)
  have h7 : ContDiff ℝ 1 (thetaCuspCenterMixedDensitySeventhJet a) :=
    contDiff_succ_of_hasDerivAt_eight
      (fun t => hasDerivAt_thetaCuspCenterMixedDensitySeventhJet ha0 ha t) h8
  have h6 : ContDiff ℝ 2 (thetaCuspCenterMixedDensitySixthJet a) :=
    contDiff_succ_of_hasDerivAt_eight
      (fun t => hasDerivAt_thetaCuspCenterMixedDensitySixthJet ha0 ha t) h7
  have h5 : ContDiff ℝ 3 (thetaCuspCenterMixedDensityFifthJet a) :=
    contDiff_succ_of_hasDerivAt_eight
      (fun t => hasDerivAt_thetaCuspCenterMixedDensityFifthJet ha0 ha t) h6
  have h4 : ContDiff ℝ 4 (thetaCuspCenterMixedDensityFourthJet a) :=
    contDiff_succ_of_hasDerivAt_eight
      (fun t => hasDerivAt_thetaCuspCenterMixedDensityFourthJet ha0 ha t) h5
  have h3 : ContDiff ℝ 5 (thetaCuspCenterMixedDensityThirdJet a) :=
    contDiff_succ_of_hasDerivAt_eight
      (fun t => hasDerivAt_thetaCuspCenterMixedDensityThirdJet ha0 ha t) h4
  have h2 : ContDiff ℝ 6 (thetaCuspCenterMixedDensitySecondJet a) :=
    contDiff_succ_of_hasDerivAt_eight
      (fun t => hasDerivAt_thetaCuspCenterMixedDensitySecondJet ha0 ha t) h3
  have h1 : ContDiff ℝ 7 (thetaCuspCenterMixedDensityFirstJet a) :=
    contDiff_succ_of_hasDerivAt_eight
      (fun t => hasDerivAt_thetaCuspCenterMixedDensityFirstJet ha0 ha t) h2
  exact contDiff_succ_of_hasDerivAt_eight
    (fun t => hasDerivAt_thetaCuspCenterMixedDensity ha0 ha t) h1

theorem iteratedDeriv_zero_of_even_real_of_odd
    {f : ℝ → ℝ} (heven : Function.Even f) {n : ℕ} (hn : Odd n) :
    iteratedDeriv n f 0 = 0 := by
  have hfun : (fun x : ℝ => f (-x)) = f := funext heven
  have hcomp := iteratedDeriv_comp_neg n f 0
  rw [hfun, neg_zero, hn.neg_one_pow] at hcomp
  simp only [neg_one_smul] at hcomp
  linarith

theorem exists_thetaCuspCenterMixed_oddParityWall_pos_right
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, 0 < t → t < delta →
      0 < thetaCuspCenterMixedOddParityWall a t := by
  let f : ℝ → ℝ := thetaCuspCenterMixedDensity a
  have hf : ContDiff ℝ 8 f := contDiff_eight_thetaCuspCenterMixedDensity ha0.le ha
  have heven : Function.Even f := fun t => thetaCuspCenterMixedDensity_even a t
  have h1 : iteratedDeriv 1 f 0 = 0 :=
    iteratedDeriv_zero_of_even_real_of_odd heven (by norm_num)
  have h3 : iteratedDeriv 3 f 0 = 0 :=
    iteratedDeriv_zero_of_even_real_of_odd heven (by norm_num)
  have h5 : iteratedDeriv 5 f 0 = 0 :=
    iteratedDeriv_zero_of_even_real_of_odd heven (by norm_num)
  have h7 : iteratedDeriv 7 f 0 = 0 :=
    iteratedDeriv_zero_of_even_real_of_odd heven (by norm_num)
  have h6 : 0 < iteratedDeriv 2 f 0 * iteratedDeriv 6 f 0 -
      iteratedDeriv 4 f 0 ^ (2 : ℕ) :=
    thetaCuspCenterMixedDensity_iteratedDeriv_secondSixthHankel_pos ha0 ha
  rcases HilbertMetric.exists_fourPointOddWall_pos_right hf h1 h3 h5 h7 h6 with
    ⟨delta, hdelta, hwall⟩
  refine ⟨delta, hdelta, fun t ht ht_delta => ?_⟩
  simpa [thetaCuspCenterMixedOddParityWall, toeplitzFourOddParityWall,
    HilbertMetric.fourPointOddWall, f] using hwall t ht ht_delta

theorem exists_thetaCuspCenterMixedGramFourEquispaced_posSemidef_right
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, 0 < t → t < delta →
      Matrix.PosSemidef (thetaCuspCenterMixedGramFourEquispaced a t) := by
  rcases exists_thetaCuspCenterMixed_evenParityWall_pos_right ha0 ha with
    ⟨deltaEven, hdeltaEven, hEven⟩
  rcases exists_thetaCuspCenterMixed_oddParityWall_pos_right ha0 ha with
    ⟨deltaOdd, hdeltaOdd, hOdd⟩
  refine ⟨min deltaEven deltaOdd, lt_min hdeltaEven hdeltaOdd, fun t ht ht_delta => ?_⟩
  rw [thetaCuspCenterMixedGramFourEquispaced_posSemidef_iff_parityWalls ha0 ha ht]
  exact ⟨(hEven t ht (lt_of_lt_of_le ht_delta (min_le_left _ _))).le,
    (hOdd t ht (lt_of_lt_of_le ht_delta (min_le_right _ _))).le⟩

theorem det_toeplitzFour_eq_parityWalls (a b c d : ℝ) :
    (toeplitzFour a b c d).det =
      toeplitzFourEvenParityWall a b c d * toeplitzFourOddParityWall a b c d := by
  classical
  have h12 : (Fin.succAbove (1 : Fin 4) (2 : Fin 3)) = 3 := by decide
  have h21 : (Fin.succAbove (2 : Fin 4) (1 : Fin 3)) = 1 := by decide
  have h22 : (Fin.succAbove (2 : Fin 4) (2 : Fin 3)) = 3 := by decide
  have h31 : (Fin.succAbove (3 : Fin 4) (1 : Fin 3)) = 1 := by decide
  have h32 : (Fin.succAbove (3 : Fin 4) (2 : Fin 3)) = 2 := by decide
  rw [Matrix.det_succ_row_zero]
  simp [toeplitzFour, toeplitzFourEvenParityWall, toeplitzFourOddParityWall,
    Matrix.det_fin_three, Fin.sum_univ_four, h12, h21, h22, h31, h32]
  ring

theorem exists_thetaCuspCenterMixedGramFourEquispaced_posDef_right
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, 0 < t → t < delta →
      Matrix.PosDef (thetaCuspCenterMixedGramFourEquispaced a t) := by
  rcases exists_thetaCuspCenterMixed_evenParityWall_pos_right ha0 ha with
    ⟨deltaEven, hdeltaEven, hEven⟩
  rcases exists_thetaCuspCenterMixed_oddParityWall_pos_right ha0 ha with
    ⟨deltaOdd, hdeltaOdd, hOdd⟩
  refine ⟨min deltaEven deltaOdd, lt_min hdeltaEven hdeltaOdd, fun t ht ht_delta => ?_⟩
  have he := hEven t ht (lt_of_lt_of_le ht_delta (min_le_left _ _))
  have ho := hOdd t ht (lt_of_lt_of_le ht_delta (min_le_right _ _))
  have hpsd : Matrix.PosSemidef (thetaCuspCenterMixedGramFourEquispaced a t) :=
    (thetaCuspCenterMixedGramFourEquispaced_posSemidef_iff_parityWalls ha0 ha ht).2
      ⟨he.le, ho.le⟩
  apply hpsd.posDef_iff_det_ne_zero.mpr
  unfold thetaCuspCenterMixedGramFourEquispaced
  rw [det_toeplitzFour_eq_parityWalls]
  exact mul_ne_zero
    (by simpa [thetaCuspCenterMixedEvenParityWall] using he.ne')
    (by simpa [thetaCuspCenterMixedOddParityWall] using ho.ne')

end

end RHTower
