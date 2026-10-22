import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenSixthJet
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionFourthTuran

/-!
# Sixth reflection--Turan jet of the theta source

This is the literal extension of the atomwise likelihood-ratio derivative ladder beyond the
fourth reflected Turán layer.  It records the two missing logarithmic difference jets.  The
subsequent task is quantitative: carry these exact jets through the higher-atom series with a
summable sixth-order majorant.
-/

namespace RHTower

noncomputable section

/-- Fifth logarithmic derivative of an atom-to-first-atom likelihood ratio. -/
def thetaCuspAtomLikelihoodLogJetFour (n : ℕ) (x : ℝ) : ℝ :=
  -(thetaCuspBornWittenLogFifthDerivative n x -
    thetaCuspBornWittenLogFifthDerivative 1 x)

/-- Sixth logarithmic derivative of an atom-to-first-atom likelihood ratio. -/
def thetaCuspAtomLikelihoodLogJetFive (n : ℕ) (x : ℝ) : ℝ :=
  -(thetaCuspBornWittenLogSixthDerivative n x -
    thetaCuspBornWittenLogSixthDerivative 1 x)

/-- The existing fourth likelihood log jet differentiates to the new fifth one. -/
theorem hasDerivAt_thetaCuspAtomLikelihoodLogJetThree
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (thetaCuspAtomLikelihoodLogJetThree n)
      (thetaCuspAtomLikelihoodLogJetFour n x) x := by
  exact (hasDerivAt_thetaCuspBornWittenLogFourthDerivative hn hx |>.sub
    (hasDerivAt_thetaCuspBornWittenLogFourthDerivative
      (n := 1) (by norm_num) hx)).neg

/-- The new fifth likelihood log jet differentiates to the literal sixth one. -/
theorem hasDerivAt_thetaCuspAtomLikelihoodLogJetFour
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (thetaCuspAtomLikelihoodLogJetFour n)
      (thetaCuspAtomLikelihoodLogJetFive n x) x := by
  exact (hasDerivAt_thetaCuspBornWittenLogFifthDerivative hn hx |>.sub
    (hasDerivAt_thetaCuspBornWittenLogFifthDerivative
      (n := 1) (by norm_num) hx)).neg

/-- Fifth ordinary derivative of an atom-to-first-atom likelihood ratio. -/
def thetaCuspAtomLikelihoodRatioJetFive (n : ℕ) (x : ℝ) : ℝ :=
  (thetaCuspAtomLikelihoodLogJetZero n x ^ (5 : ℕ) +
      10 * thetaCuspAtomLikelihoodLogJetZero n x ^ (3 : ℕ) *
        thetaCuspAtomLikelihoodLogJetOne n x +
      15 * thetaCuspAtomLikelihoodLogJetZero n x *
        thetaCuspAtomLikelihoodLogJetOne n x ^ (2 : ℕ) +
      10 * thetaCuspAtomLikelihoodLogJetZero n x ^ (2 : ℕ) *
        thetaCuspAtomLikelihoodLogJetTwo n x +
      10 * thetaCuspAtomLikelihoodLogJetOne n x *
        thetaCuspAtomLikelihoodLogJetTwo n x +
      5 * thetaCuspAtomLikelihoodLogJetZero n x *
        thetaCuspAtomLikelihoodLogJetThree n x +
      thetaCuspAtomLikelihoodLogJetFour n x) *
    thetaCuspAtomLikelihoodRatio n x

/-- Differentiating the fourth ordinary likelihood jet produces its fifth Bell jet. -/
theorem hasDerivAt_thetaCuspAtomLikelihoodRatioJetFour
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaCuspAtomLikelihoodRatioJetFour n)
      (thetaCuspAtomLikelihoodRatioJetFive n x) x := by
  have h0 := hasDerivAt_thetaCuspAtomLikelihoodLogJetZero hn hx.le
  have h1 := hasDerivAt_thetaCuspAtomLikelihoodLogJetOne hn hx.le
  have h2 := hasDerivAt_thetaCuspAtomLikelihoodLogJetTwo hn hx.le
  have h3 := hasDerivAt_thetaCuspAtomLikelihoodLogJetThree hn hx.le
  have hr := hasDerivAt_thetaCuspAtomLikelihoodRatio hn hx
  have hr' : HasDerivAt (thetaCuspAtomLikelihoodRatio n)
      (thetaCuspAtomLikelihoodLogJetZero n x *
        thetaCuspAtomLikelihoodRatio n x) x := by
    simpa [thetaCuspAtomLikelihoodLogJetZero] using hr
  have hcoeff := ((((h0.pow 4).add
      (((h0.pow 2).mul h1).const_mul 6)).add
      ((h1.pow 2).const_mul 3)).add
      ((h0.mul h2).const_mul 4)).add h3
  norm_num at hcoeff
  have hcoeff' : HasDerivAt
      (fun y : ℝ => thetaCuspAtomLikelihoodLogJetZero n y ^ (4 : ℕ) +
        6 * thetaCuspAtomLikelihoodLogJetZero n y ^ (2 : ℕ) *
          thetaCuspAtomLikelihoodLogJetOne n y +
        3 * thetaCuspAtomLikelihoodLogJetOne n y ^ (2 : ℕ) +
        4 * thetaCuspAtomLikelihoodLogJetZero n y *
          thetaCuspAtomLikelihoodLogJetTwo n y +
        thetaCuspAtomLikelihoodLogJetThree n y)
      (4 * thetaCuspAtomLikelihoodLogJetZero n x ^ (3 : ℕ) *
          thetaCuspAtomLikelihoodLogJetOne n x +
        6 * (2 * thetaCuspAtomLikelihoodLogJetZero n x *
            thetaCuspAtomLikelihoodLogJetOne n x *
              thetaCuspAtomLikelihoodLogJetOne n x +
          thetaCuspAtomLikelihoodLogJetZero n x ^ (2 : ℕ) *
            thetaCuspAtomLikelihoodLogJetTwo n x) +
        3 * (2 * thetaCuspAtomLikelihoodLogJetOne n x *
          thetaCuspAtomLikelihoodLogJetTwo n x) +
        4 * (thetaCuspAtomLikelihoodLogJetOne n x *
            thetaCuspAtomLikelihoodLogJetTwo n x +
          thetaCuspAtomLikelihoodLogJetZero n x *
            thetaCuspAtomLikelihoodLogJetThree n x) +
        thetaCuspAtomLikelihoodLogJetFour n x) x := by
    apply hcoeff.congr_of_eventuallyEq
    filter_upwards with y
    simp only [Pi.add_apply, Pi.pow_apply]
    ring
  have hsource : thetaCuspAtomLikelihoodRatioJetFour n =ᶠ[nhds x]
      (fun y : ℝ =>
        (thetaCuspAtomLikelihoodLogJetZero n y ^ (4 : ℕ) +
          6 * thetaCuspAtomLikelihoodLogJetZero n y ^ (2 : ℕ) *
            thetaCuspAtomLikelihoodLogJetOne n y +
          3 * thetaCuspAtomLikelihoodLogJetOne n y ^ (2 : ℕ) +
          4 * thetaCuspAtomLikelihoodLogJetZero n y *
            thetaCuspAtomLikelihoodLogJetTwo n y +
          thetaCuspAtomLikelihoodLogJetThree n y) *
        thetaCuspAtomLikelihoodRatio n y) := by
    filter_upwards with y
    simp only [thetaCuspAtomLikelihoodRatioJetFour]
  have hproduct := (hcoeff'.mul hr').congr_of_eventuallyEq hsource
  unfold thetaCuspAtomLikelihoodRatioJetFive
  refine hproduct.congr_deriv ?_
  ring

/-- Sixth ordinary derivative of an atom-to-first-atom likelihood ratio. -/
def thetaCuspAtomLikelihoodRatioJetSix (n : ℕ) (x : ℝ) : ℝ :=
  (thetaCuspAtomLikelihoodLogJetZero n x ^ (6 : ℕ) +
      15 * thetaCuspAtomLikelihoodLogJetZero n x ^ (4 : ℕ) *
        thetaCuspAtomLikelihoodLogJetOne n x +
      45 * thetaCuspAtomLikelihoodLogJetZero n x ^ (2 : ℕ) *
        thetaCuspAtomLikelihoodLogJetOne n x ^ (2 : ℕ) +
      15 * thetaCuspAtomLikelihoodLogJetOne n x ^ (3 : ℕ) +
      20 * thetaCuspAtomLikelihoodLogJetZero n x ^ (3 : ℕ) *
        thetaCuspAtomLikelihoodLogJetTwo n x +
      60 * thetaCuspAtomLikelihoodLogJetZero n x *
        thetaCuspAtomLikelihoodLogJetOne n x *
          thetaCuspAtomLikelihoodLogJetTwo n x +
      10 * thetaCuspAtomLikelihoodLogJetTwo n x ^ (2 : ℕ) +
      15 * thetaCuspAtomLikelihoodLogJetZero n x ^ (2 : ℕ) *
        thetaCuspAtomLikelihoodLogJetThree n x +
      15 * thetaCuspAtomLikelihoodLogJetOne n x *
        thetaCuspAtomLikelihoodLogJetThree n x +
      6 * thetaCuspAtomLikelihoodLogJetZero n x *
        thetaCuspAtomLikelihoodLogJetFour n x +
      thetaCuspAtomLikelihoodLogJetFive n x) *
    thetaCuspAtomLikelihoodRatio n x

/-- Differentiating the fifth ordinary likelihood jet produces its sixth Bell jet. -/
theorem hasDerivAt_thetaCuspAtomLikelihoodRatioJetFive
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaCuspAtomLikelihoodRatioJetFive n)
      (thetaCuspAtomLikelihoodRatioJetSix n x) x := by
  have h0 := hasDerivAt_thetaCuspAtomLikelihoodLogJetZero hn hx.le
  have h1 := hasDerivAt_thetaCuspAtomLikelihoodLogJetOne hn hx.le
  have h2 := hasDerivAt_thetaCuspAtomLikelihoodLogJetTwo hn hx.le
  have h3 := hasDerivAt_thetaCuspAtomLikelihoodLogJetThree hn hx.le
  have h4 := hasDerivAt_thetaCuspAtomLikelihoodLogJetFour hn hx.le
  have hr := hasDerivAt_thetaCuspAtomLikelihoodRatio hn hx
  have hr' : HasDerivAt (thetaCuspAtomLikelihoodRatio n)
      (thetaCuspAtomLikelihoodLogJetZero n x *
        thetaCuspAtomLikelihoodRatio n x) x := by
    simpa [thetaCuspAtomLikelihoodLogJetZero] using hr
  have hcoeff := (((((((h0.pow 5).add
      (((h0.pow 3).mul h1).const_mul 10)).add
      ((h0.mul (h1.pow 2)).const_mul 15)).add
      (((h0.pow 2).mul h2).const_mul 10)).add
      ((h1.mul h2).const_mul 10)).add
      ((h0.mul h3).const_mul 5)).add h4)
  norm_num at hcoeff
  have hcoeff' : HasDerivAt
      (fun y : ℝ => thetaCuspAtomLikelihoodLogJetZero n y ^ (5 : ℕ) +
        10 * thetaCuspAtomLikelihoodLogJetZero n y ^ (3 : ℕ) *
          thetaCuspAtomLikelihoodLogJetOne n y +
        15 * thetaCuspAtomLikelihoodLogJetZero n y *
          thetaCuspAtomLikelihoodLogJetOne n y ^ (2 : ℕ) +
        10 * thetaCuspAtomLikelihoodLogJetZero n y ^ (2 : ℕ) *
          thetaCuspAtomLikelihoodLogJetTwo n y +
        10 * thetaCuspAtomLikelihoodLogJetOne n y *
          thetaCuspAtomLikelihoodLogJetTwo n y +
        5 * thetaCuspAtomLikelihoodLogJetZero n y *
          thetaCuspAtomLikelihoodLogJetThree n y +
        thetaCuspAtomLikelihoodLogJetFour n y)
      (5 * thetaCuspAtomLikelihoodLogJetZero n x ^ (4 : ℕ) *
          thetaCuspAtomLikelihoodLogJetOne n x +
        10 * (3 * thetaCuspAtomLikelihoodLogJetZero n x ^ (2 : ℕ) *
            thetaCuspAtomLikelihoodLogJetOne n x *
              thetaCuspAtomLikelihoodLogJetOne n x +
          thetaCuspAtomLikelihoodLogJetZero n x ^ (3 : ℕ) *
            thetaCuspAtomLikelihoodLogJetTwo n x) +
        15 * (thetaCuspAtomLikelihoodLogJetOne n x *
            thetaCuspAtomLikelihoodLogJetOne n x ^ (2 : ℕ) +
          thetaCuspAtomLikelihoodLogJetZero n x *
            (2 * thetaCuspAtomLikelihoodLogJetOne n x *
              thetaCuspAtomLikelihoodLogJetTwo n x)) +
        10 * (2 * thetaCuspAtomLikelihoodLogJetZero n x *
            thetaCuspAtomLikelihoodLogJetOne n x *
              thetaCuspAtomLikelihoodLogJetTwo n x +
          thetaCuspAtomLikelihoodLogJetZero n x ^ (2 : ℕ) *
            thetaCuspAtomLikelihoodLogJetThree n x) +
        10 * (thetaCuspAtomLikelihoodLogJetTwo n x *
            thetaCuspAtomLikelihoodLogJetTwo n x +
          thetaCuspAtomLikelihoodLogJetOne n x *
            thetaCuspAtomLikelihoodLogJetThree n x) +
        5 * (thetaCuspAtomLikelihoodLogJetOne n x *
            thetaCuspAtomLikelihoodLogJetThree n x +
          thetaCuspAtomLikelihoodLogJetZero n x *
            thetaCuspAtomLikelihoodLogJetFour n x) +
        thetaCuspAtomLikelihoodLogJetFive n x) x := by
    apply hcoeff.congr_of_eventuallyEq
    filter_upwards with y
    simp only [Pi.add_apply, Pi.pow_apply]
    ring
  have hsource : thetaCuspAtomLikelihoodRatioJetFive n =ᶠ[nhds x]
      (fun y : ℝ =>
        (thetaCuspAtomLikelihoodLogJetZero n y ^ (5 : ℕ) +
          10 * thetaCuspAtomLikelihoodLogJetZero n y ^ (3 : ℕ) *
            thetaCuspAtomLikelihoodLogJetOne n y +
          15 * thetaCuspAtomLikelihoodLogJetZero n y *
            thetaCuspAtomLikelihoodLogJetOne n y ^ (2 : ℕ) +
          10 * thetaCuspAtomLikelihoodLogJetZero n y ^ (2 : ℕ) *
            thetaCuspAtomLikelihoodLogJetTwo n y +
          10 * thetaCuspAtomLikelihoodLogJetOne n y *
            thetaCuspAtomLikelihoodLogJetTwo n y +
          5 * thetaCuspAtomLikelihoodLogJetZero n y *
            thetaCuspAtomLikelihoodLogJetThree n y +
          thetaCuspAtomLikelihoodLogJetFour n y) *
        thetaCuspAtomLikelihoodRatio n y) := by
    filter_upwards with y
    simp only [thetaCuspAtomLikelihoodRatioJetFive]
  have hproduct := (hcoeff'.mul hr').congr_of_eventuallyEq hsource
  unfold thetaCuspAtomLikelihoodRatioJetSix
  refine hproduct.congr_deriv ?_
  ring

private theorem scale_div_sub_fifth_strictAnti
    {A T : ℝ} (hA : 3 < A) (hAT : A < T) :
    T / (T - 3 / 2) ^ (5 : ℕ) < A / (A - 3 / 2) ^ (5 : ℕ) := by
  have hAden : 0 < A - 3 / 2 := by linarith
  have hTden : 0 < T - 3 / 2 := by linarith
  have hfour : T / (T - 3 / 2) ^ (4 : ℕ) < A / (A - 3 / 2) ^ (4 : ℕ) := by
    have hsq : T / (T - 3 / 2) ^ (2 : ℕ) < A / (A - 3 / 2) ^ (2 : ℕ) := by
      apply (div_lt_div_iff₀ (sq_pos_of_pos hTden) (sq_pos_of_pos hAden)).2
      have hfactor : 0 < A * T - (3 / 2 : ℝ) ^ (2 : ℕ) := by nlinarith
      nlinarith [mul_pos (sub_pos.mpr hAT) hfactor]
    have hinv : (T - 3 / 2)⁻¹ < (A - 3 / 2)⁻¹ :=
      (inv_lt_inv₀ hTden hAden).2 (by linarith)
    have hcube : T / (T - 3 / 2) ^ (3 : ℕ) < A / (A - 3 / 2) ^ (3 : ℕ) := by
      rw [show T / (T - 3 / 2) ^ (3 : ℕ) =
          (T / (T - 3 / 2) ^ (2 : ℕ)) * (T - 3 / 2)⁻¹ by
        field_simp [hTden.ne'],
        show A / (A - 3 / 2) ^ (3 : ℕ) =
          (A / (A - 3 / 2) ^ (2 : ℕ)) * (A - 3 / 2)⁻¹ by
        field_simp [hAden.ne']]
      calc
        T / (T - 3 / 2) ^ (2 : ℕ) * (T - 3 / 2)⁻¹ <
            A / (A - 3 / 2) ^ (2 : ℕ) * (T - 3 / 2)⁻¹ :=
          mul_lt_mul_of_pos_right hsq (by positivity)
        _ < A / (A - 3 / 2) ^ (2 : ℕ) * (A - 3 / 2)⁻¹ :=
          mul_lt_mul_of_pos_left hinv (by positivity)
    rw [show T / (T - 3 / 2) ^ (4 : ℕ) =
        (T / (T - 3 / 2) ^ (3 : ℕ)) * (T - 3 / 2)⁻¹ by
      field_simp [hTden.ne'],
      show A / (A - 3 / 2) ^ (4 : ℕ) =
        (A / (A - 3 / 2) ^ (3 : ℕ)) * (A - 3 / 2)⁻¹ by
      field_simp [hAden.ne']]
    calc
      T / (T - 3 / 2) ^ (3 : ℕ) * (T - 3 / 2)⁻¹ <
          A / (A - 3 / 2) ^ (3 : ℕ) * (T - 3 / 2)⁻¹ :=
        mul_lt_mul_of_pos_right hcube (by positivity)
      _ < A / (A - 3 / 2) ^ (3 : ℕ) * (A - 3 / 2)⁻¹ :=
        mul_lt_mul_of_pos_left hinv (by positivity)
  have hinv : (T - 3 / 2)⁻¹ < (A - 3 / 2)⁻¹ :=
    (inv_lt_inv₀ hTden hAden).2 (by linarith)
  have hTinvpos : 0 < (T - 3 / 2)⁻¹ := inv_pos.mpr hTden
  have hAquotpos : 0 < A / (A - 3 / 2) ^ (5 : ℕ) :=
    div_pos (by linarith) (pow_pos hAden 5)
  rw [show T / (T - 3 / 2) ^ (5 : ℕ) =
      (T / (T - 3 / 2) ^ (4 : ℕ)) * (T - 3 / 2)⁻¹ by
    field_simp [hTden.ne'],
    show A / (A - 3 / 2) ^ (5 : ℕ) =
      (A / (A - 3 / 2) ^ (4 : ℕ)) * (A - 3 / 2)⁻¹ by
    field_simp [hAden.ne']]
  calc
    T / (T - 3 / 2) ^ (4 : ℕ) * (T - 3 / 2)⁻¹ <
        A / (A - 3 / 2) ^ (4 : ℕ) * (T - 3 / 2)⁻¹ :=
      mul_lt_mul_of_pos_right hfour hTinvpos
    _ < A / (A - 3 / 2) ^ (4 : ℕ) * (A - 3 / 2)⁻¹ :=
      mul_lt_mul_of_pos_left hinv (by positivity)

private theorem scale_div_sub_five_lt_thirtytwo_eightyfirsts
    {A : ℝ} (hA : 3 < A) :
    A / (A - 3 / 2) ^ (5 : ℕ) < (32 / 81 : ℝ) := by
  have hden : 0 < (A - 3 / 2) ^ (5 : ℕ) := pow_pos (by linarith) 5
  apply (div_lt_iff₀ hden).2
  let y := A - 3
  have hy : 0 < y := by dsimp [y]; linarith
  apply sub_pos.mp
  rw [show (32 / 81 : ℝ) * (A - 3 / 2) ^ (5 : ℕ) - A =
      (32 / 81) * y ^ (5 : ℕ) + (80 / 27) * y ^ (4 : ℕ) + (80 / 9) * y ^ (3 : ℕ) +
        (40 / 3) * y ^ (2 : ℕ) + 9 * y by dsimp [y]; ring]
  positivity

private theorem scale_div_sub_sixth_strictAnti
    {A T : ℝ} (hA : 3 < A) (hAT : A < T) :
    T / (T - 3 / 2) ^ (6 : ℕ) < A / (A - 3 / 2) ^ (6 : ℕ) := by
  have hAden : 0 < A - 3 / 2 := by linarith
  have hTden : 0 < T - 3 / 2 := by linarith
  have hfive := scale_div_sub_fifth_strictAnti hA hAT
  have hinv : (T - 3 / 2)⁻¹ < (A - 3 / 2)⁻¹ :=
    (inv_lt_inv₀ hTden hAden).2 (by linarith)
  have hTinvpos : 0 < (T - 3 / 2)⁻¹ := inv_pos.mpr hTden
  have hAquotpos : 0 < A / (A - 3 / 2) ^ (5 : ℕ) :=
    div_pos (by linarith) (pow_pos hAden 5)
  rw [show T / (T - 3 / 2) ^ (6 : ℕ) =
      (T / (T - 3 / 2) ^ (5 : ℕ)) * (T - 3 / 2)⁻¹ by
    field_simp [hTden.ne'],
    show A / (A - 3 / 2) ^ (6 : ℕ) =
      (A / (A - 3 / 2) ^ (5 : ℕ)) * (A - 3 / 2)⁻¹ by
    field_simp [hAden.ne']]
  calc
    T / (T - 3 / 2) ^ (5 : ℕ) * (T - 3 / 2)⁻¹ <
        A / (A - 3 / 2) ^ (5 : ℕ) * (T - 3 / 2)⁻¹ :=
      mul_lt_mul_of_pos_right hfive hTinvpos
    _ < A / (A - 3 / 2) ^ (5 : ℕ) * (A - 3 / 2)⁻¹ :=
      mul_lt_mul_of_pos_left hinv hAquotpos

private theorem scale_div_sub_six_lt_sixtyfour_twofortythirds
    {A : ℝ} (hA : 3 < A) :
    A / (A - 3 / 2) ^ (6 : ℕ) < (64 / 243 : ℝ) := by
  have hden : 0 < (A - 3 / 2) ^ (6 : ℕ) := pow_pos (by linarith) 6
  apply (div_lt_iff₀ hden).2
  let y := A - 3
  have hy : 0 < y := by dsimp [y]; linarith
  apply sub_pos.mp
  rw [show (64 / 243 : ℝ) * (A - 3 / 2) ^ (6 : ℕ) - A =
      (64 / 243) * y ^ (6 : ℕ) + (64 / 27) * y ^ (5 : ℕ) + (80 / 9) * y ^ (4 : ℕ) +
        (160 / 9) * y ^ (3 : ℕ) + 20 * y ^ (2 : ℕ) + 11 * y by dsimp [y]; ring]
  positivity

/-- The fifth atom likelihood log jet is strictly negative, with a leading source scale gap. -/
theorem thetaCuspAtomLikelihoodLogJetFour_neg
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x) :
    thetaCuspAtomLikelihoodLogJetFour n x <
      -32 * (thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)) := by
  let A := thetaCuspLogConcavityScale x
  let T := A * (n : ℝ) ^ (2 : ℕ)
  let z := A * ((n : ℝ) ^ (2 : ℕ) - 1)
  have hfacts := thetaCuspLikelihoodScaleFacts hn hx.le
  dsimp only at hfacts
  rcases hfacts with ⟨hA, _hd, _hz, hAT⟩
  have hnpos : 0 < n := by omega
  have hprofileN := thetaCuspBornWittenLogFifthDerivative_eq_scaleProfile hnpos hx.le
  have hprofile1 := thetaCuspBornWittenLogFifthDerivative_eq_scaleProfile
    (n := 1) (by norm_num) hx.le
  rw [thetaCuspMorseScale_eq_logConcavityScale_mul_sq] at hprofileN hprofile1
  norm_num at hprofile1
  have hanti2 := scale_div_sub_sq_strictAnti hA hAT
  have hanti3 := scale_div_sub_cube_strictAnti hA hAT
  have hanti4 := scale_div_sub_four_strictAnti hA hAT
  have hanti5 := scale_div_sub_fifth_strictAnti hA hAT
  have hvalue : thetaCuspAtomLikelihoodLogJetFour n x =
      -32 * z -
        48 * (A / (A - 3 / 2) ^ (2 : ℕ) - T / (T - 3 / 2) ^ (2 : ℕ)) -
        1008 * (A / (A - 3 / 2) ^ (3 : ℕ) - T / (T - 3 / 2) ^ (3 : ℕ)) -
        3888 * (A / (A - 3 / 2) ^ (4 : ℕ) - T / (T - 3 / 2) ^ (4 : ℕ)) -
        3888 * (A / (A - 3 / 2) ^ (5 : ℕ) - T / (T - 3 / 2) ^ (5 : ℕ)) := by
    unfold thetaCuspAtomLikelihoodLogJetFour
    rw [hprofileN, hprofile1]
    dsimp [z, T, A]
    ring
  rw [hvalue]
  dsimp [z, T, A]
  nlinarith

/-- The fifth atom likelihood log jet has a uniform linear source-scale envelope. -/
theorem thetaCuspAtomLikelihoodLogJetFour_abs_le
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x) :
    |thetaCuspAtomLikelihoodLogJetFour n x| ≤
      600 * (thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)) := by
  let A := thetaCuspLogConcavityScale x
  let T := A * (n : ℝ) ^ (2 : ℕ)
  let z := A * ((n : ℝ) ^ (2 : ℕ) - 1)
  have hfacts := thetaCuspLikelihoodScaleFacts hn hx.le
  dsimp only at hfacts
  rcases hfacts with ⟨hA, _hd, hz, hAT⟩
  have hnpos : 0 < n := by omega
  have hprofileN := thetaCuspBornWittenLogFifthDerivative_eq_scaleProfile hnpos hx.le
  have hprofile1 := thetaCuspBornWittenLogFifthDerivative_eq_scaleProfile
    (n := 1) (by norm_num) hx.le
  rw [thetaCuspMorseScale_eq_logConcavityScale_mul_sq] at hprofileN hprofile1
  norm_num at hprofile1
  have hanti2 := scale_div_sub_sq_strictAnti hA hAT
  have hanti3 := scale_div_sub_cube_strictAnti hA hAT
  have hanti4 := scale_div_sub_four_strictAnti hA hAT
  have hanti5 := scale_div_sub_fifth_strictAnti hA hAT
  have hA2 := scale_div_sub_sq_lt_four_thirds hA
  have hA3 := scale_div_sub_cube_lt_eight_ninths hA
  have hA4 := scale_div_sub_four_lt_sixteen_twentysevenths hA
  have hA5 := scale_div_sub_five_lt_thirtytwo_eightyfirsts hA
  have hT2 : 0 < T / (T - 3 / 2) ^ (2 : ℕ) :=
    div_pos (lt_trans (by linarith) hAT) (sq_pos_of_pos (by linarith))
  have hT3 : 0 < T / (T - 3 / 2) ^ (3 : ℕ) :=
    div_pos (lt_trans (by linarith) hAT) (pow_pos (by linarith) 3)
  have hT4 : 0 < T / (T - 3 / 2) ^ (4 : ℕ) :=
    div_pos (lt_trans (by linarith) hAT) (pow_pos (by linarith) 4)
  have hT5 : 0 < T / (T - 3 / 2) ^ (5 : ℕ) :=
    div_pos (lt_trans (by linarith) hAT) (pow_pos (by linarith) 5)
  have hvalue : thetaCuspAtomLikelihoodLogJetFour n x =
      -32 * z -
        48 * (A / (A - 3 / 2) ^ (2 : ℕ) - T / (T - 3 / 2) ^ (2 : ℕ)) -
        1008 * (A / (A - 3 / 2) ^ (3 : ℕ) - T / (T - 3 / 2) ^ (3 : ℕ)) -
        3888 * (A / (A - 3 / 2) ^ (4 : ℕ) - T / (T - 3 / 2) ^ (4 : ℕ)) -
        3888 * (A / (A - 3 / 2) ^ (5 : ℕ) - T / (T - 3 / 2) ^ (5 : ℕ)) := by
    unfold thetaCuspAtomLikelihoodLogJetFour
    rw [hprofileN, hprofile1]
    dsimp [z, T, A]
    ring
  rw [abs_le, hvalue]
  dsimp [z, T, A] at hz hanti2 hanti3 hanti4 hanti5 hA2 hA3 hA4 hA5 hT2 hT3 hT4 hT5 ⊢
  constructor <;> nlinarith

/-- The sixth atom likelihood log jet has a uniform linear source-scale envelope. -/
theorem thetaCuspAtomLikelihoodLogJetFive_abs_le
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x) :
    |thetaCuspAtomLikelihoodLogJetFive n x| ≤
      8000 * (thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)) := by
  let A := thetaCuspLogConcavityScale x
  let T := A * (n : ℝ) ^ (2 : ℕ)
  let z := A * ((n : ℝ) ^ (2 : ℕ) - 1)
  have hfacts := thetaCuspLikelihoodScaleFacts hn hx.le
  dsimp only at hfacts
  rcases hfacts with ⟨hA, _hd, hz, hAT⟩
  have hnpos : 0 < n := by omega
  have hprofileN := thetaCuspBornWittenLogSixthDerivative_eq_scaleProfile hnpos hx.le
  have hprofile1 := thetaCuspBornWittenLogSixthDerivative_eq_scaleProfile
    (n := 1) (by norm_num) hx.le
  rw [thetaCuspMorseScale_eq_logConcavityScale_mul_sq] at hprofileN hprofile1
  norm_num at hprofile1
  have hanti2 := scale_div_sub_sq_strictAnti hA hAT
  have hanti3 := scale_div_sub_cube_strictAnti hA hAT
  have hanti4 := scale_div_sub_four_strictAnti hA hAT
  have hanti5 := scale_div_sub_fifth_strictAnti hA hAT
  have hanti6 := scale_div_sub_sixth_strictAnti hA hAT
  have hA2 := scale_div_sub_sq_lt_four_thirds hA
  have hA3 := scale_div_sub_cube_lt_eight_ninths hA
  have hA4 := scale_div_sub_four_lt_sixteen_twentysevenths hA
  have hA5 := scale_div_sub_five_lt_thirtytwo_eightyfirsts hA
  have hA6 := scale_div_sub_six_lt_sixtyfour_twofortythirds hA
  have hT2 : 0 < T / (T - 3 / 2) ^ (2 : ℕ) :=
    div_pos (lt_trans (by linarith) hAT) (sq_pos_of_pos (by linarith))
  have hT3 : 0 < T / (T - 3 / 2) ^ (3 : ℕ) :=
    div_pos (lt_trans (by linarith) hAT) (pow_pos (by linarith) 3)
  have hT4 : 0 < T / (T - 3 / 2) ^ (4 : ℕ) :=
    div_pos (lt_trans (by linarith) hAT) (pow_pos (by linarith) 4)
  have hT5 : 0 < T / (T - 3 / 2) ^ (5 : ℕ) :=
    div_pos (lt_trans (by linarith) hAT) (pow_pos (by linarith) 5)
  have hT6 : 0 < T / (T - 3 / 2) ^ (6 : ℕ) :=
    div_pos (lt_trans (by linarith) hAT) (pow_pos (by linarith) 6)
  have hvalue : thetaCuspAtomLikelihoodLogJetFive n x =
      -64 * z +
        96 * (A / (A - 3 / 2) ^ (2 : ℕ) - T / (T - 3 / 2) ^ (2 : ℕ)) +
        4320 * (A / (A - 3 / 2) ^ (3 : ℕ) - T / (T - 3 / 2) ^ (3 : ℕ)) +
        32400 * (A / (A - 3 / 2) ^ (4 : ℕ) - T / (T - 3 / 2) ^ (4 : ℕ)) +
        77760 * (A / (A - 3 / 2) ^ (5 : ℕ) - T / (T - 3 / 2) ^ (5 : ℕ)) +
        58320 * (A / (A - 3 / 2) ^ (6 : ℕ) - T / (T - 3 / 2) ^ (6 : ℕ)) := by
    unfold thetaCuspAtomLikelihoodLogJetFive
    rw [hprofileN, hprofile1]
    dsimp [z, T, A]
    ring
  rw [abs_le, hvalue]
  dsimp [z, T, A] at hz hanti2 hanti3 hanti4 hanti5 hanti6 hA2 hA3 hA4 hA5 hA6 hT2 hT3 hT4 hT5 hT6 ⊢
  constructor <;> nlinarith

/-- A fifth-derivative Bell-polynomial majorant for one higher theta likelihood ratio. -/
theorem thetaCuspAtomLikelihoodRatioJetFive_abs_le
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x) :
    |thetaCuspAtomLikelihoodRatioJetFive n x| ≤
      5000 * (thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)) ^ (5 : ℕ) *
        thetaCuspAtomLikelihoodRatio n x := by
  let z := thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)
  let p := -thetaCuspAtomLikelihoodLogJetZero n x
  let alpha := -thetaCuspAtomLikelihoodLogJetOne n x
  let beta := -thetaCuspAtomLikelihoodLogJetTwo n x
  let gamma := thetaCuspAtomLikelihoodLogJetThree n x
  let delta := thetaCuspAtomLikelihoodLogJetFour n x
  have hq := thetaCuspAtomLikelihoodLogJetZero_bounds hn hx
  have hq1 := thetaCuspAtomLikelihoodLogJetOne_bounds hn hx
  have hq2 := thetaCuspAtomLikelihoodLogJetTwo_bounds hn hx
  have hq3 := thetaCuspAtomLikelihoodLogJetThree_abs_le hn hx
  have hq4 := thetaCuspAtomLikelihoodLogJetFour_abs_le hn hx
  have hr := thetaCuspAtomLikelihoodRatio_pos (by omega : 0 < n) hx
  have hz := (thetaCuspLikelihoodScaleFacts hn hx.le).2.2.1
  have hp0 : 0 ≤ p := by dsimp [p, z]; linarith
  have hp : p ≤ 3 * z := by dsimp [p, z]; linarith
  have ha0 : 0 ≤ alpha := by dsimp [alpha, z]; linarith
  have ha : alpha ≤ 4 * z := by dsimp [alpha, z]; linarith
  have hb0 : 0 ≤ beta := by dsimp [beta, z]; linarith
  have hb : beta ≤ 14 * z := by dsimp [beta, z]; linarith
  have hg : |gamma| ≤ 32 * z := by simpa only [gamma, z] using hq3
  have hdelta : |delta| ≤ 600 * z := by simpa only [delta, z] using hq4
  have hz0 : 0 ≤ z := by linarith
  have hz1 : 1 ≤ z := by linarith
  have hp2 : p ^ (2 : ℕ) ≤ 9 * z ^ (2 : ℕ) := by
    have h := pow_le_pow_left₀ hp0 hp 2
    nlinarith
  have hp3 : p ^ (3 : ℕ) ≤ 27 * z ^ (3 : ℕ) := by
    have h := pow_le_pow_left₀ hp0 hp 3
    nlinarith
  have hp5 : p ^ (5 : ℕ) ≤ 243 * z ^ (5 : ℕ) := by
    have h := pow_le_pow_left₀ hp0 hp 5
    nlinarith
  have ha2 : alpha ^ (2 : ℕ) ≤ 16 * z ^ (2 : ℕ) := by
    have h := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hz2one : 1 ≤ z ^ (2 : ℕ) := one_le_pow₀ hz1
  have hz3one : 1 ≤ z ^ (3 : ℕ) := one_le_pow₀ hz1
  have hz4one : 1 ≤ z ^ (4 : ℕ) := one_le_pow₀ hz1
  have hz2 : z ^ (2 : ℕ) ≤ z ^ (5 : ℕ) := by
    calc
      z ^ (2 : ℕ) = z ^ (2 : ℕ) * 1 := by ring
      _ ≤ z ^ (2 : ℕ) * z ^ (3 : ℕ) := by gcongr
      _ = z ^ (5 : ℕ) := by ring
  have hz3 : z ^ (3 : ℕ) ≤ z ^ (5 : ℕ) := by
    calc
      z ^ (3 : ℕ) = z ^ (3 : ℕ) * 1 := by ring
      _ ≤ z ^ (3 : ℕ) * z ^ (2 : ℕ) := by gcongr
      _ = z ^ (5 : ℕ) := by ring
  have hz4 : z ^ (4 : ℕ) ≤ z ^ (5 : ℕ) := by
    calc
      z ^ (4 : ℕ) = z ^ (4 : ℕ) * 1 := by ring
      _ ≤ z ^ (4 : ℕ) * z := by gcongr
      _ = z ^ (5 : ℕ) := by ring
  have hz1to5 : z ≤ z ^ (5 : ℕ) := by
    calc
      z = z * 1 := by ring
      _ ≤ z * z ^ (4 : ℕ) := by gcongr
      _ = z ^ (5 : ℕ) := by ring
  have hterm1 : |-p ^ (5 : ℕ)| ≤ 243 * z ^ (5 : ℕ) := by
    rw [abs_neg, abs_of_nonneg (pow_nonneg hp0 _)]
    exact hp5
  have hterm2 : |10 * p ^ (3 : ℕ) * alpha| ≤ 1080 * z ^ (5 : ℕ) := by
    have hbound : 10 * p ^ (3 : ℕ) * alpha ≤ 1080 * z ^ (4 : ℕ) := by
      calc
        10 * p ^ (3 : ℕ) * alpha ≤ 10 * (27 * z ^ (3 : ℕ)) * (4 * z) := by gcongr
        _ = 1080 * z ^ (4 : ℕ) := by ring
    rw [abs_of_nonneg (by positivity)]
    exact hbound.trans (by gcongr)
  have hterm3 : |-15 * p * alpha ^ (2 : ℕ)| ≤ 720 * z ^ (5 : ℕ) := by
    have hbound : 15 * p * alpha ^ (2 : ℕ) ≤ 720 * z ^ (3 : ℕ) := by
      calc
        15 * p * alpha ^ (2 : ℕ) ≤ 15 * (3 * z) * (16 * z ^ (2 : ℕ)) := by gcongr
        _ = 720 * z ^ (3 : ℕ) := by ring
    rw [abs_mul, abs_mul, abs_of_neg (by norm_num),
      abs_of_nonneg hp0, abs_of_nonneg (pow_nonneg ha0 _)]
    norm_num
    exact hbound.trans (by gcongr)
  have hterm4 : |-10 * p ^ (2 : ℕ) * beta| ≤ 1260 * z ^ (5 : ℕ) := by
    have hbound : 10 * p ^ (2 : ℕ) * beta ≤ 1260 * z ^ (3 : ℕ) := by
      calc
        10 * p ^ (2 : ℕ) * beta ≤ 10 * (9 * z ^ (2 : ℕ)) * (14 * z) := by gcongr
        _ = 1260 * z ^ (3 : ℕ) := by ring
    rw [abs_mul, abs_mul, abs_of_neg (by norm_num),
      abs_of_nonneg (pow_nonneg hp0 _), abs_of_nonneg hb0]
    norm_num
    exact hbound.trans (by gcongr)
  have hterm5 : |10 * alpha * beta| ≤ 560 * z ^ (5 : ℕ) := by
    have hbound : 10 * alpha * beta ≤ 560 * z ^ (2 : ℕ) := by
      calc
        10 * alpha * beta ≤ 10 * (4 * z) * (14 * z) := by gcongr
        _ = 560 * z ^ (2 : ℕ) := by ring
    rw [abs_of_nonneg (by positivity)]
    exact hbound.trans (by gcongr)
  have hterm6 : |-5 * p * gamma| ≤ 480 * z ^ (5 : ℕ) := by
    have hbound : 5 * p * |gamma| ≤ 480 * z ^ (2 : ℕ) := by
      calc
        5 * p * |gamma| ≤ 5 * (3 * z) * (32 * z) := by gcongr
        _ = 480 * z ^ (2 : ℕ) := by ring
    rw [abs_mul, abs_mul, abs_of_neg (by norm_num), abs_of_nonneg hp0]
    norm_num
    exact hbound.trans (by gcongr)
  have hterm7 : |delta| ≤ 600 * z ^ (5 : ℕ) :=
    hdelta.trans (by gcongr)
  have hcoeff :
      |-p ^ (5 : ℕ) + 10 * p ^ (3 : ℕ) * alpha - 15 * p * alpha ^ (2 : ℕ) -
          10 * p ^ (2 : ℕ) * beta + 10 * alpha * beta - 5 * p * gamma + delta| ≤
        5000 * z ^ (5 : ℕ) := by
    calc
      |-p ^ (5 : ℕ) + 10 * p ^ (3 : ℕ) * alpha - 15 * p * alpha ^ (2 : ℕ) -
            10 * p ^ (2 : ℕ) * beta + 10 * alpha * beta - 5 * p * gamma + delta| ≤
          |-p ^ (5 : ℕ)| + |10 * p ^ (3 : ℕ) * alpha| + |-15 * p * alpha ^ (2 : ℕ)| +
            |-10 * p ^ (2 : ℕ) * beta| + |10 * alpha * beta| + |-5 * p * gamma| + |delta| := by
        calc
          |-p ^ (5 : ℕ) + 10 * p ^ (3 : ℕ) * alpha - 15 * p * alpha ^ (2 : ℕ) -
              10 * p ^ (2 : ℕ) * beta + 10 * alpha * beta - 5 * p * gamma + delta| ≤
              |-p ^ (5 : ℕ) + 10 * p ^ (3 : ℕ) * alpha - 15 * p * alpha ^ (2 : ℕ) -
                10 * p ^ (2 : ℕ) * beta + 10 * alpha * beta - 5 * p * gamma| + |delta| :=
            abs_add_le _ _
          _ ≤ (|-p ^ (5 : ℕ) + 10 * p ^ (3 : ℕ) * alpha - 15 * p * alpha ^ (2 : ℕ) -
                10 * p ^ (2 : ℕ) * beta + 10 * alpha * beta| + |-5 * p * gamma|) + |delta| := by
            gcongr
            rw [show -5 * p * gamma = -(5 * p * gamma) by ring, abs_neg]
            exact abs_sub _ _
          _ ≤ ((|-p ^ (5 : ℕ) + 10 * p ^ (3 : ℕ) * alpha - 15 * p * alpha ^ (2 : ℕ) -
                10 * p ^ (2 : ℕ) * beta| + |10 * alpha * beta|) + |-5 * p * gamma|) + |delta| := by
            gcongr
            exact abs_add_le _ _
          _ ≤ (((|-p ^ (5 : ℕ) + 10 * p ^ (3 : ℕ) * alpha - 15 * p * alpha ^ (2 : ℕ)| +
                |-10 * p ^ (2 : ℕ) * beta|) + |10 * alpha * beta|) + |-5 * p * gamma|) + |delta| := by
            gcongr
            rw [show -10 * p ^ (2 : ℕ) * beta = -(10 * p ^ (2 : ℕ) * beta) by ring, abs_neg]
            exact abs_sub _ _
          _ ≤ ((((|-p ^ (5 : ℕ) + 10 * p ^ (3 : ℕ) * alpha| + |-15 * p * alpha ^ (2 : ℕ)|) +
                |-10 * p ^ (2 : ℕ) * beta|) + |10 * alpha * beta|) + |-5 * p * gamma|) + |delta| := by
            gcongr
            rw [show -15 * p * alpha ^ (2 : ℕ) = -(15 * p * alpha ^ (2 : ℕ)) by ring, abs_neg]
            exact abs_sub _ _
          _ ≤ (((|-p ^ (5 : ℕ)| + |10 * p ^ (3 : ℕ) * alpha|) + |-15 * p * alpha ^ (2 : ℕ)| +
                |-10 * p ^ (2 : ℕ) * beta| + |10 * alpha * beta| + |-5 * p * gamma| + |delta|)) := by
            gcongr
            exact abs_add_le _ _
      _ ≤ 5000 * z ^ (5 : ℕ) := by nlinarith
  unfold thetaCuspAtomLikelihoodRatioJetFive
  rw [abs_mul, abs_of_pos hr]
  apply mul_le_mul_of_nonneg_right _ hr.le
  rw [show thetaCuspAtomLikelihoodLogJetZero n x ^ (5 : ℕ) +
      10 * thetaCuspAtomLikelihoodLogJetZero n x ^ (3 : ℕ) *
        thetaCuspAtomLikelihoodLogJetOne n x +
      15 * thetaCuspAtomLikelihoodLogJetZero n x *
        thetaCuspAtomLikelihoodLogJetOne n x ^ (2 : ℕ) +
      10 * thetaCuspAtomLikelihoodLogJetZero n x ^ (2 : ℕ) *
        thetaCuspAtomLikelihoodLogJetTwo n x +
      10 * thetaCuspAtomLikelihoodLogJetOne n x *
        thetaCuspAtomLikelihoodLogJetTwo n x +
      5 * thetaCuspAtomLikelihoodLogJetZero n x *
        thetaCuspAtomLikelihoodLogJetThree n x +
      thetaCuspAtomLikelihoodLogJetFour n x =
      -p ^ (5 : ℕ) + 10 * p ^ (3 : ℕ) * alpha - 15 * p * alpha ^ (2 : ℕ) -
        10 * p ^ (2 : ℕ) * beta + 10 * alpha * beta - 5 * p * gamma + delta by
    dsimp [p, alpha, beta, gamma, delta]
    ring]
  exact hcoeff

end

end RHTower
