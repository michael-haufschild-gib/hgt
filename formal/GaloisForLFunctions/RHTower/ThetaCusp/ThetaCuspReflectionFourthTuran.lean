import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenPopescuCorrection
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspKernelLogConcavity

/-!
# Fourth reflection-Turan jet of the theta source

This file develops the source-side likelihood-ratio jets needed for the fourth local
reflection-product inequality.  The `n`th higher atom is divided by the first atom and its first
four derivatives are written as Bell polynomials in the exact Born--Witten score differences.
On the nonnegative logarithmic half-line these jets alternate strictly through order four, with
explicit Gaussian-scale bounds.

Only exact theta atoms and symbolic inequalities are used.  No zero computation or RH assumption
appears.
-/

open Real Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- First logarithmic jet of the `n`th atom-to-first-atom likelihood ratio. -/
def thetaCuspAtomLikelihoodLogJetZero (n : ℕ) (x : ℝ) : ℝ :=
  -2 * (thetaCuspBornWittenSuperpotential n x -
    thetaCuspBornWittenSuperpotential 1 x)

/-- Second logarithmic jet of the atom likelihood ratio. -/
def thetaCuspAtomLikelihoodLogJetOne (n : ℕ) (x : ℝ) : ℝ :=
  -(thetaCuspBornWittenLogCurvature n x -
    thetaCuspBornWittenLogCurvature 1 x)

/-- Third logarithmic jet of the atom likelihood ratio. -/
def thetaCuspAtomLikelihoodLogJetTwo (n : ℕ) (x : ℝ) : ℝ :=
  -(thetaCuspBornWittenLogThirdDerivative n x -
    thetaCuspBornWittenLogThirdDerivative 1 x)

/-- Fourth logarithmic jet of the atom likelihood ratio. -/
def thetaCuspAtomLikelihoodLogJetThree (n : ℕ) (x : ℝ) : ℝ :=
  -(thetaCuspBornWittenLogFourthDerivative n x -
    thetaCuspBornWittenLogFourthDerivative 1 x)

/-- First ordinary likelihood-ratio jet. -/
def thetaCuspAtomLikelihoodRatioJetOne (n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspAtomLikelihoodLogJetZero n x * thetaCuspAtomLikelihoodRatio n x

/-- Second ordinary likelihood-ratio jet. -/
def thetaCuspAtomLikelihoodRatioJetTwo (n : ℕ) (x : ℝ) : ℝ :=
  (thetaCuspAtomLikelihoodLogJetZero n x ^ (2 : ℕ) +
    thetaCuspAtomLikelihoodLogJetOne n x) * thetaCuspAtomLikelihoodRatio n x

/-- Third ordinary likelihood-ratio jet. -/
def thetaCuspAtomLikelihoodRatioJetThree (n : ℕ) (x : ℝ) : ℝ :=
  (thetaCuspAtomLikelihoodLogJetZero n x ^ (3 : ℕ) +
      3 * thetaCuspAtomLikelihoodLogJetZero n x *
        thetaCuspAtomLikelihoodLogJetOne n x +
      thetaCuspAtomLikelihoodLogJetTwo n x) *
    thetaCuspAtomLikelihoodRatio n x

/-- Fourth ordinary likelihood-ratio jet. -/
def thetaCuspAtomLikelihoodRatioJetFour (n : ℕ) (x : ℝ) : ℝ :=
  (thetaCuspAtomLikelihoodLogJetZero n x ^ (4 : ℕ) +
      6 * thetaCuspAtomLikelihoodLogJetZero n x ^ (2 : ℕ) *
        thetaCuspAtomLikelihoodLogJetOne n x +
      3 * thetaCuspAtomLikelihoodLogJetOne n x ^ (2 : ℕ) +
      4 * thetaCuspAtomLikelihoodLogJetZero n x *
        thetaCuspAtomLikelihoodLogJetTwo n x +
      thetaCuspAtomLikelihoodLogJetThree n x) *
    thetaCuspAtomLikelihoodRatio n x

theorem hasDerivAt_thetaCuspAtomLikelihoodLogJetZero
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (thetaCuspAtomLikelihoodLogJetZero n)
      (thetaCuspAtomLikelihoodLogJetOne n x) x := by
  have hn' := hasDerivAt_thetaCuspBornWittenSuperpotential hn hx
  have h1 := hasDerivAt_thetaCuspBornWittenSuperpotential (n := 1) (by norm_num) hx
  unfold thetaCuspAtomLikelihoodLogJetZero thetaCuspAtomLikelihoodLogJetOne
    thetaCuspBornWittenLogCurvature
  convert (hn'.sub h1).const_mul (-2) using 1 <;> first | rfl | ring

theorem hasDerivAt_thetaCuspAtomLikelihoodLogJetOne
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (thetaCuspAtomLikelihoodLogJetOne n)
      (thetaCuspAtomLikelihoodLogJetTwo n x) x := by
  exact (hasDerivAt_thetaCuspBornWittenLogCurvature hn hx |>.sub
    (hasDerivAt_thetaCuspBornWittenLogCurvature (n := 1) (by norm_num) hx)).neg

theorem hasDerivAt_thetaCuspAtomLikelihoodLogJetTwo
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (thetaCuspAtomLikelihoodLogJetTwo n)
      (thetaCuspAtomLikelihoodLogJetThree n x) x := by
  exact (hasDerivAt_thetaCuspBornWittenLogThirdDerivative hn hx |>.sub
    (hasDerivAt_thetaCuspBornWittenLogThirdDerivative
      (n := 1) (by norm_num) hx)).neg

theorem hasDerivAt_thetaCuspAtomLikelihoodRatioJetOne
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaCuspAtomLikelihoodRatioJetOne n)
      (thetaCuspAtomLikelihoodRatioJetTwo n x) x := by
  have hq := hasDerivAt_thetaCuspAtomLikelihoodLogJetZero hn hx.le
  have hr := hasDerivAt_thetaCuspAtomLikelihoodRatio hn hx
  have hr' : HasDerivAt (thetaCuspAtomLikelihoodRatio n)
      (thetaCuspAtomLikelihoodLogJetZero n x *
        thetaCuspAtomLikelihoodRatio n x) x := by
    simpa [thetaCuspAtomLikelihoodLogJetZero] using hr
  unfold thetaCuspAtomLikelihoodRatioJetOne thetaCuspAtomLikelihoodRatioJetTwo
  convert hq.mul hr' using 1 <;> first | rfl | ring

theorem hasDerivAt_thetaCuspAtomLikelihoodRatioJetTwo
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaCuspAtomLikelihoodRatioJetTwo n)
      (thetaCuspAtomLikelihoodRatioJetThree n x) x := by
  have hq := hasDerivAt_thetaCuspAtomLikelihoodLogJetZero hn hx.le
  have hq1 := hasDerivAt_thetaCuspAtomLikelihoodLogJetOne hn hx.le
  have hr := hasDerivAt_thetaCuspAtomLikelihoodRatio hn hx
  have hr' : HasDerivAt (thetaCuspAtomLikelihoodRatio n)
      (thetaCuspAtomLikelihoodLogJetZero n x *
        thetaCuspAtomLikelihoodRatio n x) x := by
    simpa [thetaCuspAtomLikelihoodLogJetZero] using hr
  have hcoeff := (hq.pow 2).add hq1
  unfold thetaCuspAtomLikelihoodRatioJetTwo thetaCuspAtomLikelihoodRatioJetThree
  convert hcoeff.mul hr' using 1 <;>
    first
      | rfl
      | (simp only [Pi.add_apply, Pi.pow_apply]; ring)

theorem hasDerivAt_thetaCuspAtomLikelihoodRatioJetThree
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaCuspAtomLikelihoodRatioJetThree n)
      (thetaCuspAtomLikelihoodRatioJetFour n x) x := by
  have hq := hasDerivAt_thetaCuspAtomLikelihoodLogJetZero hn hx.le
  have hq1 := hasDerivAt_thetaCuspAtomLikelihoodLogJetOne hn hx.le
  have hq2 := hasDerivAt_thetaCuspAtomLikelihoodLogJetTwo hn hx.le
  have hr := hasDerivAt_thetaCuspAtomLikelihoodRatio hn hx
  have hr' : HasDerivAt (thetaCuspAtomLikelihoodRatio n)
      (thetaCuspAtomLikelihoodLogJetZero n x *
        thetaCuspAtomLikelihoodRatio n x) x := by
    simpa [thetaCuspAtomLikelihoodLogJetZero] using hr
  have hcoeff := ((hq.pow 3).add ((hq.mul hq1).const_mul 3)).add hq2
  unfold thetaCuspAtomLikelihoodRatioJetThree thetaCuspAtomLikelihoodRatioJetFour
  convert hcoeff.mul hr' using 1 <;>
    first
      | rfl
      | ((try funext y); simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply]; ring)

theorem iteratedDeriv_one_thetaCuspAtomLikelihoodRatio_eq
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 1 (thetaCuspAtomLikelihoodRatio n) x =
      thetaCuspAtomLikelihoodRatioJetOne n x := by
  simp only [iteratedDeriv_one, thetaCuspAtomLikelihoodRatioJetOne,
    thetaCuspAtomLikelihoodLogJetZero]
  exact deriv_thetaCuspAtomLikelihoodRatio hn hx

theorem iteratedDeriv_two_thetaCuspAtomLikelihoodRatio_eq
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 2 (thetaCuspAtomLikelihoodRatio n) x =
      thetaCuspAtomLikelihoodRatioJetTwo n x := by
  have heq : deriv (thetaCuspAtomLikelihoodRatio n) =ᶠ[nhds x]
      thetaCuspAtomLikelihoodRatioJetOne n := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simpa only [iteratedDeriv_one] using
      iteratedDeriv_one_thetaCuspAtomLikelihoodRatio_eq hn hy
  rw [show iteratedDeriv 2 (thetaCuspAtomLikelihoodRatio n) x =
      deriv (deriv (thetaCuspAtomLikelihoodRatio n)) x by simp [iteratedDeriv_succ]]
  exact (hasDerivAt_thetaCuspAtomLikelihoodRatioJetOne hn hx |>.congr_of_eventuallyEq
    heq).deriv

theorem iteratedDeriv_three_thetaCuspAtomLikelihoodRatio_eq
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 3 (thetaCuspAtomLikelihoodRatio n) x =
      thetaCuspAtomLikelihoodRatioJetThree n x := by
  have heq : iteratedDeriv 2 (thetaCuspAtomLikelihoodRatio n) =ᶠ[nhds x]
      thetaCuspAtomLikelihoodRatioJetTwo n := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact iteratedDeriv_two_thetaCuspAtomLikelihoodRatio_eq hn hy
  rw [iteratedDeriv_succ]
  exact (hasDerivAt_thetaCuspAtomLikelihoodRatioJetTwo hn hx |>.congr_of_eventuallyEq
    heq).deriv

theorem iteratedDeriv_four_thetaCuspAtomLikelihoodRatio_eq
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 4 (thetaCuspAtomLikelihoodRatio n) x =
      thetaCuspAtomLikelihoodRatioJetFour n x := by
  have heq : iteratedDeriv 3 (thetaCuspAtomLikelihoodRatio n) =ᶠ[nhds x]
      thetaCuspAtomLikelihoodRatioJetThree n := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact iteratedDeriv_three_thetaCuspAtomLikelihoodRatio_eq hn hy
  rw [iteratedDeriv_succ]
  exact (hasDerivAt_thetaCuspAtomLikelihoodRatioJetThree hn hx |>.congr_of_eventuallyEq
    heq).deriv

theorem thetaCuspMorseScale_eq_logConcavityScale_mul_sq
    (n : ℕ) (x : ℝ) :
    thetaCuspMorseScale n x = thetaCuspLogConcavityScale x * (n : ℝ) ^ (2 : ℕ) := by
  unfold thetaCuspMorseScale thetaCuspLogConcavityScale
  ring

theorem scale_div_sub_sq_strictAnti
    {A T : ℝ} (hA : 3 < A) (hAT : A < T) :
    T / (T - 3 / 2) ^ (2 : ℕ) < A / (A - 3 / 2) ^ (2 : ℕ) := by
  have hAden : 0 < A - 3 / 2 := by linarith
  have hTden : 0 < T - 3 / 2 := by linarith
  apply (div_lt_div_iff₀ (sq_pos_of_pos hTden) (sq_pos_of_pos hAden)).2
  have hfactor : 0 < A * T - (3 / 2 : ℝ) ^ (2 : ℕ) := by nlinarith
  nlinarith [mul_pos (sub_pos.mpr hAT) hfactor]

theorem scale_div_sub_cube_strictAnti
    {A T : ℝ} (hA : 3 < A) (hAT : A < T) :
    T / (T - 3 / 2) ^ (3 : ℕ) < A / (A - 3 / 2) ^ (3 : ℕ) := by
  have hAden : 0 < A - 3 / 2 := by linarith
  have hTden : 0 < T - 3 / 2 := by linarith
  have hsq := scale_div_sub_sq_strictAnti hA hAT
  have hinv : (T - 3 / 2)⁻¹ < (A - 3 / 2)⁻¹ :=
    (inv_lt_inv₀ hTden hAden).2 (by linarith)
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

theorem scale_div_sub_four_strictAnti
    {A T : ℝ} (hA : 3 < A) (hAT : A < T) :
    T / (T - 3 / 2) ^ (4 : ℕ) < A / (A - 3 / 2) ^ (4 : ℕ) := by
  have hAden : 0 < A - 3 / 2 := by linarith
  have hTden : 0 < T - 3 / 2 := by linarith
  have hcube := scale_div_sub_cube_strictAnti hA hAT
  have hinv : (T - 3 / 2)⁻¹ < (A - 3 / 2)⁻¹ :=
    (inv_lt_inv₀ hTden hAden).2 (by linarith)
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

theorem scale_div_sub_sq_lt_four_thirds
    {A : ℝ} (hA : 3 < A) :
    A / (A - 3 / 2) ^ (2 : ℕ) < (4 / 3 : ℝ) := by
  have hden : 0 < (A - 3 / 2) ^ (2 : ℕ) := sq_pos_of_pos (by linarith)
  apply (div_lt_iff₀ hden).2
  have hprod : 0 < (A - 3) * (4 * A - 3) :=
    mul_pos (by linarith) (by linarith)
  nlinarith

theorem scale_div_sub_cube_lt_eight_ninths
    {A : ℝ} (hA : 3 < A) :
    A / (A - 3 / 2) ^ (3 : ℕ) < (8 / 9 : ℝ) := by
  have hden : 0 < (A - 3 / 2) ^ (3 : ℕ) := pow_pos (by linarith) 3
  apply (div_lt_iff₀ hden).2
  let y := A - 3
  have hy : 0 < y := by dsimp [y]; linarith
  apply sub_pos.mp
  rw [show (8 / 9 : ℝ) * (A - 3 / 2) ^ (3 : ℕ) - A =
      (8 / 9) * y ^ (3 : ℕ) + 4 * y ^ (2 : ℕ) + 5 * y by dsimp [y]; ring]
  positivity

theorem scale_div_sub_four_lt_sixteen_twentysevenths
    {A : ℝ} (hA : 3 < A) :
    A / (A - 3 / 2) ^ (4 : ℕ) < (16 / 27 : ℝ) := by
  have hden : 0 < (A - 3 / 2) ^ (4 : ℕ) := pow_pos (by linarith) 4
  apply (div_lt_iff₀ hden).2
  let y := A - 3
  have hy : 0 < y := by dsimp [y]; linarith
  apply sub_pos.mp
  rw [show (16 / 27 : ℝ) * (A - 3 / 2) ^ (4 : ℕ) - A =
      (16 / 27) * y ^ (4 : ℕ) + (32 / 9) * y ^ (3 : ℕ) + 8 * y ^ (2 : ℕ) + 7 * y by
    dsimp [y]; ring]
  positivity

private theorem thetaCuspBornWittenLogCurvature_eq_scaleProfile
    {n : ℕ} (_hn : 0 < n) {x : ℝ} (_hx : 0 ≤ x) :
    thetaCuspBornWittenLogCurvature n x =
      4 * thetaCuspMorseScale n x +
        6 * thetaCuspMorseScale n x /
          (thetaCuspMorseScale n x - 3 / 2) ^ (2 : ℕ) := by
  unfold thetaCuspBornWittenLogCurvature thetaCuspBornWittenCurvature
  rw [thetaCuspBornWittenWeight_eq]
  ring

private theorem thetaCuspBornWittenLogThirdDerivative_eq_scaleProfile
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspBornWittenLogThirdDerivative n x =
      8 * thetaCuspMorseScale n x -
        12 * thetaCuspMorseScale n x /
          (thetaCuspMorseScale n x - 3 / 2) ^ (2 : ℕ) -
        36 * thetaCuspMorseScale n x /
          (thetaCuspMorseScale n x - 3 / 2) ^ (3 : ℕ) := by
  have hweight := thetaCuspBornWittenWeight_pos hn hx
  rw [thetaCuspBornWittenWeight_eq] at hweight
  unfold thetaCuspBornWittenLogThirdDerivative
  rw [thetaCuspBornWittenWeight_eq]
  field_simp [hweight.ne']; ring

private theorem thetaCuspBornWittenLogFourthDerivative_eq_scaleProfile
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspBornWittenLogFourthDerivative n x =
      16 * thetaCuspMorseScale n x +
        24 * thetaCuspMorseScale n x /
          (thetaCuspMorseScale n x - 3 / 2) ^ (2 : ℕ) +
        216 * thetaCuspMorseScale n x /
          (thetaCuspMorseScale n x - 3 / 2) ^ (3 : ℕ) +
        324 * thetaCuspMorseScale n x /
          (thetaCuspMorseScale n x - 3 / 2) ^ (4 : ℕ) := by
  have hweight := thetaCuspBornWittenWeight_pos hn hx
  rw [thetaCuspBornWittenWeight_eq] at hweight
  unfold thetaCuspBornWittenLogFourthDerivative
  rw [thetaCuspBornWittenWeight_eq]
  field_simp [hweight.ne']; ring

theorem thetaCuspLikelihoodScaleFacts
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    let A := thetaCuspLogConcavityScale x
    let d := (n : ℝ) ^ (2 : ℕ) - 1
    let z := A * d
    let T := A * (n : ℝ) ^ (2 : ℕ)
    3 < A ∧ 3 ≤ d ∧ 9 < z ∧ A < T := by
  dsimp
  have hA := thetaCuspLogConcavityScale_gt_three hx
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (3 : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) - 1 := by nlinarith
  have hz : 9 < thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1) := by
    calc
      9 < thetaCuspLogConcavityScale x * 3 := by nlinarith
      _ ≤ thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1) :=
        mul_le_mul_of_nonneg_left hd (thetaCuspLogConcavityScale_pos x).le
  have hT : thetaCuspLogConcavityScale x <
      thetaCuspLogConcavityScale x * (n : ℝ) ^ (2 : ℕ) := by
    have hApos := thetaCuspLogConcavityScale_pos x
    nlinarith [mul_lt_mul_of_pos_left (by nlinarith : (1 : ℝ) < (n : ℝ) ^ (2 : ℕ)) hApos]
  exact ⟨hA, hd, hz, hT⟩

theorem thetaCuspAtomLikelihoodLogJetZero_bounds
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x) :
    -(20 / 9 : ℝ) *
        (thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)) <
        thetaCuspAtomLikelihoodLogJetZero n x ∧
      thetaCuspAtomLikelihoodLogJetZero n x <
        -2 * (thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)) := by
  let A := thetaCuspLogConcavityScale x
  let d := (n : ℝ) ^ (2 : ℕ) - 1
  let z := A * d
  let T := A * (n : ℝ) ^ (2 : ℕ)
  have hfacts := thetaCuspLikelihoodScaleFacts hn hx.le
  dsimp only at hfacts
  rcases hfacts with ⟨hA, hd, hz, hAT⟩
  have hnpos : 0 < n := by omega
  have hdiff := thetaCuspBornWittenSuperpotential_sub_eq_scaleDifference_mul
    (m := 1) (n := n) (by norm_num) hnpos hx.le
  rw [thetaCuspMorseScale_eq_logConcavityScale_mul_sq,
    thetaCuspMorseScale_eq_logConcavityScale_mul_sq] at hdiff
  norm_num at hdiff
  have hscale : A * (n : ℝ) ^ (2 : ℕ) - A = z := by
    dsimp [A, z]
    ring
  rw [hscale] at hdiff
  have hw1 : (3 / 2 : ℝ) < thetaCuspBornWittenWeight 1 x :=
    three_halves_lt_thetaCuspBornWittenWeight (n := 1) (by norm_num) hx.le
  have hwn : (9 : ℝ) < thetaCuspBornWittenWeight n x := by
    rw [thetaCuspBornWittenWeight_eq,
      thetaCuspMorseScale_eq_logConcavityScale_mul_sq]
    nlinarith
  have hprod : (27 / 2 : ℝ) <
      thetaCuspBornWittenWeight n x * thetaCuspBornWittenWeight 1 x := by
    have hleft : (9 : ℝ) * (3 / 2) <
        thetaCuspBornWittenWeight n x * (3 / 2) :=
      mul_lt_mul_of_pos_right hwn (by norm_num)
    have hright : thetaCuspBornWittenWeight n x * (3 / 2) <
        thetaCuspBornWittenWeight n x * thetaCuspBornWittenWeight 1 x :=
      mul_lt_mul_of_pos_left hw1 (by linarith)
    nlinarith
  have hfrac : (3 / 2 : ℝ) /
      (thetaCuspBornWittenWeight n x * thetaCuspBornWittenWeight 1 x) < 1 / 9 := by
    exact (div_lt_iff₀ (by linarith : 0 < thetaCuspBornWittenWeight n x *
      thetaCuspBornWittenWeight 1 x)).2 (by nlinarith)
  have hfactor0 : 1 < 1 + (3 / 2 : ℝ) /
      (thetaCuspBornWittenWeight n x * thetaCuspBornWittenWeight 1 x) := by
    have := div_pos (by norm_num : (0 : ℝ) < 3 / 2)
      (by linarith : 0 < thetaCuspBornWittenWeight n x *
        thetaCuspBornWittenWeight 1 x)
    linarith
  dsimp [thetaCuspAtomLikelihoodLogJetZero, z, d, A]
  rw [hdiff]
  constructor <;> nlinarith

theorem thetaCuspAtomLikelihoodLogJetOne_bounds
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x) :
    -4 * (thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)) <
        thetaCuspAtomLikelihoodLogJetOne n x ∧
      thetaCuspAtomLikelihoodLogJetOne n x <
        -4 * (thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)) + 8 := by
  let A := thetaCuspLogConcavityScale x
  let T := A * (n : ℝ) ^ (2 : ℕ)
  let z := A * ((n : ℝ) ^ (2 : ℕ) - 1)
  have hfacts := thetaCuspLikelihoodScaleFacts hn hx.le
  dsimp only at hfacts
  rcases hfacts with ⟨hA, _hd, _hz, hAT⟩
  have hnpos : 0 < n := by omega
  have hprofileN := thetaCuspBornWittenLogCurvature_eq_scaleProfile hnpos hx.le
  have hprofile1 := thetaCuspBornWittenLogCurvature_eq_scaleProfile
    (n := 1) (by norm_num) hx.le
  rw [thetaCuspMorseScale_eq_logConcavityScale_mul_sq] at hprofileN hprofile1
  norm_num at hprofile1
  have hanti := scale_div_sub_sq_strictAnti hA hAT
  have hAupper := scale_div_sub_sq_lt_four_thirds hA
  have hTpos : 0 < T / (T - 3 / 2) ^ (2 : ℕ) := by
    apply div_pos
    · exact lt_trans (by linarith) hAT
    · exact sq_pos_of_pos (by linarith)
  dsimp [T, A] at hTpos
  have hvalue : thetaCuspAtomLikelihoodLogJetOne n x =
      -4 * z + 6 * (A / (A - 3 / 2) ^ (2 : ℕ) - T / (T - 3 / 2) ^ (2 : ℕ)) := by
    unfold thetaCuspAtomLikelihoodLogJetOne
    rw [hprofileN, hprofile1]
    dsimp [z, T, A]
    ring
  rw [hvalue]
  dsimp [z, T, A]
  constructor <;> nlinarith

theorem thetaCuspAtomLikelihoodLogJetTwo_bounds
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x) :
    -8 * (thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)) - 48 <
        thetaCuspAtomLikelihoodLogJetTwo n x ∧
      thetaCuspAtomLikelihoodLogJetTwo n x <
        -8 * (thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)) := by
  let A := thetaCuspLogConcavityScale x
  let T := A * (n : ℝ) ^ (2 : ℕ)
  let z := A * ((n : ℝ) ^ (2 : ℕ) - 1)
  have hfacts := thetaCuspLikelihoodScaleFacts hn hx.le
  dsimp only at hfacts
  rcases hfacts with ⟨hA, _hd, _hz, hAT⟩
  have hnpos : 0 < n := by omega
  have hprofileN := thetaCuspBornWittenLogThirdDerivative_eq_scaleProfile hnpos hx.le
  have hprofile1 := thetaCuspBornWittenLogThirdDerivative_eq_scaleProfile
    (n := 1) (by norm_num) hx.le
  rw [thetaCuspMorseScale_eq_logConcavityScale_mul_sq] at hprofileN hprofile1
  norm_num at hprofile1
  have hanti2 := scale_div_sub_sq_strictAnti hA hAT
  have hanti3 := scale_div_sub_cube_strictAnti hA hAT
  have hA2 := scale_div_sub_sq_lt_four_thirds hA
  have hA3 := scale_div_sub_cube_lt_eight_ninths hA
  have hT2 : 0 < T / (T - 3 / 2) ^ (2 : ℕ) := by
    apply div_pos
    · exact lt_trans (by linarith) hAT
    · exact sq_pos_of_pos (by linarith)
  have hT3 : 0 < T / (T - 3 / 2) ^ (3 : ℕ) := by
    apply div_pos
    · exact lt_trans (by linarith) hAT
    · exact pow_pos (by linarith) 3
  dsimp [T, A] at hT2 hT3
  have hvalue : thetaCuspAtomLikelihoodLogJetTwo n x =
      -8 * z +
        12 * (T / (T - 3 / 2) ^ (2 : ℕ) - A / (A - 3 / 2) ^ (2 : ℕ)) +
        36 * (T / (T - 3 / 2) ^ (3 : ℕ) - A / (A - 3 / 2) ^ (3 : ℕ)) := by
    unfold thetaCuspAtomLikelihoodLogJetTwo
    rw [hprofileN, hprofile1]
    dsimp [z, T, A]
    ring
  rw [hvalue]
  dsimp [z, T, A]
  constructor <;> nlinarith

theorem thetaCuspAtomLikelihoodLogJetThree_lower
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x) :
    -16 * (thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)) <
      thetaCuspAtomLikelihoodLogJetThree n x := by
  let A := thetaCuspLogConcavityScale x
  let T := A * (n : ℝ) ^ (2 : ℕ)
  let z := A * ((n : ℝ) ^ (2 : ℕ) - 1)
  have hfacts := thetaCuspLikelihoodScaleFacts hn hx.le
  dsimp only at hfacts
  rcases hfacts with ⟨hA, _hd, _hz, hAT⟩
  have hnpos : 0 < n := by omega
  have hprofileN := thetaCuspBornWittenLogFourthDerivative_eq_scaleProfile hnpos hx.le
  have hprofile1 := thetaCuspBornWittenLogFourthDerivative_eq_scaleProfile
    (n := 1) (by norm_num) hx.le
  rw [thetaCuspMorseScale_eq_logConcavityScale_mul_sq] at hprofileN hprofile1
  norm_num at hprofile1
  have hanti2 := scale_div_sub_sq_strictAnti hA hAT
  have hanti3 := scale_div_sub_cube_strictAnti hA hAT
  have hanti4 := scale_div_sub_four_strictAnti hA hAT
  have hvalue : thetaCuspAtomLikelihoodLogJetThree n x =
      -16 * z +
        24 * (A / (A - 3 / 2) ^ (2 : ℕ) - T / (T - 3 / 2) ^ (2 : ℕ)) +
        216 * (A / (A - 3 / 2) ^ (3 : ℕ) - T / (T - 3 / 2) ^ (3 : ℕ)) +
        324 * (A / (A - 3 / 2) ^ (4 : ℕ) - T / (T - 3 / 2) ^ (4 : ℕ)) := by
    unfold thetaCuspAtomLikelihoodLogJetThree
    rw [hprofileN, hprofile1]
    dsimp [z, T, A]
    ring
  rw [hvalue]
  dsimp [z, T, A]
  nlinarith

/-- The fourth logarithmic ratio jet has a linear Gaussian-scale envelope.  The exact lower
bound above is what proves positivity; this symmetric envelope supplies a summable majorant for
termwise differentiation of the complete higher-atom mixture. -/
theorem thetaCuspAtomLikelihoodLogJetThree_abs_le
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x) :
    |thetaCuspAtomLikelihoodLogJetThree n x| ≤
      32 * (thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)) := by
  let A := thetaCuspLogConcavityScale x
  let T := A * (n : ℝ) ^ (2 : ℕ)
  let z := A * ((n : ℝ) ^ (2 : ℕ) - 1)
  have hfacts := thetaCuspLikelihoodScaleFacts hn hx.le
  dsimp only at hfacts
  rcases hfacts with ⟨hA, _hd, hz, hAT⟩
  have hnpos : 0 < n := by omega
  have hprofileN := thetaCuspBornWittenLogFourthDerivative_eq_scaleProfile hnpos hx.le
  have hprofile1 := thetaCuspBornWittenLogFourthDerivative_eq_scaleProfile
    (n := 1) (by norm_num) hx.le
  rw [thetaCuspMorseScale_eq_logConcavityScale_mul_sq] at hprofileN hprofile1
  norm_num at hprofile1
  have hanti2 := scale_div_sub_sq_strictAnti hA hAT
  have hanti3 := scale_div_sub_cube_strictAnti hA hAT
  have hanti4 := scale_div_sub_four_strictAnti hA hAT
  have hA2 := scale_div_sub_sq_lt_four_thirds hA
  have hA3 := scale_div_sub_cube_lt_eight_ninths hA
  have hA4 := scale_div_sub_four_lt_sixteen_twentysevenths hA
  have hT2 : 0 < T / (T - 3 / 2) ^ (2 : ℕ) := by
    exact div_pos (lt_trans (by linarith) hAT) (sq_pos_of_pos (by linarith))
  have hT3 : 0 < T / (T - 3 / 2) ^ (3 : ℕ) := by
    exact div_pos (lt_trans (by linarith) hAT) (pow_pos (by linarith) 3)
  have hT4 : 0 < T / (T - 3 / 2) ^ (4 : ℕ) := by
    exact div_pos (lt_trans (by linarith) hAT) (pow_pos (by linarith) 4)
  have hvalue : thetaCuspAtomLikelihoodLogJetThree n x =
      -16 * z +
        24 * (A / (A - 3 / 2) ^ (2 : ℕ) - T / (T - 3 / 2) ^ (2 : ℕ)) +
        216 * (A / (A - 3 / 2) ^ (3 : ℕ) - T / (T - 3 / 2) ^ (3 : ℕ)) +
        324 * (A / (A - 3 / 2) ^ (4 : ℕ) - T / (T - 3 / 2) ^ (4 : ℕ)) := by
    unfold thetaCuspAtomLikelihoodLogJetThree
    rw [hprofileN, hprofile1]
    dsimp [z, T, A]
    ring
  rw [abs_le]
  rw [hvalue]
  dsimp [z, T, A] at hz hanti2 hanti3 hanti4 hA2 hA3 hA4 hT2 hT3 hT4 ⊢
  constructor <;> nlinarith

theorem thetaCuspAtomLikelihoodRatioJetOne_abs_le
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x) :
    |thetaCuspAtomLikelihoodRatioJetOne n x| ≤
      (20 / 9 : ℝ) *
        (thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)) *
          thetaCuspAtomLikelihoodRatio n x := by
  let z := thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)
  have hq := thetaCuspAtomLikelihoodLogJetZero_bounds hn hx
  have hr := thetaCuspAtomLikelihoodRatio_pos (by omega : 0 < n) hx
  have hz := (thetaCuspLikelihoodScaleFacts hn hx.le).2.2.1
  dsimp [thetaCuspAtomLikelihoodRatioJetOne, z]
  rw [abs_mul, abs_of_pos hr]
  have hqneg : thetaCuspAtomLikelihoodLogJetZero n x < 0 := by linarith
  rw [abs_of_neg hqneg]
  apply mul_le_mul_of_nonneg_right _ hr.le
  linarith

theorem thetaCuspAtomLikelihoodRatioJetTwo_pos_le
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspAtomLikelihoodRatioJetTwo n x ∧
      thetaCuspAtomLikelihoodRatioJetTwo n x ≤
        (400 / 81 : ℝ) *
            (thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)) ^ (2 : ℕ) *
          thetaCuspAtomLikelihoodRatio n x := by
  let z := thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)
  let p := -thetaCuspAtomLikelihoodLogJetZero n x
  have hq := thetaCuspAtomLikelihoodLogJetZero_bounds hn hx
  have hq1 := thetaCuspAtomLikelihoodLogJetOne_bounds hn hx
  have hr := thetaCuspAtomLikelihoodRatio_pos (by omega : 0 < n) hx
  have hz := (thetaCuspLikelihoodScaleFacts hn hx.le).2.2.1
  have hpLower : 2 * z < p := by dsimp [p]; linarith
  have hpUpper : p < (20 / 9 : ℝ) * z := by dsimp [p]; linarith
  have hcoeffPos : 0 < p ^ (2 : ℕ) + thetaCuspAtomLikelihoodLogJetOne n x := by
    have hpsq : (2 * z) ^ (2 : ℕ) < p ^ (2 : ℕ) := by nlinarith
    nlinarith
  have hcoeffUpper :
      p ^ (2 : ℕ) + thetaCuspAtomLikelihoodLogJetOne n x ≤ (400 / 81 : ℝ) * z ^ (2 : ℕ) := by
    have hpsq : p ^ (2 : ℕ) < ((20 / 9 : ℝ) * z) ^ (2 : ℕ) := by nlinarith
    have hq1neg : thetaCuspAtomLikelihoodLogJetOne n x < 0 := by nlinarith
    nlinarith
  dsimp [thetaCuspAtomLikelihoodRatioJetTwo, p]
  rw [show thetaCuspAtomLikelihoodLogJetZero n x ^ (2 : ℕ) = p ^ (2 : ℕ) by dsimp [p]; ring]
  exact ⟨mul_pos hcoeffPos hr,
    mul_le_mul_of_nonneg_right hcoeffUpper hr.le⟩

theorem thetaCuspAtomLikelihoodRatioJetThree_neg_abs_le
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x) :
    thetaCuspAtomLikelihoodRatioJetThree n x < 0 ∧
      |thetaCuspAtomLikelihoodRatioJetThree n x| ≤
        12 * (thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)) ^ (3 : ℕ) *
          thetaCuspAtomLikelihoodRatio n x := by
  let z := thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)
  let p := -thetaCuspAtomLikelihoodLogJetZero n x
  let alpha := -thetaCuspAtomLikelihoodLogJetOne n x
  let beta := -thetaCuspAtomLikelihoodLogJetTwo n x
  have hq := thetaCuspAtomLikelihoodLogJetZero_bounds hn hx
  have hq1 := thetaCuspAtomLikelihoodLogJetOne_bounds hn hx
  have hq2 := thetaCuspAtomLikelihoodLogJetTwo_bounds hn hx
  have hr := thetaCuspAtomLikelihoodRatio_pos (by omega : 0 < n) hx
  have hz := (thetaCuspLikelihoodScaleFacts hn hx.le).2.2.1
  have hpLower : 2 * z < p := by dsimp [p]; linarith
  have hpUpper : p < (20 / 9 : ℝ) * z := by dsimp [p]; linarith
  have ha0 : 0 < alpha := by dsimp [alpha]; nlinarith
  have haUpper : alpha < 4 * z := by dsimp [alpha]; linarith
  have hbLower : 8 * z < beta := by dsimp [beta]; linarith
  have hbUpper : beta < 8 * z + 48 := by dsimp [beta]; linarith
  have hp0 : 0 < p := by nlinarith
  have hcoeffNeg : -p ^ (3 : ℕ) + 3 * p * alpha - beta < 0 := by
    have hp2 : p ^ (2 : ℕ) > 3 * alpha := by
      have : 4 * z ^ (2 : ℕ) > 12 * z := by nlinarith
      nlinarith
    nlinarith [mul_pos hp0 (sub_pos.mpr hp2)]
  have hcoeffLower : -(12 * z ^ (3 : ℕ)) ≤ -p ^ (3 : ℕ) + 3 * p * alpha - beta := by
    have hp3 : p ^ (3 : ℕ) < (20 / 9 : ℝ) ^ (3 : ℕ) * z ^ (3 : ℕ) := by
      have hp3' := pow_lt_pow_left₀ hpUpper hp0.le (by norm_num : (3 : ℕ) ≠ 0)
      convert hp3' using 1 <;> first | rfl | ring
    have hcubic : 8 * z + 48 < (1 / 6 : ℝ) * z ^ (3 : ℕ) := by
      let y := z - 9
      have hy : 0 < y := by dsimp [y, z]; linarith
      apply sub_pos.mp
      rw [show (1 / 6 : ℝ) * z ^ (3 : ℕ) - (8 * z + 48) =
          (1 / 6) * y ^ (3 : ℕ) + (9 / 2) * y ^ (2 : ℕ) + (65 / 2) * y + 3 / 2 by
        dsimp [y]; ring]
      positivity
    have hb : beta < (1 / 6 : ℝ) * z ^ (3 : ℕ) := lt_trans hbUpper hcubic
    nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ (3 : ℝ))
      (by positivity : 0 ≤ p)) ha0.le]
  dsimp [thetaCuspAtomLikelihoodRatioJetThree, p, alpha, beta]
  rw [show thetaCuspAtomLikelihoodLogJetZero n x ^ (3 : ℕ) +
        3 * thetaCuspAtomLikelihoodLogJetZero n x *
          thetaCuspAtomLikelihoodLogJetOne n x +
        thetaCuspAtomLikelihoodLogJetTwo n x =
      -p ^ (3 : ℕ) + 3 * p * alpha - beta by dsimp [p, alpha, beta]; ring]
  constructor
  · exact mul_neg_of_neg_of_pos hcoeffNeg hr
  · rw [abs_mul, abs_of_pos hr, abs_of_neg hcoeffNeg]
    exact mul_le_mul_of_nonneg_right (by linarith) hr.le

theorem thetaCuspAtomLikelihoodRatioJetFour_pos
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspAtomLikelihoodRatioJetFour n x := by
  let z := thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)
  let p := -thetaCuspAtomLikelihoodLogJetZero n x
  let alpha := -thetaCuspAtomLikelihoodLogJetOne n x
  let beta := -thetaCuspAtomLikelihoodLogJetTwo n x
  have hq := thetaCuspAtomLikelihoodLogJetZero_bounds hn hx
  have hq1 := thetaCuspAtomLikelihoodLogJetOne_bounds hn hx
  have hq2 := thetaCuspAtomLikelihoodLogJetTwo_bounds hn hx
  have hq3 := thetaCuspAtomLikelihoodLogJetThree_lower hn hx
  have hr := thetaCuspAtomLikelihoodRatio_pos (by omega : 0 < n) hx
  have hz := (thetaCuspLikelihoodScaleFacts hn hx.le).2.2.1
  have hpLower : 2 * z < p := by dsimp [p]; linarith
  have ha0 : 0 < alpha := by dsimp [alpha]; nlinarith
  have haUpper : alpha < 4 * z := by dsimp [alpha]; linarith
  have hb0 : 0 < beta := by dsimp [beta]; nlinarith
  have hp0 : 0 < p := by nlinarith
  have hcore :
      0 < p ^ (4 : ℕ) - 6 * p ^ (2 : ℕ) * alpha + 3 * alpha ^ (2 : ℕ) +
          4 * p * beta + thetaCuspAtomLikelihoodLogJetThree n x := by
    have hp2 : 4 * z ^ (2 : ℕ) < p ^ (2 : ℕ) := by nlinarith
    have hbracket : 4 * z * (z - 6) < p ^ (2 : ℕ) - 6 * alpha := by nlinarith
    have hprod : 16 * z ^ (3 : ℕ) * (z - 6) < p ^ (2 : ℕ) * (p ^ (2 : ℕ) - 6 * alpha) := by
      have hleftPos : 0 < 4 * z * (z - 6) := by
        exact mul_pos (mul_pos (by norm_num) (by nlinarith)) (by nlinarith)
      calc
        16 * z ^ (3 : ℕ) * (z - 6) =
            (4 * z ^ (2 : ℕ)) * (4 * z * (z - 6)) := by ring
        _ < p ^ (2 : ℕ) * (4 * z * (z - 6)) :=
          mul_lt_mul_of_pos_right hp2 hleftPos
        _ < p ^ (2 : ℕ) * (p ^ (2 : ℕ) - 6 * alpha) :=
          mul_lt_mul_of_pos_left hbracket (sq_pos_of_pos hp0)
    have hbase : 0 < 16 * z ^ (3 : ℕ) * (z - 6) - 16 * z := by
      have hinner : 1 < z ^ (2 : ℕ) * (z - 6) := by
        have hzsq : 1 < z ^ (2 : ℕ) := by nlinarith
        have hz6 : 3 < z - 6 := by nlinarith
        nlinarith [mul_lt_mul_of_pos_left hz6 (sq_pos_of_pos (by nlinarith : 0 < z))]
      rw [show 16 * z ^ (3 : ℕ) * (z - 6) - 16 * z =
          16 * z * (z ^ (2 : ℕ) * (z - 6) - 1) by ring]
      exact mul_pos (mul_pos (by norm_num) (by nlinarith)) (sub_pos.mpr hinner)
    nlinarith [mul_pos (by norm_num : (0 : ℝ) < 3) (sq_pos_of_pos ha0),
      mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hp0) hb0]
  unfold thetaCuspAtomLikelihoodRatioJetFour
  rw [show thetaCuspAtomLikelihoodLogJetZero n x ^ (4 : ℕ) +
        6 * thetaCuspAtomLikelihoodLogJetZero n x ^ (2 : ℕ) *
          thetaCuspAtomLikelihoodLogJetOne n x +
        3 * thetaCuspAtomLikelihoodLogJetOne n x ^ (2 : ℕ) +
        4 * thetaCuspAtomLikelihoodLogJetZero n x *
          thetaCuspAtomLikelihoodLogJetTwo n x +
        thetaCuspAtomLikelihoodLogJetThree n x =
      p ^ (4 : ℕ) - 6 * p ^ (2 : ℕ) * alpha + 3 * alpha ^ (2 : ℕ) + 4 * p * beta +
        thetaCuspAtomLikelihoodLogJetThree n x by
    dsimp [p, alpha, beta]; ring]
  exact mul_pos hcore hr

/-- A fourth-jet majorant for the atom likelihood ratios.  Its deliberately round constant is
used only to justify differentiation of the infinite mixture; the strict sign is retained by
`thetaCuspAtomLikelihoodRatioJetFour_pos`. -/
theorem thetaCuspAtomLikelihoodRatioJetFour_abs_le
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x) :
    |thetaCuspAtomLikelihoodRatioJetFour n x| ≤
      600 * (thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)) ^ (4 : ℕ) *
        thetaCuspAtomLikelihoodRatio n x := by
  let z := thetaCuspLogConcavityScale x * ((n : ℝ) ^ (2 : ℕ) - 1)
  let p := -thetaCuspAtomLikelihoodLogJetZero n x
  let alpha := -thetaCuspAtomLikelihoodLogJetOne n x
  let beta := -thetaCuspAtomLikelihoodLogJetTwo n x
  have hq := thetaCuspAtomLikelihoodLogJetZero_bounds hn hx
  have hq1 := thetaCuspAtomLikelihoodLogJetOne_bounds hn hx
  have hq2 := thetaCuspAtomLikelihoodLogJetTwo_bounds hn hx
  have hq3 := thetaCuspAtomLikelihoodLogJetThree_abs_le hn hx
  have hr := thetaCuspAtomLikelihoodRatio_pos (by omega : 0 < n) hx
  have hz := (thetaCuspLikelihoodScaleFacts hn hx.le).2.2.1
  have hp0 : 0 ≤ p := by dsimp [p, z]; linarith
  have hp : p ≤ 3 * z := by dsimp [p, z]; linarith
  have ha0 : 0 ≤ alpha := by dsimp [alpha, z]; linarith
  have ha : alpha ≤ 4 * z := by dsimp [alpha, z]; linarith
  have hb0 : 0 ≤ beta := by dsimp [beta, z]; linarith
  have hb : beta ≤ 14 * z := by dsimp [beta, z]; linarith
  have hp4 : p ^ (4 : ℕ) ≤ 81 * z ^ (4 : ℕ) := by
    have := pow_le_pow_left₀ hp0 hp 4
    nlinarith
  have hp2 : p ^ (2 : ℕ) ≤ 9 * z ^ (2 : ℕ) := by
    have := pow_le_pow_left₀ hp0 hp 2
    nlinarith
  have hpa : 6 * p ^ (2 : ℕ) * alpha ≤ 216 * z ^ (3 : ℕ) := by
    calc
      6 * p ^ (2 : ℕ) * alpha ≤ 6 * (9 * z ^ (2 : ℕ)) * (4 * z) := by gcongr
      _ = 216 * z ^ (3 : ℕ) := by ring
  have ha2 : 3 * alpha ^ (2 : ℕ) ≤ 48 * z ^ (2 : ℕ) := by
    have halpha := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hpb : 4 * p * beta ≤ 168 * z ^ (2 : ℕ) := by
    calc
      4 * p * beta ≤ 4 * (3 * z) * (14 * z) := by gcongr
      _ = 168 * z ^ (2 : ℕ) := by ring
  have hz1 : z ≤ z ^ (4 : ℕ) := by
    have hzpos : 0 ≤ z := by linarith
    have hzsq : z ≤ z ^ (2 : ℕ) := by nlinarith
    have hzsq4 : z ^ (2 : ℕ) ≤ z ^ (4 : ℕ) := by nlinarith
    exact hzsq.trans hzsq4
  have hz2 : z ^ (2 : ℕ) ≤ z ^ (4 : ℕ) := by nlinarith
  have hz3 : z ^ (3 : ℕ) ≤ z ^ (4 : ℕ) := by
    calc
      z ^ (3 : ℕ) = z ^ (3 : ℕ) * 1 := by ring
      _ ≤ z ^ (3 : ℕ) * z := by gcongr; linarith
      _ = z ^ (4 : ℕ) := by ring
  have hcoeff :
      |p ^ (4 : ℕ) - 6 * p ^ (2 : ℕ) * alpha + 3 * alpha ^ (2 : ℕ) + 4 * p * beta +
          thetaCuspAtomLikelihoodLogJetThree n x| ≤ 600 * z ^ (4 : ℕ) := by
    rw [abs_le]
    have hq3' :
        -32 * z ≤ thetaCuspAtomLikelihoodLogJetThree n x ∧
          thetaCuspAtomLikelihoodLogJetThree n x ≤ 32 * z := by
      have hq3bounds := (abs_le.mp hq3)
      dsimp [z] at hq3bounds ⊢
      constructor <;> linarith
    constructor <;> nlinarith
  unfold thetaCuspAtomLikelihoodRatioJetFour
  rw [show thetaCuspAtomLikelihoodLogJetZero n x ^ (4 : ℕ) +
        6 * thetaCuspAtomLikelihoodLogJetZero n x ^ (2 : ℕ) *
            thetaCuspAtomLikelihoodLogJetOne n x +
          3 * thetaCuspAtomLikelihoodLogJetOne n x ^ (2 : ℕ) +
        4 * thetaCuspAtomLikelihoodLogJetZero n x *
            thetaCuspAtomLikelihoodLogJetTwo n x +
          thetaCuspAtomLikelihoodLogJetThree n x =
      p ^ (4 : ℕ) - 6 * p ^ (2 : ℕ) * alpha + 3 * alpha ^ (2 : ℕ) + 4 * p * beta +
        thetaCuspAtomLikelihoodLogJetThree n x by
      dsimp [p, alpha, beta]; ring]
  rw [abs_mul, abs_of_pos hr]
  exact mul_le_mul_of_nonneg_right hcoeff hr.le

end

end RHTower
