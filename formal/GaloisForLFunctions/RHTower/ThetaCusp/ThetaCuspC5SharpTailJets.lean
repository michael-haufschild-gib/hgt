import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5SharpTailMeasures
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthLogJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodEighthBellHigherEvenAbsorption

/-!
# Sharp second-atom asymptotics of the higher-likelihood log-partition jets

For `A(x) ≥ 6` every log-partition jet `J_k(x)` (`k = 2, …, 7`) equals its explicit second-atom
main part `e^{-3A} N_k(A)/(2A-3)^{k+1}` up to an error `K_k A^k ε(x)² + L_k A^k e^{-8(A-π)}/399`.
The main parts are monotone in absolute value on `[6, ∞)`.
-/

namespace RHTower

open Set Filter Topology

noncomputable section

theorem mul_le_mul_nn {a b a' b' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (haa : a ≤ a') (hbb : b ≤ b') :
    a * b ≤ a' * b' :=
  mul_le_mul haa hbb hb (ha.trans haa)

theorem secondAtomMomentProfile_eq_A (j : ℕ) (A : ℝ) :
    secondAtomMomentProfile j (A - 3 / 2) = Real.exp (-3 * A) * secondAtomProfile j (A - 3 / 2) := by
  unfold secondAtomMomentProfile
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Derivative of an explicit polynomial of degree at most sixteen. -/
theorem hasDerivAt_poly16 (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ B : ℝ) :
    HasDerivAt (fun x : ℝ => a₀ + a₁ * x + a₂ * x ^ (2 : ℕ) + a₃ * x ^ (3 : ℕ) + a₄ * x ^ (4 : ℕ) + a₅ * x ^ (5 : ℕ) +
        a₆ * x ^ (6 : ℕ) + a₇ * x ^ (7 : ℕ) + a₈ * x ^ (8 : ℕ) + a₉ * x ^ (9 : ℕ) + a₁₀ * x ^ (10 : ℕ) + a₁₁ * x ^ (11 : ℕ) +
        a₁₂ * x ^ (12 : ℕ) + a₁₃ * x ^ (13 : ℕ) + a₁₄ * x ^ (14 : ℕ) + a₁₅ * x ^ (15 : ℕ) + a₁₆ * x ^ (16 : ℕ))
      (a₁ + 2 * a₂ * B + 3 * a₃ * B ^ (2 : ℕ) + 4 * a₄ * B ^ (3 : ℕ) + 5 * a₅ * B ^ (4 : ℕ) + 6 * a₆ * B ^ (5 : ℕ) +
        7 * a₇ * B ^ (6 : ℕ) + 8 * a₈ * B ^ (7 : ℕ) + 9 * a₉ * B ^ (8 : ℕ) + 10 * a₁₀ * B ^ (9 : ℕ) + 11 * a₁₁ * B ^ (10 : ℕ) +
        12 * a₁₂ * B ^ (11 : ℕ) + 13 * a₁₃ * B ^ (12 : ℕ) + 14 * a₁₄ * B ^ (13 : ℕ) + 15 * a₁₅ * B ^ (14 : ℕ) +
        16 * a₁₆ * B ^ (15 : ℕ)) B := by
  have h := ((((((((((((((((hasDerivAt_const B a₀).add ((hasDerivAt_id B).const_mul a₁)).add
    ((hasDerivAt_pow 2 B).const_mul a₂)).add ((hasDerivAt_pow 3 B).const_mul a₃)).add
    ((hasDerivAt_pow 4 B).const_mul a₄)).add ((hasDerivAt_pow 5 B).const_mul a₅)).add
    ((hasDerivAt_pow 6 B).const_mul a₆)).add ((hasDerivAt_pow 7 B).const_mul a₇)).add
    ((hasDerivAt_pow 8 B).const_mul a₈)).add ((hasDerivAt_pow 9 B).const_mul a₉)).add
    ((hasDerivAt_pow 10 B).const_mul a₁₀)).add ((hasDerivAt_pow 11 B).const_mul a₁₁)).add
    ((hasDerivAt_pow 12 B).const_mul a₁₂)).add ((hasDerivAt_pow 13 B).const_mul a₁₃)).add
    ((hasDerivAt_pow 14 B).const_mul a₁₄)).add ((hasDerivAt_pow 15 B).const_mul a₁₅)).add
    ((hasDerivAt_pow 16 B).const_mul a₁₆)
  refine h.congr_deriv ?_
  push_cast
  ring

/-! ## Main parts, identities, derivatives, monotonicity -/

/-- Numerator of the main second-atom part of the `2`-th log-partition jet. -/
def sharpJetMainNumerator2 (A : ℝ) : ℝ := 2160 * A + (-13680) * A ^ (2 : ℕ) + 24192 * A ^ (3 : ℕ) + (-17088) * A ^ (4 : ℕ) + 4608 * A ^ (5 : ℕ)

/-- Derivative numerator of the main `2`-th jet. -/
def sharpJetMainDerivNumerator2 (A : ℝ) : ℝ := (-6480) + 92880 * A + (-326448) * A ^ (2 : ℕ) + 504864 * A ^ (3 : ℕ) + (-402240) * A ^ (4 : ℕ) + 162432 * A ^ (5 : ℕ) + (-27648) * A ^ (6 : ℕ)

def sharpJetMainDerivShiftedAbs2 (s : ℝ) : ℝ := 450327600 + 534220272 * s + 264746736 * s ^ (2 : ℕ) + 70112736 * s ^ (3 : ℕ) + 10459200 * s ^ (4 : ℕ) + 832896 * s ^ (5 : ℕ) + 27648 * s ^ (6 : ℕ)
def sharpJetMainShiftedAbs2 (s : ℝ) : ℝ := 18431712 + 17546544 * s + 6684048 * s ^ (2 : ℕ) + 1272960 * s ^ (3 : ℕ) + 121152 * s ^ (4 : ℕ) + 4608 * s ^ (5 : ℕ)

/-- The main second-atom part of the `2`-th jet. -/
def sharpJetMain2 (A : ℝ) : ℝ :=
  Real.exp (-3 * A) * (sharpJetMainNumerator2 A / (2 * A - 3) ^ (3 : ℕ))

theorem sharpJet_identity_2 (A : ℝ) (hA : 3 / 2 < A) :
    (4) * A ^ (2 : ℕ) * secondAtomMomentProfile 2 (A - 3 / 2) + (-4) * A * secondAtomMomentProfile 1 (A - 3 / 2) =
      Real.exp (-3 * A) * (sharpJetMainNumerator2 A / (2 * A - 3) ^ (3 : ℕ)) := by
  have hne : A - 3 / 2 ≠ 0 := by intro h; linarith
  have hne2 : 2 * A - 3 ≠ 0 := by intro h; linarith
  simp only [secondAtomMomentProfile_eq_A, secondAtomProfile, secondAtomNumerator2, secondAtomNumerator1, sharpJetMainNumerator2]
  field_simp
  ring

theorem hasDerivAt_sharpJetMainNumerator2 (A : ℝ) :
    HasDerivAt sharpJetMainNumerator2 (2160 + (-27360) * A + 72576 * A ^ (2 : ℕ) + (-68352) * A ^ (3 : ℕ) + 23040 * A ^ (4 : ℕ)) A := by
  have h := hasDerivAt_poly16 0 2160 (-13680) 24192 (-17088) 4608 0 0 0 0 0 0 0 0 0 0 0 A
  unfold sharpJetMainNumerator2
  convert h using 1 <;> first | (funext x; ring) | ring

theorem hasDerivAt_sharpJetMain2 {A : ℝ} (hA : 3 / 2 < A) :
    HasDerivAt sharpJetMain2
      (Real.exp (-3 * A) * (sharpJetMainDerivNumerator2 A / (2 * A - 3) ^ (4 : ℕ))) A := by
  unfold sharpJetMain2
  have hne : 2 * A - 3 ≠ 0 := by intro h; linarith
  have h1 : HasDerivAt (fun q : ℝ => -3 * q) (-3) A := by
    simpa using (hasDerivAt_id A).const_mul (-3 : ℝ)
  have h2 : HasDerivAt (fun q : ℝ => Real.exp (-3 * q)) (Real.exp (-3 * A) * -3) A :=
    (Real.hasDerivAt_exp _).comp A h1
  have hlin : HasDerivAt (fun q : ℝ => 2 * q - 3) 2 A := by
    simpa using ((hasDerivAt_id A).const_mul (2 : ℝ)).sub_const 3
  have hden : HasDerivAt (fun q : ℝ => (2 * q - 3) ^ (3 : ℕ)) (3 * (2 * A - 3) ^ (2 : ℕ) * 2) A := by
    have := (hasDerivAt_pow 3 (2 * A - 3)).comp A hlin
    simpa [Function.comp_def] using this
  have h3 : HasDerivAt (fun q : ℝ => sharpJetMainNumerator2 q / (2 * q - 3) ^ (3 : ℕ)) _ A :=
    (hasDerivAt_sharpJetMainNumerator2 A).div hden (pow_ne_zero _ hne)
  have h4 := h2.mul h3
  refine HasDerivAt.congr_deriv (f := fun q : ℝ => Real.exp (-3 * q) * (sharpJetMainNumerator2 q / (2 * q - 3) ^ (3 : ℕ))) h4 ?_
  unfold sharpJetMainDerivNumerator2 sharpJetMainNumerator2
  field_simp
  ring

theorem sharpJetMainDerivNumerator2_eq (A : ℝ) :
    sharpJetMainDerivNumerator2 A = -sharpJetMainDerivShiftedAbs2 (A - 6) := by
  unfold sharpJetMainDerivNumerator2 sharpJetMainDerivShiftedAbs2
  ring

theorem sharpJetMainNumerator2_eq (A : ℝ) :
    sharpJetMainNumerator2 A = sharpJetMainShiftedAbs2 (A - 6) := by
  unfold sharpJetMainNumerator2 sharpJetMainShiftedAbs2
  ring

theorem sharpJetMainDerivShiftedAbs2_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ sharpJetMainDerivShiftedAbs2 s := by
  unfold sharpJetMainDerivShiftedAbs2; positivity

theorem sharpJetMainShiftedAbs2_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ sharpJetMainShiftedAbs2 s := by
  unfold sharpJetMainShiftedAbs2; positivity

theorem sharpJetMain2_abs_eq {A : ℝ} (hA : 6 ≤ A) :
    |sharpJetMain2 A| = (1 : ℝ) * sharpJetMain2 A := by
  rw [one_mul]
  unfold sharpJetMain2
  rw [sharpJetMainNumerator2_eq]
  have hS := sharpJetMainShiftedAbs2_nonneg (show 0 ≤ A - 6 by linarith)
  have hden : 0 < (2 * A - 3) ^ (3 : ℕ) := by
    have : 0 < 2 * A - 3 := by linarith
    positivity
  have h0 : 0 ≤ Real.exp (-3 * A) * (sharpJetMainShiftedAbs2 (A - 6) / (2 * A - 3) ^ (3 : ℕ)) := by
    positivity
  exact abs_of_nonneg h0

/-- `|h_2|` is antitone on `[6, ∞)`. -/
theorem sharpJetMain2_abs_le_of_le {A₁ A : ℝ} (h1 : 6 ≤ A₁) (h : A₁ ≤ A) :
    |sharpJetMain2 A| ≤ |sharpJetMain2 A₁| := by
  have hanti : AntitoneOn (fun A => (1 : ℝ) * sharpJetMain2 A) (Ici 6) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 6)
    · intro x hx
      have hx6 : 6 ≤ x := mem_Ici.mp hx
      exact ((hasDerivAt_sharpJetMain2 (show 3 / 2 < x by linarith)).const_mul (1 : ℝ)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx6 : 6 < x := mem_Ioi.mp hx
      exact ((hasDerivAt_sharpJetMain2 (show 3 / 2 < x by linarith)).const_mul (1 : ℝ)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx6 : 6 < x := mem_Ioi.mp hx
      rw [((hasDerivAt_sharpJetMain2 (show 3 / 2 < x by linarith)).const_mul (1 : ℝ)).deriv,
        sharpJetMainDerivNumerator2_eq]
      have hS := sharpJetMainDerivShiftedAbs2_nonneg (show 0 ≤ x - 6 by linarith)
      have hden : 0 < (2 * x - 3) ^ (4 : ℕ) := by
        have : 0 < 2 * x - 3 := by linarith
        positivity
      have h0 : 0 ≤ Real.exp (-3 * x) * (sharpJetMainDerivShiftedAbs2 (x - 6) / (2 * x - 3) ^ (4 : ℕ)) := by
        positivity
      have e : (1 : ℝ) * (Real.exp (-3 * x) * (-sharpJetMainDerivShiftedAbs2 (x - 6) / (2 * x - 3) ^ (4 : ℕ))) =
          -(Real.exp (-3 * x) * (sharpJetMainDerivShiftedAbs2 (x - 6) / (2 * x - 3) ^ (4 : ℕ))) := by ring
      rw [e]
      linarith
  rw [sharpJetMain2_abs_eq (h1.trans h), sharpJetMain2_abs_eq h1]
  exact hanti (mem_Ici.mpr h1) (mem_Ici.mpr (h1.trans h)) h

/-- Numerator of the main second-atom part of the `3`-th log-partition jet. -/
def sharpJetMainNumerator3 (A : ℝ) : ℝ := (-12960) * A + 185760 * A ^ (2 : ℕ) + (-652896) * A ^ (3 : ℕ) + 1009728 * A ^ (4 : ℕ) + (-804480) * A ^ (5 : ℕ) + 324864 * A ^ (6 : ℕ) + (-55296) * A ^ (7 : ℕ)

/-- Derivative numerator of the main `3`-th jet. -/
def sharpJetMainDerivNumerator3 (A : ℝ) : ℝ := 38880 + (-1153440) * A + 6882624 * A ^ (2 : ℕ) + (-17801568) * A ^ (3 : ℕ) + 25072128 * A ^ (4 : ℕ) + (-20755200) * A ^ (5 : ℕ) + 10211328 * A ^ (6 : ℕ) + (-2778624) * A ^ (7 : ℕ) + 331776 * A ^ (8 : ℕ)

def sharpJetMainDerivShiftedAbs3 (s : ℝ) : ℝ := 123335905824 + 197279211744 * s + 138462383232 * s ^ (2 : ℕ) + 55660459680 * s ^ (3 : ℕ) + 14008854528 * s ^ (4 : ℕ) + 2259375360 * s ^ (5 : ℕ) + 227939328 * s ^ (6 : ℕ) + 13146624 * s ^ (7 : ℕ) + 331776 * s ^ (8 : ℕ)
def sharpJetMainShiftedAbs3 (s : ℝ) : ℝ := 5403931200 + 7311298464 * s + 4245401376 * s ^ (2 : ℕ) + 1370846304 * s ^ (3 : ℕ) + 265735872 * s ^ (4 : ℕ) + 30913152 * s ^ (5 : ℕ) + 1997568 * s ^ (6 : ℕ) + 55296 * s ^ (7 : ℕ)

/-- The main second-atom part of the `3`-th jet. -/
def sharpJetMain3 (A : ℝ) : ℝ :=
  Real.exp (-3 * A) * (sharpJetMainNumerator3 A / (2 * A - 3) ^ (4 : ℕ))

theorem sharpJet_identity_3 (A : ℝ) (hA : 3 / 2 < A) :
    (-8) * A ^ (3 : ℕ) * secondAtomMomentProfile 3 (A - 3 / 2) + (24) * A ^ (2 : ℕ) * secondAtomMomentProfile 2 (A - 3 / 2) + (-8) * A * secondAtomMomentProfile 1 (A - 3 / 2) =
      Real.exp (-3 * A) * (sharpJetMainNumerator3 A / (2 * A - 3) ^ (4 : ℕ)) := by
  have hne : A - 3 / 2 ≠ 0 := by intro h; linarith
  have hne2 : 2 * A - 3 ≠ 0 := by intro h; linarith
  simp only [secondAtomMomentProfile_eq_A, secondAtomProfile, secondAtomNumerator3, secondAtomNumerator2, secondAtomNumerator1, sharpJetMainNumerator3]
  field_simp
  ring

theorem hasDerivAt_sharpJetMainNumerator3 (A : ℝ) :
    HasDerivAt sharpJetMainNumerator3 ((-12960) + 371520 * A + (-1958688) * A ^ (2 : ℕ) + 4038912 * A ^ (3 : ℕ) + (-4022400) * A ^ (4 : ℕ) + 1949184 * A ^ (5 : ℕ) + (-387072) * A ^ (6 : ℕ)) A := by
  have h := hasDerivAt_poly16 0 (-12960) 185760 (-652896) 1009728 (-804480) 324864 (-55296) 0 0 0 0 0 0 0 0 0 A
  unfold sharpJetMainNumerator3
  convert h using 1 <;> first | (funext x; ring) | ring

theorem hasDerivAt_sharpJetMain3 {A : ℝ} (hA : 3 / 2 < A) :
    HasDerivAt sharpJetMain3
      (Real.exp (-3 * A) * (sharpJetMainDerivNumerator3 A / (2 * A - 3) ^ (5 : ℕ))) A := by
  unfold sharpJetMain3
  have hne : 2 * A - 3 ≠ 0 := by intro h; linarith
  have h1 : HasDerivAt (fun q : ℝ => -3 * q) (-3) A := by
    simpa using (hasDerivAt_id A).const_mul (-3 : ℝ)
  have h2 : HasDerivAt (fun q : ℝ => Real.exp (-3 * q)) (Real.exp (-3 * A) * -3) A :=
    (Real.hasDerivAt_exp _).comp A h1
  have hlin : HasDerivAt (fun q : ℝ => 2 * q - 3) 2 A := by
    simpa using ((hasDerivAt_id A).const_mul (2 : ℝ)).sub_const 3
  have hden : HasDerivAt (fun q : ℝ => (2 * q - 3) ^ (4 : ℕ)) (4 * (2 * A - 3) ^ (3 : ℕ) * 2) A := by
    have := (hasDerivAt_pow 4 (2 * A - 3)).comp A hlin
    simpa [Function.comp_def] using this
  have h3 : HasDerivAt (fun q : ℝ => sharpJetMainNumerator3 q / (2 * q - 3) ^ (4 : ℕ)) _ A :=
    (hasDerivAt_sharpJetMainNumerator3 A).div hden (pow_ne_zero _ hne)
  have h4 := h2.mul h3
  refine HasDerivAt.congr_deriv (f := fun q : ℝ => Real.exp (-3 * q) * (sharpJetMainNumerator3 q / (2 * q - 3) ^ (4 : ℕ))) h4 ?_
  unfold sharpJetMainDerivNumerator3 sharpJetMainNumerator3
  field_simp
  ring

theorem sharpJetMainDerivNumerator3_eq (A : ℝ) :
    sharpJetMainDerivNumerator3 A = sharpJetMainDerivShiftedAbs3 (A - 6) := by
  unfold sharpJetMainDerivNumerator3 sharpJetMainDerivShiftedAbs3
  ring

theorem sharpJetMainNumerator3_eq (A : ℝ) :
    sharpJetMainNumerator3 A = -sharpJetMainShiftedAbs3 (A - 6) := by
  unfold sharpJetMainNumerator3 sharpJetMainShiftedAbs3
  ring

theorem sharpJetMainDerivShiftedAbs3_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ sharpJetMainDerivShiftedAbs3 s := by
  unfold sharpJetMainDerivShiftedAbs3; positivity

theorem sharpJetMainShiftedAbs3_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ sharpJetMainShiftedAbs3 s := by
  unfold sharpJetMainShiftedAbs3; positivity

theorem sharpJetMain3_abs_eq {A : ℝ} (hA : 6 ≤ A) :
    |sharpJetMain3 A| = (-1 : ℝ) * sharpJetMain3 A := by
  unfold sharpJetMain3
  rw [sharpJetMainNumerator3_eq]
  have hS := sharpJetMainShiftedAbs3_nonneg (show 0 ≤ A - 6 by linarith)
  have hden : 0 < (2 * A - 3) ^ (4 : ℕ) := by
    have : 0 < 2 * A - 3 := by linarith
    positivity
  have h0 : 0 ≤ Real.exp (-3 * A) * (sharpJetMainShiftedAbs3 (A - 6) / (2 * A - 3) ^ (4 : ℕ)) := by
    positivity
  have e : Real.exp (-3 * A) * (-sharpJetMainShiftedAbs3 (A - 6) / (2 * A - 3) ^ (4 : ℕ)) =
      -(Real.exp (-3 * A) * (sharpJetMainShiftedAbs3 (A - 6) / (2 * A - 3) ^ (4 : ℕ))) := by ring
  rw [e, abs_neg, abs_of_nonneg h0]
  ring

/-- `|h_3|` is antitone on `[6, ∞)`. -/
theorem sharpJetMain3_abs_le_of_le {A₁ A : ℝ} (h1 : 6 ≤ A₁) (h : A₁ ≤ A) :
    |sharpJetMain3 A| ≤ |sharpJetMain3 A₁| := by
  have hanti : AntitoneOn (fun A => (-1 : ℝ) * sharpJetMain3 A) (Ici 6) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 6)
    · intro x hx
      have hx6 : 6 ≤ x := mem_Ici.mp hx
      exact ((hasDerivAt_sharpJetMain3 (show 3 / 2 < x by linarith)).const_mul (-1 : ℝ)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx6 : 6 < x := mem_Ioi.mp hx
      exact ((hasDerivAt_sharpJetMain3 (show 3 / 2 < x by linarith)).const_mul (-1 : ℝ)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx6 : 6 < x := mem_Ioi.mp hx
      rw [((hasDerivAt_sharpJetMain3 (show 3 / 2 < x by linarith)).const_mul (-1 : ℝ)).deriv,
        sharpJetMainDerivNumerator3_eq]
      have hS := sharpJetMainDerivShiftedAbs3_nonneg (show 0 ≤ x - 6 by linarith)
      have hden : 0 < (2 * x - 3) ^ (5 : ℕ) := by
        have : 0 < 2 * x - 3 := by linarith
        positivity
      have h0 : 0 ≤ Real.exp (-3 * x) * (sharpJetMainDerivShiftedAbs3 (x - 6) / (2 * x - 3) ^ (5 : ℕ)) := by
        positivity
      have e : (-1 : ℝ) * (Real.exp (-3 * x) * (sharpJetMainDerivShiftedAbs3 (x - 6) / (2 * x - 3) ^ (5 : ℕ))) =
          -(Real.exp (-3 * x) * (sharpJetMainDerivShiftedAbs3 (x - 6) / (2 * x - 3) ^ (5 : ℕ))) := by ring
      rw [e]
      linarith
  rw [sharpJetMain3_abs_eq (h1.trans h), sharpJetMain3_abs_eq h1]
  exact hanti (mem_Ici.mpr h1) (mem_Ici.mpr (h1.trans h)) h

/-- Numerator of the main second-atom part of the `4`-th log-partition jet. -/
def sharpJetMainNumerator4 (A : ℝ) : ℝ := 77760 * A + (-2306880) * A ^ (2 : ℕ) + 13765248 * A ^ (3 : ℕ) + (-35603136) * A ^ (4 : ℕ) + 50144256 * A ^ (5 : ℕ) + (-41510400) * A ^ (6 : ℕ) + 20422656 * A ^ (7 : ℕ) + (-5557248) * A ^ (8 : ℕ) + 663552 * A ^ (9 : ℕ)

/-- Derivative numerator of the main `4`-th jet. -/
def sharpJetMainDerivNumerator4 (A : ℝ) : ℝ := (-233280) + 13919040 * A + (-131274432) * A ^ (2 : ℕ) + 509905152 * A ^ (3 : ℕ) + (-1083977280) * A ^ (4 : ℕ) + 1412104320 * A ^ (5 : ℕ) + (-1186355712) * A ^ (6 : ℕ) + 647930880 * A ^ (7 : ℕ) + (-223810560) * A ^ (8 : ℕ) + 44623872 * A ^ (9 : ℕ) + (-3981312) * A ^ (10 : ℕ)

def sharpJetMainDerivShiftedAbs4 (s : ℝ) : ℝ := 31234941012672 + 63361041158592 * s + 58024708219584 * s ^ (2 : ℕ) + 31567622641920 * s ^ (3 : ℕ) + 11291630131008 * s ^ (4 : ℕ) + 2773361579904 * s ^ (5 : ℕ) + 473472643584 * s ^ (6 : ℕ) + 55458044928 * s ^ (7 : ℕ) + 4263846912 * s ^ (8 : ℕ) + 194254848 * s ^ (9 : ℕ) + 3981312 * s ^ (10 : ℕ)
def sharpJetMainShiftedAbs4 (s : ℝ) : ℝ := 1480030869888 + 2614022352576 * s + 2056107022272 * s ^ (2 : ℕ) + 944850282624 * s ^ (3 : ℕ) + 279427173696 * s ^ (4 : ℕ) + 55130213376 * s ^ (5 : ℕ) + 7254022656 * s ^ (6 : ℕ) + 613638144 * s ^ (7 : ℕ) + 30274560 * s ^ (8 : ℕ) + 663552 * s ^ (9 : ℕ)

/-- The main second-atom part of the `4`-th jet. -/
def sharpJetMain4 (A : ℝ) : ℝ :=
  Real.exp (-3 * A) * (sharpJetMainNumerator4 A / (2 * A - 3) ^ (5 : ℕ))

theorem sharpJet_identity_4 (A : ℝ) (hA : 3 / 2 < A) :
    (16) * A ^ (4 : ℕ) * secondAtomMomentProfile 4 (A - 3 / 2) + (-96) * A ^ (3 : ℕ) * secondAtomMomentProfile 3 (A - 3 / 2) + (112) * A ^ (2 : ℕ) * secondAtomMomentProfile 2 (A - 3 / 2) + (-16) * A * secondAtomMomentProfile 1 (A - 3 / 2) =
      Real.exp (-3 * A) * (sharpJetMainNumerator4 A / (2 * A - 3) ^ (5 : ℕ)) := by
  have hne : A - 3 / 2 ≠ 0 := by intro h; linarith
  have hne2 : 2 * A - 3 ≠ 0 := by intro h; linarith
  simp only [secondAtomMomentProfile_eq_A, secondAtomProfile, secondAtomNumerator4, secondAtomNumerator3, secondAtomNumerator2, secondAtomNumerator1, sharpJetMainNumerator4]
  field_simp
  ring

theorem hasDerivAt_sharpJetMainNumerator4 (A : ℝ) :
    HasDerivAt sharpJetMainNumerator4 (77760 + (-4613760) * A + 41295744 * A ^ (2 : ℕ) + (-142412544) * A ^ (3 : ℕ) + 250721280 * A ^ (4 : ℕ) + (-249062400) * A ^ (5 : ℕ) + 142958592 * A ^ (6 : ℕ) + (-44457984) * A ^ (7 : ℕ) + 5971968 * A ^ (8 : ℕ)) A := by
  have h := hasDerivAt_poly16 0 77760 (-2306880) 13765248 (-35603136) 50144256 (-41510400) 20422656 (-5557248) 663552 0 0 0 0 0 0 0 A
  unfold sharpJetMainNumerator4
  convert h using 1 <;> first | (funext x; ring) | ring

theorem hasDerivAt_sharpJetMain4 {A : ℝ} (hA : 3 / 2 < A) :
    HasDerivAt sharpJetMain4
      (Real.exp (-3 * A) * (sharpJetMainDerivNumerator4 A / (2 * A - 3) ^ (6 : ℕ))) A := by
  unfold sharpJetMain4
  have hne : 2 * A - 3 ≠ 0 := by intro h; linarith
  have h1 : HasDerivAt (fun q : ℝ => -3 * q) (-3) A := by
    simpa using (hasDerivAt_id A).const_mul (-3 : ℝ)
  have h2 : HasDerivAt (fun q : ℝ => Real.exp (-3 * q)) (Real.exp (-3 * A) * -3) A :=
    (Real.hasDerivAt_exp _).comp A h1
  have hlin : HasDerivAt (fun q : ℝ => 2 * q - 3) 2 A := by
    simpa using ((hasDerivAt_id A).const_mul (2 : ℝ)).sub_const 3
  have hden : HasDerivAt (fun q : ℝ => (2 * q - 3) ^ (5 : ℕ)) (5 * (2 * A - 3) ^ (4 : ℕ) * 2) A := by
    have := (hasDerivAt_pow 5 (2 * A - 3)).comp A hlin
    simpa [Function.comp_def] using this
  have h3 : HasDerivAt (fun q : ℝ => sharpJetMainNumerator4 q / (2 * q - 3) ^ (5 : ℕ)) _ A :=
    (hasDerivAt_sharpJetMainNumerator4 A).div hden (pow_ne_zero _ hne)
  have h4 := h2.mul h3
  refine HasDerivAt.congr_deriv (f := fun q : ℝ => Real.exp (-3 * q) * (sharpJetMainNumerator4 q / (2 * q - 3) ^ (5 : ℕ))) h4 ?_
  unfold sharpJetMainDerivNumerator4 sharpJetMainNumerator4
  field_simp
  ring

theorem sharpJetMainDerivNumerator4_eq (A : ℝ) :
    sharpJetMainDerivNumerator4 A = -sharpJetMainDerivShiftedAbs4 (A - 6) := by
  unfold sharpJetMainDerivNumerator4 sharpJetMainDerivShiftedAbs4
  ring

theorem sharpJetMainNumerator4_eq (A : ℝ) :
    sharpJetMainNumerator4 A = sharpJetMainShiftedAbs4 (A - 6) := by
  unfold sharpJetMainNumerator4 sharpJetMainShiftedAbs4
  ring

theorem sharpJetMainDerivShiftedAbs4_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ sharpJetMainDerivShiftedAbs4 s := by
  unfold sharpJetMainDerivShiftedAbs4; positivity

theorem sharpJetMainShiftedAbs4_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ sharpJetMainShiftedAbs4 s := by
  unfold sharpJetMainShiftedAbs4; positivity

theorem sharpJetMain4_abs_eq {A : ℝ} (hA : 6 ≤ A) :
    |sharpJetMain4 A| = (1 : ℝ) * sharpJetMain4 A := by
  rw [one_mul]
  unfold sharpJetMain4
  rw [sharpJetMainNumerator4_eq]
  have hS := sharpJetMainShiftedAbs4_nonneg (show 0 ≤ A - 6 by linarith)
  have hden : 0 < (2 * A - 3) ^ (5 : ℕ) := by
    have : 0 < 2 * A - 3 := by linarith
    positivity
  have h0 : 0 ≤ Real.exp (-3 * A) * (sharpJetMainShiftedAbs4 (A - 6) / (2 * A - 3) ^ (5 : ℕ)) := by
    positivity
  exact abs_of_nonneg h0

/-- `|h_4|` is antitone on `[6, ∞)`. -/
theorem sharpJetMain4_abs_le_of_le {A₁ A : ℝ} (h1 : 6 ≤ A₁) (h : A₁ ≤ A) :
    |sharpJetMain4 A| ≤ |sharpJetMain4 A₁| := by
  have hanti : AntitoneOn (fun A => (1 : ℝ) * sharpJetMain4 A) (Ici 6) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 6)
    · intro x hx
      have hx6 : 6 ≤ x := mem_Ici.mp hx
      exact ((hasDerivAt_sharpJetMain4 (show 3 / 2 < x by linarith)).const_mul (1 : ℝ)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx6 : 6 < x := mem_Ioi.mp hx
      exact ((hasDerivAt_sharpJetMain4 (show 3 / 2 < x by linarith)).const_mul (1 : ℝ)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx6 : 6 < x := mem_Ioi.mp hx
      rw [((hasDerivAt_sharpJetMain4 (show 3 / 2 < x by linarith)).const_mul (1 : ℝ)).deriv,
        sharpJetMainDerivNumerator4_eq]
      have hS := sharpJetMainDerivShiftedAbs4_nonneg (show 0 ≤ x - 6 by linarith)
      have hden : 0 < (2 * x - 3) ^ (6 : ℕ) := by
        have : 0 < 2 * x - 3 := by linarith
        positivity
      have h0 : 0 ≤ Real.exp (-3 * x) * (sharpJetMainDerivShiftedAbs4 (x - 6) / (2 * x - 3) ^ (6 : ℕ)) := by
        positivity
      have e : (1 : ℝ) * (Real.exp (-3 * x) * (-sharpJetMainDerivShiftedAbs4 (x - 6) / (2 * x - 3) ^ (6 : ℕ))) =
          -(Real.exp (-3 * x) * (sharpJetMainDerivShiftedAbs4 (x - 6) / (2 * x - 3) ^ (6 : ℕ))) := by ring
      rw [e]
      linarith
  rw [sharpJetMain4_abs_eq (h1.trans h), sharpJetMain4_abs_eq h1]
  exact hanti (mem_Ici.mpr h1) (mem_Ici.mpr (h1.trans h)) h

/-- Numerator of the main second-atom part of the `5`-th log-partition jet. -/
def sharpJetMainNumerator5 (A : ℝ) : ℝ := (-466560) * A + 27838080 * A ^ (2 : ℕ) + (-262548864) * A ^ (3 : ℕ) + 1019810304 * A ^ (4 : ℕ) + (-2167954560) * A ^ (5 : ℕ) + 2824208640 * A ^ (6 : ℕ) + (-2372711424) * A ^ (7 : ℕ) + 1295861760 * A ^ (8 : ℕ) + (-447621120) * A ^ (9 : ℕ) + 89247744 * A ^ (10 : ℕ) + (-7962624) * A ^ (11 : ℕ)

/-- Derivative numerator of the main `5`-th jet. -/
def sharpJetMainDerivNumerator5 (A : ℝ) : ℝ := 1399680 + (-166561920) * A + 2393577216 * A ^ (2 : ℕ) + (-13192398720) * A ^ (3 : ℕ) + 39193663104 * A ^ (4 : ℕ) + (-72130299264) * A ^ (5 : ℕ) + 88252545024 * A ^ (6 : ℕ) + (-74145759744) * A ^ (7 : ℕ) + 43168241664 * A ^ (8 : ℕ) + (-17166919680) * A ^ (9 : ℕ) + 4465704960 * A ^ (10 : ℕ) + (-686776320) * A ^ (11 : ℕ) + 47775744 * A ^ (12 : ℕ)

def sharpJetMainDerivShiftedAbs5 (s : ℝ) : ℝ := 7212731010574464 + 17878269205125504 * s + 20381220609057792 * s ^ (2 : ℕ) + 14117667747592320 * s ^ (3 : ℕ) + 6612982376448384 * s ^ (4 : ℕ) + 2205519894868608 * s ^ (5 : ℕ) + 536764422104064 * s ^ (6 : ℕ) + 96011492752896 * s ^ (7 : ℕ) + 12522983860224 * s ^ (8 : ℕ) + 1161261619200 * s ^ (9 : ℕ) + 72653635584 * s ^ (10 : ℕ) + 2753077248 * s ^ (11 : ℕ) + 47775744 * s ^ (12 : ℕ)
def sharpJetMainShiftedAbs5 (s : ℝ) : ℝ := 374819292152064 + 822802375928448 * s + 823018580952192 * s ^ (2 : ℕ) + 494860888142208 * s ^ (3 : ℕ) + 198634806855936 * s ^ (4 : ℕ) + 55863599220864 * s ^ (5 : ℕ) + 11228394882816 * s ^ (6 : ℕ) + 1612441826304 * s ^ (7 : ℕ) + 162082252800 * s ^ (8 : ℕ) + 10858752000 * s ^ (9 : ℕ) + 436285440 * s ^ (10 : ℕ) + 7962624 * s ^ (11 : ℕ)

/-- The main second-atom part of the `5`-th jet. -/
def sharpJetMain5 (A : ℝ) : ℝ :=
  Real.exp (-3 * A) * (sharpJetMainNumerator5 A / (2 * A - 3) ^ (6 : ℕ))

theorem sharpJet_identity_5 (A : ℝ) (hA : 3 / 2 < A) :
    (-32) * A ^ (5 : ℕ) * secondAtomMomentProfile 5 (A - 3 / 2) + (320) * A ^ (4 : ℕ) * secondAtomMomentProfile 4 (A - 3 / 2) + (-800) * A ^ (3 : ℕ) * secondAtomMomentProfile 3 (A - 3 / 2) + (480) * A ^ (2 : ℕ) * secondAtomMomentProfile 2 (A - 3 / 2) + (-32) * A * secondAtomMomentProfile 1 (A - 3 / 2) =
      Real.exp (-3 * A) * (sharpJetMainNumerator5 A / (2 * A - 3) ^ (6 : ℕ)) := by
  have hne : A - 3 / 2 ≠ 0 := by intro h; linarith
  have hne2 : 2 * A - 3 ≠ 0 := by intro h; linarith
  simp only [secondAtomMomentProfile_eq_A, secondAtomProfile, secondAtomNumerator5, secondAtomNumerator4, secondAtomNumerator3, secondAtomNumerator2, secondAtomNumerator1, sharpJetMainNumerator5]
  field_simp
  ring

theorem hasDerivAt_sharpJetMainNumerator5 (A : ℝ) :
    HasDerivAt sharpJetMainNumerator5 ((-466560) + 55676160 * A + (-787646592) * A ^ (2 : ℕ) + 4079241216 * A ^ (3 : ℕ) + (-10839772800) * A ^ (4 : ℕ) + 16945251840 * A ^ (5 : ℕ) + (-16608979968) * A ^ (6 : ℕ) + 10366894080 * A ^ (7 : ℕ) + (-4028590080) * A ^ (8 : ℕ) + 892477440 * A ^ (9 : ℕ) + (-87588864) * A ^ (10 : ℕ)) A := by
  have h := hasDerivAt_poly16 0 (-466560) 27838080 (-262548864) 1019810304 (-2167954560) 2824208640 (-2372711424) 1295861760 (-447621120) 89247744 (-7962624) 0 0 0 0 0 A
  unfold sharpJetMainNumerator5
  convert h using 1 <;> first | (funext x; ring) | ring

theorem hasDerivAt_sharpJetMain5 {A : ℝ} (hA : 3 / 2 < A) :
    HasDerivAt sharpJetMain5
      (Real.exp (-3 * A) * (sharpJetMainDerivNumerator5 A / (2 * A - 3) ^ (7 : ℕ))) A := by
  unfold sharpJetMain5
  have hne : 2 * A - 3 ≠ 0 := by intro h; linarith
  have h1 : HasDerivAt (fun q : ℝ => -3 * q) (-3) A := by
    simpa using (hasDerivAt_id A).const_mul (-3 : ℝ)
  have h2 : HasDerivAt (fun q : ℝ => Real.exp (-3 * q)) (Real.exp (-3 * A) * -3) A :=
    (Real.hasDerivAt_exp _).comp A h1
  have hlin : HasDerivAt (fun q : ℝ => 2 * q - 3) 2 A := by
    simpa using ((hasDerivAt_id A).const_mul (2 : ℝ)).sub_const 3
  have hden : HasDerivAt (fun q : ℝ => (2 * q - 3) ^ (6 : ℕ)) (6 * (2 * A - 3) ^ (5 : ℕ) * 2) A := by
    have := (hasDerivAt_pow 6 (2 * A - 3)).comp A hlin
    simpa [Function.comp_def] using this
  have h3 : HasDerivAt (fun q : ℝ => sharpJetMainNumerator5 q / (2 * q - 3) ^ (6 : ℕ)) _ A :=
    (hasDerivAt_sharpJetMainNumerator5 A).div hden (pow_ne_zero _ hne)
  have h4 := h2.mul h3
  refine HasDerivAt.congr_deriv (f := fun q : ℝ => Real.exp (-3 * q) * (sharpJetMainNumerator5 q / (2 * q - 3) ^ (6 : ℕ))) h4 ?_
  unfold sharpJetMainDerivNumerator5 sharpJetMainNumerator5
  field_simp
  ring

theorem sharpJetMainDerivNumerator5_eq (A : ℝ) :
    sharpJetMainDerivNumerator5 A = sharpJetMainDerivShiftedAbs5 (A - 6) := by
  unfold sharpJetMainDerivNumerator5 sharpJetMainDerivShiftedAbs5
  ring

theorem sharpJetMainNumerator5_eq (A : ℝ) :
    sharpJetMainNumerator5 A = -sharpJetMainShiftedAbs5 (A - 6) := by
  unfold sharpJetMainNumerator5 sharpJetMainShiftedAbs5
  ring

theorem sharpJetMainDerivShiftedAbs5_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ sharpJetMainDerivShiftedAbs5 s := by
  unfold sharpJetMainDerivShiftedAbs5; positivity

theorem sharpJetMainShiftedAbs5_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ sharpJetMainShiftedAbs5 s := by
  unfold sharpJetMainShiftedAbs5; positivity

theorem sharpJetMain5_abs_eq {A : ℝ} (hA : 6 ≤ A) :
    |sharpJetMain5 A| = (-1 : ℝ) * sharpJetMain5 A := by
  unfold sharpJetMain5
  rw [sharpJetMainNumerator5_eq]
  have hS := sharpJetMainShiftedAbs5_nonneg (show 0 ≤ A - 6 by linarith)
  have hden : 0 < (2 * A - 3) ^ (6 : ℕ) := by
    have : 0 < 2 * A - 3 := by linarith
    positivity
  have h0 : 0 ≤ Real.exp (-3 * A) * (sharpJetMainShiftedAbs5 (A - 6) / (2 * A - 3) ^ (6 : ℕ)) := by
    positivity
  have e : Real.exp (-3 * A) * (-sharpJetMainShiftedAbs5 (A - 6) / (2 * A - 3) ^ (6 : ℕ)) =
      -(Real.exp (-3 * A) * (sharpJetMainShiftedAbs5 (A - 6) / (2 * A - 3) ^ (6 : ℕ))) := by ring
  rw [e, abs_neg, abs_of_nonneg h0]
  ring

/-- `|h_5|` is antitone on `[6, ∞)`. -/
theorem sharpJetMain5_abs_le_of_le {A₁ A : ℝ} (h1 : 6 ≤ A₁) (h : A₁ ≤ A) :
    |sharpJetMain5 A| ≤ |sharpJetMain5 A₁| := by
  have hanti : AntitoneOn (fun A => (-1 : ℝ) * sharpJetMain5 A) (Ici 6) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 6)
    · intro x hx
      have hx6 : 6 ≤ x := mem_Ici.mp hx
      exact ((hasDerivAt_sharpJetMain5 (show 3 / 2 < x by linarith)).const_mul (-1 : ℝ)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx6 : 6 < x := mem_Ioi.mp hx
      exact ((hasDerivAt_sharpJetMain5 (show 3 / 2 < x by linarith)).const_mul (-1 : ℝ)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx6 : 6 < x := mem_Ioi.mp hx
      rw [((hasDerivAt_sharpJetMain5 (show 3 / 2 < x by linarith)).const_mul (-1 : ℝ)).deriv,
        sharpJetMainDerivNumerator5_eq]
      have hS := sharpJetMainDerivShiftedAbs5_nonneg (show 0 ≤ x - 6 by linarith)
      have hden : 0 < (2 * x - 3) ^ (7 : ℕ) := by
        have : 0 < 2 * x - 3 := by linarith
        positivity
      have h0 : 0 ≤ Real.exp (-3 * x) * (sharpJetMainDerivShiftedAbs5 (x - 6) / (2 * x - 3) ^ (7 : ℕ)) := by
        positivity
      have e : (-1 : ℝ) * (Real.exp (-3 * x) * (sharpJetMainDerivShiftedAbs5 (x - 6) / (2 * x - 3) ^ (7 : ℕ))) =
          -(Real.exp (-3 * x) * (sharpJetMainDerivShiftedAbs5 (x - 6) / (2 * x - 3) ^ (7 : ℕ))) := by ring
      rw [e]
      linarith
  rw [sharpJetMain5_abs_eq (h1.trans h), sharpJetMain5_abs_eq h1]
  exact hanti (mem_Ici.mpr h1) (mem_Ici.mpr (h1.trans h)) h

/-- Numerator of the main second-atom part of the `6`-th log-partition jet. -/
def sharpJetMainNumerator6 (A : ℝ) : ℝ := 2799360 * A + (-333123840) * A ^ (2 : ℕ) + 4787154432 * A ^ (3 : ℕ) + (-26384797440) * A ^ (4 : ℕ) + 78387326208 * A ^ (5 : ℕ) + (-144260598528) * A ^ (6 : ℕ) + 176505090048 * A ^ (7 : ℕ) + (-148291519488) * A ^ (8 : ℕ) + 86336483328 * A ^ (9 : ℕ) + (-34333839360) * A ^ (10 : ℕ) + 8931409920 * A ^ (11 : ℕ) + (-1373552640) * A ^ (12 : ℕ) + 95551488 * A ^ (13 : ℕ)

/-- Derivative numerator of the main `6`-th jet. -/
def sharpJetMainDerivNumerator6 (A : ℝ) : ℝ := (-8398080) + 1990344960 * A + (-42768062208) * A ^ (2 : ℕ) + 323403466752 * A ^ (3 : ℕ) + (-1283687212032) * A ^ (4 : ℕ) + 3146936189184 * A ^ (5 : ℕ) + (-5186755037952) * A ^ (6 : ℕ) + 6013105869312 * A ^ (7 : ℕ) + (-5021322304512) * A ^ (8 : ℕ) + 3042138580992 * A ^ (9 : ℕ) + (-1327763017728) * A ^ (10 : ℕ) + 407284899840 * A ^ (11 : ℕ) + (-83412467712) * A ^ (12 : ℕ) + 10247897088 * A ^ (13 : ℕ) + (-573308928) * A ^ (14 : ℕ)

def sharpJetMainDerivShiftedAbs6 (s : ℝ) : ℝ := 1487981424858741504 + 4402978296643904256 * s + 6071331763387844352 * s ^ (2 : ℕ) + 5164812546484137984 * s ^ (3 : ℕ) + 3025404660440590848 * s ^ (4 : ℕ) + 1289985558137070336 * s ^ (5 : ℕ) + 412650388036212480 * s ^ (6 : ℕ) + 100560766563823104 * s ^ (7 : ℕ) + 18754000659950592 * s ^ (8 : ℕ) + 2662865197553664 * s ^ (9 : ℕ) + 283312271462400 * s ^ (10 : ℕ) + 21898158907392 * s ^ (11 : ℕ) + 1162236542976 * s ^ (12 : ℕ) + 37910052864 * s ^ (13 : ℕ) + 573308928 * s ^ (14 : ℕ)
def sharpJetMainShiftedAbs6 (s : ℝ) : ℝ := 86552772126893568 + 228964692482654976 * s + 280331185718944512 * s ^ (2 : ℕ) + 210174454189223424 * s ^ (3 : ℕ) + 107591124012565248 * s ^ (4 : ℕ) + 39692203491320064 * s ^ (5 : ℕ) + 10852212854985984 * s ^ (6 : ℕ) + 2225666757242880 * s ^ (7 : ℕ) + 342298791828480 * s ^ (8 : ℕ) + 38981107150848 * s ^ (9 : ℕ) + 3194366865408 * s ^ (10 : ℕ) + 178344198144 * s ^ (11 : ℕ) + 6079463424 * s ^ (12 : ℕ) + 95551488 * s ^ (13 : ℕ)

/-- The main second-atom part of the `6`-th jet. -/
def sharpJetMain6 (A : ℝ) : ℝ :=
  Real.exp (-3 * A) * (sharpJetMainNumerator6 A / (2 * A - 3) ^ (7 : ℕ))

theorem sharpJet_identity_6 (A : ℝ) (hA : 3 / 2 < A) :
    (64) * A ^ (6 : ℕ) * secondAtomMomentProfile 6 (A - 3 / 2) + (-960) * A ^ (5 : ℕ) * secondAtomMomentProfile 5 (A - 3 / 2) + (4160) * A ^ (4 : ℕ) * secondAtomMomentProfile 4 (A - 3 / 2) + (-5760) * A ^ (3 : ℕ) * secondAtomMomentProfile 3 (A - 3 / 2) + (1984) * A ^ (2 : ℕ) * secondAtomMomentProfile 2 (A - 3 / 2) + (-64) * A * secondAtomMomentProfile 1 (A - 3 / 2) =
      Real.exp (-3 * A) * (sharpJetMainNumerator6 A / (2 * A - 3) ^ (7 : ℕ)) := by
  have hne : A - 3 / 2 ≠ 0 := by intro h; linarith
  have hne2 : 2 * A - 3 ≠ 0 := by intro h; linarith
  simp only [secondAtomMomentProfile_eq_A, secondAtomProfile, secondAtomNumerator6, secondAtomNumerator5, secondAtomNumerator4, secondAtomNumerator3, secondAtomNumerator2, secondAtomNumerator1, sharpJetMainNumerator6]
  field_simp
  ring

theorem hasDerivAt_sharpJetMainNumerator6 (A : ℝ) :
    HasDerivAt sharpJetMainNumerator6 (2799360 + (-666247680) * A + 14361463296 * A ^ (2 : ℕ) + (-105539189760) * A ^ (3 : ℕ) + 391936631040 * A ^ (4 : ℕ) + (-865563591168) * A ^ (5 : ℕ) + 1235535630336 * A ^ (6 : ℕ) + (-1186332155904) * A ^ (7 : ℕ) + 777028349952 * A ^ (8 : ℕ) + (-343338393600) * A ^ (9 : ℕ) + 98245509120 * A ^ (10 : ℕ) + (-16482631680) * A ^ (11 : ℕ) + 1242169344 * A ^ (12 : ℕ)) A := by
  have h := hasDerivAt_poly16 0 2799360 (-333123840) 4787154432 (-26384797440) 78387326208 (-144260598528) 176505090048 (-148291519488) 86336483328 (-34333839360) 8931409920 (-1373552640) 95551488 0 0 0 A
  unfold sharpJetMainNumerator6
  convert h using 1 <;> first | (funext x; ring) | ring

theorem hasDerivAt_sharpJetMain6 {A : ℝ} (hA : 3 / 2 < A) :
    HasDerivAt sharpJetMain6
      (Real.exp (-3 * A) * (sharpJetMainDerivNumerator6 A / (2 * A - 3) ^ (8 : ℕ))) A := by
  unfold sharpJetMain6
  have hne : 2 * A - 3 ≠ 0 := by intro h; linarith
  have h1 : HasDerivAt (fun q : ℝ => -3 * q) (-3) A := by
    simpa using (hasDerivAt_id A).const_mul (-3 : ℝ)
  have h2 : HasDerivAt (fun q : ℝ => Real.exp (-3 * q)) (Real.exp (-3 * A) * -3) A :=
    (Real.hasDerivAt_exp _).comp A h1
  have hlin : HasDerivAt (fun q : ℝ => 2 * q - 3) 2 A := by
    simpa using ((hasDerivAt_id A).const_mul (2 : ℝ)).sub_const 3
  have hden : HasDerivAt (fun q : ℝ => (2 * q - 3) ^ (7 : ℕ)) (7 * (2 * A - 3) ^ (6 : ℕ) * 2) A := by
    have := (hasDerivAt_pow 7 (2 * A - 3)).comp A hlin
    simpa [Function.comp_def] using this
  have h3 : HasDerivAt (fun q : ℝ => sharpJetMainNumerator6 q / (2 * q - 3) ^ (7 : ℕ)) _ A :=
    (hasDerivAt_sharpJetMainNumerator6 A).div hden (pow_ne_zero _ hne)
  have h4 := h2.mul h3
  refine HasDerivAt.congr_deriv (f := fun q : ℝ => Real.exp (-3 * q) * (sharpJetMainNumerator6 q / (2 * q - 3) ^ (7 : ℕ))) h4 ?_
  unfold sharpJetMainDerivNumerator6 sharpJetMainNumerator6
  field_simp
  ring

theorem sharpJetMainDerivNumerator6_eq (A : ℝ) :
    sharpJetMainDerivNumerator6 A = -sharpJetMainDerivShiftedAbs6 (A - 6) := by
  unfold sharpJetMainDerivNumerator6 sharpJetMainDerivShiftedAbs6
  ring

theorem sharpJetMainNumerator6_eq (A : ℝ) :
    sharpJetMainNumerator6 A = sharpJetMainShiftedAbs6 (A - 6) := by
  unfold sharpJetMainNumerator6 sharpJetMainShiftedAbs6
  ring

theorem sharpJetMainDerivShiftedAbs6_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ sharpJetMainDerivShiftedAbs6 s := by
  unfold sharpJetMainDerivShiftedAbs6; positivity

theorem sharpJetMainShiftedAbs6_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ sharpJetMainShiftedAbs6 s := by
  unfold sharpJetMainShiftedAbs6; positivity

theorem sharpJetMain6_abs_eq {A : ℝ} (hA : 6 ≤ A) :
    |sharpJetMain6 A| = (1 : ℝ) * sharpJetMain6 A := by
  rw [one_mul]
  unfold sharpJetMain6
  rw [sharpJetMainNumerator6_eq]
  have hS := sharpJetMainShiftedAbs6_nonneg (show 0 ≤ A - 6 by linarith)
  have hden : 0 < (2 * A - 3) ^ (7 : ℕ) := by
    have : 0 < 2 * A - 3 := by linarith
    positivity
  have h0 : 0 ≤ Real.exp (-3 * A) * (sharpJetMainShiftedAbs6 (A - 6) / (2 * A - 3) ^ (7 : ℕ)) := by
    positivity
  exact abs_of_nonneg h0

/-- `|h_6|` is antitone on `[6, ∞)`. -/
theorem sharpJetMain6_abs_le_of_le {A₁ A : ℝ} (h1 : 6 ≤ A₁) (h : A₁ ≤ A) :
    |sharpJetMain6 A| ≤ |sharpJetMain6 A₁| := by
  have hanti : AntitoneOn (fun A => (1 : ℝ) * sharpJetMain6 A) (Ici 6) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 6)
    · intro x hx
      have hx6 : 6 ≤ x := mem_Ici.mp hx
      exact ((hasDerivAt_sharpJetMain6 (show 3 / 2 < x by linarith)).const_mul (1 : ℝ)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx6 : 6 < x := mem_Ioi.mp hx
      exact ((hasDerivAt_sharpJetMain6 (show 3 / 2 < x by linarith)).const_mul (1 : ℝ)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx6 : 6 < x := mem_Ioi.mp hx
      rw [((hasDerivAt_sharpJetMain6 (show 3 / 2 < x by linarith)).const_mul (1 : ℝ)).deriv,
        sharpJetMainDerivNumerator6_eq]
      have hS := sharpJetMainDerivShiftedAbs6_nonneg (show 0 ≤ x - 6 by linarith)
      have hden : 0 < (2 * x - 3) ^ (8 : ℕ) := by
        have : 0 < 2 * x - 3 := by linarith
        positivity
      have h0 : 0 ≤ Real.exp (-3 * x) * (sharpJetMainDerivShiftedAbs6 (x - 6) / (2 * x - 3) ^ (8 : ℕ)) := by
        positivity
      have e : (1 : ℝ) * (Real.exp (-3 * x) * (-sharpJetMainDerivShiftedAbs6 (x - 6) / (2 * x - 3) ^ (8 : ℕ))) =
          -(Real.exp (-3 * x) * (sharpJetMainDerivShiftedAbs6 (x - 6) / (2 * x - 3) ^ (8 : ℕ))) := by ring
      rw [e]
      linarith
  rw [sharpJetMain6_abs_eq (h1.trans h), sharpJetMain6_abs_eq h1]
  exact hanti (mem_Ici.mpr h1) (mem_Ici.mpr (h1.trans h)) h

/-- Numerator of the main second-atom part of the `7`-th log-partition jet. -/
def sharpJetMainNumerator7 (A : ℝ) : ℝ := (-16796160) * A + 3980689920 * A ^ (2 : ℕ) + (-85536124416) * A ^ (3 : ℕ) + 646806933504 * A ^ (4 : ℕ) + (-2567374424064) * A ^ (5 : ℕ) + 6293872378368 * A ^ (6 : ℕ) + (-10373510075904) * A ^ (7 : ℕ) + 12026211738624 * A ^ (8 : ℕ) + (-10042644609024) * A ^ (9 : ℕ) + 6084277161984 * A ^ (10 : ℕ) + (-2655526035456) * A ^ (11 : ℕ) + 814569799680 * A ^ (12 : ℕ) + (-166824935424) * A ^ (13 : ℕ) + 20495794176 * A ^ (14 : ℕ) + (-1146617856) * A ^ (15 : ℕ)

/-- Derivative numerator of the main `7`-th jet. -/
def sharpJetMainDerivNumerator7 (A : ℝ) : ℝ := 50388480 + (-23800158720) * A + 757983826944 * A ^ (2 : ℕ) + (-7700031217152) * A ^ (3 : ℕ) + 39670640040960 * A ^ (4 : ℕ) + (-124872667683840) * A ^ (5 : ℕ) + 264717320030208 * A ^ (6 : ℕ) + (-399006886528512) * A ^ (7 : ℕ) + 441628370546688 * A ^ (8 : ℕ) + (-365154675990528) * A ^ (9 : ℕ) + 226983829929984 * A ^ (10 : ℕ) + (-105663066292224) * A ^ (11 : ℕ) + 36287015288832 * A ^ (12 : ℕ) + (-8917915926528) * A ^ (13 : ℕ) + 1482959093760 * A ^ (14 : ℕ) + (-149346975744) * A ^ (15 : ℕ) + 6879707136 * A ^ (16 : ℕ)

def sharpJetMainDerivShiftedAbs7 (s : ℝ) : ℝ := 265493093542111609344 + 925499581806092152320 * s + 1518434606576597391360 * s ^ (2 : ℕ) + 1553585630996116210176 * s ^ (3 : ℕ) + 1108050699312778724352 * s ^ (4 : ℕ) + 583601982994621762560 * s ^ (5 : ℕ) + 234650976650312518656 * s ^ (6 : ℕ) + 73435316951175068160 * s ^ (7 : ℕ) + 18072304378366095360 * s ^ (8 : ℕ) + 3508283849806897152 * s ^ (9 : ℕ) + 535349445622824960 * s ^ (10 : ℕ) + 63534056478326784 * s ^ (11 : ℕ) + 5748345603883008 * s ^ (12 : ℕ) + 383288454807552 * s ^ (13 : ℕ) + 17762066104320 * s ^ (14 : ℕ) + 511104909312 * s ^ (15 : ℕ) + 6879707136 * s ^ (16 : ℕ)
def sharpJetMainShiftedAbs7 (s : ℝ) : ℝ := 17855777098304898048 + 55811702409444334080 * s + 81661937753941940736 * s ^ (2 : ℕ) + 74120414084585344512 * s ^ (3 : ℕ) + 46634481018255366144 * s ^ (4 : ℕ) + 21530636018526025728 * s ^ (5 : ℕ) + 7531775772708690432 * s ^ (6 : ℕ) + 2032029974838302208 * s ^ (7 : ℕ) + 426169541047053312 * s ^ (8 : ℕ) + 69462383690545152 * s ^ (9 : ℕ) + 8725477652656128 * s ^ (10 : ℕ) + 829402449813504 * s ^ (11 : ℕ) + 57743156330496 * s ^ (12 : ℕ) + 2779393720320 * s ^ (13 : ℕ) + 82699812864 * s ^ (14 : ℕ) + 1146617856 * s ^ (15 : ℕ)

/-- The main second-atom part of the `7`-th jet. -/
def sharpJetMain7 (A : ℝ) : ℝ :=
  Real.exp (-3 * A) * (sharpJetMainNumerator7 A / (2 * A - 3) ^ (8 : ℕ))

theorem sharpJet_identity_7 (A : ℝ) (hA : 3 / 2 < A) :
    (-128) * A ^ (7 : ℕ) * secondAtomMomentProfile 7 (A - 3 / 2) + (2688) * A ^ (6 : ℕ) * secondAtomMomentProfile 6 (A - 3 / 2) + (-17920) * A ^ (5 : ℕ) * secondAtomMomentProfile 5 (A - 3 / 2) + (44800) * A ^ (4 : ℕ) * secondAtomMomentProfile 4 (A - 3 / 2) + (-38528) * A ^ (3 : ℕ) * secondAtomMomentProfile 3 (A - 3 / 2) + (8064) * A ^ (2 : ℕ) * secondAtomMomentProfile 2 (A - 3 / 2) + (-128) * A * secondAtomMomentProfile 1 (A - 3 / 2) =
      Real.exp (-3 * A) * (sharpJetMainNumerator7 A / (2 * A - 3) ^ (8 : ℕ)) := by
  have hne : A - 3 / 2 ≠ 0 := by intro h; linarith
  have hne2 : 2 * A - 3 ≠ 0 := by intro h; linarith
  simp only [secondAtomMomentProfile_eq_A, secondAtomProfile, secondAtomNumerator7, secondAtomNumerator6, secondAtomNumerator5, secondAtomNumerator4, secondAtomNumerator3, secondAtomNumerator2, secondAtomNumerator1, sharpJetMainNumerator7]
  field_simp
  ring

theorem hasDerivAt_sharpJetMainNumerator7 (A : ℝ) :
    HasDerivAt sharpJetMainNumerator7 ((-16796160) + 7961379840 * A + (-256608373248) * A ^ (2 : ℕ) + 2587227734016 * A ^ (3 : ℕ) + (-12836872120320) * A ^ (4 : ℕ) + 37763234270208 * A ^ (5 : ℕ) + (-72614570531328) * A ^ (6 : ℕ) + 96209693908992 * A ^ (7 : ℕ) + (-90383801481216) * A ^ (8 : ℕ) + 60842771619840 * A ^ (9 : ℕ) + (-29210786390016) * A ^ (10 : ℕ) + 9774837596160 * A ^ (11 : ℕ) + (-2168724160512) * A ^ (12 : ℕ) + 286941118464 * A ^ (13 : ℕ) + (-17199267840) * A ^ (14 : ℕ)) A := by
  have h := hasDerivAt_poly16 0 (-16796160) 3980689920 (-85536124416) 646806933504 (-2567374424064) 6293872378368 (-10373510075904) 12026211738624 (-10042644609024) 6084277161984 (-2655526035456) 814569799680 (-166824935424) 20495794176 (-1146617856) 0 A
  unfold sharpJetMainNumerator7
  convert h using 1 <;> first | (funext x; ring) | ring

theorem hasDerivAt_sharpJetMain7 {A : ℝ} (hA : 3 / 2 < A) :
    HasDerivAt sharpJetMain7
      (Real.exp (-3 * A) * (sharpJetMainDerivNumerator7 A / (2 * A - 3) ^ (9 : ℕ))) A := by
  unfold sharpJetMain7
  have hne : 2 * A - 3 ≠ 0 := by intro h; linarith
  have h1 : HasDerivAt (fun q : ℝ => -3 * q) (-3) A := by
    simpa using (hasDerivAt_id A).const_mul (-3 : ℝ)
  have h2 : HasDerivAt (fun q : ℝ => Real.exp (-3 * q)) (Real.exp (-3 * A) * -3) A :=
    (Real.hasDerivAt_exp _).comp A h1
  have hlin : HasDerivAt (fun q : ℝ => 2 * q - 3) 2 A := by
    simpa using ((hasDerivAt_id A).const_mul (2 : ℝ)).sub_const 3
  have hden : HasDerivAt (fun q : ℝ => (2 * q - 3) ^ (8 : ℕ)) (8 * (2 * A - 3) ^ (7 : ℕ) * 2) A := by
    have := (hasDerivAt_pow 8 (2 * A - 3)).comp A hlin
    simpa [Function.comp_def] using this
  have h3 : HasDerivAt (fun q : ℝ => sharpJetMainNumerator7 q / (2 * q - 3) ^ (8 : ℕ)) _ A :=
    (hasDerivAt_sharpJetMainNumerator7 A).div hden (pow_ne_zero _ hne)
  have h4 := h2.mul h3
  refine HasDerivAt.congr_deriv (f := fun q : ℝ => Real.exp (-3 * q) * (sharpJetMainNumerator7 q / (2 * q - 3) ^ (8 : ℕ))) h4 ?_
  unfold sharpJetMainDerivNumerator7 sharpJetMainNumerator7
  field_simp
  ring

theorem sharpJetMainDerivNumerator7_eq (A : ℝ) :
    sharpJetMainDerivNumerator7 A = sharpJetMainDerivShiftedAbs7 (A - 6) := by
  unfold sharpJetMainDerivNumerator7 sharpJetMainDerivShiftedAbs7
  ring

theorem sharpJetMainNumerator7_eq (A : ℝ) :
    sharpJetMainNumerator7 A = -sharpJetMainShiftedAbs7 (A - 6) := by
  unfold sharpJetMainNumerator7 sharpJetMainShiftedAbs7
  ring

theorem sharpJetMainDerivShiftedAbs7_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ sharpJetMainDerivShiftedAbs7 s := by
  unfold sharpJetMainDerivShiftedAbs7; positivity

theorem sharpJetMainShiftedAbs7_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ sharpJetMainShiftedAbs7 s := by
  unfold sharpJetMainShiftedAbs7; positivity

theorem sharpJetMain7_abs_eq {A : ℝ} (hA : 6 ≤ A) :
    |sharpJetMain7 A| = (-1 : ℝ) * sharpJetMain7 A := by
  unfold sharpJetMain7
  rw [sharpJetMainNumerator7_eq]
  have hS := sharpJetMainShiftedAbs7_nonneg (show 0 ≤ A - 6 by linarith)
  have hden : 0 < (2 * A - 3) ^ (8 : ℕ) := by
    have : 0 < 2 * A - 3 := by linarith
    positivity
  have h0 : 0 ≤ Real.exp (-3 * A) * (sharpJetMainShiftedAbs7 (A - 6) / (2 * A - 3) ^ (8 : ℕ)) := by
    positivity
  have e : Real.exp (-3 * A) * (-sharpJetMainShiftedAbs7 (A - 6) / (2 * A - 3) ^ (8 : ℕ)) =
      -(Real.exp (-3 * A) * (sharpJetMainShiftedAbs7 (A - 6) / (2 * A - 3) ^ (8 : ℕ))) := by ring
  rw [e, abs_neg, abs_of_nonneg h0]
  ring

/-- `|h_7|` is antitone on `[6, ∞)`. -/
theorem sharpJetMain7_abs_le_of_le {A₁ A : ℝ} (h1 : 6 ≤ A₁) (h : A₁ ≤ A) :
    |sharpJetMain7 A| ≤ |sharpJetMain7 A₁| := by
  have hanti : AntitoneOn (fun A => (-1 : ℝ) * sharpJetMain7 A) (Ici 6) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 6)
    · intro x hx
      have hx6 : 6 ≤ x := mem_Ici.mp hx
      exact ((hasDerivAt_sharpJetMain7 (show 3 / 2 < x by linarith)).const_mul (-1 : ℝ)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx6 : 6 < x := mem_Ioi.mp hx
      exact ((hasDerivAt_sharpJetMain7 (show 3 / 2 < x by linarith)).const_mul (-1 : ℝ)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx6 : 6 < x := mem_Ioi.mp hx
      rw [((hasDerivAt_sharpJetMain7 (show 3 / 2 < x by linarith)).const_mul (-1 : ℝ)).deriv,
        sharpJetMainDerivNumerator7_eq]
      have hS := sharpJetMainDerivShiftedAbs7_nonneg (show 0 ≤ x - 6 by linarith)
      have hden : 0 < (2 * x - 3) ^ (9 : ℕ) := by
        have : 0 < 2 * x - 3 := by linarith
        positivity
      have h0 : 0 ≤ Real.exp (-3 * x) * (sharpJetMainDerivShiftedAbs7 (x - 6) / (2 * x - 3) ^ (9 : ℕ)) := by
        positivity
      have e : (-1 : ℝ) * (Real.exp (-3 * x) * (sharpJetMainDerivShiftedAbs7 (x - 6) / (2 * x - 3) ^ (9 : ℕ))) =
          -(Real.exp (-3 * x) * (sharpJetMainDerivShiftedAbs7 (x - 6) / (2 * x - 3) ^ (9 : ℕ))) := by ring
      rw [e]
      linarith
  rw [sharpJetMain7_abs_eq (h1.trans h), sharpJetMain7_abs_eq h1]
  exact hanti (mem_Ici.mpr h1) (mem_Ici.mpr (h1.trans h)) h

/-! ## Cumulant–moment gaps (pure real arithmetic) -/

theorem cumulant_gap_2 {μ m2 ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 1000000) (hμ0 : 0 ≤ μ) (hμ : μ ≤ 3 * ε) (hm20 : 0 ≤ m2) (hm2 : m2 ≤ 9 * ε) :
    |(m2 - μ ^ (2 : ℕ)) - m2| ≤ 9 * ε ^ (2 : ℕ) := by
  have hε1' : ε ≤ 1 := by linarith
  have hε2 : ε ^ (2 : ℕ) * (1 / 1000000) ≥ 0 := by positivity
  have hε3 : ∀ n : ℕ, 3 ≤ n → ε ^ n ≤ ε ^ (2 : ℕ) * (1 / 1000000) := by
    intro n hn
    have h1 : ε ^ n ≤ ε ^ (3 : ℕ) := pow_le_pow_of_le_one hε0 hε1' hn
    have h2 : ε ^ (3 : ℕ) = ε ^ (2 : ℕ) * ε := by ring
    have h3 : ε ^ (2 : ℕ) * ε ≤ ε ^ (2 : ℕ) * (1 / 1000000) := mul_le_mul_of_nonneg_left hε1 (by positivity)
    linarith
  have pμ : ∀ n : ℕ, μ ^ n ≤ (3 * ε) ^ n := fun n => pow_le_pow_left₀ hμ0 hμ n
  have pm2 : ∀ n : ℕ, m2 ^ n ≤ (9 * ε) ^ n := fun n => pow_le_pow_left₀ hm20 hm2 n
  have t0 : 0 ≤ μ ^ (2 : ℕ) ∧ μ ^ (2 : ℕ) ≤ 9 * ε ^ (2 : ℕ) := by
    refine ⟨(pow_nonneg hμ0 2), ?_⟩
    have hb : μ ^ (2 : ℕ) ≤ (3 * ε) ^ (2 : ℕ) := (pμ 2)
    have he : (3 * ε) ^ (2 : ℕ) = 9 * ε ^ (2 : ℕ) := by ring
    linarith
  rw [abs_le]
  constructor <;> linarith only [t0.1, t0.2]

theorem cumulant_gap_3 {μ m2 m3 ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 1000000) (hμ0 : 0 ≤ μ) (hμ : μ ≤ 3 * ε) (hm20 : 0 ≤ m2) (hm2 : m2 ≤ 9 * ε) (hm30 : 0 ≤ m3) (hm3 : m3 ≤ 27 * ε) :
    |(m3 - 3 * μ * m2 + 2 * μ ^ (3 : ℕ)) - m3| ≤ 82 * ε ^ (2 : ℕ) := by
  have hε1' : ε ≤ 1 := by linarith
  have hε2 : ε ^ (2 : ℕ) * (1 / 1000000) ≥ 0 := by positivity
  have hε3 : ∀ n : ℕ, 3 ≤ n → ε ^ n ≤ ε ^ (2 : ℕ) * (1 / 1000000) := by
    intro n hn
    have h1 : ε ^ n ≤ ε ^ (3 : ℕ) := pow_le_pow_of_le_one hε0 hε1' hn
    have h2 : ε ^ (3 : ℕ) = ε ^ (2 : ℕ) * ε := by ring
    have h3 : ε ^ (2 : ℕ) * ε ≤ ε ^ (2 : ℕ) * (1 / 1000000) := mul_le_mul_of_nonneg_left hε1 (by positivity)
    linarith
  have pμ : ∀ n : ℕ, μ ^ n ≤ (3 * ε) ^ n := fun n => pow_le_pow_left₀ hμ0 hμ n
  have pm2 : ∀ n : ℕ, m2 ^ n ≤ (9 * ε) ^ n := fun n => pow_le_pow_left₀ hm20 hm2 n
  have pm3 : ∀ n : ℕ, m3 ^ n ≤ (27 * ε) ^ n := fun n => pow_le_pow_left₀ hm30 hm3 n
  have t0 : 0 ≤ μ * m2 ∧ μ * m2 ≤ 27 * ε ^ (2 : ℕ) := by
    refine ⟨(mul_nonneg hμ0 hm20), ?_⟩
    have hb : μ * m2 ≤ (3 * ε) * (9 * ε) := (mul_le_mul_nn hμ0 hm20 hμ hm2)
    have he : (3 * ε) * (9 * ε) = 27 * ε ^ (2 : ℕ) := by ring
    linarith
  have t1 : 0 ≤ μ ^ (3 : ℕ) ∧ μ ^ (3 : ℕ) ≤ 27 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(pow_nonneg hμ0 3), ?_⟩
    have hb : μ ^ (3 : ℕ) ≤ (3 * ε) ^ (3 : ℕ) := (pμ 3)
    have he : (3 * ε) ^ (3 : ℕ) = 27 * ε ^ (3 : ℕ) := by ring
    have hd := hε3 3 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  rw [abs_le]
  constructor <;> linarith only [t0.1, t0.2, t1.1, t1.2]

theorem cumulant_gap_4 {μ m2 m3 m4 ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 1000000) (hμ0 : 0 ≤ μ) (hμ : μ ≤ 3 * ε) (hm20 : 0 ≤ m2) (hm2 : m2 ≤ 9 * ε) (hm30 : 0 ≤ m3) (hm3 : m3 ≤ 27 * ε) (hm40 : 0 ≤ m4) (hm4 : m4 ≤ 81 * ε) :
    |(m4 - 4 * μ * m3 - 3 * m2 ^ (2 : ℕ) + 12 * μ ^ (2 : ℕ) * m2 - 6 * μ ^ (4 : ℕ)) - m4| ≤ 568 * ε ^ (2 : ℕ) := by
  have hε1' : ε ≤ 1 := by linarith
  have hε2 : ε ^ (2 : ℕ) * (1 / 1000000) ≥ 0 := by positivity
  have hε3 : ∀ n : ℕ, 3 ≤ n → ε ^ n ≤ ε ^ (2 : ℕ) * (1 / 1000000) := by
    intro n hn
    have h1 : ε ^ n ≤ ε ^ (3 : ℕ) := pow_le_pow_of_le_one hε0 hε1' hn
    have h2 : ε ^ (3 : ℕ) = ε ^ (2 : ℕ) * ε := by ring
    have h3 : ε ^ (2 : ℕ) * ε ≤ ε ^ (2 : ℕ) * (1 / 1000000) := mul_le_mul_of_nonneg_left hε1 (by positivity)
    linarith
  have pμ : ∀ n : ℕ, μ ^ n ≤ (3 * ε) ^ n := fun n => pow_le_pow_left₀ hμ0 hμ n
  have pm2 : ∀ n : ℕ, m2 ^ n ≤ (9 * ε) ^ n := fun n => pow_le_pow_left₀ hm20 hm2 n
  have pm3 : ∀ n : ℕ, m3 ^ n ≤ (27 * ε) ^ n := fun n => pow_le_pow_left₀ hm30 hm3 n
  have pm4 : ∀ n : ℕ, m4 ^ n ≤ (81 * ε) ^ n := fun n => pow_le_pow_left₀ hm40 hm4 n
  have t0 : 0 ≤ μ * m3 ∧ μ * m3 ≤ 81 * ε ^ (2 : ℕ) := by
    refine ⟨(mul_nonneg hμ0 hm30), ?_⟩
    have hb : μ * m3 ≤ (3 * ε) * (27 * ε) := (mul_le_mul_nn hμ0 hm30 hμ hm3)
    have he : (3 * ε) * (27 * ε) = 81 * ε ^ (2 : ℕ) := by ring
    linarith
  have t1 : 0 ≤ m2 ^ (2 : ℕ) ∧ m2 ^ (2 : ℕ) ≤ 81 * ε ^ (2 : ℕ) := by
    refine ⟨(pow_nonneg hm20 2), ?_⟩
    have hb : m2 ^ (2 : ℕ) ≤ (9 * ε) ^ (2 : ℕ) := (pm2 2)
    have he : (9 * ε) ^ (2 : ℕ) = 81 * ε ^ (2 : ℕ) := by ring
    linarith
  have t2 : 0 ≤ μ ^ (2 : ℕ) * m2 ∧ μ ^ (2 : ℕ) * m2 ≤ 81 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(mul_nonneg (pow_nonneg hμ0 2) hm20), ?_⟩
    have hb : μ ^ (2 : ℕ) * m2 ≤ (3 * ε) ^ (2 : ℕ) * (9 * ε) := (mul_le_mul_nn (pow_nonneg hμ0 2) hm20 (pμ 2) hm2)
    have he : (3 * ε) ^ (2 : ℕ) * (9 * ε) = 81 * ε ^ (3 : ℕ) := by ring
    have hd := hε3 3 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  have t3 : 0 ≤ μ ^ (4 : ℕ) ∧ μ ^ (4 : ℕ) ≤ 81 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(pow_nonneg hμ0 4), ?_⟩
    have hb : μ ^ (4 : ℕ) ≤ (3 * ε) ^ (4 : ℕ) := (pμ 4)
    have he : (3 * ε) ^ (4 : ℕ) = 81 * ε ^ (4 : ℕ) := by ring
    have hd := hε3 4 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  rw [abs_le]
  constructor <;> linarith only [t0.1, t0.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2]

theorem cumulant_gap_5 {μ m2 m3 m4 m5 ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 1000000) (hμ0 : 0 ≤ μ) (hμ : μ ≤ 3 * ε) (hm20 : 0 ≤ m2) (hm2 : m2 ≤ 9 * ε) (hm30 : 0 ≤ m3) (hm3 : m3 ≤ 27 * ε) (hm40 : 0 ≤ m4) (hm4 : m4 ≤ 81 * ε) (hm50 : 0 ≤ m5) (hm5 : m5 ≤ 243 * ε) :
    |(m5 - 5 * μ * m4 - 10 * m2 * m3 + 20 * μ ^ (2 : ℕ) * m3 + 30 * μ * m2 ^ (2 : ℕ) - 60 * μ ^ (3 : ℕ) * m2 + 24 * μ ^ (5 : ℕ)) - m5| ≤ 3646 * ε ^ (2 : ℕ) := by
  have hε1' : ε ≤ 1 := by linarith
  have hε2 : ε ^ (2 : ℕ) * (1 / 1000000) ≥ 0 := by positivity
  have hε3 : ∀ n : ℕ, 3 ≤ n → ε ^ n ≤ ε ^ (2 : ℕ) * (1 / 1000000) := by
    intro n hn
    have h1 : ε ^ n ≤ ε ^ (3 : ℕ) := pow_le_pow_of_le_one hε0 hε1' hn
    have h2 : ε ^ (3 : ℕ) = ε ^ (2 : ℕ) * ε := by ring
    have h3 : ε ^ (2 : ℕ) * ε ≤ ε ^ (2 : ℕ) * (1 / 1000000) := mul_le_mul_of_nonneg_left hε1 (by positivity)
    linarith
  have pμ : ∀ n : ℕ, μ ^ n ≤ (3 * ε) ^ n := fun n => pow_le_pow_left₀ hμ0 hμ n
  have pm2 : ∀ n : ℕ, m2 ^ n ≤ (9 * ε) ^ n := fun n => pow_le_pow_left₀ hm20 hm2 n
  have pm3 : ∀ n : ℕ, m3 ^ n ≤ (27 * ε) ^ n := fun n => pow_le_pow_left₀ hm30 hm3 n
  have pm4 : ∀ n : ℕ, m4 ^ n ≤ (81 * ε) ^ n := fun n => pow_le_pow_left₀ hm40 hm4 n
  have pm5 : ∀ n : ℕ, m5 ^ n ≤ (243 * ε) ^ n := fun n => pow_le_pow_left₀ hm50 hm5 n
  have t0 : 0 ≤ μ * m4 ∧ μ * m4 ≤ 243 * ε ^ (2 : ℕ) := by
    refine ⟨(mul_nonneg hμ0 hm40), ?_⟩
    have hb : μ * m4 ≤ (3 * ε) * (81 * ε) := (mul_le_mul_nn hμ0 hm40 hμ hm4)
    have he : (3 * ε) * (81 * ε) = 243 * ε ^ (2 : ℕ) := by ring
    linarith
  have t1 : 0 ≤ m2 * m3 ∧ m2 * m3 ≤ 243 * ε ^ (2 : ℕ) := by
    refine ⟨(mul_nonneg hm20 hm30), ?_⟩
    have hb : m2 * m3 ≤ (9 * ε) * (27 * ε) := (mul_le_mul_nn hm20 hm30 hm2 hm3)
    have he : (9 * ε) * (27 * ε) = 243 * ε ^ (2 : ℕ) := by ring
    linarith
  have t2 : 0 ≤ μ ^ (2 : ℕ) * m3 ∧ μ ^ (2 : ℕ) * m3 ≤ 243 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(mul_nonneg (pow_nonneg hμ0 2) hm30), ?_⟩
    have hb : μ ^ (2 : ℕ) * m3 ≤ (3 * ε) ^ (2 : ℕ) * (27 * ε) := (mul_le_mul_nn (pow_nonneg hμ0 2) hm30 (pμ 2) hm3)
    have he : (3 * ε) ^ (2 : ℕ) * (27 * ε) = 243 * ε ^ (3 : ℕ) := by ring
    have hd := hε3 3 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  have t3 : 0 ≤ μ * m2 ^ (2 : ℕ) ∧ μ * m2 ^ (2 : ℕ) ≤ 243 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(mul_nonneg hμ0 (pow_nonneg hm20 2)), ?_⟩
    have hb : μ * m2 ^ (2 : ℕ) ≤ (3 * ε) * (9 * ε) ^ (2 : ℕ) := (mul_le_mul_nn hμ0 (pow_nonneg hm20 2) hμ (pm2 2))
    have he : (3 * ε) * (9 * ε) ^ (2 : ℕ) = 243 * ε ^ (3 : ℕ) := by ring
    have hd := hε3 3 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  have t4 : 0 ≤ μ ^ (3 : ℕ) * m2 ∧ μ ^ (3 : ℕ) * m2 ≤ 243 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(mul_nonneg (pow_nonneg hμ0 3) hm20), ?_⟩
    have hb : μ ^ (3 : ℕ) * m2 ≤ (3 * ε) ^ (3 : ℕ) * (9 * ε) := (mul_le_mul_nn (pow_nonneg hμ0 3) hm20 (pμ 3) hm2)
    have he : (3 * ε) ^ (3 : ℕ) * (9 * ε) = 243 * ε ^ (4 : ℕ) := by ring
    have hd := hε3 4 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  have t5 : 0 ≤ μ ^ (5 : ℕ) ∧ μ ^ (5 : ℕ) ≤ 243 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(pow_nonneg hμ0 5), ?_⟩
    have hb : μ ^ (5 : ℕ) ≤ (3 * ε) ^ (5 : ℕ) := (pμ 5)
    have he : (3 * ε) ^ (5 : ℕ) = 243 * ε ^ (5 : ℕ) := by ring
    have hd := hε3 5 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  rw [abs_le]
  constructor <;> linarith only [t0.1, t0.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2, t5.1, t5.2]

theorem cumulant_gap_6 {μ m2 m3 m4 m5 m6 ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 1000000) (hμ0 : 0 ≤ μ) (hμ : μ ≤ 3 * ε) (hm20 : 0 ≤ m2) (hm2 : m2 ≤ 9 * ε) (hm30 : 0 ≤ m3) (hm3 : m3 ≤ 27 * ε) (hm40 : 0 ≤ m4) (hm4 : m4 ≤ 81 * ε) (hm50 : 0 ≤ m5) (hm5 : m5 ≤ 243 * ε) (hm60 : 0 ≤ m6) (hm6 : m6 ≤ 729 * ε) :
    |(m6 - 6 * μ * m5 - 15 * m2 * m4 - 10 * m3 ^ (2 : ℕ) + 30 * μ ^ (2 : ℕ) * m4 + 120 * μ * m2 * m3 - 120 * μ ^ (3 : ℕ) * m3 + 30 * m2 ^ (3 : ℕ) - 270 * μ ^ (2 : ℕ) * m2 ^ (2 : ℕ) + 360 * μ ^ (4 : ℕ) * m2 - 120 * μ ^ (6 : ℕ)) - m6| ≤ 22600 * ε ^ (2 : ℕ) := by
  have hε1' : ε ≤ 1 := by linarith
  have hε2 : ε ^ (2 : ℕ) * (1 / 1000000) ≥ 0 := by positivity
  have hε3 : ∀ n : ℕ, 3 ≤ n → ε ^ n ≤ ε ^ (2 : ℕ) * (1 / 1000000) := by
    intro n hn
    have h1 : ε ^ n ≤ ε ^ (3 : ℕ) := pow_le_pow_of_le_one hε0 hε1' hn
    have h2 : ε ^ (3 : ℕ) = ε ^ (2 : ℕ) * ε := by ring
    have h3 : ε ^ (2 : ℕ) * ε ≤ ε ^ (2 : ℕ) * (1 / 1000000) := mul_le_mul_of_nonneg_left hε1 (by positivity)
    linarith
  have pμ : ∀ n : ℕ, μ ^ n ≤ (3 * ε) ^ n := fun n => pow_le_pow_left₀ hμ0 hμ n
  have pm2 : ∀ n : ℕ, m2 ^ n ≤ (9 * ε) ^ n := fun n => pow_le_pow_left₀ hm20 hm2 n
  have pm3 : ∀ n : ℕ, m3 ^ n ≤ (27 * ε) ^ n := fun n => pow_le_pow_left₀ hm30 hm3 n
  have pm4 : ∀ n : ℕ, m4 ^ n ≤ (81 * ε) ^ n := fun n => pow_le_pow_left₀ hm40 hm4 n
  have pm5 : ∀ n : ℕ, m5 ^ n ≤ (243 * ε) ^ n := fun n => pow_le_pow_left₀ hm50 hm5 n
  have pm6 : ∀ n : ℕ, m6 ^ n ≤ (729 * ε) ^ n := fun n => pow_le_pow_left₀ hm60 hm6 n
  have t0 : 0 ≤ μ * m5 ∧ μ * m5 ≤ 729 * ε ^ (2 : ℕ) := by
    refine ⟨(mul_nonneg hμ0 hm50), ?_⟩
    have hb : μ * m5 ≤ (3 * ε) * (243 * ε) := (mul_le_mul_nn hμ0 hm50 hμ hm5)
    have he : (3 * ε) * (243 * ε) = 729 * ε ^ (2 : ℕ) := by ring
    linarith
  have t1 : 0 ≤ m2 * m4 ∧ m2 * m4 ≤ 729 * ε ^ (2 : ℕ) := by
    refine ⟨(mul_nonneg hm20 hm40), ?_⟩
    have hb : m2 * m4 ≤ (9 * ε) * (81 * ε) := (mul_le_mul_nn hm20 hm40 hm2 hm4)
    have he : (9 * ε) * (81 * ε) = 729 * ε ^ (2 : ℕ) := by ring
    linarith
  have t2 : 0 ≤ m3 ^ (2 : ℕ) ∧ m3 ^ (2 : ℕ) ≤ 729 * ε ^ (2 : ℕ) := by
    refine ⟨(pow_nonneg hm30 2), ?_⟩
    have hb : m3 ^ (2 : ℕ) ≤ (27 * ε) ^ (2 : ℕ) := (pm3 2)
    have he : (27 * ε) ^ (2 : ℕ) = 729 * ε ^ (2 : ℕ) := by ring
    linarith
  have t3 : 0 ≤ μ ^ (2 : ℕ) * m4 ∧ μ ^ (2 : ℕ) * m4 ≤ 729 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(mul_nonneg (pow_nonneg hμ0 2) hm40), ?_⟩
    have hb : μ ^ (2 : ℕ) * m4 ≤ (3 * ε) ^ (2 : ℕ) * (81 * ε) := (mul_le_mul_nn (pow_nonneg hμ0 2) hm40 (pμ 2) hm4)
    have he : (3 * ε) ^ (2 : ℕ) * (81 * ε) = 729 * ε ^ (3 : ℕ) := by ring
    have hd := hε3 3 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  have t4 : 0 ≤ μ * m2 * m3 ∧ μ * m2 * m3 ≤ 729 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(mul_nonneg (mul_nonneg hμ0 hm20) hm30), ?_⟩
    have hb : μ * m2 * m3 ≤ (3 * ε) * (9 * ε) * (27 * ε) := (mul_le_mul_nn (mul_nonneg hμ0 hm20) hm30 (mul_le_mul_nn hμ0 hm20 hμ hm2) hm3)
    have he : (3 * ε) * (9 * ε) * (27 * ε) = 729 * ε ^ (3 : ℕ) := by ring
    have hd := hε3 3 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  have t5 : 0 ≤ μ ^ (3 : ℕ) * m3 ∧ μ ^ (3 : ℕ) * m3 ≤ 729 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(mul_nonneg (pow_nonneg hμ0 3) hm30), ?_⟩
    have hb : μ ^ (3 : ℕ) * m3 ≤ (3 * ε) ^ (3 : ℕ) * (27 * ε) := (mul_le_mul_nn (pow_nonneg hμ0 3) hm30 (pμ 3) hm3)
    have he : (3 * ε) ^ (3 : ℕ) * (27 * ε) = 729 * ε ^ (4 : ℕ) := by ring
    have hd := hε3 4 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  have t6 : 0 ≤ m2 ^ (3 : ℕ) ∧ m2 ^ (3 : ℕ) ≤ 729 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(pow_nonneg hm20 3), ?_⟩
    have hb : m2 ^ (3 : ℕ) ≤ (9 * ε) ^ (3 : ℕ) := (pm2 3)
    have he : (9 * ε) ^ (3 : ℕ) = 729 * ε ^ (3 : ℕ) := by ring
    have hd := hε3 3 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  have t7 : 0 ≤ μ ^ (2 : ℕ) * m2 ^ (2 : ℕ) ∧ μ ^ (2 : ℕ) * m2 ^ (2 : ℕ) ≤ 729 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(mul_nonneg (pow_nonneg hμ0 2) (pow_nonneg hm20 2)), ?_⟩
    have hb : μ ^ (2 : ℕ) * m2 ^ (2 : ℕ) ≤ (3 * ε) ^ (2 : ℕ) * (9 * ε) ^ (2 : ℕ) := (mul_le_mul_nn (pow_nonneg hμ0 2) (pow_nonneg hm20 2) (pμ 2) (pm2 2))
    have he : (3 * ε) ^ (2 : ℕ) * (9 * ε) ^ (2 : ℕ) = 729 * ε ^ (4 : ℕ) := by ring
    have hd := hε3 4 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  have t8 : 0 ≤ μ ^ (4 : ℕ) * m2 ∧ μ ^ (4 : ℕ) * m2 ≤ 729 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(mul_nonneg (pow_nonneg hμ0 4) hm20), ?_⟩
    have hb : μ ^ (4 : ℕ) * m2 ≤ (3 * ε) ^ (4 : ℕ) * (9 * ε) := (mul_le_mul_nn (pow_nonneg hμ0 4) hm20 (pμ 4) hm2)
    have he : (3 * ε) ^ (4 : ℕ) * (9 * ε) = 729 * ε ^ (5 : ℕ) := by ring
    have hd := hε3 5 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  have t9 : 0 ≤ μ ^ (6 : ℕ) ∧ μ ^ (6 : ℕ) ≤ 729 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(pow_nonneg hμ0 6), ?_⟩
    have hb : μ ^ (6 : ℕ) ≤ (3 * ε) ^ (6 : ℕ) := (pμ 6)
    have he : (3 * ε) ^ (6 : ℕ) = 729 * ε ^ (6 : ℕ) := by ring
    have hd := hε3 6 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  rw [abs_le]
  constructor <;> linarith only [t0.1, t0.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2, t5.1, t5.2, t6.1, t6.2, t7.1, t7.2, t8.1, t8.2, t9.1, t9.2]

theorem cumulant_gap_7 {μ m2 m3 m4 m5 m6 m7 ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 1000000) (hμ0 : 0 ≤ μ) (hμ : μ ≤ 3 * ε) (hm20 : 0 ≤ m2) (hm2 : m2 ≤ 9 * ε) (hm30 : 0 ≤ m3) (hm3 : m3 ≤ 27 * ε) (hm40 : 0 ≤ m4) (hm4 : m4 ≤ 81 * ε) (hm50 : 0 ≤ m5) (hm5 : m5 ≤ 243 * ε) (hm60 : 0 ≤ m6) (hm6 : m6 ≤ 729 * ε) (hm70 : 0 ≤ m7) (hm7 : m7 ≤ 2187 * ε) :
    |(m7 - 7 * μ * m6 - 21 * m2 * m5 - 35 * m3 * m4 + 42 * μ ^ (2 : ℕ) * m5 + 210 * μ * m2 * m4 + 140 * μ * m3 ^ (2 : ℕ) + 210 * m2 ^ (2 : ℕ) * m3 - 210 * μ ^ (3 : ℕ) * m4 - 1260 * μ ^ (2 : ℕ) * m2 * m3 - 630 * μ * m2 ^ (3 : ℕ) + 840 * μ ^ (4 : ℕ) * m3 + 2520 * μ ^ (3 : ℕ) * m2 ^ (2 : ℕ) - 2520 * μ ^ (5 : ℕ) * m2 + 720 * μ ^ (7 : ℕ)) - m7| ≤ 137802 * ε ^ (2 : ℕ) := by
  have hε1' : ε ≤ 1 := by linarith
  have hε2 : ε ^ (2 : ℕ) * (1 / 1000000) ≥ 0 := by positivity
  have hε3 : ∀ n : ℕ, 3 ≤ n → ε ^ n ≤ ε ^ (2 : ℕ) * (1 / 1000000) := by
    intro n hn
    have h1 : ε ^ n ≤ ε ^ (3 : ℕ) := pow_le_pow_of_le_one hε0 hε1' hn
    have h2 : ε ^ (3 : ℕ) = ε ^ (2 : ℕ) * ε := by ring
    have h3 : ε ^ (2 : ℕ) * ε ≤ ε ^ (2 : ℕ) * (1 / 1000000) := mul_le_mul_of_nonneg_left hε1 (by positivity)
    linarith
  have pμ : ∀ n : ℕ, μ ^ n ≤ (3 * ε) ^ n := fun n => pow_le_pow_left₀ hμ0 hμ n
  have pm2 : ∀ n : ℕ, m2 ^ n ≤ (9 * ε) ^ n := fun n => pow_le_pow_left₀ hm20 hm2 n
  have pm3 : ∀ n : ℕ, m3 ^ n ≤ (27 * ε) ^ n := fun n => pow_le_pow_left₀ hm30 hm3 n
  have pm4 : ∀ n : ℕ, m4 ^ n ≤ (81 * ε) ^ n := fun n => pow_le_pow_left₀ hm40 hm4 n
  have pm5 : ∀ n : ℕ, m5 ^ n ≤ (243 * ε) ^ n := fun n => pow_le_pow_left₀ hm50 hm5 n
  have pm6 : ∀ n : ℕ, m6 ^ n ≤ (729 * ε) ^ n := fun n => pow_le_pow_left₀ hm60 hm6 n
  have pm7 : ∀ n : ℕ, m7 ^ n ≤ (2187 * ε) ^ n := fun n => pow_le_pow_left₀ hm70 hm7 n
  have t0 : 0 ≤ μ * m6 ∧ μ * m6 ≤ 2187 * ε ^ (2 : ℕ) := by
    refine ⟨(mul_nonneg hμ0 hm60), ?_⟩
    have hb : μ * m6 ≤ (3 * ε) * (729 * ε) := (mul_le_mul_nn hμ0 hm60 hμ hm6)
    have he : (3 * ε) * (729 * ε) = 2187 * ε ^ (2 : ℕ) := by ring
    linarith
  have t1 : 0 ≤ m2 * m5 ∧ m2 * m5 ≤ 2187 * ε ^ (2 : ℕ) := by
    refine ⟨(mul_nonneg hm20 hm50), ?_⟩
    have hb : m2 * m5 ≤ (9 * ε) * (243 * ε) := (mul_le_mul_nn hm20 hm50 hm2 hm5)
    have he : (9 * ε) * (243 * ε) = 2187 * ε ^ (2 : ℕ) := by ring
    linarith
  have t2 : 0 ≤ m3 * m4 ∧ m3 * m4 ≤ 2187 * ε ^ (2 : ℕ) := by
    refine ⟨(mul_nonneg hm30 hm40), ?_⟩
    have hb : m3 * m4 ≤ (27 * ε) * (81 * ε) := (mul_le_mul_nn hm30 hm40 hm3 hm4)
    have he : (27 * ε) * (81 * ε) = 2187 * ε ^ (2 : ℕ) := by ring
    linarith
  have t3 : 0 ≤ μ ^ (2 : ℕ) * m5 ∧ μ ^ (2 : ℕ) * m5 ≤ 2187 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(mul_nonneg (pow_nonneg hμ0 2) hm50), ?_⟩
    have hb : μ ^ (2 : ℕ) * m5 ≤ (3 * ε) ^ (2 : ℕ) * (243 * ε) := (mul_le_mul_nn (pow_nonneg hμ0 2) hm50 (pμ 2) hm5)
    have he : (3 * ε) ^ (2 : ℕ) * (243 * ε) = 2187 * ε ^ (3 : ℕ) := by ring
    have hd := hε3 3 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  have t4 : 0 ≤ μ * m2 * m4 ∧ μ * m2 * m4 ≤ 2187 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(mul_nonneg (mul_nonneg hμ0 hm20) hm40), ?_⟩
    have hb : μ * m2 * m4 ≤ (3 * ε) * (9 * ε) * (81 * ε) := (mul_le_mul_nn (mul_nonneg hμ0 hm20) hm40 (mul_le_mul_nn hμ0 hm20 hμ hm2) hm4)
    have he : (3 * ε) * (9 * ε) * (81 * ε) = 2187 * ε ^ (3 : ℕ) := by ring
    have hd := hε3 3 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  have t5 : 0 ≤ μ * m3 ^ (2 : ℕ) ∧ μ * m3 ^ (2 : ℕ) ≤ 2187 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(mul_nonneg hμ0 (pow_nonneg hm30 2)), ?_⟩
    have hb : μ * m3 ^ (2 : ℕ) ≤ (3 * ε) * (27 * ε) ^ (2 : ℕ) := (mul_le_mul_nn hμ0 (pow_nonneg hm30 2) hμ (pm3 2))
    have he : (3 * ε) * (27 * ε) ^ (2 : ℕ) = 2187 * ε ^ (3 : ℕ) := by ring
    have hd := hε3 3 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  have t6 : 0 ≤ m2 ^ (2 : ℕ) * m3 ∧ m2 ^ (2 : ℕ) * m3 ≤ 2187 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(mul_nonneg (pow_nonneg hm20 2) hm30), ?_⟩
    have hb : m2 ^ (2 : ℕ) * m3 ≤ (9 * ε) ^ (2 : ℕ) * (27 * ε) := (mul_le_mul_nn (pow_nonneg hm20 2) hm30 (pm2 2) hm3)
    have he : (9 * ε) ^ (2 : ℕ) * (27 * ε) = 2187 * ε ^ (3 : ℕ) := by ring
    have hd := hε3 3 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  have t7 : 0 ≤ μ ^ (3 : ℕ) * m4 ∧ μ ^ (3 : ℕ) * m4 ≤ 2187 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(mul_nonneg (pow_nonneg hμ0 3) hm40), ?_⟩
    have hb : μ ^ (3 : ℕ) * m4 ≤ (3 * ε) ^ (3 : ℕ) * (81 * ε) := (mul_le_mul_nn (pow_nonneg hμ0 3) hm40 (pμ 3) hm4)
    have he : (3 * ε) ^ (3 : ℕ) * (81 * ε) = 2187 * ε ^ (4 : ℕ) := by ring
    have hd := hε3 4 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  have t8 : 0 ≤ μ ^ (2 : ℕ) * m2 * m3 ∧ μ ^ (2 : ℕ) * m2 * m3 ≤ 2187 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(mul_nonneg (mul_nonneg (pow_nonneg hμ0 2) hm20) hm30), ?_⟩
    have hb : μ ^ (2 : ℕ) * m2 * m3 ≤ (3 * ε) ^ (2 : ℕ) * (9 * ε) * (27 * ε) := (mul_le_mul_nn (mul_nonneg (pow_nonneg hμ0 2) hm20) hm30 (mul_le_mul_nn (pow_nonneg hμ0 2) hm20 (pμ 2) hm2) hm3)
    have he : (3 * ε) ^ (2 : ℕ) * (9 * ε) * (27 * ε) = 2187 * ε ^ (4 : ℕ) := by ring
    have hd := hε3 4 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  have t9 : 0 ≤ μ * m2 ^ (3 : ℕ) ∧ μ * m2 ^ (3 : ℕ) ≤ 2187 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(mul_nonneg hμ0 (pow_nonneg hm20 3)), ?_⟩
    have hb : μ * m2 ^ (3 : ℕ) ≤ (3 * ε) * (9 * ε) ^ (3 : ℕ) := (mul_le_mul_nn hμ0 (pow_nonneg hm20 3) hμ (pm2 3))
    have he : (3 * ε) * (9 * ε) ^ (3 : ℕ) = 2187 * ε ^ (4 : ℕ) := by ring
    have hd := hε3 4 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  have t10 : 0 ≤ μ ^ (4 : ℕ) * m3 ∧ μ ^ (4 : ℕ) * m3 ≤ 2187 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(mul_nonneg (pow_nonneg hμ0 4) hm30), ?_⟩
    have hb : μ ^ (4 : ℕ) * m3 ≤ (3 * ε) ^ (4 : ℕ) * (27 * ε) := (mul_le_mul_nn (pow_nonneg hμ0 4) hm30 (pμ 4) hm3)
    have he : (3 * ε) ^ (4 : ℕ) * (27 * ε) = 2187 * ε ^ (5 : ℕ) := by ring
    have hd := hε3 5 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  have t11 : 0 ≤ μ ^ (3 : ℕ) * m2 ^ (2 : ℕ) ∧ μ ^ (3 : ℕ) * m2 ^ (2 : ℕ) ≤ 2187 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(mul_nonneg (pow_nonneg hμ0 3) (pow_nonneg hm20 2)), ?_⟩
    have hb : μ ^ (3 : ℕ) * m2 ^ (2 : ℕ) ≤ (3 * ε) ^ (3 : ℕ) * (9 * ε) ^ (2 : ℕ) := (mul_le_mul_nn (pow_nonneg hμ0 3) (pow_nonneg hm20 2) (pμ 3) (pm2 2))
    have he : (3 * ε) ^ (3 : ℕ) * (9 * ε) ^ (2 : ℕ) = 2187 * ε ^ (5 : ℕ) := by ring
    have hd := hε3 5 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  have t12 : 0 ≤ μ ^ (5 : ℕ) * m2 ∧ μ ^ (5 : ℕ) * m2 ≤ 2187 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(mul_nonneg (pow_nonneg hμ0 5) hm20), ?_⟩
    have hb : μ ^ (5 : ℕ) * m2 ≤ (3 * ε) ^ (5 : ℕ) * (9 * ε) := (mul_le_mul_nn (pow_nonneg hμ0 5) hm20 (pμ 5) hm2)
    have he : (3 * ε) ^ (5 : ℕ) * (9 * ε) = 2187 * ε ^ (6 : ℕ) := by ring
    have hd := hε3 6 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  have t13 : 0 ≤ μ ^ (7 : ℕ) ∧ μ ^ (7 : ℕ) ≤ 2187 * (ε ^ (2 : ℕ) * (1 / 1000000)) := by
    refine ⟨(pow_nonneg hμ0 7), ?_⟩
    have hb : μ ^ (7 : ℕ) ≤ (3 * ε) ^ (7 : ℕ) := (pμ 7)
    have he : (3 * ε) ^ (7 : ℕ) = 2187 * ε ^ (7 : ℕ) := by ring
    have hd := hε3 7 (by norm_num)
    rw [he] at hb
    calc _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  rw [abs_le]
  constructor <;> linarith only [t0.1, t0.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2, t5.1, t5.2, t6.1, t6.2, t7.1, t7.2, t8.1, t8.2, t9.1, t9.2, t10.1, t10.2, t11.1, t11.2, t12.1, t12.2, t13.1, t13.2]


/-! ## Regime-I inputs -/

theorem regimeOne_moment_bound7 {x : ℝ} (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (m : ℕ) (hm : m ≤ 7) :
    thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) m ≤
      3 ^ m * regimeOneLikelihoodScale x := by
  have hx : 0 ≤ x := (regimeOne_pos_of_six_le hA).le
  apply thetaCuspLikelihoodNormalizedMoment_le_regimeOneScale m hx
  have hm' : (m : ℝ) ≤ 7 := by exact_mod_cast hm
  have := Real.pi_lt_d2
  norm_num at this
  linarith

/-- `|NM_m − M_m| ≤ 2·3^m ε²` in regime I. -/
theorem abs_normalizedMoment_sub_moment_le {x : ℝ}
    (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) (m : ℕ) (hm : m ≤ 7) :
    |thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) m -
        thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) m| ≤
      2 * 3 ^ m * regimeOneLikelihoodScale x ^ (2 : ℕ) := by
  have hx : 0 ≤ x := (regimeOne_pos_of_six_le hA).le
  have hB : 0 < thetaCuspLikelihoodCoordinate x := thetaCuspLikelihoodCoordinate_pos hx
  set B := thetaCuspLikelihoodCoordinate x with hBdef
  set ε := regimeOneLikelihoodScale x with hεdef
  have hZ : thetaCuspLikelihoodPartition B = 1 + thetaCuspHigherLikelihoodSpectralMoment B 0 := by
    unfold thetaCuspLikelihoodPartition
    rw [thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
  have hM0nn := thetaCuspHigherLikelihoodSpectralMoment_nonneg (B := B) 0
  have hMmnn := thetaCuspHigherLikelihoodSpectralMoment_nonneg (B := B) m
  have hZpos : 0 < 1 + thetaCuspHigherLikelihoodSpectralMoment B 0 := by linarith
  have hNM0 : thetaCuspLikelihoodNormalizedMoment B 0 ≤ ε := by
    simpa using regimeOne_moment_bound7 hA 0 (by norm_num)
  have hNMm : thetaCuspLikelihoodNormalizedMoment B m ≤ 3 ^ m * ε := regimeOne_moment_bound7 hA m hm
  have hNMnn : 0 ≤ thetaCuspLikelihoodNormalizedMoment B m :=
    thetaCuspLikelihoodNormalizedMoment_nonneg hB m
  have hε : ε ≤ 5 / 10000000 := regimeOneLikelihoodScale_le_of_six_le hA
  have hM0 : thetaCuspHigherLikelihoodSpectralMoment B 0 =
      thetaCuspLikelihoodNormalizedMoment B 0 * (1 + thetaCuspHigherLikelihoodSpectralMoment B 0) := by
    unfold thetaCuspLikelihoodNormalizedMoment
    rw [hZ]
    field_simp
  have hM0' : thetaCuspHigherLikelihoodSpectralMoment B 0 ≤ 2 * ε := by
    have hNM0nn : 0 ≤ thetaCuspLikelihoodNormalizedMoment B 0 :=
      thetaCuspLikelihoodNormalizedMoment_nonneg hB 0
    nlinarith
  have hkey : thetaCuspHigherLikelihoodSpectralMoment B m - thetaCuspLikelihoodNormalizedMoment B m =
      thetaCuspLikelihoodNormalizedMoment B m * thetaCuspHigherLikelihoodSpectralMoment B 0 := by
    unfold thetaCuspLikelihoodNormalizedMoment
    rw [hZ]
    field_simp
    ring
  rw [abs_sub_comm, hkey, abs_of_nonneg (mul_nonneg hNMnn hM0nn)]
  calc thetaCuspLikelihoodNormalizedMoment B m * thetaCuspHigherLikelihoodSpectralMoment B 0
      ≤ (3 ^ m * ε) * (2 * ε) := mul_le_mul_nn hNMnn hM0nn hNMm hM0'
    _ = 2 * 3 ^ m * ε ^ (2 : ℕ) := by ring

/-- **Deviation of every cumulant from its second-atom profile** in regime I. -/
theorem sharpJet_deviation_bounds {x : ℝ} (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    let B := thetaCuspLikelihoodCoordinate x
    let ε := regimeOneLikelihoodScale x
    let E8 := Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) / 399
    |thetaCuspLikelihoodMean B - secondAtomMomentProfile 1 B| ≤ (0 + 2 * 3) * ε ^ (2 : ℕ) + 8 * E8 ∧
    |thetaCuspLikelihoodVariance B - secondAtomMomentProfile 2 B| ≤ (9 + 2 * 9) * ε ^ (2 : ℕ) + 64 * E8 ∧
    |thetaCuspLikelihoodThirdCumulant B - secondAtomMomentProfile 3 B| ≤
      (82 + 2 * 27) * ε ^ (2 : ℕ) + 512 * E8 ∧
    |thetaCuspLikelihoodFourthCumulant B - secondAtomMomentProfile 4 B| ≤
      (568 + 2 * 81) * ε ^ (2 : ℕ) + 4096 * E8 ∧
    |thetaCuspLikelihoodFifthCumulant B - secondAtomMomentProfile 5 B| ≤
      (3646 + 2 * 243) * ε ^ (2 : ℕ) + 32768 * E8 ∧
    |thetaCuspLikelihoodSixthCumulant B - secondAtomMomentProfile 6 B| ≤
      (22600 + 2 * 729) * ε ^ (2 : ℕ) + 262144 * E8 ∧
    |thetaCuspLikelihoodSeventhCumulant B - secondAtomMomentProfile 7 B| ≤
      (137802 + 2 * 2187) * ε ^ (2 : ℕ) + 2097152 * E8 := by
  intro B ε E8
  have hx : 0 ≤ x := (regimeOne_pos_of_six_le hA).le
  have hB : 0 < B := thetaCuspLikelihoodCoordinate_pos hx
  have hε0 : 0 ≤ ε := (regimeOneLikelihoodScale_pos x).le
  have hε1 : ε ≤ 1 / 1000000 := by
    have := regimeOneLikelihoodScale_le_of_six_le hA
    show regimeOneLikelihoodScale x ≤ 1 / 1000000
    linarith
  obtain ⟨hμ0, hμ, -, -, -, -⟩ := regimeOne_cumulant_bounds hA
  have hn : ∀ m, 0 ≤ thetaCuspLikelihoodNormalizedMoment B m :=
    fun m => thetaCuspLikelihoodNormalizedMoment_nonneg hB m
  have hu : ∀ m, m ≤ 7 → thetaCuspLikelihoodNormalizedMoment B m ≤ 3 ^ m * ε :=
    fun m hm => regimeOne_moment_bound7 hA m hm
  have hu2 : thetaCuspLikelihoodNormalizedMoment B 2 ≤ 9 * ε := by
    have := hu 2 (by norm_num); norm_num at this; linarith
  have hu3 : thetaCuspLikelihoodNormalizedMoment B 3 ≤ 27 * ε := by
    have := hu 3 (by norm_num); norm_num at this; linarith
  have hu4 : thetaCuspLikelihoodNormalizedMoment B 4 ≤ 81 * ε := by
    have := hu 4 (by norm_num); norm_num at this; linarith
  have hu5 : thetaCuspLikelihoodNormalizedMoment B 5 ≤ 243 * ε := by
    have := hu 5 (by norm_num); norm_num at this; linarith
  have hu6 : thetaCuspLikelihoodNormalizedMoment B 6 ≤ 729 * ε := by
    have := hu 6 (by norm_num); norm_num at this; linarith
  have hu7 : thetaCuspLikelihoodNormalizedMoment B 7 ≤ 2187 * ε := by
    have := hu 7 (by norm_num); norm_num at this; linarith
  -- deep tail and decomposition
  have hT : ∀ m, m ≤ 7 → thetaCuspDeepTailMoment B m ≤ 8 ^ m * E8 := by
    intro m hm
    have := thetaCuspDeepTailMoment_le_regimeOne m hm hA
    show thetaCuspDeepTailMoment B m ≤ 8 ^ m * (Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) / 399)
    linarith [this]
  have hT0 : ∀ m, 0 ≤ thetaCuspDeepTailMoment B m := fun m => thetaCuspDeepTailMoment_nonneg B m
  have hdec : ∀ m, m ≤ 7 → thetaCuspHigherLikelihoodSpectralMoment B m =
      secondAtomMomentProfile m B + thetaCuspDeepTailMoment B m := by
    intro m hm
    rw [thetaCuspHigherLikelihoodSpectralMoment_eq_second_add_deep hB m,
      thetaCuspSecondAtomMoment_eq_profile m hm B hB]
  have hnm : ∀ m, m ≤ 7 → |thetaCuspLikelihoodNormalizedMoment B m -
      thetaCuspHigherLikelihoodSpectralMoment B m| ≤ 2 * 3 ^ m * ε ^ (2 : ℕ) :=
    fun m hm => abs_normalizedMoment_sub_moment_le hA m hm
  -- generic combination
  have comb : ∀ (κ : ℝ) (m : ℕ) (C : ℝ), m ≤ 7 →
      |κ - thetaCuspLikelihoodNormalizedMoment B m| ≤ C * ε ^ (2 : ℕ) →
      |κ - secondAtomMomentProfile m B| ≤ (C + 2 * 3 ^ m) * ε ^ (2 : ℕ) + 8 ^ m * E8 := by
    intro κ m C hm hg
    have h1 := abs_sub_le κ (thetaCuspLikelihoodNormalizedMoment B m) (secondAtomMomentProfile m B)
    have h2 := abs_sub_le (thetaCuspLikelihoodNormalizedMoment B m)
      (thetaCuspHigherLikelihoodSpectralMoment B m) (secondAtomMomentProfile m B)
    have h3 : |thetaCuspHigherLikelihoodSpectralMoment B m - secondAtomMomentProfile m B| ≤
        8 ^ m * E8 := by
      rw [hdec m hm, add_sub_cancel_left, abs_of_nonneg (hT0 m)]
      exact hT m hm
    have h4 := hnm m hm
    nlinarith [h1, h2, h3, h4, hg]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hg : |thetaCuspLikelihoodMean B - thetaCuspLikelihoodNormalizedMoment B 1| ≤ 0 * ε ^ (2 : ℕ) := by
      have : thetaCuspLikelihoodMean B = thetaCuspLikelihoodNormalizedMoment B 1 := rfl
      rw [this, sub_self, abs_zero]; simp
    have := comb _ 1 0 (by norm_num) hg
    norm_num at this ⊢
    linarith
  · have hg := cumulant_gap_2 hε0 hε1 hμ0 hμ (hn 2) hu2
    have e : thetaCuspLikelihoodVariance B - thetaCuspLikelihoodNormalizedMoment B 2 =
        (thetaCuspLikelihoodNormalizedMoment B 2 - thetaCuspLikelihoodMean B ^ (2 : ℕ)) -
          thetaCuspLikelihoodNormalizedMoment B 2 := by
      unfold thetaCuspLikelihoodVariance thetaCuspLikelihoodNormalizedMoment; ring
    have := comb _ 2 9 (by norm_num) (by rw [e]; exact hg)
    norm_num at this ⊢
    linarith
  · have hg := cumulant_gap_3 hε0 hε1 hμ0 hμ (hn 2) hu2 (hn 3) hu3
    have e : thetaCuspLikelihoodThirdCumulant B - thetaCuspLikelihoodNormalizedMoment B 3 =
        (thetaCuspLikelihoodNormalizedMoment B 3 - 3 * thetaCuspLikelihoodMean B *
          thetaCuspLikelihoodNormalizedMoment B 2 + 2 * thetaCuspLikelihoodMean B ^ (3 : ℕ)) -
          thetaCuspLikelihoodNormalizedMoment B 3 := by
      unfold thetaCuspLikelihoodThirdCumulant thetaCuspLikelihoodNormalizedMoment; ring
    have := comb _ 3 82 (by norm_num) (by rw [e]; exact hg)
    norm_num at this ⊢
    linarith
  · have hg := cumulant_gap_4 hε0 hε1 hμ0 hμ (hn 2) hu2 (hn 3) hu3 (hn 4) hu4
    have e : thetaCuspLikelihoodFourthCumulant B - thetaCuspLikelihoodNormalizedMoment B 4 =
        (thetaCuspLikelihoodNormalizedMoment B 4 - 4 * thetaCuspLikelihoodMean B *
          thetaCuspLikelihoodNormalizedMoment B 3 - 3 * thetaCuspLikelihoodNormalizedMoment B 2 ^ (2 : ℕ) +
          12 * thetaCuspLikelihoodMean B ^ (2 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 2 -
          6 * thetaCuspLikelihoodMean B ^ (4 : ℕ)) - thetaCuspLikelihoodNormalizedMoment B 4 := by
      unfold thetaCuspLikelihoodFourthCumulant; ring
    have := comb _ 4 568 (by norm_num) (by rw [e]; exact hg)
    norm_num at this ⊢
    linarith
  · have hg := cumulant_gap_5 hε0 hε1 hμ0 hμ (hn 2) hu2 (hn 3) hu3 (hn 4) hu4 (hn 5) hu5
    have e : thetaCuspLikelihoodFifthCumulant B - thetaCuspLikelihoodNormalizedMoment B 5 =
        (thetaCuspLikelihoodNormalizedMoment B 5 - 5 * thetaCuspLikelihoodMean B *
          thetaCuspLikelihoodNormalizedMoment B 4 - 10 * thetaCuspLikelihoodNormalizedMoment B 2 *
          thetaCuspLikelihoodNormalizedMoment B 3 + 20 * thetaCuspLikelihoodMean B ^ (2 : ℕ) *
          thetaCuspLikelihoodNormalizedMoment B 3 + 30 * thetaCuspLikelihoodMean B *
          thetaCuspLikelihoodNormalizedMoment B 2 ^ (2 : ℕ) - 60 * thetaCuspLikelihoodMean B ^ (3 : ℕ) *
          thetaCuspLikelihoodNormalizedMoment B 2 + 24 * thetaCuspLikelihoodMean B ^ (5 : ℕ)) -
          thetaCuspLikelihoodNormalizedMoment B 5 := by
      unfold thetaCuspLikelihoodFifthCumulant; ring
    have := comb _ 5 3646 (by norm_num) (by rw [e]; exact hg)
    norm_num at this ⊢
    linarith
  · have hg := cumulant_gap_6 hε0 hε1 hμ0 hμ (hn 2) hu2 (hn 3) hu3 (hn 4) hu4 (hn 5) hu5 (hn 6) hu6
    have e : thetaCuspLikelihoodSixthCumulant B - thetaCuspLikelihoodNormalizedMoment B 6 =
        (thetaCuspLikelihoodNormalizedMoment B 6 - 6 * thetaCuspLikelihoodMean B *
          thetaCuspLikelihoodNormalizedMoment B 5 - 15 * thetaCuspLikelihoodNormalizedMoment B 2 *
          thetaCuspLikelihoodNormalizedMoment B 4 - 10 * thetaCuspLikelihoodNormalizedMoment B 3 ^ (2 : ℕ) +
          30 * thetaCuspLikelihoodMean B ^ (2 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 4 +
          120 * thetaCuspLikelihoodMean B * thetaCuspLikelihoodNormalizedMoment B 2 *
          thetaCuspLikelihoodNormalizedMoment B 3 - 120 * thetaCuspLikelihoodMean B ^ (3 : ℕ) *
          thetaCuspLikelihoodNormalizedMoment B 3 + 30 * thetaCuspLikelihoodNormalizedMoment B 2 ^ (3 : ℕ) -
          270 * thetaCuspLikelihoodMean B ^ (2 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 2 ^ (2 : ℕ) +
          360 * thetaCuspLikelihoodMean B ^ (4 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 2 -
          120 * thetaCuspLikelihoodMean B ^ (6 : ℕ)) - thetaCuspLikelihoodNormalizedMoment B 6 := by
      unfold thetaCuspLikelihoodSixthCumulant; ring
    have := comb _ 6 22600 (by norm_num) (by rw [e]; exact hg)
    norm_num at this ⊢
    linarith
  · have hg := cumulant_gap_7 hε0 hε1 hμ0 hμ (hn 2) hu2 (hn 3) hu3 (hn 4) hu4 (hn 5) hu5 (hn 6) hu6
      (hn 7) hu7
    have e : thetaCuspLikelihoodSeventhCumulant B - thetaCuspLikelihoodNormalizedMoment B 7 =
        (thetaCuspLikelihoodNormalizedMoment B 7 - 7 * thetaCuspLikelihoodMean B *
          thetaCuspLikelihoodNormalizedMoment B 6 - 21 * thetaCuspLikelihoodNormalizedMoment B 2 *
          thetaCuspLikelihoodNormalizedMoment B 5 - 35 * thetaCuspLikelihoodNormalizedMoment B 3 *
          thetaCuspLikelihoodNormalizedMoment B 4 + 42 * thetaCuspLikelihoodMean B ^ (2 : ℕ) *
          thetaCuspLikelihoodNormalizedMoment B 5 + 210 * thetaCuspLikelihoodMean B *
          thetaCuspLikelihoodNormalizedMoment B 2 * thetaCuspLikelihoodNormalizedMoment B 4 +
          140 * thetaCuspLikelihoodMean B * thetaCuspLikelihoodNormalizedMoment B 3 ^ (2 : ℕ) +
          210 * thetaCuspLikelihoodNormalizedMoment B 2 ^ (2 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 3 -
          210 * thetaCuspLikelihoodMean B ^ (3 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 4 -
          1260 * thetaCuspLikelihoodMean B ^ (2 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 2 *
          thetaCuspLikelihoodNormalizedMoment B 3 - 630 * thetaCuspLikelihoodMean B *
          thetaCuspLikelihoodNormalizedMoment B 2 ^ (3 : ℕ) + 840 * thetaCuspLikelihoodMean B ^ (4 : ℕ) *
          thetaCuspLikelihoodNormalizedMoment B 3 + 2520 * thetaCuspLikelihoodMean B ^ (3 : ℕ) *
          thetaCuspLikelihoodNormalizedMoment B 2 ^ (2 : ℕ) - 2520 * thetaCuspLikelihoodMean B ^ (5 : ℕ) *
          thetaCuspLikelihoodNormalizedMoment B 2 + 720 * thetaCuspLikelihoodMean B ^ (7 : ℕ)) -
          thetaCuspLikelihoodNormalizedMoment B 7 := by
      unfold thetaCuspLikelihoodSeventhCumulant; ring
    have := comb _ 7 137802 (by norm_num) (by rw [e]; exact hg)
    norm_num at this ⊢
    linarith

/-! ## The sharp jet bounds -/

/-- **Sharp bound for the `2`-th jet** in regime I. -/
theorem sharpJet_bound_2 {x : ℝ} (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspLikelihoodSourceLogPartitionJetTwo x -
        sharpJetMain2 (thetaCuspSingleAtomReflectionScale 1 x)| ≤
      188 * thetaCuspSingleAtomReflectionScale 1 x ^ (2 : ℕ) * regimeOneLikelihoodScale x ^ (2 : ℕ) +
      262 * thetaCuspSingleAtomReflectionScale 1 x ^ (2 : ℕ) *
        (Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) / 399) := by
  obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6, hk7⟩ := sharpJet_deviation_bounds hA
  have hBA : thetaCuspLikelihoodCoordinate x = thetaCuspSingleAtomReflectionScale 1 x - 3 / 2 :=
    thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hA0 : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hid := sharpJet_identity_2 (thetaCuspSingleAtomReflectionScale 1 x) (by linarith)
  rw [← hBA] at hid
  have hE80 : 0 ≤ Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) / 399 := by positivity
  have hε20 : 0 ≤ regimeOneLikelihoodScale x ^ (2 : ℕ) := by positivity
  generalize hAg : thetaCuspSingleAtomReflectionScale 1 x = A at *
  generalize hBg : thetaCuspLikelihoodCoordinate x = B at *
  generalize hεg : regimeOneLikelihoodScale x = ε at *
  generalize hEg : Real.exp (-(8 * (A - Real.pi))) / 399 = E8 at *
  unfold thetaCuspLikelihoodSourceLogPartitionJetTwo
  rw [hAg, hBg]
  unfold sharpJetMain2
  rw [← hid]
  have hAj2 : 0 ≤ A ^ (2 : ℕ) := by positivity
  have u2 := mul_le_mul_of_nonneg_left (abs_le.mp hk2).2 hAj2
  have l2 := mul_le_mul_of_nonneg_left (abs_le.mp hk2).1 hAj2
  have hAj1 : 0 ≤ A := by positivity
  have u1 := mul_le_mul_of_nonneg_left (abs_le.mp hk1).2 hAj1
  have l1 := mul_le_mul_of_nonneg_left (abs_le.mp hk1).1 hAj1
  have hp1 : 6 ^ (1 : ℕ) * A ≤ A ^ (2 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hA 1
    calc 6 ^ (1 : ℕ) * A ≤ A * A := mul_le_mul_of_nonneg_right (by simpa using this) hAj1
      _ = A ^ (2 : ℕ) := by ring
  have hpe1 := mul_le_mul_of_nonneg_right hp1 hε20
  have hpE1 := mul_le_mul_of_nonneg_right hp1 hE80
  have hnn1 : 0 ≤ A ^ (2 : ℕ) * ε ^ (2 : ℕ) := mul_nonneg hAj2 hε20
  have hnn2 : 0 ≤ A ^ (2 : ℕ) * E8 := mul_nonneg hAj2 hE80
  rw [abs_le]
  constructor <;> linarith only [u2, l2, u1, l1, hpe1, hpE1, hnn1, hnn2]

/-- **Sharp bound for the `3`-th jet** in regime I. -/
theorem sharpJet_bound_3 {x : ℝ} (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspLikelihoodSourceLogPartitionJetThree x -
        sharpJetMain3 (thetaCuspSingleAtomReflectionScale 1 x)| ≤
      1703 * thetaCuspSingleAtomReflectionScale 1 x ^ (3 : ℕ) * regimeOneLikelihoodScale x ^ (2 : ℕ) +
      4354 * thetaCuspSingleAtomReflectionScale 1 x ^ (3 : ℕ) *
        (Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) / 399) := by
  obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6, hk7⟩ := sharpJet_deviation_bounds hA
  have hBA : thetaCuspLikelihoodCoordinate x = thetaCuspSingleAtomReflectionScale 1 x - 3 / 2 :=
    thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hA0 : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hid := sharpJet_identity_3 (thetaCuspSingleAtomReflectionScale 1 x) (by linarith)
  rw [← hBA] at hid
  have hE80 : 0 ≤ Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) / 399 := by positivity
  have hε20 : 0 ≤ regimeOneLikelihoodScale x ^ (2 : ℕ) := by positivity
  generalize hAg : thetaCuspSingleAtomReflectionScale 1 x = A at *
  generalize hBg : thetaCuspLikelihoodCoordinate x = B at *
  generalize hεg : regimeOneLikelihoodScale x = ε at *
  generalize hEg : Real.exp (-(8 * (A - Real.pi))) / 399 = E8 at *
  unfold thetaCuspLikelihoodSourceLogPartitionJetThree
  rw [hAg, hBg]
  unfold sharpJetMain3
  rw [← hid]
  have hAj3 : 0 ≤ A ^ (3 : ℕ) := by positivity
  have u3 := mul_le_mul_of_nonneg_left (abs_le.mp hk3).2 hAj3
  have l3 := mul_le_mul_of_nonneg_left (abs_le.mp hk3).1 hAj3
  have hAj2 : 0 ≤ A ^ (2 : ℕ) := by positivity
  have u2 := mul_le_mul_of_nonneg_left (abs_le.mp hk2).2 hAj2
  have l2 := mul_le_mul_of_nonneg_left (abs_le.mp hk2).1 hAj2
  have hp2 : 6 ^ (1 : ℕ) * A ^ (2 : ℕ) ≤ A ^ (3 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hA 1
    calc 6 ^ (1 : ℕ) * A ^ (2 : ℕ) ≤ A * A ^ (2 : ℕ) := mul_le_mul_of_nonneg_right (by simpa using this) hAj2
      _ = A ^ (3 : ℕ) := by ring
  have hpe2 := mul_le_mul_of_nonneg_right hp2 hε20
  have hpE2 := mul_le_mul_of_nonneg_right hp2 hE80
  have hAj1 : 0 ≤ A := by positivity
  have u1 := mul_le_mul_of_nonneg_left (abs_le.mp hk1).2 hAj1
  have l1 := mul_le_mul_of_nonneg_left (abs_le.mp hk1).1 hAj1
  have hp1 : 6 ^ (2 : ℕ) * A ≤ A ^ (3 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hA 2
    calc 6 ^ (2 : ℕ) * A ≤ A ^ (2 : ℕ) * A := mul_le_mul_of_nonneg_right this hAj1
      _ = A ^ (3 : ℕ) := by ring
  have hpe1 := mul_le_mul_of_nonneg_right hp1 hε20
  have hpE1 := mul_le_mul_of_nonneg_right hp1 hE80
  have hnn1 : 0 ≤ A ^ (3 : ℕ) * ε ^ (2 : ℕ) := mul_nonneg hAj3 hε20
  have hnn2 : 0 ≤ A ^ (3 : ℕ) * E8 := mul_nonneg hAj3 hE80
  rw [abs_le]
  constructor <;> linarith only [u3, l3, u2, l2, u1, l1, hpe2, hpE2, hpe1, hpE1, hnn1, hnn2]

/-- **Sharp bound for the `4`-th jet** in regime I. -/
theorem sharpJet_bound_4 {x : ℝ} (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspLikelihoodSourceLogPartitionJetFour x -
        sharpJetMain4 (thetaCuspSingleAtomReflectionScale 1 x)| ≤
      17453 * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) * regimeOneLikelihoodScale x ^ (2 : ℕ) +
      73928 * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) *
        (Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) / 399) := by
  obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6, hk7⟩ := sharpJet_deviation_bounds hA
  have hBA : thetaCuspLikelihoodCoordinate x = thetaCuspSingleAtomReflectionScale 1 x - 3 / 2 :=
    thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hA0 : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hid := sharpJet_identity_4 (thetaCuspSingleAtomReflectionScale 1 x) (by linarith)
  rw [← hBA] at hid
  have hE80 : 0 ≤ Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) / 399 := by positivity
  have hε20 : 0 ≤ regimeOneLikelihoodScale x ^ (2 : ℕ) := by positivity
  generalize hAg : thetaCuspSingleAtomReflectionScale 1 x = A at *
  generalize hBg : thetaCuspLikelihoodCoordinate x = B at *
  generalize hεg : regimeOneLikelihoodScale x = ε at *
  generalize hEg : Real.exp (-(8 * (A - Real.pi))) / 399 = E8 at *
  unfold thetaCuspLikelihoodSourceLogPartitionJetFour
  rw [hAg, hBg]
  unfold sharpJetMain4
  rw [← hid]
  have hAj4 : 0 ≤ A ^ (4 : ℕ) := by positivity
  have u4 := mul_le_mul_of_nonneg_left (abs_le.mp hk4).2 hAj4
  have l4 := mul_le_mul_of_nonneg_left (abs_le.mp hk4).1 hAj4
  have hAj3 : 0 ≤ A ^ (3 : ℕ) := by positivity
  have u3 := mul_le_mul_of_nonneg_left (abs_le.mp hk3).2 hAj3
  have l3 := mul_le_mul_of_nonneg_left (abs_le.mp hk3).1 hAj3
  have hp3 : 6 ^ (1 : ℕ) * A ^ (3 : ℕ) ≤ A ^ (4 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hA 1
    calc 6 ^ (1 : ℕ) * A ^ (3 : ℕ) ≤ A * A ^ (3 : ℕ) := mul_le_mul_of_nonneg_right (by simpa using this) hAj3
      _ = A ^ (4 : ℕ) := by ring
  have hpe3 := mul_le_mul_of_nonneg_right hp3 hε20
  have hpE3 := mul_le_mul_of_nonneg_right hp3 hE80
  have hAj2 : 0 ≤ A ^ (2 : ℕ) := by positivity
  have u2 := mul_le_mul_of_nonneg_left (abs_le.mp hk2).2 hAj2
  have l2 := mul_le_mul_of_nonneg_left (abs_le.mp hk2).1 hAj2
  have hp2 : 6 ^ (2 : ℕ) * A ^ (2 : ℕ) ≤ A ^ (4 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hA 2
    calc 6 ^ (2 : ℕ) * A ^ (2 : ℕ) ≤ A ^ (2 : ℕ) * A ^ (2 : ℕ) := mul_le_mul_of_nonneg_right this hAj2
      _ = A ^ (4 : ℕ) := by ring
  have hpe2 := mul_le_mul_of_nonneg_right hp2 hε20
  have hpE2 := mul_le_mul_of_nonneg_right hp2 hE80
  have hAj1 : 0 ≤ A := by positivity
  have u1 := mul_le_mul_of_nonneg_left (abs_le.mp hk1).2 hAj1
  have l1 := mul_le_mul_of_nonneg_left (abs_le.mp hk1).1 hAj1
  have hp1 : 6 ^ (3 : ℕ) * A ≤ A ^ (4 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hA 3
    calc 6 ^ (3 : ℕ) * A ≤ A ^ (3 : ℕ) * A := mul_le_mul_of_nonneg_right this hAj1
      _ = A ^ (4 : ℕ) := by ring
  have hpe1 := mul_le_mul_of_nonneg_right hp1 hε20
  have hpE1 := mul_le_mul_of_nonneg_right hp1 hE80
  have hnn1 : 0 ≤ A ^ (4 : ℕ) * ε ^ (2 : ℕ) := mul_nonneg hAj4 hε20
  have hnn2 : 0 ≤ A ^ (4 : ℕ) * E8 := mul_nonneg hAj4 hE80
  rw [abs_le]
  constructor <;> linarith only [u4, l4, u3, l3, u2, l2, u1, l1, hpe3, hpE3, hpe2, hpE2, hpe1, hpE1, hnn1, hnn2]

/-- **Sharp bound for the `5`-th jet** in regime I. -/
theorem sharpJet_bound_5 {x : ℝ} (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspLikelihoodSourceLogPartitionJetFive x -
        sharpJetMain5 (thetaCuspSingleAtomReflectionScale 1 x)| ≤
      199672 * thetaCuspSingleAtomReflectionScale 1 x ^ (5 : ℕ) * regimeOneLikelihoodScale x ^ (2 : ℕ) +
      1278550 * thetaCuspSingleAtomReflectionScale 1 x ^ (5 : ℕ) *
        (Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) / 399) := by
  obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6, hk7⟩ := sharpJet_deviation_bounds hA
  have hBA : thetaCuspLikelihoodCoordinate x = thetaCuspSingleAtomReflectionScale 1 x - 3 / 2 :=
    thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hA0 : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hid := sharpJet_identity_5 (thetaCuspSingleAtomReflectionScale 1 x) (by linarith)
  rw [← hBA] at hid
  have hE80 : 0 ≤ Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) / 399 := by positivity
  have hε20 : 0 ≤ regimeOneLikelihoodScale x ^ (2 : ℕ) := by positivity
  generalize hAg : thetaCuspSingleAtomReflectionScale 1 x = A at *
  generalize hBg : thetaCuspLikelihoodCoordinate x = B at *
  generalize hεg : regimeOneLikelihoodScale x = ε at *
  generalize hEg : Real.exp (-(8 * (A - Real.pi))) / 399 = E8 at *
  unfold thetaCuspLikelihoodSourceLogPartitionJetFive
  rw [hAg, hBg]
  unfold sharpJetMain5
  rw [← hid]
  have hAj5 : 0 ≤ A ^ (5 : ℕ) := by positivity
  have u5 := mul_le_mul_of_nonneg_left (abs_le.mp hk5).2 hAj5
  have l5 := mul_le_mul_of_nonneg_left (abs_le.mp hk5).1 hAj5
  have hAj4 : 0 ≤ A ^ (4 : ℕ) := by positivity
  have u4 := mul_le_mul_of_nonneg_left (abs_le.mp hk4).2 hAj4
  have l4 := mul_le_mul_of_nonneg_left (abs_le.mp hk4).1 hAj4
  have hp4 : 6 ^ (1 : ℕ) * A ^ (4 : ℕ) ≤ A ^ (5 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hA 1
    calc 6 ^ (1 : ℕ) * A ^ (4 : ℕ) ≤ A * A ^ (4 : ℕ) := mul_le_mul_of_nonneg_right (by simpa using this) hAj4
      _ = A ^ (5 : ℕ) := by ring
  have hpe4 := mul_le_mul_of_nonneg_right hp4 hε20
  have hpE4 := mul_le_mul_of_nonneg_right hp4 hE80
  have hAj3 : 0 ≤ A ^ (3 : ℕ) := by positivity
  have u3 := mul_le_mul_of_nonneg_left (abs_le.mp hk3).2 hAj3
  have l3 := mul_le_mul_of_nonneg_left (abs_le.mp hk3).1 hAj3
  have hp3 : 6 ^ (2 : ℕ) * A ^ (3 : ℕ) ≤ A ^ (5 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hA 2
    calc 6 ^ (2 : ℕ) * A ^ (3 : ℕ) ≤ A ^ (2 : ℕ) * A ^ (3 : ℕ) := mul_le_mul_of_nonneg_right this hAj3
      _ = A ^ (5 : ℕ) := by ring
  have hpe3 := mul_le_mul_of_nonneg_right hp3 hε20
  have hpE3 := mul_le_mul_of_nonneg_right hp3 hE80
  have hAj2 : 0 ≤ A ^ (2 : ℕ) := by positivity
  have u2 := mul_le_mul_of_nonneg_left (abs_le.mp hk2).2 hAj2
  have l2 := mul_le_mul_of_nonneg_left (abs_le.mp hk2).1 hAj2
  have hp2 : 6 ^ (3 : ℕ) * A ^ (2 : ℕ) ≤ A ^ (5 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hA 3
    calc 6 ^ (3 : ℕ) * A ^ (2 : ℕ) ≤ A ^ (3 : ℕ) * A ^ (2 : ℕ) := mul_le_mul_of_nonneg_right this hAj2
      _ = A ^ (5 : ℕ) := by ring
  have hpe2 := mul_le_mul_of_nonneg_right hp2 hε20
  have hpE2 := mul_le_mul_of_nonneg_right hp2 hE80
  have hAj1 : 0 ≤ A := by positivity
  have u1 := mul_le_mul_of_nonneg_left (abs_le.mp hk1).2 hAj1
  have l1 := mul_le_mul_of_nonneg_left (abs_le.mp hk1).1 hAj1
  have hp1 : 6 ^ (4 : ℕ) * A ≤ A ^ (5 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hA 4
    calc 6 ^ (4 : ℕ) * A ≤ A ^ (4 : ℕ) * A := mul_le_mul_of_nonneg_right this hAj1
      _ = A ^ (5 : ℕ) := by ring
  have hpe1 := mul_le_mul_of_nonneg_right hp1 hε20
  have hpE1 := mul_le_mul_of_nonneg_right hp1 hE80
  have hnn1 : 0 ≤ A ^ (5 : ℕ) * ε ^ (2 : ℕ) := mul_nonneg hAj5 hε20
  have hnn2 : 0 ≤ A ^ (5 : ℕ) * E8 := mul_nonneg hAj5 hE80
  rw [abs_le]
  constructor <;> linarith only [u5, l5, u4, l4, u3, l3, u2, l2, u1, l1, hpe4, hpE4, hpe3, hpE3, hpe2, hpE2, hpe1, hpE1, hnn1, hnn2]

/-- **Sharp bound for the `6`-th jet** in regime I. -/
theorem sharpJet_bound_6 {x : ℝ} (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspLikelihoodSourceLogPartitionJetSix x -
        sharpJetMain6 (thetaCuspSingleAtomReflectionScale 1 x)| ≤
      2480116 * thetaCuspSingleAtomReflectionScale 1 x ^ (6 : ℕ) * regimeOneLikelihoodScale x ^ (2 : ℕ) +
      22507163 * thetaCuspSingleAtomReflectionScale 1 x ^ (6 : ℕ) *
        (Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) / 399) := by
  obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6, hk7⟩ := sharpJet_deviation_bounds hA
  have hBA : thetaCuspLikelihoodCoordinate x = thetaCuspSingleAtomReflectionScale 1 x - 3 / 2 :=
    thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hA0 : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hid := sharpJet_identity_6 (thetaCuspSingleAtomReflectionScale 1 x) (by linarith)
  rw [← hBA] at hid
  have hE80 : 0 ≤ Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) / 399 := by positivity
  have hε20 : 0 ≤ regimeOneLikelihoodScale x ^ (2 : ℕ) := by positivity
  generalize hAg : thetaCuspSingleAtomReflectionScale 1 x = A at *
  generalize hBg : thetaCuspLikelihoodCoordinate x = B at *
  generalize hεg : regimeOneLikelihoodScale x = ε at *
  generalize hEg : Real.exp (-(8 * (A - Real.pi))) / 399 = E8 at *
  unfold thetaCuspLikelihoodSourceLogPartitionJetSix
  rw [hAg, hBg]
  unfold sharpJetMain6
  rw [← hid]
  have hAj6 : 0 ≤ A ^ (6 : ℕ) := by positivity
  have u6 := mul_le_mul_of_nonneg_left (abs_le.mp hk6).2 hAj6
  have l6 := mul_le_mul_of_nonneg_left (abs_le.mp hk6).1 hAj6
  have hAj5 : 0 ≤ A ^ (5 : ℕ) := by positivity
  have u5 := mul_le_mul_of_nonneg_left (abs_le.mp hk5).2 hAj5
  have l5 := mul_le_mul_of_nonneg_left (abs_le.mp hk5).1 hAj5
  have hp5 : 6 ^ (1 : ℕ) * A ^ (5 : ℕ) ≤ A ^ (6 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hA 1
    calc 6 ^ (1 : ℕ) * A ^ (5 : ℕ) ≤ A * A ^ (5 : ℕ) := mul_le_mul_of_nonneg_right (by simpa using this) hAj5
      _ = A ^ (6 : ℕ) := by ring
  have hpe5 := mul_le_mul_of_nonneg_right hp5 hε20
  have hpE5 := mul_le_mul_of_nonneg_right hp5 hE80
  have hAj4 : 0 ≤ A ^ (4 : ℕ) := by positivity
  have u4 := mul_le_mul_of_nonneg_left (abs_le.mp hk4).2 hAj4
  have l4 := mul_le_mul_of_nonneg_left (abs_le.mp hk4).1 hAj4
  have hp4 : 6 ^ (2 : ℕ) * A ^ (4 : ℕ) ≤ A ^ (6 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hA 2
    calc 6 ^ (2 : ℕ) * A ^ (4 : ℕ) ≤ A ^ (2 : ℕ) * A ^ (4 : ℕ) := mul_le_mul_of_nonneg_right this hAj4
      _ = A ^ (6 : ℕ) := by ring
  have hpe4 := mul_le_mul_of_nonneg_right hp4 hε20
  have hpE4 := mul_le_mul_of_nonneg_right hp4 hE80
  have hAj3 : 0 ≤ A ^ (3 : ℕ) := by positivity
  have u3 := mul_le_mul_of_nonneg_left (abs_le.mp hk3).2 hAj3
  have l3 := mul_le_mul_of_nonneg_left (abs_le.mp hk3).1 hAj3
  have hp3 : 6 ^ (3 : ℕ) * A ^ (3 : ℕ) ≤ A ^ (6 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hA 3
    calc 6 ^ (3 : ℕ) * A ^ (3 : ℕ) ≤ A ^ (3 : ℕ) * A ^ (3 : ℕ) := mul_le_mul_of_nonneg_right this hAj3
      _ = A ^ (6 : ℕ) := by ring
  have hpe3 := mul_le_mul_of_nonneg_right hp3 hε20
  have hpE3 := mul_le_mul_of_nonneg_right hp3 hE80
  have hAj2 : 0 ≤ A ^ (2 : ℕ) := by positivity
  have u2 := mul_le_mul_of_nonneg_left (abs_le.mp hk2).2 hAj2
  have l2 := mul_le_mul_of_nonneg_left (abs_le.mp hk2).1 hAj2
  have hp2 : 6 ^ (4 : ℕ) * A ^ (2 : ℕ) ≤ A ^ (6 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hA 4
    calc 6 ^ (4 : ℕ) * A ^ (2 : ℕ) ≤ A ^ (4 : ℕ) * A ^ (2 : ℕ) := mul_le_mul_of_nonneg_right this hAj2
      _ = A ^ (6 : ℕ) := by ring
  have hpe2 := mul_le_mul_of_nonneg_right hp2 hε20
  have hpE2 := mul_le_mul_of_nonneg_right hp2 hE80
  have hAj1 : 0 ≤ A := by positivity
  have u1 := mul_le_mul_of_nonneg_left (abs_le.mp hk1).2 hAj1
  have l1 := mul_le_mul_of_nonneg_left (abs_le.mp hk1).1 hAj1
  have hp1 : 6 ^ (5 : ℕ) * A ≤ A ^ (6 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hA 5
    calc 6 ^ (5 : ℕ) * A ≤ A ^ (5 : ℕ) * A := mul_le_mul_of_nonneg_right this hAj1
      _ = A ^ (6 : ℕ) := by ring
  have hpe1 := mul_le_mul_of_nonneg_right hp1 hε20
  have hpE1 := mul_le_mul_of_nonneg_right hp1 hE80
  have hnn1 : 0 ≤ A ^ (6 : ℕ) * ε ^ (2 : ℕ) := mul_nonneg hAj6 hε20
  have hnn2 : 0 ≤ A ^ (6 : ℕ) * E8 := mul_nonneg hAj6 hE80
  rw [abs_le]
  constructor <;> linarith only [u6, l6, u5, l5, u4, l4, u3, l3, u2, l2, u1, l1, hpe5, hpE5, hpe4, hpE4, hpe3, hpE3, hpe2, hpE2, hpe1, hpE1, hnn1, hnn2]

/-- **Sharp bound for the `7`-th jet** in regime I. -/
theorem sharpJet_bound_7 {x : ℝ} (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspLikelihoodSourceLogPartitionJetSeven x -
        sharpJetMain7 (thetaCuspSingleAtomReflectionScale 1 x)| ≤
      32679009 * thetaCuspSingleAtomReflectionScale 1 x ^ (7 : ℕ) * regimeOneLikelihoodScale x ^ (2 : ℕ) +
      403051979 * thetaCuspSingleAtomReflectionScale 1 x ^ (7 : ℕ) *
        (Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) / 399) := by
  obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6, hk7⟩ := sharpJet_deviation_bounds hA
  have hBA : thetaCuspLikelihoodCoordinate x = thetaCuspSingleAtomReflectionScale 1 x - 3 / 2 :=
    thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hA0 : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hid := sharpJet_identity_7 (thetaCuspSingleAtomReflectionScale 1 x) (by linarith)
  rw [← hBA] at hid
  have hE80 : 0 ≤ Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) / 399 := by positivity
  have hε20 : 0 ≤ regimeOneLikelihoodScale x ^ (2 : ℕ) := by positivity
  generalize hAg : thetaCuspSingleAtomReflectionScale 1 x = A at *
  generalize hBg : thetaCuspLikelihoodCoordinate x = B at *
  generalize hεg : regimeOneLikelihoodScale x = ε at *
  generalize hEg : Real.exp (-(8 * (A - Real.pi))) / 399 = E8 at *
  unfold thetaCuspLikelihoodSourceLogPartitionJetSeven
  rw [hAg, hBg]
  unfold sharpJetMain7
  rw [← hid]
  have hAj7 : 0 ≤ A ^ (7 : ℕ) := by positivity
  have u7 := mul_le_mul_of_nonneg_left (abs_le.mp hk7).2 hAj7
  have l7 := mul_le_mul_of_nonneg_left (abs_le.mp hk7).1 hAj7
  have hAj6 : 0 ≤ A ^ (6 : ℕ) := by positivity
  have u6 := mul_le_mul_of_nonneg_left (abs_le.mp hk6).2 hAj6
  have l6 := mul_le_mul_of_nonneg_left (abs_le.mp hk6).1 hAj6
  have hp6 : 6 ^ (1 : ℕ) * A ^ (6 : ℕ) ≤ A ^ (7 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hA 1
    calc 6 ^ (1 : ℕ) * A ^ (6 : ℕ) ≤ A * A ^ (6 : ℕ) := mul_le_mul_of_nonneg_right (by simpa using this) hAj6
      _ = A ^ (7 : ℕ) := by ring
  have hpe6 := mul_le_mul_of_nonneg_right hp6 hε20
  have hpE6 := mul_le_mul_of_nonneg_right hp6 hE80
  have hAj5 : 0 ≤ A ^ (5 : ℕ) := by positivity
  have u5 := mul_le_mul_of_nonneg_left (abs_le.mp hk5).2 hAj5
  have l5 := mul_le_mul_of_nonneg_left (abs_le.mp hk5).1 hAj5
  have hp5 : 6 ^ (2 : ℕ) * A ^ (5 : ℕ) ≤ A ^ (7 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hA 2
    calc 6 ^ (2 : ℕ) * A ^ (5 : ℕ) ≤ A ^ (2 : ℕ) * A ^ (5 : ℕ) := mul_le_mul_of_nonneg_right this hAj5
      _ = A ^ (7 : ℕ) := by ring
  have hpe5 := mul_le_mul_of_nonneg_right hp5 hε20
  have hpE5 := mul_le_mul_of_nonneg_right hp5 hE80
  have hAj4 : 0 ≤ A ^ (4 : ℕ) := by positivity
  have u4 := mul_le_mul_of_nonneg_left (abs_le.mp hk4).2 hAj4
  have l4 := mul_le_mul_of_nonneg_left (abs_le.mp hk4).1 hAj4
  have hp4 : 6 ^ (3 : ℕ) * A ^ (4 : ℕ) ≤ A ^ (7 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hA 3
    calc 6 ^ (3 : ℕ) * A ^ (4 : ℕ) ≤ A ^ (3 : ℕ) * A ^ (4 : ℕ) := mul_le_mul_of_nonneg_right this hAj4
      _ = A ^ (7 : ℕ) := by ring
  have hpe4 := mul_le_mul_of_nonneg_right hp4 hε20
  have hpE4 := mul_le_mul_of_nonneg_right hp4 hE80
  have hAj3 : 0 ≤ A ^ (3 : ℕ) := by positivity
  have u3 := mul_le_mul_of_nonneg_left (abs_le.mp hk3).2 hAj3
  have l3 := mul_le_mul_of_nonneg_left (abs_le.mp hk3).1 hAj3
  have hp3 : 6 ^ (4 : ℕ) * A ^ (3 : ℕ) ≤ A ^ (7 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hA 4
    calc 6 ^ (4 : ℕ) * A ^ (3 : ℕ) ≤ A ^ (4 : ℕ) * A ^ (3 : ℕ) := mul_le_mul_of_nonneg_right this hAj3
      _ = A ^ (7 : ℕ) := by ring
  have hpe3 := mul_le_mul_of_nonneg_right hp3 hε20
  have hpE3 := mul_le_mul_of_nonneg_right hp3 hE80
  have hAj2 : 0 ≤ A ^ (2 : ℕ) := by positivity
  have u2 := mul_le_mul_of_nonneg_left (abs_le.mp hk2).2 hAj2
  have l2 := mul_le_mul_of_nonneg_left (abs_le.mp hk2).1 hAj2
  have hp2 : 6 ^ (5 : ℕ) * A ^ (2 : ℕ) ≤ A ^ (7 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hA 5
    calc 6 ^ (5 : ℕ) * A ^ (2 : ℕ) ≤ A ^ (5 : ℕ) * A ^ (2 : ℕ) := mul_le_mul_of_nonneg_right this hAj2
      _ = A ^ (7 : ℕ) := by ring
  have hpe2 := mul_le_mul_of_nonneg_right hp2 hε20
  have hpE2 := mul_le_mul_of_nonneg_right hp2 hE80
  have hAj1 : 0 ≤ A := by positivity
  have u1 := mul_le_mul_of_nonneg_left (abs_le.mp hk1).2 hAj1
  have l1 := mul_le_mul_of_nonneg_left (abs_le.mp hk1).1 hAj1
  have hp1 : 6 ^ (6 : ℕ) * A ≤ A ^ (7 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hA 6
    calc 6 ^ (6 : ℕ) * A ≤ A ^ (6 : ℕ) * A := mul_le_mul_of_nonneg_right this hAj1
      _ = A ^ (7 : ℕ) := by ring
  have hpe1 := mul_le_mul_of_nonneg_right hp1 hε20
  have hpE1 := mul_le_mul_of_nonneg_right hp1 hE80
  have hnn1 : 0 ≤ A ^ (7 : ℕ) * ε ^ (2 : ℕ) := mul_nonneg hAj7 hε20
  have hnn2 : 0 ≤ A ^ (7 : ℕ) * E8 := mul_nonneg hAj7 hE80
  rw [abs_le]
  constructor <;> linarith only [u7, l7, u6, l6, u5, l5, u4, l4, u3, l3, u2, l2, u1, l1, hpe6, hpE6, hpe5, hpE5, hpe4, hpE4, hpe3, hpE3, hpe2, hpE2, hpe1, hpE1, hnn1, hnn2]

end

end RHTower
