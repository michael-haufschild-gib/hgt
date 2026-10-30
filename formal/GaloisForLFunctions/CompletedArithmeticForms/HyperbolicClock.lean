import GaloisForLFunctions.CompletedArithmeticForms.FirstAtomMixedHorizon
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# An exact positive clock for the first theta atom

An inverse-hyperbolic source coordinate turns the literal first-atom pair into a
Gaussian polynomial. Its signed moments form a positive mixture of adjacent Gamma
sequences at every order. The inverse nonlinear clock recovers the physical source,
whose finite rank obstruction shows that this coordinate change does not preserve
the full signed Hankel cone.
-/

noncomputable section

open Matrix

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower _root_.RHTower.ThetaCuspGaussianLimit

/-- The positive amplitude in the exact reflected first-atom identity. -/
def firstAtomClockAmplitude (x : ℝ) : ℝ :=
  let q := thetaCuspSingleAtomReflectionScale 1 x
  4 * q ^ 2 * Real.exp (x - 2 * q)

/-- The source-dependent constant term of the Gaussian clock profile. -/
def firstAtomClockShape (x : ℝ) : ℝ :=
  (2 * thetaCuspSingleAtomReflectionScale 1 x - 3) ^ 2

theorem firstAtomClockAmplitude_pos (x : ℝ) : 0 < firstAtomClockAmplitude x := by
  unfold firstAtomClockAmplitude thetaCuspSingleAtomReflectionScale
  positivity

/-- The actual reflected source in its inverse-hyperbolic Gaussian coordinate. -/
def firstAtomGaussianClockProfile (x t : ℝ) : ℝ :=
  let u := Real.arsinh (t / Real.sqrt (thetaCuspSingleAtomReflectionScale 1 x))
  thetaCuspSourceTerm (x + u) 1 * thetaCuspSourceTerm (x - u) 1

/-- Exact source identity, with no truncation or limiting approximation. -/
theorem firstAtomGaussianClockProfile_eq (x t : ℝ) :
    firstAtomGaussianClockProfile x t =
      firstAtomClockAmplitude x * Real.exp (-4 * t ^ 2) * (firstAtomClockShape x - 24 * t ^ 2) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq : 0 < q := by dsimp [q, thetaCuspSingleAtomReflectionScale]; positivity
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq.le
  have hc (u : ℝ) : Real.cosh (2 * u) - 1 = 2 * Real.sinh u ^ 2 := by
    have ha := Real.cosh_add u u
    have hb := Real.cosh_sq_sub_sinh_sq u
    rw [show u + u = 2 * u by ring] at ha
    nlinarith only [ha, hb]
  have harg : -2 * q * (2 * (t / Real.sqrt q) ^ 2) = -4 * t ^ 2 := by
    rw [div_pow, hsq]
    field_simp
    ring
  have hfactor : (2 * q - 3) ^ 2 - 12 * q * (2 * (t / Real.sqrt q) ^ 2) =
      (2 * q - 3) ^ 2 - 24 * t ^ 2 := by
    rw [div_pow, hsq]
    field_simp
    ring
  unfold firstAtomGaussianClockProfile
  rw [ThetaCuspOddFour.firstAtomPair_eq_affine]
  dsimp only [ThetaCuspOddFour.affine, ThetaCuspOddFour.gaussian, ThetaCuspOddFour.factor,
    firstAtomClockAmplitude, firstAtomClockShape]
  rw [hc, Real.sinh_arsinh]
  change 4 * q ^ 2 * Real.exp (x - 2 * q) *
    (Real.exp (-2 * q * (2 * (t / Real.sqrt q) ^ 2)) *
      ((2 * q - 3) ^ 2 - 12 * q * (2 * (t / Real.sqrt q) ^ 2))) = _
  rw [harg, hfactor]
  ring

/-- The inverse nonlinear coordinate recovers the physical reflected source exactly. -/
theorem firstAtomGaussianClockProfile_pullback (x u : ℝ) :
    firstAtomGaussianClockProfile x
      (Real.sqrt (thetaCuspSingleAtomReflectionScale 1 x) * Real.sinh u) =
        thetaCuspSourceTerm (x + u) 1 * thetaCuspSourceTerm (x - u) 1 := by
  have hs : Real.sqrt (thetaCuspSingleAtomReflectionScale 1 x) ≠ 0 := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  unfold firstAtomGaussianClockProfile
  rw [mul_div_cancel_left₀ _ hs, Real.arsinh_sinh]

private theorem gaussianProfile_hasDerivAt (t : ℝ) :
    HasDerivAt profile (profile t * (-8 * t)) t := by
  convert (((hasDerivAt_id t).pow 2).const_mul (-4)).exp using 1
  · funext y
    rfl
  · norm_num
    unfold profile
    ring

private theorem gaussianProfile_second_derivative :
    iteratedDeriv 2 profile = fun t => (-8 + 64 * t ^ 2) * profile t := by
  have hd : deriv profile = fun t => -8 * t * profile t := by
    funext t
    exact (gaussianProfile_hasDerivAt t).deriv.trans (by ring)
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd]
  funext t
  exact (((hasDerivAt_id t).const_mul (-8)).mul (gaussianProfile_hasDerivAt t)).deriv.trans
    (by dsimp only [id]; ring)

private theorem firstAtomGaussianClockProfile_eq_derivative_mixture (x : ℝ) :
    firstAtomGaussianClockProfile x = fun t => firstAtomClockAmplitude x *
      ((firstAtomClockShape x - 3) * profile t - (3 / 8) * iteratedDeriv 2 profile t) := by
  funext t
  rw [firstAtomGaussianClockProfile_eq, gaussianProfile_second_derivative]
  unfold profile
  ring

/-- All signed clocked moments are an exact adjacent-Gamma mixture. -/
theorem firstAtomGaussianClockProfile_signed_even_jet (x : ℝ) (k : ℕ) :
    (-1 : ℝ) ^ k * iteratedDeriv (2 * k) (firstAtomGaussianClockProfile x) 0 =
      firstAtomClockAmplitude x *
        ((firstAtomClockShape x - 3) * gaussianMoment k + (3 / 8) * gaussianMoment (k + 1)) := by
  have hleft : ContDiffAt ℝ (2 * k : ℕ)
      (fun t => (firstAtomClockShape x - 3) * profile t) 0 := by
    unfold profile
    fun_prop
  have hright : ContDiffAt ℝ (2 * k : ℕ)
      (fun t => (3 / 8 : ℝ) * iteratedDeriv 2 profile t) 0 := by
    rw [gaussianProfile_second_derivative]
    unfold profile
    fun_prop
  have hiter : iteratedDeriv (2 * k) (iteratedDeriv 2 profile) 0 =
      iteratedDeriv (2 * (k + 1)) profile 0 := by
    have htwo : iteratedDeriv 2 profile = deriv (deriv profile) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [htwo, show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
    simp only [iteratedDeriv_succ']
  have hnext : (-1 : ℝ) ^ k * iteratedDeriv (2 * (k + 1)) profile 0 = -gaussianMoment (k + 1) := by
    calc
      _ = -((-1 : ℝ) ^ (k + 1) * iteratedDeriv (2 * (k + 1)) profile 0) := by
        rw [pow_succ]
        ring
      _ = _ := by rw [profile_signed_even_jet]
  rw [firstAtomGaussianClockProfile_eq_derivative_mixture, _root_.iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_sub hleft hright, _root_.iteratedDeriv_const_mul_field,
    _root_.iteratedDeriv_const_mul_field, hiter]
  calc
    _ = firstAtomClockAmplitude x *
        ((firstAtomClockShape x - 3) * ((-1 : ℝ) ^ k * iteratedDeriv (2 * k) profile 0) -
          (3 / 8) * ((-1 : ℝ) ^ k * iteratedDeriv (2 * (k + 1)) profile 0)) := by ring
    _ = _ := by rw [profile_signed_even_jet, hnext]; ring

/-- The adjacent-Gamma mixture has the exact affine dependence on moment order. -/
theorem firstAtomGaussianClockProfile_signed_even_jet_eq (x : ℝ) (k : ℕ) :
    (-1 : ℝ) ^ k * iteratedDeriv (2 * k) (firstAtomGaussianClockProfile x) 0 =
      firstAtomClockAmplitude x * gaussianMoment k * (firstAtomClockShape x + 6 * (k : ℝ)) := by
  have hg : gaussianMoment (k + 1) = 8 * (2 * (k : ℝ) + 1) * gaussianMoment k := by
    simp only [gaussianMoment, pow_succ, gammaShapeMoment_succ]
    ring
  rw [firstAtomGaussianClockProfile_signed_even_jet, hg]
  ring

/-- Odd derivatives vanish in the exact clocked source. -/
theorem firstAtomGaussianClockProfile_odd_jet_zero (x : ℝ) {n : ℕ} (hn : Odd n) :
    iteratedDeriv n (firstAtomGaussianClockProfile x) 0 = 0 := by
  apply iteratedDeriv_zero_of_even_real_of_odd _ hn
  intro t
  rw [firstAtomGaussianClockProfile_eq, firstAtomGaussianClockProfile_eq, neg_sq]

/-- Literal Fourier-signed jets of the Gaussian-clock source. -/
def firstAtomGaussianClockSignedJet (x : ℝ) (n : ℕ) : ℝ :=
  ((-Complex.I) ^ n).re * iteratedDeriv n (firstAtomGaussianClockProfile x) 0

/-- Signed even moments in the exact nonlinear source coordinate. -/
def firstAtomGaussianClockMoment (x : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * iteratedDeriv (2 * k) (firstAtomGaussianClockProfile x) 0

theorem firstAtomGaussianClockSignedJet_eq_evenMomentSequence (x : ℝ) :
    firstAtomGaussianClockSignedJet x = evenMomentSequence (firstAtomGaussianClockMoment x) := by
  funext n
  have hI : (-Complex.I : ℂ) ^ 2 = ((-1 : ℝ) : ℂ) := by norm_num
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    rw [show n = 2 * k by omega, evenMomentSequence_even]
    simp only [firstAtomGaussianClockSignedJet, firstAtomGaussianClockMoment, pow_mul, hI,
      ← Complex.ofReal_pow, Complex.ofReal_re]
  · obtain ⟨k, hk⟩ := ho
    rw [show n = 2 * k + 1 by omega, evenMomentSequence_odd]
    simp only [firstAtomGaussianClockSignedJet, pow_add, pow_mul, hI,
      ← Complex.ofReal_pow, pow_one, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re, Complex.I_re, neg_zero, mul_zero,
      Complex.neg_im, Complex.I_im, zero_mul, sub_zero]

/-- Every shifted clocked head is exactly a mixture of two adjacent full Gamma heads. -/
theorem firstAtomGaussianClockHead_eq (x : ℝ) (N s : ℕ) :
    finiteHankelMatrix (fun k => firstAtomGaussianClockMoment x (k + s)) N =
      firstAtomClockAmplitude x •
        ((firstAtomClockShape x - 3) • gaussianShiftedHead N s +
          (3 / 8 : ℝ) • gaussianShiftedHead N (s + 1)) := by
  ext i j
  simp only [finiteHankelMatrix, firstAtomGaussianClockMoment,
    firstAtomGaussianClockProfile_signed_even_jet, Matrix.smul_apply, Matrix.add_apply,
    smul_eq_mul, gaussianShiftedHead, Nat.add_assoc]

/-- All shifted heads are strict at one fixed center whenever the Gaussian mixture is nonnegative. -/
theorem firstAtomGaussianClockHead_posDef {x : ℝ} (hshape : 3 ≤ firstAtomClockShape x)
    (N s : ℕ) :
    (finiteHankelMatrix (fun k => firstAtomGaussianClockMoment x (k + s)) N).PosDef := by
  rw [firstAtomGaussianClockHead_eq]
  apply Matrix.PosDef.smul _ (firstAtomClockAmplitude_pos x)
  have hsecond := (gaussianShiftedHead_posDef N (s + 1)).smul (by norm_num : (0 : ℝ) < 3 / 8)
  rcases lt_or_eq_of_le hshape with hlt | heq
  · exact ((gaussianShiftedHead_posDef N s).smul (sub_pos.mpr hlt)).add hsecond
  · rw [← heq, sub_self, zero_smul, zero_add]
    exact hsecond

/-- Exact parity gives strictness of every full signed head at the same source center. -/
theorem firstAtomGaussianClockSignedHead_posDef {x : ℝ} (hshape : 3 ≤ firstAtomClockShape x)
    (N : ℕ) :
    (finiteHankelMatrix (firstAtomGaussianClockSignedJet x) N).PosDef := by
  rw [firstAtomGaussianClockSignedJet_eq_evenMomentSequence,
    finiteHankelMatrix_evenMomentSequence_posDef_iff]
  exact ⟨firstAtomGaussianClockHead_posDef hshape ((N + 1) / 2) 0,
    firstAtomGaussianClockHead_posDef hshape (N / 2) 1⟩

theorem firstAtomClockShape_ge_three_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    3 ≤ firstAtomClockShape x := by
  have hq := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx
  have hd : 3 ≤ 2 * thetaCuspSingleAtomReflectionScale 1 x - 3 := by linarith only [hq]
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hd 2
  unfold firstAtomClockShape
  linarith only [hs]

/-- A nonnegative source center has one clocked positive cone containing every finite rank. -/
theorem firstAtomGaussianClock_all_rank_strict_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    ∀ N : ℕ, (finiteHankelMatrix (firstAtomGaussianClockSignedJet x) N).PosDef :=
  firstAtomGaussianClockSignedHead_posDef (firstAtomClockShape_ge_three_of_nonneg hx)

/-- An exact invertible nonlinear source clock can have a positive all-rank cone
while its physical pullback has a finite failing head. -/
theorem firstAtomGaussianClock_positive_pullback_fails {x : ℝ} (hx : 0 ≤ x) :
    (∀ N : ℕ, (finiteHankelMatrix (firstAtomGaussianClockSignedJet x) N).PosDef) ∧
      ∃ N : ℕ, ¬ (finiteHankelMatrix (firstAtomSignedSequence x) N).PosSemidef :=
  ⟨firstAtomGaussianClock_all_rank_strict_of_nonneg hx,
    exists_firstAtom_signed_head_not_posSemidef x⟩

#print axioms firstAtomGaussianClockProfile_eq
#print axioms firstAtomGaussianClockProfile_pullback
#print axioms firstAtomGaussianClockProfile_signed_even_jet
#print axioms firstAtomGaussianClockHead_posDef
#print axioms firstAtomGaussianClock_all_rank_strict_of_nonneg
#print axioms firstAtomGaussianClock_positive_pullback_fails

end GaloisForLFunctions.CompletedArithmeticForms
