import GaloisForLFunctions.RHTower.AngularPolynomialLaguerreEnergy
import GaloisForLFunctions.RHTower.LargeValues

/-!
# Angular small-arc concentration from actual integral energy

The Cayley half-density sends a fixed physical window to an angular arc whose length is of order
the inverse mass.  This file proves the exact analytic estimate needed to compare that shrinking
arc with a root-sensitive Bernstein bound.

If the full angular derivative energy of `Q(cos theta)` is at most `B^2` times its full mass, then
an arc of radius `delta` carries at most

`2 * delta * (1 / (2 * pi) + 2 * B)`

times the full mass.  The proof uses the corpus's genuine integral Sobolev theorem on one complete
period and an integrated AM--GM estimate.  It is not a sampled reporter or a coefficient
computation.
-/

open MeasureTheory Polynomial Set
open scoped Interval

namespace RHTower

noncomputable section

/-- Full-period angular `L^2` mass of an algebraic polynomial. -/
def angularPolynomialMass (Q : Polynomial ℝ) : ℝ :=
  ∫ theta in (-Real.pi)..Real.pi, angularPolynomialEval Q theta ^ 2

/-- Full-period angular derivative energy of an algebraic polynomial. -/
def angularPolynomialEnergy (Q : Polynomial ℝ) : ℝ :=
  ∫ theta in (-Real.pi)..Real.pi, angularPolynomialVelocity Q theta ^ 2

/-- Mass carried by the symmetric angular arc of radius `delta`. -/
def angularPolynomialArcMass (Q : Polynomial ℝ) (delta : ℝ) : ℝ :=
  ∫ theta in (-delta)..delta, angularPolynomialEval Q theta ^ 2

/-- Full-period angular mass is nonnegative. -/
theorem angularPolynomialMass_nonneg (Q : Polynomial ℝ) :
    0 ≤ angularPolynomialMass Q := by
  apply intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
  intro theta _
  exact sq_nonneg _

/-- Full-period angular derivative energy is nonnegative. -/
theorem angularPolynomialEnergy_nonneg (Q : Polynomial ℝ) :
    0 ≤ angularPolynomialEnergy Q := by
  apply intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
  intro theta _
  exact sq_nonneg _

/-- **Integral angular Sobolev cap.**  A derivative-energy bound controls every point of the
cosine-circle polynomial by the full mass with the square-root bandwidth scale `B`. -/
theorem angularPolynomialEval_sq_le_of_energy
    (Q : Polynomial ℝ) {B : ℝ} (hB : 0 < B)
    (henergy : angularPolynomialEnergy Q ≤ B ^ 2 * angularPolynomialMass Q)
    {theta : ℝ} (htheta : theta ∈ Set.Icc (-Real.pi) Real.pi) :
    angularPolynomialEval Q theta ^ 2 ≤
      (1 / (2 * Real.pi) + 2 * B) * angularPolynomialMass Q := by
  let f : ℝ → ℂ := fun t => (angularPolynomialEval Q t : ℂ)
  let f' : ℝ → ℂ := fun t => (angularPolynomialVelocity Q t : ℂ)
  have hqcont : Continuous (angularPolynomialEval Q) := by
    unfold angularPolynomialEval
    fun_prop
  have hvcont : Continuous (angularPolynomialVelocity Q) := by
    unfold angularPolynomialVelocity
    fun_prop
  have hperiod : 0 < 2 * Real.pi := by positivity
  have hright : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have hf : ∀ y ∈ Set.uIcc (-Real.pi) (-Real.pi + 2 * Real.pi),
      HasDerivAt f (f' y) y := by
    intro y _
    exact (hasDerivAt_angularPolynomialEval Q y).ofReal_comp
  have hinner : IntervalIntegrable
      (fun y => 2 * inner ℝ (f y) (f' y)) volume
      (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul
      (Complex.continuous_re.comp
        ((Complex.continuous_ofReal.comp hvcont).mul
          ((Complex.continuous_ofReal.comp hqcont).star)))
  have hmassInt : IntervalIntegrable (fun y => ‖f y‖ ^ 2) volume
      (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    exact (Complex.continuous_ofReal.comp hqcont).norm.pow 2
  have hcrossInt : IntervalIntegrable
      (fun y => 2 * (‖f y‖ * ‖f' y‖)) volume
      (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul
      ((Complex.continuous_ofReal.comp hqcont).norm.mul
        (Complex.continuous_ofReal.comp hvcont).norm)
  have hsob := sobolev_pointwise (f := f) (f' := f') (c := -Real.pi)
    (δ := 2 * Real.pi) hperiod hf hinner hmassInt hcrossInt
    (t := theta) (by rwa [hright])
  have hmassEq :
      (∫ y in (-Real.pi)..(-Real.pi + 2 * Real.pi), ‖f y‖ ^ 2) =
        angularPolynomialMass Q := by
    rw [hright]
    unfold angularPolynomialMass
    apply intervalIntegral.integral_congr
    intro y _
    simp [f, Complex.norm_real, sq_abs]
  have henergyEq :
      (∫ y in (-Real.pi)..(-Real.pi + 2 * Real.pi), ‖f' y‖ ^ 2) =
        angularPolynomialEnergy Q := by
    rw [hright]
    unfold angularPolynomialEnergy
    apply intervalIntegral.integral_congr
    intro y _
    simp [f', Complex.norm_real, sq_abs]
  have hcrossPoint : ∀ y : ℝ,
      2 * (‖f y‖ * ‖f' y‖) ≤
        B * ‖f y‖ ^ 2 + (1 / B) * ‖f' y‖ ^ 2 := by
    intro y
    have hamgm := two_mul_le_div_add_mul
      (a := ‖f y‖) (b := ‖f' y‖) (η := 1 / B) (by positivity)
    have hBinv : B ≠ 0 := ne_of_gt hB
    calc
      2 * (‖f y‖ * ‖f' y‖)
          ≤ ‖f y‖ ^ 2 / (1 / B) + (1 / B) * ‖f' y‖ ^ 2 := hamgm
      _ = B * ‖f y‖ ^ 2 + (1 / B) * ‖f' y‖ ^ 2 := by
        field_simp
  have hvelocityInt : IntervalIntegrable (fun y => ‖f' y‖ ^ 2) volume
      (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    exact (Complex.continuous_ofReal.comp hvcont).norm.pow 2
  have hproductInt : IntervalIntegrable (fun y => ‖f y‖ * ‖f' y‖) volume
      (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    exact (Complex.continuous_ofReal.comp hqcont).norm.mul
      (Complex.continuous_ofReal.comp hvcont).norm
  have hmajorInt : IntervalIntegrable
      (fun y => B * ‖f y‖ ^ 2 + (1 / B) * ‖f' y‖ ^ 2) volume
      (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    exact (hmassInt.const_mul B).add (hvelocityInt.const_mul (1 / B))
  have hcrossLe :
      (∫ y in (-Real.pi)..(-Real.pi + 2 * Real.pi),
          2 * (‖f y‖ * ‖f' y‖)) ≤
        B * angularPolynomialMass Q + (1 / B) * angularPolynomialEnergy Q := by
    have hmono := intervalIntegral.integral_mono_on
      (show -Real.pi ≤ -Real.pi + 2 * Real.pi by linarith [Real.pi_pos])
      hcrossInt hmajorInt (fun y _ => hcrossPoint y)
    have hleftEq :
      (∫ y in (-Real.pi)..(-Real.pi + 2 * Real.pi),
          2 * (‖f y‖ * ‖f' y‖)) =
          2 * ∫ y in (-Real.pi)..(-Real.pi + 2 * Real.pi), ‖f y‖ * ‖f' y‖ := by
      rw [intervalIntegral.integral_const_mul]
    have hrightEq :
        (∫ y in (-Real.pi)..(-Real.pi + 2 * Real.pi),
          B * ‖f y‖ ^ 2 + (1 / B) * ‖f' y‖ ^ 2) =
          B * angularPolynomialMass Q + (1 / B) * angularPolynomialEnergy Q := by
      rw [intervalIntegral.integral_add (hmassInt.const_mul B)
        (hvelocityInt.const_mul (1 / B)),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        hmassEq, henergyEq]
    rw [hleftEq, hrightEq] at hmono
    rw [hleftEq]
    exact hmono
  have hcrossEnergy :
      B * angularPolynomialMass Q + (1 / B) * angularPolynomialEnergy Q ≤
        2 * B * angularPolynomialMass Q := by
    have hmul := mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ 1 / B)
    have hBinv : B ≠ 0 := ne_of_gt hB
    field_simp [hBinv] at hmul ⊢
    nlinarith [angularPolynomialMass_nonneg Q]
  have hsobReal : angularPolynomialEval Q theta ^ 2 ≤
      (1 / (2 * Real.pi)) * angularPolynomialMass Q +
        ∫ y in (-Real.pi)..(-Real.pi + 2 * Real.pi),
          2 * (‖f y‖ * ‖f' y‖) := by
    rw [hmassEq] at hsob
    simpa [f, Complex.norm_real, sq_abs] using hsob
  calc
    angularPolynomialEval Q theta ^ 2
        ≤ (1 / (2 * Real.pi)) * angularPolynomialMass Q +
          ∫ y in (-Real.pi)..(-Real.pi + 2 * Real.pi),
            2 * (‖f y‖ * ‖f' y‖) := hsobReal
    _ ≤ (1 / (2 * Real.pi)) * angularPolynomialMass Q +
          (B * angularPolynomialMass Q + (1 / B) * angularPolynomialEnergy Q) :=
      add_le_add_right hcrossLe _
    _ ≤ (1 / (2 * Real.pi)) * angularPolynomialMass Q +
          2 * B * angularPolynomialMass Q := add_le_add (le_refl _) hcrossEnergy
    _ = (1 / (2 * Real.pi) + 2 * B) * angularPolynomialMass Q := by ring

/-- **Shrinking-arc mass cap.**  If full derivative energy is at most `B^2` times full mass, an
arc of radius `delta` carries at most its length times the exact integral Sobolev cap. -/
theorem angularPolynomialArcMass_le_of_energy
    (Q : Polynomial ℝ) {B delta : ℝ} (hB : 0 < B)
    (hdelta : 0 ≤ delta) (hdeltaPi : delta ≤ Real.pi)
    (henergy : angularPolynomialEnergy Q ≤ B ^ 2 * angularPolynomialMass Q) :
    angularPolynomialArcMass Q delta ≤
      2 * delta * (1 / (2 * Real.pi) + 2 * B) * angularPolynomialMass Q := by
  have hbounds : ∀ theta ∈ Set.Icc (-delta) delta,
      angularPolynomialEval Q theta ^ 2 ≤
        (1 / (2 * Real.pi) + 2 * B) * angularPolynomialMass Q := by
    intro theta htheta
    exact angularPolynomialEval_sq_le_of_energy Q hB henergy
      ⟨by linarith [htheta.1], by linarith [htheta.2]⟩
  have hleft : -delta ≤ delta := by linarith
  have hfunInt : IntervalIntegrable
      (fun theta => angularPolynomialEval Q theta ^ 2) volume (-delta) delta := by
    apply Continuous.intervalIntegrable
    unfold angularPolynomialEval
    fun_prop
  have hconstInt : IntervalIntegrable
      (fun _ : ℝ => (1 / (2 * Real.pi) + 2 * B) * angularPolynomialMass Q)
      volume (-delta) delta := intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hleft hfunInt hconstInt hbounds
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  unfold angularPolynomialArcMass
  calc
    (∫ theta in (-delta)..delta, angularPolynomialEval Q theta ^ 2)
        ≤ (delta - -delta) *
          ((1 / (2 * Real.pi) + 2 * B) * angularPolynomialMass Q) := hmono
    _ = 2 * delta * (1 / (2 * Real.pi) + 2 * B) *
          angularPolynomialMass Q := by ring

/-! ## Exact Cayley half-density transfer -/

/-- Physical-to-angular Cayley coordinate at positive mass `a`. -/
def cayleyAngularCoordinate (a x : ℝ) : ℝ :=
  2 * Real.arctan (x / a)

/-- Squared physical Cayley half-density packet.  This is exactly
`a^2 / (a^2+x^2) * Q(cos(2 arctan(x/a)))^2`. -/
def cayleyHalfDensityPolynomialSq (a : ℝ) (Q : Polynomial ℝ) (x : ℝ) : ℝ :=
  a ^ 2 / (a ^ 2 + x ^ 2) *
    angularPolynomialEval Q (cayleyAngularCoordinate a x) ^ 2

/-- Exact derivative of the physical-to-angular Cayley coordinate. -/
theorem hasDerivAt_cayleyAngularCoordinate {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    HasDerivAt (cayleyAngularCoordinate a) (2 * a / (a ^ 2 + x ^ 2)) x := by
  have hinner : HasDerivAt (fun y : ℝ => y / a) (1 / a) x := by
    simpa only [id_eq, one_div] using (hasDerivAt_id x).div_const a
  have hcomp := (Real.hasDerivAt_arctan (x / a)).comp x hinner
  have hraw : HasDerivAt (fun y : ℝ => 2 * Real.arctan (y / a))
      (2 * ((1 / (1 + (x / a) ^ 2)) * (1 / a))) x := hcomp.const_mul 2
  have hden : a ^ 2 + x ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero ha, sq_nonneg x]
  convert hraw using 1
  · rfl
  · field_simp [ha, hden]

/-- Cayley angular coordinate is odd in the physical variable. -/
theorem cayleyAngularCoordinate_neg (a x : ℝ) :
    cayleyAngularCoordinate a (-x) = -cayleyAngularCoordinate a x := by
  unfold cayleyAngularCoordinate
  rw [show -x / a = -(x / a) by ring, Real.arctan_neg]
  ring

/-- **Exact finite-window half-density Jacobian.**  Physical packet mass on `[-R,R]` is `a/2`
times angular polynomial mass on the corresponding Cayley arc. -/
theorem integral_cayleyHalfDensityPolynomialSq_eq_arcMass
    (Q : Polynomial ℝ) {a R : ℝ} (ha : 0 < a) :
    (∫ x in (-R)..R, cayleyHalfDensityPolynomialSq a Q x) =
      (a / 2) * angularPolynomialArcMass Q (cayleyAngularCoordinate a R) := by
  let phi : ℝ → ℝ := cayleyAngularCoordinate a
  let phi' : ℝ → ℝ := fun x => 2 * a / (a ^ 2 + x ^ 2)
  let density : ℝ → ℝ := fun theta => angularPolynomialEval Q theta ^ 2
  have hphi : ∀ x ∈ Set.uIcc (-R) R, HasDerivAt phi (phi' x) x := by
    intro x _
    exact hasDerivAt_cayleyAngularCoordinate ha.ne' x
  have hphi' : ContinuousOn phi' (Set.uIcc (-R) R) := by
    apply Continuous.continuousOn
    dsimp [phi']
    exact continuous_const.div
      (continuous_const.add (continuous_id.pow 2))
      (fun x => by nlinarith [sq_pos_of_pos ha, sq_nonneg x])
  have hdensity : Continuous density := by
    dsimp [density]
    unfold angularPolynomialEval
    fun_prop
  have hsubst := intervalIntegral.integral_comp_mul_deriv
    (a := -R) (b := R) (f := phi) (f' := phi') (g := density)
    hphi hphi' hdensity
  have hleft :
      (∫ x in (-R)..R, cayleyHalfDensityPolynomialSq a Q x) =
        (a / 2) * ∫ x in (-R)..R, (density ∘ phi) x * phi' x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp [cayleyHalfDensityPolynomialSq, density, phi, phi']
    have hden : a ^ 2 + x ^ 2 ≠ 0 := by
      nlinarith [sq_pos_of_pos ha, sq_nonneg x]
    field_simp [hden]
    ring
  have hend : phi (-R) = -phi R := by
    exact cayleyAngularCoordinate_neg a R
  rw [hleft, hsubst, hend]
  rfl

/-- **Physical Cayley-window cap.**  A full angular bandwidth bound gives the corresponding exact
finite physical-window mass bound with no unproved Jacobian or normalization step. -/
theorem integral_cayleyHalfDensityPolynomialSq_le_of_energy
    (Q : Polynomial ℝ) {a R B : ℝ} (ha : 0 < a) (hR : 0 ≤ R) (hB : 0 < B)
    (henergy : angularPolynomialEnergy Q ≤ B ^ 2 * angularPolynomialMass Q) :
    (∫ x in (-R)..R, cayleyHalfDensityPolynomialSq a Q x) ≤
      a * cayleyAngularCoordinate a R *
        (1 / (2 * Real.pi) + 2 * B) * angularPolynomialMass Q := by
  have hdelta0 : 0 ≤ cayleyAngularCoordinate a R := by
    unfold cayleyAngularCoordinate
    positivity
  have hdeltaPi : cayleyAngularCoordinate a R ≤ Real.pi := by
    unfold cayleyAngularCoordinate
    have hlt := Real.arctan_lt_pi_div_two (R / a)
    linarith
  rw [integral_cayleyHalfDensityPolynomialSq_eq_arcMass Q ha]
  have hcap := angularPolynomialArcMass_le_of_energy Q hB hdelta0 hdeltaPi henergy
  have hscale : 0 ≤ a / 2 := by positivity
  have := mul_le_mul_of_nonneg_left hcap hscale
  nlinarith

end

end RHTower
