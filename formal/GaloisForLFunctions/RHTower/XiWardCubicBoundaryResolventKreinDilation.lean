import GaloisForLFunctions.RHTower.XiWardCubicBoundaryResolventTransmuter

/-!
# Cubic Ward boundary-resolvent Krein dilation (W-H198)

W-H197 proves that the unique second-order boundary-resolvent rate transmuter is active at every
primitive-cell/strict-right-zero resonance.  The excess gain is not an uncontrolled loss: every
scalar transfer `h` with `1 ≤ |h|²` has a canonical rank-one `SU(1,1)` dilation.  Its second channel
has coefficient `sqrt (|h|² - 1)`, preserves the exact Krein charge `|x|² - |y|²`, and has the
uniquely forced charge `|h|² - 1` on the incoming positive unit vector.

For the W-H197 resonant transfer this companion charge is strictly positive at every actual
strict-right Xi zero.  Consequently a completed source-to-zero contraction cannot discard the
signed auxiliary channel before landing.  It must realize this precise rank-one defect inside a
pole--Gamma Krein colligation and short it only after the full completed trace is assembled.
-/

open Complex

namespace RHTower

noncomputable section

/-- Canonical nonnegative coefficient of the negative channel dilating an active scalar transfer.
-/
def xiWardCubicKreinCompanion (h : ℂ) : ℝ :=
  Real.sqrt (Complex.normSq h - 1)

/-- Canonical two-channel `SU(1,1)` dilation of an active scalar transfer. -/
def xiWardCubicKreinDilation (h x y : ℂ) : ℂ × ℂ :=
  (h * x + (xiWardCubicKreinCompanion h : ℂ) * y,
    (xiWardCubicKreinCompanion h : ℂ) * x + (starRingEnd ℂ) h * y)

/-- Algebraic charge law before imposing the active-gain inequality. -/
theorem normSq_kreinDilation_first_sub_second
    (h x y : ℂ) :
    Complex.normSq (xiWardCubicKreinDilation h x y).1 -
        Complex.normSq (xiWardCubicKreinDilation h x y).2 =
      (Complex.normSq h - xiWardCubicKreinCompanion h ^ (2 : ℕ)) *
        (Complex.normSq x - Complex.normSq y) := by
  simp only [xiWardCubicKreinDilation, xiWardCubicKreinCompanion,
    Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- The companion squared is exactly the scalar excess power gain. -/
theorem sq_xiWardCubicKreinCompanion
    {h : ℂ} (hh : 1 ≤ Complex.normSq h) :
    xiWardCubicKreinCompanion h ^ (2 : ℕ) = Complex.normSq h - 1 := by
  rw [xiWardCubicKreinCompanion, Real.sq_sqrt]
  linarith

/-- Exact `J`-unitarity: the dilation preserves the two-channel Krein charge. -/
theorem xiWardCubicKreinDilation_preserves_charge
    {h : ℂ} (hh : 1 ≤ Complex.normSq h) (x y : ℂ) :
    Complex.normSq (xiWardCubicKreinDilation h x y).1 -
        Complex.normSq (xiWardCubicKreinDilation h x y).2 =
      Complex.normSq x - Complex.normSq y := by
  rw [normSq_kreinDilation_first_sub_second,
    sq_xiWardCubicKreinCompanion hh]
  ring

/-- Any two-channel charge-preserving lift whose positive output on `(1,0)` is `h` must pay
exactly the same negative charge.  Only its phase can vary. -/
theorem xiWardCubic_negative_companion_charge_forced
    {h v : ℂ} (hcharge : Complex.normSq h - Complex.normSq v = 1) :
    Complex.normSq v = Complex.normSq h - 1 := by
  linarith

/-- The canonical companion realizes the uniquely forced negative charge. -/
theorem normSq_kreinDilation_unit_negative
    {h : ℂ} (hh : 1 ≤ Complex.normSq h) :
    Complex.normSq (xiWardCubicKreinDilation h 1 0).2 =
      Complex.normSq h - 1 := by
  simp only [xiWardCubicKreinDilation, mul_one, mul_zero, add_zero,
    Complex.normSq_ofReal]
  simpa [pow_two] using sq_xiWardCubicKreinCompanion hh

/-- The negative channel is nontrivial for every strictly active scalar transfer. -/
theorem xiWardCubicKreinCompanion_sq_pos
    {h : ℂ} (hh : 1 < Complex.normSq h) :
    0 < xiWardCubicKreinCompanion h ^ (2 : ℕ) := by
  rw [sq_xiWardCubicKreinCompanion hh.le]
  linarith

/-- Resonant transfer attached to a primitive Euler cell and a strict-right Xi zero. -/
def xiWardCubicPrimitiveStrictRightResonantTransfer
    (pe : Nat.Primes × ℕ) (kappa : ℝ) (q : XiRightZeroCopy) : ℂ :=
  xiWardCubicBoundaryResolventTransfer
    (routePPrimitiveBurnolSpectralPoint pe kappa - 1 / 2)
    ((q.1.1 : ℂ) - 1 / 2)
    (-I * ((((q.1.1 : ℂ) - 1 / 2).im : ℝ) : ℂ))

/-- **W-H198 strict defect law.** Every actual primitive-to-strict-right incidence requires a
strictly positive rank-one negative companion charge. -/
theorem primitive_to_strictRight_kreinCompanion_sq_pos
    (pe : Nat.Primes × ℕ) (kappa : ℝ) (q : XiRightZeroCopy) :
    0 < xiWardCubicKreinCompanion
      (xiWardCubicPrimitiveStrictRightResonantTransfer pe kappa q) ^ (2 : ℕ) := by
  apply xiWardCubicKreinCompanion_sq_pos
  exact one_lt_normSq_primitive_to_strictRight_boundaryResolventTransfer pe kappa q

/-- The exact negative charge needed by each strict-right incidence is its resonant excess gain.
-/
theorem primitive_to_strictRight_kreinCompanion_sq_eq_excess_gain
    (pe : Nat.Primes × ℕ) (kappa : ℝ) (q : XiRightZeroCopy) :
    xiWardCubicKreinCompanion
        (xiWardCubicPrimitiveStrictRightResonantTransfer pe kappa q) ^ (2 : ℕ) =
      Complex.normSq
          (xiWardCubicPrimitiveStrictRightResonantTransfer pe kappa q) - 1 := by
  apply sq_xiWardCubicKreinCompanion
  exact (one_lt_normSq_primitive_to_strictRight_boundaryResolventTransfer pe kappa q).le

/-- Every primitive-to-strict-right resonant cell admits an exact charge-preserving signed lift.
-/
theorem primitive_to_strictRight_kreinDilation_preserves_charge
    (pe : Nat.Primes × ℕ) (kappa : ℝ) (q : XiRightZeroCopy) (x y : ℂ) :
    Complex.normSq
        (xiWardCubicKreinDilation
          (xiWardCubicPrimitiveStrictRightResonantTransfer pe kappa q) x y).1 -
      Complex.normSq
        (xiWardCubicKreinDilation
          (xiWardCubicPrimitiveStrictRightResonantTransfer pe kappa q) x y).2 =
      Complex.normSq x - Complex.normSq y := by
  apply xiWardCubicKreinDilation_preserves_charge
  exact (one_lt_normSq_primitive_to_strictRight_boundaryResolventTransfer pe kappa q).le

end

end RHTower
