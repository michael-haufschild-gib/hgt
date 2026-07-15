import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayPolarization
import GaloisForLFunctions.RHTower.SoninSemilocalJacobiTransform

/-!
# Fourth-order Jacobi value relation for the primitive theta ray

The growing completion coefficient in the primitive polar reflection is a degree-four polynomial
in the logistic coordinate `tanh t`.  The exact archimedean Jacobi transform shows that its
degree-zero and degree-two spectral components cancel: the corresponding spectral packet is
literally `X^4`.

Equivalently, twice the growing coefficient times the archimedean characteristic is the Fourier
transform of the nonnegative fourth spectral multiplier against the canonical Gamma measure.
This is an exact source-specific value relation.  No upper-half-plane current sign or RH statement
is asserted here; using the multiplier requires the separate primitive-ray polar and endpoint-seam
assembly.
-/

open Complex Real MeasureTheory Polynomial

namespace RHTower

noncomputable section

def thetaCuspPrimitiveRayJacobiSpectralPacket : ℝ[X] :=
  C (7 / 4 : ℝ) * semilocalArchimedeanJacobiPolynomial 0 +
    C ((33 / 4 : ℝ) / semilocalArchimedeanJacobiNormalization 2) *
      semilocalArchimedeanJacobiPolynomial 2 +
    C ((105 / 16 : ℝ) / semilocalArchimedeanJacobiNormalization 4) *
      semilocalArchimedeanJacobiPolynomial 4

theorem thetaCuspPrimitiveRayJacobiSpectralPacket_eval (s : ℝ) :
    thetaCuspPrimitiveRayJacobiSpectralPacket.eval s = s ^ 4 := by
  let a : ℕ → ℝ := semilocalArchimedeanJacobiCoefficient
  let c : ℕ → ℝ := semilocalArchimedeanJacobiNormalization
  let p : ℕ → ℝ := fun n => (semilocalArchimedeanJacobiPolynomial n).eval s
  have ha (n : ℕ) : 0 < a n := semilocalArchimedeanJacobiCoefficient_pos n
  have hc (n : ℕ) : 0 < c n := semilocalArchimedeanJacobiNormalization_pos n
  have haSq (n : ℕ) : a n ^ 2 = ((n : ℝ) + 1 / 2) * ((n : ℝ) + 1) :=
    semilocalArchimedeanJacobiCoefficient_sq n
  have hcSq (n : ℕ) : c n ^ 2 =
      (Nat.factorial (2 * n) : ℝ) /
        (((2 : ℝ) ^ n * (Nat.factorial n : ℝ)) ^ 2) :=
    semilocalArchimedeanJacobiNormalization_sq n
  have hc2prod : c 2 * a 0 * a 1 = 3 / 4 := by
    have hnon : 0 ≤ c 2 * a 0 * a 1 :=
      (mul_pos (mul_pos (hc 2) (ha 0)) (ha 1)).le
    have hsq : (c 2 * a 0 * a 1) ^ 2 = (3 / 4 : ℝ) ^ 2 := by
      rw [mul_pow, mul_pow, hcSq, haSq, haSq]
      norm_num
    nlinarith
  have hc4prod : c 4 * a 0 * a 1 * a 2 * a 3 = 105 / 16 := by
    have hnon : 0 ≤ c 4 * a 0 * a 1 * a 2 * a 3 :=
      (mul_pos (mul_pos (mul_pos (mul_pos (hc 4) (ha 0)) (ha 1)) (ha 2)) (ha 3)).le
    have hsq : (c 4 * a 0 * a 1 * a 2 * a 3) ^ 2 = (105 / 16 : ℝ) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, mul_pow, hcSq, haSq, haSq, haSq, haSq]
      norm_num
    nlinarith
  have hp0 : p 0 = 1 := by
    simp [p]
  have hp1 : a 0 * p 1 = s := by
    simp only [a, p, semilocalArchimedeanJacobiPolynomial, eval_mul, eval_C, eval_X]
    rw [← mul_assoc, mul_inv_cancel₀ (ha 0).ne', one_mul]
  have hrec0 := semilocalArchimedeanJacobiPolynomial_eval_recurrence 0 s
  have hrec1 := semilocalArchimedeanJacobiPolynomial_eval_recurrence 1 s
  have hrec2 := semilocalArchimedeanJacobiPolynomial_eval_recurrence 2 s
  change s * p 1 = a 0 * p 0 + a 1 * p 2 at hrec0
  change s * p 2 = a 1 * p 1 + a 2 * p 3 at hrec1
  change s * p 3 = a 2 * p 2 + a 3 * p 4 at hrec2
  have hp2raw : a 0 * a 1 * p 2 = s ^ 2 - 1 / 2 := by
    rw [hp0] at hrec0
    have ha0sq := haSq 0
    norm_num at ha0sq
    calc
      a 0 * a 1 * p 2 = a 0 * (a 1 * p 2) := by ring
      _ = a 0 * (s * p 1 - a 0) := by
        rw [show a 1 * p 2 = s * p 1 - a 0 by linarith [hrec0]]
      _ = s * (a 0 * p 1) - a 0 ^ 2 := by ring
      _ = s ^ 2 - 1 / 2 := by rw [hp1, ha0sq]; ring
  have hp4raw : a 0 * a 1 * a 2 * a 3 * p 4 =
      s ^ 4 - 11 * s ^ 2 + 15 / 4 := by
    have ha0sq := haSq 0
    have ha1sq := haSq 1
    have ha2sq := haSq 2
    norm_num at ha0sq ha1sq ha2sq
    calc
      a 0 * a 1 * a 2 * a 3 * p 4 =
          a 0 * a 1 * a 2 * (s * p 3 - a 2 * p 2) := by
            rw [show a 0 * a 1 * a 2 * a 3 * p 4 =
              a 0 * a 1 * a 2 * (a 3 * p 4) by ring,
              show a 3 * p 4 = s * p 3 - a 2 * p 2 by linarith [hrec2]]
      _ = a 0 * a 1 *
          (s * (s * p 2 - a 1 * p 1) - a 2 ^ 2 * p 2) := by
            rw [show a 0 * a 1 * a 2 * (s * p 3 - a 2 * p 2) =
              a 0 * a 1 * (s * (a 2 * p 3) - a 2 ^ 2 * p 2) by ring,
              show a 2 * p 3 = s * p 2 - a 1 * p 1 by linarith [hrec1]]
      _ = (s ^ 2 - a 2 ^ 2) * (a 0 * a 1 * p 2) -
          a 1 ^ 2 * s * (a 0 * p 1) := by ring
      _ = s ^ 4 - 11 * s ^ 2 + 15 / 4 := by
        rw [hp2raw, hp1, ha1sq, ha2sq]
        ring
  have hp2scaled : p 2 / c 2 = (4 / 3 : ℝ) * (s ^ 2 - 1 / 2) := by
    calc
      p 2 / c 2 = (a 0 * a 1 * p 2) / (c 2 * a 0 * a 1) := by
        field_simp [(hc 2).ne', (ha 0).ne', (ha 1).ne']
      _ = (s ^ 2 - 1 / 2) / (3 / 4) := by rw [hp2raw, hc2prod]
      _ = (4 / 3 : ℝ) * (s ^ 2 - 1 / 2) := by ring
  have hp4scaled : p 4 / c 4 =
      (16 / 105 : ℝ) * (s ^ 4 - 11 * s ^ 2 + 15 / 4) := by
    calc
      p 4 / c 4 =
          (a 0 * a 1 * a 2 * a 3 * p 4) /
            (c 4 * a 0 * a 1 * a 2 * a 3) := by
        field_simp [(hc 4).ne', (ha 0).ne', (ha 1).ne', (ha 2).ne', (ha 3).ne']
      _ = (s ^ 4 - 11 * s ^ 2 + 15 / 4) / (105 / 16) := by
        rw [hp4raw, hc4prod]
      _ = (16 / 105 : ℝ) * (s ^ 4 - 11 * s ^ 2 + 15 / 4) := by ring
  simp only [thetaCuspPrimitiveRayJacobiSpectralPacket, eval_add, eval_mul, eval_C]
  change 7 / 4 * p 0 + (33 / 4 / c 2) * p 2 + (105 / 16 / c 4) * p 4 = s ^ 4
  rw [hp0]
  rw [show (33 / 4 / c 2) * p 2 = (33 / 4) * (p 2 / c 2) by ring,
    show (105 / 16 / c 4) * p 4 = (105 / 16) * (p 4 / c 4) by ring,
    hp2scaled, hp4scaled]
  ring

theorem thetaCuspPrimitiveRayJacobiSpectralPacket_eq_X_pow_four :
    thetaCuspPrimitiveRayJacobiSpectralPacket = X ^ 4 := by
  apply Polynomial.funext
  intro s
  rw [thetaCuspPrimitiveRayJacobiSpectralPacket_eval]
  simp

theorem semilocalArchimedeanPolynomialFourier_add
    (P Q : ℝ[X]) (t : ℝ) :
    semilocalArchimedeanPolynomialFourier (P + Q) t =
      semilocalArchimedeanPolynomialFourier P t +
        semilocalArchimedeanPolynomialFourier Q t := by
  unfold semilocalArchimedeanPolynomialFourier
  rw [show (fun s : ℝ => (((P + Q).eval s : ℝ) : ℂ) *
      Complex.exp (((t * s : ℝ) : ℂ) * I)) =
      fun s : ℝ => (((P.eval s : ℝ) : ℂ) *
          Complex.exp (((t * s : ℝ) : ℂ) * I)) +
        (((Q.eval s : ℝ) : ℂ) *
          Complex.exp (((t * s : ℝ) : ℂ) * I)) by
    funext s
    simp
    ring]
  exact integral_add
    (integrable_semilocalArchimedeanPolynomialFourier_integrand P t)
    (integrable_semilocalArchimedeanPolynomialFourier_integrand Q t)

theorem semilocalArchimedeanPolynomialFourier_const_mul
    (r : ℝ) (P : ℝ[X]) (t : ℝ) :
    semilocalArchimedeanPolynomialFourier (C r * P) t =
      (r : ℂ) * semilocalArchimedeanPolynomialFourier P t := by
  unfold semilocalArchimedeanPolynomialFourier
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  simp
  ring

theorem two_mul_characteristic_mul_primitiveRayGrowingCoefficient_logistic
    (t : ℝ) :
    2 * semilocalArchimedeanCharacteristic t *
        thetaCuspPrimitiveRayGrowingCoefficient ((1 + Real.tanh t) / 2) =
      semilocalArchimedeanCharacteristic t *
        (7 / 4 - (33 / 4) * Real.tanh t ^ 2 +
          (105 / 16) * Real.tanh t ^ 4) := by
  unfold thetaCuspPrimitiveRayGrowingCoefficient thetaCuspPrimitiveRayMoment
  ring

theorem semilocalArchimedean_fourthMomentFourier_eq_primitiveRayGrowing
    (t : ℝ) :
    semilocalArchimedeanPolynomialFourier (X ^ 4) t =
      (2 * semilocalArchimedeanCharacteristic t *
        thetaCuspPrimitiveRayGrowingCoefficient
          ((1 + Real.tanh t) / 2) : ℝ) := by
  rw [← thetaCuspPrimitiveRayJacobiSpectralPacket_eq_X_pow_four]
  unfold thetaCuspPrimitiveRayJacobiSpectralPacket
  rw [semilocalArchimedeanPolynomialFourier_add,
    semilocalArchimedeanPolynomialFourier_add,
    semilocalArchimedeanPolynomialFourier_const_mul,
    semilocalArchimedeanPolynomialFourier_const_mul,
    semilocalArchimedeanPolynomialFourier_const_mul]
  have h0 : semilocalArchimedeanPolynomialFourier
      (semilocalArchimedeanJacobiPolynomial 0) t =
        semilocalArchimedeanJacobiFourier 0 t := rfl
  have h2 : semilocalArchimedeanPolynomialFourier
      (semilocalArchimedeanJacobiPolynomial 2) t =
        semilocalArchimedeanJacobiFourier 2 t := rfl
  have h4 : semilocalArchimedeanPolynomialFourier
      (semilocalArchimedeanJacobiPolynomial 4) t =
        semilocalArchimedeanJacobiFourier 4 t := rfl
  rw [h0, h2, h4]
  rw [semilocalArchimedeanJacobiFourier_eq_closedForm,
    semilocalArchimedeanJacobiFourier_eq_closedForm,
    semilocalArchimedeanJacobiFourier_eq_closedForm]
  rw [semilocalArchimedeanJacobiFourierClosedForm]
  rw [semilocalArchimedeanJacobiFourierClosedForm]
  rw [semilocalArchimedeanJacobiFourierClosedForm]
  rw [two_mul_characteristic_mul_primitiveRayGrowingCoefficient_logistic]
  have hc2ne : (semilocalArchimedeanJacobiNormalization 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (semilocalArchimedeanJacobiNormalization_pos 2).ne'
  have hc4ne : (semilocalArchimedeanJacobiNormalization 4 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (semilocalArchimedeanJacobiNormalization_pos 4).ne'
  push_cast
  field_simp [hc2ne, hc4ne]
  norm_num [pow_succ, semilocalArchimedeanJacobiNormalization]
  ring_nf
  simp

theorem integral_semilocalArchimedean_fourthMoment_eq_primitiveRayGrowing
    (t : ℝ) :
    (∫ s : ℝ, ((s ^ 4 : ℝ) : ℂ) *
        Complex.exp (((t * s : ℝ) : ℂ) * I)
          ∂semilocalArchimedeanGammaMeasure) =
      (2 * semilocalArchimedeanCharacteristic t *
        thetaCuspPrimitiveRayGrowingCoefficient
          ((1 + Real.tanh t) / 2) : ℝ) := by
  simpa [semilocalArchimedeanPolynomialFourier] using
    semilocalArchimedean_fourthMomentFourier_eq_primitiveRayGrowing t

end

end RHTower
