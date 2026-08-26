import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskyFiniteMassParityRigidity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskySingleSectorFrequencyNoGo

/-!
# Finite-mass reflection rigidity of the four-dimensional Teukolsky parity gap

At the horizon `u = 1`, the exact Birmingham--Mokhtari scalar/vector parity gap depends on the
shifted virtual angular parameter `A = Q + 2` through

`G(A,x) = 6x ((2+3x)A + 6x + 6x^2) / (A+3x)^2`.

For positive `A`, `B`, and mass coordinate `x`, its exact secant difference is

`G(A,x)-G(B,x) = 6x(B-A)H(A,B,x) / ((A+3x)^2(B+3x)^2)`,

where `H` is strictly positive.  Hence this finite-mass radial response is injective in `A`.
For a Xi divisor point with `a = Re rho`, the two reflected BM shifts are
`A = a(3-a)` and `B = (1-a)(2+a)`, so `B-A = 2(1-2a)`.  The resulting reflected parity defect
therefore vanishes exactly at critical-line incidence for every positive mass, and away from the
line has the same orientation as the first BM backreaction defect.

This is an exact nonperturbative statement about the diagonal BM radial potential.  It does not
identify that potential difference with the total nonlinear Einstein `(++-)` cokernel section.

**[CORPUS-ORIGINAL] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]**
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Horizon parity gap as a function of shifted angular parameter `A = Q + 2`. -/
def d4HorizonFiniteMassParityProfile (A x : ℝ) : ℝ :=
  6 * x * ((2 + 3 * x) * A + 6 * x + 6 * x ^ 2) / (A + 3 * x) ^ 2

/-- Positive cross-numerator in the exact secant difference of the horizon parity profile. -/
def d4HorizonFiniteMassParityCrossNumerator (A B x : ℝ) : ℝ :=
  (2 + 3 * x) * A * B +
    6 * x * (1 + x) * (A + B) + 18 * x ^ 2 + 9 * x ^ 3

/-- Exact finite-mass secant factorization of the horizon parity profile. -/
theorem d4HorizonFiniteMassParityProfile_sub_eq
    (A B x : ℝ) (hA : A + 3 * x ≠ 0) (hB : B + 3 * x ≠ 0) :
    d4HorizonFiniteMassParityProfile A x -
        d4HorizonFiniteMassParityProfile B x =
      6 * x * (B - A) * d4HorizonFiniteMassParityCrossNumerator A B x /
        ((A + 3 * x) ^ 2 * (B + 3 * x) ^ 2) := by
  have hA2 : (A + 3 * x) ^ 2 ≠ 0 := pow_ne_zero 2 hA
  have hB2 : (B + 3 * x) ^ 2 ≠ 0 := pow_ne_zero 2 hB
  have hden : (A + 3 * x) ^ 2 * (B + 3 * x) ^ 2 ≠ 0 :=
    mul_ne_zero hA2 hB2
  have hprofileA :
      d4HorizonFiniteMassParityProfile A x * (A + 3 * x) ^ 2 =
        6 * x * ((2 + 3 * x) * A + 6 * x + 6 * x ^ 2) := by
    unfold d4HorizonFiniteMassParityProfile
    exact div_mul_cancel₀ _ hA2
  have hprofileB :
      d4HorizonFiniteMassParityProfile B x * (B + 3 * x) ^ 2 =
        6 * x * ((2 + 3 * x) * B + 6 * x + 6 * x ^ 2) := by
    unfold d4HorizonFiniteMassParityProfile
    exact div_mul_cancel₀ _ hB2
  apply (eq_div_iff hden).2
  calc
    (d4HorizonFiniteMassParityProfile A x -
          d4HorizonFiniteMassParityProfile B x) *
          ((A + 3 * x) ^ 2 * (B + 3 * x) ^ 2) =
        (d4HorizonFiniteMassParityProfile A x * (A + 3 * x) ^ 2) *
            (B + 3 * x) ^ 2 -
          (d4HorizonFiniteMassParityProfile B x * (B + 3 * x) ^ 2) *
            (A + 3 * x) ^ 2 := by ring
    _ =
        (6 * x * ((2 + 3 * x) * A + 6 * x + 6 * x ^ 2)) *
            (B + 3 * x) ^ 2 -
          (6 * x * ((2 + 3 * x) * B + 6 * x + 6 * x ^ 2)) *
            (A + 3 * x) ^ 2 := by rw [hprofileA, hprofileB]
    _ = 6 * x * (B - A) *
        d4HorizonFiniteMassParityCrossNumerator A B x := by
      unfold d4HorizonFiniteMassParityCrossNumerator
      ring

theorem d4HorizonFiniteMassParityCrossNumerator_pos
    {A B x : ℝ} (hA : 0 < A) (hB : 0 < B) (hx : 0 < x) :
    0 < d4HorizonFiniteMassParityCrossNumerator A B x := by
  unfold d4HorizonFiniteMassParityCrossNumerator
  positivity

/-- Positive-mass horizon parity profile separates all positive shifted angular parameters. -/
theorem d4HorizonFiniteMassParityProfile_eq_iff
    {A B x : ℝ} (hA : 0 < A) (hB : 0 < B) (hx : 0 < x) :
    d4HorizonFiniteMassParityProfile A x =
        d4HorizonFiniteMassParityProfile B x ↔ A = B := by
  have hAden : A + 3 * x ≠ 0 := ne_of_gt (by positivity)
  have hBden : B + 3 * x ≠ 0 := ne_of_gt (by positivity)
  rw [← sub_eq_zero,
    d4HorizonFiniteMassParityProfile_sub_eq A B x hAden hBden]
  have hcross := d4HorizonFiniteMassParityCrossNumerator_pos hA hB hx
  have hden : (A + 3 * x) ^ 2 * (B + 3 * x) ^ 2 ≠ 0 := by positivity
  constructor
  · intro h
    rcases div_eq_zero_iff.mp h with hnum | hdenzero
    · rcases mul_eq_zero.mp hnum with hprod | hcrosszero
      · rcases mul_eq_zero.mp hprod with h6x | hBA
        · exact False.elim ((mul_ne_zero (by norm_num) (ne_of_gt hx)) h6x)
        · linarith
      · exact False.elim ((ne_of_gt hcross) hcrosszero)
    · exact False.elim (hden hdenzero)
  · rintro rfl
    ring

/-- Positive shifted angular parameter `A = Q + 2` of a reflected-real-pair BM channel. -/
def d4BMXiHorizonAngularShift (q : XiZeroCopy) : ℝ :=
  d4BMXiReflectedRealPairMediatorAngularQ q + 2

theorem d4BMXiHorizonAngularShift_pos (q : XiZeroCopy) :
    0 < d4BMXiHorizonAngularShift q := by
  have hQ := d4BMXiReflectedRealPairMediatorAngularQ_mem_Ioo q
  unfold d4BMXiHorizonAngularShift
  linarith [hQ.1]

theorem d4BMXiHorizonAngularShift_eq (q : XiZeroCopy) :
    d4BMXiHorizonAngularShift q =
      (q.1 : ℂ).re * (3 - (q.1 : ℂ).re) := by
  exact d4BMXiReflectedRealPairMediatorAngularQ_add_two q

theorem d4BMXiHorizonAngularShift_reflect_eq (q : XiZeroCopy) :
    d4BMXiHorizonAngularShift (xiZeroCopyReflectEquiv q) =
      (1 - (q.1 : ℂ).re) * (2 + (q.1 : ℂ).re) := by
  unfold d4BMXiHorizonAngularShift d4BMXiReflectedRealPairMediatorAngularQ
  rw [xiZeroCopyReflectEquiv_rho]
  simp only [Complex.sub_re, Complex.one_re]
  ring

/-- Exact finite-mass horizon parity gap on a Xi-reflected BM mediator. -/
def d4BMXiHorizonFiniteMassParityGap (q : XiZeroCopy) (x : ℝ) : ℝ :=
  d4ScalarBracket (d4BMXiReflectedRealPairMediatorAngularQ q) x 1 -
    d4VectorBracket (d4BMXiReflectedRealPairMediatorAngularQ q) x

theorem d4BMXiHorizonFiniteMassParityGap_eq_profile
    (q : XiZeroCopy) {x : ℝ} (hx : 0 < x) :
    d4BMXiHorizonFiniteMassParityGap q x =
      d4HorizonFiniteMassParityProfile (d4BMXiHorizonAngularShift q) x := by
  have hQ := d4BMXiReflectedRealPairMediatorAngularQ_mem_Ioo q
  have hden : d4BMXiReflectedRealPairMediatorAngularQ q + 2 + 3 * x ≠ 0 :=
    ne_of_gt (by linarith [hQ.1])
  unfold d4BMXiHorizonFiniteMassParityGap
  rw [d4ParitySplit_eq_finiteMassFactor _ x 1 hden]
  unfold d4HorizonFiniteMassParityProfile d4BMXiHorizonAngularShift
  ring

/-- Difference between reflected finite-mass horizon parity gaps. -/
def d4BMXiHorizonFiniteMassParityDefect (q : XiZeroCopy) (x : ℝ) : ℝ :=
  d4BMXiHorizonFiniteMassParityGap q x -
    d4BMXiHorizonFiniteMassParityGap (xiZeroCopyReflectEquiv q) x

/-- Strictly positive finite-mass multiplier of horizontal Xi displacement. -/
def d4BMXiHorizonFiniteMassReflectionSusceptibility
    (q : XiZeroCopy) (x : ℝ) : ℝ :=
  let A := d4BMXiHorizonAngularShift q
  let B := d4BMXiHorizonAngularShift (xiZeroCopyReflectEquiv q)
  12 * x * d4HorizonFiniteMassParityCrossNumerator A B x /
    ((A + 3 * x) ^ 2 * (B + 3 * x) ^ 2)

theorem d4BMXiHorizonFiniteMassReflectionSusceptibility_pos
    (q : XiZeroCopy) {x : ℝ} (hx : 0 < x) :
    0 < d4BMXiHorizonFiniteMassReflectionSusceptibility q x := by
  have hA := d4BMXiHorizonAngularShift_pos q
  have hB := d4BMXiHorizonAngularShift_pos (xiZeroCopyReflectEquiv q)
  have hcross := d4HorizonFiniteMassParityCrossNumerator_pos hA hB hx
  unfold d4BMXiHorizonFiniteMassReflectionSusceptibility
  exact div_pos (mul_pos (mul_pos (by norm_num) hx) hcross) (by positivity)

/-- Exact factorization of the reflected finite-mass horizon parity defect. -/
theorem d4BMXiHorizonFiniteMassParityDefect_eq
    (q : XiZeroCopy) {x : ℝ} (hx : 0 < x) :
    d4BMXiHorizonFiniteMassParityDefect q x =
      (1 - 2 * (q.1 : ℂ).re) *
        d4BMXiHorizonFiniteMassReflectionSusceptibility q x := by
  let A := d4BMXiHorizonAngularShift q
  let B := d4BMXiHorizonAngularShift (xiZeroCopyReflectEquiv q)
  have hApos : 0 < A := d4BMXiHorizonAngularShift_pos q
  have hBpos : 0 < B := d4BMXiHorizonAngularShift_pos (xiZeroCopyReflectEquiv q)
  have hA : A + 3 * x ≠ 0 := ne_of_gt (by positivity)
  have hB : B + 3 * x ≠ 0 := ne_of_gt (by positivity)
  have hBA : B - A = 2 * (1 - 2 * (q.1 : ℂ).re) := by
    dsimp [A, B]
    rw [d4BMXiHorizonAngularShift_reflect_eq,
      d4BMXiHorizonAngularShift_eq]
    ring
  unfold d4BMXiHorizonFiniteMassParityDefect
  rw [d4BMXiHorizonFiniteMassParityGap_eq_profile q hx,
    d4BMXiHorizonFiniteMassParityGap_eq_profile (xiZeroCopyReflectEquiv q) hx,
    d4HorizonFiniteMassParityProfile_sub_eq A B x hA hB]
  unfold d4BMXiHorizonFiniteMassReflectionSusceptibility
  dsimp only
  rw [hBA]
  ring

/-- Reflected finite-mass horizon parity gaps agree exactly at critical-line incidence. -/
theorem d4BMXiHorizonFiniteMassParityDefect_eq_zero_iff
    (q : XiZeroCopy) {x : ℝ} (hx : 0 < x) :
    d4BMXiHorizonFiniteMassParityDefect q x = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiHorizonFiniteMassParityDefect_eq q hx]
  have hs := d4BMXiHorizonFiniteMassReflectionSusceptibility_pos q hx
  constructor
  · intro h
    rcases mul_eq_zero.mp h with htilt | hs0
    · linarith
    · exact False.elim ((ne_of_gt hs) hs0)
  · intro h
    rw [h]
    norm_num

/-- For every positive mass, the exact reflected radial defect reinforces the first BM
backreaction orientation off the critical line. -/
theorem d4BMXiHorizonFiniteMassParityDefect_mul_first_pos_of_tilt
    (q : XiZeroCopy) {x : ℝ} (hx : 0 < x)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    0 < d4BMXiHorizonFiniteMassParityDefect q x *
      d4BMXiReflectionOddBackreactionDefect q := by
  let a : ℝ := (q.1 : ℂ).re
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have ha0 : 0 < a := by simpa [a] using hstrip.1
  have ha1 : a < 1 := by simpa [a] using hstrip.2
  have hD : 0 < a * (1 - a) * (3 - a) * (2 + a) := by
    exact mul_pos (mul_pos (mul_pos ha0 (by linarith)) (by linarith)) (by linarith)
  have htilt : 1 - 2 * a ≠ 0 := by
    intro h
    apply hoff
    dsimp [a] at h ⊢
    linarith
  have hs := d4BMXiHorizonFiniteMassReflectionSusceptibility_pos q hx
  rw [d4BMXiHorizonFiniteMassParityDefect_eq q hx,
    d4BMXiReflectionOddBackreactionDefect_eq]
  change 0 < ((1 - 2 * a) *
      d4BMXiHorizonFiniteMassReflectionSusceptibility q x) *
        (24 * (1 - 2 * a) / (a * (1 - a) * (3 - a) * (2 + a)))
  rw [show ((1 - 2 * a) *
          d4BMXiHorizonFiniteMassReflectionSusceptibility q x) *
        (24 * (1 - 2 * a) / (a * (1 - a) * (3 - a) * (2 + a))) =
      (24 * d4BMXiHorizonFiniteMassReflectionSusceptibility q x *
        (1 - 2 * a) ^ 2) /
          (a * (1 - a) * (3 - a) * (2 + a)) by ring]
  exact div_pos (mul_pos (mul_pos (by norm_num) hs) (sq_pos_of_ne_zero htilt)) hD

end

end RHTower
