import GaloisForLFunctions.RHTower.PrimeArchThetaSingleGibbsGammaCoordinate

/-!
# Boundary equipartition for the theta Liouville--Gibbs atoms

The positive Gibbs atom underlying every theta source has logarithmic derivative

`b_n' = (5/2 - 2 t_n) b_n`,

where `t_n = pi * n^2 * exp (2x)` is the Morse coordinate.  Pairing this static Ward equation
with `x^k` gives the exact half-line equipartition relation

`2 T_(k,n) = k L_(k-1,n) + (5/2) L_(k,n)`  for `k > 0`,

where `L` is the existing Liouville--Gibbs moment and `T` is the same moment with one Morse-scale
insertion.  At `k = 0`, the endpoint current survives and gives

`2 T_(0,n) = b_n(0) + (5/2) L_(0,n)`;

for the first atom, `b_1(0) = exp (-pi)`.  The elementary source inequality
`exp (2x) >= 1 + 2x` then removes `T` from every positive-power identity and yields

`4 pi n^2 L_(k+1,n) + (2 pi n^2 - 5/2) L_(k,n) <= k L_(k-1,n)`.

Thus the log-Gamma moments in the open first-atom certificate are not independent boxes: every
upper successor is constrained by two earlier moments.  The boundary restriction matters.  This
is the moment-recursion mechanism emphasized in half-line quantum bootstraps and the static
matrix-element relation supplied by generalized hypervirial theorems; see Berenstein--Hulsey,
arXiv:2206.01765, and Sukumar, arXiv:1410.5592.

No numerical enclosure is used here.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Gibbs moment with one insertion of the source-defined Morse coordinate. -/
def thetaCuspLiouvilleGibbsMorseMoment (k n : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0,
    x ^ k * thetaCuspMorseScale n x * thetaCuspLiouvilleGibbsAtom n x

/-- The Liouville--Gibbs atom is nonnegative pointwise. -/
theorem thetaCuspLiouvilleGibbsAtom_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ thetaCuspLiouvilleGibbsAtom n x := by
  rw [← thetaCuspMorseGroundState_sq]
  positivity

/-- Every polynomial moment of the Liouville--Gibbs atom is nonnegative. -/
theorem thetaCuspLiouvilleGibbsMoment_nonneg (k n : ℕ) :
    0 ≤ thetaCuspLiouvilleGibbsMoment k n := by
  rw [thetaCuspLiouvilleGibbsMoment]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg (pow_nonneg hx.le k)
    (thetaCuspLiouvilleGibbsAtom_nonneg n x)

/-- Every polynomial moment with one Morse insertion is integrable for a positive atom number. -/
theorem integrableOn_pow_mul_thetaCuspMorseScale_mul_liouvilleGibbsAtom
    (k : ℕ) {n : ℕ} (hn : 0 < n) :
    IntegrableOn (fun x : ℝ =>
      x ^ k * thetaCuspMorseScale n x * thetaCuspLiouvilleGibbsAtom n x)
        (Ioi 0) := by
  have h := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
    k (X ^ 4) hn
  have hpi := h.const_mul Real.pi
  apply hpi.congr
  filter_upwards [] with x
  simp only [thetaCuspMorseScale, thetaCuspLiouvilleGibbsAtom,
    thetaCuspPolynomialAtom, eval_pow, eval_X]
  ring

/-- Exact Gibbs score in the Morse coordinate. -/
theorem deriv_thetaCuspLiouvilleGibbsAtom_eq_morseScore (n : ℕ) (x : ℝ) :
    deriv (thetaCuspLiouvilleGibbsAtom n) x =
      ((5 / 2 : ℝ) - 2 * thetaCuspMorseScale n x) *
        thetaCuspLiouvilleGibbsAtom n x := by
  rw [(hasDerivAt_thetaCuspLiouvilleGibbsAtom n x).deriv]
  simp only [thetaCuspLiouvilleGibbsAtom, thetaCuspLogDerivativeStep,
    thetaCuspPolynomialAtom, thetaCuspMorseScale, derivative_pow,
    derivative_X, Nat.cast_ofNat, mul_one, eval_add, eval_sub, eval_mul,
    eval_C, eval_X, eval_pow]
  ring

/-- **Anomalous endpoint equipartition.**  At power zero the half-line boundary current survives
as the endpoint Gibbs density.  This is the exact boundary term absent from the positive-power
identity below. -/
theorem two_mul_thetaCuspLiouvilleGibbsMorseMoment_zero_eq
    {n : ℕ} (hn : 0 < n) :
    2 * thetaCuspLiouvilleGibbsMorseMoment 0 n =
      thetaCuspLiouvilleGibbsAtom n 0 +
        (5 / 2 : ℝ) * thetaCuspLiouvilleGibbsMoment 0 n := by
  let b : ℝ → ℝ := thetaCuspLiouvilleGibbsAtom n
  have hraw := thetaCuspAtomRawEvenMoment_zero_eq_liouvilleGibbs hn
  have hL : IntegrableOn b (Ioi 0) := by
    have hraw' := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos 0 (X ^ 2) hn
    simp only [pow_zero, one_mul] at hraw'
    exact hraw'
  have hT : IntegrableOn (fun x : ℝ =>
      thetaCuspMorseScale n x * b x) (Ioi 0) := by
    simpa only [b, pow_zero, one_mul] using
      integrableOn_pow_mul_thetaCuspMorseScale_mul_liouvilleGibbsAtom 0 hn
  have hsource : (fun x : ℝ => thetaCuspSourceTerm x n) =
      fun x : ℝ => 4 * Real.pi *
        (thetaCuspMorseScale n x - 3 / 2) * b x := by
    funext x
    rw [thetaCuspSourceTerm_eq_morseBornObservable,
      thetaCuspMorseGroundState_sq]
    simp only [b, thetaCuspMorseSuperpotential]
    ring
  have hsplit :
      (∫ x : ℝ in Ioi 0,
          4 * Real.pi * (thetaCuspMorseScale n x - 3 / 2) * b x) =
        4 * Real.pi * thetaCuspLiouvilleGibbsMorseMoment 0 n -
          6 * Real.pi * thetaCuspLiouvilleGibbsMoment 0 n := by
    rw [show (fun x : ℝ =>
        4 * Real.pi * (thetaCuspMorseScale n x - 3 / 2) * b x) =
      fun x : ℝ =>
        4 * Real.pi * (thetaCuspMorseScale n x * b x) -
          6 * Real.pi * b x by
            funext x
            ring]
    rw [integral_sub (hT.const_mul (4 * Real.pi))
      (hL.const_mul (6 * Real.pi)), integral_const_mul, integral_const_mul]
    simp only [thetaCuspLiouvilleGibbsMorseMoment,
      thetaCuspLiouvilleGibbsMoment, pow_zero, one_mul, b]
  rw [thetaCuspAtomRawEvenMoment] at hraw
  simp only [Nat.mul_zero, pow_zero, one_mul] at hraw
  rw [hsource, hsplit] at hraw
  apply (mul_left_cancel₀ (show 4 * Real.pi ≠ 0 by positivity))
  nlinarith [hraw]

/-- For the first atom, the anomalous endpoint charge is exactly `exp (-pi)`, the only
non-moment scalar in the current rational-enclosure certificate. -/
theorem two_mul_thetaCuspFirstAtomLiouvilleGibbsMorseMoment_zero_eq :
    2 * thetaCuspLiouvilleGibbsMorseMoment 0 1 =
      Real.exp (-Real.pi) +
        (5 / 2 : ℝ) * thetaCuspLiouvilleGibbsMoment 0 1 := by
  simpa [thetaCuspLiouvilleGibbsAtom_zero] using
    two_mul_thetaCuspLiouvilleGibbsMorseMoment_zero_eq
      (n := 1) (by norm_num)

/-- **Boundary equipartition identity.**  The Morse insertion is exactly a two-term expression
in consecutive polynomial moments.  Positive powers kill the endpoint current, so no boundary
charge appears in this form. -/
theorem two_mul_thetaCuspLiouvilleGibbsMorseMoment_eq
    (k : ℕ) (hk : 0 < k) {n : ℕ} (hn : 0 < n) :
    2 * thetaCuspLiouvilleGibbsMorseMoment k n =
      (k : ℝ) * thetaCuspLiouvilleGibbsMoment (k - 1) n +
        (5 / 2 : ℝ) * thetaCuspLiouvilleGibbsMoment k n := by
  have hibp := integral_pow_mul_thetaCuspLiouvilleGibbs_deriv_eq k hk hn
  have hL : IntegrableOn (fun x : ℝ =>
      x ^ k * thetaCuspLiouvilleGibbsAtom n x) (Ioi 0) := by
    simpa only [thetaCuspLiouvilleGibbsAtom] using
      integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos k (X ^ 2) hn
  have hT :=
    integrableOn_pow_mul_thetaCuspMorseScale_mul_liouvilleGibbsAtom k hn
  have hscore :
      (∫ x : ℝ in Ioi 0,
          x ^ k * deriv (thetaCuspLiouvilleGibbsAtom n) x) =
        (5 / 2 : ℝ) * thetaCuspLiouvilleGibbsMoment k n -
          2 * thetaCuspLiouvilleGibbsMorseMoment k n := by
    calc
      (∫ x : ℝ in Ioi 0,
          x ^ k * deriv (thetaCuspLiouvilleGibbsAtom n) x) =
          ∫ x : ℝ in Ioi 0,
            ((5 / 2 : ℝ) *
                (x ^ k * thetaCuspLiouvilleGibbsAtom n x) -
              2 * (x ^ k * thetaCuspMorseScale n x *
                thetaCuspLiouvilleGibbsAtom n x)) := by
            apply integral_congr_ae
            filter_upwards [] with x
            rw [deriv_thetaCuspLiouvilleGibbsAtom_eq_morseScore]
            ring
      _ = (5 / 2 : ℝ) * thetaCuspLiouvilleGibbsMoment k n -
          2 * thetaCuspLiouvilleGibbsMorseMoment k n := by
            rw [integral_sub (hL.const_mul (5 / 2 : ℝ)) (hT.const_mul 2),
              integral_const_mul, integral_const_mul]
            rfl
  rw [hscore] at hibp
  nlinarith

/-- The Morse coordinate dominates its affine tangent at the half-line endpoint. -/
theorem thetaCuspMorseScale_affine_lower
    (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Real.pi * (n : ℝ) ^ 2 * (1 + 2 * x) ≤ thetaCuspMorseScale n x := by
  have hexp : 1 + 2 * x ≤ Real.exp (2 * x) := by
    simpa [add_comm] using Real.add_one_le_exp (2 * x)
  have he2 : Real.exp (2 * x) = Real.exp x ^ 2 := by
    calc
      Real.exp (2 * x) = Real.exp ((2 : ℝ) * x) := rfl
      _ = Real.exp x ^ 2 := Real.exp_nat_mul x 2
  have hcore :
      (n : ℝ) ^ 2 * (1 + 2 * x) ≤
        (n : ℝ) ^ 2 * Real.exp (2 * x) :=
    mul_le_mul_of_nonneg_left hexp (sq_nonneg (n : ℝ))
  rw [thetaCuspMorseScale, mul_pow, ← he2]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hcore Real.pi_pos.le

/-- Integrated affine lower bound for the Morse insertion. -/
theorem pi_mul_sq_mul_gibbsMoment_affine_le_morseMoment
    (k : ℕ) {n : ℕ} (hn : 0 < n) :
    Real.pi * (n : ℝ) ^ 2 *
        (thetaCuspLiouvilleGibbsMoment k n +
          2 * thetaCuspLiouvilleGibbsMoment (k + 1) n) ≤
      thetaCuspLiouvilleGibbsMorseMoment k n := by
  let b : ℝ → ℝ := thetaCuspLiouvilleGibbsAtom n
  have hL : IntegrableOn (fun x : ℝ => x ^ k * b x) (Ioi 0) := by
    simpa only [b, thetaCuspLiouvilleGibbsAtom] using
      integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos k (X ^ 2) hn
  have hLnext : IntegrableOn (fun x : ℝ => x ^ (k + 1) * b x) (Ioi 0) := by
    simpa only [b, thetaCuspLiouvilleGibbsAtom] using
      integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos (k + 1) (X ^ 2) hn
  have hlower : IntegrableOn (fun x : ℝ =>
      Real.pi * (n : ℝ) ^ 2 *
        (x ^ k * b x + 2 * (x ^ (k + 1) * b x))) (Ioi 0) :=
    (hL.add (hLnext.const_mul 2)).const_mul (Real.pi * (n : ℝ) ^ 2)
  have hupper :=
    integrableOn_pow_mul_thetaCuspMorseScale_mul_liouvilleGibbsAtom k hn
  have hle :
      (∫ x : ℝ in Ioi 0,
          Real.pi * (n : ℝ) ^ 2 *
            (x ^ k * b x + 2 * (x ^ (k + 1) * b x))) ≤
        ∫ x : ℝ in Ioi 0,
          x ^ k * thetaCuspMorseScale n x *
            thetaCuspLiouvilleGibbsAtom n x := by
    apply integral_mono_ae hlower hupper
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hscale := thetaCuspMorseScale_affine_lower n hx.le
    have hb : 0 ≤ b x := thetaCuspLiouvilleGibbsAtom_nonneg n x
    have hweight : 0 ≤ x ^ k * b x := mul_nonneg (pow_nonneg hx.le k) hb
    calc
      Real.pi * (n : ℝ) ^ 2 *
          (x ^ k * b x + 2 * (x ^ (k + 1) * b x)) =
          (Real.pi * (n : ℝ) ^ 2 * (1 + 2 * x)) *
            (x ^ k * b x) := by
              rw [pow_succ']
              ring
      _ ≤ thetaCuspMorseScale n x * (x ^ k * b x) :=
        mul_le_mul_of_nonneg_right hscale hweight
      _ = x ^ k * thetaCuspMorseScale n x *
          thetaCuspLiouvilleGibbsAtom n x := by
            simp only [b]
            ring
  rw [integral_const_mul,
    integral_add hL (hLnext.const_mul 2), integral_const_mul] at hle
  simpa only [b, thetaCuspLiouvilleGibbsMoment,
    thetaCuspLiouvilleGibbsMorseMoment] using hle

/-- **Unconditional Gibbs-moment successor bound.**  Boundary equipartition and the affine Morse
lower bound eliminate the inserted energy.  This is the denominator-free recurrence directly
available to the first-atom log-Gamma enclosure problem. -/
theorem thetaCuspLiouvilleGibbsMoment_succ_equipartition_upper
    (k : ℕ) (hk : 0 < k) {n : ℕ} (hn : 0 < n) :
    4 * Real.pi * (n : ℝ) ^ 2 *
          thetaCuspLiouvilleGibbsMoment (k + 1) n +
        (2 * Real.pi * (n : ℝ) ^ 2 - 5 / 2) *
          thetaCuspLiouvilleGibbsMoment k n ≤
      (k : ℝ) * thetaCuspLiouvilleGibbsMoment (k - 1) n := by
  have hequip := two_mul_thetaCuspLiouvilleGibbsMorseMoment_eq k hk hn
  have hlower := pi_mul_sq_mul_gibbsMoment_affine_le_morseMoment k hn
  nlinarith

/-- Rational-coefficient consequence of boundary equipartition.  It removes the Morse insertion
and `pi`: every positive atom's polynomial moments obey a two-step decay bound. -/
theorem twelve_mul_thetaCuspLiouvilleGibbsMoment_succ_le
    (k : ℕ) (hk : 0 < k) {n : ℕ} (hn : 0 < n) :
    12 * thetaCuspLiouvilleGibbsMoment (k + 1) n ≤
      (k : ℝ) * thetaCuspLiouvilleGibbsMoment (k - 1) n := by
  have hrec := thetaCuspLiouvilleGibbsMoment_succ_equipartition_upper k hk hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnSq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hpin : (3 : ℝ) ≤ Real.pi * (n : ℝ) ^ 2 := by
    calc
      (3 : ℝ) = 3 * 1 := by ring
      _ ≤ Real.pi * (n : ℝ) ^ 2 :=
        mul_le_mul Real.pi_gt_three.le hnSq (by norm_num) Real.pi_pos.le
  have hcoefficient :
      0 ≤ 2 * Real.pi * (n : ℝ) ^ 2 - 5 / 2 := by
    nlinarith
  have hcurrent := thetaCuspLiouvilleGibbsMoment_nonneg k n
  have hnext := thetaCuspLiouvilleGibbsMoment_nonneg (k + 1) n
  have hdrop :
      4 * Real.pi * (n : ℝ) ^ 2 *
          thetaCuspLiouvilleGibbsMoment (k + 1) n ≤
        (k : ℝ) * thetaCuspLiouvilleGibbsMoment (k - 1) n := by
    nlinarith [mul_nonneg hcoefficient hcurrent]
  have hfactor : (12 : ℝ) ≤ 4 * Real.pi * (n : ℝ) ^ 2 := by
    nlinarith
  exact (mul_le_mul_of_nonneg_right hfactor hnext).trans hdrop

/-- First-atom specialization consumed by the open single-Gibbs certificate. -/
theorem thetaCuspFirstAtomLiouvilleGibbsMoment_succ_equipartition_upper
    (k : ℕ) (hk : 0 < k) :
    4 * Real.pi * thetaCuspLiouvilleGibbsMoment (k + 1) 1 +
        (2 * Real.pi - 5 / 2) * thetaCuspLiouvilleGibbsMoment k 1 ≤
      (k : ℝ) * thetaCuspLiouvilleGibbsMoment (k - 1) 1 := by
  simpa using thetaCuspLiouvilleGibbsMoment_succ_equipartition_upper
    k hk (n := 1) (by norm_num)

/-- First-atom rational two-step moment decay, directly available to the log-Gamma moment box. -/
theorem twelve_mul_thetaCuspFirstAtomLiouvilleGibbsMoment_succ_le
    (k : ℕ) (hk : 0 < k) :
    12 * thetaCuspLiouvilleGibbsMoment (k + 1) 1 ≤
      (k : ℝ) * thetaCuspLiouvilleGibbsMoment (k - 1) 1 := by
  simpa using twelve_mul_thetaCuspLiouvilleGibbsMoment_succ_le
    k hk (n := 1) (by norm_num)

end

end RHTower
