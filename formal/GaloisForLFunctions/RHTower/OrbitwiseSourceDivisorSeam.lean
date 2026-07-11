import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# Orbitwise source--divisor seam: faithful detector, flat transport

The two lower endpoints of the functional-equation/Schwarz orbit of a point `ρ` are
`conj ρ` and `1 - ρ`.  On the absolute-convergence half-plane, translate both endpoints far to
the right and compare the actual von Mangoldt source.  Multiplication by `2^x` extracts the first
prime atom and gives the canonical limit

`log 2 * (2^(-conj ρ) - 2^(-(1-ρ)))`.

This source seam is faithful: it vanishes exactly on the critical line.  It is not, however, an
obstruction supplied by orbit composition.  The associated multiplicative first-prime transport is
`2^(b-a) = 2^b / 2^a`, an exact coboundary.  Forward and reverse orbit edges therefore cancel at
every point, on or off the line.  Thus the first-prime source distinguishes the two endpoints but
does not canonically identify them; declaring its edge trivial would restate the desired fixed-point
condition.
-/

open Complex Filter Real LSeries

namespace RHTower

noncomputable section

/-- Absorb a fixed complex translation into the von Mangoldt coefficients. -/
def shiftedVonMangoldtCoeff (a : ℂ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ a

@[simp] theorem shiftedVonMangoldtCoeff_zero (a : ℂ) :
    shiftedVonMangoldtCoeff a 0 = 0 := by
  simp [shiftedVonMangoldtCoeff]

@[simp] theorem shiftedVonMangoldtCoeff_one (a : ℂ) :
    shiftedVonMangoldtCoeff a 1 = 0 := by
  simp [shiftedVonMangoldtCoeff, ArithmeticFunction.vonMangoldt_apply_one]

theorem shiftedVonMangoldtCoeff_two (a : ℂ) :
    shiftedVonMangoldtCoeff a 2 = (Real.log 2 : ℂ) / (2 : ℂ) ^ a := by
  rw [shiftedVonMangoldtCoeff, ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
  norm_num

/-- Translating the argument of the von Mangoldt L-series is coefficient twisting. -/
theorem LSeries_shiftedVonMangoldtCoeff (a s : ℂ) :
    LSeries (shiftedVonMangoldtCoeff a) s =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (a + s) := by
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    rw [shiftedVonMangoldtCoeff, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
    field_simp

/-- Every fixed coefficient twist of the von Mangoldt sequence has a finite absolute-convergence
abscissa. -/
theorem shiftedVonMangoldtCoeff_abscissa_lt_top (a : ℂ) :
    abscissaOfAbsConv (shiftedVonMangoldtCoeff a) < ⊤ := by
  let x : ℝ := max 2 (2 - a.re)
  have hx : 1 < (a + (x : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, x]
    have h := le_max_right 2 (2 - a.re)
    linarith
  have hs := ArithmeticFunction.LSeriesSummable_vonMangoldt hx
  have hshift : LSeriesSummable (shiftedVonMangoldtCoeff a) (x : ℂ) := by
    rw [LSeriesSummable]
    rw [LSeriesSummable] at hs
    apply hs.congr
    intro n
    by_cases hn : n = 0
    · subst n
      simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
      rw [shiftedVonMangoldtCoeff, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
      field_simp
  have hle := hshift.abscissaOfAbsConv_le
  exact hle.trans_lt (by simp)

/-- First-prime extraction for a translated von Mangoldt source. -/
theorem tendsto_two_cpow_mul_shiftedVonMangoldtLSeries (a : ℂ) :
    Tendsto (fun x : ℝ => (2 : ℂ) ^ (x : ℂ) *
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (a + (x : ℂ)))
      atTop (nhds ((Real.log 2 : ℂ) / (2 : ℂ) ^ a)) := by
  have h := LSeries.tendsto_cpow_mul_atTop
    (f := shiftedVonMangoldtCoeff a) (n := 1)
    (fun m hm => by interval_cases m <;> simp [shiftedVonMangoldtCoeff])
    (shiftedVonMangoldtCoeff_abscissa_lt_top a)
  norm_num at h
  simpa [LSeries_shiftedVonMangoldtCoeff, shiftedVonMangoldtCoeff_two] using h

/-- The exact first-prime asymptotic of the source difference between two translated base points. -/
theorem tendsto_firstPrimeTranslationSeam (a b : ℂ) :
    Tendsto (fun x : ℝ => (2 : ℂ) ^ (x : ℂ) *
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (a + (x : ℂ)) -
       LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (b + (x : ℂ))))
      atTop (nhds ((Real.log 2 : ℂ) *
        ((2 : ℂ) ^ (-a) - (2 : ℂ) ^ (-b)))) := by
  have h := (tendsto_two_cpow_mul_shiftedVonMangoldtLSeries a).sub
    (tendsto_two_cpow_mul_shiftedVonMangoldtLSeries b)
  convert h using 1
  · funext x
    ring
  · congr 1
    rw [Complex.cpow_neg, Complex.cpow_neg]
    ring

/-- The first-prime source charge between the FE and Schwarz lower endpoints of `ρ`. -/
def orbitwiseFirstPrimeSeamCharge (ρ : ℂ) : ℂ :=
  (Real.log 2 : ℂ) *
    ((2 : ℂ) ^ (-(starRingEnd ℂ) ρ) - (2 : ℂ) ^ (-(1 - ρ)))

theorem tendsto_orbitwiseFirstPrimeSeamCharge (ρ : ℂ) :
    Tendsto (fun x : ℝ => (2 : ℂ) ^ (x : ℂ) *
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          ((starRingEnd ℂ) ρ + (x : ℂ)) -
       LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          ((1 - ρ) + (x : ℂ))))
      atTop (nhds (orbitwiseFirstPrimeSeamCharge ρ)) := by
  simpa [orbitwiseFirstPrimeSeamCharge] using
    tendsto_firstPrimeTranslationSeam ((starRingEnd ℂ) ρ) (1 - ρ)

/-- The same seam limit for the actual continued prime carrier `-ζ'/ζ`; sufficiently far right it
is literally the von Mangoldt L-series. -/
theorem tendsto_orbitwiseFirstPrimeSeamCharge_infinitePrimeFlux (ρ : ℂ) :
    Tendsto (fun x : ℝ => (2 : ℂ) ^ (x : ℂ) *
      (infinitePrimeFlux ((starRingEnd ℂ) ρ + (x : ℂ)) -
       infinitePrimeFlux ((1 - ρ) + (x : ℂ))))
      atTop (nhds (orbitwiseFirstPrimeSeamCharge ρ)) := by
  apply (tendsto_orbitwiseFirstPrimeSeamCharge ρ).congr'
  filter_upwards [eventually_gt_atTop (1 - ρ.re), eventually_gt_atTop ρ.re] with x hx₁ hx₂
  have h₁ : 1 < (((starRingEnd ℂ) ρ + (x : ℂ)).re) := by
    simp only [Complex.add_re, Complex.conj_re, Complex.ofReal_re]
    linarith
  have h₂ : 1 < (((1 - ρ) + (x : ℂ)).re) := by
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith
  rw [infinitePrimeFlux_eq_vonMangoldtLSeries h₁,
    infinitePrimeFlux_eq_vonMangoldtLSeries h₂]

/-- The orbitwise first-prime seam is a faithful detector of the critical line. -/
theorem orbitwiseFirstPrimeSeamCharge_eq_zero_iff (ρ : ℂ) :
    orbitwiseFirstPrimeSeamCharge ρ = 0 ↔ ρ.re = 1 / 2 := by
  constructor
  · intro hzero
    have hlog : (Real.log 2 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    have hcpow : (2 : ℂ) ^ (-(starRingEnd ℂ) ρ) = (2 : ℂ) ^ (-(1 - ρ)) := by
      have := (mul_eq_zero.mp hzero)
      exact sub_eq_zero.mp (this.resolve_left hlog)
    have hnorm := congrArg norm hcpow
    change ‖((2 : ℝ) : ℂ) ^ (-(starRingEnd ℂ) ρ)‖ =
      ‖((2 : ℝ) : ℂ) ^ (-(1 - ρ))‖ at hnorm
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num),
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)] at hnorm
    have hre :=
      (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective hnorm
    simp only [Complex.neg_re, Complex.conj_re, Complex.one_re, Complex.sub_re] at hre
    linarith
  · intro hre
    have horbit : (starRingEnd ℂ) ρ = 1 - ρ := by
      apply Complex.ext
      · simp only [Complex.conj_re, Complex.sub_re, Complex.one_re]
        linarith
      · simp only [Complex.conj_im, Complex.sub_im, Complex.one_im]
        ring
    simp [orbitwiseFirstPrimeSeamCharge, horbit]

/-- The multiplicative first-prime transport between two base points. -/
def firstPrimeOrbitTransport (a b : ℂ) : ℂ :=
  (2 : ℂ) ^ (b - a)

/-- First-prime transport is an exact coboundary. -/
theorem firstPrimeOrbitTransport_eq_coboundary (a b : ℂ) :
    firstPrimeOrbitTransport a b = (2 : ℂ) ^ b / (2 : ℂ) ^ a := by
  rw [firstPrimeOrbitTransport, Complex.cpow_sub _ _ (by norm_num)]

/-- First-prime transport composes by ordinary additive translation. -/
theorem firstPrimeOrbitTransport_trans (a b c : ℂ) :
    firstPrimeOrbitTransport a b * firstPrimeOrbitTransport b c =
      firstPrimeOrbitTransport a c := by
  rw [firstPrimeOrbitTransport, firstPrimeOrbitTransport, firstPrimeOrbitTransport,
    ← Complex.cpow_add _ _ (by norm_num)]
  congr 1
  ring

@[simp] theorem firstPrimeOrbitTransport_self (a : ℂ) :
    firstPrimeOrbitTransport a a = 1 := by
  simp [firstPrimeOrbitTransport]

/-- Forward and reverse source transports cancel at every pair of points. -/
theorem firstPrimeOrbitTransport_reverse (a b : ℂ) :
    firstPrimeOrbitTransport a b * firstPrimeOrbitTransport b a = 1 := by
  rw [firstPrimeOrbitTransport_trans]
  exact firstPrimeOrbitTransport_self a

/-- The FE--Schwarz endpoint edge can be nontrivial, but its reverse always cancels it. -/
theorem orbitwiseFirstPrimeTransport_reverse_cancels (ρ : ℂ) :
    firstPrimeOrbitTransport ((starRingEnd ℂ) ρ) (1 - ρ) *
      firstPrimeOrbitTransport (1 - ρ) ((starRingEnd ℂ) ρ) = 1 :=
  firstPrimeOrbitTransport_reverse _ _

end

end RHTower
