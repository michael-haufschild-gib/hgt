import GaloisForLFunctions.RHTower.MarkovParitySplitAndPoleMomentCountertermBridge

/-!
# Markov Odd-Shift Window Duality, Pole-Free Gauss Mode Bounds, and Plastic Crossover on the Primitive Hyperplane

This module advances Route HF and the Prime-Blind Archimedean Positivity (PBAP) program by
unifying:
1. the odd-shift operator `oddShift g h x = (g(x - h/2) - g(x + h/2)) / 2` from
   `WeilMarkovOddPositivity.lean` and the shift-pair window-pinning formalism `shiftPair` /
   `windowValue` / `windowVector` / `windowSum` from `WeilFullConeWindowPinning.lean`,
2. the rank-2 `(1, 1)` pole signature `2 C(f)² - 2 S(f)²` and the Double-Negative Continuum Pole
   Theorem on the primitive hyperplane `coshHalfMoment f = 0` from Modules 35–36, and
3. the Gauss-mode and plastic Lévy–cosh crossover bounds from `WeilLevyPoleGaussModeCancellation.lean`
   and `WeilLevyCoshPlasticCrossover.lean`.

## Main Results

1. **Section 1 (Exact Position-Space Autocorrelation, Shift-Pair Bridge, and Hyperbolic Pole-Flip
   Duality of `oddShift g h`):**
   - `weilTest_oddShift`: for every continuous compactly supported `g : ℝ → ℝ` and `h, y ∈ ℝ`,
     `EF.weilTest (oddShift g h) (oddShift g h) y = (2 * autoCorr g y - autoCorr g (y + h) - autoCorr g (y - h)) / 4`.
   - `weilTest_oddShift_eq_one_fourth_shiftPair`:
     `EF.weilTest (oddShift g h) (oddShift g h) y = (1 / 4 : ℂ) * EF.weilTest (shiftPair g (-1) h) (shiftPair g (-1) h) y`.
   - `coshHalfMoment_oddShift` and `sinhHalfMoment_oddShift`: the odd-shift operator swaps the
     hyperbolic half-moments up to `sinh(h / 4)`:
     `coshHalfMoment (oddShift g h) = Real.sinh (h / 4) * sinhHalfMoment g` and
     `sinhHalfMoment (oddShift g h) = Real.sinh (h / 4) * coshHalfMoment g`.
   - `re_weilPoleTerm_oddShift`: `oddShift g h` flips the sign of `weilPoleTerm` and scales it by
     `sinh(h / 4)²`:
     `(weilPoleTerm k_{oddShift g h}).re = -Real.sinh (h / 4) ^ 2 * (weilPoleTerm k_g).re`.

2. **Section 2 (Short-Support Window Evaluation of `oddShift g h`: Sign Reversal of the Prime
   Counterterm and Exponential Sinh-Square Growth):**
   - `logValue_oddShift`, `logVector_oddShift`, and `primeBlindCounterterm_oddShift`: when `g` is
     supported in `[-1/4, 1/4]`, the central autocorrelation term `2 * autoCorr g (±log n)` vanishes
     for all `n ≥ 2`, so `logValue (oddShift g h) n = -(1 / 2) * windowValue g h n` and
     `primeBlindCounterterm lam (oddShift g h) = -(1 / 2) * windowSum hg hgc hsupp lam h`.
   - `markovCountertermEnergy_oddShift_eq_arch_add_half_windowSum`: on `oddShift g h`, the subtracted
     prime counterterm flips sign and becomes `+(1 / 2) * windowSum hg hgc hsupp lam h`.
   - `markovCountertermEnergy_oddShift_eq_re_weilFullFunctional_add_sinh_cosh_of_even` and
     `two_mul_sinh_sq_cosh_sq_le_markovCountertermEnergy_oddShift_of_even`: for an even bump `g`,
     `markovCountertermEnergy lam (oddShift g h)` equals `(weilFullFunctional lam k_{oddShift g h}).re + 2 * sinh(h / 4)² * coshHalfMoment g²`.

3. **Section 3 (Pole-Free One-Mode and Two-Mode Gauss Lower Bounds for `markovArchRe` and
   `markovCountertermEnergy`):**
   - `oneMode_gauss_le_markovArchRe` and `twoMode_gauss_le_markovArchRe`: for all signed real tests
     `f ∈ C²_c(ℝ)`, `markovArchRe k_f` satisfies the pole-free one-mode (`A(0) + 4`) and two-mode
     (`A(0) + 24/5`) Gauss lower bounds with decaying `exp(-|u - v|/2)` and `exp(-5|u - v|/2)` pair
     integrals.
   - `oneMode_gauss_pole_add_sinh_sq_le_markovCountertermEnergy_of_cosh_zero` and
     `twoMode_gauss_pole_add_sinh_sq_le_markovCountertermEnergy_of_cosh_zero`: on the primitive
     hyperplane `coshHalfMoment f = 0` (and in particular on all odd tests), `markovCountertermEnergy lam`
     gains the bonus square `+ 2 * sinhHalfMoment f ^ 2` over the one-mode and two-mode Gauss–pole
     lower bounds.

4. **Section 4 (Plastic Lévy–Cosh Crossover + Bonus Sinh-Square Lower Bounds and Unconditional
   Short-Support Positivity on the Primitive Hyperplane and Odd Sector):**
   - `markovArchRe_ofReal_eq_weilArchRe_add_sinh_sq_of_cosh_zero`: on `coshHalfMoment f = 0`,
     `markovArchRe k_f = weilArchRe k_f + 2 * sinhHalfMoment f ^ 2`.
   - `levyCosh_crossover_add_sinh_sq_le_markovCountertermEnergy_of_cosh_zero`: the full plastic
     Lévy–cosh crossover lower bound for `markovCountertermEnergy lam` on the primitive hyperplane
     with the bonus square `+ 2 * sinhHalfMoment f ^ 2`.
   - `primeBlindCounterterm_eq_zero_of_support_Icc_le_threshold`: any test `f` vanishing outside
     `[a, a + L]` with `L ≤ screwSignThreshold` has `primeBlindCounterterm lam f = 0` for every
     `lam : ℕ → ℝ`.
   - `levyCosh_short_support_add_sinh_sq_le_markovCountertermEnergy_of_cosh_zero`,
     `two_mul_sinh_sq_le_markovCountertermEnergy_of_cosh_zero_support_Icc_le`, and
     `two_mul_sinh_sq_le_markovEnergy_of_odd_support_Icc_le_inv_130`: unconditional short-support
     positivity with the `+ 2 * sinhHalfMoment f ^ 2` bonus on the primitive hyperplane and on odd
     tests.
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff FourierTransform
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole WeilLevyPoleGauss WeilLevyCoshCrossover LebesgueAtomWeil
open RHTower.NonnegativeCone

/-! ## Section 1: Exact Position-Space Autocorrelation, Shift-Pair Bridge, and Hyperbolic Pole-Flip Duality of `oddShift g h` -/

/-- The complex lift of `oddShift g h` expressed as a 2-term linear combination of translates of
`liftC g`. -/
theorem oddShift_liftC_eq_sum (g : ℝ → ℝ) (h : ℝ) :
    (fun u => (oddShift g h u : ℂ)) = fun u => ∑ m ∈ Finset.range 2,
      (if m = 0 then (1 / 2 : ℂ) else (-1 / 2 : ℂ)) *
        liftC g (u - if m = 0 then h / 2 else -(h / 2)) := by
  funext u
  simp only [oddShift, liftC, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    if_true, one_ne_zero, if_false, sub_neg_eq_add]
  push_cast
  ring

/-- **Exact Position-Space Second-Central-Difference Identity for `EF.weilTest` of `oddShift g h`**:
for any continuous compactly supported `g : ℝ → ℝ` and `h, y ∈ ℝ`,
`EF.weilTest (oddShift g h) (oddShift g h) y = (2 * autoCorr g y - autoCorr g (y + h) - autoCorr g (y - h)) / 4`. -/
theorem weilTest_oddShift {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (h y : ℝ) :
    EF.weilTest (fun u => (oddShift g h u : ℂ)) (fun u => (oddShift g h u : ℂ)) y =
      (((2 * autoCorr g y - autoCorr g (y + h) - autoCorr g (y - h)) / 4 : ℝ) : ℂ) := by
  rw [oddShift_liftC_eq_sum, weilTest_sum_translates
    (show Continuous (liftC g) from Complex.continuous_ofReal.comp hg) (hasCompactSupport_liftC hgc)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, if_true, one_ne_zero,
    if_false, map_div₀, map_neg, map_one, map_ofNat, sub_neg_eq_add, weilTest_liftC]
  rw [show y - h / 2 + h / 2 = y by ring,
    show y - h / 2 + -(h / 2) = y - h by ring,
    show y + h / 2 + h / 2 = y + h by ring,
    show y + h / 2 + -(h / 2) = y by ring]
  push_cast
  ring

/-- **Exact Autocorrelation Bridge Between `oddShift g h` and `shiftPair g (-1) h`**:
because `EF.weilTest` is translation-invariant and `oddShift g h` is `-1/2` of a translate of
`shiftPair g (-1) h`, its autocorrelation is identically `1/4` of `EF.weilTest (shiftPair g (-1) h) (shiftPair g (-1) h)`. -/
theorem weilTest_oddShift_eq_one_fourth_shiftPair {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (h y : ℝ) :
    EF.weilTest (fun u => (oddShift g h u : ℂ)) (fun u => (oddShift g h u : ℂ)) y =
      (1 / 4 : ℂ) * EF.weilTest (shiftPair g (-1) h) (shiftPair g (-1) h) y := by
  rw [weilTest_oddShift hg hgc, weilTest_shiftPair hg hgc]
  push_cast
  ring

/-- Evaluation of `paperFT` of `oddShift g h` at `I / 2`:
`paperFT (oddShift g h) (I / 2) = -sinh(h / 4) * paperFT g (I / 2)`. -/
theorem paperFT_oddShift_I_div_two {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (h : ℝ) :
    paperFT (fun x => (oddShift g h x : ℂ)) (I / 2) =
      ((-Real.sinh (h / 4) : ℝ) : ℂ) * paperFT (fun x => (g x : ℂ)) (I / 2) := by
  rw [paperFT_oddShift hg hgc h (I / 2)]
  congr 1
  have e1 : I * (I / 2) * ((h / 2 : ℝ) : ℂ) = ((-(h / 4) : ℝ) : ℂ) := by
    rw [show I * (I / 2) * ((h / 2 : ℝ) : ℂ) = (I * I) * (h : ℂ) / 4 by push_cast; ring,
      Complex.I_mul_I]
    push_cast; ring
  have e2 : I * (I / 2) * ((-(h / 2) : ℝ) : ℂ) = ((h / 4 : ℝ) : ℂ) := by
    rw [show I * (I / 2) * ((-(h / 2) : ℝ) : ℂ) = -(I * I) * (h : ℂ) / 4 by push_cast; ring,
      Complex.I_mul_I]
    push_cast; ring
  rw [e1, e2, ← Complex.ofReal_exp, ← Complex.ofReal_exp, Real.sinh_eq]
  push_cast
  ring

/-- Evaluation of `paperFT` of `oddShift g h` at `-I / 2`:
`paperFT (oddShift g h) (-I / 2) = sinh(h / 4) * paperFT g (-I / 2)`. -/
theorem paperFT_oddShift_neg_I_div_two {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (h : ℝ) :
    paperFT (fun x => (oddShift g h x : ℂ)) (-I / 2) =
      ((Real.sinh (h / 4) : ℝ) : ℂ) * paperFT (fun x => (g x : ℂ)) (-I / 2) := by
  rw [paperFT_oddShift hg hgc h (-I / 2)]
  congr 1
  have e1 : I * (-I / 2) * ((h / 2 : ℝ) : ℂ) = ((h / 4 : ℝ) : ℂ) := by
    rw [show I * (-I / 2) * ((h / 2 : ℝ) : ℂ) = -(I * I) * (h : ℂ) / 4 by push_cast; ring,
      Complex.I_mul_I]
    push_cast; ring
  have e2 : I * (-I / 2) * ((-(h / 2) : ℝ) : ℂ) = ((-(h / 4) : ℝ) : ℂ) := by
    rw [show I * (-I / 2) * ((-(h / 2) : ℝ) : ℂ) = (I * I) * (h : ℂ) / 4 by push_cast; ring,
      Complex.I_mul_I]
    push_cast; ring
  rw [e1, e2, ← Complex.ofReal_exp, ← Complex.ofReal_exp, Real.sinh_eq]
  push_cast
  ring

/-- **Hyperbolic Half-Moment Swap Duality of `oddShift g h`**:
for any continuous compactly supported `g : ℝ → ℝ` and shift `h ∈ ℝ`,
`coshHalfMoment (oddShift g h) = Real.sinh (h / 4) * sinhHalfMoment g` and
`sinhHalfMoment (oddShift g h) = Real.sinh (h / 4) * coshHalfMoment g`. -/
theorem coshHalfMoment_and_sinhHalfMoment_oddShift {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (h : ℝ) :
    coshHalfMoment (oddShift g h) = Real.sinh (h / 4) * sinhHalfMoment g ∧
      sinhHalfMoment (oddShift g h) = Real.sinh (h / 4) * coshHalfMoment g := by
  have hod : Continuous (oddShift g h) := by
    unfold oddShift; fun_prop
  have hoc : HasCompactSupport (oddShift g h) := hasCompactSupport_oddShift hgc h
  obtain ⟨hOp, hOm⟩ := integral_mul_exp_half_eq_cosh_add_sinh hod hoc
  obtain ⟨hgp, hgm⟩ := integral_mul_exp_half_eq_cosh_add_sinh hg hgc
  have h1 := paperFT_oddShift_I_div_two hg hgc h
  have h2 := paperFT_oddShift_neg_I_div_two hg hgc h
  rw [paperFT_ofReal_I_div_two, paperFT_ofReal_I_div_two, hOm, hgm, ← Complex.ofReal_mul] at h1
  rw [paperFT_ofReal_neg_I_div_two, paperFT_ofReal_neg_I_div_two, hOp, hgp,
    ← Complex.ofReal_mul] at h2
  have h1r := congrArg Complex.re h1
  have h2r := congrArg Complex.re h2
  simp only [Complex.ofReal_re] at h1r h2r
  constructor <;> linarith

/-- First component of `coshHalfMoment_and_sinhHalfMoment_oddShift`:
`coshHalfMoment (oddShift g h) = Real.sinh (h / 4) * sinhHalfMoment g`. -/
theorem coshHalfMoment_oddShift {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (h : ℝ) :
    coshHalfMoment (oddShift g h) = Real.sinh (h / 4) * sinhHalfMoment g :=
  (coshHalfMoment_and_sinhHalfMoment_oddShift hg hgc h).1

/-- Second component of `coshHalfMoment_and_sinhHalfMoment_oddShift`:
`sinhHalfMoment (oddShift g h) = Real.sinh (h / 4) * coshHalfMoment g`. -/
theorem sinhHalfMoment_oddShift {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (h : ℝ) :
    sinhHalfMoment (oddShift g h) = Real.sinh (h / 4) * coshHalfMoment g :=
  (coshHalfMoment_and_sinhHalfMoment_oddShift hg hgc h).2

/-- **Universal Pole-Flip Identity of `oddShift g h`**:
for every continuous compactly supported `g : ℝ → ℝ` and `h ∈ ℝ`, applying `oddShift g h` flips the
sign of `(weilPoleTerm k_g).re` and multiplies it by `sinh(h / 4)²`. -/
theorem re_weilPoleTerm_oddShift {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (h : ℝ) :
    (weilPoleTerm (EF.weilTest (fun u => (oddShift g h u : ℂ))
        (fun u => (oddShift g h u : ℂ)))).re =
      -Real.sinh (h / 4) ^ 2 *
        (weilPoleTerm (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re := by
  have hod : Continuous (oddShift g h) := by
    unfold oddShift; fun_prop
  have hoc : HasCompactSupport (oddShift g h) := hasCompactSupport_oddShift hgc h
  rw [re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq hod hoc,
    re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq hg hgc,
    coshHalfMoment_oddShift hg hgc h, sinhHalfMoment_oddShift hg hgc h]
  ring

/-! ## Section 2: Short-Support Window Evaluation of `oddShift g h`: Sign Reversal of the Prime Counterterm and Exponential Sinh-Square Growth -/

/-- For every continuous compactly supported `g : ℝ → ℝ`, `h ∈ ℝ`, and `n : ℕ`,
`logValue (oddShift g h) n = (1 / 4) * logValue (shiftPair g (-1) h) n`. -/
theorem logValue_oddShift_eq_one_fourth_shiftPair {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (h : ℝ) (n : ℕ) :
    logValue (fun u => (oddShift g h u : ℂ)) n =
      (1 / 4 : ℝ) * logValue (shiftPair g (-1) h) n := by
  unfold logValue
  rw [weilTest_oddShift_eq_one_fourth_shiftPair hg hgc,
    weilTest_oddShift_eq_one_fourth_shiftPair hg hgc,
    ← mul_add, show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul]
  ring

/-- **Short-Support Window Identity for `logValue` of `oddShift g h`**:
when `g` is supported in `[-1/4, 1/4]` (`∀ u, 1 / 4 < |u| → g u = 0`), for every `n ≥ 2` and `h ∈ ℝ`,
`logValue (oddShift g h) n = -(1 / 2) * windowValue g h n`. -/
theorem logValue_oddShift {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (h : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    logValue (fun u => (oddShift g h u : ℂ)) n = -(1 / 2 : ℝ) * windowValue g h n := by
  rw [logValue_oddShift_eq_one_fourth_shiftPair hg hgc h n,
    logValue_shiftPair hg hgc hsupp (-1) h hn]
  ring

/-- **Short-Support Window Identity for `logVector` of `oddShift g h`**:
when `g ∈ C²_c(ℝ)` is supported in `[-1/4, 1/4]`, the finitely supported `logVector` of
`oddShift g h` equals `-(1 / 2) • windowVector hg hgc hsupp h`. -/
theorem logVector_oddShift {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (h : ℝ) :
    logVector (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
      (hasCompactSupport_oddShift hgc h)) =
      (-(1 / 2 : ℝ)) • windowVector hg hgc hsupp h := by
  ext j
  rw [logVector_apply, Finsupp.smul_apply, smul_eq_mul]
  change logValue (fun u => (oddShift g h u : ℂ)) j = _
  rw [logValue_oddShift hg.continuous hgc hsupp h j.2]
  simp [windowVector, Finsupp.ofSupportFinite_coe]

/-- **Sign-Reversed Window Identity for `primeBlindCounterterm` on `oddShift g h`**:
for any `g ∈ C²_c(ℝ)` supported in `[-1/4, 1/4]`, any counterterm sequence `lam : ℕ → ℝ`, and
any shift `h ∈ ℝ`,
`primeBlindCounterterm lam (oddShift g h) = -(1 / 2) * windowSum hg hgc hsupp lam h`. -/
theorem primeBlindCounterterm_oddShift (lam : ℕ → ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (h : ℝ) :
    primeBlindCounterterm lam (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
      (hasCompactSupport_oddShift hgc h)) =
      -(1 / 2 : ℝ) * windowSum hg hgc hsupp lam h := by
  unfold primeBlindCounterterm windowSum
  rw [logVector_oddShift hg hgc hsupp h, map_smul, smul_eq_mul]

/-- **Markov Counterterm Energy of `oddShift g h` for a Short-Support Bump**:
because `primeBlindCounterterm lam (oddShift g h) = -(1 / 2) * windowSum lam h`, the subtracted
counterterm in `markovCountertermEnergy lam (oddShift g h)` becomes `+(1 / 2) * windowSum lam h`:
`markovCountertermEnergy lam (oddShift g h) = markovArchRe k_{oddShift g h} + (1 / 2) * windowSum lam h`. -/
theorem markovCountertermEnergy_oddShift_eq_arch_add_half_windowSum (lam : ℕ → ℝ) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hsupp : ∀ u, 1 / 4 < |u| → g u = 0)
    (h : ℝ) :
    markovCountertermEnergy lam (fun u => (oddShift g h u : ℂ)) =
      markovArchRe (EF.weilTest (fun u => (oddShift g h u : ℂ))
        (fun u => (oddShift g h u : ℂ))) +
        (1 / 2 : ℝ) * windowSum hg hgc hsupp lam h := by
  have h1 : markovCountertermEnergy lam (fun u => (oddShift g h u : ℂ)) =
      markovArchRe (EF.weilTest (fun u => (oddShift g h u : ℂ))
        (fun u => (oddShift g h u : ℂ))) -
        primeBlindCounterterm lam (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
          (hasCompactSupport_oddShift hgc h)) :=
    markovCountertermEnergy_eq_markovArchRe_sub_counterterm lam
      (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h) (hasCompactSupport_oddShift hgc h))
  rw [h1, primeBlindCounterterm_oddShift lam hg hgc hsupp h]
  ring

/-- **Exponential Sinh-Square Bonus Identity for `markovCountertermEnergy` on `oddShift g h`**:
for any even `g ∈ C²_c(ℝ)` (`∀ x, g (-x) = g x`), any counterterm sequence `lam : ℕ → ℝ`, and
any shift `h ∈ ℝ`,
`markovCountertermEnergy lam (oddShift g h) = (weilFullFunctional lam k_{oddShift g h}).re + 2 * Real.sinh (h / 4) ^ 2 * coshHalfMoment g ^ 2`. -/
theorem markovCountertermEnergy_oddShift_eq_re_weilFullFunctional_add_sinh_cosh_of_even
    (lam : ℕ → ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (heven : ∀ x, g (-x) = g x) (h : ℝ) :
    markovCountertermEnergy lam (fun u => (oddShift g h u : ℂ)) =
      (weilFullFunctional lam (EF.weilTest (fun u => (oddShift g h u : ℂ))
        (fun u => (oddShift g h u : ℂ)))).re +
        2 * Real.sinh (h / 4) ^ 2 * coshHalfMoment g ^ 2 := by
  rw [markovCountertermEnergy_real_eq_re_weilFullFunctional_add_sinh_sq_of_odd lam
      (contDiff_oddShift hg h) (hasCompactSupport_oddShift hgc h) (oddShift_neg heven h),
    sinhHalfMoment_oddShift hg.continuous hgc h]
  ring

/-- When `WeilPositiveFull lam` holds and `g ∈ C²_c(ℝ)` is even, `markovCountertermEnergy lam (oddShift g h)`
is bounded below by the exponentially growing nonnegative square
`2 * Real.sinh (h / 4) ^ 2 * coshHalfMoment g ^ 2 ≥ 0`. -/
theorem two_mul_sinh_sq_cosh_sq_le_markovCountertermEnergy_oddShift_of_even
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ x, g (-x) = g x) (h : ℝ) :
    2 * Real.sinh (h / 4) ^ 2 * coshHalfMoment g ^ 2 ≤
      markovCountertermEnergy lam (fun u => (oddShift g h u : ℂ)) := by
  rw [markovCountertermEnergy_oddShift_eq_re_weilFullFunctional_add_sinh_cosh_of_even
    lam hg hgc heven h]
  have hnn := hW (fun u => (oddShift g h u : ℂ))
    (Complex.ofRealCLM.contDiff.comp (contDiff_oddShift hg h))
    ((hasCompactSupport_oddShift hgc h).comp_left Complex.ofReal_zero)
  linarith

/-! ## Section 3: Pole-Free One-Mode and Two-Mode Gauss Lower Bounds for `markovArchRe` and `markovCountertermEnergy` -/

/-- On the primitive hyperplane `coshHalfMoment f = 0`, `markovArchRe` equals `weilArchRe` plus
the nonnegative bonus square `2 * sinhHalfMoment f ^ 2`. -/
theorem markovArchRe_ofReal_eq_weilArchRe_add_sinh_sq_of_cosh_zero {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hcosh : coshHalfMoment f = 0) :
    markovArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) =
      weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) +
        2 * sinhHalfMoment f ^ 2 := by
  unfold markovArchRe
  rw [re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq hf hfc, hcosh]
  ring

/-- **One-Mode Gauss–Pole + Sinh-Square Lower Bound for `markovCountertermEnergy` on the Primitive
Hyperplane**:
for any `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0` (in particular any odd test) and any counterterm
`lam : ℕ → ℝ`,
`(EF.gammaBracket 0 + 4) * ∫ f² + 2 * sinhHalfMoment f ^ 2 + ∫∫ f(u) f(v) exp(|u - v| / 2) du dv - primeBlindCounterterm lam f ≤ markovCountertermEnergy lam f`. -/
theorem oneMode_gauss_pole_add_sinh_sq_le_markovCountertermEnergy_of_cosh_zero
    (lam : ℕ → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) :
    (EF.gammaBracket 0 + 4) * (∫ u : ℝ, f u ^ 2) +
        2 * sinhHalfMoment f ^ 2 +
        (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (|p.1 - p.2| / 2)) -
        primeBlindCounterterm lam (realWeilTestFn f hf hfc) ≤
      markovCountertermEnergy lam (fun u => (f u : ℂ)) := by
  have h1 := oneMode_gauss_pole_le_weilArchRe hf hfc
  have h2 := markovArchRe_ofReal_eq_weilArchRe_add_sinh_sq_of_cosh_zero hf.continuous hfc hcosh
  have h3 : markovCountertermEnergy lam (fun u => (f u : ℂ)) =
      markovArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) -
        primeBlindCounterterm lam (realWeilTestFn f hf hfc) :=
    markovCountertermEnergy_eq_markovArchRe_sub_counterterm lam (realWeilTestFn f hf hfc)
  linarith

/-- **Two-Mode Gauss–Pole + Sinh-Square Lower Bound for `markovCountertermEnergy` on the Primitive
Hyperplane**:
for any `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0` (in particular any odd test) and any counterterm
`lam : ℕ → ℝ`,
`(EF.gammaBracket 0 + 24 / 5) * ∫ f² + 2 * sinhHalfMoment f ^ 2 + ∫∫ f(u) f(v) (exp(|u - v| / 2) - exp(-5 |u - v| / 2)) du dv - primeBlindCounterterm lam f ≤ markovCountertermEnergy lam f`. -/
theorem twoMode_gauss_pole_add_sinh_sq_le_markovCountertermEnergy_of_cosh_zero
    (lam : ℕ → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) :
    (EF.gammaBracket 0 + 24 / 5) * (∫ u : ℝ, f u ^ 2) +
        2 * sinhHalfMoment f ^ 2 +
        (∫ p : ℝ × ℝ, f p.1 * f p.2 *
          (Real.exp (|p.1 - p.2| / 2) - Real.exp (-5 * |p.1 - p.2| / 2))) -
        primeBlindCounterterm lam (realWeilTestFn f hf hfc) ≤
      markovCountertermEnergy lam (fun u => (f u : ℂ)) := by
  have h1 := twoMode_gauss_pole_le_weilArchRe hf hfc
  have h2 := markovArchRe_ofReal_eq_weilArchRe_add_sinh_sq_of_cosh_zero hf.continuous hfc hcosh
  have h3 : markovCountertermEnergy lam (fun u => (f u : ℂ)) =
      markovArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) -
        primeBlindCounterterm lam (realWeilTestFn f hf hfc) :=
    markovCountertermEnergy_eq_markovArchRe_sub_counterterm lam (realWeilTestFn f hf hfc)
  linarith

/-- **Pole-Free One-Mode Spectral Lower Bound for `markovArchRe` (All Signed Real Tests)**:
for every real test `f ∈ C²_c(ℝ)`, subtracting `weilPoleTerm` from `weilArchRe` yields
`(EF.gammaBracket 0 + 4) * ∫ f² - ∫ p : ℝ × ℝ, f p.1 * f p.2 * exp(-(1 / 2) * |p.1 - p.2|) ≤ markovArchRe k_f`. -/
theorem oneMode_gauss_le_markovArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (EF.gammaBracket 0 + 4) * (∫ u : ℝ, f u ^ 2) -
        (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|)) ≤
      markovArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hJ := jumpEnergy_ne_top_of_smooth hf hfc
  have h1 := ENNReal.toReal_mono hJ (ofReal_oneMode_le_jumpEnergy hB)
  rw [markovArchRe_ofReal_eq_levy hf hfc]
  rcases le_or_gt 0
      (4 * (∫ u, f u ^ 2) - ∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|)) with
    ha | ha
  · rw [ENNReal.toReal_ofReal ha] at h1
    linarith
  · have h2 : 0 ≤ (jumpEnergy f).toReal := ENNReal.toReal_nonneg
    linarith

/-- **Pole-Free Two-Mode Spectral Lower Bound for `markovArchRe` (All Signed Real Tests)**:
for every real test `f ∈ C²_c(ℝ)`,
`(EF.gammaBracket 0 + 24 / 5) * ∫ f² - (∫∫ f(u)f(v) e^{-|u-v|/2} + ∫∫ f(u)f(v) e^{-5|u-v|/2}) ≤ markovArchRe k_f`. -/
theorem twoMode_gauss_le_markovArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (EF.gammaBracket 0 + 24 / 5) * (∫ u : ℝ, f u ^ 2) -
        ((∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|)) +
          ∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(5 / 2) * |p.1 - p.2|)) ≤
      markovArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hJ := jumpEnergy_ne_top_of_smooth hf hfc
  have h1 := ENNReal.toReal_mono hJ (ofReal_twoMode_le_jumpEnergy hB)
  rw [markovArchRe_ofReal_eq_levy hf hfc]
  rcases le_or_gt 0
      ((24 / 5) * (∫ u, f u ^ 2) -
        ((∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|)) +
          ∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(5 / 2) * |p.1 - p.2|))) with
    ha | ha
  · rw [ENNReal.toReal_ofReal ha] at h1
    linarith
  · have h2 : 0 ≤ (jumpEnergy f).toReal := ENNReal.toReal_nonneg
    linarith

/-! ## Section 4: Plastic Lévy–Cosh Crossover + Bonus Sinh-Square Lower Bounds and Unconditional Short-Support Positivity on the Primitive Hyperplane and Odd Sector -/

/-- **Plastic Lévy–Cosh Crossover + Bonus Sinh-Square Lower Bound for `markovCountertermEnergy`
on the Primitive Hyperplane**:
for any `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0` (in particular any odd test), any counterterm
`lam : ℕ → ℝ`, and any `0 < δ ≤ c ≤ screwSignThreshold`,
`(A(0) + levyCoshPotential c) ∫ f² + 2 S(f)² + ∫_{x ∈ (δ, c)} (-screwRegularKernel x) ‖f - f(· + x)‖₂² + ∫∫ f(u) f(v) (2 cosh((u - v)/2) - levyCoshKernel c |u - v|) du dv - primeBlindCounterterm lam f ≤ markovCountertermEnergy lam f`. -/
theorem levyCosh_crossover_add_sinh_sq_le_markovCountertermEnergy_of_cosh_zero
    (lam : ℕ → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {δ c : ℝ} (hδ : 0 < δ) (hδc : δ ≤ c)
    (hct : c ≤ screwSignThreshold) :
    (EF.gammaBracket 0 + levyCoshPotential c) * (∫ u : ℝ, f u ^ 2) +
        2 * sinhHalfMoment f ^ 2 +
        (∫ x in Ioo δ c, (-screwRegularKernel x) * (∫ u, (f u - f (u + x)) ^ 2)) +
        (∫ p : ℝ × ℝ, f p.1 * f p.2 *
          (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) -
        primeBlindCounterterm lam (realWeilTestFn f hf hfc) ≤
      markovCountertermEnergy lam (fun u => (f u : ℂ)) := by
  have h1 := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hδ hδc hct
  have h2 := markovArchRe_ofReal_eq_weilArchRe_add_sinh_sq_of_cosh_zero hf.continuous hfc hcosh
  have h3 : markovCountertermEnergy lam (fun u => (f u : ℂ)) =
      markovArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) -
        primeBlindCounterterm lam (realWeilTestFn f hf hfc) :=
    markovCountertermEnergy_eq_markovArchRe_sub_counterterm lam (realWeilTestFn f hf hfc)
  linarith

/-- If `f : ℝ → ℝ` vanishes outside `[a, a + L]` and `|y| > L`, then `EF.weilTest f f y = 0`. -/
theorem weilTest_ofReal_eq_zero_of_support_Icc {f : ℝ → ℝ} {a L y : ℝ}
    (hsupp : ∀ u ∉ Icc a (a + L), f u = 0) (hy : L < |y|) :
    EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) y = 0 := by
  rw [weilTest_apply]
  have h0 : (fun t : ℝ => (f t : ℂ) * (starRingEnd ℂ) (f (t - y) : ℂ)) = fun _ => 0 := by
    funext t
    by_cases ht : t ∈ Icc a (a + L)
    · have hty : t - y ∉ Icc a (a + L) := by
        intro hmem
        have habs : |y| ≤ L := abs_le.mpr ⟨by linarith [ht.1, hmem.2], by linarith [ht.2, hmem.1]⟩
        linarith
      simp [hsupp (t - y) hty]
    · simp [hsupp t ht]
  rw [h0, integral_zero]

/-- **Automatic Prime-Blindness of Tests Supported on Intervals of Length `≤ screwSignThreshold`**:
because `screwSignThreshold < 151 / 500 < 17 / 25 < log 2 ≤ log n` for all `n ≥ 2`, any `f ∈ C²_c(ℝ)`
vanishing outside `[a, a + L]` with `L ≤ screwSignThreshold` has `logValue f n = 0` for all `n ≥ 2`
and hence `primeBlindCounterterm lam f = 0` for **every** counterterm sequence `lam : ℕ → ℝ`. -/
theorem primeBlindCounterterm_eq_zero_of_support_Icc_le_threshold (lam : ℕ → ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {a L : ℝ} (hLt : L ≤ screwSignThreshold)
    (hsupp : ∀ u ∉ Icc a (a + L), f u = 0) :
    primeBlindCounterterm lam (realWeilTestFn f hf hfc) = 0 := by
  have hN : ∀ n : ℕ, 1 < n →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log n) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log n) = 0 := by
    intro n hn
    have hn2 : 2 ≤ n := hn
    have hlog : Real.log 2 ≤ Real.log n :=
      Real.log_le_log two_pos (by exact_mod_cast hn2 : (2 : ℝ) ≤ n)
    have hgt : L < Real.log n := by
      linarith [screwSignThreshold_lt, WeilExcess.seventeen_div_twentyfive_lt_log_two]
    have hpos : 0 < Real.log n := by
      linarith [WeilExcess.seventeen_div_twentyfive_lt_log_two]
    constructor
    · exact weilTest_ofReal_eq_zero_of_support_Icc hsupp (by rwa [abs_of_pos hpos])
    · exact weilTest_ofReal_eq_zero_of_support_Icc hsupp (by rwa [abs_neg, abs_of_pos hpos])
  rw [primeBlindCounterterm_eq_sum_Icc lam (f := realWeilTestFn f hf hfc) (N := 1) hN,
    Finset.Icc_eq_empty (by omega), Finset.sum_empty]

/-- **Short-Support Plastic-Crossover + Sinh-Square Lower Bound on the Primitive Hyperplane**:
for every `f ∈ C²_c(ℝ)` on the primitive hyperplane `coshHalfMoment f = 0` vanishing outside
`[a, a + L]` with `0 < L ≤ screwSignThreshold`, and for **every** counterterm sequence `lam : ℕ → ℝ`,
`(EF.gammaBracket 0 + levyCoshPotential L) * ∫ f² + 2 * sinhHalfMoment f ^ 2 ≤ markovCountertermEnergy lam f`. -/
theorem levyCosh_short_support_add_sinh_sq_le_markovCountertermEnergy_of_cosh_zero
    (lam : ℕ → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {a L : ℝ} (hL0 : 0 < L) (hLt : L ≤ screwSignThreshold)
    (hsupp : ∀ u ∉ Icc a (a + L), f u = 0) :
    (EF.gammaBracket 0 + levyCoshPotential L) * (∫ u : ℝ, f u ^ 2) +
        2 * sinhHalfMoment f ^ 2 ≤
      markovCountertermEnergy lam (fun u => (f u : ℂ)) := by
  have h1 := levyCosh_signed_short_support_le_weilArchRe hf hfc hL0 hLt hsupp
  have h2 := markovArchRe_ofReal_eq_weilArchRe_add_sinh_sq_of_cosh_zero hf.continuous hfc hcosh
  have h3 : markovCountertermEnergy lam (fun u => (f u : ℂ)) =
      markovArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) -
        primeBlindCounterterm lam (realWeilTestFn f hf hfc) :=
    markovCountertermEnergy_eq_markovArchRe_sub_counterterm lam (realWeilTestFn f hf hfc)
  have h4 := primeBlindCounterterm_eq_zero_of_support_Icc_le_threshold lam hf hfc hLt hsupp
  linarith

/-- **Unconditional Short-Support Positivity with Sinh-Square Bonus on the Primitive Hyperplane**:
if `f ∈ C²_c(ℝ)` satisfies `coshHalfMoment f = 0` and vanishes outside `[a, a + L]` with
`0 < L ≤ screwSignThreshold` and `-EF.gammaBracket 0 ≤ levyCoshPotential L`, then for every
counterterm sequence `lam : ℕ → ℝ`,
`2 * sinhHalfMoment f ^ 2 ≤ markovCountertermEnergy lam (fun u => (f u : ℂ))`. -/
theorem two_mul_sinh_sq_le_markovCountertermEnergy_of_cosh_zero_support_Icc_le
    (lam : ℕ → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {a L : ℝ} (hL0 : 0 < L) (hLt : L ≤ screwSignThreshold)
    (hsupp : ∀ u ∉ Icc a (a + L), f u = 0)
    (hΦ : -EF.gammaBracket 0 ≤ levyCoshPotential L) :
    2 * sinhHalfMoment f ^ 2 ≤ markovCountertermEnergy lam (fun u => (f u : ℂ)) := by
  have hmain := levyCosh_short_support_add_sinh_sq_le_markovCountertermEnergy_of_cosh_zero
    lam hf hfc hcosh hL0 hLt hsupp
  have hsq : 0 ≤ ∫ u : ℝ, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  nlinarith

/-- **Concrete Unconditional Short-Support Positivity on `[a, a + L]` (`0 < L ≤ 1 / 130`)
for `markovEnergy` on the Primitive Hyperplane and on Odd Tests**:
every `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0` (in particular every odd test) vanishing outside
`[a, a + L]` with `0 < L ≤ 1 / 130` satisfies
`2 * sinhHalfMoment f ^ 2 ≤ markovEnergy (fun u => (f u : ℂ))`. -/
theorem two_mul_sinh_sq_le_markovEnergy_of_cosh_zero_support_Icc_le_inv_130
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {a L : ℝ} (hL0 : 0 < L) (hL : L ≤ 1 / 130)
    (hsupp : ∀ u ∉ Icc a (a + L), f u = 0) :
    2 * sinhHalfMoment f ^ 2 ≤ markovEnergy (fun u => (f u : ℂ)) := by
  have hLt : L ≤ screwSignThreshold := by linarith [screwSignThreshold_gt]
  have hΦ : -EF.gammaBracket 0 ≤ levyCoshPotential L :=
    (neg_gammaBracket_zero_le_two_mul_archLevyAntideriv hL0 hL).trans
      (two_mul_archLevyAntideriv_lt_levyCoshPotential hL0).le
  exact two_mul_sinh_sq_le_markovCountertermEnergy_of_cosh_zero_support_Icc_le
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) hf hfc hcosh hL0 hLt hsupp hΦ

/-- Specialization of `two_mul_sinh_sq_le_markovEnergy_of_cosh_zero_support_Icc_le_inv_130` to odd
tests `f (-x) = -f x`. -/
theorem two_mul_sinh_sq_le_markovEnergy_of_odd_support_Icc_le_inv_130
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hodd : ∀ x, f (-x) = -f x) {a L : ℝ} (hL0 : 0 < L) (hL : L ≤ 1 / 130)
    (hsupp : ∀ u ∉ Icc a (a + L), f u = 0) :
    2 * sinhHalfMoment f ^ 2 ≤ markovEnergy (fun u => (f u : ℂ)) :=
  two_mul_sinh_sq_le_markovEnergy_of_cosh_zero_support_Icc_le_inv_130
    hf hfc (coshHalfMoment_eq_zero_of_odd hodd) hL0 hL hsupp

end RHTower

end
