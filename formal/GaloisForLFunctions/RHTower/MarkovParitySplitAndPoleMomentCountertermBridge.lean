import GaloisForLFunctions.RHTower.EulerMaclaurinCountertermQuadratureAndOneSidedPBAP

/-!
# Universal Parity Split, Decaying/Growing Pole Moments, and the Double-Negative Continuum Pole Theorem on the Primitive Hyperplane

Building on `EulerMaclaurinCountertermQuadratureAndOneSidedPBAP`, `WeilMarkovOddPositivity`, and
`WeilMarkovPrimitiveHyperplane`, this module establishes three structural results on Route HF / PBAP:

1. **Section 1 (Universal Parity Split of `weilContinuumLogProfile`, `logValue`, `logVector`,
   `primeBlindCounterterm`, `weilFullFunctional`, and `markovCountertermEnergy`):**
   - For every real test `F : ℝ → ℝ`, the decomposition `F = evenPartReal F + oddPartReal F` splits
     the symmetric autocorrelation `k_F(y) + k_F(-y)` additively without cross terms at every `y : ℝ`
     (`weilTest_ofReal_add_neg_eq_even_add_odd`), because the cross-correlations `crossCorr Fe Fo`
     and `crossCorr Fo Fe` are odd functions.
   - Consequently, `primeIntegrand`, `weilContinuumLogProfile`, `logValue`, `logVector`, and
     `primeBlindCounterterm lam` split additively into their even and odd parts for **every**
     counterterm weight sequence `lam : ℕ → ℝ` simultaneously.
   - The pole functional `weilPoleTerm` splits orthogonally into its positive even square
     `+2 C(F_e)² = +2 C(F)²` and its negative odd square `-2 S(F_o)² = -2 S(F)²`, so `weilArchRe`,
     `markovArchRe`, `(weilFullFunctional lam).re`, and `markovCountertermEnergy lam` all split
     additively across `F = F_e + F_o` for every `lam : ℕ → ℝ`.

2. **Section 2 (Bochner Positivity of the Decaying Pole Moment and the Double-Negative Continuum
   Pole Theorem on the Primitive Hyperplane and on Odd Tests):**
   - We prove that for every `f : WeilTestFn`, the decaying exponential moment
     `∫ u : ℝ, Real.exp (-|u| / 2) * (EF.weilTest f.1 f.1 u).re` equals the nonnegative spectral
     integral `(1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2)) ≥ 0`
     (`re_integral_expNegHalfAbs_weilTest_eq`, `re_integral_expNegHalfAbs_weilTest_nonneg`).
   - Combining `re_paperFT_pole_sub_lebesguePart_eq_exp_neg_abs` with the rank-2 `(1, 1)` pole
     signature `2 C(f)² - 2 S(f)²`, we prove the exact identity for the growing continuum pole
     integral of any real `f ∈ C²_c(ℝ)`:
     `(∫ x, primeIntegrand k_f x ∂lebesguePart).re = 2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2 - ∫ u : ℝ, Real.exp (-|u| / 2) * (k_f u).re`.
   - On the **primitive hyperplane** `coshHalfMoment f = 0` — and in particular for **every odd
     test** `f(-x) = -f(x)` — the positive square `2 C(f)²` vanishes and the growing continuum pole
     integral is **unconditionally nonpositive** (bounded above by the sum of two nonpositive terms
     `-2 S(f)² ≤ 0` and `-(1/(2π)) ∫ |f̂(r)|² / (1/4 + r²) dr ≤ 0`).
   - Consequently, on the primitive hyperplane and on all odd tests, the discrete unit-step Poisson
     comb counterterm `primeBlindCounterterm unitStepCountertermWeight` is bounded above purely by
     `-rightCellQuadratureDefect (weilContinuumLogProfile F) N - 2 * sinhHalfMoment f ^ 2`!

3. **Section 3 (Counterterm Splitting, `m`-th Cesàro Monotonicity, and Test-Dependent Counterterm
   Criteria for `markovCountertermEnergy` and `markovEnergy`):**
   - We prove baseline-plus-fluctuation splitting and the `m`-th order Cesàro comparison principle
     for `markovCountertermEnergy`, together with test-dependent counterterm sufficiency criteria for
     `RiemannHypothesis` on odd tests and on the primitive hyperplane.
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

/-! ## Section 1: Universal Parity Split of `weilContinuumLogProfile`, `logValue`, `logVector`, `primeBlindCounterterm`, `weilFullFunctional`, and `markovCountertermEnergy` -/

/-- **Symmetric Autocorrelation Parity Split**:
for any continuous compactly supported real function `F : ℝ → ℝ` and any shift `y : ℝ`, the odd
cross-correlations `crossCorr (evenPartReal F) (oddPartReal F)` and
`crossCorr (oddPartReal F) (evenPartReal F)` cancel between `y` and `-y`, so
`k_F(y) + k_F(-y) = (k_{F_e}(y) + k_{F_e}(-y)) + (k_{F_o}(y) + k_{F_o}(-y))`. -/
theorem weilTest_ofReal_add_neg_eq_even_add_odd {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (y : ℝ) :
    EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) y +
        EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) (-y) =
      (EF.weilTest (fun x => (evenPartReal F x : ℂ)) (fun x => (evenPartReal F x : ℂ)) y +
          EF.weilTest (fun x => (evenPartReal F x : ℂ)) (fun x => (evenPartReal F x : ℂ)) (-y)) +
        (EF.weilTest (fun x => (oddPartReal F x : ℂ)) (fun x => (oddPartReal F x : ℂ)) y +
          EF.weilTest (fun x => (oddPartReal F x : ℂ)) (fun x => (oddPartReal F x : ℂ)) (-y)) := by
  set Fe := evenPartReal F
  set Fo := oddPartReal F
  have hFe : Continuous Fe := (hF.add (hF.comp continuous_neg)).div_const 2
  have hFo : Continuous Fo := (hF.sub (hF.comp continuous_neg)).div_const 2
  have hFec := hasCompactSupport_evenPartReal hFc
  have hFoc := hasCompactSupport_oddPartReal hFc
  have hk : ∀ z : ℝ, EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) z =
      EF.weilTest (fun x => (Fe x : ℂ)) (fun x => (Fe x : ℂ)) z +
        EF.weilTest (fun x => (Fo x : ℂ)) (fun x => (Fo x : ℂ)) z +
        ((crossCorr Fe Fo z + crossCorr Fo Fe z : ℝ) : ℂ) := by
    intro z
    have hFsum : (fun x => Fe x + Fo x) = F := funext (evenPartReal_add_oddPartReal F)
    have hcc := crossCorr_add_add hFe hFec hFo hFoc z
    rw [hFsum] at hcc
    rw [weilTest_ofReal_eq, weilTest_ofReal_eq, weilTest_ofReal_eq]
    change ((crossCorr F F z : ℝ) : ℂ) = ((crossCorr Fe Fe z : ℝ) : ℂ) +
      ((crossCorr Fo Fo z : ℝ) : ℂ) + ((crossCorr Fe Fo z + crossCorr Fo Fe z : ℝ) : ℂ)
    rw [hcc]
    push_cast
    ring
  have hcross : crossCorr Fe Fo y + crossCorr Fo Fe y +
      (crossCorr Fe Fo (-y) + crossCorr Fo Fe (-y)) = 0 := by
    rw [crossCorr_even_odd_neg (evenPartReal_neg F) (oddPartReal_neg F),
      crossCorr_odd_even_neg (evenPartReal_neg F) (oddPartReal_neg F)]
    ring
  have hcrossC : (((crossCorr Fe Fo y + crossCorr Fo Fe y : ℝ) : ℂ) +
      ((crossCorr Fe Fo (-y) + crossCorr Fo Fe (-y) : ℝ) : ℂ)) = 0 := by
    rw [← Complex.ofReal_add, hcross, Complex.ofReal_zero]
  rw [hk y, hk (-y)]
  linear_combination hcrossC

/-- **Parity Split of `primeIntegrand`**:
for any continuous compactly supported `F : ℝ → ℝ` and any `x : ℝ`, `primeIntegrand` splits
additively across `F = evenPartReal F + oddPartReal F`. -/
theorem primeIntegrand_ofReal_eq_even_add_odd {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (x : ℝ) :
    primeIntegrand (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ))) x =
      primeIntegrand
          (EF.weilTest (fun u => (evenPartReal F u : ℂ)) (fun u => (evenPartReal F u : ℂ))) x +
        primeIntegrand
          (EF.weilTest (fun u => (oddPartReal F u : ℂ)) (fun u => (oddPartReal F u : ℂ))) x := by
  unfold primeIntegrand
  rw [weilTest_ofReal_add_neg_eq_even_add_odd hF hFc (Real.log x), mul_add]

/-- **Parity Split of `weilContinuumLogProfile`**:
for any continuous compactly supported `F : ℝ → ℝ` and any `x : ℝ`,
`weilContinuumLogProfile F x = weilContinuumLogProfile (evenPartReal F) x + weilContinuumLogProfile (oddPartReal F) x`. -/
theorem weilContinuumLogProfile_ofReal_eq_even_add_odd {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (x : ℝ) :
    weilContinuumLogProfile (fun u => (F u : ℂ)) x =
      weilContinuumLogProfile (fun u => (evenPartReal F u : ℂ)) x +
        weilContinuumLogProfile (fun u => (oddPartReal F u : ℂ)) x := by
  unfold weilContinuumLogProfile
  rw [primeIntegrand_ofReal_eq_even_add_odd hF hFc x, Complex.add_re]

/-- **Parity Split of `logValue`**:
for any continuous compactly supported `F : ℝ → ℝ` and any natural number `n : ℕ`,
`logValue F n = logValue (evenPartReal F) n + logValue (oddPartReal F) n`. -/
theorem logValue_ofReal_eq_even_add_odd {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (n : ℕ) :
    logValue (fun u => (F u : ℂ)) n =
      logValue (fun u => (evenPartReal F u : ℂ)) n +
        logValue (fun u => (oddPartReal F u : ℂ)) n := by
  rw [← weilContinuumLogProfile_natCast_eq_logValue,
    ← weilContinuumLogProfile_natCast_eq_logValue,
    ← weilContinuumLogProfile_natCast_eq_logValue]
  exact weilContinuumLogProfile_ofReal_eq_even_add_odd hF hFc (n : ℝ)

/-- **Parity Split of `logVector`**:
for any `F ∈ C²_c(ℝ)`, `logVector` splits additively across `evenPartReal F` and `oddPartReal F`. -/
theorem logVector_realWeilTestFn_eq_even_add_odd {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) :
    logVector (realWeilTestFn F hF hFc) =
      logVector (realWeilTestFn (evenPartReal F) (contDiff_evenPartReal hF)
        (hasCompactSupport_evenPartReal hFc)) +
        logVector (realWeilTestFn (oddPartReal F) (contDiff_oddPartReal hF)
          (hasCompactSupport_oddPartReal hFc)) := by
  ext j
  rw [Finsupp.add_apply, logVector_apply, logVector_apply, logVector_apply]
  exact logValue_ofReal_eq_even_add_odd hF.continuous hFc j.1

/-- **Universal Counterterm Parity Split**:
for every `F ∈ C²_c(ℝ)` and **every** counterterm weight sequence `lam : ℕ → ℝ`,
`primeBlindCounterterm lam` splits additively into its even and odd parts without cross terms. -/
theorem primeBlindCounterterm_realWeilTestFn_eq_even_add_odd (lam : ℕ → ℝ) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) :
    primeBlindCounterterm lam (realWeilTestFn F hF hFc) =
      primeBlindCounterterm lam (realWeilTestFn (evenPartReal F) (contDiff_evenPartReal hF)
        (hasCompactSupport_evenPartReal hFc)) +
        primeBlindCounterterm lam (realWeilTestFn (oddPartReal F) (contDiff_oddPartReal hF)
          (hasCompactSupport_oddPartReal hFc)) := by
  unfold primeBlindCounterterm
  rw [logVector_realWeilTestFn_eq_even_add_odd hF hFc, map_add]

/-- For any even test `u : ℝ → ℝ`, `sinhHalfMoment u = 0`. -/
theorem sinhHalfMoment_eq_zero_of_even {u : ℝ → ℝ} (heven : ∀ x, u (-x) = u x) :
    sinhHalfMoment u = 0 := by
  unfold sinhHalfMoment
  have h : ∫ x : ℝ, u x * Real.sinh (x / 2) = -∫ x : ℝ, u x * Real.sinh (x / 2) := by
    rw [← integral_neg, ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [heven, show -x / 2 = -(x / 2) by ring, Real.sinh_neg]
    ring
  linarith

/-- The even cosh moment of `F` equals the cosh moment of `evenPartReal F`. -/
theorem coshHalfMoment_eq_evenPartReal {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) :
    coshHalfMoment F = coshHalfMoment (evenPartReal F) := by
  have hFe : Continuous (evenPartReal F) := (hF.add (hF.comp continuous_neg)).div_const 2
  have hFo : Continuous (oddPartReal F) := (hF.sub (hF.comp continuous_neg)).div_const 2
  have i1 : Integrable fun x : ℝ => evenPartReal F x * Real.cosh (x / 2) :=
    (hFe.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_evenPartReal hFc).mul_right
  have i2 : Integrable fun x : ℝ => oddPartReal F x * Real.cosh (x / 2) :=
    (hFo.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_oddPartReal hFc).mul_right
  have hsum : coshHalfMoment F =
      coshHalfMoment (evenPartReal F) + coshHalfMoment (oddPartReal F) := by
    unfold coshHalfMoment
    rw [← integral_add i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← add_mul, evenPartReal_add_oddPartReal]
  rw [hsum, coshHalfMoment_eq_zero_of_odd (oddPartReal_neg F), add_zero]

/-- The odd sinh moment of `F` equals the sinh moment of `oddPartReal F`. -/
theorem sinhHalfMoment_eq_oddPartReal {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) :
    sinhHalfMoment F = sinhHalfMoment (oddPartReal F) := by
  have hFe : Continuous (evenPartReal F) := (hF.add (hF.comp continuous_neg)).div_const 2
  have hFo : Continuous (oddPartReal F) := (hF.sub (hF.comp continuous_neg)).div_const 2
  have i1 : Integrable fun x : ℝ => evenPartReal F x * Real.sinh (x / 2) :=
    (hFe.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_evenPartReal hFc).mul_right
  have i2 : Integrable fun x : ℝ => oddPartReal F x * Real.sinh (x / 2) :=
    (hFo.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_oddPartReal hFc).mul_right
  have hsum : sinhHalfMoment F =
      sinhHalfMoment (evenPartReal F) + sinhHalfMoment (oddPartReal F) := by
    unfold sinhHalfMoment
    rw [← integral_add i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← add_mul, evenPartReal_add_oddPartReal]
  rw [hsum, sinhHalfMoment_eq_zero_of_even (evenPartReal_neg F), zero_add]

/-- On `evenPartReal F`, the pole term is the pure nonnegative square `+2 * coshHalfMoment F ^ 2`. -/
theorem re_weilPoleTerm_evenPartReal_eq {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) :
    (weilPoleTerm (EF.weilTest (fun x => (evenPartReal F x : ℂ))
      (fun x => (evenPartReal F x : ℂ)))).re = 2 * coshHalfMoment F ^ 2 := by
  have hFe : Continuous (evenPartReal F) := (hF.add (hF.comp continuous_neg)).div_const 2
  rw [re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq hFe
    (hasCompactSupport_evenPartReal hFc),
    ← coshHalfMoment_eq_evenPartReal hF hFc,
    sinhHalfMoment_eq_zero_of_even (evenPartReal_neg F)]
  ring

/-- On `oddPartReal F`, the pole term is the pure nonpositive square `-2 * sinhHalfMoment F ^ 2`. -/
theorem re_weilPoleTerm_oddPartReal_eq {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) :
    (weilPoleTerm (EF.weilTest (fun x => (oddPartReal F x : ℂ))
      (fun x => (oddPartReal F x : ℂ)))).re = -(2 * sinhHalfMoment F ^ 2) := by
  have hFo : Continuous (oddPartReal F) := (hF.sub (hF.comp continuous_neg)).div_const 2
  rw [re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq hFo
    (hasCompactSupport_oddPartReal hFc),
    coshHalfMoment_eq_zero_of_odd (oddPartReal_neg F),
    ← sinhHalfMoment_eq_oddPartReal hF hFc]
  ring

/-- **Parity Split of `weilPoleTerm`**:
for any continuous compactly supported `F : ℝ → ℝ`, `(weilPoleTerm k_F).re` splits additively into
its even positive square `(weilPoleTerm k_{F_e}).re = 2 C(F)²` and its odd negative square
`(weilPoleTerm k_{F_o}).re = -2 S(F)²`. -/
theorem re_weilPoleTerm_ofReal_eq_even_add_odd {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) :
    (weilPoleTerm (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re =
      (weilPoleTerm (EF.weilTest (fun x => (evenPartReal F x : ℂ))
        (fun x => (evenPartReal F x : ℂ)))).re +
        (weilPoleTerm (EF.weilTest (fun x => (oddPartReal F x : ℂ))
          (fun x => (oddPartReal F x : ℂ)))).re := by
  rw [re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq hF hFc,
    re_weilPoleTerm_evenPartReal_eq hF hFc, re_weilPoleTerm_oddPartReal_eq hF hFc]
  ring

/-- **Parity Split of `markovArchRe`**:
for any `F ∈ C²_c(ℝ)`, `markovArchRe` splits additively across `evenPartReal F` and `oddPartReal F`. -/
theorem markovArchRe_ofReal_eq_even_add_odd {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) :
    markovArchRe (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ))) =
      markovArchRe (EF.weilTest (fun x => (evenPartReal F x : ℂ))
        (fun x => (evenPartReal F x : ℂ))) +
        markovArchRe (EF.weilTest (fun x => (oddPartReal F x : ℂ))
          (fun x => (oddPartReal F x : ℂ))) := by
  have hm := markovEnergy_ofReal_eq_even_add_odd hF hFc
  have h1 : markovEnergy (fun x => (F x : ℂ)) =
      markovArchRe (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ))) -
        primeBlindCounterterm (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (realWeilTestFn F hF hFc) :=
    markovEnergy_eq_markovArchRe_sub_counterterm (realWeilTestFn F hF hFc)
  have h2 : markovEnergy (fun x => (evenPartReal F x : ℂ)) =
      markovArchRe (EF.weilTest (fun x => (evenPartReal F x : ℂ))
        (fun x => (evenPartReal F x : ℂ))) -
        primeBlindCounterterm (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (realWeilTestFn (evenPartReal F) (contDiff_evenPartReal hF)
            (hasCompactSupport_evenPartReal hFc)) :=
    markovEnergy_eq_markovArchRe_sub_counterterm
      (realWeilTestFn (evenPartReal F) (contDiff_evenPartReal hF)
        (hasCompactSupport_evenPartReal hFc))
  have h3 : markovEnergy (fun x => (oddPartReal F x : ℂ)) =
      markovArchRe (EF.weilTest (fun x => (oddPartReal F x : ℂ))
        (fun x => (oddPartReal F x : ℂ))) -
        primeBlindCounterterm (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (realWeilTestFn (oddPartReal F) (contDiff_oddPartReal hF)
            (hasCompactSupport_oddPartReal hFc)) :=
    markovEnergy_eq_markovArchRe_sub_counterterm
      (realWeilTestFn (oddPartReal F) (contDiff_oddPartReal hF)
        (hasCompactSupport_oddPartReal hFc))
  have hc := primeBlindCounterterm_realWeilTestFn_eq_even_add_odd
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) hF hFc
  linarith

/-- **Parity Split of `weilArchRe`**:
for any `F ∈ C²_c(ℝ)`, `weilArchRe` splits additively across `evenPartReal F` and `oddPartReal F`. -/
theorem weilArchRe_ofReal_eq_even_add_odd {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) :
    weilArchRe (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ))) =
      weilArchRe (EF.weilTest (fun x => (evenPartReal F x : ℂ))
        (fun x => (evenPartReal F x : ℂ))) +
        weilArchRe (EF.weilTest (fun x => (oddPartReal F x : ℂ))
          (fun x => (oddPartReal F x : ℂ))) := by
  have h1 : ∀ k : ℝ → ℂ, weilArchRe k = markovArchRe k + (weilPoleTerm k).re := fun k => by
    unfold markovArchRe; ring
  rw [h1, h1, h1, markovArchRe_ofReal_eq_even_add_odd hF hFc,
    re_weilPoleTerm_ofReal_eq_even_add_odd hF.continuous hFc]
  ring

/-- **Universal Parity Split of `(weilFullFunctional lam).re`**:
for any `F ∈ C²_c(ℝ)` and **every** counterterm sequence `lam : ℕ → ℝ`,
`(weilFullFunctional lam k_F).re = (weilFullFunctional lam k_{F_e}).re + (weilFullFunctional lam k_{F_o}).re`. -/
theorem re_weilFullFunctional_ofReal_eq_even_add_odd (lam : ℕ → ℝ) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) :
    (weilFullFunctional lam (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re =
      (weilFullFunctional lam (EF.weilTest (fun x => (evenPartReal F x : ℂ))
        (fun x => (evenPartReal F x : ℂ)))).re +
        (weilFullFunctional lam (EF.weilTest (fun x => (oddPartReal F x : ℂ))
          (fun x => (oddPartReal F x : ℂ)))).re := by
  have h1 : (weilFullFunctional lam (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re =
      weilArchRe (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ))) -
        primeBlindCounterterm lam (realWeilTestFn F hF hFc) :=
    re_weilFullFunctional_eq_weilArchRe_sub_counterterm lam (realWeilTestFn F hF hFc)
  have h2 : (weilFullFunctional lam (EF.weilTest (fun x => (evenPartReal F x : ℂ))
      (fun x => (evenPartReal F x : ℂ)))).re =
      weilArchRe (EF.weilTest (fun x => (evenPartReal F x : ℂ))
        (fun x => (evenPartReal F x : ℂ))) -
        primeBlindCounterterm lam
          (realWeilTestFn (evenPartReal F) (contDiff_evenPartReal hF)
            (hasCompactSupport_evenPartReal hFc)) :=
    re_weilFullFunctional_eq_weilArchRe_sub_counterterm lam
      (realWeilTestFn (evenPartReal F) (contDiff_evenPartReal hF)
        (hasCompactSupport_evenPartReal hFc))
  have h3 : (weilFullFunctional lam (EF.weilTest (fun x => (oddPartReal F x : ℂ))
      (fun x => (oddPartReal F x : ℂ)))).re =
      weilArchRe (EF.weilTest (fun x => (oddPartReal F x : ℂ))
        (fun x => (oddPartReal F x : ℂ))) -
        primeBlindCounterterm lam
          (realWeilTestFn (oddPartReal F) (contDiff_oddPartReal hF)
            (hasCompactSupport_oddPartReal hFc)) :=
    re_weilFullFunctional_eq_weilArchRe_sub_counterterm lam
      (realWeilTestFn (oddPartReal F) (contDiff_oddPartReal hF)
        (hasCompactSupport_oddPartReal hFc))
  rw [h1, h2, h3, weilArchRe_ofReal_eq_even_add_odd hF hFc,
    primeBlindCounterterm_realWeilTestFn_eq_even_add_odd lam hF hFc]
  ring

/-- **Universal Parity Split of `markovCountertermEnergy lam`**:
for any `F ∈ C²_c(ℝ)` and **every** counterterm sequence `lam : ℕ → ℝ`,
`markovCountertermEnergy lam F = markovCountertermEnergy lam F_e + markovCountertermEnergy lam F_o`. -/
theorem markovCountertermEnergy_ofReal_eq_even_add_odd (lam : ℕ → ℝ) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) :
    markovCountertermEnergy lam (fun x => (F x : ℂ)) =
      markovCountertermEnergy lam (fun x => (evenPartReal F x : ℂ)) +
        markovCountertermEnergy lam (fun x => (oddPartReal F x : ℂ)) := by
  have h1 : markovCountertermEnergy lam (fun x => (F x : ℂ)) =
      markovArchRe (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ))) -
        primeBlindCounterterm lam (realWeilTestFn F hF hFc) :=
    markovCountertermEnergy_eq_markovArchRe_sub_counterterm lam (realWeilTestFn F hF hFc)
  have h2 : markovCountertermEnergy lam (fun x => (evenPartReal F x : ℂ)) =
      markovArchRe (EF.weilTest (fun x => (evenPartReal F x : ℂ))
        (fun x => (evenPartReal F x : ℂ))) -
        primeBlindCounterterm lam
          (realWeilTestFn (evenPartReal F) (contDiff_evenPartReal hF)
            (hasCompactSupport_evenPartReal hFc)) :=
    markovCountertermEnergy_eq_markovArchRe_sub_counterterm lam
      (realWeilTestFn (evenPartReal F) (contDiff_evenPartReal hF)
        (hasCompactSupport_evenPartReal hFc))
  have h3 : markovCountertermEnergy lam (fun x => (oddPartReal F x : ℂ)) =
      markovArchRe (EF.weilTest (fun x => (oddPartReal F x : ℂ))
        (fun x => (oddPartReal F x : ℂ))) -
        primeBlindCounterterm lam
          (realWeilTestFn (oddPartReal F) (contDiff_oddPartReal hF)
            (hasCompactSupport_oddPartReal hFc)) :=
    markovCountertermEnergy_eq_markovArchRe_sub_counterterm lam
      (realWeilTestFn (oddPartReal F) (contDiff_oddPartReal hF)
        (hasCompactSupport_oddPartReal hFc))
  rw [h1, h2, h3, markovArchRe_ofReal_eq_even_add_odd hF hFc,
    primeBlindCounterterm_realWeilTestFn_eq_even_add_odd lam hF hFc]
  ring

/-! ## Section 2: Bochner Positivity of the Decaying Pole Moment and the Double-Negative Continuum Pole Theorem on the Primitive Hyperplane -/

/-- **Spectral Evaluation of the Decaying Pole Moment `∫ e^{-|u|/2} (k_f u).re du`**:
for every `f : WeilTestFn`,
`∫ u : ℝ, Real.exp (-|u| / 2) * (EF.weilTest f.1 f.1 u).re = (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2))`. -/
theorem re_integral_expNegHalfAbs_weilTest_eq (f : WeilTestFn) :
    (∫ u : ℝ, Real.exp (-|u| / 2) * (EF.weilTest f.1 f.1 u).re) =
      (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2)) := by
  have hkd : ContDiff ℝ 2 (EF.weilTest f.1 f.1) :=
    EF.weilTest_contDiff f.2.1 f.2.1.continuous f.2.2
  have hkc : HasCompactSupport (EF.weilTest f.1 f.1) :=
    EF.weilTest_hasCompactSupport f.2.2 f.2.2
  have hki : Integrable (EF.weilTest f.1 f.1) :=
    hkd.continuous.integrable_of_hasCompactSupport hkc
  have hFk := EF.integrable_fourier_of_contDiff_two hkd hkc
  have h1 := integral_expNegHalfAbs_mul_eq hkd.continuous hki hFk
  have hFi : Integrable fun u : ℝ => (Real.exp (-|u| / 2) : ℂ) * EF.weilTest f.1 f.1 u :=
    ((by fun_prop : Continuous fun u : ℝ => (Real.exp (-|u| / 2) : ℂ)).mul
      hkd.continuous).integrable_of_hasCompactSupport hkc.mul_left
  have hre := integral_re hFi
  change ∫ u : ℝ, ((Real.exp (-|u| / 2) : ℂ) * EF.weilTest f.1 f.1 u).re =
    (∫ u : ℝ, (Real.exp (-|u| / 2) : ℂ) * EF.weilTest f.1 f.1 u).re at hre
  have hlhs : (∫ u : ℝ, Real.exp (-|u| / 2) * (EF.weilTest f.1 f.1 u).re) =
      (∫ u : ℝ, (Real.exp (-|u| / 2) : ℂ) * EF.weilTest f.1 f.1 u).re := by
    rw [← hre]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    exact (Complex.re_ofReal_mul (Real.exp (-|u| / 2)) (EF.weilTest f.1 f.1 u)).symm
  rw [hlhs, h1]
  have hPn : ∀ r : ℝ, paperFT (EF.weilTest f.1 f.1) r = ((‖paperFT f.1 r‖ ^ 2 : ℝ) : ℂ) :=
    fun r => by
      rw [EF.paperFT_weilTest f.2.1.continuous f.2.1.continuous f.2.2 f.2.2,
        Complex.conj_ofReal, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hrhs : (∫ r : ℝ, paperFT (EF.weilTest f.1 f.1) r * ((1 / (1 / 4 + r ^ 2) : ℝ) : ℂ)) =
      ((∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2)) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only
    rw [hPn]
    push_cast
    ring
  rw [hrhs, show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **Bochner Nonnegativity of the Decaying Pole Moment**:
for every `f : WeilTestFn`, `0 ≤ ∫ u : ℝ, Real.exp (-|u| / 2) * (EF.weilTest f.1 f.1 u).re`. -/
theorem re_integral_expNegHalfAbs_weilTest_nonneg (f : WeilTestFn) :
    0 ≤ ∫ u : ℝ, Real.exp (-|u| / 2) * (EF.weilTest f.1 f.1 u).re := by
  rw [re_integral_expNegHalfAbs_weilTest_eq]
  refine mul_nonneg (by positivity) (integral_nonneg fun r => ?_)
  positivity

/-- Sum of the growing continuum pole integral `(∫ primeIntegrand k d(lebesguePart)).re` and the
decaying exponential integral `∫ e^{-|u|/2} (k u).re du` equals `(weilPoleTerm k).re`. -/
theorem re_integral_primeIntegrand_lebesguePart_add_exp_neg_abs_eq_re_weilPoleTerm
    {k : ℝ → ℂ} (hk : Continuous k) (hkc : HasCompactSupport k) :
    (∫ x, primeIntegrand k x ∂lebesguePart).re +
        (∫ u : ℝ, Real.exp (-|u| / 2) * (k u).re) =
      (weilPoleTerm k).re := by
  have h := re_paperFT_pole_sub_lebesguePart_eq_exp_neg_abs hk hkc
  unfold weilPoleTerm
  rw [Complex.sub_re] at h
  linarith

/-- **Exact Pole-Signature Decomposition of the Growing Continuum `lebesguePart` Integral**:
for every real test `f ∈ C²_c(ℝ)`,
`(∫ x, primeIntegrand k_f x ∂lebesguePart).re = 2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2 - ∫ u : ℝ, Real.exp (-|u| / 2) * (k_f u).re`. -/
theorem re_integral_primeIntegrand_lebesguePart_ofReal_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (∫ x, primeIntegrand (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) x
        ∂lebesguePart).re =
      2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2 -
        ∫ u : ℝ, Real.exp (-|u| / 2) *
          (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) u).re := by
  have hkd : ContDiff ℝ 2 (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
    EF.weilTest_contDiff (realWeilTestFn f hf hfc).2.1 (realWeilTestFn f hf hfc).2.1.continuous
      (realWeilTestFn f hf hfc).2.2
  have hkc : HasCompactSupport (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
    EF.weilTest_hasCompactSupport (realWeilTestFn f hf hfc).2.2 (realWeilTestFn f hf hfc).2.2
  have hsum := re_integral_primeIntegrand_lebesguePart_add_exp_neg_abs_eq_re_weilPoleTerm
    hkd.continuous hkc
  have hpole := re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq hf.continuous hfc
  linarith

/-- **Exact Identity for the Growing Continuum `lebesguePart` Integral on the Primitive Hyperplane**:
when `coshHalfMoment f = 0`, the growing continuum pole integral equals
`-2 * sinhHalfMoment f ^ 2 - ∫ u : ℝ, Real.exp (-|u| / 2) * (k_f u).re`. -/
theorem re_integral_primeIntegrand_lebesguePart_ofReal_eq_of_cosh_zero {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hcosh : coshHalfMoment f = 0) :
    (∫ x, primeIntegrand (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) x
        ∂lebesguePart).re =
      -(2 * sinhHalfMoment f ^ 2) -
        ∫ u : ℝ, Real.exp (-|u| / 2) *
          (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) u).re := by
  rw [re_integral_primeIntegrand_lebesguePart_ofReal_eq hf hfc, hcosh]
  ring

/-- **Double-Negative Upper Bound I on the Primitive Hyperplane**:
when `coshHalfMoment f = 0`, the growing continuum pole integral is bounded above by
`-2 * sinhHalfMoment f ^ 2 ≤ 0`. -/
theorem re_integral_primeIntegrand_lebesguePart_ofReal_le_neg_two_mul_sinh_sq_of_cosh_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) :
    (∫ x, primeIntegrand (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) x
        ∂lebesguePart).re ≤
      -(2 * sinhHalfMoment f ^ 2) := by
  rw [re_integral_primeIntegrand_lebesguePart_ofReal_eq_of_cosh_zero hf hfc hcosh]
  have hnn := re_integral_expNegHalfAbs_weilTest_nonneg (realWeilTestFn f hf hfc)
  change 0 ≤ ∫ u : ℝ, Real.exp (-|u| / 2) *
    (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) u).re at hnn
  linarith

/-- **Double-Negative Upper Bound II on the Primitive Hyperplane**:
when `coshHalfMoment f = 0`, the growing continuum pole integral is bounded above by
`-∫ u : ℝ, Real.exp (-|u| / 2) * (k_f u).re ≤ 0`. -/
theorem re_integral_primeIntegrand_lebesguePart_ofReal_le_neg_exp_neg_abs_of_cosh_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) :
    (∫ x, primeIntegrand (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) x
        ∂lebesguePart).re ≤
      -∫ u : ℝ, Real.exp (-|u| / 2) *
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) u).re := by
  rw [re_integral_primeIntegrand_lebesguePart_ofReal_eq_of_cosh_zero hf hfc hcosh]
  nlinarith [sq_nonneg (sinhHalfMoment f)]

/-- **Unconditional Nonpositivity of the Growing Continuum Pole Integral on the Primitive Hyperplane**:
for every `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0`,
`(∫ x, primeIntegrand k_f x ∂lebesguePart).re ≤ 0`. -/
theorem re_integral_primeIntegrand_lebesguePart_ofReal_nonpos_of_cosh_zero {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hcosh : coshHalfMoment f = 0) :
    (∫ x, primeIntegrand (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) x
        ∂lebesguePart).re ≤ 0 := by
  have h := re_integral_primeIntegrand_lebesguePart_ofReal_le_neg_two_mul_sinh_sq_of_cosh_zero
    hf hfc hcosh
  nlinarith [sq_nonneg (sinhHalfMoment f)]

/-- **Unconditional Nonpositivity of the Growing Continuum Pole Integral on Odd Tests**:
for every odd `f ∈ C²_c(ℝ)` (`∀ x, f (-x) = -f x`),
`(∫ x, primeIntegrand k_f x ∂lebesguePart).re ≤ -(2 * sinhHalfMoment f ^ 2) ≤ 0`. -/
theorem re_integral_primeIntegrand_lebesguePart_ofReal_le_neg_two_mul_sinh_sq_of_odd {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hodd : ∀ x, f (-x) = -f x) :
    (∫ x, primeIntegrand (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) x
        ∂lebesguePart).re ≤
      -(2 * sinhHalfMoment f ^ 2) :=
  re_integral_primeIntegrand_lebesguePart_ofReal_le_neg_two_mul_sinh_sq_of_cosh_zero hf hfc
    (coshHalfMoment_eq_zero_of_odd hodd)

/-- For every odd `f ∈ C²_c(ℝ)`, `(∫ x, primeIntegrand k_f x ∂lebesguePart).re ≤ 0`. -/
theorem re_integral_primeIntegrand_lebesguePart_ofReal_nonpos_of_odd {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hodd : ∀ x, f (-x) = -f x) :
    (∫ x, primeIntegrand (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) x
        ∂lebesguePart).re ≤ 0 :=
  re_integral_primeIntegrand_lebesguePart_ofReal_nonpos_of_cosh_zero hf hfc
    (coshHalfMoment_eq_zero_of_odd hodd)

/-- **Unit-Step Poisson Comb Upper Bound on the Primitive Hyperplane**:
for any `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0` and cutoff `1 ≤ N`, the sum of the unit-step
Poisson comb `primeBlindCounterterm unitStepCountertermWeight` and the cell-quadrature defect
`rightCellQuadratureDefect` is bounded above by `-2 * sinhHalfMoment f ^ 2 ≤ 0`. -/
theorem primeBlindCounterterm_unitStep_add_rightCellQuadratureDefect_le_of_cosh_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0) :
    primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc) +
        rightCellQuadratureDefect
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N ≤
      -(2 * sinhHalfMoment f ^ 2) := by
  have h1 := re_integral_lebesguePart_sub_unitStep_eq_rightCellQuadratureDefect
    (realWeilTestFn f hf hfc) hN1 hN
  have h2 := re_integral_primeIntegrand_lebesguePart_ofReal_le_neg_two_mul_sinh_sq_of_cosh_zero
    hf hfc hcosh
  change (∫ x, primeIntegrand (EF.weilTest (realWeilTestFn f hf hfc).1
    (realWeilTestFn f hf hfc).1) x ∂lebesguePart).re ≤ _ at h2
  linarith

/-! ## Section 3: Counterterm Splitting, `m`-th Cesàro Monotonicity, and Test-Dependent Counterterm Criteria for `markovCountertermEnergy` and `markovEnergy` -/

/-- **Baseline-Plus-Fluctuation Splitting for `markovCountertermEnergy`**:
for any `f : WeilTestFn` and counterterm weights `lam₀ δ : ℕ → ℝ`,
`markovCountertermEnergy (lam₀ + δ) f.1 = markovCountertermEnergy lam₀ f.1 - primeBlindCounterterm δ f`. -/
theorem markovCountertermEnergy_add_counterterm (lam₀ δ : ℕ → ℝ) (f : WeilTestFn) :
    markovCountertermEnergy (lam₀ + δ) f.1 =
      markovCountertermEnergy lam₀ f.1 - primeBlindCounterterm δ f := by
  rw [markovCountertermEnergy_eq_markovArchRe_sub_counterterm,
    markovCountertermEnergy_eq_markovArchRe_sub_counterterm,
    primeBlindCounterterm_add]
  ring

/-- **The `m`-th Order Cesàro Comparison Principle for `markovCountertermEnergy`**:
for any order `m : ℕ` and support cutoff `N` of `f : WeilTestFn`, if
`0 ≤ iteratedForwardDiff m (logValue f.1) n` and
`countertermIteratedPrefixSum m lam₁ n ≤ countertermIteratedPrefixSum m lam₂ n` for all
`n ∈ Finset.Icc 2 N`, then `markovCountertermEnergy lam₂ f.1 ≤ markovCountertermEnergy lam₁ f.1`. -/
theorem markovCountertermEnergy_le_of_iteratedPrefixSum_le (m : ℕ) {lam₁ lam₂ : ℕ → ℝ}
    {f : WeilTestFn} {N : ℕ}
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N, 0 ≤ iteratedForwardDiff m (logValue f.1) n)
    (hdom : ∀ n ∈ Finset.Icc 2 N,
      countertermIteratedPrefixSum m lam₁ n ≤ countertermIteratedPrefixSum m lam₂ n) :
    markovCountertermEnergy lam₂ f.1 ≤ markovCountertermEnergy lam₁ f.1 := by
  rw [markovCountertermEnergy_eq_markovArchRe_sub_counterterm,
    markovCountertermEnergy_eq_markovArchRe_sub_counterterm]
  linarith [primeBlindCounterterm_le_of_iteratedPrefixSum_le m hN hdiff hdom]

/-- **Test-Dependent Counterterm Domination Criterion for `RiemannHypothesis` on Odd Tests**:
if for every odd real test `f ∈ C²_c(ℝ)` there exists *some* counterterm weight sequence
`lam : ℕ → ℝ` (which may depend on `f`) such that
`0 ≤ markovCountertermEnergy lam (fun x => (f x : ℂ))` and
`primeBlindCounterterm Λ (realWeilTestFn f hf hfc) ≤ primeBlindCounterterm lam (realWeilTestFn f hf hfc)`,
then `RiemannHypothesis` holds unconditionally. -/
theorem riemannHypothesis_of_forall_odd_exists_counterterm_markov_nonneg
    (h : ∀ f : ℝ → ℝ, (hf : ContDiff ℝ 2 f) → (hfc : HasCompactSupport f) →
      (∀ x, f (-x) = -f x) →
      ∃ lam : ℕ → ℝ,
        0 ≤ markovCountertermEnergy lam (fun x => (f x : ℂ)) ∧
          primeBlindCounterterm (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
            (realWeilTestFn f hf hfc) ≤
            primeBlindCounterterm lam (realWeilTestFn f hf hfc)) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_forall_odd_markovEnergy_nonneg.mpr fun f hf hfc hodd => ?_
  obtain ⟨lam, hnn, hle⟩ := h f hf hfc hodd
  have h1 := markovCountertermEnergy_eq_markovArchRe_sub_counterterm lam (realWeilTestFn f hf hfc)
  have h2 := markovEnergy_eq_markovArchRe_sub_counterterm (realWeilTestFn f hf hfc)
  change markovCountertermEnergy lam (fun x => (f x : ℂ)) = _ at h1
  change markovEnergy (fun x => (f x : ℂ)) = _ at h2
  linarith

/-- **Test-Dependent Counterterm Domination Criterion for `RiemannHypothesis` on the Primitive Hyperplane**:
if for every real test `f ∈ C²_c(ℝ)` on the primitive hyperplane `coshHalfMoment f = 0` there
exists *some* counterterm weight sequence `lam : ℕ → ℝ` (which may depend on `f`) such that
`0 ≤ markovCountertermEnergy lam (fun x => (f x : ℂ))` and
`primeBlindCounterterm Λ (realWeilTestFn f hf hfc) ≤ primeBlindCounterterm lam (realWeilTestFn f hf hfc)`,
then `RiemannHypothesis` holds unconditionally. -/
theorem riemannHypothesis_of_forall_cosh_zero_exists_counterterm_markov_nonneg
    (h : ∀ f : ℝ → ℝ, (hf : ContDiff ℝ 2 f) → (hfc : HasCompactSupport f) →
      coshHalfMoment f = 0 →
      ∃ lam : ℕ → ℝ,
        0 ≤ markovCountertermEnergy lam (fun x => (f x : ℂ)) ∧
          primeBlindCounterterm (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
            (realWeilTestFn f hf hfc) ≤
            primeBlindCounterterm lam (realWeilTestFn f hf hfc)) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_forall_cosh_moment_zero_markovEnergy_nonneg.mpr
    fun f hf hfc hcosh => ?_
  obtain ⟨lam, hnn, hle⟩ := h f hf hfc hcosh
  have h1 := markovCountertermEnergy_eq_markovArchRe_sub_counterterm lam (realWeilTestFn f hf hfc)
  have h2 := markovEnergy_eq_markovArchRe_sub_counterterm (realWeilTestFn f hf hfc)
  change markovCountertermEnergy lam (fun x => (f x : ℂ)) = _ at h1
  change markovEnergy (fun x => (f x : ℂ)) = _ at h2
  linarith

end RHTower

end
