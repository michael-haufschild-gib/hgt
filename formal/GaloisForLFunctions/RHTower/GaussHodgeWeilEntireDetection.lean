import GaloisForLFunctions.RHTower.GaussHodgeWeilFundamentalSymmetry
import GaloisForLFunctions.RHTower.XiHedenmalmMultiplicityChain

/-!
# Entire detection: the Weil criterion on analytic tests alone

The fundamental-symmetry criteria quantify over arbitrary square-summable tests, and their
converses use rough indicator witnesses.  This module removes the rough tests: the entire
(complex-differentiable) class already detects everything.

The witness is built from the corpus's canonical divided chain.  At a hypothetical off-line
divisor point `alpha` the terminal divided quotient `XiC(z)/(z-alpha)^m` (multiplicity-exact,
entire by iterated `dslope`) is nonzero at `alpha` and vanishes at every other divisor point;
combining the chains at `alpha` and at its reflection `conj alpha`, normalized by their center
values, gives an *entire*, square-summable, divisor-odd test taking the value `1` at `alpha` —
with no simplicity hypothesis and no conjugation symmetry of `XiC` used.

Consequences:

* `riemannHypothesis_iff_forall_entire_divisorOdd_eval_eq_zero` — RH ⟺ every **entire**
  divisor-odd test vanishes on the divisor: the odd sector cannot hide from analytic tests.
* `riemannHypothesis_iff_xiWeilPolarization_nonneg_entire` — RH ⟺ the diagonal Weil form is
  nonnegative on **entire** square-summable tests: Weil positivity cannot fail on rough tests
  only, so any producer that controls the analytic class controls everything.
* `riemannHypothesis_iff_polarization_parityFlip_invariant_entire` — RH ⟺ the Weil form agrees
  with its parity twist on entire tests.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## The terminal divided quotient vanishes at every other divisor point -/

/-- The multiplicity-exact terminal divided quotient at a divisor support point vanishes at
every divisor point other than its center: divide `XiC z = (z-a)^m * chain z` by the nonzero
factor `(z-a)^m`. -/
theorem xiThetaDividedChain_terminal_eq_zero_of_ne (rho : XiDivisorSupport) {x : ℂ}
    (hx : XiC x = 0) (hne : x ≠ xiSpectralPointSupport rho) :
    xiThetaDividedChain (xiSpectralPointSupport rho) (xiSupportMultiplicity rho) x = 0 := by
  obtain ⟨-, -, hfact⟩ := xiThetaDividedChain_local_order rho
  have h := (hfact x).symm
  rw [hx] at h
  have hpow : (x - xiSpectralPointSupport rho) ^ xiSupportMultiplicity rho ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr hne)
  exact (mul_eq_zero.mp h).resolve_left hpow

/-! ## The entire divisor-odd witness at an off-line divisor point -/

/-- **The entire odd witness.**  At any divisor copy whose centered spectral point is not real
there is an entire, square-summable, divisor-odd test with value `1` there.  The construction
is multiplicity-exact: normalized terminal divided quotients at the point and at its
reflection. -/
theorem exists_entire_divisorOdd_unit_test (q0 : XiZeroCopy)
    (hne : (starRingEnd ℂ) (xiSpectralPoint q0) ≠ xiSpectralPoint q0) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ XiWeilDivisorOdd F ∧
      XiWeilSquareSummable F ∧ F (xiSpectralPoint q0) = 1 := by
  set alpha := xiSpectralPoint q0 with halpha
  set q1 := xiZeroCopyLineConjEquiv q0 with hq1def
  have hbeta : xiSpectralPoint q1 = (starRingEnd ℂ) alpha := xiSpectralPoint_lineConj q0
  have hsupp0 : xiSpectralPointSupport q0.1 = alpha := (xiSpectralPoint_eq_support q0).symm
  have hsupp1 : xiSpectralPointSupport q1.1 = (starRingEnd ℂ) alpha :=
    (xiSpectralPoint_eq_support q1).symm.trans hbeta
  set c : ℂ := xiThetaDividedChain (xiSpectralPointSupport q0.1) (xiSupportMultiplicity q0.1)
    (xiSpectralPointSupport q0.1) with hc
  set d : ℂ := xiThetaDividedChain (xiSpectralPointSupport q1.1) (xiSupportMultiplicity q1.1)
    (xiSpectralPointSupport q1.1) with hd
  have hcne : c ≠ 0 := xiThetaDividedChain_nonzero_at_multiplicity q0.1
  have hdne : d ≠ 0 := xiThetaDividedChain_nonzero_at_multiplicity q1.1
  set F : ℂ → ℂ := fun z =>
    c⁻¹ * xiThetaDividedChain (xiSpectralPointSupport q0.1) (xiSupportMultiplicity q0.1) z -
      d⁻¹ * xiThetaDividedChain (xiSpectralPointSupport q1.1) (xiSupportMultiplicity q1.1) z
    with hFdef
  have hXialpha : XiC alpha = 0 := XiC_xiSpectralPoint_eq_zero q0
  have hXibeta : XiC ((starRingEnd ℂ) alpha) = 0 := by
    rw [← hbeta]
    exact XiC_xiSpectralPoint_eq_zero q1
  have hAvan : ∀ x : ℂ, XiC x = 0 → x ≠ alpha →
      xiThetaDividedChain (xiSpectralPointSupport q0.1) (xiSupportMultiplicity q0.1) x = 0 := by
    intro x hx hxne
    exact xiThetaDividedChain_terminal_eq_zero_of_ne q0.1 hx (by rw [hsupp0]; exact hxne)
  have hBvan : ∀ x : ℂ, XiC x = 0 → x ≠ (starRingEnd ℂ) alpha →
      xiThetaDividedChain (xiSpectralPointSupport q1.1) (xiSupportMultiplicity q1.1) x = 0 := by
    intro x hx hxne
    exact xiThetaDividedChain_terminal_eq_zero_of_ne q1.1 hx (by rw [hsupp1]; exact hxne)
  have hAval : xiThetaDividedChain (xiSpectralPointSupport q0.1) (xiSupportMultiplicity q0.1)
      alpha = c := by
    rw [hc, hsupp0]
  have hBval : xiThetaDividedChain (xiSpectralPointSupport q1.1) (xiSupportMultiplicity q1.1)
      ((starRingEnd ℂ) alpha) = d := by
    rw [hd, hsupp1]
  have hF1 : F alpha = 1 := by
    rw [hFdef]
    simp only
    rw [hAval, hBvan alpha hXialpha (Ne.symm hne), inv_mul_cancel₀ hcne, mul_zero, sub_zero]
  have hFm1 : F ((starRingEnd ℂ) alpha) = -1 := by
    rw [hFdef]
    simp only
    rw [hBval, hAvan _ hXibeta hne, inv_mul_cancel₀ hdne, mul_zero, zero_sub]
  have hFvan : ∀ x : ℂ, XiC x = 0 → x ≠ alpha → x ≠ (starRingEnd ℂ) alpha → F x = 0 := by
    intro x hx h1 h2
    rw [hFdef]
    simp only
    rw [hAvan x hx h1, hBvan x hx h2, mul_zero, mul_zero, sub_zero]
  have hdiffA : Differentiable ℂ
      (xiThetaDividedChain (xiSpectralPointSupport q0.1) (xiSupportMultiplicity q0.1)) :=
    fun z => (xiThetaDividedChain_analyticAt _ _ z).differentiableAt
  have hdiffB : Differentiable ℂ
      (xiThetaDividedChain (xiSpectralPointSupport q1.1) (xiSupportMultiplicity q1.1)) :=
    fun z => (xiThetaDividedChain_analyticAt _ _ z).differentiableAt
  have hdiff : Differentiable ℂ F := by
    rw [hFdef]
    exact (hdiffA.const_mul c⁻¹).sub (hdiffB.const_mul d⁻¹)
  have hOdd : XiWeilDivisorOdd F := by
    intro q
    have hxz : XiC (xiSpectralPoint q) = 0 := XiC_xiSpectralPoint_eq_zero q
    have hcz : XiC ((starRingEnd ℂ) (xiSpectralPoint q)) = 0 := by
      rw [← xiSpectralPoint_lineConj q]
      exact XiC_xiSpectralPoint_eq_zero _
    by_cases h1 : xiSpectralPoint q = alpha
    · rw [h1, hFm1, hF1]
    · by_cases h2 : xiSpectralPoint q = (starRingEnd ℂ) alpha
      · rw [h2, Complex.conj_conj, hF1, hFm1]
        norm_num
      · have h3 : (starRingEnd ℂ) (xiSpectralPoint q) ≠ alpha := by
          intro hcon
          apply h2
          have := congrArg (starRingEnd ℂ) hcon
          rwa [Complex.conj_conj] at this
        have h4 : (starRingEnd ℂ) (xiSpectralPoint q) ≠ (starRingEnd ℂ) alpha := by
          intro hcon
          apply h1
          have := congrArg (starRingEnd ℂ) hcon
          rwa [Complex.conj_conj, Complex.conj_conj] at this
        rw [hFvan _ hcz h3 h4, hFvan _ hxz h1 h2, neg_zero]
  have hsq : XiWeilSquareSummable F := by
    unfold XiWeilSquareSummable
    apply summable_of_hasFiniteSupport
    apply ((finite_xiSpectralPoint_fiber alpha).union
      (finite_xiSpectralPoint_fiber ((starRingEnd ℂ) alpha))).subset
    intro q hq
    simp only [Function.mem_support] at hq
    by_contra hnotin
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hnotin
    obtain ⟨hna, hnb⟩ := hnotin
    apply hq
    rw [hFvan _ (XiC_xiSpectralPoint_eq_zero q) hna hnb, norm_zero]
    norm_num
  exact ⟨F, hdiff, hOdd, hsq, hF1⟩

/-! ## The entire class detects everything -/

/-- **RH ⟺ entire divisor-odd tests vanish on the divisor.**  The negative sector of the Weil
form cannot be supported on rough tests only: if any divisor point is off the line, an entire
test already exhibits the odd sector. -/
theorem riemannHypothesis_iff_forall_entire_divisorOdd_eval_eq_zero :
    RiemannHypothesis ↔
      ∀ F : ℂ → ℂ, Differentiable ℂ F → XiWeilDivisorOdd F →
        ∀ q : XiZeroCopy, F (xiSpectralPoint q) = 0 := by
  constructor
  · intro hRH F _ hOdd q
    exact riemannHypothesis_iff_forall_divisorOdd_eval_eq_zero.mp hRH F hOdd q
  · intro hodd
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    by_cases hreal : (starRingEnd ℂ) (xiSpectralPoint q) = xiSpectralPoint q
    · exact ⟨(xiSpectralPoint q).re, (Complex.conj_eq_iff_re.mp hreal).symm⟩
    · exfalso
      obtain ⟨F, hdiff, hOdd, -, hF1⟩ := exists_entire_divisorOdd_unit_test q hreal
      exact one_ne_zero (hF1.symm.trans (hodd F hdiff hOdd q))

/-- **RH ⟺ Weil positivity on entire tests.**  Nonnegativity of the diagonal Weil form on the
entire square-summable class alone forces RH: the corpus's criterion on arbitrary
square-summable tests is equivalent to its restriction to analytic tests, so an analytic-class
positivity producer suffices. -/
theorem riemannHypothesis_iff_xiWeilPolarization_nonneg_entire :
    RiemannHypothesis ↔
      ∀ F : ℂ → ℂ, Differentiable ℂ F → XiWeilSquareSummable F →
        0 ≤ (xiWeilPolarization F F).re := by
  constructor
  · intro hRH F _ hsq
    exact riemannHypothesis_iff_xiWeilPolarization_nonneg.mp hRH F hsq
  · intro hpos
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    by_cases hreal : (starRingEnd ℂ) (xiSpectralPoint q) = xiSpectralPoint q
    · exact ⟨(xiSpectralPoint q).re, (Complex.conj_eq_iff_re.mp hreal).symm⟩
    · exfalso
      obtain ⟨F, hdiff, hOdd, hsq, hF1⟩ := exists_entire_divisorOdd_unit_test q hreal
      have hsumC : Summable (fun r : XiZeroCopy =>
          ((‖F (xiSpectralPoint r)‖ ^ 2 : ℝ) : ℂ)) := by
        simpa only [Function.comp_apply] using!
          hsq.map Complex.ofRealCLM Complex.ofRealCLM.continuous
      have hcongr : (∑' a : XiZeroCopy, (((‖F (xiSpectralPoint a)‖ ^ 2 : ℝ) : ℂ)).re) =
          ∑' a : XiZeroCopy, ‖F (xiSpectralPoint a)‖ ^ 2 :=
        tsum_congr fun a => Complex.ofReal_re _
      have hre : (xiWeilPolarization F F).re =
          -∑' r : XiZeroCopy, ‖F (xiSpectralPoint r)‖ ^ 2 := by
        rw [xiWeilPolarization_diagonal_of_divisorOdd hOdd, Complex.neg_re,
          Complex.re_tsum hsumC, hcongr]
      have hFsum : Summable (fun r : XiZeroCopy => ‖F (xiSpectralPoint r)‖ ^ 2) := hsq
      have hle : ‖F (xiSpectralPoint q)‖ ^ 2 ≤
          ∑' r : XiZeroCopy, ‖F (xiSpectralPoint r)‖ ^ 2 :=
        hFsum.le_tsum q fun r _ => sq_nonneg _
      rw [hF1] at hle
      have h0 := hpos F hdiff hsq
      rw [hre] at h0
      simp only [norm_one, one_pow] at hle
      linarith

/-- **RH ⟺ parity-twist invariance on entire tests.**  The fundamental symmetry of the Weil
form is invisible already when tested against entire functions exactly on RH. -/
theorem riemannHypothesis_iff_polarization_parityFlip_invariant_entire :
    RiemannHypothesis ↔
      ∀ F G : ℂ → ℂ, Differentiable ℂ F → Differentiable ℂ G →
        xiWeilPolarization F G = xiWeilPolarization F (xiWeilParityFlip G) := by
  constructor
  · intro hRH F G _ _
    exact riemannHypothesis_iff_polarization_parityFlip_invariant.mp hRH F G
  · intro hinv
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    by_cases hreal : (starRingEnd ℂ) (xiSpectralPoint q) = xiSpectralPoint q
    · exact ⟨(xiSpectralPoint q).re, (Complex.conj_eq_iff_re.mp hreal).symm⟩
    · exfalso
      obtain ⟨F, hdiff, hOdd, hsq, hF1⟩ := exists_entire_divisorOdd_unit_test q hreal
      have heq := hinv F F hdiff hdiff
      rw [xiWeilPolarization_diagonal_of_divisorOdd hOdd,
        xiWeilPolarization_parityFlip_diagonal F] at heq
      have hsumC : Summable (fun r : XiZeroCopy =>
          ((‖F (xiSpectralPoint r)‖ ^ 2 : ℝ) : ℂ)) := by
        simpa only [Function.comp_apply] using!
          hsq.map Complex.ofRealCLM Complex.ofRealCLM.continuous
      have hcongr : (∑' a : XiZeroCopy, (((‖F (xiSpectralPoint a)‖ ^ 2 : ℝ) : ℂ)).re) =
          ∑' a : XiZeroCopy, ‖F (xiSpectralPoint a)‖ ^ 2 :=
        tsum_congr fun a => Complex.ofReal_re _
      have hres := congrArg Complex.re heq
      rw [Complex.neg_re, Complex.re_tsum hsumC, hcongr] at hres
      have hS : (∑' r : XiZeroCopy, ‖F (xiSpectralPoint r)‖ ^ 2) = 0 := by
        linarith
      have hFsum : Summable (fun r : XiZeroCopy => ‖F (xiSpectralPoint r)‖ ^ 2) := hsq
      have hle : ‖F (xiSpectralPoint q)‖ ^ 2 ≤
          ∑' r : XiZeroCopy, ‖F (xiSpectralPoint r)‖ ^ 2 :=
        hFsum.le_tsum q fun r _ => sq_nonneg _
      rw [hF1, hS] at hle
      simp only [norm_one, one_pow] at hle
      linarith

end

end RHTower
