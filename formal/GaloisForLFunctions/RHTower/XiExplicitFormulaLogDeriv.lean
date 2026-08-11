import GaloisForLFunctions.RHTower.XiRelativeResolventTrace
import GaloisForLFunctions.RHTower.ArchEnvelope
import GaloisForLFunctions.RHTower.RHLadderTheory
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The logarithmic-derivative explicit formula on the right half-plane

The corpus's unconditional Hadamard partial fraction
(`logDeriv_XiC_eq_relativeResolventTrace`) is transported from centered spectral coordinates to
the classical `s`-plane and glued to the arithmetic side.  The results:

* `logDeriv_xi_eq_partialFraction` — wherever `xi s ≠ 0`, the logarithmic derivative of the
  completed zeta is the absolutely convergent multiplicity-exact sum
  `Σ'_ρ (1/(ρ − 1/2) + 1/(s − ρ))` over the divisor, with no linear term.
* `xi_explicitFormula_logDeriv` — for `Re s > 1` the zero side equals the arithmetic side:

  `Σ'_ρ (1/(ρ − 1/2) + 1/(s − ρ)) = 1/s + 1/(s−1) + logDeriv Γℝ s − Σ_n Λ(n) n^{-s}`.

This is the first unconditional zero-sum = prime-sum identity in the corpus: the
logarithmic-derivative fragment of the Guinand–Weil explicit formula, assembled from the
Hadamard factorization (zero side), the factor split of `xi` (polar and archimedean terms), and
mathlib's Dirichlet-series evaluation of `−ζ'/ζ` (prime side).
-/

open Complex

namespace RHTower

noncomputable section

/-- The completed zeta in classical coordinates is the centered function at the rotated
argument. -/
theorem xi_eq_XiC_comp (s : ℂ) : xi s = XiC ((s - 1 / 2) * (-Complex.I)) := by
  rw [XiC]
  congr 1
  have hI : (-Complex.I) * Complex.I = 1 := by
    rw [neg_mul, Complex.I_mul_I]
    ring
  linear_combination (1 / 2 - s) * hI

/-- Rotation by `-i` transports a centered resolvent difference to the classical one; pure
algebra, no nonvanishing hypotheses. -/
theorem resolvent_coordinate_transport (A S : ℂ) :
    ((A * -Complex.I)⁻¹ - (A * -Complex.I - S * -Complex.I)⁻¹) * -Complex.I =
      A⁻¹ - (A - S)⁻¹ := by
  have hI : (-Complex.I) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  rw [← sub_mul, mul_inv, mul_inv, ← sub_mul, mul_assoc, inv_mul_cancel₀ hI, mul_one]

/-- **The classical partial fraction of the completed zeta.**  Wherever `xi s ≠ 0`, its
logarithmic derivative is the multiplicity-exact absolutely convergent sum of
`1/(ρ − 1/2) + 1/(s − ρ)` over the divisor — with no linear term, evenness having removed the
exponential factor inside the Hadamard constancy theorem. -/
theorem logDeriv_xi_eq_partialFraction {s : ℂ} (hs : xi s ≠ 0) :
    logDeriv xi s = ∑' q : XiZeroCopy,
      (((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹) := by
  set h : ℂ → ℂ := fun w => (w - 1 / 2) * -Complex.I with hh
  have hcomp : xi = XiC ∘ h := by
    funext w
    exact xi_eq_XiC_comp w
  have hXiCne : XiC (h s) ≠ 0 := by
    rw [← xi_eq_XiC_comp]
    exact hs
  have hd1 : DifferentiableAt ℂ XiC (h s) :=
    (XiC_analytic (h s) (Set.mem_univ _)).differentiableAt
  have hderivh : HasDerivAt h (-Complex.I) s := by
    have h1 : HasDerivAt (fun w : ℂ => (w - 1 / 2) * -Complex.I)
        (1 * -Complex.I) s :=
      ((hasDerivAt_id s).sub_const _).mul_const _
    rw [one_mul] at h1
    exact h1
  have hstep : logDeriv xi s = logDeriv (XiC ∘ h) s := by rw [hcomp]
  rw [hstep, logDeriv_comp hd1 hderivh.differentiableAt, hderivh.deriv,
    logDeriv_XiC_eq_relativeResolventTrace hXiCne, xiRelativeResolventTrace,
    ← tsum_mul_right]
  apply tsum_congr
  intro q
  rw [xiRelativeResolventTerm]
  have hspec : xiSpectralPoint q = (((q.1 : ℂ)) - 1 / 2) * -Complex.I := by
    rw [xiSpectralPoint_eq_support, xiSpectralPointSupport]
  rw [hspec]
  have hth := resolvent_coordinate_transport (((q.1 : ℂ)) - 1 / 2) (s - 1 / 2)
  calc ((((q.1 : ℂ) - 1 / 2) * -Complex.I)⁻¹ -
        (((q.1 : ℂ) - 1 / 2) * -Complex.I - h s)⁻¹) * -Complex.I =
      ((((q.1 : ℂ) - 1 / 2) * -Complex.I)⁻¹ -
        (((q.1 : ℂ) - 1 / 2) * -Complex.I - (s - 1 / 2) * -Complex.I)⁻¹) * -Complex.I := by
        rw [hh]
    _ = (((q.1 : ℂ)) - 1 / 2)⁻¹ - (((q.1 : ℂ)) - 1 / 2 - (s - 1 / 2))⁻¹ := hth
    _ = (((q.1 : ℂ)) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹ := by
        rw [show ((q.1 : ℂ)) - 1 / 2 - (s - 1 / 2) = -(s - (q.1 : ℂ)) by ring, inv_neg]
        ring

/-- **The factor split of the completed zeta on the right half-plane**: polar, archimedean, and
zeta logarithmic derivatives separate additively. -/
theorem logDeriv_xi_split {s : ℂ} (hs : 1 < s.re) :
    logDeriv xi s = s⁻¹ + (s - 1)⁻¹ + logDeriv Complex.Gammaℝ s +
      logDeriv riemannZeta s := by
  have h0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    linarith
  have h1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    linarith
  have hre : (0 : ℝ) < s.re := by linarith
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre
  have hpoly_ne : s * (s - 1) / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) two_ne_zero
  have hopen : IsOpen {w : ℂ | w ≠ 0 ∧ w ≠ 1 ∧ 0 < w.re} := by
    apply IsOpen.inter isOpen_ne
    exact IsOpen.inter isOpen_ne (isOpen_lt continuous_const Complex.continuous_re)
  have hev : xi =ᶠ[nhds s]
      fun w => w * (w - 1) / 2 * (Complex.Gammaℝ w * riemannZeta w) := by
    filter_upwards [hopen.mem_nhds ⟨h0, h1, hre⟩] with w hw
    obtain ⟨hw0, hw1, hwre⟩ := hw
    have hwΓ : Complex.Gammaℝ w ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hwre
    rw [xi_eq_half_mul hw0 hw1]
    congr 1
    rw [riemannZeta_def_of_ne_zero hw0, mul_div_cancel₀ _ hwΓ]
  have hlogcongr : logDeriv xi s =
      logDeriv (fun w => w * (w - 1) / 2 * (Complex.Gammaℝ w * riemannZeta w)) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hpolyd : HasDerivAt (fun w : ℂ => w * (w - 1) / 2) ((2 * s - 1) / 2) s := by
    have hid : HasDerivAt (fun w : ℂ => w) 1 s := hasDerivAt_id s
    have hbase : HasDerivAt (fun w : ℂ => w * (w - 1)) (1 * (s - 1) + s * 1) s :=
      hid.mul (hid.sub_const (1 : ℂ))
    have hval : (1 : ℂ) * (s - 1) + s * 1 = 2 * s - 1 := by ring
    rw [hval] at hbase
    exact hbase.div_const 2
  have hΓd : DifferentiableAt ℂ Complex.Gammaℝ s :=
    (hasDerivAt_Gammaℝ_of_re_pos hre).differentiableAt
  have hζd : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta h1
  rw [hlogcongr,
    logDeriv_mul (f := fun w : ℂ => w * (w - 1) / 2)
      (g := fun w : ℂ => Complex.Gammaℝ w * riemannZeta w) s hpoly_ne
      (mul_ne_zero hΓ hζ) hpolyd.differentiableAt (hΓd.mul hζd),
    logDeriv_mul (f := Complex.Gammaℝ) (g := riemannZeta) s hΓ hζ hΓd hζd]
  have hpolylog : logDeriv (fun w : ℂ => w * (w - 1) / 2) s = s⁻¹ + (s - 1)⁻¹ := by
    rw [logDeriv_apply, hpolyd.deriv]
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr h1
    field_simp
    ring
  rw [hpolylog]
  ring

/-- **The logarithmic-derivative explicit formula.**  On `Re s > 1` the multiplicity-exact zero
sum equals the arithmetic side: polar terms, archimedean logarithmic derivative, and minus the
von Mangoldt Dirichlet series.  Unconditional — the corpus's first zero-sum = prime-sum
identity. -/
theorem xi_explicitFormula_logDeriv {s : ℂ} (hs : 1 < s.re) :
    ∑' q : XiZeroCopy, (((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹) =
      s⁻¹ + (s - 1)⁻¹ + logDeriv Complex.Gammaℝ s -
        LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s := by
  have hxine : xi s ≠ 0 := xi_ne_zero_of_one_le_re hs.le
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have hlogζ : logDeriv riemannZeta s =
      -LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s := by
    rw [logDeriv_apply, hL]
    ring
  rw [← logDeriv_xi_eq_partialFraction hxine, logDeriv_xi_split hs, hlogζ]
  ring

end

end RHTower
