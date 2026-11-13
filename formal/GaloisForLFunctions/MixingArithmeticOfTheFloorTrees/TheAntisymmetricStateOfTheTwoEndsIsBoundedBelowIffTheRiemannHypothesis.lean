import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheOddSectorOfAWindowCarriesNoBoundStateIffTheRiemannHypothesis
import GaloisForLFunctions.SurfaceOfSpecZ.OneSidedHasseWeilAtTheIntegerDegrees
import GaloisForLFunctions.SquareRootThreshold.DifferenceTwoBumpTestsDecideTheCriticalLine
import GaloisForLFunctions.SquareRootThreshold.OneParameterLagFamilyDeterminesTheConfiguration
import GaloisForLFunctions.RHTower.XiGaussianHeatWindowNyquistExclusion
import GaloisForLFunctions.SquareRootThreshold.LagRateBoundsTheDeBruijnNewmanHeatTime
import GaloisForLFunctions.SquareRootThreshold.OneParameterLagFamilyMeasuresTheAbscissa
import GaloisForLFunctions.SquareRootThreshold.NegativityRateEqualsMaximalDepth

/-!
# The antisymmetric state of the two ends is bounded below iff the Riemann hypothesis

At infinite block size the binding energy of a window lives in its even sector, and RH is the
statement that the odd sector carries no bound state (`riemannHypothesis_iff_forall_odd_neutralForm_nonneg`).
This module shows that **a uniform bound below suffices**: if the odd sector can bind only to a
bounded depth, it does not bind at all.

The witness is the antisymmetric state of the two ends of a window. Take the **pole-free profile**
`f₀ = U − κ(U(· + 1) + U(· − 1))`, `U = U_1^{⋆4}` the cubic spline and `κ = 1/(2 cosh ½)`. It is
even, its two charges vanish (`charge_poleFreeProfile`), and its transform
`(1 − 2κ cos z) Û(z)` vanishes at no spectral point of a zero off the critical line
(`paperFT_poleFreeProfile_ne_zero`): `|cos z| ≤ cosh(Im z) < cosh ½` there. Put a copy at each
end of the window `[−v/2 − 5, v/2 + 5]` with opposite signs:

  `o_v = f₀(· + v/2) − f₀(· − v/2)`.

It is odd and pole-free, so its neutral form is Weil's form of the zeros
(`neutralForm_twoEndOdd`): `N(o_v) = 2 Re S(0) − 2 Re S(v)`, with `S` the lag structure of `f₀`
(SRT). A bound `N(o_v) ≥ −C` for all `v ≥ 0` is therefore an upper bound on `2 Re S`, and
Landau's argument (SRT, `evenCoeff_eq_zero_of_two_re_lagStructure_le_exp`) removes every
exponent right of the line; since `f₀` sees every zero off the line, there is none
(`riemannHypothesis_iff_twoEndOdd_bddBelow`). The mass of `o_v` is at most `4 ∫ f₀²`, so the
same holds for the odd sector in units of mass (`riemannHypothesis_iff_odd_sector_bddBelow`):

  **RH iff the odd sector of every window is bounded below by a fixed constant times the mass.**

So the sign question of the second bound state reduces to a uniform bound on its depth, and the
antisymmetric state of the two ends of one profile already decides it. The same argument with
Landau's exponent `θ` is a rate law (`zetaZeroWidth_le_iff_twoEndOdd_rate`): the zero width is at
most `θ < ½` iff the depth of the antisymmetric state grows at most like `e^{θ v}` in the length
`v` of the window.

The symmetric state `e_v = f₀(· + v/2) + f₀(· − v/2)` has `N(e_v) = 2 Re S(0) + 2 Re S(v)`
(`neutralForm_twoEndEven`), and Landau's argument from below (`riemannHypothesis_of_le_lagStructure`)
makes a lower bound on `S` force RH as well: without RH both states sink without bound.
-/

open MeasureTheory Complex
open scoped ComplexConjugate
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx)
open GaloisForLFunctions.SquareRootThreshold (lagStructure twoBump bumpTest lagPoint evenCoeff
  boxSpline)
open Zeta23

noncomputable section

namespace GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

/-! ### The pole-free profile -/

/-- The cubic spline `U_1^{⋆4}`, an even bump on `[−4, 4]`. -/
abbrev spline : ℝ → ℝ := _root_.RHTower.WeilDeletion.upow 1 3

theorem spline_neg (x : ℝ) : spline (-x) = spline x := SquareRootThreshold.upow_neg 1 3 x

theorem spline_eq_zero {x : ℝ} (hx : 4 < |x|) : spline x = 0 := by
  by_contra h
  have h' := SquareRootThreshold.boxSpline_support one_pos 3 x
    (by simpa [SquareRootThreshold.boxSpline] using h)
  norm_num at h'
  linarith

theorem contDiff_spline : ContDiff ℝ 2 spline := by
  exact_mod_cast BiScaleUncertainty.ChebyshevGauge.contDiff_upow one_pos 2

/-- The weight `κ = 1/(2 cosh ½)` that removes both charges. -/
def chargeWeight : ℝ := 1 / (2 * Real.cosh (1 / 2))

theorem chargeWeight_pos : 0 < chargeWeight := by
  unfold chargeWeight
  have := Real.cosh_pos (1 / 2)
  positivity

theorem chargeWeight_mul : chargeWeight * (Real.exp (1 / 2) + Real.exp (-(1 / 2))) = 1 := by
  have hc := Real.cosh_pos (1 / 2)
  unfold chargeWeight
  rw [Real.cosh_eq] at hc ⊢
  field_simp

/-- **The pole-free profile** `f₀ = U − κ(U(· + 1) + U(· − 1))`. -/
def poleFreeProfile (u : ℝ) : ℝ := spline u - chargeWeight * (spline (u + 1) + spline (u - 1))

theorem poleFreeProfile_neg (u : ℝ) : poleFreeProfile (-u) = poleFreeProfile u := by
  unfold poleFreeProfile
  rw [spline_neg, show -u + 1 = -(u - 1) by ring, show -u - 1 = -(u + 1) by ring, spline_neg,
    spline_neg]
  ring

theorem contDiff_poleFreeProfile : ContDiff ℝ 2 poleFreeProfile :=
  contDiff_spline.sub (contDiff_const.mul
    ((contDiff_spline.comp (contDiff_id.add contDiff_const)).add
      (contDiff_spline.comp (contDiff_id.sub contDiff_const))))

theorem poleFreeProfile_eq_zero {u : ℝ} (hu : 5 < |u|) : poleFreeProfile u = 0 := by
  have h1 : 4 < |u + 1| := by
    have h := abs_sub_abs_le_abs_sub u (-1)
    rw [sub_neg_eq_add, abs_neg, abs_one] at h
    linarith
  have h2 : 4 < |u - 1| := by
    have h := abs_sub_abs_le_abs_sub u 1
    rw [abs_one] at h
    linarith
  have h0 : 4 < |u| := by linarith
  unfold poleFreeProfile
  rw [spline_eq_zero h0, spline_eq_zero h1, spline_eq_zero h2]
  ring

theorem cx_poleFreeProfile_support : ∀ u, cx poleFreeProfile u ≠ 0 → |u| ≤ 5 := fun u hu => by
  by_contra h
  exact hu (by simp [cx, poleFreeProfile_eq_zero (not_le.mp h)])

theorem hasCompactSupport_cx_poleFreeProfile : HasCompactSupport (cx poleFreeProfile) :=
  hasCompactSupport_of_support_subset_abs cx_poleFreeProfile_support

theorem contDiff_cx_poleFreeProfile : ContDiff ℝ 2 (cx poleFreeProfile) :=
  Complex.ofRealCLM.contDiff.comp contDiff_poleFreeProfile

theorem lagPoint_three_zero : lagPoint 3 1 0 = -1 := by
  simp only [lagPoint, Fin.val_zero, Nat.cast_zero, Nat.cast_ofNat]; norm_num

theorem lagPoint_three_one : lagPoint 3 1 1 = 0 := by
  simp only [lagPoint, Fin.val_one, Nat.cast_one, Nat.cast_ofNat]; norm_num

theorem lagPoint_three_two : lagPoint 3 1 2 = 1 := by
  simp only [lagPoint, Fin.val_two, Nat.cast_ofNat]; norm_num

/-- The pole-free profile as three copies of the spline at the lags `−1, 0, 1`. -/
theorem cx_poleFreeProfile_eq :
    cx poleFreeProfile = bumpTest (boxSpline 1 3) 1
      ![-(chargeWeight : ℂ), 1, -(chargeWeight : ℂ)] := by
  have h0 : lagPoint 3 1 0 = -1 := lagPoint_three_zero
  have h1 : lagPoint 3 1 1 = 0 := lagPoint_three_one
  have h2 : lagPoint 3 1 2 = 1 := lagPoint_three_two
  funext t
  simp only [bumpTest, Fin.sum_univ_three, h0, h1, h2, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, cx, poleFreeProfile, boxSpline,
    sub_neg_eq_add, sub_zero]
  push_cast
  ring

/-- **The transform of the pole-free profile** is `(1 − κ(e^{−iz} + e^{iz})) Û(z)`. -/
theorem paperFT_poleFreeProfile (z : ℂ) :
    paperFT (cx poleFreeProfile) z =
      (1 - chargeWeight * (cexp (-(I * z)) + cexp (I * z))) * paperFT (boxSpline 1 3) z := by
  have h0 : lagPoint 3 1 0 = -1 := lagPoint_three_zero
  have h1 : lagPoint 3 1 1 = 0 := lagPoint_three_one
  have h2 : lagPoint 3 1 2 = 1 := lagPoint_three_two
  rw [cx_poleFreeProfile_eq, SquareRootThreshold.paperFT_bumpTest
    (SquareRootThreshold.contDiff_boxSpline one_pos 2).continuous
    (hasCompactSupport_of_support_subset_abs
      (SquareRootThreshold.boxSpline_support one_pos 3))]
  congr 1
  rw [Fin.sum_univ_three, h0, h1, h2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  push_cast
  simp only [mul_zero, Complex.exp_zero, mul_neg_one, mul_one]
  ring

/-- **Both charges of the pole-free profile vanish**: its transform is zero at `i/2`. -/
theorem paperFT_poleFreeProfile_I_div_two : paperFT (cx poleFreeProfile) (I / 2) = 0 := by
  rw [paperFT_poleFreeProfile]
  have e1 : -(I * (I / 2)) = ((1 / 2 : ℝ) : ℂ) := by
    rw [← mul_div_assoc, I_mul_I]; push_cast; ring
  have e2 : I * (I / 2) = ((-(1 / 2) : ℝ) : ℂ) := by
    rw [← mul_div_assoc, I_mul_I]; push_cast; ring
  rw [e1, e2, ← Complex.ofReal_exp, ← Complex.ofReal_exp,
    show (1 : ℂ) - (chargeWeight : ℂ) * ((Real.exp (1 / 2) : ℂ) + (Real.exp (-(1 / 2)) : ℂ)) =
      ((1 - chargeWeight * (Real.exp (1 / 2) + Real.exp (-(1 / 2))) : ℝ) : ℂ) by push_cast; ring,
    chargeWeight_mul, sub_self, Complex.ofReal_zero, zero_mul]

theorem charge_poleFreeProfile : ∫ u, poleFreeProfile u * Real.exp (-u / 2) = 0 := by
  have h := paperFT_poleFreeProfile_I_div_two
  have e : paperFT (cx poleFreeProfile) (I / 2) =
      ((∫ u, poleFreeProfile u * Real.exp (-u / 2) : ℝ) : ℂ) :=
    _root_.RHTower.WeilLevyPole.paperFT_ofReal_I_div_two poleFreeProfile
  rw [e] at h
  exact_mod_cast h

/-- **The pole-free profile sees every zero off the critical line**: `1 − 2κ cos z ≠ 0` because
`|cos z| ≤ cosh(Im z) < cosh ½`, and the spline transform has no non-real zero. -/
theorem paperFT_poleFreeProfile_ne_zero {z : ℂ} (hz0 : z.im ≠ 0) (hz : |z.im| < 1 / 2) :
    paperFT (cx poleFreeProfile) z ≠ 0 := by
  rw [paperFT_poleFreeProfile]
  refine mul_ne_zero ?_ (SquareRootThreshold.paperFT_boxSpline_ne_zero one_pos 3 hz0)
  intro h
  have h1 : (chargeWeight : ℂ) * (cexp (-(I * z)) + cexp (I * z)) = 1 := by
    linear_combination -h
  have hn := congrArg norm h1
  rw [norm_mul, norm_one, Complex.norm_of_nonneg chargeWeight_pos.le] at hn
  have hle : ‖cexp (-(I * z)) + cexp (I * z)‖ ≤ Real.exp z.im + Real.exp (-z.im) := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [Complex.norm_exp, Complex.norm_exp]
    congr 1 <;> congr 1 <;> simp [Complex.mul_re]
  have hcosh : Real.exp z.im + Real.exp (-z.im) < Real.exp (1 / 2) + Real.exp (-(1 / 2)) := by
    have := Real.cosh_lt_cosh.mpr
      (show |z.im| < |(1 / 2 : ℝ)| by rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)])
    rw [Real.cosh_eq, Real.cosh_eq] at this
    linarith
  have hlt := mul_lt_mul_of_pos_left (hle.trans_lt hcosh) chargeWeight_pos
  rw [chargeWeight_mul] at hlt
  linarith

theorem evenCoeff_poleFreeProfile_sees {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier)
    (hre : 1 / 2 < ρ.re) : evenCoeff zetaZeroConfig (cx poleFreeProfile) (ρ - 1 / 2) ≠ 0 := by
  obtain ⟨_, h0, h1⟩ := id hρ
  refine SquareRootThreshold.evenCoeff_sub_half_ne_zero_of_conj_symm zetaZeroConfig
    contDiff_cx_poleFreeProfile.continuous hasCompactSupport_cx_poleFreeProfile
    (_root_.RHTower.conj_paperFT_ofReal_conj_of_even poleFreeProfile_neg)
    (_root_.RHTower.paperFT_ofReal_neg_of_even poleFreeProfile_neg) hρ ?_
  apply paperFT_poleFreeProfile_ne_zero
  · rw [SquareRootThreshold.im_gammaOf]; linarith
  · rw [SquareRootThreshold.im_gammaOf, abs_lt]; constructor <;> linarith

theorem evenCoeff_poleFreeProfile_real {x : ℂ}
    (hx : evenCoeff zetaZeroConfig (cx poleFreeProfile) x ≠ 0) : x.im ≠ 0 := by
  intro him
  rcases SquareRootThreshold.mem_of_evenCoeff_ne_zero hx with h | h
  · exact SurfaceOfSpecZ.not_mem_carrier_of_im_eq_zero h (by simp [him])
  · exact SurfaceOfSpecZ.not_mem_carrier_of_im_eq_zero h (by simp [him])

/-! ### The antisymmetric state of the two ends -/

/-- **The antisymmetric state of the two ends**: copies of `f₀` at `∓v/2` with opposite signs. -/
def twoEndOdd (v u : ℝ) : ℝ := poleFreeProfile (u + v / 2) - poleFreeProfile (u - v / 2)

theorem twoEndOdd_neg (v u : ℝ) : twoEndOdd v (-u) = -twoEndOdd v u := by
  unfold twoEndOdd
  rw [show -u + v / 2 = -(u - v / 2) by ring, show -u - v / 2 = -(u + v / 2) by ring,
    poleFreeProfile_neg, poleFreeProfile_neg]
  ring

theorem contDiff_twoEndOdd (v : ℝ) : ContDiff ℝ 2 (twoEndOdd v) :=
  (contDiff_poleFreeProfile.comp (contDiff_id.add contDiff_const)).sub
    (contDiff_poleFreeProfile.comp (contDiff_id.sub contDiff_const))

theorem twoEndOdd_eq_zero (v : ℝ) {u : ℝ} (hu : 5 + |v| / 2 < |u|) : twoEndOdd v u = 0 := by
  have h1 : 5 < |u + v / 2| := by
    have h := abs_sub_abs_le_abs_sub u (-(v / 2))
    rw [sub_neg_eq_add, abs_neg, abs_div, abs_two] at h
    linarith
  have h2 : 5 < |u - v / 2| := by
    have h := abs_sub_abs_le_abs_sub u (v / 2)
    rw [abs_div, abs_two] at h
    linarith
  unfold twoEndOdd
  rw [poleFreeProfile_eq_zero h1, poleFreeProfile_eq_zero h2, sub_zero]

theorem hasCompactSupport_twoEndOdd (v : ℝ) : HasCompactSupport (twoEndOdd v) :=
  HasCompactSupport.intro (isCompact_Icc (a := -(5 + |v| / 2)) (b := 5 + |v| / 2)) fun u hu =>
    twoEndOdd_eq_zero v (by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with h | h
      · exact lt_of_lt_of_le (by linarith) (neg_le_abs u)
      · exact lt_of_lt_of_le h (le_abs_self u))

theorem cx_twoEndOdd (v : ℝ) : cx (twoEndOdd v) = twoBump (cx poleFreeProfile) v (-1) := by
  have l0 : lagPoint 2 v 0 = -(v / 2) := by
    simp only [lagPoint, Fin.val_zero, Nat.cast_zero, Nat.cast_ofNat]; ring
  have l1 : lagPoint 2 v 1 = v / 2 := by
    simp only [lagPoint, Fin.val_one, Nat.cast_one, Nat.cast_ofNat]; ring
  funext t
  simp only [twoBump, bumpTest, Fin.sum_univ_two, l0, l1, Matrix.cons_val_zero,
    Matrix.cons_val_one, cx, twoEndOdd, sub_neg_eq_add]
  push_cast
  ring

theorem charge_twoEndOdd (v : ℝ) : ∫ u, twoEndOdd v u * Real.exp (-u / 2) = 0 := by
  have h : paperFT (cx (twoEndOdd v)) (I / 2) = 0 := by
    rw [cx_twoEndOdd, SquareRootThreshold.paperFT_twoBump contDiff_cx_poleFreeProfile.continuous
      hasCompactSupport_cx_poleFreeProfile, paperFT_poleFreeProfile_I_div_two, mul_zero]
  have e : paperFT (cx (twoEndOdd v)) (I / 2) =
      ((∫ u, twoEndOdd v u * Real.exp (-u / 2) : ℝ) : ℂ) :=
    _root_.RHTower.WeilLevyPole.paperFT_ofReal_I_div_two (twoEndOdd v)
  rw [e] at h
  exact_mod_cast h

/-- **The neutral form of the antisymmetric state is the lag structure of the profile**:
`N(o_v) = 2 Re S(0) − 2 Re S(v)`. -/
theorem neutralForm_twoEndOdd (v : ℝ) {Q : ℕ}
    (hQ : ∀ n : ℕ, Q < n → packetAutocorr (twoEndOdd v) (Real.log n) = 0) :
    neutralForm Q (twoEndOdd v) =
      2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) 0).re -
        2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) v).re := by
  rw [neutralForm_eq_re_sub (contDiff_twoEndOdd v) (hasCompactSupport_twoEndOdd v) hQ,
    Complex.sub_re, poleConfig_W_ofReal, Complex.ofReal_re, charge_twoEndOdd v, zero_mul,
    mul_zero, sub_zero]
  have h := SquareRootThreshold.re_W_lag_eq zetaZeroConfig
    SquareRootThreshold.temperedConfig_zetaZeroConfig contDiff_cx_poleFreeProfile
    cx_poleFreeProfile_support v
  rw [← cx_twoEndOdd] at h
  exact h

/-- Every antisymmetric state has a contact range covering its support. -/
theorem exists_range_twoEndOdd (v : ℝ) :
    ∃ Q : ℕ, ∀ n : ℕ, Q < n → packetAutocorr (twoEndOdd v) (Real.log n) = 0 := by
  obtain ⟨Q, hQ⟩ := exists_nat_gt (Real.exp (10 + |v| + 1))
  refine ⟨Q, fun n hn => ?_⟩
  have hn' : Real.exp (10 + |v| + 1) < n := hQ.trans (by exact_mod_cast hn)
  have hlog : 10 + |v| + 1 < Real.log n :=
    (Real.lt_log_iff_exp_lt (by exact_mod_cast (show 0 < n by omega))).mpr hn'
  refine packetAutocorr_eq_zero_of_vanishing_off (a := -(5 + |v| / 2)) (b := 5 + |v| / 2)
    (fun u hu => twoEndOdd_eq_zero v ?_) (by linarith)
  rcases hu with h | h
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs u)
  · exact lt_of_lt_of_le h (le_abs_self u)

/-! ### Landau from either side -/

/-- **An upper bound on the lag structure of the pole-free profile forces RH**: Landau's argument
removes every exponent right of the line, and the profile sees every zero off the line. -/
theorem riemannHypothesis_of_lagStructure_le {M : ℝ}
    (hM : ∀ u : ℝ, 0 ≤ u → 2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) u).re ≤ M) :
    RiemannHypothesis := by
  apply SurfaceOfSpecZ.riemannHypothesis_of_forall_re_le
  intro ρ hρ
  by_contra hre
  push Not at hre
  refine evenCoeff_poleFreeProfile_sees hρ hre
    (SquareRootThreshold.evenCoeff_eq_zero_of_two_re_lagStructure_le_exp zetaZeroConfig
      SquareRootThreshold.temperedConfig_zetaZeroConfig contDiff_cx_poleFreeProfile
      cx_poleFreeProfile_support le_rfl (by norm_num)
      (fun x hx him => absurd him (evenCoeff_poleFreeProfile_real hx)) (M := M)
      (fun u hu => by rw [zero_mul, Real.exp_zero, mul_one]; exact hM u hu) ?_)
  rw [show (ρ - 1 / 2).re = ρ.re - 1 / 2 by simp]
  linarith

/-- **A lower bound on the lag structure of the pole-free profile forces RH.** -/
theorem riemannHypothesis_of_le_lagStructure {M : ℝ}
    (hM : ∀ u : ℝ, 0 ≤ u → -M ≤ 2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) u).re) :
    RiemannHypothesis := by
  apply SurfaceOfSpecZ.riemannHypothesis_of_forall_re_le
  intro ρ hρ
  by_contra hre
  push Not at hre
  refine evenCoeff_poleFreeProfile_sees hρ hre
    (SurfaceOfSpecZ.evenCoeff_eq_zero_of_two_re_lagStructure_ge zetaZeroConfig
      SquareRootThreshold.temperedConfig_zetaZeroConfig contDiff_cx_poleFreeProfile
      cx_poleFreeProfile_support le_rfl (by norm_num)
      (fun x hx him => absurd him (evenCoeff_poleFreeProfile_real hx)) (M := M)
      (fun u hu => by rw [zero_mul, Real.exp_zero, mul_one]; exact hM u hu) ?_)
  rw [show (ρ - 1 / 2).re = ρ.re - 1 / 2 by simp]
  linarith

/-! ### The symmetric state of the two ends -/

/-- **The symmetric state of the two ends**: copies of `f₀` at `∓v/2` with equal signs. -/
def twoEndEven (v u : ℝ) : ℝ := poleFreeProfile (u + v / 2) + poleFreeProfile (u - v / 2)

theorem twoEndEven_neg (v u : ℝ) : twoEndEven v (-u) = twoEndEven v u := by
  unfold twoEndEven
  rw [show -u + v / 2 = -(u - v / 2) by ring, show -u - v / 2 = -(u + v / 2) by ring,
    poleFreeProfile_neg, poleFreeProfile_neg]
  ring

theorem contDiff_twoEndEven (v : ℝ) : ContDiff ℝ 2 (twoEndEven v) :=
  (contDiff_poleFreeProfile.comp (contDiff_id.add contDiff_const)).add
    (contDiff_poleFreeProfile.comp (contDiff_id.sub contDiff_const))

theorem twoEndEven_eq_zero (v : ℝ) {u : ℝ} (hu : 5 + |v| / 2 < |u|) : twoEndEven v u = 0 := by
  have h1 : 5 < |u + v / 2| := by
    have h := abs_sub_abs_le_abs_sub u (-(v / 2))
    rw [sub_neg_eq_add, abs_neg, abs_div, abs_two] at h
    linarith
  have h2 : 5 < |u - v / 2| := by
    have h := abs_sub_abs_le_abs_sub u (v / 2)
    rw [abs_div, abs_two] at h
    linarith
  unfold twoEndEven
  rw [poleFreeProfile_eq_zero h1, poleFreeProfile_eq_zero h2, add_zero]

theorem hasCompactSupport_twoEndEven (v : ℝ) : HasCompactSupport (twoEndEven v) :=
  HasCompactSupport.intro (isCompact_Icc (a := -(5 + |v| / 2)) (b := 5 + |v| / 2)) fun u hu =>
    twoEndEven_eq_zero v (by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with h | h
      · exact lt_of_lt_of_le (by linarith) (neg_le_abs u)
      · exact lt_of_lt_of_le h (le_abs_self u))

theorem cx_twoEndEven (v : ℝ) : cx (twoEndEven v) = twoBump (cx poleFreeProfile) v 1 := by
  have l0 : lagPoint 2 v 0 = -(v / 2) := by
    simp only [lagPoint, Fin.val_zero, Nat.cast_zero, Nat.cast_ofNat]; ring
  have l1 : lagPoint 2 v 1 = v / 2 := by
    simp only [lagPoint, Fin.val_one, Nat.cast_one, Nat.cast_ofNat]; ring
  funext t
  simp only [twoBump, bumpTest, Fin.sum_univ_two, l0, l1, Matrix.cons_val_zero,
    Matrix.cons_val_one, cx, twoEndEven, sub_neg_eq_add]
  push_cast
  ring

theorem charge_twoEndEven (v : ℝ) : ∫ u, twoEndEven v u * Real.exp (-u / 2) = 0 := by
  have h : paperFT (cx (twoEndEven v)) (I / 2) = 0 := by
    rw [cx_twoEndEven, SquareRootThreshold.paperFT_twoBump contDiff_cx_poleFreeProfile.continuous
      hasCompactSupport_cx_poleFreeProfile, paperFT_poleFreeProfile_I_div_two, mul_zero]
  have e : paperFT (cx (twoEndEven v)) (I / 2) =
      ((∫ u, twoEndEven v u * Real.exp (-u / 2) : ℝ) : ℂ) :=
    _root_.RHTower.WeilLevyPole.paperFT_ofReal_I_div_two (twoEndEven v)
  rw [e] at h
  exact_mod_cast h

/-- **The neutral form of the symmetric state**: `N(e_v) = 2 Re S(0) + 2 Re S(v)`. -/
theorem neutralForm_twoEndEven (v : ℝ) {Q : ℕ}
    (hQ : ∀ n : ℕ, Q < n → packetAutocorr (twoEndEven v) (Real.log n) = 0) :
    neutralForm Q (twoEndEven v) =
      2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) 0).re +
        2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) v).re := by
  rw [neutralForm_eq_re_sub (contDiff_twoEndEven v) (hasCompactSupport_twoEndEven v) hQ,
    Complex.sub_re, poleConfig_W_ofReal, Complex.ofReal_re, charge_twoEndEven v, zero_mul,
    mul_zero, sub_zero]
  have h := SquareRootThreshold.re_W_unit_twoBump zetaZeroConfig
    SquareRootThreshold.temperedConfig_zetaZeroConfig contDiff_cx_poleFreeProfile
    cx_poleFreeProfile_support v (τ := 1) (by simp)
  rw [SquareRootThreshold.conj_lagStructure_neg zetaZeroConfig
    SquareRootThreshold.temperedConfig_zetaZeroConfig contDiff_cx_poleFreeProfile
    cx_poleFreeProfile_support v, one_mul, Complex.add_re, ← cx_twoEndEven] at h
  refine h.trans ?_
  ring

/-! ### The self-improvement -/

/-- **RH iff the antisymmetric state of the two ends is bounded below.** If `N(o_v) ≥ −C` for every
`v ≥ 0`, then `2 Re S(v) ≤ 2 Re S(0) + C`, Landau's argument removes every exponent of `S` right of
the line, and the pole-free profile sees every zero off the line. -/
theorem riemannHypothesis_iff_twoEndOdd_bddBelow :
    RiemannHypothesis ↔ ∃ C : ℝ, ∀ v : ℝ, 0 ≤ v → ∀ Q : ℕ,
      (∀ n : ℕ, Q < n → packetAutocorr (twoEndOdd v) (Real.log n) = 0) →
        -C ≤ neutralForm Q (twoEndOdd v) := by
  constructor
  · intro hRH
    refine ⟨0, fun v _ Q hQ => ?_⟩
    rw [neg_zero]
    exact neutralForm_nonneg_of_odd_of_riemannHypothesis hRH (contDiff_twoEndOdd v)
      (hasCompactSupport_twoEndOdd v) hQ (c := 0) fun u => by rw [zero_sub]; exact twoEndOdd_neg v u
  · rintro ⟨C, hC⟩
    refine riemannHypothesis_of_lagStructure_le
      (M := 2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) 0).re + C) fun u hu => ?_
    obtain ⟨Q, hQ⟩ := exists_range_twoEndOdd u
    have h := hC u hu Q hQ
    rw [neutralForm_twoEndOdd u hQ] at h
    linarith

/-- The mass of the antisymmetric state is at most four times that of the profile. -/
theorem integral_twoEndOdd_sq_le (v : ℝ) :
    ∫ u, twoEndOdd v u ^ 2 ≤ 4 * ∫ u, poleFreeProfile u ^ 2 := by
  have hc : Continuous fun u => poleFreeProfile u ^ 2 := contDiff_poleFreeProfile.continuous.pow 2
  have hcs : HasCompactSupport fun u => poleFreeProfile u ^ 2 :=
    HasCompactSupport.intro (isCompact_Icc (a := -5) (b := 5)) fun u hu => by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rw [poleFreeProfile_eq_zero (by
        rcases hu with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith)]
      ring
  have hi : Integrable fun u => poleFreeProfile u ^ 2 := hc.integrable_of_hasCompactSupport hcs
  have hshift : ∀ c : ℝ, ∫ u, poleFreeProfile (u + c) ^ 2 = ∫ u, poleFreeProfile u ^ 2 :=
    fun c => integral_add_right_eq_self (fun u => poleFreeProfile u ^ 2) c
  have hi1 : Integrable fun u => 2 * poleFreeProfile (u + v / 2) ^ 2 :=
    (hi.comp_add_right (v / 2)).const_mul 2
  have hi2 : Integrable fun u => 2 * poleFreeProfile (u - v / 2) ^ 2 :=
    (hi.comp_sub_right (v / 2)).const_mul 2
  have hcont : Continuous fun u => twoEndOdd v u ^ 2 := (contDiff_twoEndOdd v).continuous.pow 2
  have hint : Integrable fun u => twoEndOdd v u ^ 2 :=
    hcont.integrable_of_hasCompactSupport
      ((hasCompactSupport_twoEndOdd v).comp_left (g := fun x : ℝ => x ^ 2) (by norm_num))
  calc ∫ u, twoEndOdd v u ^ 2 ≤
        ∫ u, (2 * poleFreeProfile (u + v / 2) ^ 2 + 2 * poleFreeProfile (u - v / 2) ^ 2) :=
        integral_mono hint (hi1.add hi2) fun u => by
          simp only [twoEndOdd]
          nlinarith [sq_nonneg (poleFreeProfile (u + v / 2) + poleFreeProfile (u - v / 2))]
    _ = 4 * ∫ u, poleFreeProfile u ^ 2 := by
        rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul, hshift,
          show (fun u => poleFreeProfile (u - v / 2) ^ 2) =
            fun u => poleFreeProfile (u + -(v / 2)) ^ 2 from funext fun u => by ring_nf,
          hshift]
        ring

/-- The mass of the symmetric state is at most four times that of the profile. -/
theorem integral_twoEndEven_sq_le (v : ℝ) :
    ∫ u, twoEndEven v u ^ 2 ≤ 4 * ∫ u, poleFreeProfile u ^ 2 := by
  have hc : Continuous fun u => poleFreeProfile u ^ 2 := contDiff_poleFreeProfile.continuous.pow 2
  have hcs : HasCompactSupport fun u => poleFreeProfile u ^ 2 :=
    HasCompactSupport.intro (isCompact_Icc (a := -5) (b := 5)) fun u hu => by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rw [poleFreeProfile_eq_zero (by
        rcases hu with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith)]
      ring
  have hi : Integrable fun u => poleFreeProfile u ^ 2 := hc.integrable_of_hasCompactSupport hcs
  have hshift : ∀ c : ℝ, ∫ u, poleFreeProfile (u + c) ^ 2 = ∫ u, poleFreeProfile u ^ 2 :=
    fun c => integral_add_right_eq_self (fun u => poleFreeProfile u ^ 2) c
  have hi1 : Integrable fun u => 2 * poleFreeProfile (u + v / 2) ^ 2 :=
    (hi.comp_add_right (v / 2)).const_mul 2
  have hi2 : Integrable fun u => 2 * poleFreeProfile (u - v / 2) ^ 2 :=
    (hi.comp_sub_right (v / 2)).const_mul 2
  have hcont : Continuous fun u => twoEndEven v u ^ 2 := (contDiff_twoEndEven v).continuous.pow 2
  have hint : Integrable fun u => twoEndEven v u ^ 2 :=
    hcont.integrable_of_hasCompactSupport
      ((hasCompactSupport_twoEndEven v).comp_left (g := fun x : ℝ => x ^ 2) (by norm_num))
  calc ∫ u, twoEndEven v u ^ 2 ≤
        ∫ u, (2 * poleFreeProfile (u + v / 2) ^ 2 + 2 * poleFreeProfile (u - v / 2) ^ 2) :=
        integral_mono hint (hi1.add hi2) fun u => by
          simp only [twoEndEven]
          nlinarith [sq_nonneg (poleFreeProfile (u + v / 2) - poleFreeProfile (u - v / 2))]
    _ = 4 * ∫ u, poleFreeProfile u ^ 2 := by
        rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul, hshift,
          show (fun u => poleFreeProfile (u - v / 2) ^ 2) =
            fun u => poleFreeProfile (u + -(v / 2)) ^ 2 from funext fun u => by ring_nf,
          hshift]
        ring

/-- **RH iff the odd sector of every window is bounded below** by a fixed multiple of the mass:
a uniform bound on the depth of odd bound states forces their absence. -/
theorem riemannHypothesis_iff_odd_sector_bddBelow :
    RiemannHypothesis ↔ ∃ C : ℝ, ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      (∀ u, g (-u) = -g u) → ∀ Q : ℕ, (∀ n : ℕ, Q < n → packetAutocorr g (Real.log n) = 0) →
        -(C * ∫ u, g u ^ 2) ≤ neutralForm Q g := by
  constructor
  · intro hRH
    refine ⟨0, fun g hg hgc hodd Q hQ => ?_⟩
    rw [zero_mul, neg_zero]
    exact neutralForm_nonneg_of_odd_of_riemannHypothesis hRH hg hgc hQ (c := 0)
      fun u => by rw [zero_sub]; exact hodd u
  · rintro ⟨C, hC⟩
    refine riemannHypothesis_iff_twoEndOdd_bddBelow.mpr
      ⟨|C| * (4 * ∫ u, poleFreeProfile u ^ 2), fun v _ Q hQ => ?_⟩
    have h := hC (twoEndOdd v) (contDiff_twoEndOdd v) (hasCompactSupport_twoEndOdd v)
      (twoEndOdd_neg v) Q hQ
    have hm := integral_twoEndOdd_sq_le v
    have hm0 : 0 ≤ ∫ u, twoEndOdd v u ^ 2 := integral_nonneg fun u => sq_nonneg _
    have h1 : C * ∫ u, twoEndOdd v u ^ 2 ≤ |C| * ∫ u, twoEndOdd v u ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hm0
    have h2 : |C| * ∫ u, twoEndOdd v u ^ 2 ≤ |C| * (4 * ∫ u, poleFreeProfile u ^ 2) :=
      mul_le_mul_of_nonneg_left hm (abs_nonneg C)
    linarith

/-! ### The rate law -/

/-- **The zero width is the growth rate of the depth of the antisymmetric state.** For
`0 ≤ θ < ½`, every zero satisfies `|Re ρ − ½| ≤ θ` iff `N(o_v) ≥ −C e^{θ v}` for all `v ≥ 0`. -/
theorem zetaZeroWidth_le_iff_twoEndOdd_rate {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) :
    SquareRootThreshold.zetaZeroWidth ≤ θ ↔ ∃ C : ℝ, ∀ v : ℝ, 0 ≤ v → ∀ Q : ℕ,
      (∀ n : ℕ, Q < n → packetAutocorr (twoEndOdd v) (Real.log n) = 0) →
        -(C * Real.exp (θ * v)) ≤ neutralForm Q (twoEndOdd v) := by
  obtain ⟨S0, hS0⟩ : ∃ S0, S0 = 2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) 0).re :=
    ⟨_, rfl⟩
  rw [SquareRootThreshold.zetaZeroWidth_le_iff_re_le hθ0]
  constructor
  · intro hre
    obtain ⟨K, hK⟩ : ∃ K, K = ∑' z : ℂ, ‖evenCoeff zetaZeroConfig (cx poleFreeProfile) z‖ :=
      ⟨_, rfl⟩
    refine ⟨|S0| + K, fun v hv Q hQ => ?_⟩
    have hτ : ∀ z : ℂ, evenCoeff zetaZeroConfig (cx poleFreeProfile) z ≠ 0 → z.re ≤ θ := by
      intro z hz
      rcases SquareRootThreshold.mem_of_evenCoeff_ne_zero hz with h | h
      · have := hre _ h; simp at this; linarith
      · have := hre _ h; simp at this; linarith
    have hup := SquareRootThreshold.two_re_lagStructure_le_mul_exp zetaZeroConfig
      SquareRootThreshold.temperedConfig_zetaZeroConfig contDiff_cx_poleFreeProfile
      cx_poleFreeProfile_support hτ hv
    rw [← hK] at hup
    rw [neutralForm_twoEndOdd v hQ, ← hS0]
    have he : 1 ≤ Real.exp (θ * v) := Real.one_le_exp (mul_nonneg hθ0 hv)
    have h1 : -S0 ≤ |S0| * Real.exp (θ * v) := by
      nlinarith [neg_abs_le S0, abs_nonneg S0]
    linarith
  · rintro ⟨C, hC⟩ ρ hρ
    by_contra hlt
    push Not at hlt
    have hMa : ∀ u : ℝ, 0 ≤ u →
        2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) u).re ≤
          (|S0| + |C|) * Real.exp (θ * u) := by
      intro u hu
      obtain ⟨Q, hQ⟩ := exists_range_twoEndOdd u
      have h := hC u hu Q hQ
      rw [neutralForm_twoEndOdd u hQ, ← hS0] at h
      have he : 1 ≤ Real.exp (θ * u) := Real.one_le_exp (mul_nonneg hθ0 hu)
      have hC' : C * Real.exp (θ * u) ≤ |C| * Real.exp (θ * u) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
      have hS : |S0| * 1 ≤ |S0| * Real.exp (θ * u) := mul_le_mul_of_nonneg_left he (abs_nonneg S0)
      linarith [le_abs_self S0]
    refine evenCoeff_poleFreeProfile_sees hρ (by linarith)
      (SquareRootThreshold.evenCoeff_eq_zero_of_two_re_lagStructure_le_exp zetaZeroConfig
        SquareRootThreshold.temperedConfig_zetaZeroConfig contDiff_cx_poleFreeProfile
        cx_poleFreeProfile_support hθ0 hθ
        (fun x hx him => absurd him (evenCoeff_poleFreeProfile_real hx)) hMa ?_)
    rw [show (ρ - 1 / 2).re = ρ.re - 1 / 2 by simp]
    linarith

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
