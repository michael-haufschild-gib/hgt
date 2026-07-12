import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowHolomorphy
import GaloisForLFunctions.RHTower.CCMShiftedXiCancellation
import GaloisForLFunctions.RHTower.XiLogDerivNotHolonomic
import GaloisForLFunctions.RHTower.CarrierSlope

/-!
# Pole-filled continuation of the dyadic sharp prime source

Let `R(t) = (t - 1) * ζ(t)` with the removable value `R(1) = 1`, and let `M(s)` be the
Mellin factor of the sharp interval `[1,2]`.  The polar zeta term and the von-Mangoldt
logarithmic derivative combine as

`dslope (2*M(3/2)*R(s-1/2) - 2*M(s)) (3/2) s
  + 2*M(s) * logDeriv R(s-1/2)`.

The divided-difference numerator vanishes at `s = 3/2`, so the zeta pole is cancelled by
construction.  The only remaining possible poles are zeros of the pole-filled zeta, while the
dyadic quadrature remainder is holomorphic on `Re s > 1/2`.
-/

open Complex Filter Function Set

noncomputable section

namespace RHTower

/-- Entire numerator in which the shifted zeta pole cancellation is encoded as a zero. -/
def dyadicSharpPrimePoleNumerator (s : ℂ) : ℂ :=
  2 * sharpPrimeWindowMellin (Real.log 2) (3 / 2) *
      regularizedRiemannZeta (s - 1 / 2) -
    2 * sharpPrimeWindowMellin (Real.log 2) s

/-- The pole-filled sharp source before the holomorphic quadrature correction. -/
def dyadicSharpPrimePoleFilledMain (s : ℂ) : ℂ :=
  dslope dyadicSharpPrimePoleNumerator (3 / 2) s +
    2 * sharpPrimeWindowMellin (Real.log 2) s *
      logDeriv regularizedRiemannZeta (s - 1 / 2)

/-- Canonical continued dyadic sharp prime-polar source. -/
def dyadicSharpPrimeContinuedSource (s : ℂ) : ℂ :=
  dyadicSharpPrimePoleFilledMain s -
    2 * dyadicSharpPrimeWindowErrorSeries s

theorem differentiable_dyadicSharpPrimePoleNumerator :
    Differentiable ℂ dyadicSharpPrimePoleNumerator := by
  unfold dyadicSharpPrimePoleNumerator
  exact ((differentiable_regularizedRiemannZeta.comp
      (differentiable_id.sub_const (1 / 2))).const_mul
        (2 * sharpPrimeWindowMellin (Real.log 2) (3 / 2))).sub
    (differentiable_sharpPrimeWindowMellin_logTwo.const_mul 2)

@[simp] theorem dyadicSharpPrimePoleNumerator_three_halves :
    dyadicSharpPrimePoleNumerator (3 / 2) = 0 := by
  rw [dyadicSharpPrimePoleNumerator]
  norm_num [regularizedRiemannZeta_one]

/-- The divided-difference pole numerator is entire, including at the cancelled zeta pole. -/
theorem differentiable_dyadicSharpPrimePoleDividedDifference :
    Differentiable ℂ
      (dslope dyadicSharpPrimePoleNumerator (3 / 2)) := by
  rw [← differentiableOn_univ, differentiableOn_dslope Filter.univ_mem]
  exact differentiable_dyadicSharpPrimePoleNumerator.differentiableOn

theorem meromorphicAt_logDeriv_regularizedRiemannZeta (s : ℂ) :
    MeromorphicAt (logDeriv regularizedRiemannZeta) s := by
  rw [show logDeriv regularizedRiemannZeta =
      deriv regularizedRiemannZeta / regularizedRiemannZeta by
    funext z
    rw [logDeriv_apply]
    rfl]
  have hreg : AnalyticAt ℂ regularizedRiemannZeta s :=
    (differentiable_regularizedRiemannZeta.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  exact hreg.deriv.meromorphicAt.div hreg.meromorphicAt

/-- The pole-filled zeta is not identically zero near any point, since its value at `1` is `1`. -/
theorem analyticOrderAt_regularizedRiemannZeta_ne_top (s : ℂ) :
    analyticOrderAt regularizedRiemannZeta s ≠ ⊤ := by
  intro htop
  have hev := analyticOrderAt_eq_top.mp htop
  have hreg : AnalyticOnNhd ℂ regularizedRiemannZeta Set.univ :=
    differentiable_regularizedRiemannZeta.differentiableOn.analyticOnNhd isOpen_univ
  have heq := hreg.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ s) hev
  have hone := heq (Set.mem_univ (1 : ℂ))
  norm_num only [regularizedRiemannZeta_one, Pi.zero_apply] at hone

/-- Every zero of the pole-filled zeta produces an exact simple pole of its logarithmic
derivative, irrespective of multiplicity. -/
theorem meromorphicOrderAt_logDeriv_regularizedRiemannZeta_eq_neg_one
    {s : ℂ} (hzero : regularizedRiemannZeta s = 0) :
    meromorphicOrderAt (logDeriv regularizedRiemannZeta) s =
      ((-1 : ℤ) : WithTop ℤ) := by
  have hreg : AnalyticAt ℂ regularizedRiemannZeta s :=
    (differentiable_regularizedRiemannZeta.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  have hmne : (analyticOrderAt regularizedRiemannZeta s).toNat ≠ 0 := by
    intro h0
    have horder0 : analyticOrderAt regularizedRiemannZeta s = 0 := by
      rw [(ENat.coe_toNat
        (analyticOrderAt_regularizedRiemannZeta_ne_top s)).symm, h0]
      rfl
    rcases analyticOrderAt_eq_zero.mp horder0 with h | h
    · exact h hreg
    · exact h hzero
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hmne
  have horder : analyticOrderAt regularizedRiemannZeta s = (k + 1 : ℕ) := by
    calc
      analyticOrderAt regularizedRiemannZeta s =
          ((analyticOrderAt regularizedRiemannZeta s).toNat : ℕ∞) :=
        (ENat.coe_toNat (analyticOrderAt_regularizedRiemannZeta_ne_top s)).symm
      _ = (k + 1 : ℕ) := by rw [hk, Nat.succ_eq_add_one]
  have hderiv : analyticOrderAt (deriv regularizedRiemannZeta) s = k :=
    analyticOrderAt_deriv_of_pos hreg horder
  rw [show logDeriv regularizedRiemannZeta =
      deriv regularizedRiemannZeta / regularizedRiemannZeta by
    funext z
    rw [logDeriv_apply]
    rfl]
  rw [meromorphicOrderAt_div hreg.deriv.meromorphicAt hreg.meromorphicAt,
    hreg.deriv.meromorphicOrderAt_eq, hreg.meromorphicOrderAt_eq,
    hderiv, horder, ENat.map_coe, ENat.map_coe]
  exact_mod_cast (show (k : ℤ) - ((k + 1 : ℕ) : ℤ) = -1 by omega)

/-- The completed sharp source is meromorphic on the whole quadrature half-plane. -/
theorem meromorphicOn_dyadicSharpPrimeContinuedSource_rightHalf :
    MeromorphicOn dyadicSharpPrimeContinuedSource {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  let U : Set ℂ := {z : ℂ | 1 / 2 < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hdiv : AnalyticAt ℂ
      (dslope dyadicSharpPrimePoleNumerator (3 / 2)) s :=
    (differentiable_dyadicSharpPrimePoleDividedDifference.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  have hM : AnalyticAt ℂ (sharpPrimeWindowMellin (Real.log 2)) s :=
    (differentiable_sharpPrimeWindowMellin_logTwo.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  have hshift : AnalyticAt ℂ (fun z : ℂ => z - 1 / 2) s := by fun_prop
  have hlog : MeromorphicAt
      (fun z : ℂ => logDeriv regularizedRiemannZeta (z - 1 / 2)) s :=
    MeromorphicAt.comp_analyticAt
      (meromorphicAt_logDeriv_regularizedRiemannZeta (s - 1 / 2)) hshift
  have herr : AnalyticAt ℂ dyadicSharpPrimeWindowErrorSeries s :=
    (differentiableOn_dyadicSharpPrimeWindowErrorSeries_rightHalf.analyticOnNhd
      hUopen) s hs
  exact (hdiv.meromorphicAt.add
    ((analyticAt_const.mul hM).meromorphicAt.mul hlog)).sub
      (analyticAt_const.mul herr).meromorphicAt

/-- Away from a zero of the pole-filled zeta, the continued sharp source is analytic. -/
theorem analyticAt_dyadicSharpPrimeContinuedSource_of_regularizedZeta_ne_zero
    {s : ℂ} (hs : 1 / 2 < s.re)
    (hz : regularizedRiemannZeta (s - 1 / 2) ≠ 0) :
    AnalyticAt ℂ dyadicSharpPrimeContinuedSource s := by
  let U : Set ℂ := {z : ℂ | 1 / 2 < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hdiv : AnalyticAt ℂ
      (dslope dyadicSharpPrimePoleNumerator (3 / 2)) s :=
    (differentiable_dyadicSharpPrimePoleDividedDifference.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  have hM : AnalyticAt ℂ (sharpPrimeWindowMellin (Real.log 2)) s :=
    (differentiable_sharpPrimeWindowMellin_logTwo.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  have hreg : AnalyticAt ℂ regularizedRiemannZeta (s - 1 / 2) :=
    (differentiable_regularizedRiemannZeta.differentiableOn.analyticOnNhd
      isOpen_univ) (s - 1 / 2) (Set.mem_univ _)
  have hlog : AnalyticAt ℂ
      (fun z : ℂ => logDeriv regularizedRiemannZeta (z - 1 / 2)) s := by
    rw [show (fun z : ℂ => logDeriv regularizedRiemannZeta (z - 1 / 2)) =
        fun z : ℂ => deriv regularizedRiemannZeta (z - 1 / 2) /
          regularizedRiemannZeta (z - 1 / 2) by
      funext z
      rw [logDeriv_apply]]
    have hshift : AnalyticAt ℂ (fun z : ℂ => z - 1 / 2) s := by fun_prop
    have hnum := AnalyticAt.comp (f := fun z : ℂ => z - 1 / 2) (x := s)
      hreg.deriv hshift
    have hden := AnalyticAt.comp (f := fun z : ℂ => z - 1 / 2) (x := s)
      hreg hshift
    simpa only [Function.comp_apply] using hnum.div hden hz
  have herr : AnalyticAt ℂ dyadicSharpPrimeWindowErrorSeries s :=
    (differentiableOn_dyadicSharpPrimeWindowErrorSeries_rightHalf.analyticOnNhd
      hUopen) s hs
  exact (hdiv.add ((analyticAt_const.mul hM).mul hlog)).sub
    (analyticAt_const.mul herr)

/-- In particular the shifted zeta pole at `3/2` is genuinely removable in the complete source. -/
theorem analyticAt_dyadicSharpPrimeContinuedSource_three_halves :
    AnalyticAt ℂ dyadicSharpPrimeContinuedSource (3 / 2) := by
  apply analyticAt_dyadicSharpPrimeContinuedSource_of_regularizedZeta_ne_zero
  · norm_num
  · norm_num [regularizedRiemannZeta_one]

/-- **Sharp-window noncensorship.**  Every right-half Xi zero produces an exact simple pole of
the continued dyadic sharp source.  The artificial zeta pole at `3/2` has already been removed;
these are genuine divisor poles, and the positive-width Mellin factor cannot cancel them. -/
theorem meromorphicOrderAt_dyadicSharpPrimeContinuedSource_eq_neg_one
    (q : XiRightZeroCopy) :
    meromorphicOrderAt dyadicSharpPrimeContinuedSource (xiRightShiftedPole q) =
      ((-1 : ℤ) : WithTop ℤ) := by
  let p : ℂ := xiRightShiftedPole q
  let ρ : ℂ := (q.1.1 : ℂ)
  have hpρ : p - 1 / 2 = ρ := by
    simpa only [p, ρ] using xiRightShiftedPole_sub_half q
  have hcenterRe := congrArg Complex.re
    (xiRightCenteredZero_eq_support_sub_half q)
  simp only [Complex.sub_re] at hcenterRe
  norm_num at hcenterRe
  have hcenterBounds := abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)
  have hρpos : 0 < ρ.re := by
    dsimp only [ρ]
    linarith
  have hρlt : ρ.re < 1 := by
    dsimp only [ρ]
    linarith
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hρlt
    exact (lt_irrefl 1 hρlt).elim
  have hxi : xi ρ = 0 := by
    dsimp only [ρ]
    exact xi_eq_zero_of_mem_divisor_support q.1.1
  have hζ : riemannZeta ρ = 0 := (xi_eq_zero_iff hρpos hρ1).mp hxi
  have hregZero : regularizedRiemannZeta ρ = 0 := by
    rw [regularizedRiemannZeta_of_ne_one hρ1, hζ, mul_zero]
  let shift : ℂ → ℂ := fun z => z - 1 / 2
  have hshiftAnalytic : AnalyticAt ℂ shift p := by
    dsimp only [shift]
    fun_prop
  have hshiftDeriv : deriv shift p ≠ 0 := by
    dsimp only [shift]
    rw [deriv_sub_const, deriv_id'']
    norm_num
  have hshiftOrder : meromorphicOrderAt
      (fun z : ℂ => logDeriv regularizedRiemannZeta (z - 1 / 2)) p =
        ((-1 : ℤ) : WithTop ℤ) := by
    have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero
      (f := logDeriv regularizedRiemannZeta) (g := shift) (x := p)
      hshiftAnalytic hshiftDeriv
    rw [show shift p = ρ by simpa only [shift] using hpρ,
      meromorphicOrderAt_logDeriv_regularizedRiemannZeta_eq_neg_one hregZero] at hcomp
    simpa only [shift, Function.comp_apply] using hcomp
  have hpRight : 1 < p.re := by
    dsimp only [p]
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re]
    linarith [xiRightCenteredZero_re_pos q]
  have hpHalf : 1 / 2 < p.re := by linarith
  have hMne : sharpPrimeWindowMellin (Real.log 2) p ≠ 0 :=
    sharpPrimeWindowMellin_ne_zero_of_one_lt_re
      (Real.log_pos (by norm_num)) hpRight
  let singular : ℂ → ℂ := fun z =>
    2 * sharpPrimeWindowMellin (Real.log 2) z *
      logDeriv regularizedRiemannZeta (z - 1 / 2)
  have hM : AnalyticAt ℂ (sharpPrimeWindowMellin (Real.log 2)) p :=
    (differentiable_sharpPrimeWindowMellin_logTwo.differentiableOn.analyticOnNhd
      isOpen_univ) p (Set.mem_univ p)
  have hfac : AnalyticAt ℂ
      (fun z : ℂ => 2 * sharpPrimeWindowMellin (Real.log 2) z) p :=
    analyticAt_const.mul hM
  have hfac0 : 2 * sharpPrimeWindowMellin (Real.log 2) p ≠ 0 :=
    mul_ne_zero (by norm_num) hMne
  have hfacOrder : meromorphicOrderAt
      (fun z : ℂ => 2 * sharpPrimeWindowMellin (Real.log 2) z) p = 0 := by
    rw [hfac.meromorphicOrderAt_eq,
      hfac.analyticOrderAt_eq_zero.mpr hfac0]
    simp
  have hshiftMero : MeromorphicAt
      (fun z : ℂ => logDeriv regularizedRiemannZeta (z - 1 / 2)) p := by
    have hbase : MeromorphicAt (logDeriv regularizedRiemannZeta) (shift p) := by
      rw [show shift p = ρ by simpa only [shift] using hpρ]
      exact meromorphicAt_logDeriv_regularizedRiemannZeta ρ
    have hcomp := MeromorphicAt.comp_analyticAt
      (f := logDeriv regularizedRiemannZeta) (g := shift)
      hbase hshiftAnalytic
    simpa only [shift, Function.comp_apply] using hcomp
  have hsingOrder : meromorphicOrderAt singular p =
      ((-1 : ℤ) : WithTop ℤ) := by
    dsimp only [singular]
    rw [fun_meromorphicOrderAt_mul hfac.meromorphicAt hshiftMero,
      hfacOrder, hshiftOrder]
    norm_num
  let correction : ℂ → ℂ := fun z =>
    dslope dyadicSharpPrimePoleNumerator (3 / 2) z -
      2 * dyadicSharpPrimeWindowErrorSeries z
  have hdiv : AnalyticAt ℂ
      (dslope dyadicSharpPrimePoleNumerator (3 / 2)) p :=
    (differentiable_dyadicSharpPrimePoleDividedDifference.differentiableOn.analyticOnNhd
      isOpen_univ) p (Set.mem_univ p)
  have herr : AnalyticAt ℂ dyadicSharpPrimeWindowErrorSeries p :=
    (differentiableOn_dyadicSharpPrimeWindowErrorSeries_rightHalf.analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)) p hpHalf
  have hcorr : AnalyticAt ℂ correction p := by
    dsimp only [correction]
    exact hdiv.sub (analyticAt_const.mul herr)
  have hlt : meromorphicOrderAt singular p <
      meromorphicOrderAt correction p := by
    rw [hsingOrder]
    exact lt_of_lt_of_le
      (by exact_mod_cast (show (-1 : ℤ) < 0 by omega))
      hcorr.meromorphicOrderAt_nonneg
  have hfun : dyadicSharpPrimeContinuedSource = singular + correction := by
    funext z
    simp only [dyadicSharpPrimeContinuedSource, dyadicSharpPrimePoleFilledMain,
      singular, correction, Pi.add_apply]
    ring
  rw [hfun, meromorphicOrderAt_add_eq_left_of_lt hcorr.meromorphicAt hlt,
    hsingOrder]

/-- **Sharp-source holomorphy criterion for RH.**  After pole filling and exact quadrature
correction, one fixed dyadic sharp source is holomorphic on `Re s > 1` exactly when RH holds.
This statement has no test-function regularity interface and no divisor hypothesis. -/
theorem riemannHypothesis_iff_dyadicSharpPrimeContinuedSource_analyticOn_rightOne :
    RiemannHypothesis ↔
      AnalyticOnNhd ℂ dyadicSharpPrimeContinuedSource {s : ℂ | 1 < s.re} := by
  constructor
  · intro hRH
    have hxi := rh_iff_xi_ne_zero_right.mp hRH
    intro s hs
    change 1 < s.re at hs
    apply analyticAt_dyadicSharpPrimeContinuedSource_of_regularizedZeta_ne_zero
    · linarith
    · let t : ℂ := s - 1 / 2
      have htRight : t ∈ rightHalf := by
        rw [mem_rightHalf]
        dsimp only [t]
        norm_num [Complex.sub_re]
        linarith
      change regularizedRiemannZeta t ≠ 0
      by_cases ht : t = 1
      · rw [ht, regularizedRiemannZeta_one]
        norm_num
      · rw [regularizedRiemannZeta_of_ne_one ht]
        apply mul_ne_zero (sub_ne_zero.mpr ht)
        intro hζ
        have htpos : 0 < t.re := by
          rw [mem_rightHalf] at htRight
          linarith
        exact hxi t htRight ((xi_eq_zero_iff htpos ht).mpr hζ)
  · intro han
    by_contra hRH
    have hne : Nonempty XiRightZeroCopy :=
      nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
    let q : XiRightZeroCopy := Classical.choice hne
    let p : ℂ := xiRightShiftedPole q
    have hp : 1 < p.re := by
      dsimp only [p]
      rw [xiRightShiftedPole, Complex.add_re, Complex.one_re]
      linarith [xiRightCenteredZero_re_pos q]
    have hpAnalytic : AnalyticAt ℂ dyadicSharpPrimeContinuedSource p := han p hp
    have hnonneg : (0 : WithTop ℤ) ≤
        meromorphicOrderAt dyadicSharpPrimeContinuedSource p :=
      hpAnalytic.meromorphicOrderAt_nonneg
    have horder := meromorphicOrderAt_dyadicSharpPrimeContinuedSource_eq_neg_one q
    dsimp only [p] at hnonneg
    rw [horder] at hnonneg
    have hnot : ¬ ((0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)) := by
      exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)
    exact hnot hnonneg

/-- Logarithmic derivative of the pole-filled zeta away from the filled pole. -/
theorem logDeriv_regularizedRiemannZeta_eq
    {t : ℂ} (ht : t ≠ 1) (hz : riemannZeta t ≠ 0) :
    logDeriv regularizedRiemannZeta t =
      1 / (t - 1) + zetaLogDeriv t := by
  have hev : regularizedRiemannZeta =ᶠ[nhds t]
      fun z => (z - 1) * riemannZeta z := by
    filter_upwards [isOpen_ne.mem_nhds ht] with z hz1
    exact regularizedRiemannZeta_of_ne_one hz1
  have hζdiff : DifferentiableAt ℂ riemannZeta t :=
    differentiableAt_riemannZeta ht
  have hprod0 := ((hasDerivAt_id t).sub_const 1).mul hζdiff.hasDerivAt
  have hprod : HasDerivAt (fun z : ℂ => (z - 1) * riemannZeta z)
      (riemannZeta t + (t - 1) * deriv riemannZeta t) t := by
    convert hprod0 using 1 <;> simp [Function.id_def] <;> ring
  rw [logDeriv_apply, hev.deriv_eq, hprod.deriv,
    regularizedRiemannZeta_of_ne_one ht, zetaLogDeriv]
  have ht1 : t - 1 ≠ 0 := sub_ne_zero.mpr ht
  field_simp [ht1, hz]

/-- On the absolute-convergence half-plane, the pole-filled expression is exactly the expected
polar zeta plus von-Mangoldt logarithmic-derivative expression. -/
theorem dyadicSharpPrimePoleFilledMain_eq_zetaLogDeriv
    {s : ℂ} (hs : 3 / 2 < s.re) :
    dyadicSharpPrimePoleFilledMain s =
      2 * sharpPrimeWindowMellin (Real.log 2) (3 / 2) *
          riemannZeta (s - 1 / 2) +
        2 * sharpPrimeWindowMellin (Real.log 2) s *
          zetaLogDeriv (s - 1 / 2) := by
  have ht : s - 1 / 2 ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.sub_re] at hre
    linarith
  have hz : riemannZeta (s - 1 / 2) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by
      norm_num [Complex.sub_re]
      linarith)
  have hs0 : s ≠ 3 / 2 := by
    intro h
    rw [h] at hs
    norm_num at hs
  rw [dyadicSharpPrimePoleFilledMain,
    dslope_of_ne _ hs0, slope_def_field,
    dyadicSharpPrimePoleNumerator_three_halves,
    sub_zero, dyadicSharpPrimePoleNumerator,
    regularizedRiemannZeta_of_ne_one ht,
    logDeriv_regularizedRiemannZeta_eq ht hz]
  have hden : (s - 1 / 2) - 1 = s - 3 / 2 := by ring
  rw [hden]
  have hden0 : s - 3 / 2 ≠ 0 := sub_ne_zero.mpr hs0
  let d : ℂ := s - 3 / 2
  have hd : d ≠ 0 := by simpa only [d] using hden0
  let A : ℂ := sharpPrimeWindowMellin (Real.log 2) (3 / 2)
  let B : ℂ := sharpPrimeWindowMellin (Real.log 2) s
  let Z : ℂ := riemannZeta (s - 1 / 2)
  let W : ℂ := zetaLogDeriv (s - 1 / 2)
  rw [show s - 3 / 2 = d by rfl]
  change (2 * A * (d * Z) - 2 * B) / d +
      2 * B * (1 / d + W) = 2 * A * Z + 2 * B * W
  rw [div_eq_mul_inv, one_div]
  have hc : d * d⁻¹ = 1 := mul_inv_cancel₀ hd
  calc
    (2 * A * (d * Z) - 2 * B) * d⁻¹ +
        2 * B * (d⁻¹ + W) =
      2 * A * Z * (d * d⁻¹) + 2 * B * W := by ring
    _ = 2 * A * Z + 2 * B * W := by rw [hc]; ring

/-- Far right, the canonical continuation is the polar-zeta/log-derivative main term minus the
holomorphic dyadic quadrature remainder. -/
theorem dyadicSharpPrimeContinuedSource_eq_zetaLogDeriv
    {s : ℂ} (hs : 3 / 2 < s.re) :
    dyadicSharpPrimeContinuedSource s =
      2 * sharpPrimeWindowMellin (Real.log 2) (3 / 2) *
          riemannZeta (s - 1 / 2) +
        2 * sharpPrimeWindowMellin (Real.log 2) s *
          zetaLogDeriv (s - 1 / 2) -
        2 * dyadicSharpPrimeWindowErrorSeries s := by
  rw [dyadicSharpPrimeContinuedSource,
    dyadicSharpPrimePoleFilledMain_eq_zetaLogDeriv hs]

end RHTower
