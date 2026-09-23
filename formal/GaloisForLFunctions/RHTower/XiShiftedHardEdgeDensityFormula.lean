import GaloisForLFunctions.RHTower.XiShiftedHardEdgePrimeDensity
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeMomentDerivatives

/-!
# The completed source formula in density coordinates

The Euler-ray response of the completed zeta splits, at every mass above the pole, into a
nonnegative polar term, the archimedean density and the prime density:

`M_n(X) = 2(X − 1/4)^{-(n+1)} + (1/pi)·A_n(X) − (1/pi)·Pi_n(X)`.

At `n = 0` this is the corpus's arithmetic evaluation of the Weil diagonal of the Cauchy test,
read through the Poisson reproduction of the archimedean rate and the closed form of the prime
series.  All four terms obey the same mass-derivative recursion, so the identity propagates to
every order by uniqueness of the derivative.
-/

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## Reality of the archimedean factor on the real axis -/

theorem im_gaussDigammaSeriesTerm_ofReal (s : ℝ) (n : ℕ) :
    (gaussDigammaSeriesTerm ((s : ℝ) : ℂ) n).im = 0 := by
  rw [gaussDigammaSeriesTerm]
  have h1 : ((s : ℂ) + (n : ℂ)) = (((s + n : ℝ)) : ℂ) := by push_cast; ring
  have h2 : ((1 : ℂ) / (((n : ℂ)) + 1)) = ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
  have h3 : ((1 : ℂ) / ((((s + n : ℝ))) : ℂ)) = ((1 / (s + n) : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, h3]
  simp

theorem im_digamma_ofReal {s : ℝ} (hs : 0 < s) : (Complex.digamma ((s : ℝ) : ℂ)).im = 0 := by
  have hre : (((s : ℝ) : ℂ)).re = s := Complex.ofReal_re s
  have hsum : Summable fun n : ℕ => gaussDigammaSeriesTerm ((s : ℝ) : ℂ) n :=
    summable_norm_iff.mp
      (GaloisForLFunctions.HTGeometry.summable_norm_gaussDigammaSeriesTerm_all _)
  rw [digamma_eq_neg_euler_add_tsum_gauss (by rw [hre]; exact hs), Complex.add_im,
    Complex.im_tsum hsum]
  simp [im_gaussDigammaSeriesTerm_ofReal]

theorem digamma_ofReal_eq {s : ℝ} (hs : 0 < s) :
    Complex.digamma ((s : ℝ) : ℂ)
      = (((Complex.digamma ((s : ℝ) : ℂ)).re : ℝ) : ℂ) := by
  refine Complex.ext ?_ ?_
  · rw [Complex.ofReal_re]
  · rw [Complex.ofReal_im, im_digamma_ofReal hs]

theorem logDeriv_Gammaℝ_ofReal_eq {s : ℝ} (hs : 0 < s) :
    logDeriv Complex.Gammaℝ ((s : ℝ) : ℂ)
      = (((logDeriv Complex.Gammaℝ ((s : ℝ) : ℂ)).re : ℝ) : ℂ) := by
  have hre : (((s : ℝ) : ℂ)).re = s := Complex.ofReal_re s
  rw [logDeriv_Gammaℝ_of_re_pos (by rw [hre]; exact hs)]
  have hhalf : (((s : ℝ) : ℂ)) / 2 = (((s / 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [hhalf, digamma_ofReal_eq (by linarith : (0 : ℝ) < s / 2)]
  refine Complex.ext ?_ ?_
  · rw [Complex.ofReal_re]
  · simp

/-! ## The density moments -/

/-- The density form of the Euler-ray response: polar, archimedean and prime. -/
def routeUDensityMoment (n : ℕ) (X : ℝ) : ℂ :=
  2 * ((((X - 1 / 4) ^ (n + 1) : ℝ)) : ℂ)⁻¹
    + (1 / (Real.pi : ℂ)) * routeUArchimedeanMoment n X
    - (1 / (Real.pi : ℂ)) * routeUPrimeMoment n X

theorem hasDerivAt_polarMoment (n : ℕ) {X : ℝ} (hX : 1 / 4 < X) :
    HasDerivAt (fun Z : ℝ => 2 * ((((Z - 1 / 4) ^ (n + 1) : ℝ)) : ℂ)⁻¹)
      (-((n : ℂ) + 1) * (2 * ((((X - 1 / 4) ^ (n + 2) : ℝ)) : ℂ)⁻¹)) X := by
  have hpos : (0 : ℝ) < X - 1 / 4 := by linarith
  have hne : (X - 1 / 4) ≠ 0 := ne_of_gt hpos
  have hbase : HasDerivAt (fun Z : ℝ => (Z - 1 / 4) ^ (n + 1))
      (((n : ℝ) + 1) * (X - 1 / 4) ^ n) X := by
    have h : HasDerivAt (fun Z : ℝ => Z - 1 / 4) 1 X := (hasDerivAt_id X).sub_const _
    have h2 : HasDerivAt (fun Z : ℝ => (Z - 1 / 4) ^ (n + 1))
        ((((n + 1 : ℕ) : ℝ)) * (X - 1 / 4) ^ (n + 1 - 1) * 1) X := h.pow (n + 1)
    refine h2.congr_deriv ?_
    push_cast
    simp
  have hnepow : (X - 1 / 4) ^ (n + 1) ≠ 0 := by positivity
  have hinv : HasDerivAt (fun Z : ℝ => ((Z - 1 / 4) ^ (n + 1))⁻¹)
      (-((n : ℝ) + 1) * ((X - 1 / 4) ^ (n + 2))⁻¹) X := by
    refine (hbase.inv hnepow).congr_deriv ?_
    have hun : ((X - 1 / 4) ^ n) ≠ 0 := by positivity
    have hu2 : ((X - 1 / 4) ^ (n + 2)) ≠ 0 := by positivity
    have hpowid : ((X - 1 / 4) ^ (n + 1)) ^ (2 : ℕ) = (X - 1 / 4) ^ (n + 2) * (X - 1 / 4) ^ n := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    rw [hpowid, div_eq_mul_inv, mul_inv,
      show -(((n : ℝ) + 1) * (X - 1 / 4) ^ n)
          * (((X - 1 / 4) ^ (n + 2))⁻¹ * ((X - 1 / 4) ^ n)⁻¹)
        = (-((n : ℝ) + 1) * ((X - 1 / 4) ^ (n + 2))⁻¹)
          * ((X - 1 / 4) ^ n * ((X - 1 / 4) ^ n)⁻¹) by ring,
      mul_inv_cancel₀ hun, mul_one]
  have hcast : HasDerivAt (fun Z : ℝ => ((((Z - 1 / 4) ^ (n + 1) : ℝ)) : ℂ)⁻¹)
      (((-((n : ℝ) + 1) * ((X - 1 / 4) ^ (n + 2))⁻¹ : ℝ)) : ℂ) X := by
    refine (hinv.ofReal_comp).congr_of_eventuallyEq ?_
    filter_upwards with Z
    rw [Complex.ofReal_inv]
  have hres := hcast.const_mul (2 : ℂ)
  refine hres.congr_deriv ?_
  push_cast
  ring

theorem hasDerivAt_routeUDensityMoment (n : ℕ) {X : ℝ} (hX : 1 / 4 < X) :
    HasDerivAt (routeUDensityMoment n)
      (-((n : ℂ) + 1) * routeUDensityMoment (n + 1) X) X := by
  have hXpos : (0 : ℝ) < X := by linarith
  have hpolar := hasDerivAt_polarMoment n hX
  have harch := (hasDerivAt_routeUArchimedeanMoment n hXpos).const_mul (1 / (Real.pi : ℂ))
  have hprime := (hasDerivAt_routeUPrimeMoment n hX).const_mul (1 / (Real.pi : ℂ))
  have hsum := (hpolar.add harch).sub hprime
  refine hsum.congr_deriv ?_
  rw [routeUDensityMoment]
  ring

/-! ## The base case -/

theorem routeUDensityMoment_zero_eq {a : ℝ} (ha : 1 / 2 < a) :
    routeUDensityMoment 0 (a ^ (2 : ℕ))
      = ((a : ℂ))⁻¹ * (((1 / 2 : ℂ) + (a : ℂ))⁻¹ + ((1 / 2 : ℂ) + (a : ℂ) - 1)⁻¹
          + logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + (a : ℂ))
          - LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
              ((1 / 2 : ℂ) + (a : ℂ))) := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hane : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt ha0)
  have hX : (1 : ℝ) / 4 < a ^ (2 : ℕ) := by nlinarith
  have hsqrt : Real.sqrt (a ^ (2 : ℕ)) = a := Real.sqrt_sq ha0.le
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt Real.pi_pos)
  have hshift : ((1 / 2 : ℂ) + (a : ℂ)) = (((1 / 2 + a : ℝ)) : ℂ) := by push_cast; ring
  -- the polar term
  have hpolar : 2 * ((((a ^ (2 : ℕ) - 1 / 4) ^ (0 + 1) : ℝ)) : ℂ)⁻¹
      = ((a : ℂ))⁻¹ * (((1 / 2 : ℂ) + (a : ℂ))⁻¹ + ((1 / 2 : ℂ) + (a : ℂ) - 1)⁻¹) := by
    have h1 : ((1 / 2 : ℂ) + (a : ℂ)) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at this
      norm_num at this
      linarith
    have h2 : ((1 / 2 : ℂ) + (a : ℂ) - 1) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.one_re,
        Complex.zero_re] at this
      norm_num at this
      linarith
    have h3 : ((((a ^ (2 : ℕ) - 1 / 4) ^ (0 + 1) : ℝ)) : ℂ) ≠ 0 := by
      refine Complex.ofReal_ne_zero.2 ?_
      have : (0 : ℝ) < (a ^ (2 : ℕ) - 1 / 4) ^ (0 + 1) := by
        have : (0 : ℝ) < a ^ (2 : ℕ) - 1 / 4 := by nlinarith
        positivity
      exact ne_of_gt this
    rw [pow_one]
    have hfac : ((((a ^ (2 : ℕ) - 1 / 4 : ℝ)) : ℂ))
        = ((1 / 2 : ℂ) + (a : ℂ)) * ((1 / 2 : ℂ) + (a : ℂ) - 1) := by
      push_cast
      ring
    have huv : ((1 / 2 : ℂ) + (a : ℂ)) + ((1 / 2 : ℂ) + (a : ℂ) - 1) = 2 * (a : ℂ) := by ring
    rw [hfac, mul_inv, inv_add_inv h1 h2, huv]
    field_simp
  -- the archimedean term
  have harch : (1 / (Real.pi : ℂ)) * routeUArchimedeanMoment 0 (a ^ (2 : ℕ))
      = ((a : ℂ))⁻¹ * logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + (a : ℂ)) := by
    have hL := logDeriv_Gammaℝ_ofReal_eq (by linarith : (0 : ℝ) < 1 / 2 + a)
    rw [routeUArchimedeanMoment_zero_eq ha0, hshift]
    conv_rhs => rw [hL]
    push_cast
    field_simp
  -- the prime term
  have hprime : (1 / (Real.pi : ℂ)) * routeUPrimeMoment 0 (a ^ (2 : ℕ))
      = ((a : ℂ))⁻¹ * LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          ((1 / 2 : ℂ) + (a : ℂ)) := by
    rw [routeUPrimeMoment_zero_eq hX, hsqrt, hshift]
    push_cast
    field_simp
  rw [routeUDensityMoment, hpolar, harch, hprime]
  ring

/-! ## The density formula at every order -/

/-- **(CSHC.6) in density coordinates, at every order.** -/
theorem xiResolventMoment_eq_routeUDensityMoment :
    ∀ (n : ℕ) {X : ℝ}, 1 / 4 < X → xiResolventMoment n X = routeUDensityMoment n X := by
  intro n
  induction n with
  | zero =>
    intro X hX
    have hXpos : (0 : ℝ) < X := by linarith
    have hsq : Real.sqrt X ^ (2 : ℕ) = X := Real.sq_sqrt hXpos.le
    have ha : (1 : ℝ) / 2 < Real.sqrt X := by
      have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 4) hX
      rwa [show Real.sqrt (1 / 4 : ℝ) = 1 / 2 by
        rw [show (1 : ℝ) / 4 = (1 / 2) ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]] at h
    have ha0 : (0 : ℝ) < Real.sqrt X := by linarith
    have hane : ((Real.sqrt X : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt ha0)
    have hbase := tsum_routeUHardEdgeRationalTestSq_one_eq_arithmetic ha
    rw [tsum_routeUHardEdgeRationalTestSq_one] at hbase
    rw [hsq] at hbase
    have hkey : ((Real.sqrt X : ℝ) : ℂ) * xiResolventMoment 0 X
        = (((1 / 2 : ℂ) + (Real.sqrt X : ℂ))⁻¹ + ((1 / 2 : ℂ) + (Real.sqrt X : ℂ) - 1)⁻¹
            + logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + (Real.sqrt X : ℂ))
            - LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
                ((1 / 2 : ℂ) + (Real.sqrt X : ℂ))) := by
      have hcast : (((X : ℝ)) : ℂ) = ((Real.sqrt X : ℝ) : ℂ) * ((Real.sqrt X : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul]
        congr 1
        nlinarith [hsq]
      rw [hcast] at hbase
      field_simp at hbase ⊢
      linear_combination hbase
    have hdens := routeUDensityMoment_zero_eq ha
    rw [hsq] at hdens
    rw [hdens, ← hkey]
    field_simp
  | succ n ih =>
    intro X hX
    have hXpos : (0 : ℝ) < X := by linarith
    have hEq : (fun Z : ℝ => xiResolventMoment n Z) =ᶠ[nhds X] routeUDensityMoment n := by
      filter_upwards [Ioi_mem_nhds hX] with Z hZ
      exact ih hZ
    have hM := hasDerivAt_xiResolventMoment hXpos n
    have hD := hasDerivAt_routeUDensityMoment n hX
    have hM' : HasDerivAt (routeUDensityMoment n)
        (-((n : ℂ) + 1) * xiResolventMoment (n + 1) X) X := hM.congr_of_eventuallyEq hEq.symm
    have huniq := hM'.unique hD
    have hne : (-((n : ℂ) + 1)) ≠ 0 := by
      intro h
      have hn : ((n : ℂ) + 1) = 0 := by linear_combination -h
      have := congrArg Complex.re hn
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.zero_re] at this
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact mul_left_cancel₀ hne huniq

end RHTower

end
