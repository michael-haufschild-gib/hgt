import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomHighOrderQuadrature
import GaloisForLFunctions.HTGeometry.PolynomialSmoothApproximation
import GaloisForLFunctions.RHTower.WallFinitePart

/-!
# Exact first-atom moment bounds from high-order quadrature

The local exponential enclosures are assembled into polynomial density certificates.  Their
integrals are exact rational numbers, leaving only one uniform analytic tail estimate.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators Interval

namespace RHTower

noncomputable section

def thetaCuspFirstAtomHighOrderLowerPolynomial64 (r j : ℕ) : ℝ[X] :=
  C (12.5663706143591729538 : ℝ) *
    (C ((j : ℝ) / 64) + X) ^ (2 * r) *
    thetaCuspFirstSourceTaylorLower64 j *
    (C ((0.0432139182637 : ℝ) *
      thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j) *
      thetaCuspFirstRateTaylorLocalLowerCertificate64 j)

def thetaCuspFirstAtomHighOrderUpperPolynomial64 (r j : ℕ) : ℝ[X] :=
  C (12.5663706143591729539 : ℝ) *
    (C ((j : ℝ) / 64) + X) ^ (2 * r) *
    thetaCuspFirstSourceTaylorUpper64 j *
    (C ((0.0432139182638 : ℝ) *
      thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 j) *
      thetaCuspFirstRateTaylorLocalUpperCertificate64 j)

theorem thetaCuspFirstAtomHighOrderLowerPolynomial64_eval_le_density
    {r j : ℕ} (hj : j < 64) {y : ℝ} (hy : 0 ≤ y) (hyh : y ≤ 1 / 64) :
    (thetaCuspFirstAtomHighOrderLowerPolynomial64 r j).eval y ≤
      2 * (((j : ℝ) / 64 + y) ^ (2 * r) *
        thetaCuspSourceTerm ((j : ℝ) / 64 + y) 1) := by
  let x : ℝ := (j : ℝ) / 64 + y
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hs := thetaCuspFirstSourceTaylorLower64_eval_le_actual j hy
  have hs0 := thetaCuspFirstSourceTaylorLower64_eval_nonneg j hy
  have hg := thetaCuspFirstGibbsTaylorLower64_le hj hy hyh
  have hg0 : 0 ≤
      (0.0432139182637 : ℝ) *
        thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
        (thetaCuspFirstRateTaylorLocalLowerCertificate64 j).eval y := by
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64_pos hj).le)
      (thetaCuspFirstRateTaylorLocalLowerCertificate64_eval_pos hj hy hyh).le
  have hactualG0 : 0 ≤ thetaCuspLiouvilleGibbsAtom 1 x := by
    rw [thetaCuspLiouvilleGibbsAtom_apply]
    positivity
  have hactualS0 : 0 ≤ 2 * Real.pi * Real.exp (2 * x) - 3 := hs0.trans hs
  have houter : (12.5663706143591729538 : ℝ) ≤ 4 * Real.pi := by
    nlinarith [Real.pi_gt_d20]
  rw [thetaCuspFirstAtomHighOrderLowerPolynomial64]
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X]
  change (12.5663706143591729538 : ℝ) * x ^ (2 * r) *
      (thetaCuspFirstSourceTaylorLower64 j).eval y *
      ((0.0432139182637 : ℝ) *
        thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
        (thetaCuspFirstRateTaylorLocalLowerCertificate64 j).eval y) ≤
    2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1)
  rw [thetaCuspSourceTerm_one_eq_liouvilleGibbs]
  calc
    (12.5663706143591729538 : ℝ) * x ^ (2 * r) *
          (thetaCuspFirstSourceTaylorLower64 j).eval y *
          ((0.0432139182637 : ℝ) *
            thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
            (thetaCuspFirstRateTaylorLocalLowerCertificate64 j).eval y) ≤
        (12.5663706143591729538 : ℝ) * x ^ (2 * r) *
          (thetaCuspFirstSourceTaylorLower64 j).eval y *
          thetaCuspLiouvilleGibbsAtom 1 x := by
      exact mul_le_mul_of_nonneg_left hg
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hx0 _)) hs0)
    _ ≤ (12.5663706143591729538 : ℝ) * x ^ (2 * r) *
          (2 * Real.pi * Real.exp (2 * x) - 3) *
          thetaCuspLiouvilleGibbsAtom 1 x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs
          (mul_nonneg (by norm_num) (pow_nonneg hx0 _))) hactualG0
    _ ≤ (4 * Real.pi) * x ^ (2 * r) *
          (2 * Real.pi * Real.exp (2 * x) - 3) *
          thetaCuspLiouvilleGibbsAtom 1 x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right houter (pow_nonneg hx0 _)) hactualS0)
        hactualG0
    _ = 2 * (x ^ (2 * r) *
          (2 * Real.pi * (2 * Real.pi * Real.exp (2 * x) - 3) *
            thetaCuspLiouvilleGibbsAtom 1 x)) := by ring

theorem thetaCuspFirstAtom_density_le_highOrderUpperPolynomial64_eval
    {r j : ℕ} (hj : j < 64) {y : ℝ} (hy : 0 ≤ y) (hyh : y ≤ 1 / 64) :
    2 * (((j : ℝ) / 64 + y) ^ (2 * r) *
        thetaCuspSourceTerm ((j : ℝ) / 64 + y) 1) ≤
      (thetaCuspFirstAtomHighOrderUpperPolynomial64 r j).eval y := by
  let x : ℝ := (j : ℝ) / 64 + y
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hs := actual_le_thetaCuspFirstSourceTaylorUpper64_eval j hy hyh
  have hactualS0 : 0 ≤ 2 * Real.pi * Real.exp (2 * x) - 3 := by
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by positivity)
    nlinarith [Real.pi_gt_d4]
  have hs0 : 0 ≤ (thetaCuspFirstSourceTaylorUpper64 j).eval y :=
    hactualS0.trans hs
  have hg := thetaCuspFirstGibbs_le_taylorUpper64 hj hy hyh
  have hactualG0 : 0 ≤ thetaCuspLiouvilleGibbsAtom 1 x := by
    rw [thetaCuspLiouvilleGibbsAtom_apply]
    positivity
  have hcertG0 : 0 ≤
      (0.0432139182638 : ℝ) *
        thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 j *
        (thetaCuspFirstRateTaylorLocalUpperCertificate64 j).eval y :=
    hactualG0.trans hg
  have houter : 4 * Real.pi ≤ (12.5663706143591729539 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  rw [thetaCuspFirstAtomHighOrderUpperPolynomial64]
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X]
  change 2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1) ≤
    (12.5663706143591729539 : ℝ) * x ^ (2 * r) *
      (thetaCuspFirstSourceTaylorUpper64 j).eval y *
      ((0.0432139182638 : ℝ) *
        thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 j *
        (thetaCuspFirstRateTaylorLocalUpperCertificate64 j).eval y)
  rw [thetaCuspSourceTerm_one_eq_liouvilleGibbs]
  calc
    2 * (x ^ (2 * r) *
          (2 * Real.pi * (2 * Real.pi * Real.exp (2 * x) - 3) *
            thetaCuspLiouvilleGibbsAtom 1 x)) =
        (4 * Real.pi) * x ^ (2 * r) *
          (2 * Real.pi * Real.exp (2 * x) - 3) *
          thetaCuspLiouvilleGibbsAtom 1 x := by ring
    _ ≤ (12.5663706143591729539 : ℝ) * x ^ (2 * r) *
          (2 * Real.pi * Real.exp (2 * x) - 3) *
          thetaCuspLiouvilleGibbsAtom 1 x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right houter (pow_nonneg hx0 _)) hactualS0)
        hactualG0
    _ ≤ (12.5663706143591729539 : ℝ) * x ^ (2 * r) *
          (thetaCuspFirstSourceTaylorUpper64 j).eval y *
          thetaCuspLiouvilleGibbsAtom 1 x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs
          (mul_nonneg (by norm_num) (pow_nonneg hx0 _))) hactualG0
    _ ≤ (12.5663706143591729539 : ℝ) * x ^ (2 * r) *
          (thetaCuspFirstSourceTaylorUpper64 j).eval y *
          ((0.0432139182638 : ℝ) *
            thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 j *
            (thetaCuspFirstRateTaylorLocalUpperCertificate64 j).eval y) := by
      exact mul_le_mul_of_nonneg_left hg
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hx0 _)) hs0)

theorem intervalIntegral_polynomial_eval_eq_realAntiderivative_eval
    (p : ℝ[X]) (a b : ℝ) :
    (∫ x in a..b, p.eval x) =
      (Polynomial.realAntiderivative p).eval b -
        (Polynomial.realAntiderivative p).eval a := by
  have h := Polynomial.eval_anchoredRealAntiderivative_eq_add_integral p a 0 b
  rw [Polynomial.anchoredRealAntiderivative] at h
  simp only [eval_add, eval_C, zero_add] at h
  linarith

def thetaCuspFirstAtomHighOrderLowerIntervalMass64 (r j : ℕ) : ℝ :=
  (Polynomial.realAntiderivative
      (thetaCuspFirstAtomHighOrderLowerPolynomial64 r j)).eval (1 / 64) -
    (Polynomial.realAntiderivative
      (thetaCuspFirstAtomHighOrderLowerPolynomial64 r j)).eval 0

def thetaCuspFirstAtomHighOrderUpperIntervalMass64 (r j : ℕ) : ℝ :=
  (Polynomial.realAntiderivative
      (thetaCuspFirstAtomHighOrderUpperPolynomial64 r j)).eval (1 / 64) -
    (Polynomial.realAntiderivative
      (thetaCuspFirstAtomHighOrderUpperPolynomial64 r j)).eval 0

theorem intervalIntegral_thetaCuspFirstAtomHighOrderLowerPolynomial64_eq_mass
    (r j : ℕ) :
    (∫ y in (0 : ℝ)..1 / 64,
      (thetaCuspFirstAtomHighOrderLowerPolynomial64 r j).eval y) =
      thetaCuspFirstAtomHighOrderLowerIntervalMass64 r j := by
  exact intervalIntegral_polynomial_eval_eq_realAntiderivative_eval _ _ _

theorem intervalIntegral_thetaCuspFirstAtomHighOrderUpperPolynomial64_eq_mass
    (r j : ℕ) :
    (∫ y in (0 : ℝ)..1 / 64,
      (thetaCuspFirstAtomHighOrderUpperPolynomial64 r j).eval y) =
      thetaCuspFirstAtomHighOrderUpperIntervalMass64 r j := by
  exact intervalIntegral_polynomial_eval_eq_realAntiderivative_eval _ _ _

theorem sum_firstAtomHighOrderLowerMass64_le_thetaCuspAtomRawEvenMoment
    (r : ℕ) :
    (∑ j ∈ Finset.range 64,
        thetaCuspFirstAtomHighOrderLowerIntervalMass64 r j) ≤
      thetaCuspAtomRawEvenMoment r 1 := by
  let f : ℝ → ℝ := fun x => 2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1)
  have hfcont : Continuous f := by
    dsimp only [f]
    unfold thetaCuspSourceTerm thetaCuspSeed
    fun_prop
  have hfint : IntegrableOn f (Ioi 0) := by
    have h := (integrableOn_pow_mul_thetaCuspSourceTerm r 1).const_mul 2
    apply h.congr
    filter_upwards [] with x
    dsimp only [f]
  have hfnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (by norm_num) <|
      mul_nonneg (pow_nonneg hx.le _) (thetaCuspSourceTerm_nonneg_of_pos hx 1)
  have hsegment (j : ℕ) (hj : j < 64) :
      thetaCuspFirstAtomHighOrderLowerIntervalMass64 r j ≤
        ∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x := by
    rw [← intervalIntegral_thetaCuspFirstAtomHighOrderLowerPolynomial64_eq_mass]
    calc
      (∫ y in (0 : ℝ)..1 / 64,
          (thetaCuspFirstAtomHighOrderLowerPolynomial64 r j).eval y) ≤
          ∫ y in (0 : ℝ)..1 / 64, f (y + (j : ℝ) / 64) := by
        apply intervalIntegral.integral_mono_on
        · norm_num
        · exact (Polynomial.continuous _).intervalIntegrable _ _
        · exact (hfcont.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
        · intro y hy
          simpa only [f, add_comm] using
            thetaCuspFirstAtomHighOrderLowerPolynomial64_eval_le_density
              hj hy.1 hy.2
      _ = ∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x := by
        rw [intervalIntegral.integral_comp_add_right]
        congr 2 <;> push_cast <;> ring
  have hsum :
      (∑ j ∈ Finset.range 64,
          thetaCuspFirstAtomHighOrderLowerIntervalMass64 r j) ≤
        ∑ j ∈ Finset.range 64,
          ∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x := by
    exact Finset.sum_le_sum fun j hj => hsegment j (Finset.mem_range.mp hj)
  have hjoin :
      (∑ j ∈ Finset.range 64,
          ∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x) =
        ∫ x in (0 : ℝ)..1, f x := by
    convert
      (intervalIntegral.sum_integral_adjacent_intervals
        (f := f) (a := fun k : ℕ => (k : ℝ) / 64) (n := 64) (μ := volume)
        (fun k _ => hfcont.intervalIntegrable _ _)) using 1 <;> norm_num
  have hwindow : (∫ x in (0 : ℝ)..1, f x) ≤ ∫ x in Ioi 0, f x := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    exact setIntegral_mono_set hfint hfnonneg
      (Filter.Eventually.of_forall fun x hx => hx.1)
  have hraw : (∫ x in Ioi 0, f x) = thetaCuspAtomRawEvenMoment r 1 := by
    rw [thetaCuspAtomRawEvenMoment]
    dsimp only [f]
    rw [← integral_const_mul]
  exact hsum.trans (hjoin.le.trans (hwindow.trans hraw.le))

theorem thetaCuspAtomRawEvenMoment_le_sum_firstAtomHighOrderUpperMass64_add_tail
    (r : ℕ) :
    thetaCuspAtomRawEvenMoment r 1 ≤
      (∑ j ∈ Finset.range 64,
        thetaCuspFirstAtomHighOrderUpperIntervalMass64 r j) +
      ∫ x in Ioi (1 : ℝ), 2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1) := by
  let f : ℝ → ℝ := fun x => 2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1)
  have hfcont : Continuous f := by
    dsimp only [f]
    unfold thetaCuspSourceTerm thetaCuspSeed
    fun_prop
  have hfint : IntegrableOn f (Ioi 0) := by
    have h := (integrableOn_pow_mul_thetaCuspSourceTerm r 1).const_mul 2
    apply h.congr
    filter_upwards [] with x
    dsimp only [f]
  have hsegment (j : ℕ) (hj : j < 64) :
      (∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x) ≤
        thetaCuspFirstAtomHighOrderUpperIntervalMass64 r j := by
    rw [← intervalIntegral_thetaCuspFirstAtomHighOrderUpperPolynomial64_eq_mass]
    calc
      (∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x) =
          ∫ y in (0 : ℝ)..1 / 64, f (y + (j : ℝ) / 64) := by
        rw [intervalIntegral.integral_comp_add_right]
        congr 2 <;> push_cast <;> ring
      _ ≤ ∫ y in (0 : ℝ)..1 / 64,
          (thetaCuspFirstAtomHighOrderUpperPolynomial64 r j).eval y := by
        apply intervalIntegral.integral_mono_on
        · norm_num
        · exact (hfcont.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
        · exact (Polynomial.continuous _).intervalIntegrable _ _
        · intro y hy
          simpa only [f, add_comm] using
            thetaCuspFirstAtom_density_le_highOrderUpperPolynomial64_eval
              hj hy.1 hy.2
  have hsum :
      (∑ j ∈ Finset.range 64,
          ∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x) ≤
        ∑ j ∈ Finset.range 64,
          thetaCuspFirstAtomHighOrderUpperIntervalMass64 r j := by
    exact Finset.sum_le_sum fun j hj => hsegment j (Finset.mem_range.mp hj)
  have hjoin :
      (∑ j ∈ Finset.range 64,
          ∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64), f x) =
        ∫ x in (0 : ℝ)..1, f x := by
    convert
      (intervalIntegral.sum_integral_adjacent_intervals
        (f := f) (a := fun k : ℕ => (k : ℝ) / 64) (n := 64) (μ := volume)
        (fun k _ => hfcont.intervalIntegrable _ _)) using 1 <;> norm_num
  have hsplit : (∫ x in Ioi (0 : ℝ), f x) =
      (∫ x in (0 : ℝ)..1, f x) + ∫ x in Ioi (1 : ℝ), f x :=
    GaloisForLFunctions.RHTower.integral_Ioi_eq_intervalIntegral_add_tail
      (by norm_num) hfint
  have hraw : (∫ x in Ioi 0, f x) = thetaCuspAtomRawEvenMoment r 1 := by
    rw [thetaCuspAtomRawEvenMoment]
    dsimp only [f]
    rw [← integral_const_mul]
  rw [← hraw, hsplit]
  simpa only [f] using add_le_add (hjoin ▸ hsum)
    (le_refl (∫ x in Ioi (1 : ℝ), f x))

theorem twentyThree_lt_pi_mul_exp_two :
    (23 : ℝ) < Real.pi * Real.exp 2 := by
  have he : (331 / 45 : ℝ) ≤ Real.exp 2 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 7
    norm_num [Finset.sum_range_succ] at h ⊢
    exact h
  have hpi := Real.pi_gt_d20
  have h1 : (3.14159265358979323846 : ℝ) * (331 / 45) <
      Real.pi * (331 / 45) := by gcongr
  have h2 : Real.pi * (331 / 45) ≤ Real.pi * Real.exp 2 := by gcongr
  have h23 : (23 : ℝ) < (3.14159265358979323846 : ℝ) * (331 / 45) := by
    norm_num
  exact h23.trans (h1.trans_le h2)

theorem thetaCuspFirstAtom_tail_density_le_exp_majorant
    {r : ℕ} (hr : r ≤ 3) {x : ℝ} (hx : 1 ≤ x) :
    2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1) ≤
      79 * Real.exp (-37 / 2) * Real.exp (-(71 / 2) * (x - 1)) := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hxshift : 0 ≤ x - 1 := sub_nonneg.mpr hx
  have hxexp : x ≤ Real.exp (x - 1) := by
    nlinarith [Real.add_one_le_exp (x - 1)]
  have hrNat : 2 * r ≤ 6 := by omega
  have hrReal : ((2 * r : ℕ) : ℝ) ≤ 6 := by exact_mod_cast hrNat
  have hxpow : x ^ (2 * r) ≤ Real.exp (6 * (x - 1)) := by
    calc
      x ^ (2 * r) ≤ Real.exp (x - 1) ^ (2 * r) :=
        pow_le_pow_left₀ hx0 hxexp _
      _ = Real.exp (((2 * r : ℕ) : ℝ) * (x - 1)) := by
        rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (6 * (x - 1)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right hrReal hxshift
  have hdouble : 46 * x - 23 ≤ Real.pi * Real.exp (2 * x) := by
    have hconvex : 1 + 2 * (x - 1) ≤ Real.exp (2 * (x - 1)) :=
      by simpa [add_comm] using Real.add_one_le_exp (2 * (x - 1))
    calc
      46 * x - 23 = 23 * (1 + 2 * (x - 1)) := by ring
      _ ≤ (Real.pi * Real.exp 2) * Real.exp (2 * (x - 1)) := by
        exact mul_le_mul twentyThree_lt_pi_mul_exp_two.le hconvex
          (by nlinarith) (by positivity)
      _ = Real.pi * Real.exp (2 * x) := by
        rw [show Real.pi * Real.exp 2 * Real.exp (2 * (x - 1)) =
          Real.pi * (Real.exp 2 * Real.exp (2 * (x - 1))) by ring,
          ← Real.exp_add]
        congr 1
        ring
  have hpiCoeff : 8 * Real.pi ^ 2 ≤ (79 : ℝ) := by
    nlinarith [Real.pi_pos, Real.pi_lt_d20]
  have hsource := HedenmalmThetaSource.thetaCuspSourceTerm_one_le x
  have henv0 := (HedenmalmThetaSource.thetaEnvelope_pos x).le
  calc
    2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1) ≤
        2 * (x ^ (2 * r) *
          (4 * Real.pi ^ 2 * HedenmalmThetaSource.thetaEnvelope x)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsource (pow_nonneg hx0 _)) (by norm_num)
    _ = 8 * Real.pi ^ 2 * (x ^ (2 * r) *
          HedenmalmThetaSource.thetaEnvelope x) := by ring
    _ ≤ 79 * (x ^ (2 * r) * HedenmalmThetaSource.thetaEnvelope x) := by
      exact mul_le_mul_of_nonneg_right hpiCoeff
        (mul_nonneg (pow_nonneg hx0 _) henv0)
    _ ≤ 79 * (Real.exp (6 * (x - 1)) *
          HedenmalmThetaSource.thetaEnvelope x) := by
      gcongr
    _ = 79 * Real.exp
          (6 * (x - 1) + 9 * x / 2 - Real.pi * Real.exp (2 * x)) := by
      rw [HedenmalmThetaSource.thetaEnvelope, ← Real.exp_add, ← Real.exp_add]
      ring
    _ ≤ 79 * Real.exp (-37 / 2 - (71 / 2) * (x - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.exp_le_exp.mpr (by nlinarith [hdouble])
    _ = 79 * Real.exp (-37 / 2) * Real.exp (-(71 / 2) * (x - 1)) := by
      rw [show -37 / 2 - (71 / 2) * (x - 1) =
        -37 / 2 + (-(71 / 2) * (x - 1)) by ring, Real.exp_add]
      ring

theorem ninetyMillion_lt_exp_thirtySeven_div_two :
    (90000000 : ℝ) < Real.exp (37 / 2) := by
  have heOne : (685 / 252 : ℝ) ≤ Real.exp 1 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 8
    norm_num [Finset.sum_range_succ] at h ⊢
    exact h
  have heHalf : (79 / 48 : ℝ) ≤ Real.exp (1 / 2) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) 4
    norm_num [Finset.sum_range_succ] at h ⊢
    exact h
  have hePow : (685 / 252 : ℝ) ^ 18 ≤ Real.exp 1 ^ 18 :=
    pow_le_pow_left₀ (by norm_num) heOne 18
  have hprod : (685 / 252 : ℝ) ^ 18 * (79 / 48) ≤
      Real.exp 1 ^ 18 * Real.exp (1 / 2) := by
    exact mul_le_mul hePow heHalf (by positivity) (by positivity)
  have hrat : (90000000 : ℝ) < (685 / 252 : ℝ) ^ 18 * (79 / 48) := by
    norm_num
  calc
    (90000000 : ℝ) < (685 / 252 : ℝ) ^ 18 * (79 / 48) := hrat
    _ ≤ Real.exp 1 ^ 18 * Real.exp (1 / 2) := hprod
    _ = Real.exp (37 / 2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      norm_num

theorem exp_neg_thirtySeven_div_two_lt_one_div_ninetyMillion :
    Real.exp (-37 / 2) < (1 / 90000000 : ℝ) := by
  rw [show (-37 / 2 : ℝ) = -(37 / 2) by ring, Real.exp_neg]
  simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num)
    ninetyMillion_lt_exp_thirtySeven_div_two

theorem thetaCuspFirstAtom_tail_evenMoment_lt_one_div_fortyMillion
    {r : ℕ} (hr : r ≤ 3) :
    (∫ x in Ioi (1 : ℝ),
      2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1)) <
      (1 / 40000000 : ℝ) := by
  let f : ℝ → ℝ := fun x => 2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1)
  let g : ℝ → ℝ := fun x =>
    79 * Real.exp (-37 / 2) * Real.exp (-(71 / 2) * (x - 1))
  have hfint : IntegrableOn f (Ioi (1 : ℝ)) := by
    have hzero : IntegrableOn f (Ioi (0 : ℝ)) := by
      have h := (integrableOn_pow_mul_thetaCuspSourceTerm r 1).const_mul 2
      apply h.congr
      filter_upwards [] with x
      dsimp only [f]
    exact hzero.mono_set (show Ioi (1 : ℝ) ⊆ Ioi 0 by
      intro x hx
      change (1 : ℝ) < x at hx
      exact zero_lt_one.trans hx)
  have hgint : IntegrableOn g (Ioi (1 : ℝ)) := by
    exact (HedenmalmThetaSource.integrableOn_exp_neg_shift
      (x := (1 : ℝ)) (a := (71 / 2 : ℝ)) (by norm_num)).const_mul
        (79 * Real.exp (-37 / 2))
  have hmono : (∫ x in Ioi (1 : ℝ), f x) ≤ ∫ x in Ioi (1 : ℝ), g x := by
    apply MeasureTheory.integral_mono_ae hfint hgint
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact thetaCuspFirstAtom_tail_density_le_exp_majorant hr hx.le
  have hgeval : (∫ x in Ioi (1 : ℝ), g x) =
      (158 / 71 : ℝ) * Real.exp (-37 / 2) := by
    rw [show g = fun x : ℝ =>
        (79 * Real.exp (-37 / 2)) *
          Real.exp (-(71 / 2) * (x - 1)) by rfl,
      integral_const_mul,
      HedenmalmThetaSource.integral_Ioi_exp_neg_shift (by norm_num)]
    ring
  have hnumeric : (158 / 71 : ℝ) * Real.exp (-37 / 2) <
      (1 / 40000000 : ℝ) := by
    calc
      (158 / 71 : ℝ) * Real.exp (-37 / 2) <
          (158 / 71 : ℝ) * (1 / 90000000) :=
        mul_lt_mul_of_pos_left
          exp_neg_thirtySeven_div_two_lt_one_div_ninetyMillion (by norm_num)
      _ < (1 / 40000000 : ℝ) := by norm_num
  exact hmono.trans_lt (hgeval ▸ hnumeric)

end

end RHTower
