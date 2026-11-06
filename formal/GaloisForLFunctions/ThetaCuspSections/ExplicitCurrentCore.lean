import GaloisForLFunctions.ThetaCuspSections.ExplicitCurrentTail
import GaloisForLFunctions.VerifiedHeightRungs.ThetaEntries
import GaloisForLFunctions.VerifiedHeightRungs.LiAndHausdorffEntries
import GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget.TheVerifiedHeightSixtySeven
import GaloisForLFunctions.RHTower.WeilDeletionZeroSide
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewCesaroLandauRecurrence
import GaloisForLFunctions.RHTower.EulerMascheroniCorrectedUpper
import GaloisForLFunctions.RHTower.HarmonicGeometricBounds
import GaloisForLFunctions.RHTower.XiLaguerrePolya
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstMoment

/-!
# An explicit core for the current

**Theorem** (`current_ge_of_abs_le`). For `0 < a ≤ ½` and `|b| ≤ 5`, `current a b ≥ 6·10⁻⁴ a`.

The current is `2 |Ξ(z)|² Re ξ'/ξ(½ + a + ib)`, `z = b − ia`.

* **`Re ξ'/ξ`.** All zeros below height `67` are on the line, and each zero contributes at least
  `(9/20) a Re 1/(ρ(1−ρ))` to `2 Re ξ'/ξ`. Their sum is the exact constant `2 + γ − log 4π`.
* **`|Ξ(z)|`.** The current is the `a`-derivative of `|Ξ(b − ia)|²`, so `|Ξ(z)| ≥ |Ξ(b)|`.
  On the line, `cos(bx) ≥ 1 − b²x²/2` against the positive source gives
  `Ξ(b) ≥ Ξ(0)(1 − (b²/2) Σ_ρ 1/|ρ−½|²)`, and `Ξ(0) ≥ 0.49` follows from the theta tail.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.ThetaCuspSections.ExplicitCollar

open _root_.RHTower CriticalCollar QuantitativeCollar LogarithmicCollar
open GaloisForLFunctions.VerifiedHeightRungs GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget

/-! ## Constants -/

private theorem gamma_lower : (5772 / 10000 : ℝ) ≤ Real.eulerMascheroniConstant := by
  have h := (harmonic_mascheroni_geometric_bounds (n := 16) (by norm_num)).2
  have hl := log_le_geometric_cubic (x := (17 / 16 : ℝ)) (by norm_num)
  have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [Real.log_div (by norm_num) (by norm_num), h16] at hl
  norm_num [harmonic, Finset.sum_range_succ, h16] at h hl
  linarith only [h, hl, Real.log_two_lt_d9]

private theorem le_log_pi : (1.1444 : ℝ) ≤ Real.log Real.pi := by
  have hpow : (2 : ℝ) ^ 71 ≤ Real.pi ^ 43 := by
    have hπ := Real.pi_gt_d4
    calc (2 : ℝ) ^ 71 ≤ 3.1415 ^ 43 := by norm_num
      _ ≤ Real.pi ^ 43 := pow_le_pow_left₀ (by norm_num) hπ.le 43
  have hl := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hl
  have h2 := Real.log_two_gt_d9
  norm_num at hl ⊢
  linarith only [hl, h2]

private theorem log_pi_le : Real.log Real.pi ≤ 1.1453 := by
  have hpow : Real.pi ^ 23 ≤ (2 : ℝ) ^ 38 := by
    have hπ := Real.pi_lt_d4
    calc Real.pi ^ 23 ≤ 3.1416 ^ 23 := pow_le_pow_left₀ Real.pi_pos.le hπ.le 23
      _ ≤ (2 : ℝ) ^ 38 := by norm_num
  have hl := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hl
  have h2 := Real.log_two_lt_d9
  norm_num at hl ⊢
  linarith only [hl, h2]

private theorem log_four_pi : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
  rw [Real.log_mul (by norm_num) Real.pi_ne_zero, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num

/-- The lower bound of the zero sum. -/
theorem le_poleSharpConstant : (0.0456 : ℝ) ≤ poleSharpConstant := by
  unfold poleSharpConstant
  rw [log_four_pi]
  have h1 := gamma_lower
  have h2 := log_pi_le
  have h3 := Real.log_two_lt_d9
  norm_num at h1 h2 h3 ⊢
  linarith only [h1, h2, h3]

/-- The upper bound of the zero sum. -/
theorem poleSharpConstant_le : poleSharpConstant ≤ 0.0466 := by
  unfold poleSharpConstant
  rw [log_four_pi]
  have h1 := eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  have h2 := le_log_pi
  have h3 := Real.log_two_gt_d9
  norm_num at h1 h2 h3 ⊢
  linarith only [h1, h2, h3]

/-! ## The value at the centre -/

private theorem exp_neg_pi_le : Real.exp (-Real.pi) ≤ 1 / 20 := by
  have h3 : (20 : ℝ) ≤ Real.exp 3 := by
    have h : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h]
    calc (20 : ℝ) ≤ 2.7182818283 ^ 3 := by norm_num
      _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 3
  have hπ : Real.exp 3 ≤ Real.exp Real.pi := Real.exp_le_exp.mpr Real.pi_gt_three.le
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by norm_num) (h3.trans hπ)

/-- The theta tail on the positive half-line. -/
theorem tail_zero_le {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspTailDerivative 0 x ≤ 1 / 19 * Real.exp (-(57 / 10 * x)) := by
  obtain ⟨r, hr⟩ : ∃ r, r = Real.exp (-Real.pi) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact Real.exp_pos _
  have hr1 : r ≤ 1 / 20 := by rw [hr]; exact exp_neg_pi_le
  have hgeo : HasSum (fun n : ℕ => r ^ n) (1 - r)⁻¹ :=
    hasSum_geometric_of_lt_one hr0.le (by linarith only [hr1])
  have hterm (n : ℕ) : thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 0) (n + 1) x ≤
      (r * r ^ n) * Real.exp (-(57 / 10 * x)) := by
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith only [this]
    have hE : 1 + 2 * x ≤ Real.exp x ^ 2 := by
      rw [← Real.exp_nat_mul]
      have := Real.add_one_le_exp (((2 : ℕ) : ℝ) * x)
      push_cast at this ⊢
      linarith only [this]
    have hbig : (n : ℝ) + 1 + 2 * x ≤ (((n + 1 : ℕ) : ℝ) * Real.exp x) ^ 2 := by
      push_cast
      rw [mul_pow]
      have h1 : ((n : ℝ) + 1) * 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith only [hn]
      have h2 : ((n : ℝ) + 1) ^ 2 * (1 + 2 * x) ≤ ((n : ℝ) + 1) ^ 2 * Real.exp x ^ 2 :=
        mul_le_mul_of_nonneg_left hE (by positivity)
      have h3 : 1 * (2 * x) ≤ ((n : ℝ) + 1) ^ 2 * (2 * x) :=
        mul_le_mul_of_nonneg_right (by nlinarith only [hn]) (by positivity)
      nlinarith only [h1, h2, h3]
    have hrn : r * r ^ n = Real.exp (-Real.pi * ((n : ℝ) + 1)) := by
      rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    unfold thetaCuspPolynomialAtom
    simp only [thetaCuspTailDerivativePolynomial, Polynomial.eval_one, mul_one]
    rw [hrn, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hπ := Real.pi_gt_d2
    have h1 := mul_le_mul_of_nonneg_left hbig Real.pi_pos.le
    have h2 : (5.78 : ℝ) * x ≤ (2 * Real.pi - 1 / 2) * x :=
      mul_le_mul_of_nonneg_right (by norm_num at hπ ⊢; linarith only [hπ]) hx
    norm_num at h2
    nlinarith only [h1, h2, hx]
  have hS : Summable fun n : ℕ => (r * r ^ n) * Real.exp (-(57 / 10 * x)) :=
    (hgeo.summable.mul_left r).mul_right _
  have hval : ∑' n : ℕ, (r * r ^ n) * Real.exp (-(57 / 10 * x)) =
      r * (1 - r)⁻¹ * Real.exp (-(57 / 10 * x)) := by
    rw [tsum_mul_right, tsum_mul_left, hgeo.tsum_eq]
  unfold thetaCuspTailDerivative
  refine ((summable_thetaCuspTailDerivative 0 x).tsum_le_tsum hterm hS).trans ?_
  rw [hval]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  have h1r : 0 < 1 - r := by linarith only [hr1]
  rw [← div_eq_mul_inv, div_le_iff₀ h1r]
  linarith only [hr1]

/-- `Ξ(0) ≥ 0.49`. -/
theorem Xi_zero_ge : (0.49 : ℝ) ≤ Xi 0 := by
  rw [Xi_zero_eq_two_mul_integral_thetaCuspFullSource]
  have h := integral_Ioi_thetaCuspFullSource_mul_cos 0
  simp only [zero_mul, Real.cos_zero, mul_one] at h
  rw [h]
  have hmaj : IntegrableOn (fun x : ℝ => 1 / 19 * Real.exp (-(57 / 10) * x)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (a := -(57 / 10)) (by norm_num) 0).const_mul _
  have hle : ∫ x in Ioi (0 : ℝ), thetaCuspTailDerivative 0 x ≤
      ∫ x in Ioi (0 : ℝ), 1 / 19 * Real.exp (-(57 / 10) * x) := by
    refine setIntegral_mono_on (integrableOn_thetaCuspTailDerivative_Ioi 0) hmaj measurableSet_Ioi
      fun x hx => ?_
    have h1 := tail_zero_le (le_of_lt hx)
    rwa [show -(57 / 10 * x) = -(57 / 10) * x by ring] at h1
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num) 0] at hle
  norm_num at hle ⊢
  linarith only [hle]

/-! ## The value on the real line -/

/-- The second moment of the source is half the zero sum, times `Ξ(0)`. -/
theorem second_moment_le :
    ∫ x in Ioi (0 : ℝ), x ^ 2 * thetaCuspFullSource x ≤
      Xi 0 / 2 * (11 / 10 * poleSharpConstant) := by
  have h2 := Xi_secondDeriv_zero_eq_neg_two_mul_thetaCuspSecondMoment
  have h3 := Xi_secondDeriv_eq_center_mul_canonicalProduct_re 0
  have h4 := secondDeriv_xiCanonicalProduct_zero
  rw [Complex.ofReal_zero, h4, Complex.neg_re] at h3
  have hX := Xi_zero_pos
  have hnorm : ∀ q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ =
      1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := fun q => by
    rw [xiZeroCopyReciprocalSquare, norm_pow, norm_inv, one_div, inv_pow]
  have hsum : Summable fun q : XiZeroCopy => ‖xiZeroCopyReciprocalSquare q‖ := by
    simp_rw [hnorm]
    exact xiSpectralPoint_inv_sq_summable
  have hre : (∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q).re ≤
      11 / 10 * poleSharpConstant := by
    refine (Complex.re_le_norm _).trans ((norm_tsum_le_tsum_norm hsum).trans ?_)
    simp_rw [hnorm]
    exact WeilDeletion.tsum_inv_normSq_spectralPoint_le
  have h5 : 2 * ∫ x in Ioi (0 : ℝ), x ^ 2 * thetaCuspFullSource x =
      Xi 0 * (∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q).re := by
    linarith only [h2, h3]
  have h6 := mul_le_mul_of_nonneg_left hre hX.le
  linarith only [h5, h6]

/-- `Ξ(b) ≥ 0.176` for `|b| ≤ 5`. -/
theorem Xi_ge_of_abs_le {b : ℝ} (hb : |b| ≤ 5) : (0.176 : ℝ) ≤ Xi b := by
  rw [Xi_eq_thetaCuspCosineRepresentation b]
  unfold thetaCuspCosineRepresentation
  have hsrc : IntegrableOn thetaCuspFullSource (Ioi 0) :=
    integrable_thetaCuspFullSource'.integrableOn
  have hsec : IntegrableOn (fun x : ℝ => x ^ 2 * thetaCuspFullSource x) (Ioi 0) :=
    integrable_thetaCuspSecondMoment.integrableOn
  have hcos : IntegrableOn (fun x : ℝ => thetaCuspFullSource x * Real.cos (b * x)) (Ioi 0) := by
    refine Integrable.mul_bdd (c := 1) hsrc (by fun_prop) (ae_of_all _ fun x => ?_)
    simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (b * x)
  have hmono : ∫ x in Ioi (0 : ℝ), (thetaCuspFullSource x - b ^ 2 / 2 *
      (x ^ 2 * thetaCuspFullSource x)) ≤
      ∫ x in Ioi (0 : ℝ), thetaCuspFullSource x * Real.cos (b * x) := by
    refine setIntegral_mono_on (hsrc.sub (hsec.const_mul _)) hcos measurableSet_Ioi fun x _ => ?_
    have hc := Real.one_sub_sq_div_two_le_cos (x := b * x)
    have hp := (thetaCuspFullSource_pos x).le
    have := mul_le_mul_of_nonneg_left hc hp
    nlinarith only [this]
  rw [integral_sub hsrc (hsec.const_mul _), integral_const_mul] at hmono
  have hX0 := Xi_zero_eq_two_mul_integral_thetaCuspFullSource
  have hsecle := second_moment_le
  have hsq : b ^ 2 ≤ 25 := by
    rw [← sq_abs]
    nlinarith only [hb, abs_nonneg b]
  have hP := poleSharpConstant_le
  have hP0 := le_poleSharpConstant
  have hXg := Xi_zero_ge
  obtain ⟨S, hS⟩ : ∃ S, S = ∫ x in Ioi (0 : ℝ), x ^ 2 * thetaCuspFullSource x := ⟨_, rfl⟩
  obtain ⟨I₀, hI₀⟩ : ∃ I₀, I₀ = ∫ x in Ioi (0 : ℝ), thetaCuspFullSource x := ⟨_, rfl⟩
  rw [← hS, ← hI₀] at hmono
  rw [← hS] at hsecle
  rw [← hI₀] at hX0
  have hS0 : 0 ≤ S := by rw [hS]; exact integral_Ioi_thetaCuspSecondMoment_pos.le
  have h1 : b ^ 2 / 2 * S ≤ 25 / 2 * (Xi 0 / 2 * (11 / 10 * 0.0466)) := by
    have h2 : S ≤ Xi 0 / 2 * (11 / 10 * 0.0466) := by
      refine hsecle.trans (mul_le_mul_of_nonneg_left ?_ (by linarith only [hXg]))
      linarith only [hP]
    exact mul_le_mul (by linarith only [hsq]) h2 hS0 (by norm_num)
  norm_num at h1 hXg ⊢
  linarith only [hmono, hX0, h1, hXg]

/-! ## The modulus off the line -/

/-- The current is the aperture derivative of `|Ξ(b − ia)|²`. -/
theorem hasDerivAt_normSq_XiC (a b : ℝ) :
    HasDerivAt (fun a' : ℝ => Complex.normSq (XiC ((b : ℂ) - (a' : ℂ) * I))) (current a b) a := by
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = (b : ℂ) - (a : ℂ) * I := ⟨_, rfl⟩
  have hinner : HasDerivAt (fun y : ℂ => (b : ℂ) - y * I) (-I) (a : ℂ) := by
    simpa using ((hasDerivAt_id (a : ℂ)).mul_const I).const_sub (b : ℂ)
  have hout : HasDerivAt XiC (deriv XiC z) ((b : ℂ) - (a : ℂ) * I) := by
    rw [← hz]
    exact (XiC_differentiable z).hasDerivAt
  have hcomp : HasDerivAt (fun y : ℂ => XiC ((b : ℂ) - y * I)) (deriv XiC z * -I) (a : ℂ) := by
    have := HasDerivAt.comp (h₂ := XiC) (h := fun y : ℂ => (b : ℂ) - y * I) (a : ℂ) hout hinner
    exact this
  have hreal : HasDerivAt (fun a' : ℝ => XiC ((b : ℂ) - (a' : ℂ) * I)) (deriv XiC z * -I) a :=
    hcomp.comp_ofReal
  obtain ⟨g', hg'⟩ : ∃ g', g' = deriv XiC z * -I := ⟨_, rfl⟩
  rw [← hg'] at hreal
  have hre : HasDerivAt (fun a' : ℝ => (XiC ((b : ℂ) - (a' : ℂ) * I)).re) g'.re a :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt a hreal
  have him : HasDerivAt (fun a' : ℝ => (XiC ((b : ℂ) - (a' : ℂ) * I)).im) g'.im a :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt a hreal
  have hsum := (hre.mul hre).add (him.mul him)
  have hcur : current a b = 2 * ((starRingEnd ℂ) (XiC z) * (-I * deriv XiC z)).re := by
    rw [hz]
    rfl
  rw [hcur, show -I * deriv XiC z = g' by rw [hg']; ring]
  refine (hsum.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun a' => ?_)
  · rw [← hz]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  · simp [Complex.normSq_apply]

/-- `|Ξ(b − ia)|² ≥ Ξ(b)²` while the current is nonnegative. -/
theorem sq_Xi_le_normSq {a b : ℝ} (ha : 0 ≤ a) (hnn : ∀ a' ∈ Ioo 0 a, 0 ≤ current a' b) :
    Xi b ^ 2 ≤ Complex.normSq (XiC ((b : ℂ) - (a : ℂ) * I)) := by
  let F : ℝ → ℝ := fun a' => Complex.normSq (XiC ((b : ℂ) - (a' : ℂ) * I))
  have hderiv (a' : ℝ) : HasDerivAt F (current a' b) a' := hasDerivAt_normSq_XiC a' b
  have hmono : MonotoneOn F (Icc 0 a) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 a)
      (fun a' _ => (hderiv a').continuousAt.continuousWithinAt)
      (fun a' _ => (hderiv a').differentiableAt.differentiableWithinAt) fun a' ha' => ?_
    rw [(hderiv a').deriv]
    rw [interior_Icc] at ha'
    exact hnn a' ha'
  have h := hmono (left_mem_Icc.mpr ha) (right_mem_Icc.mpr ha) ha
  have hF0 : F 0 = Xi b ^ 2 := by
    simp only [F, Complex.ofReal_zero, zero_mul, sub_zero]
    rw [XiC_ofReal, Complex.normSq_ofReal]
    ring
  rwa [hF0] at h

/-! ## The logarithmic derivative -/

/-- Every zero contributes to the pair sum at least its share of `2 + γ − log 4π`. -/
theorem pair_floor {a b : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hb : |b| ≤ 5) (q : XiZeroCopy) :
    9 / 20 * a * ((1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re ≤
      xiLinePairRe a ((q.1 : ℂ).re - 1 / 2) (b - (q.1 : ℂ).im) := by
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = (q.1 : ℂ).re - 1 / 2 := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = (q.1 : ℂ).im := ⟨_, rfl⟩
  rw [← hδ, ← hγ]
  have hδ1 : δ ^ 2 < 1 / 4 := by
    rw [hδ]
    exact xi_divisor_support_centered_re_sq_lt_quarter q.1
  have hγ2 : 41 / 2 < γ ^ 2 := by
    rw [hγ]
    exact xiZeroCopy_fortyOne_div_two_lt_im_sq q
  -- The zero sum term.
  have hρ : (q.1 : ℂ) * (1 - (q.1 : ℂ)) = ((1 / 4 - δ ^ 2 + γ ^ 2 : ℝ) : ℂ) +
      ((-(2 * δ * γ) : ℝ) : ℂ) * I := by
    have hq : (q.1 : ℂ) = ((1 / 2 + δ : ℝ) : ℂ) + (γ : ℂ) * I := by
      apply Complex.ext
      · simp [hδ]
      · simp [hγ]
    rw [hq]
    push_cast
    ring_nf
    rw [I_sq]
    ring
  obtain ⟨A, hA⟩ : ∃ A, A = 1 / 4 - δ ^ 2 + γ ^ 2 := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; nlinarith only [hδ1, hγ2]
  have hr : ((1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re ≤ 1 / A := by
    rw [hρ, one_div, Complex.inv_re, Complex.normSq_apply, ← hA]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im,
      zero_add, sub_zero, zero_mul]
    rw [div_le_div_iff₀ (by nlinarith only [hA0, mul_self_nonneg (2 * δ * γ)]) hA0]
    nlinarith only [mul_self_nonneg (2 * δ * γ)]
  -- The pair.
  obtain ⟨u, hu⟩ : ∃ u, u = b - γ := ⟨_, rfl⟩
  rw [← hu]
  have habsu : |u| ≤ |γ| + 5 := by
    rw [hu]
    have := abs_sub b γ
    linarith only [this, hb]
  have hu2 : u ^ 2 ≤ γ ^ 2 + 10 * |γ| + 25 := by
    rw [← sq_abs u]
    have h1 := pow_le_pow_left₀ (abs_nonneg u) habsu 2
    have h2 := sq_abs γ
    nlinarith only [h1, h2]
  have hgabs : (4.5 : ℝ) < |γ| := by
    have h2 := sq_abs γ
    have h3 := abs_nonneg γ
    by_contra hc
    nlinarith only [not_lt.1 hc, h2, h3, hγ2]
  have hgoal : 9 / 20 * a * (1 / A) ≤ xiLinePairRe a δ u := by
    unfold xiLinePairRe
    by_cases hoff : δ = 0
    · subst hoff
      simp only [sub_zero, add_zero]
      have hD : 0 < a ^ 2 + u ^ 2 := by positivity
      have hA' : A = 1 / 4 + γ ^ 2 := by rw [hA]; ring
      have e : a / (a ^ 2 + u ^ 2) + a / (a ^ 2 + u ^ 2) = 2 * a / (a ^ 2 + u ^ 2) := by ring
      rw [e, show 9 / 20 * a * (1 / A) = 9 / 20 * a / A by ring,
        div_le_div_iff₀ hA0 hD]
      have hkey : 9 / 20 * (a ^ 2 + u ^ 2) ≤ 2 * A := by
        rw [hA']
        nlinarith only [hu2, hgabs, ha2, ha, sq_abs γ, abs_nonneg γ]
      nlinarith only [mul_le_mul_of_nonneg_left hkey ha.le]
    · -- Off the line the zero is far above the window.
      have hqoff : (q.1 : ℂ).re ≠ 1 / 2 := by
        intro h
        apply hoff
        rw [hδ, h]
        ring
      have hfar : (67 : ℝ) < |γ| := by
        have hzero : xi (q.1 : ℂ) = 0 := xi_xiZeroCopy_eq_zero q
        rw [hγ]
        exact lt_abs_im_of_rhVerifiedThrough rhVerifiedThrough_sixtySeven hzero
          (xiZeroCopy_re_pos q) (xiZeroCopy_re_lt_one q) hqoff
      have habslow : |γ| - 5 ≤ |u| := by
        rw [hu]
        have := abs_sub_abs_le_abs_sub γ b
        rw [abs_sub_comm γ b] at this
        linarith only [this, hb]
      have hX : (62 : ℝ) ^ 2 ≤ u ^ 2 := by
        rw [← sq_abs u]
        exact pow_le_pow_left₀ (by norm_num) (by linarith only [habslow, hfar]) 2
      have hδabs : |δ| ≤ 1 / 2 := by
        rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]
        linarith only [hδ1]
      obtain ⟨hδa, hδb⟩ := abs_le.mp hδabs
      have h1 : (a - δ) ^ 2 ≤ 1 := by nlinarith only [ha, ha2, hδa, hδb]
      have h2 : (a + δ) ^ 2 ≤ 1 := by nlinarith only [ha, ha2, hδa, hδb]
      obtain ⟨X, hXdef⟩ : ∃ X, X = u ^ 2 := ⟨_, rfl⟩
      rw [← hXdef] at hX hu2 ⊢
      norm_num at hX
      have hD1 : 0 < (a - δ) ^ 2 + X := by positivity
      have hD2 : 0 < (a + δ) ^ 2 + X := by positivity
      rw [div_add_div _ _ hD1.ne' hD2.ne', show 9 / 20 * a * (1 / A) = 9 / 20 * a / A by ring,
        div_le_div_iff₀ hA0 (mul_pos hD1 hD2)]
      have hnum : (a - δ) * ((a + δ) ^ 2 + X) + ((a - δ) ^ 2 + X) * (a + δ) =
          2 * a * (a ^ 2 - δ ^ 2 + X) := by ring
      rw [hnum]
      have hprod : ((a - δ) ^ 2 + X) * ((a + δ) ^ 2 + X) ≤ (1 + X) ^ 2 := by
        nlinarith only [h1, h2, hD1, hD2]
      have hA2 : γ ^ 2 ≤ A := by rw [hA]; linarith only [hδ1]
      have hnum2 : X - 1 / 4 ≤ a ^ 2 - δ ^ 2 + X := by nlinarith only [hδ1, sq_nonneg a]
      have hgX : X ≤ 2 * γ ^ 2 := by
        have h3 := sq_abs γ
        nlinarith only [hu2, hfar, h3]
      have hmain : 9 / 20 * (1 + X) ^ 2 ≤ 2 * (X - 1 / 4) * γ ^ 2 := by
        nlinarith only [hgX, hX, mul_nonneg (by linarith only [hX] : (0 : ℝ) ≤ X)
          (by linarith only [hgX] : (0 : ℝ) ≤ 2 * γ ^ 2 - X)]
      have hX4 : 0 ≤ X - 1 / 4 := by linarith only [hX]
      calc 9 / 20 * a * (((a - δ) ^ 2 + X) * ((a + δ) ^ 2 + X))
          ≤ 9 / 20 * a * (1 + X) ^ 2 := mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = a * (9 / 20 * (1 + X) ^ 2) := by ring
        _ ≤ a * (2 * (X - 1 / 4) * γ ^ 2) := mul_le_mul_of_nonneg_left hmain ha.le
        _ ≤ a * (2 * (a ^ 2 - δ ^ 2 + X) * A) := by
            refine mul_le_mul_of_nonneg_left ?_ ha.le
            exact mul_le_mul (by linarith only [hnum2]) hA2 (sq_nonneg _)
              (by linarith only [hnum2, hX4])
        _ = _ := by ring
  refine le_trans ?_ hgoal
  exact mul_le_mul_of_nonneg_left hr (by positivity)

/-- **The floor of the logarithmic derivative.** -/
theorem re_logDeriv_xi_ge {a b : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hb : |b| ≤ 5) :
    0.0102 * a ≤ (logDeriv xi (1 / 2 + ((b : ℂ) - (a : ℂ) * I) * I)).re ∧
      xi (1 / 2 + ((b : ℂ) - (a : ℂ) * I) * I) ≠ 0 := by
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = 1 / 2 + ((b : ℂ) - (a : ℂ) * I) * I := ⟨_, rfl⟩
  rw [← hs]
  have hre : s.re = 1 / 2 + a := by
    rw [hs]
    norm_num [Complex.mul_re, Complex.mul_im]
  have him : s.im = b := by
    rw [hs]
    norm_num [Complex.mul_re, Complex.mul_im]
  have hxi : xi s ≠ 0 := by
    intro h0
    rcases eq_or_lt_of_le ha2 with rfl | hlt
    · exact xi_ne_zero_of_one_le_re (by rw [hre]; norm_num) h0
    · have h := lt_abs_im_of_rhVerifiedThrough rhVerifiedThrough_sixtySeven h0
        (by rw [hre]; linarith only [ha]) (by rw [hre]; linarith only [hlt])
        (by rw [hre]; linarith only [ha])
      rw [him] at h
      linarith only [h, hb]
  refine ⟨?_, hxi⟩
  have hsa : s.re - 1 / 2 = a := by rw [hre]; ring
  have hfloor (q : XiZeroCopy) := pair_floor ha ha2 hb q
  have hpair (q : XiZeroCopy) :
      0 ≤ xiLinePairRe (s.re - 1 / 2) ((q.1 : ℂ).re - 1 / 2) (s.im - (q.1 : ℂ).im) := by
    rw [hsa, him]
    by_cases hoff : (q.1 : ℂ).re = 1 / 2
    · rw [hoff, sub_self]
      unfold xiLinePairRe
      simp only [sub_zero, add_zero]
      positivity
    · refine le_trans ?_ (hfloor q)
      have hr : 0 ≤ ((1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
        have := WeilDeletion.inv_normSq_spectralPoint_le q
        have hp : 0 ≤ 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by positivity
        linarith only [this, hp]
      positivity
  have hsumRe : Summable fun q : XiZeroCopy => ((1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re :=
    summable_inv_mul_one_sub.mapL Complex.reCLM
  have hval : ∑' q : XiZeroCopy, ((1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re =
      poleSharpConstant := by
    rw [← Complex.re_tsum summable_inv_mul_one_sub, tsum_inv_zero_mul_one_sub_zero_re]
  have hmain : 9 / 20 * a * poleSharpConstant ≤ 2 * (logDeriv xi s).re := by
    rw [← hval, ← tsum_mul_left]
    refine (hsumRe.mul_left _).tsum_le_of_sum_le fun F => ?_
    refine le_trans (Finset.sum_le_sum fun q _ => ?_)
      (sum_pair_le_two_mul_re_logDeriv_xi hxi hpair F)
    rw [hsa, him]
    exact hfloor q
  have hP := le_poleSharpConstant
  have h1 := mul_le_mul_of_nonneg_left hP (by positivity : 0 ≤ 9 / 20 * a)
  norm_num at h1 ⊢
  linarith only [h1, hmain, ha]

/-! ## The floor -/

/-- **The explicit core of the current.** -/
theorem current_ge_of_abs_le {a b : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hb : |b| ≤ 5) :
    0.0006 * a ≤ current a b := by
  obtain ⟨hlog, hxi⟩ := re_logDeriv_xi_ge ha ha2 hb
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = (b : ℂ) - (a : ℂ) * I := ⟨_, rfl⟩
  rw [← hz] at hlog hxi
  have hne : XiC z ≠ 0 := hxi
  have him : 0.0102 * a ≤ (logDeriv XiC z).im := by
    rw [logDeriv_XiC_eq_mul_I_logDeriv_xi]
    simpa using hlog
  have hnn : ∀ a' ∈ Set.Ioo 0 a, 0 ≤ current a' b := fun a' ha' =>
    current_nonneg_of_rhVerifiedThrough (T := 66) ha'.1 (by
      have := rhVerifiedThrough_sixtySeven
      norm_num
      exact this) (hb.trans (by norm_num))
  have hN := sq_Xi_le_normSq ha.le hnn
  rw [← hz] at hN
  have hXi := Xi_ge_of_abs_le hb
  have hsq : (0.176 : ℝ) ^ 2 ≤ Xi b ^ 2 := pow_le_pow_left₀ (by norm_num) hXi 2
  have hcur : current a b = 2 * ((starRingEnd ℂ) (XiC z) * (-I * deriv XiC z)).re := by
    rw [hz]
    rfl
  rw [hcur, kreinCurrent_eq_normSq_mul_logDeriv_im _ _ hne, ← logDeriv_apply]
  have h1 : (0.176 : ℝ) ^ 2 * (0.0102 * a) ≤ Complex.normSq (XiC z) * (logDeriv XiC z).im :=
    mul_le_mul (hsq.trans hN) him (by positivity) (Complex.normSq_nonneg _)
  norm_num at h1 ⊢
  linarith only [h1, ha]

end GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
