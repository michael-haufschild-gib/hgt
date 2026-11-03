import GaloisForLFunctions.WindowTowerOfSpecZ.TheFirstFoldRetainsTwoMomentCharges
import Mathlib.Analysis.Convex.Deriv

/-! # A bounded polynomial comparison for the first fold

Four terms of the logarithmic potential give a bounded multiplication and
reflection form. Logarithmic convexity gives its lower spectral bound;
ordinary convexity reduces its upper bound to the strip endpoints.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open ArithmeticIncidencePositivity SelectivePositivityAndThresholdLaws

/-- Four positive terms of the exterior logarithmic potential. -/
def firstFoldLogPolynomial (u : ℝ) : ℝ :=
  u ^ 2 / 2 + u ^ 4 / 4 + u ^ 6 / 6 + u ^ 8 / 8

/-- The polynomial multiplication coefficient of the first-fold comparison. -/
def firstFoldPolynomialPotential (u : ℝ) : ℝ :=
  137 / 60 - firstFoldMomentMassCost + firstFoldLogPolynomial u

private def polynomialSlope (u : ℝ) : ℝ := u + u ^ 3 + u ^ 5 + u ^ 7

private def polynomialCurvature (u : ℝ) : ℝ := 1 + 3 * u ^ 2 + 5 * u ^ 4 + 7 * u ^ 6

theorem firstFoldLogPolynomial_nonneg (u : ℝ) : 0 ≤ firstFoldLogPolynomial u := by
  unfold firstFoldLogPolynomial
  positivity

theorem continuous_firstFoldLogPolynomial : Continuous firstFoldLogPolynomial := by
  unfold firstFoldLogPolynomial
  fun_prop

private theorem polynomial_deriv (u : ℝ) :
    HasDerivAt firstFoldLogPolynomial (polynomialSlope u) u := by
  have h := ((((hasDerivAt_pow 2 u).div_const 2).add
    ((hasDerivAt_pow 4 u).div_const 4)).add
    ((hasDerivAt_pow 6 u).div_const 6)).add ((hasDerivAt_pow 8 u).div_const 8)
  exact h.congr_deriv (by unfold polynomialSlope; ring)

private theorem polynomial_slope_deriv (u : ℝ) :
    HasDerivAt polynomialSlope (polynomialCurvature u) u := by
  have h := (((hasDerivAt_id u).add (hasDerivAt_pow 3 u)).add
    (hasDerivAt_pow 5 u)).add (hasDerivAt_pow 7 u)
  exact h.congr_deriv (by unfold polynomialCurvature; ring)

theorem firstFoldLogPolynomial_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    firstFoldLogPolynomial x ≤ firstFoldLogPolynomial y := by
  have h2 := pow_le_pow_left₀ hx hxy 2
  have h4 := pow_le_pow_left₀ hx hxy 4
  have h6 := pow_le_pow_left₀ hx hxy 6
  have h8 := pow_le_pow_left₀ hx hxy 8
  unfold firstFoldLogPolynomial
  linarith only [h2, h4, h6, h8]

theorem firstFoldLogPolynomial_convex : ConvexOn ℝ (Icc (0 : ℝ) 1) firstFoldLogPolynomial := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    continuous_firstFoldLogPolynomial.continuousOn
    (fun u _ => (polynomial_deriv u).hasDerivWithinAt)
    (fun u _ => (polynomial_slope_deriv u).hasDerivWithinAt)
  intro u _
  unfold polynomialCurvature
  positivity

/-- The fourth polynomial truncation lies below the exact logarithmic potential. -/
theorem firstFoldLogPolynomial_le_log {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    firstFoldLogPolynomial u ≤ -Real.log (1 - u ^ 2) / 2 := by
  let R : ℝ → ℝ := fun x => -Real.log (1 - x ^ 2) / 2 - firstFoldLogPolynomial x
  have hd {x : ℝ} (hx : x ∈ Icc (0 : ℝ) u) :
      HasDerivAt R (x ^ 9 / (1 - x ^ 2)) x := by
    have hx1 : x < 1 := hx.2.trans_lt hu.2
    have hx2 : x ^ 2 < 1 := by nlinarith only [hx.1, hx1]
    have hn : 1 - x ^ 2 ≠ 0 := ne_of_gt (by linarith only [hx2])
    have h := (((((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x)).log hn).neg).div_const 2).sub
      (polynomial_deriv x)
    exact h.congr_deriv (by
      simp only [Pi.sub_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      unfold polynomialSlope
      field_simp
      ring)
  have hm : MonotoneOn R (Icc (0 : ℝ) u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun x hx => (hd hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd (interior_subset hx)).differentiableAt.differentiableWithinAt)
    intro x hx
    have hi := interior_subset hx
    rw [(hd hi).deriv]
    have hx1 : x < 1 := hi.2.trans_lt hu.2
    have hx2 : x ^ 2 < 1 := by nlinarith only [hi.1, hx1]
    exact div_nonneg (pow_nonneg hi.1 _) (by linarith only [hx2])
  have h := hm ⟨le_rfl, hu.1.le⟩ ⟨hu.1.le, le_rfl⟩ hu.1.le
  norm_num [R, firstFoldLogPolynomial] at h
  unfold firstFoldLogPolynomial
  linarith only [h]

/-- Elementary constant bounds leave a positive multiplication coefficient. -/
theorem firstFold_polynomial_mass_bounds :
    (11 / 20 : ℝ) ≤ 137 / 60 - firstFoldMomentMassCost ∧
      137 / 60 - firstFoldMomentMassCost ≤ 14 / 25 := by
  have hp : (3 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d6]
  have hp2 : (9 : ℝ) ≤ Real.pi ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hp 2
    norm_num at h
    exact h
  have hi : 1 / (96 * Real.pi ^ 2) ≤ (1 / 864 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 96 * Real.pi ^ 2)).mpr
    linarith only [hp2]
  have hi0 : 0 ≤ 1 / (96 * Real.pi ^ 2) := by positivity
  have hlu : Real.log Real.pi ≤ Real.log 3 + Real.pi / 3 - 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < Real.pi / 3 by positivity)
    rw [Real.log_div Real.pi_ne_zero (by norm_num)] at h
    linarith only [h]
  have hgu := _root_.RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  have hgl := eulerMascheroniConstant_gt_577215_div_1000000
  have hpl : (314159 / 100000 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d6]
  have hdiv : 3 / Real.pi ≤ 3 / (314159 / 100000 : ℝ) := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    norm_num
    linarith only [hpl]
  have hll := Real.log_le_sub_one_of_pos (show 0 < 3 / Real.pi by positivity)
  rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) Real.pi_ne_zero] at hll
  unfold firstFoldMomentMassCost
  constructor
  · linarith only [hlu, hgu, hi, Real.log_three_lt_d9, Real.pi_lt_d4]
  · linarith only [hgl, hdiv, hll, hi0, Real.log_three_gt_d9]

theorem firstFold_prime_weight_bounds :
    0 ≤ Real.log 2 / Real.sqrt 2 ∧ Real.log 2 / Real.sqrt 2 ≤ 4902 / 10000 := by
  have h := vonMangoldtAtom_two_bounds
  simpa only [_root_.RHTower.vonMangoldtAtom, if_pos le_rfl,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_ofNat] using h

private theorem polynomial_log_curvature {k x : ℝ} (hk : (17 / 100 : ℝ) ≤ k)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ polynomialCurvature x * (k + firstFoldLogPolynomial x) - polynomialSlope x ^ 2 := by
  have h2 : x ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hx.1 hx.2 2
  have h4 : x ^ 4 ≤ 1 := by simpa using pow_le_pow_left₀ hx.1 hx.2 4
  have h6 : x ^ 6 ≤ 1 := by simpa using pow_le_pow_left₀ hx.1 hx.2 6
  have hk0 : 0 ≤ k := by linarith only [hk]
  have h1 : 0 ≤ 3 * k - 1 / 2 := by linarith only [hk]
  have h2c : 0 ≤ 5 * k - 1 / 4 := by linarith only [hk]
  have h3 : 0 ≤ 7 * k + 5 / 12 := by linarith only [hk]
  have hr : 0 ≤ 1 + (1 - x ^ 2) / 24 + 5 * (1 - x ^ 4) / 24 + (1 - x ^ 6) / 8 := by
    linarith only [h2, h4, h6]
  have he : polynomialCurvature x * (k + firstFoldLogPolynomial x) - polynomialSlope x ^ 2 =
      k + (3 * k - 1 / 2) * x ^ 2 + (5 * k - 1 / 4) * x ^ 4 +
        (7 * k + 5 / 12) * x ^ 6 +
        x ^ 8 * (1 + (1 - x ^ 2) / 24 + 5 * (1 - x ^ 4) / 24 + (1 - x ^ 6) / 8) := by
    unfold polynomialCurvature polynomialSlope firstFoldLogPolynomial
    ring
  rw [he]
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg hk0
    (mul_nonneg h1 (sq_nonneg x))) (mul_nonneg h2c (pow_nonneg hx.1 _)))
    (mul_nonneg h3 (pow_nonneg hx.1 _))) (mul_nonneg (pow_nonneg hx.1 _) hr)

private theorem polynomial_log_convex {k : ℝ} (hk : (17 / 100 : ℝ) ≤ k) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun u => Real.log (k + firstFoldLogPolynomial u)) := by
  have hp (u : ℝ) : 0 < k + firstFoldLogPolynomial u := by
    linarith only [hk, firstFoldLogPolynomial_nonneg u]
  have hd (u : ℝ) : HasDerivAt (fun x => Real.log (k + firstFoldLogPolynomial x))
      (polynomialSlope u / (k + firstFoldLogPolynomial u)) u :=
    ((polynomial_deriv u).const_add k).log (ne_of_gt (hp u))
  have hdd (u : ℝ) : HasDerivAt (fun x => polynomialSlope x / (k + firstFoldLogPolynomial x))
      ((polynomialCurvature u * (k + firstFoldLogPolynomial u) - polynomialSlope u ^ 2) /
        (k + firstFoldLogPolynomial u) ^ 2) u := by
    have h := (polynomial_slope_deriv u).div ((polynomial_deriv u).const_add k)
      (ne_of_gt (hp u))
    exact h.congr_deriv (by ring)
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (fun u _ => (hd u).continuousAt.continuousWithinAt)
    (fun u _ => (hd u).hasDerivWithinAt) (fun u _ => (hdd u).hasDerivWithinAt)
  intro u hu
  exact div_nonneg (polynomial_log_curvature hk (interior_subset hu)) (sq_nonneg _)

private theorem polynomial_center_lower :
    Real.log 2 / Real.sqrt 2 ≤ firstFoldPolynomialPotential (Real.log 2) - 19 / 50 := by
  have hb : (693 / 1000 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hv := firstFoldLogPolynomial_mono (by norm_num : (0 : ℝ) ≤ 693 / 1000) hb
  have hc : (19 / 50 : ℝ) + 4902 / 10000 ≤ 11 / 20 + firstFoldLogPolynomial (693 / 1000) := by
    norm_num [firstFoldLogPolynomial]
  unfold firstFoldPolynomialPotential
  linarith only [firstFold_polynomial_mass_bounds.1, firstFold_prime_weight_bounds.2, hv, hc]

private theorem polynomial_pair_lower_det {u : ℝ}
    (hu : u ∈ Icc (2 * Real.log 2 - 1) 1) :
    (Real.log 2 / Real.sqrt 2) ^ 2 ≤
      (firstFoldPolynomialPotential u - 19 / 50) *
        (firstFoldPolynomialPotential (2 * Real.log 2 - u) - 19 / 50) := by
  let k : ℝ := 137 / 60 - firstFoldMomentMassCost - 19 / 50
  have hk : (17 / 100 : ℝ) ≤ k := by dsimp [k]; linarith only [firstFold_polynomial_mass_bounds.1]
  have hb : (1 / 2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
    constructor <;> linarith only [Real.log_two_gt_d9, Real.log_two_lt_d9]
  have hu0 : u ∈ Icc (0 : ℝ) 1 := ⟨by linarith only [hu.1, hb.1], hu.2⟩
  have hv0 : 2 * Real.log 2 - u ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith only [hu.2, hb.1], by linarith only [hu.1]⟩
  have hp (x : ℝ) : 0 < k + firstFoldLogPolynomial x := by
    linarith only [hk, firstFoldLogPolynomial_nonneg x]
  have hm := (polynomial_log_convex hk).2 hu0 hv0
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hm
  rw [show (1 / 2 : ℝ) * u + (1 / 2) * (2 * Real.log 2 - u) = Real.log 2 by ring] at hm
  have hlog : Real.log ((k + firstFoldLogPolynomial (Real.log 2)) ^ 2) ≤
      Real.log ((k + firstFoldLogPolynomial u) *
        (k + firstFoldLogPolynomial (2 * Real.log 2 - u))) := by
    rw [Real.log_pow, Real.log_mul (ne_of_gt (hp u)) (ne_of_gt (hp _))]
    norm_num only [Nat.cast_ofNat]
    linarith only [hm]
  have hprod := (Real.log_le_log_iff (sq_pos_of_pos (hp _)) (mul_pos (hp _) (hp _))).mp hlog
  have hc := pow_le_pow_left₀ firstFold_prime_weight_bounds.1 polynomial_center_lower 2
  dsimp [k] at hprod
  unfold firstFoldPolynomialPotential at hc ⊢
  nlinarith only [hprod, hc]

theorem firstFoldPolynomialPotential_bounds {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    (19 / 50 : ℝ) ≤ firstFoldPolynomialPotential u ∧
      firstFoldPolynomialPotential u ≤ 37 / 20 := by
  have hv := firstFoldLogPolynomial_mono hu.1 hu.2
  rw [show firstFoldLogPolynomial 1 = (25 / 24 : ℝ) by norm_num [firstFoldLogPolynomial]] at hv
  unfold firstFoldPolynomialPotential
  constructor
  · linarith only [firstFold_polynomial_mass_bounds.1, firstFoldLogPolynomial_nonneg u]
  · linarith only [firstFold_polynomial_mass_bounds.2, hv]

private theorem pair_quadratic_nonneg {p q w : ℝ} (hp : 0 < p) (hd : w ^ 2 ≤ p * q)
    (x y : ℝ) : 0 ≤ p * x ^ 2 + 2 * w * x * y + q * y ^ 2 := by
  have h := mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg y)
  have he : 0 ≤ p * (p * x ^ 2 + 2 * w * x * y + q * y ^ 2) := by
    nlinarith only [h, sq_nonneg (p * x + w * y)]
  exact nonneg_of_mul_nonneg_right he hp

private theorem polynomial_pair_lower {u : ℝ}
    (hu : u ∈ Icc (2 * Real.log 2 - 1) 1) (x y : ℝ) :
    (19 / 50 : ℝ) * (x ^ 2 + y ^ 2) ≤
      firstFoldPolynomialPotential u * x ^ 2 +
        2 * (Real.log 2 / Real.sqrt 2) * x * y +
        firstFoldPolynomialPotential (2 * Real.log 2 - u) * y ^ 2 := by
  have hp : 0 < firstFoldPolynomialPotential u - 19 / 50 := by
    unfold firstFoldPolynomialPotential
    linarith only [firstFold_polynomial_mass_bounds.1, firstFoldLogPolynomial_nonneg u]
  have h := pair_quadratic_nonneg hp (polynomial_pair_lower_det hu) x y
  linarith only [h]

private theorem polynomial_endpoint_upper (x y : ℝ) :
    firstFoldPolynomialPotential (2 * Real.log 2 - 1) * x ^ 2 +
      2 * (Real.log 2 / Real.sqrt 2) * x * y +
      firstFoldPolynomialPotential 1 * y ^ 2 ≤ (37 / 20 : ℝ) * (x ^ 2 + y ^ 2) := by
  have hl : 0 ≤ 2 * Real.log 2 - 1 := by linarith only [Real.log_two_gt_d9]
  have hu : 2 * Real.log 2 - 1 ≤ (2 / 5 : ℝ) := by linarith only [Real.log_two_lt_d9]
  have hv := firstFoldLogPolynomial_mono hl hu
  have hv4 : firstFoldLogPolynomial (2 / 5) ≤ (9 / 100 : ℝ) := by
    norm_num [firstFoldLogPolynomial]
  have hL : firstFoldPolynomialPotential (2 * Real.log 2 - 1) ≤ (13 / 20 : ℝ) := by
    unfold firstFoldPolynomialPotential
    linarith only [hv, hv4, firstFold_polynomial_mass_bounds.2]
  have hR : firstFoldPolynomialPotential 1 ≤ (961 / 600 : ℝ) := by
    norm_num [firstFoldPolynomialPotential, firstFoldLogPolynomial]
    linarith only [firstFold_polynomial_mass_bounds.2]
  have hw : (Real.log 2 / Real.sqrt 2) ^ 2 ≤ (1 / 4 : ℝ) := by
    have h := pow_le_pow_left₀ firstFold_prime_weight_bounds.1
      (show Real.log 2 / Real.sqrt 2 ≤ (1 / 2 : ℝ) by
        linarith only [firstFold_prime_weight_bounds.2]) 2
    norm_num at h
    exact h
  have hd : (-(Real.log 2 / Real.sqrt 2)) ^ 2 ≤ (6 / 5 : ℝ) * (149 / 600) := by
    rw [neg_sq]
    linarith only [hw]
  have hq := pair_quadratic_nonneg (by norm_num : (0 : ℝ) < 6 / 5) hd x y
  have hLm := mul_le_mul_of_nonneg_right hL (sq_nonneg x)
  have hRm := mul_le_mul_of_nonneg_right hR (sq_nonneg y)
  nlinarith only [hq, hLm, hRm]

private theorem polynomial_pair_upper {u : ℝ}
    (hu : u ∈ Icc (2 * Real.log 2 - 1) 1) (x y : ℝ) :
    firstFoldPolynomialPotential u * x ^ 2 +
      2 * (Real.log 2 / Real.sqrt 2) * x * y +
      firstFoldPolynomialPotential (2 * Real.log 2 - u) * y ^ 2 ≤
        (37 / 20 : ℝ) * (x ^ 2 + y ^ 2) := by
  let l : ℝ := 2 * Real.log 2 - 1
  have hl : l ∈ Icc (0 : ℝ) 1 := by
    dsimp [l]
    constructor <;> linarith only [Real.log_two_gt_d9, Real.log_two_lt_d9]
  have hden : 0 < 1 - l := by dsimp [l]; linarith only [Real.log_two_lt_d9]
  let θ : ℝ := (u - l) / (1 - l)
  let η : ℝ := 1 - θ
  have hθ : 0 ≤ θ := div_nonneg (sub_nonneg.mpr hu.1) hden.le
  have hθ1 : θ ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    linarith only [hu.2]
  have hη : 0 ≤ η := sub_nonneg.mpr hθ1
  have hsum : η + θ = 1 := by dsimp [η]; ring
  have he1 : η * l + θ * 1 = u := by
    dsimp [η, θ]
    field_simp [ne_of_gt hden]
    ring
  have he2 : η * 1 + θ * l = 2 * Real.log 2 - u := by
    dsimp [η, θ]
    field_simp [ne_of_gt hden]
    dsimp [l]
    ring
  have hVa := firstFoldLogPolynomial_convex.2 hl (show (1 : ℝ) ∈ Icc 0 1 by norm_num) hη hθ hsum
  have hVb := firstFoldLogPolynomial_convex.2 (show (1 : ℝ) ∈ Icc 0 1 by norm_num) hl hη hθ hsum
  simp only [smul_eq_mul, he1, he2] at hVa hVb
  have hAu : firstFoldPolynomialPotential u ≤
      η * firstFoldPolynomialPotential l + θ * firstFoldPolynomialPotential 1 := by
    unfold firstFoldPolynomialPotential
    dsimp [η] at hVa ⊢
    nlinarith only [hVa]
  have hAv : firstFoldPolynomialPotential (2 * Real.log 2 - u) ≤
      η * firstFoldPolynomialPotential 1 + θ * firstFoldPolynomialPotential l := by
    unfold firstFoldPolynomialPotential
    dsimp [η] at hVb ⊢
    nlinarith only [hVb]
  have hAx := mul_le_mul_of_nonneg_right hAu (sq_nonneg x)
  have hAy := mul_le_mul_of_nonneg_right hAv (sq_nonneg y)
  have hE1 := polynomial_endpoint_upper x y
  have hE2 := polynomial_endpoint_upper y x
  change firstFoldPolynomialPotential l * x ^ 2 +
    2 * (Real.log 2 / Real.sqrt 2) * x * y + firstFoldPolynomialPotential 1 * y ^ 2 ≤ _ at hE1
  change firstFoldPolynomialPotential l * y ^ 2 +
    2 * (Real.log 2 / Real.sqrt 2) * y * x + firstFoldPolynomialPotential 1 * x ^ 2 ≤ _ at hE2
  calc
    _ ≤ (η * firstFoldPolynomialPotential l + θ * firstFoldPolynomialPotential 1) * x ^ 2 +
        2 * (Real.log 2 / Real.sqrt 2) * x * y +
        (η * firstFoldPolynomialPotential 1 + θ * firstFoldPolynomialPotential l) * y ^ 2 := by
      linarith only [hAx, hAy]
    _ = η * (firstFoldPolynomialPotential l * x ^ 2 +
        2 * (Real.log 2 / Real.sqrt 2) * x * y + firstFoldPolynomialPotential 1 * y ^ 2) +
      θ * (firstFoldPolynomialPotential l * y ^ 2 +
        2 * (Real.log 2 / Real.sqrt 2) * y * x + firstFoldPolynomialPotential 1 * x ^ 2) := by
      dsimp [η]
      ring
    _ ≤ η * ((37 / 20 : ℝ) * (x ^ 2 + y ^ 2)) + θ * ((37 / 20 : ℝ) * (y ^ 2 + x ^ 2)) :=
      add_le_add (mul_le_mul_of_nonneg_left hE1 hη) (mul_le_mul_of_nonneg_left hE2 hθ)
    _ = _ := by dsimp [η]; ring

/-- Each polynomial reflection block lies between the same two positive scalar matrices. -/
theorem firstFoldPolynomial_pair_bounds {u : ℝ}
    (hu : u ∈ Icc (2 * Real.log 2 - 1) 1) (x y : ℝ) :
    (19 / 50 : ℝ) * (x ^ 2 + y ^ 2) ≤
      firstFoldPolynomialPotential u * x ^ 2 + 2 * (Real.log 2 / Real.sqrt 2) * x * y +
        firstFoldPolynomialPotential (2 * Real.log 2 - u) * y ^ 2 ∧
    firstFoldPolynomialPotential u * x ^ 2 + 2 * (Real.log 2 / Real.sqrt 2) * x * y +
        firstFoldPolynomialPotential (2 * Real.log 2 - u) * y ^ 2 ≤
      (37 / 20 : ℝ) * (x ^ 2 + y ^ 2) :=
  ⟨polynomial_pair_lower hu x y, polynomial_pair_upper hu x y⟩

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.firstFoldLogPolynomial_le_log
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.firstFoldPolynomial_pair_bounds
