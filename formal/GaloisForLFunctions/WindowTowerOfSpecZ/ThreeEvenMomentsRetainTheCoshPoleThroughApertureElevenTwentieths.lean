import GaloisForLFunctions.ArithmeticCriticalityTheory.CurvedGaugeArchimedeanBounds
import GaloisForLFunctions.RHTower.Sieve.EnergyCauchySchwarz

/-!
# Three even moments of the cosh pole

Retaining the complete quartic Taylor polynomial confines the error to order
six. Through aperture `11/20`, the pole loses at most `1/300000` times mass.
The quartic moment remains explicit so its mixed charges can cancel against
the fourth Gamma correlation moment.
-/

noncomputable section
open Real MeasureTheory Set
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open ArithmeticCriticalityTheory

private def quarticPoleProjection (a x : ℝ) : ℝ :=
  1 + a ^ 2 * x ^ 2 / 8 + a ^ 4 * x ^ 4 / 384

private theorem cosh_quartic_remainder_bound {a x : ℝ} (ha0 : 0 ≤ a)
    (ha : a ≤ 11 / 20) (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    |Real.cosh (a * x / 2) - quarticPoleProjection a x| ≤ 1 / 1500000 := by
  let z := a * x / 2
  have hz : 0 ≤ z := by dsimp only [z]; positivity
  have hzq : z ≤ 11 / 40 := by
    have h := mul_le_mul_of_nonneg_left hx ha0
    dsimp only [z]
    linarith only [h, ha]
  have hz1 : |z| ≤ 1 := by rw [abs_of_nonneg hz]; linarith only [hzq]
  have hnz1 : |-z| ≤ 1 := by simpa only [abs_neg] using hz1
  have hl := taylor_seven_le_exp hz1
  have hln := taylor_seven_le_exp hnz1
  have hu := exp_le_taylor_seven hz1
  have hun := exp_le_taylor_seven hnz1
  norm_num only [abs_neg, abs_of_nonneg hz, neg_pow, neg_mul, one_mul] at hl hln hu hun
  have h6 := pow_le_pow_left₀ hz hzq 6
  have h7 := pow_le_pow_left₀ hz hzq 7
  have he : Real.cosh (a * x / 2) - quarticPoleProjection a x =
      (Real.exp z + Real.exp (-z)) / 2 - (1 + z ^ 2 / 2 + z ^ 4 / 24) := by
    dsimp only [quarticPoleProjection, z]
    rw [Real.cosh_eq]
    ring
  rw [he, abs_le]
  constructor <;> nlinarith only [hl, hln, hu, hun, h6, h7, pow_nonneg hz 6]

private theorem quarticPoleProjection_sq_bound {a x : ℝ} (ha0 : 0 ≤ a)
    (ha : a ≤ 11 / 20) (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    quarticPoleProjection a x ^ 2 ≤ 441 / 400 := by
  have ht : 0 ≤ a * x := mul_nonneg ha0 hx0
  have hu : a * x ≤ 11 / 20 := by
    have h := mul_le_mul_of_nonneg_left hx ha0
    linarith only [h, ha]
  have h2 := pow_le_pow_left₀ ht hu 2
  have h4 := pow_le_pow_left₀ ht hu 4
  have hp : 0 ≤ quarticPoleProjection a x ∧ quarticPoleProjection a x ≤ 21 / 20 := by
    rw [mul_pow] at h2 h4
    unfold quarticPoleProjection
    constructor
    · positivity
    · linarith only [h2, h4]
  nlinarith only [hp.1, hp.2]

private theorem cosh_pole_quartic_projection_floor {G : ℝ → ℝ} (hG : Continuous G)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 11 / 20) :
    4 * a * (∫ x in (0 : ℝ)..1, G x * quarticPoleProjection a x) ^ 2 -
      (1 / 300000) * (∫ x in (0 : ℝ)..1, G x ^ 2) ≤
        4 * a * (∫ x in (0 : ℝ)..1, G x * Real.cosh (a * x / 2)) ^ 2 := by
  let M := ∫ x in (0 : ℝ)..1, G x ^ 2
  let B := ∫ x in (0 : ℝ)..1, G x * quarticPoleProjection a x
  let E := ∫ x in (0 : ℝ)..1,
    G x * (Real.cosh (a * x / 2) - quarticPoleProjection a x)
  have hM : 0 ≤ M := intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg (G x))
  have hproj : Continuous (quarticPoleProjection a) := by unfold quarticPoleProjection; fun_prop
  have hcosh : Continuous (fun x => Real.cosh (a * x / 2)) := by fun_prop
  have hP : (∫ x in (0 : ℝ)..1, quarticPoleProjection a x ^ 2) ≤ 441 / 400 := by
    have h := intervalIntegral.integral_mono_on (μ := volume)
      (a := (0 : ℝ)) (b := 1) (by norm_num)
      ((hproj.pow 2).intervalIntegrable 0 1) (continuous_const.intervalIntegrable 0 1)
      (fun x hx => quarticPoleProjection_sq_bound ha0 ha hx.1 hx.2)
    simpa using h
  have hErr : (∫ x in (0 : ℝ)..1,
      (Real.cosh (a * x / 2) - quarticPoleProjection a x) ^ 2) ≤ 1 / 2250000000000 := by
    have h := intervalIntegral.integral_mono_on (μ := volume)
      (a := (0 : ℝ)) (b := 1) (by norm_num)
      (((hcosh.sub hproj).pow 2).intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1)
      (show ∀ x ∈ Icc (0 : ℝ) 1,
        (Real.cosh (a * x / 2) - quarticPoleProjection a x) ^ 2 ≤
          (1 / 2250000000000 : ℝ) from by
        intro x hx
        have hr := abs_le.mp (cosh_quartic_remainder_bound ha0 ha hx.1 hx.2)
        nlinarith only [hr.1, hr.2])
    simpa using h
  have hB : B ^ 2 ≤ (441 / 400) * M := by
    have h := _root_.RHTower.Sieve.integral_mul_sq_le (by norm_num : (0 : ℝ) ≤ 1) hG hproj
    exact h.trans (by simpa only [M, mul_comm] using mul_le_mul_of_nonneg_left hP hM)
  have hE : E ^ 2 ≤ (1 / 2250000000000) * M := by
    have h := _root_.RHTower.Sieve.integral_mul_sq_le (by norm_num : (0 : ℝ) ≤ 1)
      hG (hcosh.sub hproj)
    change E ^ 2 ≤ M * (∫ x in (0 : ℝ)..1,
      (Real.cosh (a * x / 2) - quarticPoleProjection a x) ^ 2) at h
    exact h.trans (by simpa only [M, mul_comm] using mul_le_mul_of_nonneg_left hErr hM)
  have he : (∫ x in (0 : ℝ)..1, G x * Real.cosh (a * x / 2)) = B + E := by
    have hi1 : IntervalIntegrable (fun x => G x * Real.cosh (a * x / 2)) volume 0 1 :=
      (hG.mul hcosh).intervalIntegrable 0 1
    have hi2 : IntervalIntegrable (fun x => G x * quarticPoleProjection a x) volume 0 1 :=
      (hG.mul hproj).intervalIntegrable 0 1
    dsimp only [B, E]
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hi1 hi2]
    ring
  have hd : B ^ 2 - (B + E) ^ 2 ≤ (1 / 700000) * M := by
    nlinarith only [hB, hE, hM, sq_nonneg (B / 1500000 + E)]
  have hm := mul_le_mul_of_nonneg_left hd (show 0 ≤ 4 * a by positivity)
  have ha' : 4 * a / 700000 ≤ (1 / 300000 : ℝ) := by linarith only [ha]
  have hr := mul_le_mul_of_nonneg_right ha' hM
  rw [he]
  change 4 * a * B ^ 2 - 1 / 300000 * M ≤ 4 * a * (B + E) ^ 2
  nlinarith only [hm, hr]

/-- Three even Legendre moments retain the cosh pole with a sixth-order remainder cost. -/
theorem even_cosh_pole_ge_three_moments {G : ℝ → ℝ} (hG : Continuous G)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 11 / 20) :
    4 * a *
      ((1 + a ^ 2 / 24 + a ^ 4 / 1920) * (∫ x in (0 : ℝ)..1, G x) +
        (a ^ 2 / 12 + a ^ 4 / 672) *
          (∫ x in (0 : ℝ)..1, G x * ((3 * x ^ 2 - 1) / 2)) +
        (a ^ 4 / 1680) *
          (∫ x in (0 : ℝ)..1, G x * ((35 * x ^ 4 - 30 * x ^ 2 + 3) / 8))) ^ 2 -
      (1 / 300000) * (∫ x in (0 : ℝ)..1, G x ^ 2) ≤
        4 * a * (∫ x in (0 : ℝ)..1, G x * Real.cosh (a * x / 2)) ^ 2 := by
  have h := cosh_pole_quartic_projection_floor hG ha0 ha
  have he : (fun x => G x * quarticPoleProjection a x) = fun x =>
      (1 + a ^ 2 / 24 + a ^ 4 / 1920) * G x +
        (a ^ 2 / 12 + a ^ 4 / 672) * (G x * ((3 * x ^ 2 - 1) / 2)) +
          (a ^ 4 / 1680) * (G x * ((35 * x ^ 4 - 30 * x ^ 2 + 3) / 8)) := by
    funext x
    unfold quarticPoleProjection
    ring
  rw [he] at h
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const_mul] at h
  exact h

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.even_cosh_pole_ge_three_moments
