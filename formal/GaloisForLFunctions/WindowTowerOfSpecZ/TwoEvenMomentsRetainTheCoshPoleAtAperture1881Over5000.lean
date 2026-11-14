import GaloisForLFunctions.ArithmeticCriticalityTheory.CurvedGaugeArchimedeanBounds
import GaloisForLFunctions.RHTower.Sieve.EnergyCauchySchwarz

/-!
# Two even moments of the cosh pole

The quartic Taylor expansion separates the constant and quadratic Legendre
charges. Orthogonality of the remaining quartic mode and the exponential
remainder bound pay the projection error with mass loss `1/50000`.
-/

noncomputable section
open Real MeasureTheory Set
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open ArithmeticCriticalityTheory

private def aperture : ℝ := 1881 / 5000
private def P2 (x : ℝ) : ℝ := (3 * x ^ 2 - 1) / 2
private def P4 (x : ℝ) : ℝ := (35 * x ^ 4 - 30 * x ^ 2 + 3) / 8
private def pole0 : ℝ := 1 + aperture ^ 2 / 24 + aperture ^ 4 / 1920
private def pole2 : ℝ := aperture ^ 2 / 12 + aperture ^ 4 / 672
private def pole4 : ℝ := aperture ^ 4 / 1680
private def poleProjection (x : ℝ) : ℝ := pole0 + pole2 * P2 x
private def coshRemainder (x : ℝ) : ℝ :=
  Real.cosh (aperture * x / 2) - (1 + aperture ^ 2 * x ^ 2 / 8 + aperture ^ 4 * x ^ 4 / 384)

private theorem coshRemainder_bound {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    |coshRemainder x| ≤ 1 / 10000000 := by
  let z := aperture * x / 2
  have hz : 0 ≤ z := by dsimp [z, aperture]; positivity
  have hzq : z ≤ 1881 / 10000 := by dsimp [z, aperture]; linarith only [hx1]
  have hz1 : |z| ≤ 1 := by rw [abs_of_nonneg hz]; linarith only [hzq]
  have hnz1 : |-z| ≤ 1 := by simpa only [abs_neg] using hz1
  have hl := taylor_seven_le_exp hz1
  have hln := taylor_seven_le_exp hnz1
  have hu := exp_le_taylor_seven hz1
  have hun := exp_le_taylor_seven hnz1
  norm_num only [abs_neg, abs_of_nonneg hz, neg_pow, neg_mul, one_mul] at hl hln hu hun
  have h6 := pow_le_pow_left₀ hz hzq 6
  have h7 := pow_le_pow_left₀ hz hzq 7
  have he : coshRemainder x = (Real.exp z + Real.exp (-z)) / 2 - (1 + z ^ 2 / 2 + z ^ 4 / 24) := by
    dsimp [coshRemainder, z]
    rw [Real.cosh_eq]
    ring
  rw [he, abs_le]
  constructor <;> nlinarith only [hl, hln, hu, hun, h6, h7, pow_nonneg hz 6]

private theorem poleProjection_decomposition (x : ℝ) :
    Real.cosh (aperture * x / 2) - poleProjection x = pole4 * P4 x + coshRemainder x := by
  unfold poleProjection pole0 pole2 pole4 P2 P4 coshRemainder
  ring

private theorem integral_P4_sq : (∫ x in (0 : ℝ)..1, P4 x ^ 2) = 1 / 9 := by
  have he : (fun x : ℝ => P4 x ^ 2) = fun x =>
      (1225 / 64 : ℝ) * x ^ 8 - (525 / 16 : ℝ) * x ^ 6 +
        (555 / 32 : ℝ) * x ^ 4 - (45 / 16 : ℝ) * x ^ 2 + 9 / 64 := by
    funext x
    dsimp [P4]
    ring
  rw [he]
  have hi (k : ℕ) (c : ℝ) : IntervalIntegrable (fun x : ℝ => c * x ^ k) volume 0 1 :=
    (continuous_const.mul (continuous_pow k)).intervalIntegrable 0 1
  have hi1 : IntervalIntegrable (fun x : ℝ => (1225 / 64 : ℝ) * x ^ 8 -
      (525 / 16 : ℝ) * x ^ 6) volume 0 1 := (hi 8 _).sub (hi 6 _)
  have hi2 : IntervalIntegrable (fun x : ℝ => (1225 / 64 : ℝ) * x ^ 8 -
      (525 / 16 : ℝ) * x ^ 6 + (555 / 32 : ℝ) * x ^ 4) volume 0 1 := hi1.add (hi 4 _)
  have hi3 : IntervalIntegrable (fun x : ℝ => (1225 / 64 : ℝ) * x ^ 8 -
      (525 / 16 : ℝ) * x ^ 6 + (555 / 32 : ℝ) * x ^ 4 - (45 / 16 : ℝ) * x ^ 2)
      volume 0 1 := hi2.sub (hi 2 _)
  rw [intervalIntegral.integral_add hi3 (continuous_const.intervalIntegrable 0 1),
    intervalIntegral.integral_sub hi2 (hi 2 _), intervalIntegral.integral_add hi1 (hi 4 _),
    intervalIntegral.integral_sub (hi 8 _) (hi 6 _)]
  simp only [intervalIntegral.integral_const_mul, integral_pow, intervalIntegral.integral_const]
  norm_num

private theorem poleProjection_mass :
    (∫ x in (0 : ℝ)..1, poleProjection x ^ 2) ≤ 121 / 100 := by
  have hc : Continuous poleProjection := by unfold poleProjection P2; fun_prop
  have h := intervalIntegral.integral_mono_on (μ := volume) (a := (0 : ℝ)) (b := 1) (by norm_num)
    ((hc.pow 2).intervalIntegrable 0 1) (continuous_const.intervalIntegrable 0 1)
    (show ∀ x ∈ Icc (0 : ℝ) 1, poleProjection x ^ 2 ≤ 121 / 100 from by
      intro x hx
      have hx2 : x ^ 2 ≤ 1 := by nlinarith only [hx.1, hx.2]
      have hsq : 0 ≤ x ^ 2 := sq_nonneg x
      have hp : -(11 / 10 : ℝ) ≤ poleProjection x ∧ poleProjection x ≤ 11 / 10 := by
        dsimp [poleProjection, pole0, pole2, aperture, P2]
        constructor <;> nlinarith only [hx2, hsq]
      nlinarith only [hp.1, hp.2])
  simpa using h

private theorem coshProjection_error_mass :
    (∫ x in (0 : ℝ)..1, (Real.cosh (aperture * x / 2) - poleProjection x) ^ 2) ≤
      1 / 30000000000 := by
  have hcont : Continuous (fun x => Real.cosh (aperture * x / 2) - poleProjection x) := by
    unfold poleProjection P2
    fun_prop
  have hP4 : Continuous P4 := by unfold P4; fun_prop
  have hiP : IntervalIntegrable (fun x => 2 * pole4 ^ 2 * P4 x ^ 2) volume 0 1 :=
    (continuous_const.mul (hP4.pow 2)).intervalIntegrable 0 1
  have hiC : IntervalIntegrable (fun _ : ℝ => (2 / 100000000000000 : ℝ)) volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hbound := intervalIntegral.integral_mono_on (μ := volume) (a := (0 : ℝ)) (b := 1) (by norm_num)
    ((hcont.pow 2).intervalIntegrable 0 1) (hiP.add hiC)
    (show ∀ x ∈ Icc (0 : ℝ) 1,
      (Real.cosh (aperture * x / 2) - poleProjection x) ^ 2 ≤
        2 * pole4 ^ 2 * P4 x ^ 2 + 2 / 100000000000000 from by
      intro x hx
      have hr := abs_le.mp (coshRemainder_bound hx.1 hx.2)
      rw [poleProjection_decomposition]
      nlinarith only [hr.1, hr.2, sq_nonneg (pole4 * P4 x - coshRemainder x)])
  rw [intervalIntegral.integral_add hiP hiC, intervalIntegral.integral_const_mul,
    integral_P4_sq, intervalIntegral.integral_const] at hbound
  norm_num [pole4, aperture] at hbound
  dsimp only [aperture]
  linarith only [hbound]

/-- The constant and quadratic Legendre charges retain the cosh pole with a small mass loss. -/
private theorem cosh_pole_projection_floor {G : ℝ → ℝ} (hG : Continuous G) :
    4 * aperture * (∫ x in (0 : ℝ)..1, G x * poleProjection x) ^ 2 -
      (1 / 50000 : ℝ) * (∫ x in (0 : ℝ)..1, G x ^ 2) ≤
        4 * aperture * (∫ x in (0 : ℝ)..1, G x * Real.cosh (aperture * x / 2)) ^ 2 := by
  let M := ∫ x in (0 : ℝ)..1, G x ^ 2
  let B := ∫ x in (0 : ℝ)..1, G x * poleProjection x
  let E := ∫ x in (0 : ℝ)..1, G x * (Real.cosh (aperture * x / 2) - poleProjection x)
  have hM : 0 ≤ M := intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg (G x))
  have hproj : Continuous poleProjection := by unfold poleProjection P2; fun_prop
  have hcosh : Continuous (fun x => Real.cosh (aperture * x / 2)) := by fun_prop
  have hB : B ^ 2 ≤ (121 / 100 : ℝ) * M := by
    have h := _root_.RHTower.Sieve.integral_mul_sq_le (by norm_num : (0 : ℝ) ≤ 1) hG hproj
    exact h.trans (by simpa [M, mul_comm] using mul_le_mul_of_nonneg_left poleProjection_mass hM)
  have hE : E ^ 2 ≤ (1 / 30000000000 : ℝ) * M := by
    have h := _root_.RHTower.Sieve.integral_mul_sq_le (by norm_num : (0 : ℝ) ≤ 1) hG (hcosh.sub hproj)
    exact h.trans (by simpa [M, mul_comm] using mul_le_mul_of_nonneg_left coshProjection_error_mass hM)
  have he : (∫ x in (0 : ℝ)..1, G x * Real.cosh (aperture * x / 2)) = B + E := by
    have hi1 : IntervalIntegrable (fun x => G x * Real.cosh (aperture * x / 2)) volume 0 1 :=
      (hG.mul hcosh).intervalIntegrable 0 1
    have hi2 : IntervalIntegrable (fun x => G x * poleProjection x) volume 0 1 :=
      (hG.mul hproj).intervalIntegrable 0 1
    dsimp [B, E]
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hi1 hi2]
    ring
  rw [he]
  change 4 * aperture * B ^ 2 - 1 / 50000 * M ≤ 4 * aperture * (B + E) ^ 2
  dsimp [aperture]
  nlinarith only [hB, hE, hM, sq_nonneg (B / 200000 + E)]

/-- The first two even moments retain the positive cosh pole with mass loss at most `1/50000`. -/
theorem even_cosh_pole_ge_two_moments {G : ℝ → ℝ} (hG : Continuous G) :
    4 * (1881 / 5000 : ℝ) *
      ((1 + (1881 / 5000 : ℝ) ^ 2 / 24 + (1881 / 5000 : ℝ) ^ 4 / 1920) *
        (∫ x in (0 : ℝ)..1, G x) +
       ((1881 / 5000 : ℝ) ^ 2 / 12 + (1881 / 5000 : ℝ) ^ 4 / 672) *
        (∫ x in (0 : ℝ)..1, G x * ((3 * x ^ 2 - 1) / 2))) ^ 2 -
      (1 / 50000 : ℝ) * (∫ x in (0 : ℝ)..1, G x ^ 2) ≤
        4 * (1881 / 5000 : ℝ) *
          (∫ x in (0 : ℝ)..1, G x * Real.cosh ((1881 / 5000 : ℝ) * x / 2)) ^ 2 := by
  have h := cosh_pole_projection_floor hG
  have he : (∫ x in (0 : ℝ)..1, G x * poleProjection x) =
      pole0 * (∫ x in (0 : ℝ)..1, G x) + pole2 * (∫ x in (0 : ℝ)..1, G x * P2 x) := by
    have hi0 : IntervalIntegrable (fun x => pole0 * G x) volume 0 1 :=
      (continuous_const.mul hG).intervalIntegrable 0 1
    have hi2 : IntervalIntegrable (fun x => pole2 * (G x * P2 x)) volume 0 1 := by
      apply Continuous.intervalIntegrable
      unfold P2
      fun_prop
    have hp : (fun x => G x * poleProjection x) = fun x => pole0 * G x + pole2 * (G x * P2 x) := by
      funext x
      dsimp [poleProjection]
      ring
    rw [hp, intervalIntegral.integral_add hi0 hi2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [he] at h
  exact h

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.even_cosh_pole_ge_two_moments
