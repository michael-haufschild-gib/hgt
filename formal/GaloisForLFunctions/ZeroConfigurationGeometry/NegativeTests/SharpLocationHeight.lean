import GaloisForLFunctions.ZeroConfigurationGeometry.NegativeTests.SharpLocation

/-!
# The sharp-location height in closed form

`zetaNegativeCameraHeight λ c` is a nested finite expression. For `1 < λ ≤ 2` its logarithm is
bounded by `max (4/(λ−1)) (7Ω log(792Ω²/(λ−1)))`, where `Ω = 2.2·10¹⁷(c + 51395)`. So the height
is single-exponential in `c log c`, and the depth exponent available at aperture `a` grows like
`a / log a`.
-/

open Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23 SquareRootThreshold

/-- The master scale of the sharp-location height at depth exponent `c`. -/
def sharpLocationScale (c : ℝ) : ℝ := 22 * 10 ^ 16 * (c + 51395)

/-- Closed form for the logarithm of the sharp-location height. -/
def sharpLocationLogHeight (lam c : ℝ) : ℝ :=
  max (4 / (lam - 1))
    (7 * sharpLocationScale c * Real.log (792 * sharpLocationScale c ^ 2 / (lam - 1)))

private theorem log_four_pi_le_three : Real.log (4 * π) ≤ 3 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have he := Real.exp_one_gt_d9
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h3]
  have h27 : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
  linarith [Real.pi_lt_d2, (by norm_num : (2.7 : ℝ) ^ 3 = 19.683)]

private theorem log_le_ten {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 20000) : Real.log x ≤ 10 := by
  rw [Real.log_le_iff_le_exp hx0]
  have he := Real.exp_one_gt_d9
  have h3 : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h3]
  have h27 : (2.7 : ℝ) ^ 10 ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num) (by linarith) 10
  have : (20000 : ℝ) ≤ (2.7 : ℝ) ^ 10 := by norm_num
  linarith

/-- For `1 < θ ≤ 3/2`, the ζ count constant is below `802`. -/
private theorem zetaCameraCountConstant_le {θ : ℝ} (hθ : 1 < θ) (hθ' : θ ≤ 3 / 2) :
    zetaCameraCountConstant θ ≤ 802 := by
  have hlog := log_four_pi_le_three
  have hdiv : 3 * θ / (2 * π) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [Real.pi_gt_three]
  unfold zetaCameraCountConstant
  linarith

private theorem nfRate_nonneg' {s : ℝ} (hs0 : 0 ≤ s) : 0 ≤ nfRate s := by
  have hlog0 : 0 ≤ Real.log (2 * s + 9) := Real.log_nonneg (by linarith)
  unfold nfRate
  positivity

/-- Rate bounds at slack at most `5100`. -/
private theorem nfRate_le {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 5100) : nfRate s ≤ 250000 := by
  have hlog : Real.log (2 * s + 9) ≤ 10 := log_le_ten (by linarith) (by linarith)
  have hlog0 : 0 ≤ Real.log (2 * s + 9) := Real.log_nonneg (by linarith)
  have hm : (1 + s) * (2 + Real.log (2 * s + 9)) ≤ 5101 * 12 :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  unfold nfRate
  nlinarith only [hm]

private theorem growthRate_bounds {ℓ : ℝ} (hs0 : 0 ≤ slackBound ℓ) (hs : slackBound ℓ ≤ 5100) :
    0 ≤ growthRate ℓ ∧ growthRate ℓ ≤ 4 * 10 ^ 9 := by
  have hn := nfRate_le hs0 hs
  have hn0 := nfRate_nonneg' hs0
  have hpi3 := Real.pi_gt_three
  have hpi := Real.pi_lt_d2
  unfold growthRate
  obtain ⟨s, hsdef⟩ : ∃ s, s = slackBound ℓ := ⟨_, rfl⟩
  rw [← hsdef] at hs0 hs hn hn0 ⊢
  have hp : (2 + s) * (1 + 2 * s) ≤ 5102 * 10201 :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  have hp0 : 0 ≤ (2 + s) * (1 + 2 * s) := by positivity
  have h1 : π * (2 + s) * (1 + 2 * s) / 2 ≤ 2 * (5102 * 10201) := by
    have hpi2 : π / 2 ≤ 2 := by linarith
    calc π * (2 + s) * (1 + 2 * s) / 2 = π / 2 * ((2 + s) * (1 + 2 * s)) := by ring
      _ ≤ 2 * (5102 * 10201) := mul_le_mul hpi2 hp hp0 (by norm_num)
  have h10 : 0 ≤ π * (2 + s) * (1 + 2 * s) / 2 := by positivity
  have h2 : 3 * s * nfRate s ≤ 3 * 5100 * 250000 :=
    mul_le_mul (by linarith) hn hn0 (by norm_num)
  have h20 : 0 ≤ 3 * s * nfRate s := by positivity
  have h3 : π / 4 ≤ 1 := by linarith
  have h30 : 0 ≤ π / 4 := by positivity
  constructor
  · linarith only [h10, h20, h30]
  · norm_num at h1 h2 ⊢
    linarith only [h1, h2, h3]

private theorem floorRate_bounds {ℓ : ℝ} (hs0 : 0 ≤ slackBound ℓ) (hs : slackBound ℓ ≤ 5100) :
    0 ≤ floorRate ℓ ∧ floorRate ℓ ≤ 2 * 10 ^ 17 := by
  have hn := nfRate_le hs0 hs
  have hn0 := nfRate_nonneg' hs0
  unfold floorRate
  obtain ⟨s, hsdef⟩ : ∃ s, s = slackBound ℓ := ⟨_, rfl⟩
  rw [← hsdef] at hs0 hs hn hn0 ⊢
  have hsq : (1 + s) ^ 2 ≤ 5101 ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h1 : 6 * s * (1 + (1 + s) ^ 2) ≤ 6 * 5100 * (1 + 5101 ^ 2) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
  have h2 : 6 * s * (1 + (1 + s) ^ 2) * nfRate s ≤ 6 * 5100 * (1 + 5101 ^ 2) * 250000 :=
    mul_le_mul h1 hn hn0 (by norm_num)
  have h20 : 0 ≤ 6 * s * (1 + (1 + s) ^ 2) * nfRate s := by positivity
  have hsq0 : 0 ≤ (1 + s) ^ 2 := by positivity
  constructor
  · linarith only [h20, hsq0]
  · norm_num at hsq h2 ⊢
    linarith only [hsq, h2]

/-- The numerical parameter `MK` of the cubic camera. -/
private def camMK (ℓ lam Lη : ℝ) : ℝ :=
  6 * slackBound ℓ * (1 + slackBound ℓ) * lam +
    ((2 * growthRate ℓ * lam ^ 2 + 2 * floorRate ℓ * lam ^ 2 * (lam + Lη)) / 2 + 2) + 2

private theorem camMK_bounds {ℓ lam Lη : ℝ} (hs0 : 0 ≤ slackBound ℓ) (hs : slackBound ℓ ≤ 5100)
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hL : 0 ≤ Lη) :
    4 ≤ camMK ℓ lam Lη ∧ camMK ℓ lam Lη ≤ 22 * 10 ^ 16 * (1 + Lη) := by
  obtain ⟨hG0, hG⟩ := growthRate_bounds hs0 hs
  obtain ⟨hF0, hF⟩ := floorRate_bounds hs0 hs
  have hsq : lam ^ 2 ≤ 1 := pow_le_one₀ hlam0.le hlam1
  have hsq0 : 0 ≤ lam ^ 2 := sq_nonneg _
  unfold camMK
  obtain ⟨s, hsdef⟩ : ∃ s, s = slackBound ℓ := ⟨_, rfl⟩
  rw [← hsdef] at hs0 hs ⊢
  obtain ⟨G, hGd⟩ : ∃ G, G = growthRate ℓ := ⟨_, rfl⟩
  obtain ⟨F, hFd⟩ : ∃ F, F = floorRate ℓ := ⟨_, rfl⟩
  rw [← hGd] at hG0 hG ⊢
  rw [← hFd] at hF0 hF ⊢
  have he0 : 0 ≤ 6 * s * (1 + s) * lam := by positivity
  have he1 : 6 * s * (1 + s) * lam ≤ 6 * 5100 * (1 + 5100) * 1 :=
    mul_le_mul (mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)) hlam1
      hlam0.le (by norm_num)
  have h1 : G * lam ^ 2 ≤ 4 * 10 ^ 9 * 1 := mul_le_mul hG hsq hsq0 (by norm_num)
  have h10 : 0 ≤ G * lam ^ 2 := by positivity
  have h2 : F * lam ^ 2 ≤ 2 * 10 ^ 17 * 1 := mul_le_mul hF hsq hsq0 (by norm_num)
  have h20 : 0 ≤ F * lam ^ 2 := by positivity
  have h3 : F * lam ^ 2 * (lam + Lη) ≤ (2 * 10 ^ 17 * 1) * (1 + Lη) :=
    mul_le_mul h2 (by linarith) (by positivity) (by norm_num)
  have h30 : 0 ≤ F * lam ^ 2 * (lam + Lη) := by positivity
  constructor
  · linarith only [he0, h10, h30, show 2 * G * lam ^ 2 = 2 * (G * lam ^ 2) by ring,
      show 2 * F * lam ^ 2 * (lam + Lη) = 2 * (F * lam ^ 2 * (lam + Lη)) by ring]
  · have hLone : (1 : ℝ) ≤ 1 + Lη := by linarith
    have : 2 * G * lam ^ 2 = 2 * (G * lam ^ 2) := by ring
    have h' : 2 * F * lam ^ 2 * (lam + Lη) = 2 * (F * lam ^ 2 * (lam + Lη)) := by ring
    rw [this, h']
    norm_num at he1 h1 h3 ⊢
    nlinarith only [he1, h1, h3, hLone]

private theorem camQ_le {MK Ω l : ℝ} (hMK : 4 ≤ MK) (hMKΩ : MK ≤ Ω) (hl0 : 0 < l) (hl1 : l ≤ 1) :
    0 ≤ max 0 (Real.log (1 / (24 * MK * (1 + 8 * MK / (l / 4))))⁻¹) ∧
      max 0 (Real.log (1 / (24 * MK * (1 + 8 * MK / (l / 4))))⁻¹) ≤
        Real.log (792 * Ω ^ 2 / l) := by
  have hΩ0 : 0 < Ω := by linarith
  have hρe : 8 * MK / (l / 4) = 32 * MK / l := by field_simp; ring
  have hρ0 : 0 ≤ 32 * MK / l := by positivity
  have hinv : (1 / (24 * MK * (1 + 8 * MK / (l / 4))))⁻¹ = 24 * MK * (1 + 32 * MK / l) := by
    rw [one_div, inv_inv, hρe]
  rw [hinv]
  have hge1 : 1 ≤ 24 * MK * (1 + 32 * MK / l) := by nlinarith only [hMK, hρ0]
  have hinv1 : 1 ≤ l⁻¹ := (one_le_inv₀ hl0).mpr hl1
  have hle : 24 * MK * (1 + 32 * MK / l) ≤ 792 * Ω ^ 2 / l := by
    have h1 : 1 + 32 * MK / l ≤ 33 * Ω / l := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have h : 32 * MK * l⁻¹ ≤ 32 * Ω * l⁻¹ := by gcongr
      have hΩ1 : 1 ≤ Ω := by linarith
      nlinarith only [h, mul_le_mul hΩ1 hinv1 (by norm_num : (0 : ℝ) ≤ 1) hΩ0.le]
    calc 24 * MK * (1 + 32 * MK / l) ≤ 24 * Ω * (33 * Ω / l) :=
          mul_le_mul (by linarith) h1 (by positivity) (by positivity)
      _ = 792 * Ω ^ 2 / l := by ring
  refine ⟨le_max_left _ _, max_le (Real.log_nonneg (hge1.trans hle)) ?_⟩
  exact Real.log_le_log (by linarith) hle

theorem sharpLocationScale_ge {c : ℝ} (hc : 0 ≤ c) : 10 ^ 22 ≤ sharpLocationScale c := by
  unfold sharpLocationScale
  nlinarith only [hc]

private theorem cameraSlowConstant_le {ℓ lam : ℝ} (hs0 : 0 ≤ slackBound ℓ)
    (hs : slackBound ℓ ≤ 5100) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    cameraSlowConstant lam ℓ 0 ≤ 2 * 10 ^ 10 := by
  unfold cameraSlowConstant
  rw [Real.rpow_zero]
  obtain ⟨s, hsdef⟩ : ∃ s, s = slackBound ℓ := ⟨_, rfl⟩
  rw [← hsdef] at hs0 hs ⊢
  have hsq : lam ^ 2 ≤ 1 := pow_le_one₀ hlam0.le hlam1
  have h1 : s * lam ^ 2 ≤ 5100 * 1 := mul_le_mul hs hsq (sq_nonneg _) (by norm_num)
  have h2 : s * lam ≤ 5100 * 1 := mul_le_mul hs hlam1 hlam0.le (by norm_num)
  have h3 : (s * lam ^ 2) * (1 + s * 1 + s * lam) ≤ (5100 * 1) * (1 + 5100 + 5100) :=
    mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
  have hpi : π * lam ≤ 4 * 1 := mul_le_mul (by linarith [Real.pi_lt_d2]) hlam1 hlam0.le (by norm_num)
  have he : 320 * s * lam ^ 2 * (1 + s * 1 + s * lam) =
      320 * ((s * lam ^ 2) * (1 + s * 1 + s * lam)) := by ring
  rw [he]
  norm_num at h3 ⊢
  linarith only [h3, hpi]

/-- The cubic isolation height, with the camera parameter `MK` named. -/
private theorem cameraCubicIsolationHeight_le {lam μ θ A Lη Ω : ℝ} (hμ : μ = lam / 2)
    (hθ : θ = μ + 1 / 2) (hlam : 1 < lam) (hlam2 : lam ≤ 2)
    (hs0 : 0 ≤ slackBound (2 * π * A / μ)) (hs : slackBound (2 * π * A / μ) ≤ 5100)
    (hL0 : 0 ≤ Lη) (hΩ : 22 * 10 ^ 16 * (1 + Lη) ≤ Ω) (hΩ22 : (10 : ℝ) ^ 22 ≤ Ω) :
    cameraCubicIsolationHeight θ μ A (33 / 100) Lη ≤
      2 * π * Real.exp (7 * Ω * Real.log (792 * Ω ^ 2 / (lam - 1))) := by
  have hμ0 : 0 < μ := by rw [hμ]; linarith
  have hμ1 : μ ≤ 1 := by rw [hμ]; linarith
  have hμ12 : 1 / 2 < μ := by rw [hμ]; linarith
  have hl0 : 0 < lam - 1 := by linarith
  have hl1 : lam - 1 ≤ 1 := by linarith
  have hβ : μ - θ / 2 = (lam - 1) / 4 := by rw [hθ, hμ]; ring
  obtain ⟨hMK4, hMKle⟩ := camMK_bounds hs0 hs hμ0 hμ1 hL0
  have hMKΩ : camMK (2 * π * A / μ) μ Lη ≤ Ω := hMKle.trans hΩ
  obtain ⟨hq0, hqle⟩ := camQ_le hMK4 hMKΩ hl0 hl1
  have hrew : cameraCubicIsolationHeight θ μ A (33 / 100) Lη =
      2 * π * Real.exp (max (max (max 1 (2 * π / μ))
        (6 * camMK (2 * π * A / μ) μ Lη *
            max 0 (Real.log (1 / (24 * camMK (2 * π * A / μ) μ Lη *
              (1 + 8 * camMK (2 * π * A / μ) μ Lη / (μ - θ / 2))))⁻¹) +
          (μ + 4) + (Real.log (max (33 / 100) 1) + 605) + 1))
        (Real.log (max (6 * cameraSlowConstant μ (2 * π * A / μ) 0) (4 * μ) + 1))) := rfl
  rw [hrew, hβ]
  obtain ⟨MK, hMKd⟩ : ∃ x, x = camMK (2 * π * A / μ) μ Lη := ⟨_, rfl⟩
  rw [← hMKd] at hMK4 hMKΩ hq0 hqle ⊢
  obtain ⟨q, hqd⟩ : ∃ x, x = max 0 (Real.log (1 / (24 * MK * (1 + 8 * MK / ((lam - 1) / 4))))⁻¹) :=
    ⟨_, rfl⟩
  rw [← hqd] at hq0 hqle ⊢
  have hslow := cameraSlowConstant_le hs0 hs hμ0 hμ1
  obtain ⟨Sl, hSl⟩ : ∃ x, x = cameraSlowConstant μ (2 * π * A / μ) 0 := ⟨_, rfl⟩
  rw [← hSl] at hslow ⊢
  have hΩ0 : 0 < Ω := lt_of_lt_of_le (by norm_num) hΩ22
  have hY1 : 3 ≤ 792 * Ω ^ 2 / (lam - 1) := by
    rw [le_div_iff₀ hl0]
    have : (1 : ℝ) ≤ Ω ^ 2 := one_le_pow₀ (le_trans (by norm_num) hΩ22)
    nlinarith only [this, hl1, hl0]
  have hlogY : 1 ≤ Real.log (792 * Ω ^ 2 / (lam - 1)) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  obtain ⟨Lg, hLg⟩ : ∃ x, x = Real.log (792 * Ω ^ 2 / (lam - 1)) := ⟨_, rfl⟩
  rw [← hLg] at hqle hlogY ⊢
  have hΩLg : Ω ≤ Ω * Lg := by nlinarith only [hΩ0, hlogY]
  have h611 : (611 : ℝ) ≤ Ω := le_trans (by norm_num) hΩ22
  have hmain : 6 * MK * q ≤ 6 * Ω * Lg :=
    mul_le_mul (by linarith) hqle hq0 (by positivity)
  have hU₁ : max 1 (2 * π / μ) ≤ 7 * Ω * Lg := by
    refine max_le (by nlinarith only [h611, hΩLg]) ?_
    rw [div_le_iff₀ hμ0]
    nlinarith only [h611, hΩLg, hμ12, Real.pi_lt_d2]
  have hU₂ : 6 * MK * q + (μ + 4) + (Real.log (max (33 / 100) 1) + 605) + 1 ≤ 7 * Ω * Lg := by
    have hmax : max ((33 : ℝ) / 100) 1 = 1 := max_eq_right (by norm_num)
    rw [hmax, Real.log_one]
    nlinarith only [hmain, hμ1, h611, hΩLg]
  have hV : Real.log (max (6 * Sl) (4 * μ) + 1) ≤ 7 * Ω * Lg := by
    have hvpos : 0 < max (6 * Sl) (4 * μ) + 1 := by
      have : 4 * μ ≤ max (6 * Sl) (4 * μ) := le_max_right _ _
      linarith
    have hvle : max (6 * Sl) (4 * μ) ≤ 12 * 10 ^ 10 :=
      max_le (by linarith only [hslow]) (by linarith only [hμ1])
    have h := Real.log_le_sub_one_of_pos hvpos
    have h12 : (12 * 10 ^ 10 : ℝ) ≤ Ω := le_trans (by norm_num) hΩ22
    nlinarith only [h, hvle, h12, hΩLg]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (max_le (max_le hU₁ hU₂) hV)) (by positivity)

/-- **Closed form of the sharp-location height.** For `1 < λ ≤ 2` and `c ≥ 0`, the starting height
of the cubic-logarithmic location theorem is at most `2π exp(sharpLocationLogHeight λ c)`. -/
theorem zetaNegativeCameraHeight_le {lam c : ℝ} (hlam : 1 < lam) (hlam2 : lam ≤ 2) (hc : 0 ≤ c) :
    zetaNegativeCameraHeight lam c ≤ 2 * π * Real.exp (sharpLocationLogHeight lam c) := by
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_d2
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = lam / 2 := ⟨_, rfl⟩
  have hμ1 : 1 / 2 < μ := by rw [hμ]; linarith
  have hμ2 : μ ≤ 1 := by rw [hμ]; linarith
  have hμ0 : 0 < μ := by linarith
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = μ + 1 / 2 := ⟨_, rfl⟩
  have hθ1 : 1 < θ := by rw [hθ]; linarith
  have hθ2 : θ ≤ 3 / 2 := by rw [hθ]; linarith
  have hA0 : 0 ≤ zetaCameraCountConstant θ := zetaCameraCountConstant_nonneg hθ1
  have hA1 : zetaCameraCountConstant θ ≤ 802 := zetaCameraCountConstant_le hθ1 hθ2
  have hℓ0 : 0 ≤ 2 * π * zetaCameraCountConstant θ / μ := by positivity
  have hℓ1 : 2 * π * zetaCameraCountConstant θ / μ ≤ 10150 := by
    rw [div_le_iff₀ hμ0]
    have h1 : 2 * π * zetaCameraCountConstant θ ≤ 2 * 3.15 * 802 :=
      mul_le_mul (by linarith) hA1 hA0 (by norm_num)
    norm_num at h1
    linarith only [h1, hμ1]
  have hs0 : 0 ≤ slackBound (2 * π * zetaCameraCountConstant θ / μ) := by
    unfold slackBound; linarith only [hℓ0]
  have hs1 : slackBound (2 * π * zetaCameraCountConstant θ / μ) ≤ 5100 := by
    unfold slackBound; linarith only [hℓ1]
  have hslow : slowExponent μ + 2 ≤ 8 := by
    unfold slowExponent
    nlinarith only [hμ2, hμ0, hpi4]
  have hslow0 : 0 ≤ slowExponent μ + 2 := by
    unfold slowExponent; positivity
  have hcl : zetaClusterCountConstant μ ≤ 803 := by
    unfold zetaClusterCountConstant
    have : (μ + 1 / 2) / π ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have hA1' : zetaCameraCountConstant (μ + 1 / 2) ≤ 802 := by rw [← hθ]; exact hA1
    linarith only [this, hA1']
  have hcl0 := zetaClusterCountConstant_nonneg hμ1
  obtain ⟨Lη, hLη⟩ : ∃ L, L = c + 2 + 8 * (slowExponent μ + 2) * zetaClusterCountConstant μ :=
    ⟨_, rfl⟩
  have hLη0 : 0 ≤ Lη := by rw [hLη]; positivity
  have hLη1 : Lη ≤ c + 51394 := by
    have : (slowExponent μ + 2) * zetaClusterCountConstant μ ≤ 8 * 803 :=
      mul_le_mul hslow hcl hcl0 (by norm_num)
    rw [hLη, show c + 2 + 8 * (slowExponent μ + 2) * zetaClusterCountConstant μ =
      c + 2 + 8 * ((slowExponent μ + 2) * zetaClusterCountConstant μ) by ring]
    linarith only [this]
  have hΩ : 22 * 10 ^ 16 * (1 + Lη) ≤ sharpLocationScale c := by
    unfold sharpLocationScale
    nlinarith only [hLη1]
  have hΩ22 := sharpLocationScale_ge hc
  have hcam := cameraCubicIsolationHeight_le hμ hθ hlam hlam2 hs0 hs1 hLη0 hΩ hΩ22
  have hmaxlog : 7 * sharpLocationScale c *
      Real.log (792 * sharpLocationScale c ^ 2 / (lam - 1)) ≤ sharpLocationLogHeight lam c :=
    le_max_right _ _
  have hfrac : 4 / (lam - 1) ≤ sharpLocationLogHeight lam c := le_max_left _ _
  have hl0 : 0 < lam - 1 := by linarith
  have hfrac1 : 4 ≤ sharpLocationLogHeight lam c := by
    refine le_trans ?_ hfrac
    rw [le_div_iff₀ hl0]; linarith
  have h20 : (20 : ℝ) ≤ 2 * π * Real.exp (sharpLocationLogHeight lam c) := by
    have hexp := Real.add_one_le_exp (sharpLocationLogHeight lam c)
    nlinarith only [hexp, hfrac1, hpi3]
  have hcount : zetaCameraCountHeight θ ≤ 2 * π * Real.exp (sharpLocationLogHeight lam c) := by
    unfold zetaCameraCountHeight
    refine max_le h20 (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
    refine max_le (by linarith only [hfrac1]) ?_
    have : 2 / (θ - 1) = 4 / (lam - 1) := by
      rw [hθ, hμ, show lam / 2 + 1 / 2 - 1 = (lam - 1) / 2 by ring]
      field_simp
      norm_num
    rw [this]; exact hfrac
  have hdef : zetaNegativeCameraHeight lam c =
      max (zetaCameraCountHeight θ) (cameraCubicIsolationHeight θ μ
        (zetaCameraCountConstant θ) (33 / 100) Lη) := by
    subst hLη hθ hμ
    rfl
  rw [hdef]
  refine max_le hcount (hcam.trans ?_)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmaxlog) (by positivity)

/-- **Sharp location with a closed-form height.** Positivity at aperture `a` confines every zero
with `T₀(c) ≤ |γ| ≤ 2π e^{a}` to depth `< exp(−c log³|γ|)`, where
`T₀(c) = 2π exp(sharpLocationLogHeight 2 (8c))`. -/
theorem zeta_depth_lt_of_positive_aperture_closed_form {c T a : ℝ} (hc : 0 ≤ c)
    (hT : 2 * π * Real.exp (sharpLocationLogHeight 2 (8 * c)) ≤ T)
    (hheight : T ≤ 2 * π * Real.exp a)
    (hpos : ∀ f : ℝ → ℂ, ApertureWindow a f → 0 ≤ (zetaZeroConfig.W f f).re) :
    ∀ p ∈ zetaZeroConfig.carrier, |p.im| = T →
      |depth p| < Real.exp (-(c * Real.log T ^ 3)) := by
  have hheight' : T ≤ 2 * π * Real.exp (2 * a / 2) := by
    rwa [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  refine zeta_depth_lt_exp_log_cube_of_positive_aperture_abs (lam := 2) (by norm_num) hc ?_
    hheight' hpos
  refine max_le ((zetaNegativeCameraHeight_le (by norm_num) le_rfl (by positivity)).trans hT) ?_
  refine le_trans ?_ hT
  have h4 : (4 : ℝ) ≤ sharpLocationLogHeight 2 (8 * c) := by
    have h : (4 : ℝ) / (2 - 1) ≤ sharpLocationLogHeight 2 (8 * c) := le_max_left _ _
    norm_num at h
    linarith only [h]
  have he2 : 3 ≤ Real.exp 2 := by linarith only [Real.add_one_le_exp (2 : ℝ)]
  have he4 : 9 ≤ Real.exp 4 := by
    have : Real.exp 4 = Real.exp 2 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
    rw [this]
    nlinarith only [he2]
  have hpi : (2 * π) ≤ Real.exp (sharpLocationLogHeight 2 (8 * c)) := by
    linarith only [he4, Real.exp_le_exp.mpr h4, Real.pi_lt_d2]
  calc (2 * π) ^ 2 = 2 * π * (2 * π) := by ring
    _ ≤ 2 * π * Real.exp (sharpLocationLogHeight 2 (8 * c)) :=
        mul_le_mul_of_nonneg_left hpi (by positivity)

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zetaNegativeCameraHeight_le
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zeta_depth_lt_of_positive_aperture_closed_form
