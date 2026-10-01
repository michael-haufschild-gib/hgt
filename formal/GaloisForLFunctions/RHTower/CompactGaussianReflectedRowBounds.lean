import GaloisForLFunctions.RHTower.SmoothAFEReflectedCompactChannel
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiUniformMovingRightLine
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiUniformMovingLeftLine

open Complex Set Filter Metric
noncomputable section
namespace RHTower

/-- Exact conductor cancellation in the common reflected row. -/
theorem norm_reflectedCompactGaussianRow (s : ℂ) {N : ℝ} (hN : 0 < N) (tau : ℝ) :
    ‖reflectedCompactGaussianRow s N tau‖ =
      ‖zetaChi (s + (tau : ℂ) * I)‖ * N ^ (s.re - 1 / 2) := by
  unfold reflectedCompactGaussianRow
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_cpow_eq_rpow_re_of_pos hN,
    Complex.sub_re, Complex.one_re, Real.sqrt_eq_rpow]
  rw [mul_comm (N ^ (1 / 2 : ℝ)) ‖zetaChi (s + (tau : ℂ) * I)‖,
    mul_assoc, ← Real.rpow_add hN]
  congr 2
  ring

/-- The common row is nonzero throughout the open critical strip. -/
theorem reflectedCompactGaussianRow_ne_zero {s : ℂ} {N : ℝ} (hN : 0 < N)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (tau : ℝ) :
    reflectedCompactGaussianRow s N tau ≠ 0 := by
  have hre : (s + (tau : ℂ) * I).re = s.re := by simp
  unfold reflectedCompactGaussianRow
  apply mul_ne_zero
  · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hN).ne')
      (zetaChi_ne_zero_of_mem_openStrip (by rwa [hre]) (by rwa [hre]))
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))

/-- Both the literal row and its inverse are holomorphic on the open strip. -/
theorem differentiableOn_reflectedCompactGaussianRow_and_inv {N : ℝ} (hN : 0 < N) (tau : ℝ) :
    DifferentiableOn ℂ (fun s => reflectedCompactGaussianRow s N tau) {s | 0 < s.re ∧ s.re < 1} ∧
    DifferentiableOn ℂ (fun s => (reflectedCompactGaussianRow s N tau)⁻¹) {s | 0 < s.re ∧ s.re < 1} := by
  have hrow : DifferentiableOn ℂ (fun s => reflectedCompactGaussianRow s N tau)
      {s | 0 < s.re ∧ s.re < 1} := by
    intro s hs
    have hchi : DifferentiableAt ℂ zetaChi (s + (tau : ℂ) * I) :=
      (zetaChi_analyticAt (Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using sub_pos.mpr hs.2))).differentiableAt
    have hpow : Differentiable ℂ (fun s : ℂ => (N : ℂ) ^ (s - 1)) :=
      (differentiable_id.sub_const 1).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))
    exact (((hchi.comp s (differentiable_id.add_const _).differentiableAt).const_mul _).mul
      hpow.differentiableAt).differentiableWithinAt
  exact ⟨hrow, hrow.inv (fun s hs => reflectedCompactGaussianRow_ne_zero hN hs.1 hs.2 tau)⟩

/-- Uniform bounds for the row and inverse throughout a moving right band when
physical height stays comparable with the exact conductor scale. -/
theorem exists_reflectedCompactGaussianRow_band_bounds {d₀ : ℝ}
    (hd₀0 : 0 ≤ d₀) (hd₀half : d₀ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 / 2 + d₀ →
      ∀ N : ℝ, 0 < N → ∀ tau : ℝ,
        N / 2 ≤ max 1 |s.im + tau| → max 1 |s.im + tau| ≤ 3 * N →
        ‖reflectedCompactGaussianRow s N tau‖ ≤ C ∧
        ‖(reflectedCompactGaussianRow s N tau)⁻¹‖ ≤ C := by
  obtain ⟨Kr, hKr, hr⟩ := exists_norm_zetaChi_moving_right_line_le_rpow hd₀0 hd₀half
  obtain ⟨Kl, hKl, hl⟩ := exists_norm_zetaChi_moving_left_line_le_rpow hd₀0 hd₀half
  refine ⟨2 * Kr + 3 * Kl + 1, by positivity, ?_⟩
  intro s hs0 hs1 N hN tau hlow hupp
  let d : ℝ := s.re - 1 / 2
  let T : ℝ := max 1 |s.im + tau|
  have hd : 0 ≤ d := sub_nonneg.mpr hs0
  have hdd₀ : d ≤ d₀ := by dsimp only [d]; linarith
  have hd1 : d ≤ 1 := by linarith
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hrepr : s + (tau : ℂ) * I = (((1 / 2 + d : ℝ) : ℂ) + ((s.im + tau : ℝ) : ℂ) * I) := by
    apply Complex.ext <;> simp [d]
  have hreflect : 1 - (s + (tau : ℂ) * I) =
      (((1 / 2 - d : ℝ) : ℂ) + ((-(s.im + tau) : ℝ) : ℂ) * I) := by
    apply Complex.ext <;> simp [d]
    ring
  have hupper : ‖zetaChi (s + (tau : ℂ) * I)‖ ≤ Kr / T ^ d := by
    rw [hrepr]
    exact hr d hd hdd₀ _
  have hinv : (zetaChi (s + (tau : ℂ) * I))⁻¹ = zetaChi (1 - (s + (tau : ℂ) * I)) :=
    inv_eq_of_mul_eq_one_right (zetaChi_mul_one_sub_of_mem_strip
      (by simp; linarith) (by simp; linarith))
  have hinvupper : ‖(zetaChi (s + (tau : ℂ) * I))⁻¹‖ ≤ Kl * T ^ d := by
    rw [hinv, hreflect]
    simpa only [abs_neg] using hl d hd hdd₀ (-(s.im + tau))
  have hratio1 : (N / T) ^ d ≤ 2 := by
    have hbase : N / T ≤ 2 := (div_le_iff₀ hT).mpr (by dsimp only [T]; linarith)
    exact (Real.rpow_le_rpow (by positivity) hbase hd).trans
      (by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hd1)
  have hratio2 : (T / N) ^ d ≤ 3 := by
    have hbase : T / N ≤ 3 := (div_le_iff₀ hN).mpr (by dsimp only [T]; linarith)
    exact (Real.rpow_le_rpow (by positivity) hbase hd).trans
      (by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hd1)
  constructor
  · rw [norm_reflectedCompactGaussianRow s hN tau]
    change ‖zetaChi (s + (tau : ℂ) * I)‖ * N ^ d ≤ _
    calc
      _ ≤ (Kr / T ^ d) * N ^ d := mul_le_mul_of_nonneg_right hupper (by positivity)
      _ = Kr * (N / T) ^ d := by rw [Real.div_rpow hN.le hT.le]; ring
      _ ≤ Kr * 2 := mul_le_mul_of_nonneg_left hratio1 hKr
      _ ≤ _ := by linarith
  · have hnorminv : ‖(reflectedCompactGaussianRow s N tau)⁻¹‖ =
        ‖(zetaChi (s + (tau : ℂ) * I))⁻¹‖ / N ^ d := by
      rw [norm_inv, norm_reflectedCompactGaussianRow s hN tau, norm_inv]
      dsimp only [d]
      rw [mul_inv_rev]
      ring
    rw [hnorminv]
    calc
      _ ≤ (Kl * T ^ d) / N ^ d := div_le_div_of_nonneg_right hinvupper (by positivity)
      _ = Kl * (T / N) ^ d := by rw [Real.div_rpow hT.le hN.le]; ring
      _ ≤ Kl * 3 := mul_le_mul_of_nonneg_left hratio2 hKl
      _ ≤ _ := by linarith

/-- On every fixed right-strip disc, one bound controls the row and inverse
throughout the actual dyadic physical-height window for every large conductor. -/
theorem exists_reflectedCompactGaussianRow_disc_bounds
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ tau ∈ Icc (N : ℝ) (2 * N),
      ∀ s ∈ closedBall c r, ‖reflectedCompactGaussianRow s N tau‖ ≤ C ∧
        ‖(reflectedCompactGaussianRow s N tau)⁻¹‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_reflectedCompactGaussianRow_band_bounds
    (d₀ := c.re + r - 1 / 2) (by linarith) (by linarith)
  refine ⟨C, hC, ?_⟩
  have hlarge : ∀ᶠ N : ℕ in atTop, 2 * (|c.im| + r + 1) ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hlarge] with N hN
  have hNR : (0 : ℝ) < N := by linarith [abs_nonneg c.im]
  intro tau htau s hs
  have hd : dist s c ≤ r := hs
  have hre0 : |s.re - c.re| ≤ dist s c := by
    simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c)
  have him0 : |s.im - c.im| ≤ dist s c := by
    simpa only [Complex.sub_im, dist_eq_norm] using Complex.abs_im_le_norm (s - c)
  have hre := hre0.trans hd
  have him := him0.trans hd
  have himabs : |s.im| ≤ |c.im| + r := by
    have h := abs_add_le (s.im - c.im) c.im
    rw [sub_add_cancel] at h
    linarith
  have htau0 : 0 ≤ tau := hNR.le.trans htau.1
  apply hbound s (by linarith [(abs_le.mp hre).1])
    (by linarith [(abs_le.mp hre).2]) N hNR tau
  · have hlow : (N : ℝ) / 2 ≤ s.im + tau := by
      linarith [(abs_le.mp himabs).1, htau.1]
    exact hlow.trans ((le_abs_self _).trans (le_max_right _ _))
  · apply max_le
    · linarith [abs_nonneg c.im]
    · have h := abs_add_le s.im tau
      rw [abs_of_nonneg htau0] at h
      linarith [htau.2, abs_nonneg c.im]

end RHTower
