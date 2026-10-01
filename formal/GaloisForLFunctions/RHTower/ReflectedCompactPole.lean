import GaloisForLFunctions.RHTower.CompactGaussianReflectedRowBounds
import GaloisForLFunctions.RHTower.SmoothAFEZetaResidueDecomposition

open Complex Filter Topology Set Metric
noncomputable section
namespace RHTower

/-- The original reflected pole in complex spectral coordinates. -/
def reflectedCompactPole (z : ℂ) (N : ℝ) : ℂ :=
  zetaChi z * smoothAFEZetaShiftedPoleResidue (1 - z) N

/-- Exact pole formula, with its original denominator. -/
theorem reflectedCompactPole_eq (z : ℂ) (N : ℝ) :
    reflectedCompactPole z N = zetaChi z * (N : ℂ) ^ z * Complex.exp (z ^ 2) / z := by
  simp [reflectedCompactPole, smoothAFEZetaShiftedPoleResidue, mul_div_assoc, mul_assoc]

/-- The pole correction is holomorphic throughout the open unit strip. -/
theorem differentiableOn_reflectedCompactPole {N : ℝ} (hN : 0 < N) :
    DifferentiableOn ℂ (fun z => reflectedCompactPole z N) {z : ℂ | 0 < z.re ∧ z.re < 1} := by
  have heq : (fun z => reflectedCompactPole z N) =
      fun z => zetaChi z * (N : ℂ) ^ z * Complex.exp (z ^ 2) / z :=
    funext (fun z => reflectedCompactPole_eq z N)
  rw [heq]
  intro z hz
  have hchi : DifferentiableAt ℂ zetaChi z := by
    apply (zetaChi_analyticAt ?_).differentiableAt
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.sub_re, Complex.one_re]
    exact sub_pos.mpr hz.2
  have hpow : Differentiable ℂ (fun z : ℂ => (N : ℂ) ^ z) :=
    differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))
  have hne : z ≠ 0 := by intro h; have := hz.1; simp [h] at this
  exact (((hchi.mul hpow.differentiableAt).mul
    ((differentiable_id.differentiableAt.pow 2).cexp)).div
      differentiable_id.differentiableAt hne).differentiableWithinAt

/-- The complex pole agrees with the unchanged pole in the original reflected AFE. -/
theorem reflectedCompactPole_rightDisplacedLinePt (d tau N : ℝ) :
    reflectedCompactPole (rightDisplacedLinePt d tau) N =
      zetaChi (rightDisplacedLinePt d tau) *
        smoothAFEZetaShiftedPoleResidue (displacedLinePt d (-tau)) N := by
  unfold reflectedCompactPole
  congr 2
  unfold rightDisplacedLinePt displacedLinePt
  push_cast
  ring

/-- The exact reflected pole stays uniformly bounded on every fixed right-strip
 disc over all sufficiently large dyadic conductor windows. -/
theorem exists_norm_reflectedCompactPole_le_disc
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ tau ∈ Icc (N : ℝ) (2 * N),
      ∀ s ∈ closedBall c r, ‖reflectedCompactPole (s + (tau : ℂ) * I) N‖ ≤ C := by
  obtain ⟨K, hK, hrow⟩ := exists_reflectedCompactGaussianRow_disc_bounds c hr hc0 hc1
  refine ⟨K * 2 * Real.exp 1, by positivity, ?_⟩
  have hlarge : ∀ᶠ N : ℕ in atTop, 2 * (|c.im| + r + 1) ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hrow, hlarge] with N hrowN hlargeN
  have hN1 : (1 : ℝ) ≤ N := by linarith [abs_nonneg c.im]
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  intro tau htau s hs
  have hd : dist s c ≤ r := hs
  have hre : |s.re - c.re| ≤ r := by
    have h : |s.re - c.re| ≤ dist s c := by
      simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s-c)
    exact h.trans hd
  have him : |s.im - c.im| ≤ r := by
    have h : |s.im - c.im| ≤ dist s c := by
      simpa only [Complex.sub_im, dist_eq_norm] using Complex.abs_im_le_norm (s-c)
    exact h.trans hd
  have hs0 : 0 ≤ s.re := by linarith [(abs_le.mp hre).1]
  have hs1 : s.re ≤ 1 := by linarith [(abs_le.mp hre).2]
  have hlow : (N : ℝ) / 2 ≤ s.im + tau := by
    linarith [(abs_le.mp him).1, le_abs_self (-c.im), abs_neg c.im, htau.1]
  let z : ℂ := s + (tau : ℂ) * I
  have hzre : z.re = s.re := by simp [z]
  have hzim : z.im = s.im + tau := by simp [z]
  have hden : (N : ℝ) / 2 ≤ ‖z‖ := by
    exact hlow.trans (by rw [← hzim]; exact (le_abs_self _).trans (Complex.abs_im_le_norm z))
  have hdenpos : 0 < ‖z‖ := lt_of_lt_of_le (half_pos hNpos) hden
  have hroot : Real.sqrt N / ‖z‖ ≤ 2 := by
    apply (div_le_iff₀ hdenpos).mpr
    exact (Real.sqrt_le_self_iff.mpr (Or.inr hN1)).trans (by linarith)
  have hexp : ‖Complex.exp (z ^ 2)‖ ≤ Real.exp 1 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    rw [pow_two, Complex.mul_re, hzre]
    nlinarith [sq_nonneg z.im]
  have hscale : (N : ℝ) ^ (s.re - 1 / 2) * Real.sqrt N = (N : ℝ) ^ s.re := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNpos]
    congr 1
    ring
  have hrowbound : ‖zetaChi z‖ * (N : ℝ) ^ (s.re - 1 / 2) ≤ K := by
    have h := (hrowN tau htau s hs).1
    rw [norm_reflectedCompactGaussianRow _ hNpos] at h
    exact h
  change ‖reflectedCompactPole z N‖ ≤ K * 2 * Real.exp 1
  rw [reflectedCompactPole_eq, norm_div, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hNpos, hzre, ← hscale]
  calc
    _ ≤ (‖zetaChi z‖ * ((N : ℝ) ^ (s.re - 1 / 2) * Real.sqrt N) * Real.exp 1) / ‖z‖ := by
      gcongr
    _ = (‖zetaChi z‖ * (N : ℝ) ^ (s.re - 1 / 2)) * (Real.sqrt N / ‖z‖) * Real.exp 1 := by ring
    _ ≤ _ := by gcongr

end RHTower

