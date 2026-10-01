import GaloisForLFunctions.RHTower.ReflectedCompactComplementConductor
import GaloisForLFunctions.RHTower.SteinhausCompactReflectedComplement

open Complex Filter Topology Set Metric MeasureTheory
noncomputable section
namespace RHTower

/-- One original coefficient envelope holds throughout a fixed right-strip disc
and every physical height in the full dyadic conductor window. -/
theorem exists_norm_reflectedComplementCoefficient_le_conductor_disc
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 < c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ tau ∈ Icc (N : ℝ) (2 * N),
      ∀ s ∈ closedBall c r, ∀ n : ℕ,
        ‖smoothAFEZetaRightComplementCoefficient (s.re - 1 / 2) (s.im + tau) N n‖ ≤
          C * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_reflectedComplementCoefficient_le_conductor_band
    (d₀ := c.re + r - 1 / 2) (by linarith) (by linarith)
  refine ⟨C, hC, ?_⟩
  have hlarge : ∀ᶠ N : ℕ in atTop, 2 * (|c.im| + r + 1) ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hlarge] with N hN
  have hNR : (0 : ℝ) < N := by linarith [abs_nonneg c.im]
  intro tau htau s hs n
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
  apply hbound (s.re - 1 / 2) (by linarith [(abs_le.mp hre).1])
    (by linarith [(abs_le.mp hre).2]) N (by linarith [abs_nonneg c.im]) (s.im + tau)
  · have hlow : (N : ℝ) / 2 ≤ s.im + tau := by
      linarith [(abs_le.mp himabs).1, htau.1]
    exact hlow.trans ((le_abs_self _).trans (le_max_right _ _))
  · apply max_le
    · linarith [abs_nonneg c.im]
    · have h := abs_add_le s.im tau
      rw [abs_of_nonneg htau0] at h
      linarith [htau.2, abs_nonneg c.im]

/-- The complete holomorphic reciprocal complement stays uniformly bounded on
one fixed disc, over all phases and the actual conductor windows. -/
theorem exists_norm_steinhausCompactReflectedComplement_le_disc
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 < c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ tau ∈ Icc (N : ℝ) (2 * N),
      ∀ s ∈ closedBall c r, ∀ ω : SteinhausModel.Omega,
        ‖steinhausCompactReflectedComplement (s + (tau : ℂ) * I) N ω‖ ≤ C := by
  obtain ⟨C, hC, hcoeff⟩ := exists_norm_reflectedComplementCoefficient_le_conductor_disc c hr hc0 hc1
  let M : ℝ := ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)
  have hM : 0 ≤ M := tsum_nonneg (fun _ => by positivity)
  refine ⟨C * M, mul_nonneg hC hM, ?_⟩
  filter_upwards [hcoeff, eventually_ge_atTop (1 : ℕ)] with N hcoeffN hN
  intro tau htau s hs ω
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hre : |s.re - c.re| ≤ r := by
    have hrc : |s.re - c.re| ≤ dist s c := by
      simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s-c)
    exact hrc.trans hs
  have hd : 0 < s.re - 1 / 2 := by linarith [(abs_le.mp hre).1]
  have hdhalf : s.re - 1 / 2 < 1 / 2 := by linarith [(abs_le.mp hre).2]
  have hrepr : rightDisplacedLinePt (s.re - 1 / 2) (s.im + tau) = s + (tau : ℂ) * I := by
    apply Complex.ext <;> simp [rightDisplacedLinePt]
  rw [← hrepr, ← steinhausFullReflectedComplement_eq_compact hd hdhalf hNR]
  let a : ℕ → ℂ := fun n =>
    smoothAFEZetaRightComplementCoefficient (s.re - 1 / 2) (s.im + tau) N n *
      starRingEnd ℂ (SteinhausModel.X (n + 1) ω)
  have hmajor : Summable (fun n : ℕ => C * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ))) :=
    (summable_smoothAFEZetaMajorant (by norm_num : (1 : ℝ) < 9 / 2)).mul_left C
  have hb (n : ℕ) : ‖a n‖ ≤ C * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) := by
    simpa only [a, norm_mul, RCLike.norm_conj, SteinhausModel.norm_X, mul_one] using
      hcoeffN tau htau s hs n
  have ha : Summable (fun n => ‖a n‖) := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hmajor
  change ‖∑' n, a n‖ ≤ C * M
  calc
    _ ≤ ∑' n, ‖a n‖ := norm_tsum_le_tsum_norm ha
    _ ≤ ∑' n : ℕ, C * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) := ha.tsum_le_tsum hb hmajor
    _ = C * M := by rw [tsum_mul_left]

end RHTower

