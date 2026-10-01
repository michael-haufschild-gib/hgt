import GaloisForLFunctions.RHTower.ReflectedCompactComplementDisc
import GaloisForLFunctions.RHTower.SteinhausReciprocalSeriesStability

open Complex Filter Topology Set Metric
noncomputable section
namespace RHTower
open SteinhausModel

/-- One fixed character prefix controls the complete holomorphic complement
uniformly over the whole disc, every reference phase and all conductor windows. -/
theorem exists_steinhausCompactReflectedComplement_character_tolerance
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 < c.re - r) (hc1 : c.re + r < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, 1 ≤ B ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ tau ∈ Icc (N : ℝ) (2 * N), ∀ s ∈ closedBall c r, ∀ ω η : Omega,
        η ∈ steinhausCharacterCell B ω δ →
          ‖steinhausCompactReflectedComplement (s + (tau : ℂ) * I) N η -
            steinhausCompactReflectedComplement (s + (tau : ℂ) * I) N ω‖ < ε := by
  obtain ⟨C, hC, hcoeff⟩ := exists_norm_reflectedComplementCoefficient_le_conductor_disc c hr hc0 hc1
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hcoeff
  let J := {q : ℕ × ℝ × ℂ // N₀ ≤ q.1 ∧
    q.2.1 ∈ Icc (q.1 : ℝ) (2 * q.1) ∧ q.2.2 ∈ closedBall c r}
  let a : J → ℕ → ℂ := fun q n => smoothAFEZetaRightComplementCoefficient
    (q.1.2.2.re - 1 / 2) (q.1.2.2.im + q.1.2.1) q.1.1 n
  let u : ℕ → ℝ := fun n => C * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ))
  have hu0 : ∀ n, 0 ≤ u n := by intro n; dsimp only [u]; positivity
  have hu : Summable u := (summable_smoothAFEZetaMajorant (by norm_num : (1 : ℝ) < 9 / 2)).mul_left C
  have hb : ∀ q : J, ∀ n, ‖a q n‖ ≤ u n := by
    intro q n
    exact hN₀ q.1.1 q.2.1 q.1.2.1 q.2.2.1 q.1.2.2 q.2.2.2 n
  obtain ⟨B, hB, δ, hδ, hcell⟩ := exists_steinhaus_reciprocalSeries_character_tolerance a hu0 hu hb hε
  refine ⟨B, hB, δ, hδ, ?_⟩
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop (1 : ℕ)] with N hN hN1
  intro tau htau s hs ω η hη
  let q : J := ⟨(N, tau, s), hN, htau, hs⟩
  have hre : |s.re - c.re| ≤ r := by
    have hrc : |s.re - c.re| ≤ dist s c := by
      simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s-c)
    exact hrc.trans hs
  have hd : 0 < s.re - 1 / 2 := by linarith [(abs_le.mp hre).1]
  have hdhalf : s.re - 1 / 2 < 1 / 2 := by linarith [(abs_le.mp hre).2]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hrepr : rightDisplacedLinePt (s.re - 1 / 2) (s.im + tau) = s + (tau : ℂ) * I := by
    apply Complex.ext <;> simp [rightDisplacedLinePt]
  rw [← hrepr, ← steinhausFullReflectedComplement_eq_compact hd hdhalf hNR,
    ← steinhausFullReflectedComplement_eq_compact hd hdhalf hNR]
  exact hcell q ω η hη

end RHTower

