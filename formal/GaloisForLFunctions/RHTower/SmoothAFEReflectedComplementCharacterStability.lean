import GaloisForLFunctions.RHTower.SmoothAFEReflectedComplementTail
import GaloisForLFunctions.RHTower.SteinhausFiniteCharacterCells
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter Topology Finset
noncomputable section
namespace RHTower
open SteinhausModel

private def reflectedComplementHead (d tau N : ℝ) (B : ℕ) (ω : Omega) : ℂ :=
  ∑ n ∈ range B, smoothAFEZetaRightComplementCoefficient d tau N n *
    starRingEnd ℂ (X (n + 1) ω)

/-- A fixed finite-character cell controls the entire literal complementary series uniformly
throughout the conductor window. Both infinite tails retain their original reciprocal phases. -/
theorem exists_fullReflectedComplement_character_tolerance
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, 1 ≤ B ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℝ, 1 ≤ N → ∀ tau : ℝ, N ≤ tau → tau ≤ 2 * N →
      ∀ ω η : Omega, η ∈ steinhausCharacterCell B ω δ →
        ‖steinhausFullReflectedComplement d tau N η -
          steinhausFullReflectedComplement d tau N ω‖ < ε := by
  obtain ⟨D, hD, htail⟩ := exists_norm_steinhausReflectedComplement_sub_head_le hd hdhalf
  have hpow : Tendsto (fun B : ℕ => (B : ℝ) ^ (-(7 / 2 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 2)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun B : ℕ => (B : ℝ)) atTop atTop)
  have hlim : Tendsto (fun B : ℕ => D * ((B : ℝ) ^ (-(7 / 2 : ℝ)) / (7 / 2 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [zero_div, mul_zero] using (hpow.div_const (7 / 2 : ℝ)).const_mul D
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp (hlim.eventually
    (Iio_mem_nhds (by positivity : 0 < ε / 4)))
  let B := max 1 B₀
  have hB : 1 ≤ B := le_max_left _ _
  obtain ⟨C, hC, hpoint⟩ := exists_norm_reflectedComplementCoefficient_le_conductor hd hdhalf
  let K : ℝ := 1 + B * C
  have hK : 0 < K := by dsimp only [K]; positivity
  let δ := ε / (4 * K)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  refine ⟨B, hB, δ, hδ, ?_⟩
  intro N hN tau hNt htN ω η hcell
  have hcoeff (n : ℕ) : ‖smoothAFEZetaRightComplementCoefficient d tau N n‖ ≤ C := by
    have hn : (1 : ℝ) ≤ n + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    have hp : (1 : ℝ) ≤ (n + 1 : ℝ) ^ (9 / 2 : ℝ) :=
      Real.one_le_rpow hn (by norm_num)
    exact (hpoint N hN tau hNt htN n).trans (by
      nlinarith [mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp) hC])
  have hhead : ‖reflectedComplementHead d tau N B η -
      reflectedComplementHead d tau N B ω‖ ≤ ε / 4 := by
    have heq : reflectedComplementHead d tau N B η - reflectedComplementHead d tau N B ω =
        ∑ n ∈ range B, smoothAFEZetaRightComplementCoefficient d tau N n *
          starRingEnd ℂ (X (n + 1) η - X (n + 1) ω) := by
      simp only [reflectedComplementHead, ← sum_sub_distrib, map_sub, mul_sub]
    rw [heq]
    calc
      _ ≤ ∑ n ∈ range B, ‖smoothAFEZetaRightComplementCoefficient d tau N n *
          starRingEnd ℂ (X (n + 1) η - X (n + 1) ω)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ range B, C * δ := by
        apply sum_le_sum
        intro n hn
        rw [norm_mul, RCLike.norm_conj]
        have hx := (hcell (n + 1) (mem_Icc.mpr ⟨by omega, by have := mem_range.mp hn; omega⟩)).le
        exact mul_le_mul (hcoeff n) hx (norm_nonneg _) hC
      _ = (B : ℝ) * C * δ := by
        simp only [sum_const, card_range, nsmul_eq_mul]
        ring
      _ ≤ K * δ := mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) hδ.le
      _ = ε / 4 := by dsimp only [δ]; field_simp [hK.ne']
  have htailQuarter (ξ : Omega) : ‖steinhausFullReflectedComplement d tau N ξ -
      reflectedComplementHead d tau N B ξ‖ < ε / 4 :=
    (htail N hN tau hNt htN ξ B hB).trans_lt (hB₀ B (le_max_right _ _))
  have heq : steinhausFullReflectedComplement d tau N η - steinhausFullReflectedComplement d tau N ω =
      (steinhausFullReflectedComplement d tau N η - reflectedComplementHead d tau N B η) +
      (reflectedComplementHead d tau N B η - reflectedComplementHead d tau N B ω) +
      (reflectedComplementHead d tau N B ω - steinhausFullReflectedComplement d tau N ω) := by ring
  have htri := (norm_add_le
    ((steinhausFullReflectedComplement d tau N η - reflectedComplementHead d tau N B η) +
      (reflectedComplementHead d tau N B η - reflectedComplementHead d tau N B ω))
    (reflectedComplementHead d tau N B ω - steinhausFullReflectedComplement d tau N ω)).trans
      (add_le_add (norm_add_le _ _) (le_refl _))
  rw [← heq, norm_sub_rev (reflectedComplementHead d tau N B ω)
    (steinhausFullReflectedComplement d tau N ω)] at htri
  linarith [htailQuarter η, htailQuarter ω]

end RHTower
