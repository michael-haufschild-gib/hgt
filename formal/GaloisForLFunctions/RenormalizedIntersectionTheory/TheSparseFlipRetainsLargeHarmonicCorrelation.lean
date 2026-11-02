import GaloisForLFunctions.RenormalizedIntersectionTheory.TheWirsingConstantOfAFlipTwinIsPositive

/-!
# Sparse flips retain cofinal large harmonic correlation

Only a lower bound for the signed prime mean is needed to rule out a small harmonic sum.
The Euler product gives a larger pole exponent than Abel summation would allow. In particular,
zero relative logarithmic density forces cofinal growth beyond every sublinear logarithmic
power, without a power-saving error term or a positive Euler-density assumption.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.ArithmeticCountingPositivity
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- A one-sided prime mean already excludes every smaller harmonic growth exponent. -/
theorem exists_gaugeHarmonicSum_gt_rpow_of_primeMean_lower {ω : ℕ → ℝ}
    (hω : IsSignGauge ω) {β C α : ℝ} (hα : 0 ≤ α) (hαβ : α < β) (hα1 : α < 1)
    (hA : ∀ n : ℕ, 1 ≤ n → β * Real.log n - C ≤ primeMean ω n) (G : ℝ) :
    ∃ N : ℕ, G * (1 + Real.log N) ^ α < gaugeHarmonicSum ω N := by
  by_contra hcon
  push Not at hcon
  set G' := max G 1
  have hG' : 0 ≤ G' := zero_le_one.trans (le_max_right _ _)
  have hL : ∀ n, gaugeHarmonicSum ω n ≤ G' * (1 + Real.log n) ^ α := fun n =>
    (hcon n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by linarith only [Real.log_natCast_nonneg n]) _))
  obtain ⟨C₂, hC₂⟩ := exists_primeSum_rpow_ge_rpow (ε := ω) (β := β) (C := C)
    (α := 0) (by linarith only [hα, hαβ]) (by norm_num) (by norm_num)
    (by simpa only [Real.rpow_zero, mul_one] using hA)
  have hgrow : Tendsto (fun K : ℕ => Real.log K ^ (β - α)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hαβ)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨K, hK3, hKbig⟩ := ((eventually_ge_atTop 3).and
    (hgrow.eventually_gt_atTop (2 * G' * Real.exp C₂))).exists
  have hlK : 1 ≤ Real.log K := one_le_log_of_three_le hK3
  have hlK0 : 0 < Real.log K := zero_lt_one.trans_le hlK
  have hσ : 0 < 1 / Real.log K := one_div_pos.mpr hlK0
  have hσ1 : 1 / Real.log K ≤ 1 := (div_le_one hlK0).mpr hlK
  have hup := tsum_twistedDirichletHom_le_rpow hω hσ hσ1 hG' hα hα1.le hL
  have hdown := exp_le_tsum_twistedDirichletHom hω hσ (X₀ := K + 1)
    (fun X hX => hC₂ K hK3 X hX)
  have e1 : Real.exp (β * Real.log (Real.log K) - C₂) =
      Real.log K ^ β * Real.exp (-C₂) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.rpow_def_of_pos hlK0, mul_comm β]
  have e2 : (1 / Real.log K) ^ (-α) = Real.log K ^ α := by
    rw [one_div, Real.inv_rpow hlK0.le, Real.rpow_neg hlK0.le, inv_inv]
  rw [e1] at hdown
  rw [e2] at hup
  have hsplit : Real.log K ^ β = Real.log K ^ α * Real.log K ^ (β - α) := by
    rw [← Real.rpow_add hlK0]
    congr 1
    ring
  have hpα : 0 < Real.log K ^ α := Real.rpow_pos_of_pos hlK0 α
  have hkey : Real.log K ^ (β - α) * Real.exp (-C₂) ≤ 2 * G' := by
    have h := hdown.trans hup
    rw [hsplit] at h
    have hh : Real.log K ^ α * (Real.log K ^ (β - α) * Real.exp (-C₂)) ≤
        Real.log K ^ α * (2 * G') := by nlinarith only [h]
    exact le_of_mul_le_mul_left hh hpα
  have hlarge := mul_lt_mul_of_pos_right hKbig (Real.exp_pos (-C₂))
  have hC2 : Real.exp C₂ * Real.exp (-C₂) = 1 := by
    rw [← Real.exp_add]
    simp only [add_neg_cancel, Real.exp_zero]
  rw [mul_assoc, hC2, mul_one] at hlarge
  exact (not_lt_of_ge hkey) hlarge

private theorem primeMean_lower_of_logMass_ratio_tendsto (P : Set ℕ) {κ : ℝ}
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 κ))
    {β : ℝ} (hβ : β < 1 - 2 * κ) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → β * Real.log n - C ≤ primeMean (primeSetFlip P) n := by
  let η := (1 - 2 * κ - β) / 2
  have hη : 0 < η := by dsimp only [η]; linarith only [hβ]
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (hP.eventually_le_const (show κ < κ + η by linarith only [hη]))
  let K := (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail) + 2 * (κ + η)
  let B := ∑ n ∈ range N₀, |β * Real.log n - primeMean (primeSetFlip P) n|
  have hB : 0 ≤ B := sum_nonneg fun n _ => abs_nonneg _
  refine ⟨|K| + B, fun n hn => ?_⟩
  by_cases hN : N₀ ≤ n
  · have hden : 0 < 1 + Real.log n := by linarith only [Real.log_natCast_nonneg n]
    have hmass := (div_le_iff₀ hden).mp (hN₀ n hN)
    have hmertens := (abs_le.mp (RHTower.Mertens.mertens_first_prime n hn)).1
    have hK : K ≤ |K| + B := (le_abs_self K).trans (le_add_of_nonneg_right hB)
    rw [primeMean_primeSetFlip]
    dsimp only [K, η] at hmass hK
    linarith only [hmass, hmertens, hK]
  · have hsmall : |β * Real.log n - primeMean (primeSetFlip P) n| ≤ B :=
      single_le_sum (f := fun m : ℕ => |β * Real.log m - primeMean (primeSetFlip P) m|)
        (fun m (_hm : m ∈ range N₀) => abs_nonneg _)
        (mem_range.mpr (lt_of_not_ge hN))
    have hupper := (le_abs_self (β * Real.log n - primeMean (primeSetFlip P) n)).trans hsmall
    linarith only [hupper, abs_nonneg K]

/-- A relative logarithmic density `κ` forces cofinal harmonic growth beyond every exponent
`α < 1 - 2κ`, without a quantitative error term in the density. -/
theorem frequently_gaugeHarmonicSum_gt_rpow_of_logMass_ratio_tendsto
    (P : Set ℕ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 κ))
    {α : ℝ} (hα : 0 ≤ α) (hακ : α < 1 - 2 * κ) (G : ℝ) :
    ∃ᶠ N : ℕ in atTop, G * (1 + Real.log N) ^ α < gaugeHarmonicSum (primeSetFlip P) N := by
  let β := (α + (1 - 2 * κ)) / 2
  have hα1 : α < 1 := by linarith only [hκ, hακ]
  have hαβ : α < β := by dsimp only [β]; linarith only [hακ]
  have hβ1 : β < 1 - 2 * κ := by dsimp only [β]; linarith only [hακ]
  obtain ⟨C, hC⟩ := primeMean_lower_of_logMass_ratio_tendsto P hP hβ1
  by_contra hnot
  have hevent : ∀ᶠ N : ℕ in atTop,
      gaugeHarmonicSum (primeSetFlip P) N ≤ G * (1 + Real.log N) ^ α := by
    simpa only [not_lt] using (not_frequently.mp hnot)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevent
  let B := |G| + ∑ n ∈ range N₀, |gaugeHarmonicSum (primeSetFlip P) n|
  have hB : 0 ≤ B := add_nonneg (abs_nonneg G) (sum_nonneg fun n _ => abs_nonneg _)
  have hGB : G ≤ B := (le_abs_self G).trans
    (le_add_of_nonneg_right (sum_nonneg fun n (_hn : n ∈ range N₀) => abs_nonneg _))
  have hglobal : ∀ n, gaugeHarmonicSum (primeSetFlip P) n ≤ B * (1 + Real.log n) ^ α := by
    intro n
    have hpow : 1 ≤ (1 + Real.log n) ^ α :=
      Real.one_le_rpow (by linarith only [Real.log_natCast_nonneg n]) hα
    by_cases hn : N₀ ≤ n
    · exact (hN₀ n hn).trans (mul_le_mul_of_nonneg_right hGB (by linarith only [hpow]))
    · have hsum := single_le_sum (fun m (_hm : m ∈ range N₀) =>
          abs_nonneg (gaugeHarmonicSum (primeSetFlip P) m)) (mem_range.mpr (lt_of_not_ge hn))
      have hle : gaugeHarmonicSum (primeSetFlip P) n ≤ B :=
        (le_abs_self _).trans (hsum.trans (le_add_of_nonneg_left (abs_nonneg G)))
      exact hle.trans (le_mul_of_one_le_right hB hpow)
  obtain ⟨N, hN⟩ := exists_gaugeHarmonicSum_gt_rpow_of_primeMean_lower
    (primeSetFlip_isSignGauge P) hα hαβ hα1 hC B
  exact (not_lt_of_ge (hglobal N)) hN

/-- At relative logarithmic density zero the cofinal growth exponent reaches one, including
prime sets of zero Euler density. -/
theorem frequently_gaugeHarmonicSum_gt_rpow_of_logMass_ratio_tendsto_zero
    (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) (G : ℝ) :
    ∃ᶠ N : ℕ in atTop, G * (1 + Real.log N) ^ α < gaugeHarmonicSum (primeSetFlip P) N :=
  frequently_gaugeHarmonicSum_gt_rpow_of_logMass_ratio_tendsto P (by norm_num)
    hP hα (by simpa using hα1) G

end GaloisForLFunctions.RenormalizedIntersectionTheory
