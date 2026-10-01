import GaloisForLFunctions.RHTower.SteinhausFullGaussianCofactorTail
import GaloisForLFunctions.RHTower.SmoothAFECofactorCellStability
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics


open Filter Topology Finset
noncomputable section
namespace RHTower

private def gaussianCofactorHead (s : ℂ) (R : ℝ) (B : ℕ) (ω : SteinhausModel.Omega) : ℂ :=
  ∑ n ∈ range B, SteinhausModel.X (n + 1) ω * ((n + 1 : ℕ) : ℂ) ^ (s - 1) *
    smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)

private theorem exists_uniform_fullGaussian_tail (s : ℂ) (U : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ R : ℝ, 0 < R → R ≤ U → ∀ ω : SteinhausModel.Omega,
      ‖steinhausFullGaussianCofactor s R ω - gaussianCofactorHead s R B ω‖ < ε := by
  let A : ℝ := |s.re| + 2
  have hA : 0 < A := by dsimp only [A]; positivity
  have hsA : s.re < A := by dsimp only [A]; linarith [le_abs_self s.re]
  obtain ⟨C, hC, htail⟩ := exists_norm_steinhausFullGaussianCofactor_sub_head_le hA
  have hpow : Tendsto (fun B : ℕ => (B : ℝ) ^ (s.re - A)) atTop (𝓝 0) := by
    simpa only [show -(A - s.re) = s.re - A by ring, Function.comp_def] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hsA)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun B : ℕ => (B : ℝ)) atTop atTop)
  have hlim : Tendsto (fun B : ℕ =>
      C * U ^ A * ((B : ℝ) ^ (s.re - A) / (A - s.re))) atTop (𝓝 0) := by
    simpa only [zero_div, mul_zero] using (hpow.div_const (A - s.re)).const_mul (C * U ^ A)
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hε))
  let B := max 1 B₀
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨B, hB, fun R hR hRU ω => ?_⟩
  calc
    _ ≤ C * R ^ A * ((B : ℝ) ^ (s.re - A) / (A - s.re)) := htail s R hR hsA B hB ω
    _ ≤ C * U ^ A * ((B : ℝ) ^ (s.re - A) / (A - s.re)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hR.le hRU hA.le) hC)
        (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sub_pos.mpr hsA).le)
    _ < ε := hB₀ B (le_max_right _ _)

/-- The full Gaussian cofactor is uniformly stable on a fixed finite-character cell for every
positive scale below a fixed bound. Both infinite tails are controlled uniformly in phase. -/
theorem exists_fullGaussianCofactor_character_tolerance
    (s : ℂ) (U : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, 1 ≤ B ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ R : ℝ, 0 < R → R ≤ U → ∀ ω η : SteinhausModel.Omega,
        (∀ n ∈ Icc 1 B, ‖SteinhausModel.X n η - SteinhausModel.X n ω‖ < δ) →
        ‖steinhausFullGaussianCofactor s R η - steinhausFullGaussianCofactor s R ω‖ < ε := by
  obtain ⟨B, hB, htail⟩ := exists_uniform_fullGaussian_tail s U
    (by positivity : 0 < ε / 4)
  let K : ℝ := 1 + ∑ n ∈ range B, ‖((n + 1 : ℕ) : ℂ) ^ (s - 1)‖
  have hK : 0 < K := by dsimp only [K]; positivity
  let δ : ℝ := ε / (4 * K)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  refine ⟨B, hB, δ, hδ, fun R hR hRU ω η hcell => ?_⟩
  have hdiff : gaussianCofactorHead s R B η - gaussianCofactorHead s R B ω =
      ∑ n ∈ range B, (SteinhausModel.X (n + 1) η - SteinhausModel.X (n + 1) ω) *
        ((n + 1 : ℕ) : ℂ) ^ (s - 1) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R) := by
    simp only [gaussianCofactorHead, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    ring
  have hhead : ‖gaussianCofactorHead s R B η - gaussianCofactorHead s R B ω‖ ≤ ε / 4 := by
    rw [hdiff]
    calc
      _ ≤ ∑ n ∈ range B, ‖(SteinhausModel.X (n + 1) η - SteinhausModel.X (n + 1) ω) *
          ((n + 1 : ℕ) : ℂ) ^ (s - 1) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ n ∈ range B, ‖((n + 1 : ℕ) : ℂ) ^ (s - 1)‖ * δ := by
        apply sum_le_sum
        intro n hn
        have hx := (hcell (n + 1) (mem_Icc.mpr ⟨by omega, by have := mem_range.mp hn; omega⟩)).le
        have hw := norm_smoothAFECutoff_le_one (by positivity : 0 < (((n + 1 : ℕ) : ℝ) / R))
        simp only [norm_mul]
        calc
          _ ≤ (δ * ‖((n + 1 : ℕ) : ℂ) ^ (s - 1)‖) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_right hx (norm_nonneg _)) hw
              (norm_nonneg _) (mul_nonneg hδ.le (norm_nonneg _))
          _ = _ := by ring
      _ = (∑ n ∈ range B, ‖((n + 1 : ℕ) : ℂ) ^ (s - 1)‖) * δ := (sum_mul ..).symm
      _ ≤ K * δ := mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) hδ.le
      _ = ε / 4 := by dsimp only [δ]; field_simp [hK.ne']
  have hη := htail R hR hRU η
  have hω := htail R hR hRU ω
  have heq : steinhausFullGaussianCofactor s R η - steinhausFullGaussianCofactor s R ω =
      (steinhausFullGaussianCofactor s R η - gaussianCofactorHead s R B η) +
      (gaussianCofactorHead s R B η - gaussianCofactorHead s R B ω) +
      (gaussianCofactorHead s R B ω - steinhausFullGaussianCofactor s R ω) := by ring
  have htri := (norm_add_le
    ((steinhausFullGaussianCofactor s R η - gaussianCofactorHead s R B η) +
      (gaussianCofactorHead s R B η - gaussianCofactorHead s R B ω))
    (gaussianCofactorHead s R B ω - steinhausFullGaussianCofactor s R ω)).trans
      (add_le_add (norm_add_le _ _) (le_refl _))
  rw [← heq, norm_sub_rev (gaussianCofactorHead s R B ω) (steinhausFullGaussianCofactor s R ω)] at htri
  linarith

end RHTower
