import GaloisForLFunctions.RHTower.SteinhausFullGaussianTruncation
import GaloisForLFunctions.RHTower.SmoothAFECofactorCellStability

open Filter Topology Finset
noncomputable section
namespace RHTower

/-- One literal Gaussian tail cutoff works across an entire left abscissa half-plane,
at every bounded positive scale and every phase. -/
theorem exists_fullGaussianCofactor_uniform_abscissa_tail
    (b U : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ L : ℕ, B ≤ L → ∀ s : ℂ, s.re ≤ b →
      ∀ R : ℝ, 0 < R → R ≤ U → ∀ ω : SteinhausModel.Omega,
        ‖steinhausFullGaussianCofactor s R ω -
          truncatedFullGaussianCofactor s R L ω‖ < ε := by
  let A : ℝ := |b| + 2
  have hA : 0 < A := by dsimp only [A]; positivity
  have hbA : b < A := by dsimp only [A]; linarith [le_abs_self b]
  obtain ⟨C, hC, htail⟩ := exists_norm_steinhausFullGaussianCofactor_sub_head_le hA
  have hpow : Tendsto (fun L : ℕ => (L : ℝ) ^ (b - A)) atTop (𝓝 0) := by
    simpa only [show -(A - b) = b - A by ring, Function.comp_def] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hbA)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop)
  have hlim : Tendsto (fun L : ℕ =>
      C * U ^ A * ((L : ℝ) ^ (b - A) / (A - b))) atTop (𝓝 0) := by
    simpa only [zero_div, mul_zero] using
      (hpow.div_const (A - b)).const_mul (C * U ^ A)
  obtain ⟨B0, hB0⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hε))
  refine ⟨max 1 B0, le_max_left _ _, fun L hL s hs R hR hRU ω => ?_⟩
  have hL1 : 1 ≤ L := (le_max_left 1 B0).trans hL
  have hsA : s.re < A := hs.trans_lt hbA
  have hratio : (L : ℝ) ^ (s.re - A) / (A - s.re) ≤
      (L : ℝ) ^ (b - A) / (A - b) := by
    apply (div_le_div_iff₀ (sub_pos.mpr hsA) (sub_pos.mpr hbA)).mpr
    exact mul_le_mul
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hL1) (sub_le_sub_right hs A))
      (sub_le_sub_left hs A) (sub_pos.mpr hbA).le
      (Real.rpow_nonneg (Nat.cast_nonneg L) _)
  calc
    _ ≤ C * R ^ A * ((L : ℝ) ^ (s.re - A) / (A - s.re)) :=
      htail s R hR hsA L hL1 ω
    _ ≤ C * U ^ A * ((L : ℝ) ^ (b - A) / (A - b)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hR.le hRU hA.le) hC)
        hratio
        (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg L) _) (sub_pos.mpr hsA).le)
        (mul_nonneg hC (Real.rpow_nonneg (hR.trans_le hRU).le _))
    _ < ε := hB0 L ((le_max_right 1 B0).trans hL)

/-- A single finite-character tolerance preserves the full cofactor simultaneously
at every point of an abscissa half-plane and every bounded positive scale. -/
theorem exists_fullGaussianCofactor_uniform_abscissa_character_tolerance
    (b U : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, 1 ≤ B ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ s : ℂ, s.re ≤ b → ∀ R : ℝ, 0 < R → R ≤ U →
        ∀ ω η : SteinhausModel.Omega,
          (∀ n ∈ Icc 1 B, ‖SteinhausModel.X n η - SteinhausModel.X n ω‖ < δ) →
          ‖steinhausFullGaussianCofactor s R η - steinhausFullGaussianCofactor s R ω‖ < ε := by
  obtain ⟨B, hB, htail⟩ := exists_fullGaussianCofactor_uniform_abscissa_tail b U
    (by positivity : 0 < ε / 4)
  let K : ℝ := 1 + ∑ n ∈ range B, ‖((n + 1 : ℕ) : ℂ) ^ ((b : ℂ) - 1)‖
  have hK : 0 < K := by dsimp only [K]; positivity
  let δ : ℝ := ε / (4 * K)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  refine ⟨B, hB, δ, hδ, fun s hs R hR hRU ω η hcell => ?_⟩
  have hdiff : truncatedFullGaussianCofactor s R B η -
      truncatedFullGaussianCofactor s R B ω =
      ∑ n ∈ range B, (SteinhausModel.X (n + 1) η - SteinhausModel.X (n + 1) ω) *
        ((n + 1 : ℕ) : ℂ) ^ (s - 1) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R) := by
    simp only [truncatedFullGaussianCofactor, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    ring
  have hhead : ‖truncatedFullGaussianCofactor s R B η -
      truncatedFullGaussianCofactor s R B ω‖ ≤ ε / 4 := by
    rw [hdiff]
    calc
      _ ≤ ∑ n ∈ range B, ‖(SteinhausModel.X (n + 1) η - SteinhausModel.X (n + 1) ω) *
          ((n + 1 : ℕ) : ℂ) ^ (s - 1) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ n ∈ range B, ‖((n + 1 : ℕ) : ℂ) ^ ((b : ℂ) - 1)‖ * δ := by
        apply sum_le_sum
        intro n hn
        have hx := (hcell (n + 1) (mem_Icc.mpr ⟨by omega, by have := mem_range.mp hn; omega⟩)).le
        have hw := norm_smoothAFECutoff_le_one
          (by positivity : 0 < (((n + 1 : ℕ) : ℝ) / R))
        have hp : ‖((n + 1 : ℕ) : ℂ) ^ (s - 1)‖ ≤
            ‖((n + 1 : ℕ) : ℂ) ^ ((b : ℂ) - 1)‖ := by
          apply Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos (Nat.succ_pos n)
          simpa only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] using
            sub_le_sub_right hs 1
        simp only [norm_mul]
        calc
          _ ≤ (δ * ‖((n + 1 : ℕ) : ℂ) ^ ((b : ℂ) - 1)‖) * 1 :=
            mul_le_mul (mul_le_mul hx hp (norm_nonneg _) hδ.le) hw
              (norm_nonneg _) (mul_nonneg hδ.le (norm_nonneg _))
          _ = _ := by ring
      _ = (∑ n ∈ range B, ‖((n + 1 : ℕ) : ℂ) ^ ((b : ℂ) - 1)‖) * δ := (sum_mul ..).symm
      _ ≤ K * δ := mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) hδ.le
      _ = ε / 4 := by dsimp only [δ]; field_simp [hK.ne']
  have hη := htail B le_rfl s hs R hR hRU η
  have hω := htail B le_rfl s hs R hR hRU ω
  have heq : steinhausFullGaussianCofactor s R η - steinhausFullGaussianCofactor s R ω =
      (steinhausFullGaussianCofactor s R η - truncatedFullGaussianCofactor s R B η) +
      (truncatedFullGaussianCofactor s R B η - truncatedFullGaussianCofactor s R B ω) +
      (truncatedFullGaussianCofactor s R B ω - steinhausFullGaussianCofactor s R ω) := by ring
  have htri := (norm_add_le
    ((steinhausFullGaussianCofactor s R η - truncatedFullGaussianCofactor s R B η) +
      (truncatedFullGaussianCofactor s R B η - truncatedFullGaussianCofactor s R B ω))
    (truncatedFullGaussianCofactor s R B ω - steinhausFullGaussianCofactor s R ω)).trans
      (add_le_add (norm_add_le _ _) (le_refl _))
  rw [← heq, norm_sub_rev (truncatedFullGaussianCofactor s R B ω)
    (steinhausFullGaussianCofactor s R ω)] at htri
  linarith

end RHTower
