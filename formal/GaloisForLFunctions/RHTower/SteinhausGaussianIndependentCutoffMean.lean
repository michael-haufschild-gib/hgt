import GaloisForLFunctions.RHTower.SteinhausGaussianWeightedMean
import GaloisForLFunctions.RHTower.SmoothAFECofactorCellStability
import GaloisForLFunctions.RHTower.SmoothAFETruncation



open MeasureTheory Filter Finset
open scoped Topology
noncomputable section
namespace RHTower
open SteinhausModel

/-- The entire absolute Gaussian Dirichlet mass has its smoothing-scale power bound,
independently of any polynomial truncation. -/
theorem exists_sum_norm_gaussian_direct_le {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ L : ℕ,
      (∑ n ∈ range L, ‖(((n + 1 : ℕ) : ℂ) ^ (-(γ : ℂ))) *
        smoothAFECutoff (((n + 1 : ℕ) : ℝ) / N)‖) ≤ C * (N : ℝ) ^ (1 - γ) := by
  obtain ⟨K, hK, htail⟩ := exists_smoothAFE_direct_tail_le (show (0 : ℝ) < 1 by norm_num)
  refine ⟨1 / (1 - γ) + K / γ, by positivity, ?_⟩
  intro N hN L
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let a : ℕ → ℝ := fun n => ‖(((n + 1 : ℕ) : ℂ) ^ (-(γ : ℂ))) *
    smoothAFECutoff (((n + 1 : ℕ) : ℝ) / N)‖
  have hs : Summable a := (summable_smoothAFE_direct (A := 1) (by norm_num) hNR
    (by simp only [Complex.ofReal_re]; linarith : 1 < (γ : ℂ).re + 1)).norm
  have hhead : ∑ n ∈ range N, a n ≤ (N : ℝ) ^ (1 - γ) / (1 - γ) := by
    have hb := HTGeometry.sum_rpow_sub_one_le (sub_pos.mpr hγ1) (by linarith : 1 - γ < 1) N
    have hp : ∀ n : ℕ, a n ≤ ((n : ℝ) + 1) ^ (-γ) := by
      intro n
      dsimp only [a]
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega : 0 < n + 1),
        Complex.neg_re, Complex.ofReal_re]
      have hc := norm_smoothAFECutoff_le_one (div_pos
        (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)) hNR)
      simpa only [Nat.cast_add, Nat.cast_one, mul_one] using
        mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg (Nat.cast_nonneg (n + 1)) (-γ))
    refine (sum_le_sum (fun n _ => hp n)).trans ?_
    simpa only [show 1 - γ - 1 = -γ by ring_nf] using hb
  have ht : (∑' n : ℕ, a (n + N)) ≤ (K / γ) * (N : ℝ) ^ (1 - γ) := by
    have hb := htail (γ : ℂ) N hNR
      (by simp only [Complex.ofReal_re]; linarith : 1 < (γ : ℂ).re + 1) N hN
    have heq : K * (N : ℝ) ^ (1 : ℝ) *
        ((N : ℝ) ^ (1 - ((γ : ℂ).re + 1)) / ((γ : ℂ).re + 1 - 1)) =
        (K / γ) * (N : ℝ) ^ (1 - γ) := by
      simp only [Complex.ofReal_re, add_sub_cancel_right,
        show 1 - (γ + 1) = -γ by ring_nf]
      rw [show K * (N : ℝ) ^ (1 : ℝ) * ((N : ℝ) ^ (-γ) / γ) =
        (K / γ) * ((N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-γ)) by ring_nf,
        ← Real.rpow_add hNR]
      rfl
    rw [heq] at hb
    exact hb
  calc
    _ ≤ ∑' n : ℕ, a n := hs.sum_le_tsum (range L) (fun n _ => norm_nonneg _)
    _ = (∑ n ∈ range N, a n) + ∑' n : ℕ, a (n + N) := (hs.sum_add_tsum_nat_add N).symm
    _ ≤ (N : ℝ) ^ (1 - γ) / (1 - γ) + (K / γ) * (N : ℝ) ^ (1 - γ) := add_le_add hhead ht
    _ = _ := by ring_nf

/-- Gaussian square-root Abel cost is controlled by the smoothing scale N, uniformly
in an independent polynomial length L. -/
theorem exists_steinhausGaussianAbelSqrtCost_uniform_cutoff
    {β : ℝ} (hβ : 0 < β) (hβhalf : β < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ L : ℕ,
      steinhausGaussianWeight β 1 N (L + 1) * Real.sqrt L +
        (∑ n ∈ Icc 1 L, (steinhausGaussianWeight β 1 N n -
          steinhausGaussianWeight β 1 N (n + 1)) * Real.sqrt n) ≤
            C * (N : ℝ) ^ (1 / 2 - β) := by
  obtain ⟨C, hC, hbound⟩ := exists_sum_norm_gaussian_direct_le
    (by linarith : 0 < β + 1 / 2) (by linarith : β + 1 / 2 < 1)
  refine ⟨C, hC, ?_⟩
  intro N hN L
  rw [steinhausAbelSqrtCost_eq]
  have hterm (n : ℕ) (hn : n ∈ Icc 1 L) :
      steinhausGaussianWeight β 1 N n * (Real.sqrt n - Real.sqrt (n - 1 : ℕ)) ≤
        ‖(n : ℂ) ^ (-((β + 1 / 2 : ℝ) : ℂ)) * smoothAFECutoff ((n : ℝ) / N)‖ := by
    have hn1 : 0 < n := (mem_Icc.mp hn).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    calc
      _ ≤ steinhausGaussianWeight β 1 N n * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (steinhausSqrtIncrement_le n hn1)
          (steinhausGaussianWeight_nonneg β one_pos hN hn1)
      _ = (n : ℝ) ^ (-(β + 1 / 2)) * (smoothAFECutoff ((n : ℝ) / N)).re := by
        simp only [steinhausGaussianWeight, one_mul]
        rw [mul_right_comm, ← Real.rpow_add hnR]
        congr 1
        ring_nf
      _ ≤ (n : ℝ) ^ (-(β + 1 / 2)) * ‖smoothAFECutoff ((n : ℝ) / N)‖ :=
        mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (Real.rpow_nonneg hnR.le _)
      _ = _ := by
        rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn1, Complex.neg_re, Complex.ofReal_re]
  refine (sum_le_sum hterm).trans ?_
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right]
  have hb := hbound N hN L
  simpa only [Nat.add_comm, show 1 - (β + 1 / 2) = 1 / 2 - β by ring_nf] using hb

/-- The original Gaussian first mean is little-o at the smoothing scale, uniformly over
all independent polynomial cutoffs. No restriction on the growth of L is needed. -/
theorem eventually_integral_norm_steinhausGaussianWeight_independent_cutoff_le
    {β : ℝ} (hβ : 0 < β) (hβhalf : β < 1 / 2) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ L : ℕ,
      (∫ ω, ‖∑ n ∈ Icc 1 L, (steinhausGaussianWeight β 1 N n : ℂ) * X n ω‖ ∂steinhausMeasure) /
        (N : ℝ) ^ (1 / 2 - β) ≤ δ := by
  obtain ⟨K, hK, hcost⟩ := exists_steinhausGaussianAbelSqrtCost_uniform_cutoff hβ hβhalf
  let d : ℝ := 1 / 2 - β
  have hd : 0 < d := by dsimp only [d]; linarith
  let ε : ℝ := δ / (2 * K)
  have hε : 0 < ε := div_pos hδ (mul_pos (by norm_num) hK)
  obtain ⟨C, hC, hmean⟩ := exists_steinhausSummatoryMean_sqrt_envelope hε
  have htail : Tendsto (fun N : ℕ => C / (N : ℝ) ^ d) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop)
  filter_upwards [htail.eventually (gt_mem_nhds (half_pos hδ)), eventually_ge_atTop (1 : ℕ)]
    with N htailN hN
  intro L
  have hp : 0 < (N : ℝ) ^ d := Real.rpow_pos_of_pos (by exact_mod_cast hN) _
  have hw1 : steinhausGaussianWeight β 1 N 1 ≤ 1 := by
    simpa using steinhausGaussianWeight_le_rpow β one_pos hN (by norm_num : 0 < 1)
  have hupper : (∫ ω, ‖∑ n ∈ Icc 1 L,
      (steinhausGaussianWeight β 1 N n : ℂ) * X n ω‖ ∂steinhausMeasure) ≤
      C + ε * (K * (N : ℝ) ^ d) := by
    refine (integral_norm_steinhausWeightedSummatory_le_envelope
      (steinhausGaussianWeight β 1 N) L
      (fun n hn => steinhausGaussianWeight_nonneg β one_pos hN hn)
      (fun n hn => steinhausGaussianWeight_succ_le hβ.le one_pos hN hn) hmean).trans ?_
    exact add_le_add (by nlinarith) (mul_le_mul_of_nonneg_left (hcost N hN L) hε.le)
  have halgebra : (C + ε * (K * (N : ℝ) ^ d)) / (N : ℝ) ^ d =
      C / (N : ℝ) ^ d + δ / 2 := by
    dsimp only [ε]
    field_simp [hp.ne', hK.ne']
  change _ / (N : ℝ) ^ d ≤ δ
  have h := div_le_div_of_nonneg_right hupper hp.le
  rw [halgebra] at h
  linarith

end RHTower
