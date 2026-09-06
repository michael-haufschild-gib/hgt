import GaloisForLFunctions.RHTower.ChronologicalHeatL2
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.FusionMellin
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# Finite chronological heat errors and their Mellin invariant

Every finite real coefficient vector gives an actual L² residual. Its two
pointwise bounds control both ends of the positive axis. At every zeta zero
in the open strip its Mellin integral equals Gamma, independently of all
coefficients. No RH assumption or numerical zero is used.
-/

noncomputable section
open Set MeasureTheory Complex
namespace RHTower
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

def chronologicalHeatError (a : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-t) + ∑ k ∈ Finset.Ioc 0 N, a k * fusionBoseDefect ((k:ℝ)*t)

theorem chronologicalHeatError_continuousOn (a : ℕ → ℝ) (N : ℕ) :
    ContinuousOn (chronologicalHeatError a N) (Ioi 0) := by
  apply (Real.continuous_exp.comp continuous_neg).continuousOn.add
  apply continuousOn_finsetSum
  intro k hk
  apply continuousOn_const.mul
  apply chronologicalBose_continuousOn.comp (continuous_const.mul continuous_id).continuousOn
  intro t ht
  change 0 < (k:ℝ)*t
  exact mul_pos (by exact_mod_cast (Finset.mem_Ioc.mp hk).1) (show 0 < t from ht)

theorem chronologicalHeatError_memLp (a : ℕ → ℝ) (N : ℕ) :
    MemLp (chronologicalHeatError a N) 2 chronologicalPositiveVolume := by
  apply chronologicalExponential_memLp.add
  apply memLp_finsetSum
  intro k hk
  exact (chronological_memLp_dilate chronologicalBose_memLp chronologicalBose_continuousOn
    (by exact_mod_cast (Finset.mem_Ioc.mp hk).1)).const_mul _

theorem chronologicalHeatError_bounds (a : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (ha : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ C)
    {t : ℝ} (ht : 0 < t) :
    |chronologicalHeatError a N t| ≤ 1+C*N ∧
      |chronologicalHeatError a N t| ≤ (1+C*N)/t := by
  have hsum : |∑ k ∈ Finset.Ioc 0 N, a k * fusionBoseDefect ((k:ℝ)*t)| ≤ C*N := by
    calc
      _ ≤ ∑ k ∈ Finset.Ioc 0 N, |a k * fusionBoseDefect ((k:ℝ)*t)| := Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ k ∈ Finset.Ioc 0 N, C := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul, abs_of_nonneg (fusionBoseDefect_bounds _).1]
        exact (mul_le_mul_of_nonneg_left (fusionBoseDefect_bounds _).2.1 (abs_nonneg _)).trans
          (by simpa using ha k hk)
      _ = _ := by simp; ring
  have hsumt : |∑ k ∈ Finset.Ioc 0 N, a k * fusionBoseDefect ((k:ℝ)*t)| ≤ C*N/t := by
    calc
      _ ≤ ∑ k ∈ Finset.Ioc 0 N, |a k * fusionBoseDefect ((k:ℝ)*t)| := Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ k ∈ Finset.Ioc 0 N, C/t := by
        apply Finset.sum_le_sum
        intro k hk
        have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (Finset.mem_Ioc.mp hk).1
        have hkt : 0 < (k:ℝ)*t := mul_pos (by linarith) ht
        have hb : fusionBoseDefect ((k:ℝ)*t) ≤ 1/t := by
          have hh := (fusionBoseDefect_bounds ((k:ℝ)*t)).2.2
          rw [abs_of_pos hkt] at hh
          exact hh.trans (one_div_le_one_div_of_le ht (by nlinarith))
        rw [abs_mul, abs_of_nonneg (fusionBoseDefect_bounds _).1]
        calc
          _ ≤ |a k| *(1/t) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
          _ ≤ C*(1/t) := mul_le_mul_of_nonneg_right (ha k hk) (by positivity)
          _ = _ := by ring
      _ = _ := by simp; ring
  have hex : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hext : Real.exp (-t) ≤ 1/t := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      (one_div_le_one_div_of_le ht (show t ≤ Real.exp t by linarith [Real.add_one_le_exp t]))
  have htri := abs_add_le (Real.exp (-t)) (∑ k ∈ Finset.Ioc 0 N, a k * fusionBoseDefect ((k:ℝ)*t))
  rw [abs_of_pos (Real.exp_pos _)] at htri
  change |chronologicalHeatError a N t| ≤ _ at htri
  constructor
  · linarith
  · rw [add_div]
    linarith

theorem chronologicalExponential_mellinConvergent {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun t : ℝ => (Real.exp (-t) : ℂ)) s := by
  simpa [MellinConvergent, mul_comm, smul_eq_mul] using Complex.GammaIntegral_convergent hs

theorem chronologicalHeatError_mellinConvergent (a : ℕ → ℝ) (N : ℕ)
    {s : ℂ} (hs : s ∈ fusionMellinStrip) :
    MellinConvergent (fun t => (chronologicalHeatError a N t : ℂ)) s := by
  have hx := chronologicalExponential_mellinConvergent hs.1
  have hm : ∀ k ∈ Finset.Ioc 0 N,
      MellinConvergent (fun t => (a k : ℂ) * fusionBoseKernel ((k:ℝ)*t)) s := by
    intro k hk
    have hd := (MellinConvergent.comp_mul_left
      (by exact_mod_cast (Finset.mem_Ioc.mp hk).1 : (0:ℝ)<k)).mpr
        (fusionBoseKernel_converges s hs)
    simpa only [smul_eq_mul] using hd.const_smul (a k : ℂ)
  simp only [MellinConvergent, smul_eq_mul] at *
  convert! hx.add (integrable_finsetSum _ hm) using 1
  ext t
  simp [chronologicalHeatError, fusionBoseKernel, mul_add, Finset.mul_sum]

theorem chronologicalHeatError_mellin_at_zero (a : ℕ → ℝ) (N : ℕ)
    {s : ℂ} (hs : s ∈ fusionMellinStrip) (hz : riemannZeta s = 0) :
    mellin (fun t => (chronologicalHeatError a N t : ℂ)) s = Complex.Gamma s := by
  have hx := chronologicalExponential_mellinConvergent hs.1
  have hm : ∀ k ∈ Finset.Ioc 0 N,
      MellinConvergent (fun t => (a k : ℂ) * fusionBoseKernel ((k:ℝ)*t)) s := by
    intro k hk
    have hd := (MellinConvergent.comp_mul_left
      (by exact_mod_cast (Finset.mem_Ioc.mp hk).1 : (0:ℝ)<k)).mpr
        (fusionBoseKernel_converges s hs)
    simpa only [smul_eq_mul] using hd.const_smul (a k : ℂ)
  have he : (fun t => (chronologicalHeatError a N t : ℂ)) =
      (fun t => (Real.exp (-t) : ℂ) +
        ∑ k ∈ Finset.Ioc 0 N, (a k : ℂ) * fusionBoseKernel ((k:ℝ)*t)) := by
    funext t
    simp [chronologicalHeatError, fusionBoseKernel]
  simp only [MellinConvergent, smul_eq_mul] at hx hm
  rw [he]
  unfold mellin
  simp only [smul_eq_mul, mul_add, Finset.mul_sum]
  rw [integral_add hx (integrable_finsetSum _ hm), integral_finsetSum _ hm]
  have hxv : (∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1) * (Real.exp (-t) : ℂ)) = Complex.Gamma s := by
    rw [Complex.Gamma_eq_integral hs.1, Complex.GammaIntegral]
    apply integral_congr_ae
    filter_upwards with t
    ring
  rw [hxv]
  suffices (∑ k ∈ Finset.Ioc 0 N,
      ∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1)*((a k : ℂ)*fusionBoseKernel ((k:ℝ)*t))) = 0 by
    rw [this, add_zero]
  apply Finset.sum_eq_zero
  intro k hk
  change mellin (fun t => (a k : ℂ) • fusionBoseKernel ((k:ℝ)*t)) s = 0
  rw [mellin_const_smul,
    mellin_comp_mul_left fusionBoseKernel s (by exact_mod_cast (Finset.mem_Ioc.mp hk).1),
    fusionBoseKernel_mellin hs]
  simp [hz]

end RHTower
