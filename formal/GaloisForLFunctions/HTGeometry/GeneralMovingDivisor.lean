import GaloisForLFunctions.HTGeometry.MovingDivisorData
import GaloisForLFunctions.HTGeometry.GapBlockLawStability

/-!
# The moving divisor of a prescribed gap process

The partial sums of a generic gap sequence, displaced inside the shrinking radii, form a moving
divisor: the radii are small enough against the gaps for the displaced sequence to stay strictly
increasing, and the mean-one hypothesis gives unit asymptotic density.
-/

open Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

open Filter
open scoped Topology

theorem tendsto_natCast_div_succ : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hsub := hconst.sub hinv
  rw [sub_zero] at hsub
  refine hsub.congr fun n => ?_
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- The partial sums of a mean-one gap sequence have unit density in the shifted normalization. -/
theorem tendsto_gapPartialSum_div_succ (g : ℕ → ℝ)
    (hg : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, g j) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => gapPartialSum g n / ((n : ℝ) + 1)) atTop (𝓝 1) := by
  have hprod := (tendsto_gapPartialSum_div g hg).mul tendsto_natCast_div_succ
  rw [one_mul] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- **The moving divisor of a prescribed gap sequence.** -/
noncomputable def gapMovingDivisor (g : ℕ → ℝ) (hgpos : ∀ j, 0 < g j)
    (hgmean : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, g j) atTop (𝓝 1)) :
    MovingDivisor where
  base := gapPartialSum g
  radius := gapRadius g
  radius_pos := gapRadius_pos hgpos
  radius_le_one := fun n => by
    have h1 := gapRadius_le_pow g n
    have h2 : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  base_gap := fun n => by
    have hps : gapPartialSum g (n + 1) = gapPartialSum g n + g n := rfl
    have h1 := gapRadius_le_gap_self hgpos n
    have h2 := gapRadius_succ_le_gap hgpos n
    have h3 := hgpos n
    rw [hps]
    linarith
  base_first := by
    have h1 := gapRadius_le_pow g 0
    have hps : gapPartialSum g 0 = 1 := rfl
    rw [hps]
    norm_num at h1
    linarith
  density := tendsto_gapPartialSum_div_succ g hgmean

theorem gapMovingDivisor_zero (g : ℕ → ℝ) (hgpos : ∀ j, 0 < g j)
    (hgmean : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, g j) atTop (𝓝 1))
    (θ : ℕ → ℝ) (n : ℕ) :
    (gapMovingDivisor g hgpos hgmean).zero θ n = gapLocation g θ n := rfl

end GaloisForLFunctions.HTGeometry
