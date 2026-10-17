import GaloisForLFunctions.BiScaleUncertainty.SynchronizedCosetSineLeverage
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# A concrete smooth source with a signed dyadic difference Gram matrix

A fixed narrow smooth bump has orthogonal integer-log-two translates. Its first
translation difference is an actual compact smooth source with negative adjacent
correlations. No seed, support, orthogonality or source-realization premise is supplied.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported ContDiff

namespace GaloisForLFunctions.BiScaleUncertainty.DyadicDifference
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
noncomputable section

def step : ℝ := Real.log 2

theorem step_pos : 0 < step := Real.log_pos (by norm_num)

/-- A literal smooth bump; no existential choice of source is involved. -/
def seedBump : ContDiffBump (0 : ℝ) :=
  ⟨step / 8, step / 4, div_pos step_pos (by norm_num), by linarith only [step_pos]⟩

def seed : C_c(ℝ, ℝ) :=
  ⟨⟨seedBump, seedBump.continuous⟩, seedBump.hasCompactSupport⟩

theorem seed_smooth : ContDiff ℝ ∞ (seed : ℝ → ℝ) := seedBump.contDiff

theorem seed_zero (u : ℝ) (hu : step / 4 ≤ |u|) : seed u = 0 := by
  apply seedBump.zero_of_le_dist
  simpa only [Real.dist_eq, sub_zero, seedBump] using hu

theorem seed_at_zero : seed 0 = 1 := by
  apply seedBump.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, dist_self] using seedBump.rIn_pos.le

theorem seed_energy_pos : 0 < autocorr seed 0 := by
  unfold autocorr
  simp only [add_zero]
  exact (seed.continuous.mul seed.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
    seed.hasCompactSupport.mul_right (fun x => mul_self_nonneg (seed x)) (x := 0)
    (by rw [seed_at_zero]; norm_num)

theorem seed_autocorr_zero (x : ℝ) (hx : step / 2 < |x|) : autocorr seed x = 0 := by
  have hz (u : ℝ) : seed u * seed (u + x) = 0 := by
    by_cases hu : seed u = 0
    · simp only [hu, zero_mul]
    by_cases hv : seed (u + x) = 0
    · simp only [hv, mul_zero]
    have hu' : |u| < step / 4 := lt_of_not_ge fun h => hu (seed_zero u h)
    have hv' : |u + x| < step / 4 := lt_of_not_ge fun h => hv (seed_zero (u + x) h)
    have ht : |x| ≤ |u + x| + |u| := by
      simpa only [add_sub_cancel_left] using abs_sub (u + x) u
    exfalso
    linarith only [hx, hu', hv', ht]
  simp only [autocorr, hz, integral_zero]

/-- The source is one fixed difference of the explicit smooth seed. -/
def source : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => seed u - seed (u + step),
    seed.continuous.sub (seed.continuous.comp (continuous_add_const step))⟩,
    seed.hasCompactSupport.sub (hasCompactSupport_comp_add seed.hasCompactSupport step)⟩

theorem source_smooth : ContDiff ℝ ∞ (source : ℝ → ℝ) :=
  seed_smooth.sub (seed_smooth.comp (contDiff_id.add contDiff_const))

def atom (j : ℤ) : Lp ℂ 2 (volume : Measure ℝ) :=
  translationFeature seed ((j : ℝ) * step)

private theorem integer_step_separated (i j : ℤ) (hij : i ≠ j) :
    step ≤ |(j : ℝ) * step - (i : ℝ) * step| := by
  rcases lt_or_gt_of_ne hij with h | h
  · have hi : (i : ℝ) + 1 ≤ j := by exact_mod_cast (show i + 1 ≤ j by omega)
    have hm := mul_le_mul_of_nonneg_right hi step_pos.le
    exact (by nlinarith only [hm] : step ≤ (j : ℝ) * step - (i : ℝ) * step).trans
      (le_abs_self _)
  · have hi : (j : ℝ) + 1 ≤ i := by exact_mod_cast (show j + 1 ≤ i by omega)
    have hm := mul_le_mul_of_nonneg_right hi step_pos.le
    exact (by nlinarith only [hm] : step ≤ -((j : ℝ) * step - (i : ℝ) * step)).trans
      (neg_le_abs _)

/-- Every off-diagonal entry vanishes for this concrete seed. -/
theorem atom_inner (i j : ℤ) :
    inner ℂ (atom i) (atom j) = if i = j then (autocorr seed 0 : ℂ) else 0 := by
  rw [atom, atom, translationFeature_inner]
  by_cases h : i = j
  · simp only [h, if_pos, sub_self]
  · rw [if_neg h, seed_autocorr_zero _ (lt_of_lt_of_le
      (by linarith only [step_pos] : step / 2 < step) (integer_step_separated i j h))]
    rfl

theorem atom_norm_sq (j : ℤ) : ‖atom j‖ ^ 2 = autocorr seed 0 :=
  translationFeature_norm_sq seed _

private theorem feature_ae (f : C_c(ℝ, ℝ)) (t : ℝ) :
    (fun u => translationFeature f t u) =ᵐ[volume] fun u => (f (u + t) : ℂ) := by
  unfold translationFeature
  exact MemLp.coeFn_toLp _

/-- The source's actual translation vector is the difference of adjacent atoms. -/
theorem source_feature (j : ℤ) :
    translationFeature source ((j : ℝ) * step) = atom j - atom (j + 1) := by
  change translationFeature source ((j : ℝ) * step) =
    translationFeature seed ((j : ℝ) * step) - translationFeature seed (((j + 1 : ℤ) : ℝ) * step)
  apply Lp.ext
  filter_upwards [feature_ae source ((j : ℝ) * step),
    feature_ae seed ((j : ℝ) * step), feature_ae seed (((j + 1 : ℤ) : ℝ) * step),
    Lp.coeFn_sub (translationFeature seed ((j : ℝ) * step))
      (translationFeature seed (((j + 1 : ℤ) : ℝ) * step))] with u hf hg hh hs
  rw [hf, hs]
  change (source (u + (j : ℝ) * step) : ℂ) =
    translationFeature seed ((j : ℝ) * step) u -
      translationFeature seed (((j + 1 : ℤ) : ℝ) * step) u
  rw [hg, hh]
  change ((seed (u + (j : ℝ) * step) - seed (u + (j : ℝ) * step + step) : ℝ) : ℂ) = _
  push_cast
  rw [show u + (j : ℝ) * step + step = u + ((j : ℝ) + 1) * step by ring]

def edge (j : ℤ) : Lp ℂ 2 (volume : Measure ℝ) :=
  translationFeature source ((j : ℝ) * step)

theorem edge_eq (j : ℤ) : edge j = atom j - atom (j + 1) := source_feature j

theorem source_energy : autocorr source 0 = 2 * autocorr seed 0 := by
  have he : translationFeature source 0 = atom 0 - atom 1 := by
    simpa only [Int.cast_zero, zero_mul, zero_add] using source_feature 0
  rw [← translationFeature_norm_sq source 0, he, norm_sub_sq (𝕜 := ℂ),
    atom_norm_sq, atom_norm_sq, atom_inner]
  norm_num
  ring

theorem source_energy_pos : 0 < autocorr source 0 := by
  rw [source_energy]
  exact mul_pos (by norm_num) seed_energy_pos

theorem source_adjacent_correlation : autocorr source step = -autocorr seed 0 := by
  have hi := translationFeature_inner source 0 step
  have h0 : translationFeature source 0 = edge 0 := by simp [edge]
  have h1 : translationFeature source step = edge 1 := by simp [edge]
  rw [h0, h1, edge_eq, edge_eq, inner_sub_left, inner_sub_right, inner_sub_right,
    atom_inner, atom_inner, atom_inner, atom_inner] at hi
  norm_num at hi
  exact_mod_cast hi.symm

end
end GaloisForLFunctions.BiScaleUncertainty.DyadicDifference
