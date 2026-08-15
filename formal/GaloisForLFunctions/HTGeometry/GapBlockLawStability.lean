import GaloisForLFunctions.HTGeometry.GenericGapSequence
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Perturbed gap sequences carry the same block empirical laws

A coordinatewise vanishing perturbation of a gap sequence leaves every Cesàro block average with a
Lipschitz test function unchanged, because the perturbation of each test value tends to zero and
Cesàro means of a null sequence vanish.

Shrinking location radii applied to the partial sums of a gap sequence produce such a perturbation
while keeping the sequence of locations strictly increasing with the same asymptotic density.
-/

open Filter Metric
open scoped Topology NNReal

namespace GaloisForLFunctions.HTGeometry

/-! ### Block stability -/

theorem tendsto_sum_abs_sub (k : ℕ) {d g : ℕ → ℝ}
    (hdg : Tendsto (fun j => d j - g j) atTop (𝓝 0)) :
    Tendsto (fun j : ℕ => ∑ i : Fin k, |d (j + i) - g (j + i)|) atTop (𝓝 0) := by
  have hcoord : ∀ i : Fin k,
      Tendsto (fun j : ℕ => |d (j + (i : ℕ)) - g (j + (i : ℕ))|) atTop (𝓝 0) := by
    intro i
    have hshift : Tendsto (fun j : ℕ => j + (i : ℕ)) atTop atTop :=
      Filter.tendsto_add_atTop_nat (i : ℕ)
    have h := hdg.comp hshift
    have habs : Tendsto (fun j : ℕ => |d (j + (i : ℕ)) - g (j + (i : ℕ))|) atTop (𝓝 |(0 : ℝ)|) :=
      (continuous_abs.tendsto _).comp h
    simpa using habs
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin k)) fun i _ => hcoord i
  simpa using hsum

theorem tendsto_dist_block (k : ℕ) {d g : ℕ → ℝ}
    (hdg : Tendsto (fun j => d j - g j) atTop (𝓝 0)) :
    Tendsto (fun j : ℕ => dist (fun i : Fin k => d (j + i)) (fun i : Fin k => g (j + i)))
      atTop (𝓝 0) := by
  refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_) (tendsto_sum_abs_sub k hdg)
  refine (dist_pi_le_iff (Finset.sum_nonneg fun _ _ => abs_nonneg _)).2 fun i => ?_
  rw [Real.dist_eq]
  exact Finset.single_le_sum (f := fun i' : Fin k => |d (j + (i' : ℕ)) - g (j + (i' : ℕ))|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-- **A coordinatewise vanishing perturbation preserves every Lipschitz block average.** -/
theorem tendsto_block_average_of_tendsto_sub {d g : ℕ → ℝ}
    (hdg : Tendsto (fun j => d j - g j) atTop (𝓝 0))
    (k : ℕ) {Φ : (Fin k → ℝ) → ℝ} {C : ℝ≥0} (hΦ : LipschitzWith C Φ) {L : ℝ}
    (hg : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, Φ (fun i : Fin k => g (j + i)))
      atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, Φ (fun i : Fin k => d (j + i)))
      atTop (𝓝 L) := by
  set u : ℕ → ℝ := fun j =>
    Φ (fun i : Fin k => d (j + i)) - Φ (fun i : Fin k => g (j + i)) with hu
  have hunull : Tendsto u atTop (𝓝 0) := by
    have hcd : Tendsto (fun j : ℕ =>
        (C : ℝ) * dist (fun i : Fin k => d (j + (i : ℕ))) (fun i : Fin k => g (j + (i : ℕ))))
        atTop (𝓝 0) := by
      simpa using (tendsto_dist_block k hdg).const_mul (C : ℝ)
    refine squeeze_zero_norm (fun j => ?_) hcd
    have := hΦ.dist_le_mul (fun i : Fin k => d (j + (i : ℕ))) (fun i : Fin k => g (j + (i : ℕ)))
    rw [Real.dist_eq] at this
    simpa [hu, Real.norm_eq_abs] using this
  have hcesaro : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, u j) atTop (𝓝 0) := by
    simpa using hunull.cesaro
  have hsum : ∀ N : ℕ,
      (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, Φ (fun i : Fin k => d (j + i))
        = (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, Φ (fun i : Fin k => g (j + i))
          + (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, u j := by
    intro N
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hu]
  refine Tendsto.congr (fun N => (hsum N).symm) ?_
  simpa using hg.add hcesaro

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Filter Metric
open scoped Topology NNReal

/-! ### Shrinking location radii -/

/-- Partial sums of a gap sequence, started at one. -/
def gapPartialSum (g : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => gapPartialSum g j + g j

theorem gapPartialSum_eq (g : ℕ → ℝ) (j : ℕ) :
    gapPartialSum g j = 1 + ∑ i ∈ Finset.range j, g i := by
  induction j with
  | zero => simp [gapPartialSum]
  | succ j ih => rw [gapPartialSum, ih, Finset.sum_range_succ]; ring

/-- The previous gap, with the convention that the gap before the first one is `1`. -/
def prevGap (g : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => g j

/-- Shrinking radii for the location perturbation. -/
noncomputable def gapRadius (g : ℕ → ℝ) (j : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ j * min 1 (min (prevGap g j) (g j)) / 16

theorem gapRadius_pos {g : ℕ → ℝ} (hg : ∀ j, 0 < g j) (j : ℕ) : 0 < gapRadius g j := by
  have hprev : 0 < prevGap g j := by
    cases j with
    | zero => norm_num [prevGap]
    | succ j => exact hg j
  have hmin : 0 < min 1 (min (prevGap g j) (g j)) :=
    lt_min zero_lt_one (lt_min hprev (hg j))
  have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity
  rw [gapRadius]
  positivity

theorem gapRadius_le_pow (g : ℕ → ℝ) (j : ℕ) : gapRadius g j ≤ (1 / 2 : ℝ) ^ j / 16 := by
  have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity
  have hmin : min 1 (min (prevGap g j) (g j)) ≤ 1 := min_le_left _ _
  rw [gapRadius]
  have := mul_le_mul_of_nonneg_left hmin (le_of_lt hpow)
  rw [mul_one] at this
  linarith

theorem gapRadius_le_gap_self {g : ℕ → ℝ} (hg : ∀ j, 0 < g j) (j : ℕ) :
    gapRadius g j ≤ g j / 16 := by
  have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity
  have hpow1 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hmin : min 1 (min (prevGap g j) (g j)) ≤ g j :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hmin0 : 0 ≤ min 1 (min (prevGap g j) (g j)) := by
    have hprev : 0 < prevGap g j := by
      cases j with
      | zero => norm_num [prevGap]
      | succ j => exact hg j
    exact le_of_lt (lt_min zero_lt_one (lt_min hprev (hg j)))
  rw [gapRadius]
  have h1 : (1 / 2 : ℝ) ^ j * min 1 (min (prevGap g j) (g j))
      ≤ min 1 (min (prevGap g j) (g j)) := by
    nlinarith
  linarith

theorem gapRadius_succ_le_gap {g : ℕ → ℝ} (hg : ∀ j, 0 < g j) (j : ℕ) :
    gapRadius g (j + 1) ≤ g j / 16 := by
  have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ (j + 1) := by positivity
  have hpow1 : (1 / 2 : ℝ) ^ (j + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hmin : min 1 (min (prevGap g (j + 1)) (g (j + 1))) ≤ g j := by
    have : prevGap g (j + 1) = g j := rfl
    rw [← this]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hmin0 : 0 ≤ min 1 (min (prevGap g (j + 1)) (g (j + 1))) := by
    have hprev : 0 < prevGap g (j + 1) := hg j
    exact le_of_lt (lt_min zero_lt_one (lt_min hprev (hg (j + 1))))
  rw [gapRadius]
  nlinarith

theorem tendsto_gapRadius (g : ℕ → ℝ) (hg : ∀ j, 0 < g j) :
    Tendsto (gapRadius g) atTop (𝓝 0) := by
  refine squeeze_zero (fun j => le_of_lt (gapRadius_pos hg j)) (gapRadius_le_pow g) ?_
  have hpow : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa using hpow.div_const 16

/-- The perturbed locations. -/
noncomputable def gapLocation (g : ℕ → ℝ) (θ : ℕ → ℝ) (j : ℕ) : ℝ :=
  gapPartialSum g j + gapRadius g j * Real.tanh (θ j)

theorem abs_gapRadius_mul_tanh_le {g : ℕ → ℝ} (hg : ∀ j, 0 < g j) (θ : ℕ → ℝ) (j : ℕ) :
    |gapRadius g j * Real.tanh (θ j)| ≤ gapRadius g j := by
  rw [abs_mul, abs_of_pos (gapRadius_pos hg j)]
  have ht : |Real.tanh (θ j)| ≤ 1 := by
    rw [abs_le]
    exact ⟨le_of_lt (Real.neg_one_lt_tanh _), le_of_lt (Real.tanh_lt_one _)⟩
  nlinarith [gapRadius_pos hg j]

/-- **The perturbed gaps differ from the prescribed gaps by a null sequence.** -/
theorem tendsto_gapLocation_diff_sub {g : ℕ → ℝ} (hg : ∀ j, 0 < g j) (θ : ℕ → ℝ) :
    Tendsto (fun j => (gapLocation g θ (j + 1) - gapLocation g θ j) - g j) atTop (𝓝 0) := by
  have hbound : ∀ j, ‖(gapLocation g θ (j + 1) - gapLocation g θ j) - g j‖
      ≤ gapRadius g (j + 1) + gapRadius g j := by
    intro j
    have hps : gapPartialSum g (j + 1) = gapPartialSum g j + g j := rfl
    have h1 := abs_gapRadius_mul_tanh_le hg θ (j + 1)
    have h2 := abs_gapRadius_mul_tanh_le hg θ j
    have heq : (gapLocation g θ (j + 1) - gapLocation g θ j) - g j
        = gapRadius g (j + 1) * Real.tanh (θ (j + 1)) - gapRadius g j * Real.tanh (θ j) := by
      simp only [gapLocation, hps]
      ring
    rw [Real.norm_eq_abs, heq]
    exact le_trans (abs_sub _ _) (add_le_add h1 h2)
  refine squeeze_zero_norm hbound ?_
  have h1 : Tendsto (fun j : ℕ => gapRadius g (j + 1)) atTop (𝓝 0) :=
    (tendsto_gapRadius g hg).comp (Filter.tendsto_add_atTop_nat 1)
  have h2 := tendsto_gapRadius g hg
  simpa using h1.add h2

/-- The perturbed locations remain strictly increasing. -/
theorem gapLocation_lt_succ {g : ℕ → ℝ} (hg : ∀ j, 0 < g j) (θ : ℕ → ℝ) (j : ℕ) :
    gapLocation g θ j < gapLocation g θ (j + 1) := by
  have hps : gapPartialSum g (j + 1) = gapPartialSum g j + g j := rfl
  have h1 := abs_gapRadius_mul_tanh_le hg θ (j + 1)
  have h2 := abs_gapRadius_mul_tanh_le hg θ j
  have h1' : -(gapRadius g (j + 1)) ≤ gapRadius g (j + 1) * Real.tanh (θ (j + 1)) :=
    neg_le_of_abs_le h1
  have h2' : gapRadius g j * Real.tanh (θ j) ≤ gapRadius g j := le_of_abs_le h2
  have hr1 := gapRadius_succ_le_gap hg j
  have hr2 := gapRadius_le_gap_self hg j
  simp only [gapLocation, hps]
  linarith [hg j]

theorem gapLocation_strictMono {g : ℕ → ℝ} (hg : ∀ j, 0 < g j) (θ : ℕ → ℝ) :
    StrictMono (gapLocation g θ) :=
  strictMono_nat_of_lt_succ (gapLocation_lt_succ hg θ)

theorem gapLocation_pos {g : ℕ → ℝ} (hg : ∀ j, 0 < g j) (θ : ℕ → ℝ) (j : ℕ) :
    0 < gapLocation g θ j := by
  have hzero : 0 < gapLocation g θ 0 := by
    have h2 := abs_gapRadius_mul_tanh_le hg θ 0
    have h2' : -(gapRadius g 0) ≤ gapRadius g 0 * Real.tanh (θ 0) := neg_le_of_abs_le h2
    have hr : gapRadius g 0 ≤ (1 / 2 : ℝ) ^ (0 : ℕ) / 16 := gapRadius_le_pow g 0
    have hps : gapPartialSum g 0 = 1 := rfl
    simp only [gapLocation, hps]
    norm_num at hr
    linarith
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact hzero
  · exact lt_of_lt_of_le hzero (le_of_lt ((gapLocation_strictMono hg θ) hj))

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Filter Metric
open scoped Topology NNReal

/-- The partial sums of a mean-one gap sequence have unit asymptotic density. -/
theorem tendsto_gapPartialSum_div (g : ℕ → ℝ)
    (hg : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, g j) atTop (𝓝 1)) :
    Tendsto (fun j : ℕ => gapPartialSum g j / j) atTop (𝓝 1) := by
  have heq : ∀ j : ℕ, gapPartialSum g j / (j : ℝ)
      = (j : ℝ)⁻¹ + (j : ℝ)⁻¹ * ∑ i ∈ Finset.range j, g i := by
    intro j
    rw [gapPartialSum_eq, div_eq_inv_mul, mul_add, mul_one]
  have hinv : Tendsto (fun j : ℕ => (j : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hsum := hinv.add hg
  rw [zero_add] at hsum
  exact hsum.congr fun j => (heq j).symm

/-- The perturbed locations have unit asymptotic density. -/
theorem tendsto_gapLocation_div {g : ℕ → ℝ} (hgpos : ∀ j, 0 < g j) (θ : ℕ → ℝ)
    (hg : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, g j) atTop (𝓝 1)) :
    Tendsto (fun j : ℕ => gapLocation g θ j / j) atTop (𝓝 1) := by
  have hpert : Tendsto (fun j : ℕ => gapRadius g j * Real.tanh (θ j) / (j : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun j => ?_) (tendsto_gapRadius g hgpos)
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [gapRadius_pos hgpos 0 |>.le]
    · have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
      have hjpos : (0 : ℝ) < (j : ℝ) := by linarith
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hjpos, div_le_iff₀ hjpos]
      have h1 := abs_gapRadius_mul_tanh_le hgpos θ j
      nlinarith [gapRadius_pos hgpos j, h1]
  have hsum := (tendsto_gapPartialSum_div g hg).add hpert
  rw [add_zero] at hsum
  refine hsum.congr fun j => ?_
  rw [gapLocation, add_div]

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Metric
open scoped Topology NNReal

/-- The gaps of the perturbed location sequence. -/
noncomputable def gapLocationGap (g : ℕ → ℝ) (θ : ℕ → ℝ) (j : ℕ) : ℝ :=
  gapLocation g θ (j + 1) - gapLocation g θ j

/-- **Every stationary ergodic positive gap law of mean one is realized, for every bounded
perturbation parameter, by a strictly increasing positive location sequence of unit density whose
gaps carry exactly the prescribed finite-block law.** -/
theorem exists_prescribedGapProcess_locations
    {P : Measure (ℕ → ℝ)} [IsProbabilityMeasure P]
    (hErg : Ergodic shiftSeq P) (hint : Integrable (fun ω => ω 0) P)
    (hmean : ∫ ω, ω 0 ∂P = 1) (hpos : ∀ᵐ ω ∂P, ∀ n, 0 < ω n) :
    ∃ g : ℕ → ℝ, (∀ j, 0 < g j) ∧
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, g j) atTop (𝓝 1) ∧
      ∀ θ : ℕ → ℝ,
        StrictMono (gapLocation g θ) ∧ (∀ j, 0 < gapLocation g θ j) ∧
        Tendsto (fun j : ℕ => gapLocation g θ j / j) atTop (𝓝 1) ∧
        ∀ (k : ℕ) (Φ : (Fin k → ℝ) → ℝ) (C : ℝ≥0), LipschitzWith C Φ →
          (∃ M : ℝ, ∀ x, |Φ x| ≤ M) →
          Tendsto
            (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
              Φ (fun i : Fin k => gapLocationGap g θ (j + i)))
            atTop (𝓝 (∫ ω, Φ (blockMap k ω) ∂P)) := by
  obtain ⟨g, hgpos, hgmean, hgblock⟩ := exists_generic_sequence hErg hint hmean hpos
  refine ⟨g, hgpos, hgmean, fun θ => ?_⟩
  refine ⟨gapLocation_strictMono hgpos θ, gapLocation_pos hgpos θ,
    tendsto_gapLocation_div hgpos θ hgmean, ?_⟩
  intro k Φ C hΦ hΦb
  have hdg : Tendsto (fun j => gapLocationGap g θ j - g j) atTop (𝓝 0) :=
    tendsto_gapLocation_diff_sub hgpos θ
  exact tendsto_block_average_of_tendsto_sub hdg k hΦ (hgblock k Φ hΦ.continuous hΦb)

end GaloisForLFunctions.HTGeometry
