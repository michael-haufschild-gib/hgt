import GaloisForLFunctions.HTGeometry.FiniteGeometricLayerTowerWitnesses
import GaloisForLFunctions.HTGeometry.BoundedRelationLogMagnitudeHypertranscendence

/-!
# An explicit infinite geometric layer tower

The infinite tower is the analytic datum behind the hypertranscendence law
`hypertranscendental_of_infiniteGeometricLayerTower`, but no tower is exhibited anywhere, so the law
has never produced a single hypertranscendental function.  This file builds one.

Take amplitudes `4⁻ⁱ` and ratios `1 + 2⁻ⁱ`.  The ratios are strictly decreasing to one, so they are
pairwise distinct — the injectivity the law needs — while the amplitudes decay fast enough that the
depth-`i` tail

`tailᵢ(n) = ∑_{j ≥ i} 4⁻ʲ (1 + 2⁻ʲ)ⁿ`

converges for every `n`: the ratios never exceed `2`, so the series is dominated by `2ⁿ` times a
geometric series.  Splitting off the first term is the tower's `split` field, and the tail bound
`tail_{i+1}(n) ≤ Kᵢ (1 + 2⁻⁽ⁱ⁺¹⁾)ⁿ` together with `1 + 2⁻⁽ⁱ⁺¹⁾ < 1 + 2⁻ⁱ` is its `small` field.

* **`dyadicInfiniteGeometricLayerTower`** — the tower;
* **`hypertranscendental_of_dyadicTaylorMagnitudes`** — consequently every smooth function whose
  Taylor magnitudes are eventually `exp (−tail₀ i)` is hypertranscendental.
-/

open Asymptotics Filter

namespace GaloisForLFunctions

noncomputable section

/-! ### The layer data -/

/-- The layer ratios `1 + 2⁻ⁱ`. -/
def dyadicLayerRatio (i : ℕ) : ℝ := 1 + (2 : ℝ)⁻¹ ^ i

/-- The layer amplitudes `4⁻ⁱ`. -/
def dyadicLayerAmplitude (i : ℕ) : ℝ := (4 : ℝ)⁻¹ ^ i

theorem dyadicLayerAmplitude_pos (i : ℕ) : 0 < dyadicLayerAmplitude i :=
  pow_pos (by norm_num) i

theorem dyadicLayerAmplitude_add (i j : ℕ) :
    dyadicLayerAmplitude (i + j) = dyadicLayerAmplitude i * dyadicLayerAmplitude j := by
  simp [dyadicLayerAmplitude, pow_add]

theorem one_lt_dyadicLayerRatio (i : ℕ) : 1 < dyadicLayerRatio i := by
  have h : (0 : ℝ) < (2 : ℝ)⁻¹ ^ i := pow_pos (by norm_num) i
  unfold dyadicLayerRatio
  linarith

theorem dyadicLayerRatio_pos (i : ℕ) : 0 < dyadicLayerRatio i :=
  lt_trans zero_lt_one (one_lt_dyadicLayerRatio i)

theorem dyadicLayerRatio_le_two (i : ℕ) : dyadicLayerRatio i ≤ 2 := by
  have h : (2 : ℝ)⁻¹ ^ i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold dyadicLayerRatio
  linarith

theorem dyadicLayerRatio_strictAnti : StrictAnti dyadicLayerRatio := by
  intro i j hij
  have h : (2 : ℝ)⁻¹ ^ j < (2 : ℝ)⁻¹ ^ i :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hij
  unfold dyadicLayerRatio
  linarith

theorem dyadicLayerRatio_injective : Function.Injective dyadicLayerRatio :=
  dyadicLayerRatio_strictAnti.injective

theorem dyadicLayerRatio_succ_lt (i : ℕ) : dyadicLayerRatio (i + 1) < dyadicLayerRatio i :=
  dyadicLayerRatio_strictAnti (Nat.lt_succ_self i)

theorem dyadicLayerRatio_pow_le (i j n : ℕ) :
    dyadicLayerRatio (i + j) ^ n ≤ dyadicLayerRatio i ^ n :=
  pow_le_pow_left₀ (le_of_lt (dyadicLayerRatio_pos _))
    (dyadicLayerRatio_strictAnti.antitone (Nat.le_add_right i j)) n

/-! ### Summability of the layer series -/

theorem summable_dyadicLayerAmplitude (i : ℕ) :
    Summable fun j : ℕ => dyadicLayerAmplitude (i + j) := by
  have hgeom : Summable fun j : ℕ => (4 : ℝ)⁻¹ ^ j :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  exact (hgeom.mul_left (dyadicLayerAmplitude i)).congr fun j =>
    (dyadicLayerAmplitude_add i j).symm

theorem summable_dyadicLayer (i n : ℕ) :
    Summable fun j : ℕ => dyadicLayerAmplitude (i + j) * dyadicLayerRatio (i + j) ^ n := by
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
    (((summable_dyadicLayerAmplitude i).mul_right ((2 : ℝ) ^ n)))
  · exact mul_nonneg (le_of_lt (dyadicLayerAmplitude_pos _)) (pow_nonneg (le_of_lt
      (dyadicLayerRatio_pos _)) n)
  · refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (dyadicLayerAmplitude_pos _))
    exact pow_le_pow_left₀ (le_of_lt (dyadicLayerRatio_pos _)) (dyadicLayerRatio_le_two _) n

/-- The depth-`i` tail profile `∑_{j ≥ i} 4⁻ʲ (1 + 2⁻ʲ)ⁿ`. -/
def dyadicLayerTail (i n : ℕ) : ℝ :=
  ∑' j : ℕ, dyadicLayerAmplitude (i + j) * dyadicLayerRatio (i + j) ^ n

theorem dyadicLayerTail_split (i n : ℕ) :
    dyadicLayerTail i n
      = dyadicLayerAmplitude i * dyadicLayerRatio i ^ n + dyadicLayerTail (i + 1) n := by
  rw [dyadicLayerTail, (summable_dyadicLayer i n).tsum_eq_zero_add]
  congr 1
  refine tsum_congr fun j => ?_
  have h : i + (j + 1) = i + 1 + j := by omega
  rw [h]

theorem dyadicLayerTail_nonneg (i n : ℕ) : 0 ≤ dyadicLayerTail i n :=
  tsum_nonneg fun _ => mul_nonneg (le_of_lt (dyadicLayerAmplitude_pos _))
    (pow_nonneg (le_of_lt (dyadicLayerRatio_pos _)) n)

theorem dyadicLayerTail_le (i n : ℕ) :
    dyadicLayerTail i n ≤ (∑' j : ℕ, dyadicLayerAmplitude (i + j)) * dyadicLayerRatio i ^ n := by
  rw [← tsum_mul_right]
  refine (summable_dyadicLayer i n).tsum_le_tsum (fun j => ?_)
    ((summable_dyadicLayerAmplitude i).mul_right _)
  exact mul_le_mul_of_nonneg_left (dyadicLayerRatio_pow_le i j n)
    (le_of_lt (dyadicLayerAmplitude_pos _))

/-- The tail at depth `i + 1` is little-`o` of the layer ratio at depth `i`: it is `O` of the next
ratio, which is strictly smaller. -/
theorem dyadicLayerTail_isLittleO (i : ℕ) :
    (fun n => dyadicLayerTail (i + 1) n) =o[atTop] fun n : ℕ => dyadicLayerRatio i ^ n := by
  have hbig : (fun n => dyadicLayerTail (i + 1) n) =O[atTop]
      fun n : ℕ => dyadicLayerRatio (i + 1) ^ n := by
    refine Asymptotics.IsBigO.of_bound (∑' j : ℕ, dyadicLayerAmplitude (i + 1 + j))
      (Filter.Eventually.of_forall fun n => ?_)
    rw [Real.norm_of_nonneg (dyadicLayerTail_nonneg _ _),
      Real.norm_of_nonneg (pow_nonneg (le_of_lt (dyadicLayerRatio_pos _)) n)]
    exact dyadicLayerTail_le (i + 1) n
  refine hbig.trans_isLittleO ?_
  exact isLittleO_pow_pow_of_lt_left (le_of_lt (dyadicLayerRatio_pos (i + 1)))
    (dyadicLayerRatio_succ_lt i)

/-! ### The tower -/

/-- **An explicit infinite geometric layer tower**, with amplitudes `4⁻ⁱ` and pairwise distinct
ratios `1 + 2⁻ⁱ`. -/
def dyadicInfiniteGeometricLayerTower :
    InfiniteGeometricLayerTower (fun n => dyadicLayerTail 0 n) where
  amplitude := dyadicLayerAmplitude
  ratio := dyadicLayerRatio
  tail := dyadicLayerTail
  tail_zero := rfl
  amplitude_pos := dyadicLayerAmplitude_pos
  ratio_one_lt := one_lt_dyadicLayerRatio
  split := fun i => funext fun n => dyadicLayerTail_split i n
  small := dyadicLayerTail_isLittleO

/-- **A concrete hypertranscendence criterion.**  A smooth function whose Taylor magnitudes are
eventually `exp (−tail₀ i)` for the dyadic layer profile is hypertranscendental: the tower has
infinitely many distinct ratios, so no nonzero integer shift polynomial can vanish at all of
them. -/
theorem hypertranscendental_of_dyadicTaylorMagnitudes {f : ℂ → ℂ}
    (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    (hb : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-dyadicLayerTail 0 i)) :
    Hypertranscendental f :=
  hypertranscendental_of_infiniteGeometricLayerTower hf dyadicInfiniteGeometricLayerTower
    dyadicLayerRatio_injective hb

/-! ### An explicit hypertranscendental entire function -/

/-- The depth-zero profile dominates `2ⁿ`: its first layer is `1 · 2ⁿ` and the rest is
nonnegative. -/
theorem two_pow_le_dyadicLayerTail_zero (n : ℕ) : (2 : ℝ) ^ n ≤ dyadicLayerTail 0 n := by
  have hsplit := dyadicLayerTail_split 0 n
  have h0 : dyadicLayerAmplitude 0 = 1 := by simp [dyadicLayerAmplitude]
  have h1 : dyadicLayerRatio 0 = 2 := by norm_num [dyadicLayerRatio]
  have h2 := dyadicLayerTail_nonneg 1 n
  rw [h0, h1] at hsplit
  linarith

/-- The profile grows superlinearly, which is what makes the exponential series entire. -/
theorem tendsto_dyadicLayerTail_zero_div_atTop :
    Tendsto (fun n : ℕ => dyadicLayerTail 0 n / (n : ℝ)) atTop atTop := by
  have hlo : (fun n : ℕ => (n : ℝ)) =o[atTop] fun n : ℕ => (2 : ℝ) ^ n :=
    isLittleO_coe_const_pow_of_one_lt (by norm_num)
  have hzero : Tendsto (fun n : ℕ => (n : ℝ) / (2 : ℝ) ^ n) atTop (nhds 0) :=
    hlo.tendsto_div_nhds_zero
  have hpos : ∀ᶠ n : ℕ in atTop, (n : ℝ) / (2 : ℝ) ^ n ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact Set.mem_Ioi.mpr (div_pos hn' (pow_pos (by norm_num) n))
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) / (2 : ℝ) ^ n)⁻¹) atTop atTop :=
    Filter.Tendsto.inv_tendsto_nhdsGT_zero
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hzero hpos)
  refine tendsto_atTop_mono' atTop ?_ hinv
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [inv_div]
  gcongr
  exact two_pow_le_dyadicLayerTail_zero n

/-- The entire series with coefficients `exp (−tail₀ n)`. -/
def dyadicLayerEntireFunction : ℂ → ℂ :=
  boundedRelationExponentialFunction (dyadicLayerTail 0) (fun _ => 1)

theorem contDiff_dyadicLayerEntireFunction :
    ContDiff ℂ (⊤ : ℕ∞) dyadicLayerEntireFunction :=
  contDiff_boundedRelationExponentialFunction tendsto_dyadicLayerTail_zero_div_atTop
    (fun _ => norm_one)

theorem norm_coeff_taylorPS_dyadicLayerEntireFunction (n : ℕ) :
    ‖PowerSeries.coeff n (taylorPS dyadicLayerEntireFunction)‖
      = Real.exp (-dyadicLayerTail 0 n) := by
  rw [dyadicLayerEntireFunction,
    taylorPS_boundedRelationExponentialFunction tendsto_dyadicLayerTail_zero_div_atTop
      (fun _ => norm_one) n]
  exact norm_boundedRelationExponentialCoeff (fun _ => norm_one) n

/-- **An explicit hypertranscendental entire function.**  The power series whose `n`-th coefficient
is `exp (−∑_{j} 4⁻ʲ (1 + 2⁻ʲ)ⁿ)` is entire and satisfies no algebraic differential equation: its
Taylor magnitudes carry an infinite tower of geometric layers with pairwise distinct ratios, and a
nonzero integer shift polynomial cannot vanish at infinitely many points. -/
theorem hypertranscendental_dyadicLayerEntireFunction :
    Hypertranscendental dyadicLayerEntireFunction :=
  hypertranscendental_of_dyadicTaylorMagnitudes contDiff_dyadicLayerEntireFunction
    (Filter.Eventually.of_forall norm_coeff_taylorPS_dyadicLayerEntireFunction)

end

end GaloisForLFunctions
