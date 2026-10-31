import GaloisForLFunctions.RHTower.XiCosineShiftCriticalScaleProducer
import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergUpper
import GaloisForLFunctions.RHTower.RHLadderTheory

/-!
# The off-line second moment is `o(V)`

**Theorem** (`tendsto_offLineSecondMoment_div`).  The squared-depth moment of the zeros,
`Σ_{0 < Im ρ ≤ V} m(ρ) (Re ρ − ½)₊²` (`offLineSecondMoment`), is `o(V)`.

So the off-line first moment `Σ m (Re ρ − ½)₊ ≤ (67/1000) V` sits at depths `o(1)`: the depth mass
`Σ m (Re ρ − ½)²` of a unit window is `o(1)` on average over the heights.

**Deep zeros** (`tendsto_offLineCountBeyond_div`, `eventually_volume_deepWindow_le`).  For every
fixed depth `d₀ > 0` the zeros with `Re ρ ≥ ½ + d₀` number `o(V)`, so the window centres
`S ∈ [T − 1, 2T + 1]` whose window `|Im ρ − S| ≤ 1` holds a zero of depth `≥ d₀` have measure
`o(T)`: the deep-companion input of the lag family holds, with no companion at all, for almost all
heights.

**Proof.**  For `x ≤ ½`, `x₊² ≤ ½ (x − d)₊ + d x₊` (`sq_max_le_half_tail_add`): below `d` use
`x ≤ d`, above it `x(x − d) ≤ ½(x − d)`.  With `d = R/log V`, the tail law with Selberg's mollifier
(`eventually_offLineTail_le_selberg`) gives `4π Σ m (x − d)₊ ≤ (g(R) + η) V` with `g(R) → 0`
(`tendsto_selbergTailRate`), and the first moment (`eventually_offLineMoment_le_selberg_upper`)
makes `d Σ m x₊ ≤ (67/1000) R V/log V = o(V)`.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-- The squared-depth moment `Σ_{0 < Im ρ ≤ V} m(ρ) (Re ρ − ½)₊²`. -/
def offLineSecondMoment (V : ℝ) : ℝ :=
  ∑ z ∈ stripFinsetPos V, ((analyticOrderAt xi z).toNat : ℝ) * max (z.re - 1 / 2) 0 ^ 2

theorem offLineSecondMoment_nonneg (V : ℝ) : 0 ≤ offLineSecondMoment V :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- `x₊² ≤ ½ (x − d)₊ + d x₊` for `x ≤ ½`. -/
theorem sq_max_le_half_tail_add {x d : ℝ} (hx : x ≤ 1 / 2) :
    max x 0 ^ 2 ≤ 1 / 2 * max (x - d) 0 + d * max x 0 := by
  rcases le_or_gt x 0 with h0 | h0
  · rw [max_eq_right h0]
    have : 0 ≤ max (x - d) 0 := le_max_right _ _
    nlinarith
  rw [max_eq_left h0.le]
  rcases le_or_gt x d with h1 | h1
  · rw [max_eq_right (by linarith)]
    nlinarith
  · rw [max_eq_left (by linarith)]
    nlinarith

/-- The zero-shift tail is at most the off-line first moment. -/
theorem offLineTail_zero_le_offLineMoment (V : ℝ) : offLineTail 0 V ≤ offLineMoment V := by
  unfold offLineTail offLineMoment
  rw [← Finset.sum_filter_add_sum_filter_not (stripFinsetPos V) (fun z => 1 / 2 < z.re)]
  have h0 : ∑ z ∈ (stripFinsetPos V).filter (fun z => ¬ 1 / 2 < z.re),
      ((analyticOrderAt xi z).toNat : ℝ) * max (z.re - 1 / 2 - 0) 0 = 0 :=
    Finset.sum_eq_zero fun z hz => by
      rw [max_eq_right (by linarith [not_lt.mp (Finset.mem_filter.mp hz).2]), mul_zero]
  rw [h0, add_zero]
  refine (Finset.sum_le_sum fun z hz => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (s := (stripFinsetPos V).filter (fun z => 1 / 2 < z.re))
      ?_ fun z hz _ => offLineMoment_term_nonneg hz)
  · rw [sub_zero, max_eq_left (by linarith [(Finset.mem_filter.mp hz).2])]
  · intro z hz
    obtain ⟨hzs, hre⟩ := Finset.mem_filter.mp hz
    obtain ⟨-, hre1, him0, himV, hxi⟩ := mem_stripFinsetPos.mp hzs
    rw [mem_boxFinsetLe]
    exact ⟨hre, hre1, him0.le, himV, hxi⟩

/-- **The off-line second moment is `o(V)`.** -/
theorem tendsto_offLineSecondMoment_div :
    Tendsto (fun V => offLineSecondMoment V / V) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- a scale `R` with `g(R) < ε`
  obtain ⟨R, hR0, hRg⟩ : ∃ R : ℝ, 0 < R ∧ selbergTailRate R < ε := by
    obtain ⟨R, hR⟩ := (tendsto_selbergTailRate.eventually (gt_mem_nhds hε)).and
      (eventually_gt_atTop (0 : ℝ)) |>.exists
    exact ⟨R, hR.2, hR.1⟩
  have hev : ∀ᶠ V in atTop, offLineSecondMoment V ≤ ε / 2 * V := by
    have hlogV : ∀ᶠ V : ℝ in atTop, 1000 * R / ε ≤ Real.log V :=
      Real.tendsto_log_atTop.eventually_ge_atTop _
    filter_upwards [eventually_offLineTail_le_selberg hR0 hε,
      ZetaGateProductAFE.eventually_offLineMoment_le_selberg_upper, hlogV,
      eventually_ge_atTop (1 : ℝ)] with V htail hmom hL hV1
    have hL0 : 0 < Real.log V := lt_of_lt_of_le (by positivity) hL
    set d := R / Real.log V with hd
    have hd0 : 0 ≤ d := by positivity
    -- termwise `x₊² ≤ ½ (x − d)₊ + d x₊`
    have hterm : offLineSecondMoment V ≤ 1 / 2 * offLineTail d V + d * offLineTail 0 V := by
      unfold offLineSecondMoment offLineTail
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun z hz => ?_
      have hre1 := (mem_stripFinsetPos.mp hz).2.1
      have h := sq_max_le_half_tail_add (d := d) (show z.re - 1 / 2 ≤ 1 / 2 by linarith)
      have hm : (0 : ℝ) ≤ ((analyticOrderAt xi z).toNat : ℝ) := Nat.cast_nonneg _
      rw [sub_zero]
      calc ((analyticOrderAt xi z).toNat : ℝ) * max (z.re - 1 / 2) 0 ^ 2
          ≤ ((analyticOrderAt xi z).toNat : ℝ) * (1 / 2 * max (z.re - 1 / 2 - d) 0
              + d * max (z.re - 1 / 2) 0) := mul_le_mul_of_nonneg_left h hm
        _ = _ := by ring
    have h0 := (offLineTail_zero_le_offLineMoment V).trans hmom
    have hπ : 1 / (8 * Real.pi) < 1 / 4 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith [Real.pi_gt_three]
    have htail' : offLineTail d V ≤ (selbergTailRate R + ε) * V / (4 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hdV : d * offLineTail 0 V ≤ ε / 1000 * (67 / 1000 * V) := by
      have hdε : d ≤ ε / 1000 := by
        rw [hd, div_le_iff₀ hL0]
        have := (div_le_iff₀ hε).mp hL
        linarith
      calc d * offLineTail 0 V ≤ d * (67 / 1000 * V) :=
            mul_le_mul_of_nonneg_left h0 hd0
        _ ≤ ε / 1000 * (67 / 1000 * V) :=
            mul_le_mul_of_nonneg_right hdε (by positivity)
    have hg : selbergTailRate R + ε ≤ 2 * ε := by linarith
    have hfirst : 1 / 2 * offLineTail d V ≤ ε * V / (4 * Real.pi) := by
      have : (selbergTailRate R + ε) * V / (4 * Real.pi) ≤ 2 * ε * V / (4 * Real.pi) := by
        gcongr
      have e : 2 * ε * V / (4 * Real.pi) = 2 * (ε * V / (4 * Real.pi)) := by ring
      linarith
    have hπ' : ε * V / (4 * Real.pi) ≤ ε / 4 * V := by
      rw [div_le_iff₀ (by positivity)]
      have : 0 ≤ ε * V := by positivity
      nlinarith [Real.pi_gt_three]
    nlinarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hev.and (eventually_gt_atTop (0 : ℝ)))
  refine ⟨N, fun V hV => ?_⟩
  obtain ⟨h1, hV0⟩ := hN V hV
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (offLineSecondMoment_nonneg V) hV0.le),
    div_lt_iff₀ hV0]
  nlinarith

/-! ## Deep zeros -/

/-- **Deep zeros are `o(V)`.**  For `d₀ > 0`, `#{Re ρ ≥ ½ + d₀, 0 < Im ρ ≤ V} = o(V)`. -/
theorem tendsto_offLineCountBeyond_div {d₀ : ℝ} (hd₀ : 0 < d₀) :
    Tendsto (fun V => offLineCountBeyond d₀ V / V) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R, hR0, hRg⟩ : ∃ R : ℝ, 0 < R ∧ selbergTailRate R < ε * d₀ := by
    obtain ⟨R, hR⟩ := (tendsto_selbergTailRate.eventually
      (gt_mem_nhds (show (0 : ℝ) < ε * d₀ by positivity))).and
      (eventually_gt_atTop (0 : ℝ)) |>.exists
    exact ⟨R, hR.2, hR.1⟩
  have hev : ∀ᶠ V in atTop, offLineCountBeyond d₀ V ≤ ε / 2 * V := by
    filter_upwards [eventually_offLineTail_le_selberg hR0 (show (0 : ℝ) < ε * d₀ by positivity),
      Real.tendsto_log_atTop.eventually_ge_atTop (2 * R / d₀), eventually_gt_atTop (0 : ℝ)]
      with V htail hL hV0
    have hL0 : 0 < Real.log V := lt_of_lt_of_le (by positivity) hL
    have hshift : R / Real.log V ≤ d₀ / 2 := by
      rw [div_le_iff₀ hL0]; rw [div_le_iff₀ hd₀] at hL; linarith
    have h1 := mul_offLineCountBeyond_le_offLineTail (d₀ / 2) V
    rw [show 2 * (d₀ / 2) = d₀ by ring] at h1
    have h2 := offLineTail_anti hshift (T := V)
    have hπ : (1 : ℝ) ≤ 4 * Real.pi := by linarith [Real.pi_gt_three]
    have h3 : offLineTail (R / Real.log V) V ≤ 2 * ε * d₀ * V / (4 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h4 : 2 * ε * d₀ * V / (4 * Real.pi) ≤ 2 * ε * d₀ * V / 4 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
      linarith [Real.pi_gt_three]
    have hc0 : 0 ≤ offLineCountBeyond d₀ V := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    nlinarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hev.and (eventually_gt_atTop (0 : ℝ)))
  refine ⟨N, fun V hV => ?_⟩
  obtain ⟨h1, hV0⟩ := hN V hV
  have hc0 : 0 ≤ offLineCountBeyond d₀ V := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hc0 hV0.le), div_lt_iff₀ hV0]
  nlinarith

/-- The window centres that see a zero of depth `≥ d₀` are covered by the unit neighbourhoods of the
deep ordinates: their measure is at most `2 #{Re ρ ≥ ½ + d₀, 0 < Im ρ ≤ 2T + 2}`. -/
theorem volume_deepWindow_le {d₀ T : ℝ} (hd₀ : 0 < d₀) (hT : 3 ≤ T) :
    MeasureTheory.volume {S ∈ Icc (T - 1) (2 * T + 1) | ∃ ρ : ℂ, xi ρ = 0 ∧
        d₀ ≤ |ρ.re - 1 / 2| ∧ |ρ.im - S| ≤ 1}
      ≤ ENNReal.ofReal (2 * offLineCountBeyond d₀ (2 * T + 2)) := by
  classical
  set F := (stripFinsetPos (2 * T + 2)).filter (fun z => 1 / 2 + d₀ ≤ z.re) with hF
  have hsub : {S ∈ Icc (T - 1) (2 * T + 1) | ∃ ρ : ℂ, xi ρ = 0 ∧
      d₀ ≤ |ρ.re - 1 / 2| ∧ |ρ.im - S| ≤ 1} ⊆ ⋃ z ∈ F, Icc (z.im - 1) (z.im + 1) := by
    rintro S ⟨hS, ρ, hρ, hd, hdist⟩
    have hlt1 : ρ.re < 1 := by
      by_contra h; push Not at h; exact xi_ne_zero_of_one_le_re h hρ
    have hgt0 : 0 < ρ.re := by
      by_contra h
      push Not at h
      apply xi_ne_zero_of_one_le_re (ρ := 1 - ρ) (by simp; linarith)
      rw [xi_one_sub]; exact hρ
    -- the right member of the pair
    obtain ⟨w, hw, hwre, hwim⟩ : ∃ w : ℂ, xi w = 0 ∧ w.re = 1 / 2 + |ρ.re - 1 / 2| ∧
        w.im = ρ.im := by
      rcases le_or_gt (1 / 2) ρ.re with h | h
      · exact ⟨ρ, hρ, by rw [abs_of_nonneg (by linarith)]; ring, rfl⟩
      · refine ⟨1 - (starRingEnd ℂ) ρ, by rw [xi_one_sub, xi_conj, hρ, map_zero], ?_, by simp⟩
        rw [abs_of_neg (by linarith)]; simp; ring
    have hrhalf : |ρ.re - 1 / 2| < 1 / 2 := by rw [abs_lt]; constructor <;> linarith
    have hwmem : w ∈ F := by
      refine Finset.mem_filter.mpr
        ⟨mem_stripFinsetPos.mpr ⟨?_, ?_, ?_, ?_, hw⟩, by rw [hwre]; linarith⟩
      · rw [hwre]; positivity
      · rw [hwre]; linarith
      · rw [hwim]; have := abs_le.mp hdist; linarith [hS.1]
      · rw [hwim]; have := abs_le.mp hdist; linarith [hS.2]
    refine Set.mem_iUnion₂.mpr ⟨w, hwmem, ?_⟩
    have := abs_le.mp hdist
    rw [hwim]
    exact ⟨by linarith, by linarith⟩
  refine (MeasureTheory.measure_mono hsub).trans
    ((MeasureTheory.measure_biUnion_finset_le _ _).trans ?_)
  have hterm : ∀ z ∈ F, MeasureTheory.volume (Icc (z.im - 1) (z.im + 1))
      ≤ ENNReal.ofReal (2 * ((analyticOrderAt xi z).toNat : ℝ)) := by
    intro z hz
    have hxi := (mem_stripFinsetPos.mp (Finset.mem_filter.mp hz).1).2.2.2.2
    have hm : (1 : ℝ) ≤ ((analyticOrderAt xi z).toNat : ℝ) := by
      have := xi_order_toNat_ne_zero hxi
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun z _ => by positivity, ← Finset.mul_sum]

/-- **The deep-companion input holds for almost all heights.**  For `d₀ > 0` and `ε > 0`, for all
large `T`, the centres `S ∈ [T − 1, 2T + 1]` whose window `|Im ρ − S| ≤ 1` holds a zero of depth
`≥ d₀` have measure `≤ εT`. -/
theorem eventually_volume_deepWindow_le {d₀ ε : ℝ} (hd₀ : 0 < d₀) (hε : 0 < ε) :
    ∀ᶠ T in atTop, MeasureTheory.volume {S ∈ Icc (T - 1) (2 * T + 1) | ∃ ρ : ℂ, xi ρ = 0 ∧
        d₀ ≤ |ρ.re - 1 / 2| ∧ |ρ.im - S| ≤ 1} ≤ ENNReal.ofReal (ε * T) := by
  have hlin : Tendsto (fun T : ℝ => 2 * T + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 (tendsto_id.const_mul_atTop (by norm_num))
  have h := hlin.eventually ((tendsto_offLineCountBeyond_div hd₀).eventually
    (gt_mem_nhds (show (0 : ℝ) < ε / 8 by positivity)))
  filter_upwards [h, eventually_ge_atTop (3 : ℝ)] with T hT hT3
  refine (volume_deepWindow_le hd₀ hT3).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [div_lt_iff₀ (by linarith)] at hT
  nlinarith

end

end RHTower
