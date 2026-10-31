import GaloisForLFunctions.RHTower.XiCosineShiftCriticalScaleProducer
import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergUpper

/-!
# The off-line second moment is `o(V)`

**Theorem** (`tendsto_offLineSecondMoment_div`).  The squared-depth moment of the zeros,
`Σ_{0 < Im ρ ≤ V} m(ρ) (Re ρ − ½)₊²` (`offLineSecondMoment`), is `o(V)`.

So the off-line first moment `Σ m (Re ρ − ½)₊ ≤ (67/1000) V` sits at depths `o(1)`: the depth mass
`Σ m (Re ρ − ½)²` of a unit window is `o(1)` on average over the heights.

**Proof.**  For `x ≤ ½`, `x₊² ≤ ½ (x − d)₊ + d x₊` (`sq_max_le`): below `d` use `x ≤ d`,
above it `x(x − d) ≤ ½(x − d)`.  With `d = R/log V`, the tail law with Selberg's mollifier
(`eventually_offLineTail_le_selberg`) gives `4π Σ m (x − d)₊ ≤ (g(R) + η) V` with `g(R) → 0`
(`tendsto_selbergTailRate`), and the first moment (`eventually_offLineMoment_le_selberg_upper`)
makes `d Σ m x₊ ≤ (67/1000) R V/log V = o(V)`.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The squared-depth moment `Σ_{0 < Im ρ ≤ V} m(ρ) (Re ρ − ½)₊²`. -/
def offLineSecondMoment (V : ℝ) : ℝ :=
  ∑ z ∈ stripFinsetPos V, ((analyticOrderAt xi z).toNat : ℝ) * max (z.re - 1 / 2) 0 ^ 2

theorem offLineSecondMoment_nonneg (V : ℝ) : 0 ≤ offLineSecondMoment V :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- `x₊² ≤ ½ (x − d)₊ + d x₊` for `x ≤ ½`. -/
theorem sq_max_le {x d : ℝ} (hx : x ≤ 1 / 2) :
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
      have h := sq_max_le (d := d) (show z.re - 1 / 2 ≤ 1 / 2 by linarith)
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

end

end RHTower

#print axioms RHTower.tendsto_offLineSecondMoment_div
