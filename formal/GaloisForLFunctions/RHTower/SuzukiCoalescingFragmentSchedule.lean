import GaloisForLFunctions.RHTower.SuzukiCoalescingFragmentPole
import GaloisForLFunctions.HTGeometry.CoalescingLimitObstruction

/-!
# The coalescence schedule

Both Clark levels of the fragmented carrier occur in an arbitrarily small window about the physical
point.  Only the depth of the section has to be tuned: three repeated turns are already more gain
than a full turn plus the deficit, and the deficit is proportional to the depth, which vanishes as
the section deepens.

Fixing the number of turns at three and letting the radius rise to one, the foot of the pole
descends to the physical point and its depth vanishes, so for every window there is a radius whose
level points lie inside it.  Assembling over a shrinking sequence of windows produces the two
sequences that rule out a continuous limit.
-/

noncomputable section

namespace RHTower

open Complex Filter Topology GaloisForLFunctions.HTGeometry

/-- The foot of the pole, as a function of the radius. -/
theorem tendsto_suzukiFragmentPole_re {c : ℝ} (hc : 0 < c) (x₀ : ℝ) :
    Tendsto (fun r : ℝ => (suzukiFragmentPole c r (suzukiCoalescingCayley c (x₀ : ℂ))).re)
      (nhds 1) (nhds x₀) := by
  have h := tendsto_suzukiFragmentPole_of_cayley hc x₀
  have := (Complex.continuous_re.tendsto ((x₀ : ℝ) : ℂ)).comp h
  simpa [Function.comp_def] using this

/-- The depth of the pole vanishes as the section deepens. -/
theorem tendsto_suzukiFragmentPole_im {c : ℝ} (hc : 0 < c) (x₀ : ℝ) :
    Tendsto (fun r : ℝ => (suzukiFragmentPole c r (suzukiCoalescingCayley c (x₀ : ℂ))).im)
      (nhds 1) (nhds 0) := by
  have h := tendsto_suzukiFragmentPole_of_cayley hc x₀
  have := (Complex.continuous_im.tendsto ((x₀ : ℝ) : ℂ)).comp h
  simpa [Function.comp_def] using this

/-- **Both Clark levels occur in every window.**  Three repeated turns and a radius close enough to
one put a `+1` point and a `-1` point of the carrier inside any interval about the physical
point. -/
theorem exists_radius_clark_levels_close {c : ℝ} (hc : 0 < c) (x₀ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∃ p q : ℝ,
      |p - x₀| < δ ∧ |q - x₀| < δ ∧
      suzukiFragmentedDiskCarrier (suzukiCoalescingCayley c (x₀ : ℂ)) r 3
          (suzukiCoalescingCayley c ((p : ℝ) : ℂ)) = 1 ∧
      suzukiFragmentedDiskCarrier (suzukiCoalescingCayley c (x₀ : ℂ)) r 3
          (suzukiCoalescingCayley c ((q : ℝ) : ℂ)) = -1 := by
  classical
  set ζ := suzukiCoalescingCayley c (x₀ : ℂ) with hζdef
  have hζ : ‖ζ‖ = 1 := by
    have hB := real_add_c_I_ne_zero hc x₀
    have hconjnorm : ‖(x₀ : ℂ) - (c : ℂ) * I‖ = ‖(x₀ : ℂ) + (c : ℂ) * I‖ := by
      rw [show ((x₀ : ℂ) - (c : ℂ) * I) = (starRingEnd ℂ) ((x₀ : ℂ) + (c : ℂ) * I) by
        simp [Complex.ext_iff]]
      exact Complex.norm_conj _
    rw [hζdef, suzukiCoalescingCayley, norm_div, hconjnorm,
      div_self (norm_ne_zero_iff.mpr hB)]
  -- the eventual conditions on the radius
  have hre := tendsto_suzukiFragmentPole_re hc x₀
  have him := tendsto_suzukiFragmentPole_im hc x₀
  have hev1 : ∀ᶠ r : ℝ in nhds 1,
      |(suzukiFragmentPole c r ζ).re - x₀| < δ / 4 :=
    Metric.tendsto_nhds.mp hre (δ / 4) (by linarith)
  have hev2 : ∀ᶠ r : ℝ in nhds 1,
      |(suzukiFragmentPole c r ζ).im - 0| < Real.pi * δ / 24 :=
    Metric.tendsto_nhds.mp him (Real.pi * δ / 24) (by positivity)
  have hev3 : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio 1), (0 : ℝ) ≤ r ∧ r < 1 := by
    have hlt : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio 1), r < 1 := by
      filter_upwards [self_mem_nhdsWithin] with r hr using hr
    have hpos : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio 1), (0 : ℝ) ≤ r := by
      have : ∀ᶠ r : ℝ in nhds (1 : ℝ), (0 : ℝ) < r :=
        eventually_gt_nhds (by norm_num)
      filter_upwards [this.filter_mono nhdsWithin_le_nhds] with r hr using hr.le
    filter_upwards [hlt, hpos] with r h1 h2 using ⟨h2, h1⟩
  have hcombined : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio 1),
      ((0 : ℝ) ≤ r ∧ r < 1) ∧
        (|(suzukiFragmentPole c r ζ).re - x₀| < δ / 4 ∧
          |(suzukiFragmentPole c r ζ).im - 0| < Real.pi * δ / 24) :=
    hev3.and ((hev1.and hev2).filter_mono nhdsWithin_le_nhds)
  obtain ⟨r, ⟨hr0, hr1⟩, hrre, hrim⟩ := hcombined.exists
  -- the geometry of the window
  set u := (suzukiFragmentPole c r ζ).re with hu
  set v := (suzukiFragmentPole c r ζ).im with hv
  have hvpos : 0 < v := suzukiFragmentPole_im_pos hζ hc hr0 hr1
  have hure : |u - x₀| < δ / 4 := hrre
  have hvim : v < Real.pi * δ / 24 := by
    have := hrim
    rwa [sub_zero, abs_of_pos hvpos] at this
  have hαu : x₀ - δ / 2 < u := by
    have := abs_lt.mp hure
    linarith [this.1]
  have huβ : u < x₀ + δ / 2 := by
    have := abs_lt.mp hure
    linarith [this.2]
  have hβu : δ / 4 < (x₀ + δ / 2) - u := by
    have := abs_lt.mp hure
    linarith [this.2]
  have huα : δ / 4 < u - (x₀ - δ / 2) := by
    have := abs_lt.mp hure
    linarith [this.1]
  -- the gain pays for one full turn beyond the level count
  have hsum : 1 / ((x₀ + δ / 2) - u) + 1 / (u - (x₀ - δ / 2)) < 8 / δ := by
    have h1 : 1 / ((x₀ + δ / 2) - u) < 4 / δ := by
      rw [div_lt_div_iff₀ (by linarith) (by linarith)]
      linarith
    have h2 : 1 / (u - (x₀ - δ / 2)) < 4 / δ := by
      rw [div_lt_div_iff₀ (by linarith) (by linarith)]
      linarith
    have hsplit : (8 : ℝ) / δ = 4 / δ + 4 / δ := by ring
    rw [hsplit]
    linarith
  have hM : 2 * Real.pi * ((1 : ℕ) + 1 : ℝ)
      ≤ 2 * Real.pi * (3 : ℕ) - 2 * ((3 : ℕ) : ℝ) * v
        * (1 / ((x₀ + δ / 2) - u) + 1 / (u - (x₀ - δ / 2))) := by
    have hbound : 6 * v * (1 / ((x₀ + δ / 2) - u) + 1 / (u - (x₀ - δ / 2)))
        < 6 * v * (8 / δ) := mul_lt_mul_of_pos_left hsum (by positivity)
    have hfinal : 6 * v * (8 / δ) < 2 * Real.pi := by
      rw [show 6 * v * (8 / δ) = 48 * v / δ by ring, div_lt_iff₀ hδ]
      nlinarith [Real.pi_pos]
    push_cast
    nlinarith
  obtain ⟨x, x', hx, hx', _⟩ :=
    exists_interlacing_suzukiFragmentedDiskCarrier_clark (ζ := ζ) hζ hc hr0 hr1
      (by rw [← hu]; exact hαu) (by rw [← hu]; exact huβ) 3 (M := 1)
      (by rw [← hu, ← hv]; exact hM)
  obtain ⟨hx0mem, hx0val⟩ := hx 0 (by norm_num)
  obtain ⟨hx0'mem, hx0'val⟩ := hx' 0 (by norm_num)
  refine ⟨r, hr0, hr1, x 0, x' 0, ?_, ?_, hx0val, hx0'val⟩
  · rw [abs_lt]
    constructor
    · linarith [hx0mem.1]
    · linarith [hx0mem.2]
  · rw [abs_lt]
    constructor
    · linarith [hx0'mem.1]
    · linarith [hx0'mem.2]

/-- **The coalescence schedule.**  There is a sequence of radii whose carriers put a `+1` point and
a `-1` point within `1/(n+1)` of the physical point. -/
theorem exists_schedule_clark_levels {c : ℝ} (hc : 0 < c) (x₀ : ℝ) :
    ∃ r : ℕ → ℝ, (∀ n, 0 ≤ r n ∧ r n < 1) ∧
      (∀ n : ℕ, ∃ p : ℝ, |p - x₀| < 1 / ((n : ℝ) + 1) ∧ p ∈ Set.univ ∧
        suzukiFragmentedDiskCarrier (suzukiCoalescingCayley c (x₀ : ℂ)) (r n) 3
          (suzukiCoalescingCayley c ((p : ℝ) : ℂ)) = 1) ∧
      (∀ n : ℕ, ∃ q : ℝ, |q - x₀| < 1 / ((n : ℝ) + 1) ∧ q ∈ Set.univ ∧
        suzukiFragmentedDiskCarrier (suzukiCoalescingCayley c (x₀ : ℂ)) (r n) 3
          (suzukiCoalescingCayley c ((q : ℝ) : ℂ)) = -1) := by
  have hδ : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  choose r hr0 hr1 p q hp hq hpval hqval using
    fun n : ℕ => exists_radius_clark_levels_close hc x₀ (hδ n)
  exact ⟨r, fun n => ⟨hr0 n, hr1 n⟩,
    fun n => ⟨p n, hp n, Set.mem_univ _, hpval n⟩,
    fun n => ⟨q n, hq n, Set.mem_univ _, hqval n⟩⟩

/-- **Theorem D's non-normality conclusion.**  Along the coalescence schedule no uniform limit of
the fragmented carriers is continuous at the physical point: both Clark levels accumulate there, and
a continuous limit would have to take both values. -/
theorem not_continuousAt_of_schedule {c : ℝ} (hc : 0 < c) (x₀ : ℝ) :
    ∃ r : ℕ → ℝ, (∀ n, 0 ≤ r n ∧ r n < 1) ∧
      ∀ G : ℝ → ℂ,
        TendstoUniformlyOn
          (fun (n : ℕ) (x : ℝ) =>
            suzukiFragmentedDiskCarrier (suzukiCoalescingCayley c (x₀ : ℂ)) (r n) 3
              (suzukiCoalescingCayley c ((x : ℝ) : ℂ))) G atTop Set.univ →
        ¬ ContinuousAt G x₀ := by
  obtain ⟨r, hr, hp, hq⟩ := exists_schedule_clark_levels hc x₀
  refine ⟨r, hr, fun G huc hcont => ?_⟩
  have hab : (1 : ℂ) ≠ -1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  exact not_continuousWithinAt_of_shrinking_levels huc hab hp hq
    (continuousWithinAt_univ G x₀ |>.mpr hcont)

end RHTower
