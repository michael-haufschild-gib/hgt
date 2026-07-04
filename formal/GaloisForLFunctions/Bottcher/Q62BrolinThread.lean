/-
# q62 — GAP-A end-to-end thread: `limitingBrolinMeasureAt c a = gapAMu c`

The target-`a` support machinery (`Q62WeylDischarge`, `Q62EquilibriumVanishing`,
`Q62FrostmanDomination`) is stated for `limitingBrolinMeasureAt c a`; the Half-A `f`-invariance
(`Q62BrolinFInvariance`) is proved for the zero-target `gapAMu c`.  This module welds them.

**Uniqueness of the Brolin limit across all targets.**  Under `volume(K_c)=0`, every target-`a`
limiting Brolin measure equals the zero-target `gapAMu c`: both are probability measures carried by
`K_c` with exterior potential `−G_c` off `K_c` (`green_eq_neg_logPotential_..._on_basin`), and
Lebesgue-nullity of `K_c` makes those potentials agree a.e., so the uniqueness engine
(`measure_eq_of_neg_logPotential_ae_eq`) forces measure equality.  From the identification:

* `f`-invariance transports from `gapAMu` to `limitingBrolinMeasureAt c a`;
* empty interior (a corollary of `volume(K_c)=0`) collapses `K_c` into its frontier, discharging the
  atomlessness hypothesis and Half B (Frostman domination) unconditionally there;
* the two sharp halves feed `equilibriumPotentialVanishesAe_of_scaling_of_dominated`, giving the
  support datum `LimitingBrolinMeasureAtSupportsJulia c a` through the two-halves route — independent
  of the direct Julia-null Riesz route in `Q62WeylDischarge`, and isolating the volume-nullity
  dependence into Half A alone (Half B stands unconditionally).
-/
import GaloisForLFunctions.Bottcher.Q62BrolinFInvariance
import GaloisForLFunctions.Bottcher.Q62FrostmanDomination
import GaloisForLFunctions.Bottcher.JuliaMeasureZero

open MeasureTheory Complex Filter Metric Set Topology

namespace Bottcher

noncomputable section

/-- `volume(K_c) = 0 ⟹ K_c has empty interior`: a nonempty interior is open with positive area. -/
theorem interior_filledJulia_eq_empty_of_volume_zero {c : ℂ}
    (hvol : volume (filledJulia c) = 0) : interior (filledJulia c) = ∅ := by
  by_contra h
  have hne : (interior (filledJulia c)).Nonempty := Set.nonempty_iff_ne_empty.mpr h
  have hpos : 0 < volume (interior (filledJulia c)) := isOpen_interior.measure_pos volume hne
  have hle : volume (interior (filledJulia c)) ≤ volume (filledJulia c) :=
    measure_mono interior_subset
  rw [hvol] at hle
  exact absurd hle (not_le.mpr hpos)

/-- **Uniqueness of the Brolin limit across all targets.**  Under `volume(K_c)=0`, the target-`a`
limiting Brolin measure coincides with the zero-target `gapAMu c`.  This is the weld that threads the
target-`a` support machinery onto the `gapAMu` `f`-invariance. -/
theorem limitingBrolinMeasureAt_eq_gapAMu_of_volume_zero {c a : ℂ}
    (hvol : volume (filledJulia c) = 0) :
    limitingBrolinMeasureAt c a = gapAMu c := by
  haveI : IsProbabilityMeasure (gapAMu c) := (gapAMu_isProbOn_filledJulia c).1
  refine measure_eq_of_neg_logPotential_ae_eq (A := max 2 ‖c‖) (B := max 2 ‖c‖) ?_ ?_ ?_
  · exact measure_mono_null (compl_subset_compl.mpr (filledJulia_subset_closedBall c))
      (limitingBrolinMeasureAt_filledJulia_compl c a)
  · exact measure_mono_null (compl_subset_compl.mpr (filledJulia_subset_closedBall c))
      (gapAMu_isProbOn_filledJulia c).2
  · have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ filledJulia c := by
      rw [ae_iff]; simpa using hvol
    filter_upwards [hae] with z hz
    show - logPotential (limitingBrolinMeasureAt c a) z = - logPotential (gapAMu c) z
    rw [← green_eq_neg_logPotential_limitingBrolinMeasureAt_on_basin hz,
        ← green_eq_neg_logPotential_gapAMu_on_basin hz]

/-- **`f`-invariance of the target-`a` Brolin measure** under `volume(K_c)=0`, transported from
`gapAMu` via the identification. -/
theorem map_quadratic_limitingBrolinMeasureAt_eq_of_volume_zero {c a : ℂ}
    (hvol : volume (filledJulia c) = 0) :
    Measure.map (quadratic c) (limitingBrolinMeasureAt c a) = limitingBrolinMeasureAt c a := by
  rw [limitingBrolinMeasureAt_eq_gapAMu_of_volume_zero hvol]
  exact map_quadratic_gapAMu_eq_of_volume_filledJulia_zero hvol

/-- Atomlessness on all of `K_c` under `volume(K_c)=0`: empty interior collapses `K_c` into its
frontier, where the Brolin measure is atomless unconditionally. -/
theorem limitingBrolinMeasureAt_singleton_eq_zero_on_filledJulia_of_volume_zero {c a : ℂ}
    (hvol : volume (filledJulia c) = 0) :
    ∀ z : ℂ, z ∈ filledJulia c → limitingBrolinMeasureAt c a {z} = 0 := by
  have hsub : filledJulia c ⊆ frontier (filledJulia c) :=
    filledJulia_subset_frontier_of_interior_empty
      (interior_filledJulia_eq_empty_of_volume_zero hvol)
  exact fun z hz => limitingBrolinMeasureAt_singleton_eq_zero_of_mem_frontier (hsub hz)

/-- **Half A (the Brolin doubling law) from `volume(K_c)=0`.**  The `f`-invariance and the
unconditional frontier atomlessness feed the scaling gate. -/
theorem brolinScalingAt_of_volume_zero {c a : ℂ}
    (hvol : volume (filledJulia c) = 0) : BrolinScalingAt c a :=
  BrolinScalingAt_of_map_quadratic_unconditional
    (map_quadratic_limitingBrolinMeasureAt_eq_of_volume_zero hvol)
    (limitingBrolinMeasureAt_singleton_eq_zero_on_filledJulia_of_volume_zero hvol)

/-- **Half B (Frostman domination) from `volume(K_c)=0`.**  Empty interior places `K_c` in its
frontier, where domination is unconditional. -/
theorem potentialDominatedOnFilledJulia_of_volume_zero {c a : ℂ}
    (hvol : volume (filledJulia c) = 0) : PotentialDominatedOnFilledJulia c a :=
  potentialDominatedOnFilledJulia_of_subset_frontier
    (filledJulia_subset_frontier_of_interior_empty
      (interior_filledJulia_eq_empty_of_volume_zero hvol))

/-- **The two-halves GAP-A support datum from `volume(K_c)=0`.**  End-to-end thread: identification
→ `f`-invariance → Half-A doubling; empty interior → Half-B domination; the two sharp halves →
`EquilibriumPotentialVanishesAe` → the support theorem.  Independent of the direct Julia-null Riesz
route (`Q62WeylDischarge`); this route isolates the volume-nullity dependence into Half A alone. -/
theorem limitingBrolinMeasureAtSupportsJulia_of_volume_zero_via_halves {c a : ℂ}
    (hvol : volume (filledJulia c) = 0) :
    LimitingBrolinMeasureAtSupportsJulia c a :=
  limitingBrolinMeasureAtSupportsJulia_of_scaling_of_dominated c a
    (brolinScalingAt_of_volume_zero hvol)
    (potentialDominatedOnFilledJulia_of_volume_zero hvol)

/-! ### Fully unconditional GAP-A support datum on the separated locus

`JuliaMeasureZero` discharges `volume(K_c)=0` unconditionally whenever the critical value `c` is
separated from `K_c` by more than `1/2` — in particular for `‖c‖ ≥ 73/25`.  Composed with the
two-halves thread above, this makes `LimitingBrolinMeasureAtSupportsJulia c a` unconditional there,
covering the whole norm-separated `q62` disconnected/mixed lane (which runs at `‖c‖ ≥ 1000`). -/

/-- **GAP-A support datum, unconditional under critical-value separation `> 1/2`.**  The sharp form:
every point of `K_c` at distance `> 1/2` from the critical value `c` gives `volume(K_c)=0`, hence the
Brolin measure charges the whole Julia frontier. -/
theorem limitingBrolinMeasureAtSupportsJulia_of_filledJulia_dist_gt_half {c a : ℂ}
    (hdist : ∀ w ∈ filledJulia c, ((1 : ℝ) / 2) < ‖w - c‖) :
    LimitingBrolinMeasureAtSupportsJulia c a :=
  limitingBrolinMeasureAtSupportsJulia_of_volume_zero_via_halves
    (volume_filledJulia_eq_zero_of_filledJulia_dist_gt_half hdist)

/-- **GAP-A support datum, unconditional for `‖c‖ ≥ 4`.** -/
theorem limitingBrolinMeasureAtSupportsJulia_of_four_le_norm {c a : ℂ} (hc : (4 : ℝ) ≤ ‖c‖) :
    LimitingBrolinMeasureAtSupportsJulia c a :=
  limitingBrolinMeasureAtSupportsJulia_of_volume_zero_via_halves
    (volume_filledJulia_eq_zero_of_four_le_norm hc)

/-- **GAP-A support datum, unconditional for `‖c‖ ≥ 3`.** -/
theorem limitingBrolinMeasureAtSupportsJulia_of_three_le_norm {c a : ℂ} (hc : (3 : ℝ) ≤ ‖c‖) :
    LimitingBrolinMeasureAtSupportsJulia c a :=
  limitingBrolinMeasureAtSupportsJulia_of_volume_zero_via_halves
    (volume_filledJulia_eq_zero_of_three_le_norm hc)

/-- **GAP-A support datum, unconditional for `‖c‖ ≥ 73/25 = 2.92`** — the current reach of the
one-step critical-value separation route. -/
theorem limitingBrolinMeasureAtSupportsJulia_of_seventy_three_div_twenty_five_le_norm {c a : ℂ}
    (hc : ((73 : ℝ) / 25) ≤ ‖c‖) :
    LimitingBrolinMeasureAtSupportsJulia c a :=
  limitingBrolinMeasureAtSupportsJulia_of_volume_zero_via_halves
    (volume_filledJulia_eq_zero_of_seventy_three_div_twenty_five_le_norm hc)

/-- `∀`-fixed-point form of the unconditional `‖c‖ ≥ 4` support datum, consumed by the q62
disconnected/mixed capstones. -/
theorem forall_fixedPoint_limitingBrolinMeasureAtSupportsJulia_of_four_le_norm {c : ℂ}
    (hc : (4 : ℝ) ≤ ‖c‖) :
    ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a :=
  fun _ _ => limitingBrolinMeasureAtSupportsJulia_of_four_le_norm hc

end

end Bottcher
