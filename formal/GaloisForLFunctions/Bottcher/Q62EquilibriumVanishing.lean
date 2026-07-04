/-
# q62 — GAP-A final input reduced to two sharp potential-theory halves

`Q62WeylDischarge` reduced the entire q62 Brolin support route (`LimitingBrolinMeasureAtSupportsJulia`,
valid across all three regimes) to the single input `EquilibriumPotentialVanishesAe c a`:
the equilibrium potential `Uᵘ = logPotential (limitingBrolinMeasureAt c a)` vanishes a.e. on
`filledJulia c` (Frostman's equilibrium identity, `Robin = -log cap K_c = 0`).

This module cuts that input into two named, standard halves and proves the assembly:

* **Half A — the doubling law** `BrolinScalingAt c a`: `−Uᵘ(f_c z) = 2·(−Uᵘ z)` on `K_c`.
  Given it, the bounded forward orbit forces `−Uᵘ ≤ 0` on `K_c` (a positive value doubles
  past the uniform upper bound `log(2·max 2 ‖c‖)`).  So `Uᵘ ≥ 0` on `K_c`.  This half is
  the standard consequence of Brolin `f`-invariance `f_*μ = μ` and the antipodal symmetry
  `(−1)_*μ = μ` (via `f(z)−f(y) = (z−y)(z+y)`), both properties of the equilibrium measure.
* **Half B — Frostman domination** `PotentialDominatedOnFilledJulia c a`: `Uᵘ ≤ 0` on `K_c`
  (the equilibrium-potential maximum principle).

`Uᵘ ≥ 0` and `Uᵘ ≤ 0` give `Uᵘ = 0` on all of `K_c`, hence `EquilibriumPotentialVanishesAe`.
Half A is proved here modulo `BrolinScalingAt`; the two remaining inputs — the doubling law
(from invariance+symmetry) and the domination bound — are the sharp GAP-A frontier.
-/
import GaloisForLFunctions.Bottcher.Brolin.TargetShifted
import GaloisForLFunctions.Bottcher.Q62WeylDischarge

open MeasureTheory Complex Filter Metric Set Topology CompactlySupported
open scoped Laplacian

namespace Bottcher

noncomputable section

/-- Uniform upper bound on `−Uᵘ` over the filled Julia set for the target-`a` Brolin
measure: `−logPotential μ ≤ log(2·max 2 ‖c‖)` on `K_c` (from the general lower bound on
`logPotential` for any probability measure carried by `K_c`). -/
theorem neg_logPotential_limitingBrolinMeasureAt_upper_bound_of_mem_filledJulia
    {c a z : ℂ} (hz : z ∈ filledJulia c) :
    - logPotential (limitingBrolinMeasureAt c a) z ≤ Real.log (2 * max 2 ‖c‖) := by
  have h := logPotential_lower_bound_of_isProbOn_filledJulia_of_mem_escapeDisk
    (limitingBrolinMeasureAt_isProbOn_filledJulia c a) (mem_escapeDisk_of_mem_filledJulia hz)
  linarith

/-- **The potential doubling law** for the target-`a` limiting Brolin measure on `K_c`:
`−Uᵘ(f_c z) = 2·(−Uᵘ z)`.  The standard consequence of Brolin `f`-invariance and the
antipodal symmetry of the measure (`f(z)−f(y) = (z−y)(z+y)`). -/
def BrolinScalingAt (c a : ℂ) : Prop :=
  ∀ w : ℂ, w ∈ filledJulia c →
    - logPotential (limitingBrolinMeasureAt c a) (quadratic c w) =
      2 * (- logPotential (limitingBrolinMeasureAt c a) w)

/-- **Frostman domination** for the target-`a` limiting Brolin measure: `Uᵘ ≤ 0` on
`K_c` (the equilibrium-potential maximum principle, Robin constant `= 0`). -/
def PotentialDominatedOnFilledJulia (c a : ℂ) : Prop :=
  ∀ z : ℂ, z ∈ filledJulia c → logPotential (limitingBrolinMeasureAt c a) z ≤ 0

/-- Antipodal measure invariance gives antipodal potential symmetry. -/
theorem logPotential_neg_eq_of_map_neg
    (μ : Measure ℂ) {z : ℂ}
    (hneg : Measure.map Neg.neg μ = μ) :
    logPotential μ (-z) = logPotential μ z := by
  unfold logPotential
  calc
    ∫ w, logKernel (-z) w ∂μ
        = ∫ w, logKernel (-z) w ∂Measure.map Neg.neg μ := by rw [hneg]
    _ = ∫ w, logKernel (-z) (-w) ∂μ := by
        rw [integral_map]
        · exact continuous_neg.aemeasurable
        · exact (logKernel_aestronglyMeasurable (-z) (Measure.map Neg.neg μ))
    _ = ∫ w, logKernel z w ∂μ := by
        apply integral_congr_ae
        filter_upwards with w
        simpa using logKernel_neg_right (-z) w

/-- Measure-level Half A kernel split.  If `μ` is invariant under `f_c`, invariant
under `z ↦ -z`, and has no atoms at the two singular preimages `z, -z`, then the
quadratic factorization `f(z)-f(w)=(z-w)(z+w)` gives `U(fz)=2U(z)`. -/
theorem logPotential_quadratic_eq_two_of_map_quadratic_of_map_neg
    (μ : Measure ℂ) {c z : ℂ}
    (hquad : Measure.map (quadratic c) μ = μ)
    (hneg : Measure.map Neg.neg μ = μ)
    (hatomZ : μ ({z} : Set ℂ) = 0)
    (hatomNegZ : μ ({-z} : Set ℂ) = 0)
    (hintZ : Integrable (fun w => logKernel z w) μ)
    (hintNegZ : Integrable (fun w => logKernel z (-w)) μ) :
    logPotential μ (quadratic c z) = 2 * logPotential μ z := by
  have hne_z : ∀ᵐ w ∂μ, w ∈ ({z} : Set ℂ)ᶜ := by
    have hzero : μ (({z} : Set ℂ)ᶜ)ᶜ = 0 := by simpa using hatomZ
    exact (mem_ae_iff).2 hzero
  have hne_negz : ∀ᵐ w ∂μ, w ∈ ({-z} : Set ℂ)ᶜ := by
    have hzero : μ (({-z} : Set ℂ)ᶜ)ᶜ = 0 := by simpa using hatomNegZ
    exact (mem_ae_iff).2 hzero
  have hsplit :
      ∀ᵐ w ∂μ,
        logKernel (quadratic c z) (quadratic c w) =
          logKernel z w + logKernel z (-w) := by
    filter_upwards [hne_z, hne_negz] with w hwz hwnegz
    exact logKernel_quadratic_eq_add
      (c := c) (z := z) (w := w)
      (fun h => hwz h.symm)
      (fun h => hwnegz (by rw [h]; simp))
  have hquadIntegral :
      logPotential μ (quadratic c z) =
        ∫ w, logKernel (quadratic c z) (quadratic c w) ∂μ := by
    unfold logPotential
    calc
      ∫ w, logKernel (quadratic c z) w ∂μ
          = ∫ w, logKernel (quadratic c z) w ∂Measure.map (quadratic c) μ := by
              rw [hquad]
      _ = ∫ w, logKernel (quadratic c z) (quadratic c w) ∂μ := by
              rw [integral_map]
              · exact (continuous_quadratic c).aemeasurable
              · exact (logKernel_aestronglyMeasurable (quadratic c z)
                  (Measure.map (quadratic c) μ))
  calc
    logPotential μ (quadratic c z)
        = ∫ w, logKernel (quadratic c z) (quadratic c w) ∂μ := hquadIntegral
    _ = ∫ w, (logKernel z w + logKernel z (-w)) ∂μ := by
        apply integral_congr_ae hsplit
    _ = ∫ w, logKernel z w ∂μ + ∫ w, logKernel z (-w) ∂μ := by
        rw [integral_add hintZ hintNegZ]
    _ = logPotential μ z + logPotential μ (-z) := by
        unfold logPotential
        congr 1
        apply integral_congr_ae
        filter_upwards with w
        exact logKernel_neg_right z w
    _ = logPotential μ z + logPotential μ z := by
        rw [logPotential_neg_eq_of_map_neg μ hneg]
    _ = 2 * logPotential μ z := by ring

/-- Half A from the standard Brolin invariances plus boundary-kernel finiteness.
The remaining nontrivial GAP-A task is to prove the two measure invariances for
the target limiting cluster; the antipodal finite symmetry is free, while
`f_*μ=μ` is exactly the shifted/full-limit identification gap. -/
theorem BrolinScalingAt_of_map_quadratic_and_map_neg
    {c a : ℂ}
    (hquad :
      Measure.map (quadratic c) (limitingBrolinMeasureAt c a) =
        limitingBrolinMeasureAt c a)
    (hneg :
      Measure.map Neg.neg (limitingBrolinMeasureAt c a) =
        limitingBrolinMeasureAt c a)
    (hatom :
      ∀ z : ℂ, z ∈ filledJulia c → limitingBrolinMeasureAt c a {z} = 0)
    (hint :
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (limitingBrolinMeasureAt c a)) :
    BrolinScalingAt c a := by
  intro z hzK
  have hnegK : -z ∈ filledJulia c := (mem_filledJulia_neg_iff c z).2 hzK
  have hintNeg :
      Integrable (fun w => logKernel z (-w)) (limitingBrolinMeasureAt c a) := by
    simpa [logKernel_neg_right] using hint (-z) hnegK
  have hpot :=
    logPotential_quadratic_eq_two_of_map_quadratic_of_map_neg
      (μ := limitingBrolinMeasureAt c a) (c := c) (z := z)
      hquad hneg (hatom z hzK) (hatom (-z) hnegK)
      (hint z hzK) hintNeg
  linarith

/-- Finite positive-level arbitrary-target pullback symmetry transported to the
compact target carrier. -/
theorem integral_preBrolinMeasureAtOnTargetEscapeDisk_neg_eq
    (c a : ℂ) (n : ℕ) (φ : C_c(ℂ, ℝ)) :
    ∫ z : targetEscapeDisk c a, φ (-(z : ℂ))
        ∂(preBrolinProbabilityAtOnTargetEscapeDisk c a (n + 1) :
          Measure (targetEscapeDisk c a)) =
      ∫ z : targetEscapeDisk c a, φ (z : ℂ)
        ∂(preBrolinProbabilityAtOnTargetEscapeDisk c a (n + 1) :
          Measure (targetEscapeDisk c a)) := by
  have hplane := integral_preBrolinMeasureAt_succ_neg_eq c a n (fun z : ℂ => φ z)
  have hleft :
      ∫ z, φ (-z) ∂preBrolinMeasureAt c a (n + 1) =
        ∫ z : targetEscapeDisk c a, φ (-(z : ℂ))
          ∂(preBrolinMeasureAtOnTargetEscapeDisk c a (n + 1)) := by
    rw [preBrolinMeasureAt_eq_map_preBrolinMeasureAtOnTargetEscapeDisk, integral_map]
    · exact measurable_subtype_coe.aemeasurable
    · exact (φ.continuous.comp continuous_neg).aestronglyMeasurable
  have hright :
      ∫ z, φ z ∂preBrolinMeasureAt c a (n + 1) =
        ∫ z : targetEscapeDisk c a, φ (z : ℂ)
          ∂(preBrolinMeasureAtOnTargetEscapeDisk c a (n + 1)) := by
    rw [preBrolinMeasureAt_eq_map_preBrolinMeasureAtOnTargetEscapeDisk, integral_map]
    · exact measurable_subtype_coe.aemeasurable
    · exact φ.continuous.aestronglyMeasurable
  rw [hleft, hright] at hplane
  simpa [preBrolinProbabilityAtOnTargetEscapeDisk] using hplane

/-- Antipodal invariance of the selected arbitrary-target limiting Brolin measure.
The finite symmetry is free for every positive level, and the selected subsequence
is eventually positive. -/
theorem integral_limitingBrolinMeasureAt_neg_eq (c a : ℂ) (φ : C_c(ℂ, ℝ)) :
    ∫ z, φ (-(z : ℂ)) ∂limitingBrolinMeasureAt c a =
      ∫ z, φ z ∂limitingBrolinMeasureAt c a := by
  let ψ : BoundedContinuousFunction (targetEscapeDisk c a) ℝ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨fun z : targetEscapeDisk c a => φ (-(z : ℂ)),
        φ.continuous.comp (continuous_neg.comp continuous_subtype_val)⟩
  have hneg :
      Tendsto
        (fun k =>
          ∫ z : targetEscapeDisk c a, φ (-(z : ℂ))
            ∂(preBrolinProbabilityAtOnTargetEscapeDisk c a
                (brolinLimitAtSubsequence c a k) :
              Measure (targetEscapeDisk c a)))
        atTop
        (𝓝 (∫ z : targetEscapeDisk c a, φ (-(z : ℂ))
          ∂(brolinLimitAtOnTargetEscapeDisk c a : Measure (targetEscapeDisk c a)))) := by
    have h :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
        (preBrolinProbabilityAtOnTargetEscapeDisk_subseq_tendsto c a)) ψ
    simpa [ψ] using h
  have hpos : ∀ᶠ k in atTop, 0 < brolinLimitAtSubsequence c a k := by
    exact (brolinLimitAtSubsequence_tendsto_atTop c a).eventually (eventually_gt_atTop 0)
  have hsame :
      Tendsto
        (fun k =>
          ∫ z : targetEscapeDisk c a, φ (-(z : ℂ))
            ∂(preBrolinProbabilityAtOnTargetEscapeDisk c a
                (brolinLimitAtSubsequence c a k) :
              Measure (targetEscapeDisk c a)))
        atTop
        (𝓝 (∫ z : targetEscapeDisk c a, φ (z : ℂ)
          ∂(brolinLimitAtOnTargetEscapeDisk c a : Measure (targetEscapeDisk c a)))) := by
    have hbase := preBrolinProbabilityAtOnTargetEscapeDisk_subseq_integral_tendsto c a φ
    exact hbase.congr' (by
      filter_upwards [hpos] with k hkpos
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
      simpa [hm] using
        (integral_preBrolinMeasureAtOnTargetEscapeDisk_neg_eq c a m φ).symm)
  have hlim :
      (∫ z : targetEscapeDisk c a, φ (-(z : ℂ))
          ∂(brolinLimitAtOnTargetEscapeDisk c a : Measure (targetEscapeDisk c a))) =
        ∫ z : targetEscapeDisk c a, φ (z : ℂ)
          ∂(brolinLimitAtOnTargetEscapeDisk c a : Measure (targetEscapeDisk c a)) :=
    tendsto_nhds_unique hneg hsame
  have hleft :
      ∫ z, φ (-(z : ℂ)) ∂limitingBrolinMeasureAt c a =
        ∫ z : targetEscapeDisk c a, φ (-(z : ℂ))
          ∂(brolinLimitAtOnTargetEscapeDisk c a : Measure (targetEscapeDisk c a)) := by
    rw [limitingBrolinMeasureAt, integral_map]
    · exact measurable_subtype_coe.aemeasurable
    · exact (φ.continuous.comp continuous_neg).aestronglyMeasurable
  rw [hleft, integral_limitingBrolinMeasureAt_eq_integral_targetEscapeDisk]
  exact hlim

/-- Measure-level antipodal invariance of the selected arbitrary-target limiting
Brolin measure. -/
theorem map_limitingBrolinMeasureAt_neg (c a : ℂ) :
    Measure.map Neg.neg (limitingBrolinMeasureAt c a) =
      limitingBrolinMeasureAt c a := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  rw [integral_map]
  · exact integral_limitingBrolinMeasureAt_neg_eq c a φ
  · exact continuous_neg.measurable.aemeasurable
  · exact φ.continuous.aestronglyMeasurable

/-- The precise shifted/full-limit bridge for Half A.  If the adjacent selected
finite measures converge to the same limiting measure against quadratic test
functions, then the target limiting measure is `f_c`-invariant. -/
theorem map_limitingBrolinMeasureAt_quadratic_of_adjacent_subseq_comp_quadratic_tendsto
    {c a : ℂ}
    (hshift :
      ∀ φ : C_c(ℂ, ℝ),
        Tendsto
          (fun k =>
            ∫ z, φ (quadratic c z)
              ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k + 1))
          atTop
          (𝓝 (∫ z, φ (quadratic c z) ∂limitingBrolinMeasureAt c a))) :
    Measure.map (quadratic c) (limitingBrolinMeasureAt c a) =
      limitingBrolinMeasureAt c a := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  rw [integral_map]
  · have hleft := hshift φ
    have hbase := limitingBrolinMeasureAt_isWeakSubseqLimitOfPreBrolinAt c a φ
    have hsame :
        Tendsto
          (fun k =>
            ∫ z, φ (quadratic c z)
              ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k + 1))
          atTop (𝓝 (∫ z, φ z ∂limitingBrolinMeasureAt c a)) := by
      exact hbase.congr' (by
        filter_upwards with k
        exact (integral_preBrolinMeasureAt_succ_comp_quadratic
          c a (brolinLimitAtSubsequence c a k) (fun z : ℂ => φ z)).symm)
    exact tendsto_nhds_unique hleft hsame
  · exact (continuous_quadratic c).aemeasurable
  · exact φ.continuous.aestronglyMeasurable

/-- Half A with the free antipodal symmetry discharged.  The only remaining
measure-invariance input is the full limiting balancedness identity
`(f_c)_* μ = μ`, i.e. the shifted-measure/full-limit gap. -/
theorem BrolinScalingAt_of_map_quadratic
    {c a : ℂ}
    (hquad :
      Measure.map (quadratic c) (limitingBrolinMeasureAt c a) =
        limitingBrolinMeasureAt c a)
    (hatom :
      ∀ z : ℂ, z ∈ filledJulia c → limitingBrolinMeasureAt c a {z} = 0)
    (hint :
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (limitingBrolinMeasureAt c a)) :
    BrolinScalingAt c a :=
  BrolinScalingAt_of_map_quadratic_and_map_neg
    hquad (map_limitingBrolinMeasureAt_neg c a) hatom hint

/-- The selected arbitrary-target limiting measure is carried by `K_c`, in the
`∀ᵐ` form used by singular-kernel lower-bound arguments. -/
theorem ae_mem_filledJulia_limitingBrolinMeasureAt (c a : ℂ) :
    ∀ᵐ w ∂limitingBrolinMeasureAt c a, w ∈ filledJulia c :=
  (mem_ae_iff).2 (limitingBrolinMeasureAt_filledJulia_compl c a)

/-- If the split antipodal logarithmic kernel is integrable against the target
limit, then the original branch is integrable.  Both branches have the same
escape-disk lower bound on the carrier, so integrability of their sum separates. -/
theorem integrable_logKernel_limitingBrolinMeasureAt_of_integrable_add_neg_right
    {c a z : ℂ} (hzK : z ∈ filledJulia c)
    (hadd :
      Integrable
        (fun w => logKernel z w + logKernel z (-w))
        (limitingBrolinMeasureAt c a)) :
    Integrable (fun w => logKernel z w) (limitingBrolinMeasureAt c a) := by
  let μ : Measure ℂ := limitingBrolinMeasureAt c a
  let D : ℝ := Real.log (2 * max 2 ‖c‖)
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact instIsProbabilityMeasure_limitingBrolinMeasureAt c a
  have hzEsc : z ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hzK
  have hsupport : ∀ᵐ w ∂μ, w ∈ filledJulia c := by
    dsimp [μ]
    exact ae_mem_filledJulia_limitingBrolinMeasureAt c a
  have hf_nonneg :
      0 ≤ᵐ[μ] fun w => logKernel z w + D := by
    filter_upwards [hsupport] with w hwK
    have hwEsc : w ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hwK
    have hfloor : -D ≤ logKernel z w := by
      dsimp [D]
      exact logKernel_escapeDisk_lower_bound hzEsc hwEsc
    have hnonneg : (0 : ℝ) ≤ logKernel z w + D := by linarith
    simpa using hnonneg
  have hg_nonneg :
      0 ≤ᵐ[μ] fun w => logKernel z (-w) + D := by
    filter_upwards [hsupport] with w hwK
    have hnegK : -w ∈ filledJulia c := (mem_filledJulia_neg_iff c w).2 hwK
    have hnegEsc : -w ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hnegK
    have hfloor : -D ≤ logKernel z (-w) := by
      dsimp [D]
      exact logKernel_escapeDisk_lower_bound hzEsc hnegEsc
    have hnonneg : (0 : ℝ) ≤ logKernel z (-w) + D := by linarith
    simpa using hnonneg
  have hshifted_sum :
      Integrable
        (fun w => (logKernel z w + logKernel z (-w)) + 2 * D)
        μ := by
    have hconst : Integrable (fun _ : ℂ => 2 * D) μ := integrable_const _
    have haddμ :
        Integrable (fun w => logKernel z w + logKernel z (-w)) μ := by
      simpa [μ] using hadd
    simpa [Pi.add_apply] using haddμ.add hconst
  have hbranch_sum :
      Integrable
        ((fun w => logKernel z w + D) +
          (fun w => logKernel z (-w) + D))
        μ := by
    refine hshifted_sum.congr ?_
    filter_upwards with w
    simp only [Pi.add_apply]
    ring
  have hf_meas :
      AEStronglyMeasurable (fun w => logKernel z w + D) μ :=
    (logKernel_aestronglyMeasurable z μ).add aestronglyMeasurable_const
  have hf_shift :
      Integrable (fun w => logKernel z w + D) μ :=
    integrable_left_of_integrable_add_of_nonneg
      (μ := μ) hf_meas hf_nonneg hg_nonneg hbranch_sum
  have hplain : Integrable (fun w => logKernel z w) μ :=
    integrable_add_const_iff.mp hf_shift
  dsimp [μ] at hplain
  exact hplain

/-- Reverse integrability transfer for an invariant target limiting measure:
target-side integrability at `f_c z` forces integrability of the branch at `z`. -/
theorem integrable_logKernel_limitingBrolinMeasureAt_of_map_quadratic
    {c a z : ℂ}
    (hquad :
      Measure.map (quadratic c) (limitingBrolinMeasureAt c a) =
        limitingBrolinMeasureAt c a)
    (hzK : z ∈ filledJulia c)
    (hatomZ : limitingBrolinMeasureAt c a ({z} : Set ℂ) = 0)
    (hatomNegZ : limitingBrolinMeasureAt c a ({-z} : Set ℂ) = 0)
    (hμint :
      Integrable (fun y => logKernel (quadratic c z) y)
        (limitingBrolinMeasureAt c a)) :
    Integrable (fun w => logKernel z w) (limitingBrolinMeasureAt c a) := by
  let μ : Measure ℂ := limitingBrolinMeasureAt c a
  have hmapint :
      Integrable (fun y => logKernel (quadratic c z) y)
        (Measure.map (quadratic c) μ) := by
    dsimp [μ]
    rw [hquad]
    exact hμint
  have hcomp :
      Integrable (fun w => logKernel (quadratic c z) (quadratic c w)) μ := by
    exact
      (integrable_map_measure
        (logKernel_aestronglyMeasurable (quadratic c z)
          (Measure.map (quadratic c) μ))
        (continuous_quadratic c).measurable.aemeasurable).1 hmapint
  have hne_z : ∀ᵐ w ∂μ, w ∈ ({z} : Set ℂ)ᶜ := by
    have hzero : μ (({z} : Set ℂ)ᶜ)ᶜ = 0 := by
      dsimp [μ]
      simpa using hatomZ
    exact (mem_ae_iff).2 hzero
  have hne_negz : ∀ᵐ w ∂μ, w ∈ ({-z} : Set ℂ)ᶜ := by
    have hzero : μ (({-z} : Set ℂ)ᶜ)ᶜ = 0 := by
      dsimp [μ]
      simpa using hatomNegZ
    exact (mem_ae_iff).2 hzero
  have hsum :
      Integrable (fun w => logKernel z w + logKernel z (-w)) μ := by
    refine hcomp.congr ?_
    filter_upwards [hne_z, hne_negz] with w hwz hwnegz
    exact logKernel_quadratic_eq_add
      (c := c) (z := z) (w := w)
      (fun h => hwz h.symm)
      (fun h => hwnegz (by rw [h]; simp))
  dsimp [μ] at hsum ⊢
  exact integrable_logKernel_limitingBrolinMeasureAt_of_integrable_add_neg_right
    (c := c) (a := a) (z := z) hzK hsum

/-- Unconditional target-measure version of the Half A kernel split.  In the
nonintegrable branch case, reverse integrability transfer forces the target-side
kernel to be nonintegrable too, so both `logPotential`s are `0` by convention. -/
theorem logPotential_limitingBrolinMeasureAt_quadratic_eq_two_of_map_quadratic_of_map_neg
    {c a z : ℂ}
    (hquad :
      Measure.map (quadratic c) (limitingBrolinMeasureAt c a) =
        limitingBrolinMeasureAt c a)
    (hneg :
      Measure.map Neg.neg (limitingBrolinMeasureAt c a) =
        limitingBrolinMeasureAt c a)
    (hzK : z ∈ filledJulia c)
    (hatomZ : limitingBrolinMeasureAt c a ({z} : Set ℂ) = 0)
    (hatomNegZ : limitingBrolinMeasureAt c a ({-z} : Set ℂ) = 0) :
    logPotential (limitingBrolinMeasureAt c a) (quadratic c z) =
      2 * logPotential (limitingBrolinMeasureAt c a) z := by
  by_cases hzint :
      Integrable (fun w => logKernel z w) (limitingBrolinMeasureAt c a)
  · have hnegint :
        Integrable (fun w => logKernel z (-w)) (limitingBrolinMeasureAt c a) := by
      let μ : Measure ℂ := limitingBrolinMeasureAt c a
      have hmap : Measure.map Neg.neg μ = μ := by simpa [μ] using hneg
      have hzmap :
          Integrable (fun w => logKernel z w) (Measure.map Neg.neg μ) := by
        rw [hmap]
        exact hzint
      simpa [μ] using
        (integrable_map_measure
          (logKernel_aestronglyMeasurable z (Measure.map Neg.neg μ))
          continuous_neg.measurable.aemeasurable).1 hzmap
    exact logPotential_quadratic_eq_two_of_map_quadratic_of_map_neg
      (μ := limitingBrolinMeasureAt c a) (c := c) (z := z)
      hquad hneg hatomZ hatomNegZ hzint hnegint
  · have hfnot :
        ¬ Integrable (fun y => logKernel (quadratic c z) y)
          (limitingBrolinMeasureAt c a) := by
      intro hfint
      exact hzint
        (integrable_logKernel_limitingBrolinMeasureAt_of_map_quadratic
          (c := c) (a := a) (z := z) hquad hzK hatomZ hatomNegZ hfint)
    have hleft :
        logPotential (limitingBrolinMeasureAt c a) (quadratic c z) = 0 := by
      unfold logPotential
      exact integral_undef hfnot
    have hright :
        logPotential (limitingBrolinMeasureAt c a) z = 0 := by
      unfold logPotential
      exact integral_undef hzint
    rw [hleft, hright, mul_zero]

/-- Half A from target-measure `f_c`-invariance and the free antipodal symmetry,
with no separate boundary-kernel integrability hypothesis. -/
theorem BrolinScalingAt_of_map_quadratic_unconditional
    {c a : ℂ}
    (hquad :
      Measure.map (quadratic c) (limitingBrolinMeasureAt c a) =
        limitingBrolinMeasureAt c a)
    (hatom :
      ∀ z : ℂ, z ∈ filledJulia c → limitingBrolinMeasureAt c a {z} = 0) :
    BrolinScalingAt c a := by
  intro z hzK
  have hnegK : -z ∈ filledJulia c := (mem_filledJulia_neg_iff c z).2 hzK
  have hpot :=
    logPotential_limitingBrolinMeasureAt_quadratic_eq_two_of_map_quadratic_of_map_neg
      (c := c) (a := a) (z := z)
      hquad (map_limitingBrolinMeasureAt_neg c a) hzK
      (hatom z hzK) (hatom (-z) hnegK)
  linarith

/-- Half A in the adjacent-shifted convergence form.  The finite balancedness
and antipodal symmetry are internal; the remaining assumption is exactly that
the adjacent selected finite measures have the same weak limit against quadratic
tests. -/
theorem BrolinScalingAt_of_adjacent_subseq_comp_quadratic_tendsto
    {c a : ℂ}
    (hshift :
      ∀ φ : C_c(ℂ, ℝ),
        Tendsto
          (fun k =>
            ∫ z, φ (quadratic c z)
              ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k + 1))
          atTop
          (𝓝 (∫ z, φ (quadratic c z) ∂limitingBrolinMeasureAt c a)))
    (hatom :
      ∀ z : ℂ, z ∈ filledJulia c → limitingBrolinMeasureAt c a {z} = 0) :
    BrolinScalingAt c a :=
  BrolinScalingAt_of_map_quadratic_unconditional
    (map_limitingBrolinMeasureAt_quadratic_of_adjacent_subseq_comp_quadratic_tendsto
      hshift)
    hatom

/-- GAP-A bridge for Half A.  The remaining shifted-measure input is exactly the
identification of the target-`a` potential with the canonical shifted potentials on the two
arguments used by the quadratic identity. -/
theorem BrolinScalingAt_of_target_potential_eq_gapAMu_and_shifted
    {c a : ℂ} (hc : Disconnected c)
    (hquad :
      ∀ z : ℂ, z ∈ filledJulia c →
        logPotential (limitingBrolinMeasureAt c a) (quadratic c z) =
          logPotential (gapAMu c) (quadratic c z))
    (hbase :
      ∀ z : ℂ, z ∈ filledJulia c →
        logPotential (limitingBrolinMeasureAt c a) z =
          logPotential (shiftedLimitingBrolinMeasure c) z) :
    BrolinScalingAt c a := by
  intro z hzK
  have h :=
    neg_logPotential_gapAMu_quadratic_eq_two_neg_shiftedPotential_unconditional
      (c := c) (z := z) hc hzK
  rw [← hquad z hzK, ← hbase z hzK] at h
  exact h

/-- GAP-A bridge for Half B.  The finite-level nonpositivity already proved for the shifted
limit gives Frostman domination once the target-`a` boundary potential is identified with the
shifted one. -/
theorem PotentialDominatedOnFilledJulia_of_target_potential_eq_shifted
    {c a : ℂ} (hc : Disconnected c)
    (hbase :
      ∀ z : ℂ, z ∈ filledJulia c →
        logPotential (limitingBrolinMeasureAt c a) z =
          logPotential (shiftedLimitingBrolinMeasure c) z) :
    PotentialDominatedOnFilledJulia c a := by
  intro z hzK
  rw [hbase z hzK]
  exact
    logPotential_shiftedLimitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK

/-- Finite target-pressure excess is supported exactly on the atom at the evaluation point.
This removes the false eventual-non-atom requirement at fixed targets: atoms are allowed, but
their mass must disappear along the selected levels. -/
theorem integral_truncatedLogKernel_preBrolinMeasureAt_sub_logPotential_le_atom
    (c a z : ℂ) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ w ∂preBrolinMeasureAt c a n -
        logPotential (preBrolinMeasureAt c a n) z ≤
      (- Real.log δ) * (preBrolinMeasureAt c a n ({z} : Set ℂ)).toReal := by
  rw [integral_preBrolinMeasureAt_eq_root_average,
    logPotential_preBrolinMeasureAt_eq_scaled_rootLogKernelSum]
  let s : Multiset ℂ := (quadraticPolyIterate c n - Polynomial.C a).roots
  let A : ℝ := - Real.log δ
  have hμz :
      (preBrolinMeasureAt c a n ({z} : Set ℂ)).toReal =
        (2 ^ n : ℝ)⁻¹ * ((s.filter fun r => r = z).card : ℝ) := by
    rw [preBrolinMeasureAt, Measure.smul_apply,
      rootCountingMeasure_apply_of_measurableSet _ (measurableSet_singleton z)]
    simp [s, ENNReal.toReal_inv, ENNReal.toReal_pow]
  have hpoint :
      ∀ r ∈ s,
        truncatedLogKernel z δ r - logKernel z r ≤ if r = z then A else 0 := by
    intro r _hr
    by_cases hrz : r = z
    · subst r
      have hmax0 : max δ 0 = δ := max_eq_left hδ.le
      have heq : truncatedLogKernel z δ z - logKernel z z = A := by
        simp [A, truncatedLogKernel, logKernel, hmax0]
      simp [heq]
    · have hle : truncatedLogKernel z δ r ≤ logKernel z r := by
        exact truncatedLogKernel_le_logKernel_of_ne hδ (fun hzr => hrz hzr.symm)
      have hdiff : truncatedLogKernel z δ r - logKernel z r ≤ 0 := by linarith
      simpa [hrz] using hdiff
  have hsum := multiset_sum_map_le_of_forall s hpoint
  rw [multiset_sum_map_sub_real] at hsum
  rw [multiset_sum_map_if_const_eq_card_filter_mul] at hsum
  rw [hμz]
  have hscale_nonneg : 0 ≤ (2 ^ n : ℝ)⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsum hscale_nonneg]

/-- Arbitrary-target finite-to-limit boundary truncation passage.  If the
selected finite target potentials tend to zero at `z`, and `z` is eventually
not an atom of the selected pullback levels, then every positive truncation of
the target limiting potential is nonpositive. -/
theorem integral_truncatedLogKernel_limitingBrolinMeasureAt_nonpos_of_subseq_boundary_potential_tendsto_zero
    {c a z : ℂ}
    (hlog0 :
      Tendsto
        (fun k =>
          logPotential
            (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z)
        atTop (𝓝 0))
    (hnotAtom :
      ∀ᶠ k in atTop,
        (quadratic c)^[brolinLimitAtSubsequence c a k] z - a ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasureAt c a ≤ 0 := by
  have hleft :=
    truncatedLogKernel_preBrolinMeasureAt_subseq_integral_tendsto_limiting
      c a z hδ
  have hdiff := hleft.sub hlog0
  have hle :
      ∀ᶠ k in atTop,
        ∫ w, truncatedLogKernel z δ w
            ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k) -
          logPotential
            (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z ≤ 0 := by
    filter_upwards [hnotAtom] with k hk
    have hineq :=
      integral_truncatedLogKernel_preBrolinMeasureAt_le_logPotential_of_iterate_ne_target
        (c := c) (a := a) (z := z) (δ := δ)
        (n := brolinLimitAtSubsequence c a k) hδ hk
    linarith
  have hlim := le_of_tendsto hdiff hle
  simpa using hlim

/-- Arbitrary-target finite-to-limit boundary truncation passage with atom-mass control.
This is the usable Half B gate at fixed targets: selected finite potentials tend to zero
and the singleton pullback mass at the evaluation point tends to zero. -/
theorem integral_truncatedLogKernel_limitingBrolinMeasureAt_nonpos_of_subseq_boundary_potential_tendsto_zero_of_atom_mass
    {c a z : ℂ}
    (hlog0 :
      Tendsto
        (fun k =>
          logPotential
            (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z)
        atTop (𝓝 0))
    (hatom0 :
      Tendsto
        (fun k =>
          (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)
            ({z} : Set ℂ)).toReal)
        atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasureAt c a ≤ 0 := by
  have hleft :=
    truncatedLogKernel_preBrolinMeasureAt_subseq_integral_tendsto_limiting
      c a z hδ
  have hdiff := hleft.sub hlog0
  have hdiff' :
      Tendsto
        (fun k =>
          ∫ w, truncatedLogKernel z δ w
              ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k) -
            logPotential
              (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z)
        atTop (𝓝 (∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasureAt c a)) := by
    simpa using hdiff
  have herr :
      Tendsto
        (fun k =>
          (- Real.log δ) *
            (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)
              ({z} : Set ℂ)).toReal)
        atTop (𝓝 0) := by
    simpa using hatom0.const_mul (- Real.log δ)
  have hle :
      ∀ᶠ k in atTop,
        ∫ w, truncatedLogKernel z δ w
            ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k) -
          logPotential
            (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z ≤
          (- Real.log δ) *
            (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)
              ({z} : Set ℂ)).toReal := by
    exact Filter.Eventually.of_forall fun k =>
      integral_truncatedLogKernel_preBrolinMeasureAt_sub_logPotential_le_atom
        c a z (brolinLimitAtSubsequence c a k) hδ
  exact le_of_tendsto_of_tendsto hdiff' herr hle

/-- Arbitrary-target finite-to-limit boundary truncation passage from finite
log-potential nonpositivity.  This is the Half B pressure form: finite
`logPotential` is allowed to have atoms, and the singleton error disappears in
the selected weak limit. -/
theorem integral_truncatedLogKernel_limitingBrolinMeasureAt_nonpos_of_subseq_logPotential_nonpos_of_atom_mass
    {c a z : ℂ}
    (hlogNonpos :
      ∀ᶠ k in atTop,
        logPotential
          (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z ≤ 0)
    (hatom0 :
      Tendsto
        (fun k =>
          (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)
            ({z} : Set ℂ)).toReal)
        atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasureAt c a ≤ 0 := by
  have hleft :=
    truncatedLogKernel_preBrolinMeasureAt_subseq_integral_tendsto_limiting
      c a z hδ
  have herr :
      Tendsto
        (fun k =>
          (- Real.log δ) *
            (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)
              ({z} : Set ℂ)).toReal)
        atTop (𝓝 0) := by
    simpa using hatom0.const_mul (- Real.log δ)
  have hle :
      ∀ᶠ k in atTop,
        ∫ w, truncatedLogKernel z δ w
            ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k) ≤
          (- Real.log δ) *
            (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)
              ({z} : Set ℂ)).toReal := by
    filter_upwards [hlogNonpos] with k hk
    have h :=
      integral_truncatedLogKernel_preBrolinMeasureAt_sub_logPotential_le_atom
        c a z (brolinLimitAtSubsequence c a k) hδ
    linarith
  exact le_of_tendsto_of_tendsto hleft herr hle

/-- If the target avoids the positive critical orbit, every level-`n` pullback root of
`a` is simple.  A multiple root would be a critical point of `f_c^[n]`, hence would
force a positive critical-orbit hit on `a`. -/
theorem roots_nodup_quadraticPolyIterate_sub_C_of_criticalOrbitAvoidingTarget
    {c a : ℂ} (hcrit : CriticalOrbitAvoidingTarget c a) (n : ℕ) :
    (quadraticPolyIterate c n - Polynomial.C a).roots.Nodup := by
  classical
  refine Multiset.nodup_iff_count_le_one.mpr ?_
  intro r
  rw [Polynomial.count_roots]
  by_contra hle
  have hmult : 1 < (quadraticPolyIterate c n - Polynomial.C a).rootMultiplicity r :=
    Nat.lt_of_not_ge hle
  have hp : quadraticPolyIterate c n - Polynomial.C a ≠ 0 :=
    (quadraticPolyIterate_sub_C_monic c a n).ne_zero
  rcases
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot
      (p := quadraticPolyIterate c n - Polynomial.C a) (t := r) hp).mp hmult with
    ⟨hroot, hderiv⟩
  have hroot_eval : (quadratic c)^[n] r = a := by
    simpa [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C,
      quadraticPolyIterate_eval, sub_eq_zero] using hroot
  have hderiv_eval :
      (quadraticPolyIterate c n).derivative.eval r = 0 := by
    simpa [Polynomial.IsRoot.def, Polynomial.derivative_sub, Polynomial.derivative_C] using hderiv
  rcases (quadratic_iterate_deriv_eq_zero_iff c n r).mp hderiv_eval with
    ⟨k, hk, hkzero⟩
  have hreturn : (quadratic c)^[n - k] (0 : ℂ) = a := by
    have hroot' : (quadratic c)^[(n - k) + k] r = a := by
      rwa [Nat.sub_add_cancel (le_of_lt hk)]
    simpa [Function.iterate_add_apply, hkzero] using hroot'
  exact hcrit (n - k) (Nat.sub_pos_of_lt hk) hreturn

/-- Under critical-orbit avoidance, a singleton can carry at most one simple level-`n`
pullback atom, hence normalized mass at most `2⁻ⁿ`. -/
theorem preBrolinMeasureAt_singleton_toReal_le_inv_pow_of_criticalOrbitAvoidingTarget
    {c a z : ℂ} (hcrit : CriticalOrbitAvoidingTarget c a) (n : ℕ) :
    (preBrolinMeasureAt c a n ({z} : Set ℂ)).toReal ≤ (2 ^ n : ℝ)⁻¹ := by
  classical
  let s : Multiset ℂ := (quadraticPolyIterate c n - Polynomial.C a).roots
  have hμz :
      (preBrolinMeasureAt c a n ({z} : Set ℂ)).toReal =
        (2 ^ n : ℝ)⁻¹ * ((s.filter fun r => r = z).card : ℝ) := by
    rw [preBrolinMeasureAt, Measure.smul_apply,
      rootCountingMeasure_apply_of_measurableSet _ (measurableSet_singleton z)]
    simp [s, ENNReal.toReal_inv, ENNReal.toReal_pow]
  have hcardNat : (s.filter fun r => r = z).card ≤ 1 := by
    have hnodup_filter : (s.filter fun r => r = z).Nodup :=
      (roots_nodup_quadraticPolyIterate_sub_C_of_criticalOrbitAvoidingTarget
        hcrit n).filter _
    rw [← Multiset.toFinset_card_of_nodup hnodup_filter]
    refine Finset.card_le_one_iff.mpr ?_
    intro x y hx hy
    have hxms : x ∈ (s.filter fun r => r = z) := Multiset.mem_toFinset.mp hx
    have hyms : y ∈ (s.filter fun r => r = z) := Multiset.mem_toFinset.mp hy
    have hxz : x = z := (Multiset.mem_filter.mp hxms).2
    have hyz : y = z := (Multiset.mem_filter.mp hyms).2
    exact hxz.trans hyz.symm
  rw [hμz]
  have hcard : ((s.filter fun r => r = z).card : ℝ) ≤ 1 := by exact_mod_cast hcardNat
  have hscale_nonneg : 0 ≤ (2 ^ n : ℝ)⁻¹ := by positivity
  simpa using mul_le_mul_of_nonneg_left hcard hscale_nonneg

/-- The selected finite singleton masses vanish for every fixed point when the target is
not postcritical. -/
theorem preBrolinMeasureAt_subseq_singleton_toReal_tendsto_zero_of_criticalOrbitAvoidingTarget
    {c a z : ℂ} (hcrit : CriticalOrbitAvoidingTarget c a) :
    Tendsto
      (fun k =>
        (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)
          ({z} : Set ℂ)).toReal)
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => (2 ^ n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)))
  refine squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun k => ?_)
    (g := fun k => (2 ^ brolinLimitAtSubsequence c a k : ℝ)⁻¹) ?_
  · exact preBrolinMeasureAt_singleton_toReal_le_inv_pow_of_criticalOrbitAvoidingTarget
      (c := c) (a := a) (z := z) hcrit (brolinLimitAtSubsequence c a k)
  · exact hpow.comp (brolinLimitAtSubsequence_tendsto_atTop c a)

/-- If all positive truncation pressures at a filled-Julia point are nonpositive,
then the target limiting Brolin measure has no atom at that point.  The proof is
the compact-carrier atom-pressure argument, using that the target limiting
measure is carried by `K_c` even though it is constructed on `targetEscapeDisk`. -/
theorem limitingBrolinMeasureAt_singleton_eq_zero_of_truncatedLogKernel_nonpos
    {c a z : ℂ} (hzK : z ∈ filledJulia c)
    (hnonpos : ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
      ∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasureAt c a ≤ 0) :
    limitingBrolinMeasureAt c a ({z} : Set ℂ) = 0 := by
  let μT : Measure (targetEscapeDisk c a) :=
    (brolinLimitAtOnTargetEscapeDisk c a : Measure (targetEscapeDisk c a))
  haveI : IsProbabilityMeasure μT := by
    dsimp [μT]
    infer_instance
  have hzTarget : z ∈ targetEscapeDisk c a := by
    rw [targetEscapeDisk, Metric.mem_closedBall, dist_zero_right]
    have hzEsc := mem_escapeDisk_of_mem_filledJulia hzK
    have hzle : ‖z‖ ≤ max 2 ‖c‖ := by
      simpa [escapeDisk, Metric.mem_closedBall, dist_zero_right] using hzEsc
    exact le_trans hzle (le_max_left _ _)
  let zz : targetEscapeDisk c a := ⟨z, hzTarget⟩
  have hsingle :
      limitingBrolinMeasureAt c a ({z} : Set ℂ) =
        μT ({zz} : Set (targetEscapeDisk c a)) := by
    have hmeas : MeasurableSet ({z} : Set ℂ) := measurableSet_singleton z
    rw [limitingBrolinMeasureAt, Measure.map_apply measurable_subtype_coe hmeas]
    congr 1
    ext w
    constructor
    · intro hw
      exact Subtype.ext (by simpa using hw)
    · intro hw
      rw [hw]
      simp [zz]
  rw [hsingle]
  by_contra hne
  have hmTop : μT ({zz} : Set (targetEscapeDisk c a)) ≠ ⊤ :=
    measure_ne_top μT {zz}
  let m : ℝ := (μT ({zz} : Set (targetEscapeDisk c a))).toReal
  have hmpos : 0 < m := ENNReal.toReal_pos hne hmTop
  let C : ℝ := 2 * max 2 ‖c‖
  have hCgt : 1 < C := by
    dsimp [C]
    have hR : (2 : ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
    nlinarith
  have hCge : 1 ≤ C := le_of_lt hCgt
  have hlogCpos : 0 < Real.log C := Real.log_pos hCgt
  let δ : ℝ := Real.exp (-(Real.log C / m + Real.log C + 1))
  have hδpos : 0 < δ := Real.exp_pos _
  have hδle : δ ≤ 1 := by
    dsimp [δ]
    rw [Real.exp_le_one_iff]
    have hdiv_nonneg : 0 ≤ Real.log C / m :=
      div_nonneg hlogCpos.le hmpos.le
    nlinarith
  have hδC : δ ≤ C := le_trans hδle hCge
  have hmaxC : max δ C = C := max_eq_right hδC
  let A : ℝ := - Real.log δ
  let B : ℝ := - Real.log C
  let S : Set (targetEscapeDisk c a) := {zz}
  have hS : MeasurableSet S := measurableSet_singleton zz
  let atomIndicator : targetEscapeDisk c a → ℝ := S.indicator (fun _ => (1 : ℝ))
  have hconst : Integrable (fun _ : targetEscapeDisk c a => B) μT :=
    integrable_const B
  have hind : Integrable atomIndicator μT := by
    dsimp [atomIndicator]
    exact (integrable_const (α := targetEscapeDisk c a) (μ := μT) (1 : ℝ)).indicator hS
  have hscaled : Integrable
      (fun w : targetEscapeDisk c a => (A - B) * atomIndicator w) μT :=
    hind.const_mul (A - B)
  have hlowerInt :
      Integrable
        (fun w : targetEscapeDisk c a => B + (A - B) * atomIndicator w) μT :=
    hconst.add hscaled
  have htruncInt :
      Integrable (fun w : targetEscapeDisk c a => truncatedLogKernel z δ (w : ℂ)) μT := by
    simpa [truncatedLogKernelOnTargetEscapeDisk, μT] using
      (truncatedLogKernelOnTargetEscapeDisk c a z δ hδpos).integrable μT
  have hKcompl :
      μT (((fun w : targetEscapeDisk c a => (w : ℂ)) ⁻¹'
        (filledJulia c)ᶜ)) = 0 := by
    have hplane := limitingBrolinMeasureAt_filledJulia_compl c a
    have hmeas : MeasurableSet ((filledJulia c)ᶜ : Set ℂ) :=
      (isClosed_filledJulia c).measurableSet.compl
    rw [limitingBrolinMeasureAt, Measure.map_apply measurable_subtype_coe hmeas] at hplane
    simpa [μT] using hplane
  have hKcompl' :
      μT ({w : targetEscapeDisk c a | (w : ℂ) ∈ filledJulia c}ᶜ) = 0 := by
    simpa [Set.preimage, Set.compl_setOf] using hKcompl
  have hmemK : ∀ᵐ (w : targetEscapeDisk c a) ∂μT, (w : ℂ) ∈ filledJulia c :=
    (mem_ae_iff).2 hKcompl'
  have hzEsc : z ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hzK
  have hmono :
      (fun w : targetEscapeDisk c a => B + (A - B) * atomIndicator w) ≤ᵐ[μT]
        (fun w : targetEscapeDisk c a => truncatedLogKernel z δ (w : ℂ)) := by
    filter_upwards [hmemK] with w hwK
    by_cases hw : w = zz
    · subst w
      have hzz : (zz : ℂ) = z := rfl
      simp [truncatedLogKernel, A, B, hzz, hδpos.le, S, atomIndicator]
    · have hnot : w ∉ S := by
        simpa [S] using hw
      have hwEsc : (w : ℂ) ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hwK
      have hlower :=
        truncatedLogKernel_escapeDisk_lower_bound (c := c) (z := z) (w := (w : ℂ))
          hδpos hzEsc hwEsc
      rw [hmaxC] at hlower
      calc
        B + (A - B) * atomIndicator w = B := by
          simp [atomIndicator, Set.indicator_of_notMem hnot]
        _ ≤ truncatedLogKernel z δ (w : ℂ) := by
          simpa [B, C] using hlower
  have hle := integral_mono_ae hlowerInt htruncInt hmono
  have hlowerIntegral :
      ∫ w : targetEscapeDisk c a, B + (A - B) * atomIndicator w ∂μT =
        B + (A - B) * (μT ({zz} : Set (targetEscapeDisk c a))).toReal := by
    rw [integral_add hconst hscaled]
    rw [integral_const, integral_const_mul]
    have hindint :
        ∫ w : targetEscapeDisk c a, atomIndicator w ∂μT =
          (μT ({zz} : Set (targetEscapeDisk c a))).toReal := by
      rw [show atomIndicator = S.indicator (fun _ => (1 : ℝ)) from rfl]
      rw [integral_indicator_const (1 : ℝ) hS]
      simp [S, measureReal_def]
    rw [hindint]
    simp [measureReal_def]
  have htargetNonpos :
      ∫ w : targetEscapeDisk c a, truncatedLogKernel z δ (w : ℂ) ∂μT ≤ 0 := by
    rw [← integral_truncatedLogKernel_limitingBrolinMeasureAt_eq_integral_targetEscapeDisk
      c a z hδpos]
    exact hnonpos hδpos hδle
  have hpress :
      B + (A - B) * (μT ({zz} : Set (targetEscapeDisk c a))).toReal ≤ 0 :=
    le_trans (by simpa [hlowerIntegral] using hle) htargetNonpos
  have hden :
      - Real.log δ + Real.log C =
        Real.log C / m + 2 * Real.log C + 1 := by
    dsimp [δ]
    rw [Real.log_exp]
    ring
  have hmass' :
      m ≤ Real.log C / (Real.log C / m + 2 * Real.log C + 1) := by
    have hDpos : 0 < - Real.log δ + Real.log C := by
      have hlogδnonpos : Real.log δ ≤ 0 := Real.log_nonpos hδpos.le hδle
      nlinarith
    rw [← hden, le_div_iff₀ hDpos]
    have hpress' :
        - Real.log C + (- Real.log δ + Real.log C) * m ≤ 0 := by
      simpa [A, B, C, m, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hpress
    nlinarith
  have hdenpos : 0 < Real.log C / m + 2 * Real.log C + 1 := by
    have hdivpos : 0 < Real.log C / m := div_pos hlogCpos hmpos
    nlinarith
  have hlt : Real.log C / (Real.log C / m + 2 * Real.log C + 1) < m := by
    rw [div_lt_iff₀ hdenpos]
    have hmul :
        m * (Real.log C / m + 2 * Real.log C + 1) =
          Real.log C + m * (2 * Real.log C + 1) := by
      field_simp [ne_of_gt hmpos]
      ring
    rw [hmul]
    have htail : 0 < m * (2 * Real.log C + 1) :=
      mul_pos hmpos (by nlinarith)
    nlinarith
  exact (not_lt_of_ge hmass') hlt

/-- Atomlessness from the finite-pressure Half B gate plus finite singleton-mass
decay. -/
theorem limitingBrolinMeasureAt_singleton_eq_zero_of_subseq_logPotential_nonpos_of_atom_mass
    {c a z : ℂ} (hzK : z ∈ filledJulia c)
    (hlogNonpos :
      ∀ᶠ k in atTop,
        logPotential
          (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z ≤ 0)
    (hatom0 :
      Tendsto
        (fun k =>
          (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)
            ({z} : Set ℂ)).toReal)
        atTop (𝓝 0)) :
    limitingBrolinMeasureAt c a ({z} : Set ℂ) = 0 :=
  limitingBrolinMeasureAt_singleton_eq_zero_of_truncatedLogKernel_nonpos hzK
    (fun hδ _hδle =>
      integral_truncatedLogKernel_limitingBrolinMeasureAt_nonpos_of_subseq_logPotential_nonpos_of_atom_mass
        (c := c) (a := a) (z := z) hlogNonpos hatom0 hδ)

/-- Atomlessness from finite-pressure nonpositivity, with finite singleton-mass
decay discharged by critical-orbit avoidance. -/
theorem limitingBrolinMeasureAt_singleton_eq_zero_of_subseq_logPotential_nonpos_of_criticalOrbitAvoidingTarget
    {c a z : ℂ} (hzK : z ∈ filledJulia c)
    (hlogNonpos :
      ∀ᶠ k in atTop,
        logPotential
          (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z ≤ 0)
    (hcrit : CriticalOrbitAvoidingTarget c a) :
    limitingBrolinMeasureAt c a ({z} : Set ℂ) = 0 :=
  limitingBrolinMeasureAt_singleton_eq_zero_of_subseq_logPotential_nonpos_of_atom_mass
    hzK hlogNonpos
    (preBrolinMeasureAt_subseq_singleton_toReal_tendsto_zero_of_criticalOrbitAvoidingTarget
      hcrit)

/-- Atomlessness from boundary-potential convergence plus finite singleton-mass
decay. -/
theorem limitingBrolinMeasureAt_singleton_eq_zero_of_subseq_boundary_potential_tendsto_zero_of_atom_mass
    {c a z : ℂ} (hzK : z ∈ filledJulia c)
    (hlog0 :
      Tendsto
        (fun k =>
          logPotential
            (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z)
        atTop (𝓝 0))
    (hatom0 :
      Tendsto
        (fun k =>
          (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)
            ({z} : Set ℂ)).toReal)
        atTop (𝓝 0)) :
    limitingBrolinMeasureAt c a ({z} : Set ℂ) = 0 :=
  limitingBrolinMeasureAt_singleton_eq_zero_of_truncatedLogKernel_nonpos hzK
    (fun hδ _hδle =>
      integral_truncatedLogKernel_limitingBrolinMeasureAt_nonpos_of_subseq_boundary_potential_tendsto_zero_of_atom_mass
        (c := c) (a := a) (z := z) hlog0 hatom0 hδ)

/-- Atomlessness from boundary-potential convergence, with finite singleton-mass
decay discharged by critical-orbit avoidance. -/
theorem limitingBrolinMeasureAt_singleton_eq_zero_of_subseq_boundary_potential_tendsto_zero_of_criticalOrbitAvoidingTarget
    {c a z : ℂ} (hzK : z ∈ filledJulia c)
    (hlog0 :
      Tendsto
        (fun k =>
          logPotential
            (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z)
        atTop (𝓝 0))
    (hcrit : CriticalOrbitAvoidingTarget c a) :
    limitingBrolinMeasureAt c a ({z} : Set ℂ) = 0 :=
  limitingBrolinMeasureAt_singleton_eq_zero_of_subseq_boundary_potential_tendsto_zero_of_atom_mass
    hzK hlog0
    (preBrolinMeasureAt_subseq_singleton_toReal_tendsto_zero_of_criticalOrbitAvoidingTarget
      hcrit)

/-- GAP-A bridge for Half B in the arbitrary-target subsequence language.  The
finite pressure estimate has a singleton atom error; the hypotheses here are the exact
remaining boundary value and vanishing-atom-mass gates needed to pass it through the
selected weak limit. -/
theorem PotentialDominatedOnFilledJulia_of_subseq_boundary_potential_tendsto_zero
    {c a : ℂ}
    (hatom :
      ∀ z : ℂ, z ∈ filledJulia c → limitingBrolinMeasureAt c a {z} = 0)
    (hlog0 :
      ∀ z : ℂ, z ∈ filledJulia c →
        Tendsto
          (fun k =>
            logPotential
              (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z)
          atTop (𝓝 0))
    (hatom0 :
      ∀ z : ℂ, z ∈ filledJulia c →
        Tendsto
          (fun k =>
            (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)
              ({z} : Set ℂ)).toReal)
          atTop (𝓝 0)) :
    PotentialDominatedOnFilledJulia c a := by
  intro z hzK
  by_cases hint : Integrable (fun w => logKernel z w) (limitingBrolinMeasureAt c a)
  · have hzero :
        limitingBrolinMeasureAt c a (({z} : Set ℂ)ᶜ)ᶜ = 0 := by
      simpa using hatom z hzK
    have hne_ae : ∀ᵐ w ∂limitingBrolinMeasureAt c a, w ∈ ({z} : Set ℂ)ᶜ :=
      (mem_ae_iff).2 hzero
    have hlim :
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂limitingBrolinMeasureAt c a)
          atTop (𝓝 (logPotential (limitingBrolinMeasureAt c a) z)) := by
      unfold logPotential
      refine tendsto_integral_of_dominated_convergence
        (fun w => ‖logKernel z w‖) ?_ hint.norm ?_ ?_
      · intro n
        exact (continuous_truncatedLogKernel
          (z := z) (δ := (((n + 1 : ℕ) : ℝ)⁻¹))
          (by positivity)).aestronglyMeasurable
      · intro n
        have hδle : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
          have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          exact inv_le_one_of_one_le₀ hn
        filter_upwards [hne_ae] with w hw
        exact norm_truncatedLogKernel_le_norm_logKernel_of_ne_of_le_one
          (by positivity) hδle (fun hzw => hw hzw.symm)
      · filter_upwards [hne_ae] with w hw
        exact truncatedLogKernel_inv_nat_succ_tendsto_logKernel_of_ne
          (fun hzw => hw hzw.symm)
    have hnonpos :
        ∀ n : ℕ,
          ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂limitingBrolinMeasureAt c a ≤ 0 := by
      intro n
      exact
        integral_truncatedLogKernel_limitingBrolinMeasureAt_nonpos_of_subseq_boundary_potential_tendsto_zero_of_atom_mass
          (c := c) (a := a) (z := z) (hlog0 z hzK) (hatom0 z hzK)
          (by positivity)
    exact le_of_tendsto hlim (Filter.Eventually.of_forall hnonpos)
  · have hzero : logPotential (limitingBrolinMeasureAt c a) z = 0 := by
      unfold logPotential
      exact integral_undef hint
    rw [hzero]

/-- Half B from finite log-potential nonpositivity along the selected pullback
levels.  This is the direct finite-pressure/Fatou route: finite atoms contribute
only the explicit singleton error, which is assumed to vanish. -/
theorem PotentialDominatedOnFilledJulia_of_subseq_logPotential_nonpos
    {c a : ℂ}
    (hatom :
      ∀ z : ℂ, z ∈ filledJulia c → limitingBrolinMeasureAt c a {z} = 0)
    (hlogNonpos :
      ∀ z : ℂ, z ∈ filledJulia c →
        ∀ᶠ k in atTop,
          logPotential
            (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z ≤ 0)
    (hatom0 :
      ∀ z : ℂ, z ∈ filledJulia c →
        Tendsto
          (fun k =>
            (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)
              ({z} : Set ℂ)).toReal)
          atTop (𝓝 0)) :
    PotentialDominatedOnFilledJulia c a := by
  intro z hzK
  by_cases hint : Integrable (fun w => logKernel z w) (limitingBrolinMeasureAt c a)
  · have hzero :
        limitingBrolinMeasureAt c a (({z} : Set ℂ)ᶜ)ᶜ = 0 := by
      simpa using hatom z hzK
    have hne_ae : ∀ᵐ w ∂limitingBrolinMeasureAt c a, w ∈ ({z} : Set ℂ)ᶜ :=
      (mem_ae_iff).2 hzero
    have hlim :
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂limitingBrolinMeasureAt c a)
          atTop (𝓝 (logPotential (limitingBrolinMeasureAt c a) z)) := by
      unfold logPotential
      refine tendsto_integral_of_dominated_convergence
        (fun w => ‖logKernel z w‖) ?_ hint.norm ?_ ?_
      · intro n
        exact (continuous_truncatedLogKernel
          (z := z) (δ := (((n + 1 : ℕ) : ℝ)⁻¹))
          (by positivity)).aestronglyMeasurable
      · intro n
        have hδle : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
          have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          exact inv_le_one_of_one_le₀ hn
        filter_upwards [hne_ae] with w hw
        exact norm_truncatedLogKernel_le_norm_logKernel_of_ne_of_le_one
          (by positivity) hδle (fun hzw => hw hzw.symm)
      · filter_upwards [hne_ae] with w hw
        exact truncatedLogKernel_inv_nat_succ_tendsto_logKernel_of_ne
          (fun hzw => hw hzw.symm)
    have hnonpos :
        ∀ n : ℕ,
          ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂limitingBrolinMeasureAt c a ≤ 0 := by
      intro n
      exact
        integral_truncatedLogKernel_limitingBrolinMeasureAt_nonpos_of_subseq_logPotential_nonpos_of_atom_mass
          (c := c) (a := a) (z := z) (hlogNonpos z hzK) (hatom0 z hzK)
          (by positivity)
    exact le_of_tendsto hlim (Filter.Eventually.of_forall hnonpos)
  · have hzero : logPotential (limitingBrolinMeasureAt c a) z = 0 := by
      unfold logPotential
      exact integral_undef hint
    rw [hzero]

/-- Half B from finite log-potential nonpositivity, with finite singleton-mass
decay discharged by critical-orbit avoidance. -/
theorem PotentialDominatedOnFilledJulia_of_subseq_logPotential_nonpos_of_criticalOrbitAvoidingTarget
    {c a : ℂ}
    (hlogNonpos :
      ∀ z : ℂ, z ∈ filledJulia c →
        ∀ᶠ k in atTop,
          logPotential
            (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z ≤ 0)
    (hcrit : CriticalOrbitAvoidingTarget c a) :
    PotentialDominatedOnFilledJulia c a :=
  PotentialDominatedOnFilledJulia_of_subseq_logPotential_nonpos
    (fun z hzK =>
      limitingBrolinMeasureAt_singleton_eq_zero_of_subseq_logPotential_nonpos_of_criticalOrbitAvoidingTarget
        hzK (hlogNonpos z hzK) hcrit)
    hlogNonpos
    (fun _z _hzK =>
      preBrolinMeasureAt_subseq_singleton_toReal_tendsto_zero_of_criticalOrbitAvoidingTarget
        hcrit)

/-- Half B with the finite singleton-mass gate discharged by critical-orbit avoidance. -/
theorem PotentialDominatedOnFilledJulia_of_subseq_boundary_potential_tendsto_zero_of_criticalOrbitAvoidingTarget
    {c a : ℂ}
    (hlog0 :
      ∀ z : ℂ, z ∈ filledJulia c →
        Tendsto
          (fun k =>
            logPotential
              (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z)
          atTop (𝓝 0))
    (hcrit : CriticalOrbitAvoidingTarget c a) :
    PotentialDominatedOnFilledJulia c a :=
  PotentialDominatedOnFilledJulia_of_subseq_boundary_potential_tendsto_zero
    (fun z hzK =>
      limitingBrolinMeasureAt_singleton_eq_zero_of_subseq_boundary_potential_tendsto_zero_of_criticalOrbitAvoidingTarget
        hzK (hlog0 z hzK) hcrit)
    hlog0
    (fun _z _hzK =>
      preBrolinMeasureAt_subseq_singleton_toReal_tendsto_zero_of_criticalOrbitAvoidingTarget
        hcrit)

/-- GAP-A bridge for Half A in adjacent-subsequence form.  Finite
arbitrary-target scaling gives the equality at levels `n` and `n+1`; the exact
remaining limit input is that the selected subsequence at `f_c z` and the
adjacent selected subsequence at `z` converge to the same target limiting
potential. -/
theorem BrolinScalingAt_of_adjacent_subseq_potential_tendsto
    {c a : ℂ}
    (hleft :
      ∀ z : ℂ, z ∈ filledJulia c →
        Tendsto
          (fun k =>
            - logPotential
              (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k))
              (quadratic c z))
          atTop
          (𝓝 (- logPotential (limitingBrolinMeasureAt c a) (quadratic c z))))
    (hright :
      ∀ z : ℂ, z ∈ filledJulia c →
        Tendsto
          (fun k =>
            - logPotential
              (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k + 1)) z)
          atTop
          (𝓝 (- logPotential (limitingBrolinMeasureAt c a) z)))
    (hnotAtom :
      ∀ z : ℂ, z ∈ filledJulia c →
        ∀ᶠ k in atTop,
          (quadratic c)^[brolinLimitAtSubsequence c a k + 1] z - a ≠ 0) :
    BrolinScalingAt c a := by
  intro z hzK
  have hfinite :
      ∀ᶠ k in atTop,
        - logPotential
            (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k))
            (quadratic c z) =
          2 * (- logPotential
            (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k + 1)) z) := by
    filter_upwards [hnotAtom z hzK] with k hk
    exact
      neg_logPotential_preBrolinMeasureAt_quadratic_eq_two_succ
        (c := c) (a := a) (z := z)
        (n := brolinLimitAtSubsequence c a k) hk
  have hleftLimit := (hleft z hzK).congr' hfinite
  have hrightLimit := (hright z hzK).const_mul 2
  exact tendsto_nhds_unique hleftLimit hrightLimit

/-- **Half A (doubling ⟹ `Uᵘ ≥ 0` on `K_c`).**  From the scaling law: a point of `K_c`
with `−Uᵘ > 0` would double `−Uᵘ` along its bounded forward orbit past the uniform
upper bound.  Hence `−Uᵘ ≤ 0`, i.e. `Uᵘ ≥ 0`, on `K_c`. -/
theorem neg_logPotential_limitingBrolinMeasureAt_nonpos_of_scaling
    {c a z : ℂ} (hzK : z ∈ filledJulia c) (hscale : BrolinScalingAt c a) :
    - logPotential (limitingBrolinMeasureAt c a) z ≤ 0 := by
  by_contra hle
  have hpos : 0 < - logPotential (limitingBrolinMeasureAt c a) z := lt_of_not_ge hle
  set A : ℕ → ℝ :=
    fun n => - logPotential (limitingBrolinMeasureAt c a) ((quadratic c)^[n] z) with hAdef
  have hA : ∀ n : ℕ, A n = (2 ^ n : ℝ) * (- logPotential (limitingBrolinMeasureAt c a) z) := by
    intro n
    induction n with
    | zero => simp [hAdef]
    | succ n ih =>
        have hnK : (quadratic c)^[n] z ∈ filledJulia c := filledJulia_forward hzK n
        calc
          A (n + 1)
              = - logPotential (limitingBrolinMeasureAt c a)
                  (quadratic c ((quadratic c)^[n] z)) := by
                    simp [hAdef, Function.iterate_succ_apply']
          _ = 2 * (- logPotential (limitingBrolinMeasureAt c a) ((quadratic c)^[n] z)) :=
                    hscale ((quadratic c)^[n] z) hnK
          _ = 2 * A n := by rw [hAdef]
          _ = 2 * ((2 ^ n : ℝ) * (- logPotential (limitingBrolinMeasureAt c a) z)) := by rw [ih]
          _ = (2 ^ (n + 1) : ℝ) * (- logPotential (limitingBrolinMeasureAt c a) z) := by
                    rw [pow_succ]; ring
  set B : ℝ := Real.log (2 * max 2 ‖c‖) with hBdef
  have htend :
      Tendsto (fun n : ℕ => (2 ^ n : ℝ) * (- logPotential (limitingBrolinMeasureAt c a) z))
        atTop atTop := by
    simpa [mul_comm] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_mul_atTop hpos
  rcases (eventually_atTop.1 (htend.eventually_gt_atTop B)) with ⟨N, hN⟩
  have hNK : (quadratic c)^[N] z ∈ filledJulia c := filledJulia_forward hzK N
  have hbound : A N ≤ B :=
    neg_logPotential_limitingBrolinMeasureAt_upper_bound_of_mem_filledJulia hNK
  have hgt : B < A N := by rw [hA N]; exact hN N le_rfl
  exact not_lt_of_ge hbound hgt

/-- **Assembly: the equilibrium potential vanishes a.e. on `K_c`** from the doubling
law (half A) plus Frostman domination (half B).  In fact it vanishes *everywhere* on
`K_c`; the a.e. form is what the GAP-A Riesz identity consumes. -/
theorem equilibriumPotentialVanishesAe_of_scaling_of_dominated (c a : ℂ)
    (hscale : BrolinScalingAt c a) (hdom : PotentialDominatedOnFilledJulia c a) :
    EquilibriumPotentialVanishesAe c a :=
  ae_of_all _ (fun z hzK => by
    have hge : 0 ≤ logPotential (limitingBrolinMeasureAt c a) z := by
      have h := neg_logPotential_limitingBrolinMeasureAt_nonpos_of_scaling hzK hscale
      linarith
    linarith [hdom z hzK])

/-- **The q62 support datum from the two sharp potential-theory halves**, for every `c`.
Composes with the Frostman-form support route (`Q62WeylDischarge`, Weyl discharged). -/
theorem limitingBrolinMeasureAtSupportsJulia_of_scaling_of_dominated (c a : ℂ)
    (hscale : BrolinScalingAt c a) (hdom : PotentialDominatedOnFilledJulia c a) :
    LimitingBrolinMeasureAtSupportsJulia c a :=
  limitingBrolinMeasureAtSupportsJulia_of_equilibriumVanishes c a
    (equilibriumPotentialVanishesAe_of_scaling_of_dominated c a hscale hdom)

/-- GAP-A support from the genuine Half A scaling law and the finite Half B boundary
gate.  This is the fixed-target-safe route: Half A is not obtained by excluding finite
atoms at the target, while Half B's finite atom error is killed by critical-orbit avoidance. -/
theorem limitingBrolinMeasureAtSupportsJulia_of_scaling_and_boundary_potential_tendsto_zero
    {c a : ℂ}
    (hscale : BrolinScalingAt c a)
    (hdomLog0 :
      ∀ z : ℂ, z ∈ filledJulia c →
        Tendsto
          (fun k =>
            logPotential
              (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z)
          atTop (𝓝 0))
    (hdomCrit : CriticalOrbitAvoidingTarget c a) :
    LimitingBrolinMeasureAtSupportsJulia c a :=
  limitingBrolinMeasureAtSupportsJulia_of_scaling_of_dominated c a hscale
    (PotentialDominatedOnFilledJulia_of_subseq_boundary_potential_tendsto_zero_of_criticalOrbitAvoidingTarget
      hdomLog0 hdomCrit)

/-- Fixed-point form of the fixed-target-safe GAP-A support route. -/
theorem forall_fixedPoint_limitingBrolinMeasureAtSupportsJulia_of_scaling_and_boundary_potential_tendsto_zero
    {c : ℂ}
    (hscale : ∀ a : ℂ, quadratic c a = a → BrolinScalingAt c a)
    (hdomLog0 :
      ∀ a : ℂ, quadratic c a = a →
        ∀ z : ℂ, z ∈ filledJulia c →
          Tendsto
            (fun k =>
              logPotential
                (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z)
            atTop (𝓝 0))
    (hdomCrit :
      ∀ a : ℂ, quadratic c a = a → CriticalOrbitAvoidingTarget c a) :
    ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a :=
  fun a ha =>
    limitingBrolinMeasureAtSupportsJulia_of_scaling_and_boundary_potential_tendsto_zero
      (hscale a ha) (hdomLog0 a ha) (hdomCrit a ha)

/-- GAP-A support from the genuine Half A scaling law and finite Half B pressure
nonpositivity.  This is the direct #163 surface: finite-level log potentials are
eventually nonpositive on `K_c`, and the limiting domination follows without any
Julia-nullity input. -/
theorem limitingBrolinMeasureAtSupportsJulia_of_scaling_and_subseq_logPotential_nonpos
    {c a : ℂ}
    (hscale : BrolinScalingAt c a)
    (hdomLogNonpos :
      ∀ z : ℂ, z ∈ filledJulia c →
        ∀ᶠ k in atTop,
          logPotential
            (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z ≤ 0)
    (hdomCrit : CriticalOrbitAvoidingTarget c a) :
    LimitingBrolinMeasureAtSupportsJulia c a :=
  limitingBrolinMeasureAtSupportsJulia_of_scaling_of_dominated c a hscale
    (PotentialDominatedOnFilledJulia_of_subseq_logPotential_nonpos_of_criticalOrbitAvoidingTarget
      hdomLogNonpos hdomCrit)

/-- Fixed-point form of the direct finite-pressure GAP-A support route. -/
theorem forall_fixedPoint_limitingBrolinMeasureAtSupportsJulia_of_scaling_and_subseq_logPotential_nonpos
    {c : ℂ}
    (hscale : ∀ a : ℂ, quadratic c a = a → BrolinScalingAt c a)
    (hdomLogNonpos :
      ∀ a : ℂ, quadratic c a = a →
        ∀ z : ℂ, z ∈ filledJulia c →
          ∀ᶠ k in atTop,
            logPotential
              (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z ≤ 0)
    (hdomCrit :
      ∀ a : ℂ, quadratic c a = a → CriticalOrbitAvoidingTarget c a) :
    ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a :=
  fun a ha =>
    limitingBrolinMeasureAtSupportsJulia_of_scaling_and_subseq_logPotential_nonpos
      (hscale a ha) (hdomLogNonpos a ha) (hdomCrit a ha)

/-- Full GAP-A support route in the current sharp formal form.  Half A is the
adjacent shifted/full-limit convergence gate; Half B is finite log-potential
nonpositivity pushed through the weak limit.  No Julia-nullity input appears. -/
theorem limitingBrolinMeasureAtSupportsJulia_of_adjacent_shift_and_subseq_logPotential_nonpos
    {c a : ℂ}
    (hshift :
      ∀ φ : C_c(ℂ, ℝ),
        Tendsto
          (fun k =>
            ∫ z, φ (quadratic c z)
              ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k + 1))
          atTop
          (𝓝 (∫ z, φ (quadratic c z) ∂limitingBrolinMeasureAt c a)))
    (hlogNonpos :
      ∀ z : ℂ, z ∈ filledJulia c →
        ∀ᶠ k in atTop,
          logPotential
            (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z ≤ 0)
    (hcrit : CriticalOrbitAvoidingTarget c a) :
    LimitingBrolinMeasureAtSupportsJulia c a :=
  let hatom : ∀ z : ℂ, z ∈ filledJulia c → limitingBrolinMeasureAt c a {z} = 0 :=
    fun z hzK =>
      limitingBrolinMeasureAt_singleton_eq_zero_of_subseq_logPotential_nonpos_of_criticalOrbitAvoidingTarget
        hzK (hlogNonpos z hzK) hcrit
  limitingBrolinMeasureAtSupportsJulia_of_scaling_and_subseq_logPotential_nonpos
    (BrolinScalingAt_of_adjacent_subseq_comp_quadratic_tendsto hshift hatom)
    hlogNonpos hcrit

/-- Fixed-point form of the full GAP-A support route. -/
theorem forall_fixedPoint_limitingBrolinMeasureAtSupportsJulia_of_adjacent_shift_and_subseq_logPotential_nonpos
    {c : ℂ}
    (hshift :
      ∀ a : ℂ, quadratic c a = a →
        ∀ φ : C_c(ℂ, ℝ),
          Tendsto
            (fun k =>
              ∫ z, φ (quadratic c z)
                ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k + 1))
            atTop
            (𝓝 (∫ z, φ (quadratic c z) ∂limitingBrolinMeasureAt c a)))
    (hlogNonpos :
      ∀ a : ℂ, quadratic c a = a →
        ∀ z : ℂ, z ∈ filledJulia c →
          ∀ᶠ k in atTop,
            logPotential
              (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z ≤ 0)
    (hcrit :
      ∀ a : ℂ, quadratic c a = a → CriticalOrbitAvoidingTarget c a) :
    ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a :=
  fun a ha =>
    limitingBrolinMeasureAtSupportsJulia_of_adjacent_shift_and_subseq_logPotential_nonpos
      (hshift a ha) (hlogNonpos a ha) (hcrit a ha)

/-- GAP-A support from the finite Half A and Half B gates in subsequence form.
This statement contains no Julia-nullity input: Half A is the adjacent-limit
promotion of finite scaling, and Half B is the finite pressure/Fatou promotion
of boundary domination; critical-orbit avoidance discharges the finite singleton
mass decay. -/
theorem limitingBrolinMeasureAtSupportsJulia_of_subseq_scaling_and_boundary_potential_tendsto_zero
    {c a : ℂ}
    (hscaleLeft :
      ∀ z : ℂ, z ∈ filledJulia c →
        Tendsto
          (fun k =>
            - logPotential
              (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k))
              (quadratic c z))
          atTop
          (𝓝 (- logPotential (limitingBrolinMeasureAt c a) (quadratic c z))))
    (hscaleRight :
      ∀ z : ℂ, z ∈ filledJulia c →
        Tendsto
          (fun k =>
            - logPotential
              (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k + 1)) z)
          atTop
          (𝓝 (- logPotential (limitingBrolinMeasureAt c a) z)))
    (hscaleNotAtom :
      ∀ z : ℂ, z ∈ filledJulia c →
        ∀ᶠ k in atTop,
          (quadratic c)^[brolinLimitAtSubsequence c a k + 1] z - a ≠ 0)
    (hdomLog0 :
      ∀ z : ℂ, z ∈ filledJulia c →
        Tendsto
          (fun k =>
            logPotential
              (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z)
          atTop (𝓝 0))
    (hdomCrit : CriticalOrbitAvoidingTarget c a) :
    LimitingBrolinMeasureAtSupportsJulia c a :=
  limitingBrolinMeasureAtSupportsJulia_of_scaling_of_dominated c a
    (BrolinScalingAt_of_adjacent_subseq_potential_tendsto
      hscaleLeft hscaleRight hscaleNotAtom)
    (PotentialDominatedOnFilledJulia_of_subseq_boundary_potential_tendsto_zero_of_criticalOrbitAvoidingTarget
      hdomLog0 hdomCrit)

/-- Fixed-point q62 support surface from the finite Half A/Half B subsequence
gates.  This is the form consumed by the q62 Brolin/backward-orbit capstones. -/
theorem forall_fixedPoint_limitingBrolinMeasureAtSupportsJulia_of_subseq_scaling_and_boundary_potential_tendsto_zero
    {c : ℂ}
    (hscaleLeft :
      ∀ a : ℂ, quadratic c a = a →
        ∀ z : ℂ, z ∈ filledJulia c →
          Tendsto
            (fun k =>
              - logPotential
                (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k))
                (quadratic c z))
            atTop
            (𝓝 (- logPotential (limitingBrolinMeasureAt c a) (quadratic c z))))
    (hscaleRight :
      ∀ a : ℂ, quadratic c a = a →
        ∀ z : ℂ, z ∈ filledJulia c →
          Tendsto
            (fun k =>
              - logPotential
                (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k + 1)) z)
            atTop
            (𝓝 (- logPotential (limitingBrolinMeasureAt c a) z)))
    (hscaleNotAtom :
      ∀ a : ℂ, quadratic c a = a →
        ∀ z : ℂ, z ∈ filledJulia c →
          ∀ᶠ k in atTop,
            (quadratic c)^[brolinLimitAtSubsequence c a k + 1] z - a ≠ 0)
    (hdomLog0 :
      ∀ a : ℂ, quadratic c a = a →
        ∀ z : ℂ, z ∈ filledJulia c →
          Tendsto
            (fun k =>
              logPotential
                (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z)
            atTop (𝓝 0))
    (hdomCrit :
      ∀ a : ℂ, quadratic c a = a →
        CriticalOrbitAvoidingTarget c a) :
    ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a :=
  fun a ha =>
    limitingBrolinMeasureAtSupportsJulia_of_subseq_scaling_and_boundary_potential_tendsto_zero
      (hscaleLeft a ha) (hscaleRight a ha) (hscaleNotAtom a ha)
      (hdomLog0 a ha) (hdomCrit a ha)

/-- Disconnected GAP-A support from the precise remaining shifted-potential identification.
This isolates the obstruction: promote the selected target limit to the canonical shifted
boundary potential, and the support theorem follows without any volume-zero input. -/
theorem limitingBrolinMeasureAtSupportsJulia_of_target_potential_eq_gapAMu_and_shifted
    {c a : ℂ} (hc : Disconnected c)
    (hquad :
      ∀ z : ℂ, z ∈ filledJulia c →
        logPotential (limitingBrolinMeasureAt c a) (quadratic c z) =
          logPotential (gapAMu c) (quadratic c z))
    (hbase :
      ∀ z : ℂ, z ∈ filledJulia c →
        logPotential (limitingBrolinMeasureAt c a) z =
          logPotential (shiftedLimitingBrolinMeasure c) z) :
    LimitingBrolinMeasureAtSupportsJulia c a :=
  limitingBrolinMeasureAtSupportsJulia_of_scaling_of_dominated c a
    (BrolinScalingAt_of_target_potential_eq_gapAMu_and_shifted hc hquad hbase)
    (PotentialDominatedOnFilledJulia_of_target_potential_eq_shifted hc hbase)

/-- Fixed-point q62 support surface from the same shifted-potential identification. -/
theorem forall_fixedPoint_limitingBrolinMeasureAtSupportsJulia_of_target_potential_eq_gapAMu_and_shifted
    {c : ℂ} (hc : Disconnected c)
    (hquad :
      ∀ a : ℂ, quadratic c a = a →
        ∀ z : ℂ, z ∈ filledJulia c →
          logPotential (limitingBrolinMeasureAt c a) (quadratic c z) =
            logPotential (gapAMu c) (quadratic c z))
    (hbase :
      ∀ a : ℂ, quadratic c a = a →
        ∀ z : ℂ, z ∈ filledJulia c →
          logPotential (limitingBrolinMeasureAt c a) z =
            logPotential (shiftedLimitingBrolinMeasure c) z) :
    ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a :=
  fun a ha =>
    limitingBrolinMeasureAtSupportsJulia_of_target_potential_eq_gapAMu_and_shifted
      hc (hquad a ha) (hbase a ha)

/-- `∀`-fixed-point form of the two-half support datum, consumed by the q62 both-connected
capstones. -/
theorem forall_fixedPoint_limitingBrolinMeasureAtSupportsJulia_of_scaling_of_dominated
    (c : ℂ) (hscale : ∀ a : ℂ, quadratic c a = a → BrolinScalingAt c a)
    (hdom : ∀ a : ℂ, quadratic c a = a → PotentialDominatedOnFilledJulia c a) :
    ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a :=
  fun a ha => limitingBrolinMeasureAtSupportsJulia_of_scaling_of_dominated c a (hscale a ha) (hdom a ha)

end

end Bottcher
