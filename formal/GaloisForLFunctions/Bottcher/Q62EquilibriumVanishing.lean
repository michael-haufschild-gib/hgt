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

open MeasureTheory Complex Filter Metric Set Topology

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

/-- GAP-A bridge for Half B in the arbitrary-target subsequence language.  The
finite pressure estimate is supplied by
`integral_truncatedLogKernel_preBrolinMeasureAt_le_logPotential_of_iterate_ne_target`;
the hypotheses here are the exact remaining boundary value and atom gates needed
to pass it through the selected weak limit. -/
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
    (hnotAtom :
      ∀ z : ℂ, z ∈ filledJulia c →
        ∀ᶠ k in atTop,
          (quadratic c)^[brolinLimitAtSubsequence c a k] z - a ≠ 0) :
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
        integral_truncatedLogKernel_limitingBrolinMeasureAt_nonpos_of_subseq_boundary_potential_tendsto_zero
          (c := c) (a := a) (z := z) (hlog0 z hzK) (hnotAtom z hzK)
          (by positivity)
    exact le_of_tendsto hlim (Filter.Eventually.of_forall hnonpos)
  · have hzero : logPotential (limitingBrolinMeasureAt c a) z = 0 := by
      unfold logPotential
      exact integral_undef hint
    rw [hzero]

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

/-- GAP-A support from the finite Half A and Half B gates in subsequence form.
This statement contains no Julia-nullity input: Half A is the adjacent-limit
promotion of finite scaling, and Half B is the finite pressure/Fatou promotion
of boundary domination. -/
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
    (hdomAtom :
      ∀ z : ℂ, z ∈ filledJulia c → limitingBrolinMeasureAt c a {z} = 0)
    (hdomLog0 :
      ∀ z : ℂ, z ∈ filledJulia c →
        Tendsto
          (fun k =>
            logPotential
              (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z)
          atTop (𝓝 0))
    (hdomNotAtom :
      ∀ z : ℂ, z ∈ filledJulia c →
        ∀ᶠ k in atTop,
          (quadratic c)^[brolinLimitAtSubsequence c a k] z - a ≠ 0) :
    LimitingBrolinMeasureAtSupportsJulia c a :=
  limitingBrolinMeasureAtSupportsJulia_of_scaling_of_dominated c a
    (BrolinScalingAt_of_adjacent_subseq_potential_tendsto
      hscaleLeft hscaleRight hscaleNotAtom)
    (PotentialDominatedOnFilledJulia_of_subseq_boundary_potential_tendsto_zero
      hdomAtom hdomLog0 hdomNotAtom)

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
    (hdomAtom :
      ∀ a : ℂ, quadratic c a = a →
        ∀ z : ℂ, z ∈ filledJulia c → limitingBrolinMeasureAt c a {z} = 0)
    (hdomLog0 :
      ∀ a : ℂ, quadratic c a = a →
        ∀ z : ℂ, z ∈ filledJulia c →
          Tendsto
            (fun k =>
              logPotential
                (preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)) z)
            atTop (𝓝 0))
    (hdomNotAtom :
      ∀ a : ℂ, quadratic c a = a →
        ∀ z : ℂ, z ∈ filledJulia c →
          ∀ᶠ k in atTop,
            (quadratic c)^[brolinLimitAtSubsequence c a k] z - a ≠ 0) :
    ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a :=
  fun a ha =>
    limitingBrolinMeasureAtSupportsJulia_of_subseq_scaling_and_boundary_potential_tendsto_zero
      (hscaleLeft a ha) (hscaleRight a ha) (hscaleNotAtom a ha)
      (hdomAtom a ha) (hdomLog0 a ha) (hdomNotAtom a ha)

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
