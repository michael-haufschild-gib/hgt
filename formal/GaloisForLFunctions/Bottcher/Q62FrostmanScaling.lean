/-
# q62 — Frostman domination from mere boundedness (the self-similar Robin constant)

GAP-A Half B for the both-connected case is `PotentialDominatedOnFilledJulia c a`, i.e. the exact
inequality `Uᵘ ≤ 0` on `K_c` (Robin constant `= 0`).  This file proves that the **exact value `0`**
is not extra content: given the doubling law `Uᵘ∘f = 2·Uᵘ` on `K_c` (Half A, `BrolinScalingAt`), the
domination `Uᵘ ≤ 0` follows from `Uᵘ` being bounded ABOVE on `K_c` by *any* constant.  The
self-similarity fixes the Robin constant at `0` for free.

This is the exact mirror of the tree's `neg_logPotential_gapAMu_nonpos_of_boundary_scaling`
(`Brolin/BoundaryCriteria`), which gives the *lower* bound `Uᵘ ≥ 0` on `K_c` from the elementary
*upper* bound on `−Uᵘ` (`neg_logPotential_..._upper_bound_of_mem_filledJulia`, `Uᵘ ≥ −log(2·max 2‖c‖)`).
Together they read: on `K_c`, `Uᵘ` is bounded below unconditionally, and `Uᵘ` bounded above ⟹ `Uᵘ = 0`.

**Net effect on the both-connected q62 support datum.**  The consumer needs
`LimitingBrolinMeasureAtSupportsJulia c a`, discharged by the tree from
`BrolinScalingAt × PotentialDominatedOnFilledJulia`.  Here the domination hypothesis is *weakened*
from the exact `Uᵘ ≤ 0` to mere upper-boundedness `Uᵘ ≤ C` — the genuine remaining potential-theoretic
input is now only "the equilibrium potential does not blow up to `+∞` on `K_c`" (a finiteness /
continuity statement), with the Robin-constant value discharged by the dynamics.
-/
import GaloisForLFunctions.Bottcher.Q62EquilibriumVanishing
import GaloisForLFunctions.Bottcher.Q62FrostmanDomination

open MeasureTheory Complex Filter Topology Metric

namespace Bottcher

noncomputable section

/-- **Frostman domination from boundedness + scaling.**  If the target-`a` Brolin potential is
bounded above on `K_c` by any constant `C` and obeys the doubling law `BrolinScalingAt`, then it is
`≤ 0` on `K_c`.  Proof: if `Uᵘ(z) > 0` for some `z ∈ K_c`, the doubling law gives
`Uᵘ(fⁿz) = 2ⁿ·Uᵘ(z) → +∞` with `fⁿz ∈ K_c`, contradicting the upper bound `C`.  The exact Robin
constant `0` is fixed by self-similarity, not assumed. -/
theorem potentialDominatedOnFilledJulia_of_scaling_of_bddAbove (c a : ℂ)
    (hscale : BrolinScalingAt c a)
    {C : ℝ} (hbdd : ∀ z ∈ filledJulia c, logPotential (limitingBrolinMeasureAt c a) z ≤ C) :
    PotentialDominatedOnFilledJulia c a := by
  intro z hzK
  by_contra hcon
  have hpos : 0 < logPotential (limitingBrolinMeasureAt c a) z := not_le.mp hcon
  set μ := limitingBrolinMeasureAt c a with hμ
  set A : ℕ → ℝ := fun n => logPotential μ ((quadratic c)^[n] z) with hAdef
  have hA : ∀ n : ℕ, A n = (2 ^ n : ℝ) * logPotential μ z := by
    intro n
    induction n with
    | zero => simp [hAdef]
    | succ n ih =>
        have hnK : (quadratic c)^[n] z ∈ filledJulia c := filledJulia_forward hzK n
        have hs := hscale ((quadratic c)^[n] z) hnK
        calc
          A (n + 1) = logPotential μ (quadratic c ((quadratic c)^[n] z)) := by
                simp [hAdef, Function.iterate_succ_apply']
          _ = 2 * logPotential μ ((quadratic c)^[n] z) := by
                have hs2 : -logPotential μ (quadratic c ((quadratic c)^[n] z))
                    = 2 * (-logPotential μ ((quadratic c)^[n] z)) := hs
                linarith
          _ = 2 * A n := by simp [hAdef]
          _ = (2 ^ (n + 1) : ℝ) * logPotential μ z := by rw [ih, pow_succ]; ring
  have htend : Tendsto (fun n : ℕ => (2 ^ n : ℝ) * logPotential μ z) atTop atTop := by
    simpa [mul_comm] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_mul_atTop hpos
  rcases (eventually_atTop.1 (htend.eventually_gt_atTop C)) with ⟨N, hN⟩
  have hNK : (quadratic c)^[N] z ∈ filledJulia c := filledJulia_forward hzK N
  have hbound : A N ≤ C := hbdd _ hNK
  have hgt : C < A N := by simpa [hA N] using hN N le_rfl
  exact not_lt_of_ge hbound hgt

/-- **Both-connected support datum from scaling + boundedness.**  Composes the Frostman-from-
boundedness lemma with the tree's two-halves assembly: `LimitingBrolinMeasureAtSupportsJulia c a`
holds as soon as the doubling law holds and the target-`a` Brolin potential is bounded above on
`K_c`.  The Robin-constant-`0` domination (`PotentialDominatedOnFilledJulia`) is no longer a separate
input — mere upper-boundedness suffices. -/
theorem limitingBrolinMeasureAtSupportsJulia_of_scaling_of_bddAbove (c a : ℂ)
    (hscale : BrolinScalingAt c a)
    {C : ℝ} (hbdd : ∀ z ∈ filledJulia c, logPotential (limitingBrolinMeasureAt c a) z ≤ C) :
    LimitingBrolinMeasureAtSupportsJulia c a :=
  limitingBrolinMeasureAtSupportsJulia_of_scaling_of_dominated c a hscale
    (potentialDominatedOnFilledJulia_of_scaling_of_bddAbove c a hscale hbdd)

/-! ### Localizing the boundedness to the orbit's limit — reduction to pure basin dynamics

The uniform bound above can be replaced by a *local* bound at whatever point the orbit converges to,
because the doubling law `U(fⁿz) = 2ⁿU(z)` only needs `U(fⁿz)` bounded *eventually*.  For a Fatou
point `p` (an attracting-cycle point) the potential is bounded near `p` for the elementary reason
that `p` lies at positive distance from the Brolin carrier `J_c`, so the log-kernel `−log‖·−ζ‖` is
bounded there.  This discharges *all* the potential theory and leaves only the dynamical fact that
`K_c` orbits converge into the Fatou set — the hyperbolic-basin input. -/

/-- **Potential bound away from the carrier.**  If, `μ`-a.e., the kernel argument keeps `‖w − ζ‖` in
an annulus `[r, M]` (`0 < r`), then `Uᵘ(w) ≤ −log r`.  Elementary: on the carrier the log-kernel is
bounded, and `‖w − ζ‖ ≥ r ⟹ −log‖w − ζ‖ ≤ −log r`. -/
theorem logPotential_le_of_ae_norm_mem_Icc {μ : Measure ℂ} [IsProbabilityMeasure μ] {w : ℂ}
    {r M : ℝ} (hr : 0 < r) (hae : ∀ᵐ ζ ∂μ, ‖w - ζ‖ ∈ Set.Icc r M) :
    logPotential μ w ≤ - Real.log r := by
  have hbdd : ∀ᵐ ζ ∂μ, ‖logKernel w ζ‖ ≤ |Real.log r| + |Real.log M| := by
    filter_upwards [hae] with ζ hζ
    obtain ⟨h1, h2⟩ := hζ
    have hpos : 0 < ‖w - ζ‖ := lt_of_lt_of_le hr h1
    have hlog : |Real.log ‖w - ζ‖| ≤ |Real.log r| + |Real.log M| := by
      rcases le_total (Real.log ‖w - ζ‖) 0 with hle | hle
      · rw [abs_of_nonpos hle]
        have hlr : |Real.log r| = - Real.log r := by
          rw [abs_of_nonpos (le_trans (Real.log_le_log hr h1) hle)]
        rw [hlr]; nlinarith [abs_nonneg (Real.log M), Real.log_le_log hr h1]
      · have hM' : Real.log ‖w - ζ‖ ≤ Real.log M := Real.log_le_log hpos h2
        rw [abs_of_nonneg hle]
        have hlM : |Real.log M| = Real.log M := abs_of_nonneg (le_trans hle hM')
        rw [hlM]; nlinarith [abs_nonneg (Real.log r), hM']
    simpa [logKernel, Real.norm_eq_abs, abs_neg] using hlog
  have hint : Integrable (fun ζ => logKernel w ζ) μ :=
    Integrable.mono' (integrable_const (|Real.log r| + |Real.log M|))
      (logKernel_aestronglyMeasurable w μ) hbdd
  have hle : logPotential μ w ≤ ∫ _ζ, (- Real.log r) ∂μ := by
    rw [logPotential]
    refine integral_mono_ae hint (integrable_const _) ?_
    filter_upwards [hae] with ζ hζ
    obtain ⟨h1, _⟩ := hζ
    have : Real.log r ≤ Real.log ‖w - ζ‖ := Real.log_le_log hr h1
    simp only [logKernel]; linarith
  simpa using hle

/-- **Localized Frostman domination.**  If the orbit of `z ∈ K_c` converges to a point `p` near which
the Brolin potential is bounded above by `C`, then `Uᵘ(z) ≤ 0`.  Doubling forces `U(fⁿz) = 2ⁿU(z)`;
the orbit eventually enters the neighbourhood where `U ≤ C`, so `2ⁿU(z) ≤ C` eventually, whence
`U(z) ≤ 0` — otherwise `2ⁿU(z) → +∞`. -/
theorem potentialNonpos_of_orbit_tendsto_of_bddAbove_nhds (c a z p : ℂ)
    (hscale : BrolinScalingAt c a) (hzK : z ∈ filledJulia c)
    (horbit : Tendsto (fun n => (quadratic c)^[n] z) atTop (𝓝 p))
    {C ε : ℝ} (hε : 0 < ε)
    (hbdd : ∀ w ∈ Metric.ball p ε, logPotential (limitingBrolinMeasureAt c a) w ≤ C) :
    logPotential (limitingBrolinMeasureAt c a) z ≤ 0 := by
  set μ := limitingBrolinMeasureAt c a with hμ
  set A : ℕ → ℝ := fun n => logPotential μ ((quadratic c)^[n] z) with hAdef
  have hA : ∀ n : ℕ, A n = (2 ^ n : ℝ) * logPotential μ z := by
    intro n
    induction n with
    | zero => simp [hAdef]
    | succ n ih =>
        have hnK : (quadratic c)^[n] z ∈ filledJulia c := filledJulia_forward hzK n
        have hs := hscale ((quadratic c)^[n] z) hnK
        calc
          A (n + 1) = logPotential μ (quadratic c ((quadratic c)^[n] z)) := by
                simp [hAdef, Function.iterate_succ_apply']
          _ = 2 * logPotential μ ((quadratic c)^[n] z) := by
                have hs2 : -logPotential μ (quadratic c ((quadratic c)^[n] z))
                    = 2 * (-logPotential μ ((quadratic c)^[n] z)) := hs
                linarith
          _ = 2 * A n := by simp [hAdef]
          _ = (2 ^ (n + 1) : ℝ) * logPotential μ z := by rw [ih, pow_succ]; ring
  have hev : ∀ᶠ n in atTop, A n ≤ C := by
    have hmem : ∀ᶠ n in atTop, (quadratic c)^[n] z ∈ Metric.ball p ε :=
      horbit (Metric.ball_mem_nhds p hε)
    filter_upwards [hmem] with n hn
    exact hbdd _ hn
  by_contra hcon
  have hpos : 0 < logPotential μ z := not_le.mp hcon
  have htend : Tendsto (fun n : ℕ => (2 ^ n : ℝ) * logPotential μ z) atTop atTop := by
    simpa [mul_comm] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_mul_atTop hpos
  have htendA : Tendsto A atTop atTop := htend.congr (fun n => (hA n).symm)
  rcases ((htendA.eventually_gt_atTop C).and hev).exists with ⟨n, hgt, hle⟩
  exact absurd hle (not_le.mpr hgt)

/-- **Frostman domination reduced to interior basin dynamics.**  Splitting `K_c` into its frontier
`J_c` and interior: on `J_c` domination is unconditional (`logPotential_..._nonpos_of_mem_frontier`);
on the interior it follows from `potentialNonpos_of_orbit_tendsto_of_bddAbove_nhds` once every interior
point's orbit converges to a Fatou point `p` off the Brolin carrier (annulus condition).  So the whole
Frostman maximum principle for positive-area `K_c` reduces to the interior orbits' basin convergence. -/
theorem potentialDominatedOnFilledJulia_of_interior_orbits_offCarrier (c a : ℂ)
    (hscale : BrolinScalingAt c a)
    (hdyn : ∀ z ∈ interior (filledJulia c), ∃ (p : ℂ) (ε M : ℝ), 0 < ε ∧
      Tendsto (fun n => (quadratic c)^[n] z) atTop (𝓝 p) ∧
      ∀ w ∈ Metric.ball p ε, ∀ᵐ ζ ∂(limitingBrolinMeasureAt c a), ‖w - ζ‖ ∈ Set.Icc ε M) :
    PotentialDominatedOnFilledJulia c a := by
  intro z hzK
  by_cases hz : z ∈ frontier (filledJulia c)
  · exact logPotential_limitingBrolinMeasureAt_nonpos_of_mem_frontier hz
  · have hzint : z ∈ interior (filledJulia c) := by
      by_contra hint
      exact hz ⟨subset_closure hzK, hint⟩
    obtain ⟨p, ε, M, hε, horbit, hann⟩ := hdyn z hzint
    exact potentialNonpos_of_orbit_tendsto_of_bddAbove_nhds c a z p hscale hzK horbit hε
      (fun w hw => logPotential_le_of_ae_norm_mem_Icc hε (hann w hw))

/-- **Both-connected support datum reduced to pure basin dynamics.**  Given the doubling law, the
support datum `LimitingBrolinMeasureAtSupportsJulia c a` for a positive-area `K_c` follows once every
*interior* point's orbit converges to a Fatou point off `J_c` (the annulus/off-carrier condition).
All the potential theory — the Frostman maximum principle and the Robin-constant value `0`, on both
`J_c` (via the tree) and the interior (via self-similarity + local boundedness) — is discharged; the
sole remaining input is the hyperbolic-basin convergence of the interior dynamics. -/
theorem limitingBrolinMeasureAtSupportsJulia_of_interior_orbits_offCarrier (c a : ℂ)
    (hscale : BrolinScalingAt c a)
    (hdyn : ∀ z ∈ interior (filledJulia c), ∃ (p : ℂ) (ε M : ℝ), 0 < ε ∧
      Tendsto (fun n => (quadratic c)^[n] z) atTop (𝓝 p) ∧
      ∀ w ∈ Metric.ball p ε, ∀ᵐ ζ ∂(limitingBrolinMeasureAt c a), ‖w - ζ‖ ∈ Set.Icc ε M) :
    LimitingBrolinMeasureAtSupportsJulia c a :=
  limitingBrolinMeasureAtSupportsJulia_of_scaling_of_dominated c a hscale
    (potentialDominatedOnFilledJulia_of_interior_orbits_offCarrier c a hscale hdyn)

end

end Bottcher
