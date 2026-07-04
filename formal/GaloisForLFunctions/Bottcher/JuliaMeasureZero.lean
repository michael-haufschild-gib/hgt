/-
# Lebesgue-null disconnected filled Julia sets

This file builds the local infrastructure for the disconnected quadratic
filled-Julia nullity theorem.  The first reusable layer is the standard
backward-trapping escape disk and the named nested-preimage characterization.
-/
import GaloisForLFunctions.Bottcher.Dynamics
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal Topology

namespace Bottcher

noncomputable section

/-- The standard escape radius for `f_c(z)=z^2+c`. -/
def quadraticEscapeRadius (c : ℂ) : ℝ := max 2 ‖c‖

/-- The standard closed escape disk is backward-trapping for the quadratic map. -/
theorem quadratic_preimage_closedBall_subset (c : ℂ) :
    (quadratic c) ⁻¹' Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c) ⊆
      Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c) := by
  intro z hz
  change quadratic c z ∈ Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c) at hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz ⊢
  have htri : ‖z‖ ^ 2 ≤ ‖quadratic c z‖ + ‖c‖ := by
    have hsub : ‖(z ^ 2 + c) - c‖ ≤ ‖z ^ 2 + c‖ + ‖c‖ := norm_sub_le (z ^ 2 + c) c
    have hnorm : ‖(z ^ 2 + c) - c‖ = ‖z‖ ^ 2 := by
      rw [show (z ^ 2 + c) - c = z ^ 2 by ring, norm_pow]
    rw [quadratic_apply]
    rwa [hnorm] at hsub
  have hR2 : quadraticEscapeRadius c + ‖c‖ ≤ (quadraticEscapeRadius c) ^ 2 := by
    unfold quadraticEscapeRadius
    by_cases h : ‖c‖ ≤ 2
    · have hmax : max (2 : ℝ) ‖c‖ = 2 := max_eq_left h
      rw [hmax]
      nlinarith [norm_nonneg c, h]
    · have hc2 : 2 ≤ ‖c‖ := le_of_not_ge h
      have hmax : max (2 : ℝ) ‖c‖ = ‖c‖ := max_eq_right hc2
      rw [hmax]
      nlinarith [norm_nonneg c, hc2]
  have hzsq : ‖z‖ ^ 2 ≤ (quadraticEscapeRadius c) ^ 2 := by
    have htri2 : ‖quadratic c z‖ + ‖c‖ ≤ quadraticEscapeRadius c + ‖c‖ := by
      nlinarith [hz]
    exact le_trans htri (le_trans htri2 hR2)
  have hRnonneg : 0 ≤ quadraticEscapeRadius c := by
    unfold quadraticEscapeRadius
    exact le_trans (by norm_num) (le_max_left (2 : ℝ) ‖c‖)
  nlinarith [hzsq, norm_nonneg z, hRnonneg]

/-- `K_c` as the nested intersection of inverse images of the standard closed escape disk. -/
theorem filledJulia_eq_iInter_preimage_closedBall (c : ℂ) :
    filledJulia c =
      ⋂ n : ℕ, (fun z => (quadratic c)^[n] z) ⁻¹'
        Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c) := by
  simpa [quadraticEscapeRadius] using filledJulia_eq_iInter c

/-- The `n`th pullback of the standard closed escape disk. -/
def quadraticPreimageClosedBall (c : ℂ) (n : ℕ) : Set ℂ :=
  (fun z => (quadratic c)^[n] z) ⁻¹' Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c)

theorem quadraticPreimageClosedBall_zero (c : ℂ) :
    quadraticPreimageClosedBall c 0 = Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c) := by
  ext z
  simp [quadraticPreimageClosedBall]

/-- The pullbacks of the trapping disk form a decreasing sequence. -/
theorem quadraticPreimageClosedBall_succ_subset (c : ℂ) (n : ℕ) :
    quadraticPreimageClosedBall c (n + 1) ⊆ quadraticPreimageClosedBall c n := by
  intro z hz
  change (quadratic c)^[n] z ∈ Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c)
  change (quadratic c)^[n + 1] z ∈ Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c) at hz
  rw [Function.iterate_succ' (quadratic c) n, Function.comp_apply] at hz
  exact quadratic_preimage_closedBall_subset c hz

/-- The next trapping-disk pullback is the quadratic preimage of the previous one. -/
theorem quadraticPreimageClosedBall_succ_eq_preimage (c : ℂ) (n : ℕ) :
    quadraticPreimageClosedBall c (n + 1) =
      (quadratic c) ⁻¹' quadraticPreimageClosedBall c n := by
  ext z
  simp [quadraticPreimageClosedBall]

/-- Antitone form of `quadraticPreimageClosedBall_succ_subset`. -/
theorem antitone_quadraticPreimageClosedBall (c : ℂ) :
    Antitone (quadraticPreimageClosedBall c) :=
  antitone_nat_of_succ_le (fun n =>
    show quadraticPreimageClosedBall c (n + 1) ≤ quadraticPreimageClosedBall c n from
      quadraticPreimageClosedBall_succ_subset c n)

/-- Each trapping-disk pullback is closed. -/
theorem isClosed_quadraticPreimageClosedBall (c : ℂ) (n : ℕ) :
    IsClosed (quadraticPreimageClosedBall c n) := by
  dsimp [quadraticPreimageClosedBall]
  exact isClosed_closedBall.preimage ((continuous_quadratic c).iterate n)

theorem measurableSet_quadraticPreimageClosedBall (c : ℂ) (n : ℕ) :
    MeasurableSet (quadraticPreimageClosedBall c n) := by
  exact (isClosed_quadraticPreimageClosedBall c n).measurableSet

/-- Every pullback of the trapping disk is still contained in the original trapping disk. -/
theorem quadraticPreimageClosedBall_subset_closedBall (c : ℂ) (n : ℕ) :
    quadraticPreimageClosedBall c n ⊆ Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c) := by
  simpa [quadraticPreimageClosedBall_zero] using
    (antitone_quadraticPreimageClosedBall c (Nat.zero_le n))

theorem volume_quadraticPreimageClosedBall_lt_top (c : ℂ) (n : ℕ) :
    volume (quadraticPreimageClosedBall c n) < ⊤ := by
  exact lt_of_le_of_lt (measure_mono (quadraticPreimageClosedBall_subset_closedBall c n))
    ((isCompact_closedBall (0 : ℂ) (quadraticEscapeRadius c)).measure_lt_top)

theorem filledJulia_subset_quadraticPreimageClosedBall (c : ℂ) (n : ℕ) :
    filledJulia c ⊆ quadraticPreimageClosedBall c n := by
  rw [filledJulia_eq_iInter_preimage_closedBall]
  exact Set.iInter_subset (fun n : ℕ => (fun z => (quadratic c)^[n] z) ⁻¹'
    Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c)) n

theorem volume_filledJulia_le_quadraticPreimageClosedBall (c : ℂ) (n : ℕ) :
    volume (filledJulia c) ≤ volume (quadraticPreimageClosedBall c n) :=
  measure_mono (filledJulia_subset_quadraticPreimageClosedBall c n)

/-- Continuity from above for the decreasing pullbacks of the trapping disk. -/
theorem volume_filledJulia_eq_iInf_quadraticPreimageClosedBall (c : ℂ) :
    volume (filledJulia c) = ⨅ n : ℕ, volume (quadraticPreimageClosedBall c n) := by
  rw [filledJulia_eq_iInter_preimage_closedBall]
  change volume (⋂ n : ℕ, quadraticPreimageClosedBall c n) =
    ⨅ n : ℕ, volume (quadraticPreimageClosedBall c n)
  exact (antitone_quadraticPreimageClosedBall c).measure_iInter
    (fun n => (measurableSet_quadraticPreimageClosedBall c n).nullMeasurableSet)
    ⟨0, ne_of_lt (volume_quadraticPreimageClosedBall_lt_top c 0)⟩

/-- It suffices to prove that the trapping-disk pullback volumes tend to zero. -/
theorem volume_filledJulia_eq_zero_of_tendsto_preimage_closedBall_zero {c : ℂ}
    (hlim : Tendsto (fun n : ℕ => volume (quadraticPreimageClosedBall c n)) atTop (𝓝 0)) :
    volume (filledJulia c) = 0 := by
  have hle : (fun _ : ℕ => volume (filledJulia c)) ≤ᶠ[atTop]
      fun n : ℕ => volume (quadraticPreimageClosedBall c n) :=
    Filter.Eventually.of_forall (volume_filledJulia_le_quadraticPreimageClosedBall c)
  exact le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds hlim hle) bot_le

/-- A finite geometrically decaying `ℝ≥0∞` sequence tends to zero. -/
lemma tendsto_zero_of_geometric_bound_ennreal
    {u : ℕ → ℝ≥0∞} {q : ℝ≥0∞} (hq : q < 1) (hu0 : u 0 < ⊤)
    (hdecay : ∀ n : ℕ, u (n + 1) ≤ q * u n) :
    Tendsto u atTop (𝓝 0) := by
  have hbound : ∀ n : ℕ, u n ≤ q ^ n * u 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        u (n + 1) ≤ q * u n := hdecay n
        _ ≤ q * (q ^ n * u 0) := mul_le_mul_right ih q
        _ = q ^ (n + 1) * u 0 := by
          rw [pow_succ', mul_assoc]
  have hqpow : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq
  have hu0_ne_top : u 0 ≠ ⊤ := ne_of_lt hu0
  have htop : (0 : ℝ≥0∞) ≠ 0 ∨ u 0 ≠ ⊤ := Or.inr hu0_ne_top
  have hmul : Tendsto (fun n : ℕ => u 0 * q ^ n) atTop (𝓝 (u 0 * 0)) :=
    ENNReal.Tendsto.const_mul hqpow htop
  have hmul0 : Tendsto (fun n : ℕ => q ^ n * u 0) atTop (𝓝 0) := by
    simpa [mul_comm] using hmul
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul0
    (fun n => bot_le) hbound

/-- Eventual finite geometric decay is enough for an `ℝ≥0∞` sequence to tend to zero. -/
lemma tendsto_zero_of_eventually_geometric_bound_ennreal
    {u : ℕ → ℝ≥0∞} {N : ℕ} {q : ℝ≥0∞} (hq : q < 1) (huN : u N < ⊤)
    (hdecay : ∀ n : ℕ, N ≤ n → u (n + 1) ≤ q * u n) :
    Tendsto u atTop (𝓝 0) := by
  have hshift : Tendsto (fun m : ℕ => u (m + N)) atTop (𝓝 0) := by
    apply tendsto_zero_of_geometric_bound_ennreal (u := fun m : ℕ => u (m + N)) hq
    · simpa using huN
    · intro m
      have hle : N ≤ m + N := by omega
      have h := hdecay (m + N) hle
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  exact (Filter.tendsto_add_atTop_iff_nat N).mp hshift

/-- A uniform geometric decay estimate for the trapping-disk pullbacks implies
`volume K_c = 0`. -/
theorem volume_filledJulia_eq_zero_of_geometric_preimage_decay {c : ℂ} {q : ℝ≥0∞}
    (hq : q < 1)
    (hdecay : ∀ n : ℕ,
      volume (quadraticPreimageClosedBall c (n + 1)) ≤
        q * volume (quadraticPreimageClosedBall c n)) :
    volume (filledJulia c) = 0 := by
  exact volume_filledJulia_eq_zero_of_tendsto_preimage_closedBall_zero
    (tendsto_zero_of_geometric_bound_ennreal hq
      (volume_quadraticPreimageClosedBall_lt_top c 0) hdecay)

/-- An eventual uniform geometric decay estimate for the trapping-disk pullbacks implies
`volume K_c = 0`. -/
theorem volume_filledJulia_eq_zero_of_eventually_geometric_preimage_decay {c : ℂ} {N : ℕ}
    {q : ℝ≥0∞} (hq : q < 1)
    (hdecay : ∀ n : ℕ, N ≤ n →
      volume (quadraticPreimageClosedBall c (n + 1)) ≤
        q * volume (quadraticPreimageClosedBall c n)) :
    volume (filledJulia c) = 0 := by
  exact volume_filledJulia_eq_zero_of_tendsto_preimage_closedBall_zero
    (tendsto_zero_of_eventually_geometric_bound_ennreal hq
      (volume_quadraticPreimageClosedBall_lt_top c N) hdecay)

/-- If the quadratic preimage area formula is available and its kernel is uniformly bounded by
`q < 1` on every trapping-disk pullback, then `K_c` is null. -/
theorem volume_filledJulia_eq_zero_of_forall_dist {c : ℂ} {q : ℝ≥0∞}
    (hq : q < 1)
    (hpreimage : ∀ A : Set ℂ, MeasurableSet A →
      volume ((quadratic c) ⁻¹' A) =
        ∫⁻ w in A, ENNReal.ofReal ((2 * ‖w - c‖)⁻¹) ∂(volume : Measure ℂ))
    (hkernel : ∀ n : ℕ, ∀ w ∈ quadraticPreimageClosedBall c n,
      ENNReal.ofReal ((2 * ‖w - c‖)⁻¹) ≤ q) :
    volume (filledJulia c) = 0 := by
  apply volume_filledJulia_eq_zero_of_geometric_preimage_decay hq
  intro n
  rw [quadraticPreimageClosedBall_succ_eq_preimage,
    hpreimage (quadraticPreimageClosedBall c n) (measurableSet_quadraticPreimageClosedBall c n)]
  calc
    ∫⁻ w in quadraticPreimageClosedBall c n,
        ENNReal.ofReal ((2 * ‖w - c‖)⁻¹) ∂(volume : Measure ℂ)
        ≤ ∫⁻ _w in quadraticPreimageClosedBall c n, q ∂(volume : Measure ℂ) := by
          exact setLIntegral_mono' (measurableSet_quadraticPreimageClosedBall c n)
            (fun w hw => hkernel n w hw)
    _ = q * volume (quadraticPreimageClosedBall c n) := by
          rw [setLIntegral_const]

/-- Tail version of `volume_filledJulia_eq_zero_of_forall_dist`: the kernel bound only needs to hold
from one pullback level onward. -/
theorem volume_filledJulia_eq_zero_of_eventually_forall_dist {c : ℂ} {N : ℕ} {q : ℝ≥0∞}
    (hq : q < 1)
    (hpreimage : ∀ A : Set ℂ, MeasurableSet A →
      volume ((quadratic c) ⁻¹' A) =
        ∫⁻ w in A, ENNReal.ofReal ((2 * ‖w - c‖)⁻¹) ∂(volume : Measure ℂ))
    (hkernel : ∀ n : ℕ, N ≤ n → ∀ w ∈ quadraticPreimageClosedBall c n,
      ENNReal.ofReal ((2 * ‖w - c‖)⁻¹) ≤ q) :
    volume (filledJulia c) = 0 := by
  apply volume_filledJulia_eq_zero_of_eventually_geometric_preimage_decay hq
  intro n hn
  rw [quadraticPreimageClosedBall_succ_eq_preimage,
    hpreimage (quadraticPreimageClosedBall c n) (measurableSet_quadraticPreimageClosedBall c n)]
  calc
    ∫⁻ w in quadraticPreimageClosedBall c n,
        ENNReal.ofReal ((2 * ‖w - c‖)⁻¹) ∂(volume : Measure ℂ)
        ≤ ∫⁻ _w in quadraticPreimageClosedBall c n, q ∂(volume : Measure ℂ) := by
          exact setLIntegral_mono' (measurableSet_quadraticPreimageClosedBall c n)
            (fun w hw => hkernel n hn w hw)
    _ = q * volume (quadraticPreimageClosedBall c n) := by
          rw [setLIntegral_const]

/-- It is enough for one trapping-disk pullback to already be null. -/
theorem volume_filledJulia_eq_zero_of_preimage_closedBall_zero {c : ℂ} {n : ℕ}
    (hzero : volume (quadraticPreimageClosedBall c n) = 0) :
    volume (filledJulia c) = 0 := by
  have hle := volume_filledJulia_le_quadraticPreimageClosedBall c n
  rw [hzero] at hle
  exact le_antisymm hle bot_le

/-- In the disconnected case, the critical value is not in `K_c`. -/
theorem criticalValue_not_mem_filledJulia_of_disconnected {c : ℂ} (hc : Disconnected c) :
    c ∉ filledJulia c := by
  have h0 : (0 : ℂ) ∉ filledJulia c := (disconnected_iff_zero_not_mem c).mp hc
  intro hcK
  exact h0 ((mem_filledJulia_iff_quadratic_mem c 0).mpr (by simpa [quadratic_apply] using hcK))

/-- In the disconnected case, some trapping-disk pullback misses a positive ball around the
critical value `c`. -/
theorem iterate_preimage_closedBall_disjoint_ball_c {c : ℂ} (hc : Disconnected c) :
    ∃ n : ℕ, ∃ r : ℝ, 0 < r ∧
      Disjoint (Metric.ball c r) (quadraticPreimageClosedBall c n) := by
  obtain ⟨n, hn⟩ := exists_orbit_gt (criticalValue_not_mem_filledJulia_of_disconnected hc)
    (quadraticEscapeRadius c)
  have hcnot : c ∉ quadraticPreimageClosedBall c n := by
    intro hcS
    change (quadratic c)^[n] c ∈ Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c) at hcS
    rw [Metric.mem_closedBall, dist_zero_right] at hcS
    linarith
  have hclosed : IsClosed (quadraticPreimageClosedBall c n) := isClosed_quadraticPreimageClosedBall c n
  have hnhds : (quadraticPreimageClosedBall c n)ᶜ ∈ nhds c :=
    hclosed.isOpen_compl.mem_nhds hcnot
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨n, r, hr, ?_⟩
  rw [Set.disjoint_left]
  intro z hzball hzS
  exact hball hzball hzS

/-- A point outside a ball around the critical value has the corresponding quadratic
preimage-area kernel bounded by the ball radius. -/
theorem quadratic_kernel_le_of_disjoint_ball_c {c w : ℂ} {r : ℝ} {q : ℝ≥0∞}
    (hr : 0 < r) (hw : w ∉ Metric.ball c r)
    (hq : ENNReal.ofReal ((2 * r)⁻¹) ≤ q) :
    ENNReal.ofReal ((2 * ‖w - c‖)⁻¹) ≤ q := by
  have hnotlt : ¬ dist w c < r := fun h => hw (Metric.mem_ball.mpr h)
  have hdist : r ≤ dist w c := le_of_not_gt hnotlt
  have hnorm : r ≤ ‖w - c‖ := by
    simpa [dist_eq_norm] using hdist
  have h2 : 2 * r ≤ 2 * ‖w - c‖ := by nlinarith
  have h2pos : 0 < 2 * r := by nlinarith
  have hinv : (2 * ‖w - c‖)⁻¹ ≤ (2 * r)⁻¹ := inv_anti₀ h2pos h2
  exact (ENNReal.ofReal_le_ofReal hinv).trans hq

/-- Setwise version of `quadratic_kernel_le_of_disjoint_ball_c` for one trapping-disk pullback. -/
theorem quadraticPreimageClosedBall_kernel_le_of_disjoint_ball_c {c : ℂ} {n : ℕ} {r : ℝ}
    {q : ℝ≥0∞} (hr : 0 < r)
    (hdisj : Disjoint (Metric.ball c r) (quadraticPreimageClosedBall c n))
    (hq : ENNReal.ofReal ((2 * r)⁻¹) ≤ q) :
    ∀ w ∈ quadraticPreimageClosedBall c n,
      ENNReal.ofReal ((2 * ‖w - c‖)⁻¹) ≤ q := by
  intro w hw
  have hwball : w ∉ Metric.ball c r := fun hwb => (Set.disjoint_left.mp hdisj hwb) hw
  exact quadratic_kernel_le_of_disjoint_ball_c hr hwball hq

/-- A separated pullback level plus the quadratic preimage area formula gives the nullity theorem,
provided the separation radius yields a contraction factor `q < 1`. -/
theorem volume_filledJulia_eq_zero_of_disjoint_ball_c
    {c : ℂ} {N : ℕ} {r : ℝ} {q : ℝ≥0∞}
    (hq : q < 1)
    (hpreimage : ∀ A : Set ℂ, MeasurableSet A →
      volume ((quadratic c) ⁻¹' A) =
        ∫⁻ w in A, ENNReal.ofReal ((2 * ‖w - c‖)⁻¹) ∂(volume : Measure ℂ))
    (hr : 0 < r)
    (hdisj : Disjoint (Metric.ball c r) (quadraticPreimageClosedBall c N))
    (hqkernel : ENNReal.ofReal ((2 * r)⁻¹) ≤ q) :
    volume (filledJulia c) = 0 := by
  apply volume_filledJulia_eq_zero_of_eventually_forall_dist hq hpreimage
  intro n hn
  exact quadraticPreimageClosedBall_kernel_le_of_disjoint_ball_c hr
    (Disjoint.mono_right (antitone_quadraticPreimageClosedBall c hn) hdisj) hqkernel

/-- `f_c(z)=z²+c` has strict complex derivative `2z`. -/
theorem quadratic_hasStrictDerivAt (c z : ℂ) :
    HasStrictDerivAt (quadratic c) (2 * z) z := by
  have h : HasStrictDerivAt (quadratic c) ((2 : ℕ) * z ^ (2 - 1)) z :=
    (hasStrictDerivAt_pow 2 z).add_const c
  convert h using 1
  norm_num

/-- Real Frechet derivative of `f_c(z)=z²+c`, viewed on the real plane. -/
theorem hasFDerivWithinAt_quadratic_real (c z : ℂ) (s : Set ℂ) :
    HasFDerivWithinAt (quadratic c) ((2 * z) • (1 : ℂ →L[ℝ] ℂ)) s z := by
  exact (quadratic_hasStrictDerivAt c z).hasDerivAt.complexToReal_fderiv.hasFDerivWithinAt

/-- The real Jacobian determinant of multiplication by the complex scalar `2z`. -/
lemma quadratic_real_fderiv_det (z : ℂ) :
    (((2 * z) • (1 : ℂ →L[ℝ] ℂ)).det) = ‖2 * z‖ ^ 2 := by
  have hmap :
      ((2 * z) • (1 : ℂ →L[ℝ] ℂ)) =
        (ContinuousLinearMap.toSpanSingleton ℂ (2 * z)).restrictScalars ℝ := by
    ext w
    simp
    ring
  rw [hmap]
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_apply,
    Complex.normSq_eq_norm_sq]

/-- On each noncritical quadratic branch, the real Jacobian cancels the inverse-branch kernel. -/
lemma quadratic_jacobian_kernel_mul_eq_one {c z : ℂ} (hz : z ≠ 0) :
    ENNReal.ofReal |(((2 * z) • (1 : ℂ →L[ℝ] ℂ)).det)| *
        ENNReal.ofReal ((4 * ‖quadratic c z - c‖)⁻¹) = 1 := by
  have hz_norm : ‖z‖ ≠ 0 := by simpa using (norm_ne_zero_iff.mpr hz)
  have hdist : ‖quadratic c z - c‖ = ‖z‖ ^ 2 := by
    rw [quadratic_apply]
    simp [norm_pow]
  have hdet : |(((2 * z) • (1 : ℂ →L[ℝ] ℂ)).det)| = 4 * ‖z‖ ^ 2 := by
    rw [quadratic_real_fderiv_det]
    rw [abs_of_nonneg (sq_nonneg ‖2 * z‖)]
    rw [norm_mul, Complex.norm_ofNat]
    ring
  rw [hdet, hdist]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * ‖z‖ ^ 2)]
  have hreal : (4 * ‖z‖ ^ 2) * (4 * ‖z‖ ^ 2)⁻¹ = 1 := by
    field_simp [hz_norm]
  rw [hreal]
  simp

/-- Complex-plane area formula for an injective real-`C¹` map on a measurable set, in
`lintegral` form. -/
theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul_complex
    {s : Set ℂ} {f : ℂ → ℂ} {f' : ℂ → ℂ →L[ℝ] ℂ}
    (hs : MeasurableSet s) (hf' : ∀ z ∈ s, HasFDerivWithinAt f (f' z) s z)
    (hf : Set.InjOn f s) (g : ℂ → ℝ≥0∞) :
    ∫⁻ z in f '' s, g z ∂(volume : Measure ℂ) =
      ∫⁻ z in s, ENNReal.ofReal |(f' z).det| * g (f z) ∂(volume : Measure ℂ) :=
  MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := volume) hs hf' hf g

/-- Complex-plane area formula for the measure of the image of an injective real-`C¹` map. -/
theorem volume_image_eq_lintegral_abs_det_fderiv_complex
    {s : Set ℂ} {f : ℂ → ℂ} {f' : ℂ → ℂ →L[ℝ] ℂ}
    (hs : MeasurableSet s) (hf' : ∀ z ∈ s, HasFDerivWithinAt f (f' z) s z)
    (hf : Set.InjOn f s) :
    volume (f '' s) = ∫⁻ z in s, ENNReal.ofReal |(f' z).det| ∂(volume : Measure ℂ) := by
  exact (MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image (μ := volume) hs hf' hf).symm

/-- Area formula on a single noncritical injective quadratic branch. -/
theorem volume_quadratic_branch_eq_lintegral_kernel {c : ℂ} {s : Set ℂ}
    (hs : MeasurableSet s) (hinj : Set.InjOn (quadratic c) s)
    (hzero : ∀ z ∈ s, z ≠ 0) :
    volume s =
      ∫⁻ w in quadratic c '' s,
        ENNReal.ofReal ((4 * ‖w - c‖)⁻¹) ∂(volume : Measure ℂ) := by
  symm
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul_complex hs
    (fun z _hz => hasFDerivWithinAt_quadratic_real c z s) hinj
    (fun w => ENNReal.ofReal ((4 * ‖w - c‖)⁻¹))]
  calc
    ∫⁻ z in s,
        ENNReal.ofReal |(((2 * z) • (1 : ℂ →L[ℝ] ℂ)).det)| *
          ENNReal.ofReal ((4 * ‖quadratic c z - c‖)⁻¹) ∂(volume : Measure ℂ)
        = ∫⁻ _z in s, (1 : ℝ≥0∞) ∂(volume : Measure ℂ) := by
          apply setLIntegral_congr_fun hs
          intro z hz
          exact quadratic_jacobian_kernel_mul_eq_one (hzero z hz)
    _ = volume s := by
          rw [setLIntegral_one]

/-- The critical value `c` has the unique preimage `0` under `z ↦ z^2+c`. -/
theorem quadratic_preimage_singleton_criticalValue (c : ℂ) :
    (quadratic c) ⁻¹' ({c} : Set ℂ) = ({0} : Set ℂ) := by
  ext z
  simp [quadratic_apply, pow_two, mul_eq_zero]

/-- The branch-overlap locus over the critical value is Lebesgue-null. -/
theorem volume_quadratic_preimage_singleton_criticalValue (c : ℂ) :
    volume ((quadratic c) ⁻¹' ({c} : Set ℂ)) = 0 := by
  rw [quadratic_preimage_singleton_criticalValue]
  exact measure_singleton 0

/-- The real linear functional cutting out the branch boundary orthogonal to `v`. -/
def quadraticBoundaryLineMap (v : ℂ) : ℂ →ₗ[ℝ] ℝ :=
  Complex.reLm.comp (LinearMap.mulLeft ℝ (starRingEnd ℂ v))

lemma quadraticBoundaryLineMap_apply (v z : ℂ) :
    quadraticBoundaryLineMap v z = (starRingEnd ℂ v * z).re := by
  rfl

/-- The line separating the two quadratic inverse sheets determined by `v`. -/
def quadraticBoundaryLine (v : ℂ) : Set ℂ :=
  {z : ℂ | (starRingEnd ℂ v * z).re = 0}

lemma quadraticBoundaryLine_eq_ker (v : ℂ) :
    quadraticBoundaryLine v = (LinearMap.ker (quadraticBoundaryLineMap v) : Set ℂ) := by
  ext z
  simp [quadraticBoundaryLine, quadraticBoundaryLineMap]

lemma quadraticBoundaryLineMap_ne_zero {v : ℂ} (hv : v ≠ 0) :
    quadraticBoundaryLineMap v ≠ 0 := by
  intro hzero
  have h_apply : quadraticBoundaryLineMap v v = (0 : ℂ →ₗ[ℝ] ℝ) v := by rw [hzero]
  rw [quadraticBoundaryLineMap_apply] at h_apply
  simp only [LinearMap.zero_apply] at h_apply
  have hnorm : (starRingEnd ℂ v * v).re = Complex.normSq v := by
    have hcomplex : ((Complex.normSq v : ℝ) : ℂ) = starRingEnd ℂ v * v := by
      simpa using (Complex.normSq_eq_conj_mul_self (z := v))
    exact (congrArg Complex.re hcomplex).symm
  rw [hnorm] at h_apply
  have hnorm_ne : Complex.normSq v ≠ 0 := mt Complex.normSq_eq_zero.mp hv
  exact hnorm_ne h_apply

lemma quadraticBoundaryLine_ker_ne_top {v : ℂ} (hv : v ≠ 0) :
    LinearMap.ker (quadraticBoundaryLineMap v) ≠ ⊤ := by
  intro htop
  exact quadraticBoundaryLineMap_ne_zero hv (LinearMap.ker_eq_top.mp htop)

/-- Every nondegenerate quadratic inverse-sheet boundary line is Lebesgue-null. -/
theorem volume_quadraticBoundaryLine_eq_zero {v : ℂ} (hv : v ≠ 0) :
    volume (quadraticBoundaryLine v) = 0 := by
  rw [quadraticBoundaryLine_eq_ker]
  exact Measure.addHaar_submodule (volume : Measure ℂ)
    (LinearMap.ker (quadraticBoundaryLineMap v)) (quadraticBoundaryLine_ker_ne_top hv)

end

end Bottcher
