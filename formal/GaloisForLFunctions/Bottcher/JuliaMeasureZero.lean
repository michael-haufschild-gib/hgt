/-
# Lebesgue-null disconnected filled Julia sets

This file builds the local infrastructure for the disconnected quadratic
filled-Julia nullity theorem.  The first reusable layer is the standard
backward-trapping escape disk and the named nested-preimage characterization.
-/
import GaloisForLFunctions.Bottcher.Dynamics
import GaloisForLFunctions.Bottcher.DisconnectedLoop
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

theorem isCompact_quadraticPreimageClosedBall (c : ℂ) (n : ℕ) :
    IsCompact (quadraticPreimageClosedBall c n) :=
  (isCompact_closedBall (0 : ℂ) (quadraticEscapeRadius c)).of_isClosed_subset
    (isClosed_quadraticPreimageClosedBall c n)
    (quadraticPreimageClosedBall_subset_closedBall c n)

/-- If an open set contains `K_c`, then a sufficiently deep trapping-disk pullback is already
contained in it. This is compactness for the decreasing closed pullbacks. -/
theorem exists_quadraticPreimageClosedBall_subset_of_filledJulia_subset_open
    {c : ℂ} {U : Set ℂ} (hU : IsOpen U) (hKU : filledJulia c ⊆ U) :
    ∃ N : ℕ, quadraticPreimageClosedBall c N ⊆ U := by
  by_contra h
  rw [not_exists] at h
  let T : ℕ → Set ℂ := fun n => quadraticPreimageClosedBall c n \ U
  have hTanti : ∀ n : ℕ, T (n + 1) ⊆ T n := by
    intro n z hz
    exact ⟨quadraticPreimageClosedBall_succ_subset c n hz.1, hz.2⟩
  have hTnonempty : ∀ n : ℕ, (T n).Nonempty := by
    intro n
    obtain ⟨z, hzS, hzU⟩ := Set.not_subset.mp (h n)
    exact ⟨z, hzS, hzU⟩
  have hTclosed : ∀ n : ℕ, IsClosed (T n) := by
    intro n
    exact (isClosed_quadraticPreimageClosedBall c n).sdiff hU
  have hTcompact0 : IsCompact (T 0) := by
    exact (isCompact_quadraticPreimageClosedBall c 0).inter_right hU.isClosed_compl
  have hnonempty : (⋂ n : ℕ, T n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      T hTanti hTnonempty hTcompact0 hTclosed
  obtain ⟨z, hz⟩ := hnonempty
  have hzK : z ∈ filledJulia c := by
    rw [filledJulia_eq_iInter_preimage_closedBall]
    exact Set.mem_iInter.mpr fun n => (Set.mem_iInter.mp hz n).1
  exact (Set.mem_iInter.mp hz 0).2 (hKU hzK)

/-- Finite-block version of
`exists_quadraticPreimageClosedBall_subset_of_filledJulia_subset_open`: if finitely many open sets
contain `K_c`, then one tail index works for the corresponding shifted trapping pullbacks. -/
theorem exists_forall_quadraticPreimageClosedBall_add_subset_of_filledJulia_subset_open
    {c : ℂ} (M : ℕ) (U : ℕ → Set ℂ)
    (hU : ∀ j : ℕ, j < M → IsOpen (U j))
    (hKU : ∀ j : ℕ, j < M → filledJulia c ⊆ U j) :
    ∃ N : ℕ, ∀ j : ℕ, j < M → quadraticPreimageClosedBall c (N + j) ⊆ U j := by
  induction M with
  | zero =>
      exact ⟨0, by intro j hj; omega⟩
  | succ M ih =>
      obtain ⟨N₀, hN₀⟩ := ih (fun j hj => hU j (Nat.lt_trans hj (Nat.lt_succ_self M)))
        (fun j hj => hKU j (Nat.lt_trans hj (Nat.lt_succ_self M)))
      obtain ⟨N₁, hN₁⟩ :=
        exists_quadraticPreimageClosedBall_subset_of_filledJulia_subset_open
          (hU M (Nat.lt_succ_self M)) (hKU M (Nat.lt_succ_self M))
      refine ⟨max N₀ N₁, ?_⟩
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjM | hjM
      · have hle : N₀ + j ≤ max N₀ N₁ + j :=
          Nat.add_le_add_right (le_max_left N₀ N₁) j
        exact (antitone_quadraticPreimageClosedBall c hle).trans (hN₀ j hjM)
      · subst j
        have hle : N₁ ≤ max N₀ N₁ + M :=
          le_trans (le_max_right N₀ N₁) (Nat.le_add_right (max N₀ N₁) M)
        exact (antitone_quadraticPreimageClosedBall c hle).trans hN₁

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

/-- A monotone finite sequence with geometric decay along a fixed positive block length tends to
zero. This is the sequence-level bridge needed for multi-step inverse-branch contraction estimates. -/
lemma tendsto_zero_of_antitone_block_geometric_bound_ennreal
    {u : ℕ → ℝ≥0∞} {M : ℕ} {q : ℝ≥0∞} (hM : 0 < M) (hq : q < 1)
    (hu0 : u 0 < ⊤) (hanti : Antitone u)
    (hdecay : ∀ n : ℕ, u (n + M) ≤ q * u n) :
    Tendsto u atTop (𝓝 0) := by
  have hblock : Tendsto (fun m : ℕ => u (m * M)) atTop (𝓝 0) := by
    apply tendsto_zero_of_geometric_bound_ennreal (u := fun m : ℕ => u (m * M)) hq
    · simpa using hu0
    · intro m
      have h := hdecay (m * M)
      simpa [Nat.succ_mul] using h
  have hdiv : Tendsto (fun n : ℕ => n / M) atTop atTop :=
    (map_div_atTop_eq_nat M hM).le
  have hblock_div : Tendsto (fun n : ℕ => u ((n / M) * M)) atTop (𝓝 0) :=
    hblock.comp hdiv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hblock_div
    (fun n => bot_le) (fun n => hanti (Nat.div_mul_le_self n M))

/-- Eventual version of `tendsto_zero_of_antitone_block_geometric_bound_ennreal`. -/
lemma tendsto_zero_of_eventually_antitone_block_geometric_bound_ennreal
    {u : ℕ → ℝ≥0∞} {N M : ℕ} {q : ℝ≥0∞} (hM : 0 < M) (hq : q < 1)
    (huN : u N < ⊤) (hanti : Antitone u)
    (hdecay : ∀ n : ℕ, N ≤ n → u (n + M) ≤ q * u n) :
    Tendsto u atTop (𝓝 0) := by
  have hshift : Tendsto (fun m : ℕ => u (m + N)) atTop (𝓝 0) := by
    apply tendsto_zero_of_antitone_block_geometric_bound_ennreal
        (u := fun m : ℕ => u (m + N)) hM hq
    · simpa using huN
    · intro a b hab
      exact hanti (Nat.add_le_add_right hab N)
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

/-- A uniform block-geometric decay estimate for the trapping-disk pullbacks implies
`volume K_c = 0`. This is the measure-facing target for any future multi-step expansion theorem. -/
theorem volume_filledJulia_eq_zero_of_block_geometric_preimage_decay {c : ℂ} {M : ℕ}
    {q : ℝ≥0∞} (hM : 0 < M) (hq : q < 1)
    (hdecay : ∀ n : ℕ,
      volume (quadraticPreimageClosedBall c (n + M)) ≤
        q * volume (quadraticPreimageClosedBall c n)) :
    volume (filledJulia c) = 0 := by
  apply volume_filledJulia_eq_zero_of_tendsto_preimage_closedBall_zero
  apply tendsto_zero_of_antitone_block_geometric_bound_ennreal hM hq
  · exact volume_quadraticPreimageClosedBall_lt_top c 0
  · intro n m hnm
    exact measure_mono (antitone_quadraticPreimageClosedBall c hnm)
  · exact hdecay

/-- An eventual block-geometric decay estimate for the trapping-disk pullbacks implies
`volume K_c = 0`. This matches the shape of disconnected escape estimates, which usually start only
after a finite critical-orbit escape time. -/
theorem volume_filledJulia_eq_zero_of_eventually_block_geometric_preimage_decay
    {c : ℂ} {N M : ℕ} {q : ℝ≥0∞} (hM : 0 < M) (hq : q < 1)
    (hdecay : ∀ n : ℕ, N ≤ n →
      volume (quadraticPreimageClosedBall c (n + M)) ≤
        q * volume (quadraticPreimageClosedBall c n)) :
    volume (filledJulia c) = 0 := by
  apply volume_filledJulia_eq_zero_of_tendsto_preimage_closedBall_zero
  apply tendsto_zero_of_eventually_antitone_block_geometric_bound_ennreal hM hq
  · exact volume_quadraticPreimageClosedBall_lt_top c N
  · intro n m hnm
    exact measure_mono (antitone_quadraticPreimageClosedBall c hnm)
  · exact hdecay

/-- If the quadratic preimage area formula is available and its kernel is uniformly bounded by
`q < 1` on every trapping-disk pullback, then `K_c` is null. -/
theorem volume_filledJulia_eq_zero_of_kernel_bound {c : ℂ} {q : ℝ≥0∞}
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

/-- Tail version of `volume_filledJulia_eq_zero_of_kernel_bound`: the kernel bound only needs to hold
from one pullback level onward. -/
theorem volume_filledJulia_eq_zero_of_eventually_kernel_bound {c : ℂ} {N : ℕ} {q : ℝ≥0∞}
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

/-- In the disconnected case, `K_c` is positively separated from the critical value `c`. -/
theorem exists_dist_filledJulia_criticalValue_pos_of_disconnected {c : ℂ}
    (hc : Disconnected c) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ filledJulia c, ρ ≤ ‖z - c‖ := by
  have hcnot : c ∉ filledJulia c := criticalValue_not_mem_filledJulia_of_disconnected hc
  rcases (filledJulia c).eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, fun z hz => ?_⟩
    rw [hemp] at hz
    simp at hz
  · obtain ⟨z₀, hz₀mem, hz₀min⟩ :=
      (isCompact_filledJulia c).exists_isMinOn hne (by fun_prop :
        ContinuousOn (fun z : ℂ => ‖z - c‖) (filledJulia c))
    have hz₀ne : z₀ - c ≠ 0 := by
      intro hz₀c
      exact hcnot (by simpa [sub_eq_zero.mp hz₀c] using hz₀mem)
    exact ⟨‖z₀ - c‖, norm_pos_iff.mpr hz₀ne, fun z hz => hz₀min hz⟩

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

/-- For `‖c‖ ≥ 4`, the first trapping-disk pullback is already separated from the
critical value by the unit ball. -/
theorem quadraticPreimageClosedBall_one_disjoint_ball_c_of_four_le_norm {c : ℂ}
    (hc : (4 : ℝ) ≤ ‖c‖) :
    Disjoint (Metric.ball c 1) (quadraticPreimageClosedBall c 1) := by
  rw [Set.disjoint_left]
  intro z hzball hzpre
  have hzdist : ‖z - c‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hzball
  have hcz : ‖c‖ - ‖z‖ ≤ ‖z - c‖ := by
    simpa [norm_sub_rev] using norm_sub_norm_le c z
  have hznorm : ‖c‖ - 1 < ‖z‖ := by linarith
  have hR : quadraticEscapeRadius c = ‖c‖ := by
    unfold quadraticEscapeRadius
    exact max_eq_right (by linarith : (2 : ℝ) ≤ ‖c‖)
  have hzpre_norm : ‖quadratic c z‖ ≤ ‖c‖ := by
    simpa [quadraticPreimageClosedBall, hR, Metric.mem_closedBall, dist_zero_right] using hzpre
  have htri : ‖z‖ ^ 2 - ‖c‖ ≤ ‖quadratic c z‖ := by
    have h := norm_sub_norm_le (z ^ 2) (-c)
    rw [norm_neg, sub_neg_eq_add, norm_pow] at h
    simpa [quadratic_apply] using h
  have hgt : ‖c‖ < ‖quadratic c z‖ := by
    nlinarith [sq_nonneg (‖z‖ - (‖c‖ - 1)), htri, hznorm, norm_nonneg z,
      norm_nonneg c, hc]
  exact not_lt_of_ge hzpre_norm hgt

/-- A quantitative first-pullback separation criterion. If the circle centered at `c`
with radius `r` is far enough from the escape disk after one quadratic step, then the
first trapping-disk pullback misses `ball c r`. -/
theorem quadraticPreimageClosedBall_one_disjoint_ball_c_of_radius {c : ℂ} {r : ℝ}
    (h2c : (2 : ℝ) ≤ ‖c‖) (hrc : r < ‖c‖)
    (hbig : 2 * ‖c‖ < (‖c‖ - r) ^ 2) :
    Disjoint (Metric.ball c r) (quadraticPreimageClosedBall c 1) := by
  rw [Set.disjoint_left]
  intro z hzball hzpre
  have hzdist : ‖z - c‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hzball
  have hcz : ‖c‖ - ‖z‖ ≤ ‖z - c‖ := by
    simpa [norm_sub_rev] using norm_sub_norm_le c z
  have hznorm : ‖c‖ - r < ‖z‖ := by linarith
  have hR : quadraticEscapeRadius c = ‖c‖ := by
    unfold quadraticEscapeRadius
    exact max_eq_right h2c
  have hzpre_norm : ‖quadratic c z‖ ≤ ‖c‖ := by
    simpa [quadraticPreimageClosedBall, hR, Metric.mem_closedBall, dist_zero_right] using hzpre
  have htri : ‖z‖ ^ 2 - ‖c‖ ≤ ‖quadratic c z‖ := by
    have h := norm_sub_norm_le (z ^ 2) (-c)
    rw [norm_neg, sub_neg_eq_add, norm_pow] at h
    simpa [quadratic_apply] using h
  have hrpos : 0 < ‖c‖ - r := by linarith
  have hgt : ‖c‖ < ‖quadratic c z‖ := by
    nlinarith [hbig, htri, hznorm, hrpos, norm_nonneg z]
  exact not_lt_of_ge hzpre_norm hgt

/-- For `‖c‖ ≥ 3`, the first trapping-disk pullback is already separated from the
critical value by the ball of radius `51 / 100`, which is large enough for contraction. -/
theorem quadraticPreimageClosedBall_one_disjoint_ball_c_of_three_le_norm {c : ℂ}
    (hc : (3 : ℝ) ≤ ‖c‖) :
    Disjoint (Metric.ball c ((51 : ℝ) / 100)) (quadraticPreimageClosedBall c 1) := by
  apply quadraticPreimageClosedBall_one_disjoint_ball_c_of_radius
  · linarith
  · linarith
  · nlinarith [sq_nonneg (‖c‖ - 3), hc]

/-- For `‖c‖ ≥ 73 / 25`, the first trapping-disk pullback is already separated from the
critical value by the ball of radius `501 / 1000`, still large enough for contraction. -/
theorem quadraticPreimageClosedBall_one_disjoint_ball_c_of_seventy_three_div_twenty_five_le_norm
    {c : ℂ} (hc : ((73 : ℝ) / 25) ≤ ‖c‖) :
    Disjoint (Metric.ball c ((501 : ℝ) / 1000)) (quadraticPreimageClosedBall c 1) := by
  apply quadraticPreimageClosedBall_one_disjoint_ball_c_of_radius
  · linarith
  · linarith
  · nlinarith [sq_nonneg (‖c‖ - (73 : ℝ) / 25), hc]

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
  apply volume_filledJulia_eq_zero_of_eventually_kernel_bound hq hpreimage
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

/-- Area formula for the positive half-plane quadratic inverse sheet over a boundary-avoiding set. -/
theorem volume_quadratic_halfplane_branch_eq_lintegral_kernel {c v : ℂ} {A : Set ℂ}
    (hA : MeasurableSet A)
    (hboundary :
      ∀ w ∈ A, ∀ z : ℂ, quadratic c z = w → (starRingEnd ℂ v * z).re ≠ 0) :
    volume ({z : ℂ | 0 < (starRingEnd ℂ v * z).re} ∩ (quadratic c ⁻¹' A)) =
      ∫⁻ w in A, ENNReal.ofReal ((4 * ‖w - c‖)⁻¹) ∂(volume : Measure ℂ) := by
  let H : Set ℂ := {z : ℂ | 0 < (starRingEnd ℂ v * z).re}
  let s : Set ℂ := H ∩ (quadratic c ⁻¹' A)
  have hhalf_open : IsOpen H := by
    dsimp [H]
    exact isOpen_lt continuous_const (by fun_prop)
  have hs : MeasurableSet s := by
    dsimp [s]
    exact hhalf_open.measurableSet.inter (hA.preimage (continuous_quadratic c).measurable)
  have hbij : Set.BijOn (quadratic c) s A := by
    dsimp [s, H]
    exact quadratic_bijOn_halfplane_preimage_of_boundary_avoid
      (c := c) (v := v) (A := A) hboundary
  have himage : quadratic c '' s = A := hbij.image_eq
  have hzero : ∀ z ∈ s, z ≠ 0 := by
    intro z hz hz0
    have hzA : quadratic c z ∈ A := hz.2
    have hne := hboundary (quadratic c z) hzA z rfl
    simp [hz0] at hne
  change volume s =
    ∫⁻ w in A, ENNReal.ofReal ((4 * ‖w - c‖)⁻¹) ∂(volume : Measure ℂ)
  rw [← himage]
  exact volume_quadratic_branch_eq_lintegral_kernel hs hbij.injOn hzero

lemma quadratic_two_kernel4_eq_kernel2 (c w : ℂ) :
    (2 : ℝ≥0∞) * ENNReal.ofReal ((4 * ‖w - c‖)⁻¹) =
      ENNReal.ofReal ((2 * ‖w - c‖)⁻¹) := by
  by_cases hw : w = c
  · simp [hw]
  · have hnorm_ne : ‖w - c‖ ≠ 0 := by
      simpa [sub_eq_zero] using sub_ne_zero.mpr hw
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
    rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
    congr 1
    field_simp [hnorm_ne]
    norm_num

lemma measurable_quadratic_kernel4 (c : ℂ) :
    Measurable (fun w : ℂ => ENNReal.ofReal ((4 * ‖w - c‖)⁻¹)) := by
  fun_prop

/-- Two-sheet quadratic area formula for targets avoiding one sheet boundary. -/
theorem volume_quadratic_preimage_eq_lintegral_kernel_of_boundary_avoid
    {c v : ℂ} {A : Set ℂ} (hA : MeasurableSet A)
    (hboundary : ∀ z : ℂ, quadratic c z ∈ A → (starRingEnd ℂ v * z).re ≠ 0) :
    volume ((quadratic c) ⁻¹' A) =
      ∫⁻ w in A, ENNReal.ofReal ((2 * ‖w - c‖)⁻¹) ∂(volume : Measure ℂ) := by
  let Hpos : Set ℂ := {z : ℂ | 0 < (starRingEnd ℂ v * z).re}
  let Hneg : Set ℂ := {z : ℂ | (starRingEnd ℂ v * z).re < 0}
  have hsplit :
      (quadratic c) ⁻¹' A = (Hpos ∩ (quadratic c ⁻¹' A)) ∪
        (Hneg ∩ (quadratic c ⁻¹' A)) := by
    dsimp [Hpos, Hneg]
    exact quadratic_preimage_eq_halfplane_union_of_boundary_avoid
      (c := c) (v := v) (A := A) hboundary
  have hneg_open : IsOpen Hneg := by
    dsimp [Hneg]
    exact isOpen_lt (by fun_prop) continuous_const
  have hneg_meas : MeasurableSet (Hneg ∩ (quadratic c ⁻¹' A)) :=
    hneg_open.measurableSet.inter (hA.preimage (continuous_quadratic c).measurable)
  have hdisj : Disjoint (Hpos ∩ (quadratic c ⁻¹' A)) (Hneg ∩ (quadratic c ⁻¹' A)) := by
    rw [Set.disjoint_left]
    intro z hzpos hzneg
    have hpos : 0 < (starRingEnd ℂ v * z).re := hzpos.1
    have hneg : (starRingEnd ℂ v * z).re < 0 := hzneg.1
    linarith
  have hboundary_pos :
      ∀ w ∈ A, ∀ z : ℂ, quadratic c z = w → (starRingEnd ℂ v * z).re ≠ 0 := by
    intro w hw z hzw
    exact hboundary z (by rwa [hzw])
  have hboundary_neg :
      ∀ w ∈ A, ∀ z : ℂ, quadratic c z = w → (starRingEnd ℂ (-v) * z).re ≠ 0 := by
    intro w hw z hzw hzero
    have hpos_zero : (starRingEnd ℂ v * z).re = 0 := by
      have hneg_re : -((starRingEnd ℂ v * z).re) = 0 := by
        simpa only [map_neg, neg_mul, Complex.neg_re] using hzero
      linarith
    exact hboundary z (by rwa [hzw]) hpos_zero
  have hpos_vol :
      volume (Hpos ∩ (quadratic c ⁻¹' A)) =
        ∫⁻ w in A, ENNReal.ofReal ((4 * ‖w - c‖)⁻¹) ∂(volume : Measure ℂ) := by
    dsimp [Hpos]
    exact volume_quadratic_halfplane_branch_eq_lintegral_kernel
      (c := c) (v := v) (A := A) hA hboundary_pos
  have hnegset :
      {z : ℂ | 0 < (starRingEnd ℂ (-v) * z).re} ∩ (quadratic c ⁻¹' A) =
        Hneg ∩ (quadratic c ⁻¹' A) := by
    dsimp [Hneg]
    ext z
    constructor
    · intro hz
      refine ⟨?_, hz.2⟩
      have hlt : 0 < -((starRingEnd ℂ v * z).re) := by
        simpa only [map_neg, neg_mul, Complex.neg_re] using hz.1
      exact neg_pos.mp hlt
    · intro hz
      refine ⟨?_, hz.2⟩
      have hlt : (starRingEnd ℂ v * z).re < 0 := hz.1
      have : 0 < -((starRingEnd ℂ v * z).re) := neg_pos.mpr hlt
      simpa only [map_neg, neg_mul, Complex.neg_re] using this
  have hneg_vol :
      volume (Hneg ∩ (quadratic c ⁻¹' A)) =
        ∫⁻ w in A, ENNReal.ofReal ((4 * ‖w - c‖)⁻¹) ∂(volume : Measure ℂ) := by
    rw [← hnegset]
    exact volume_quadratic_halfplane_branch_eq_lintegral_kernel
      (c := c) (v := -v) (A := A) hA hboundary_neg
  rw [hsplit, measure_union hdisj hneg_meas, hpos_vol, hneg_vol]
  let k4 : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal ((4 * ‖w - c‖)⁻¹)
  have hk4_meas : Measurable k4 := measurable_quadratic_kernel4 c
  calc
    (∫⁻ w in A, k4 w ∂(volume : Measure ℂ)) +
        ∫⁻ w in A, k4 w ∂(volume : Measure ℂ)
        = ∫⁻ w in A, k4 w + k4 w ∂(volume : Measure ℂ) := by
          rw [lintegral_add_left (μ := (volume : Measure ℂ).restrict A) hk4_meas]
    _ = ∫⁻ w in A, (2 : ℝ≥0∞) * k4 w ∂(volume : Measure ℂ) := by
          apply setLIntegral_congr_fun hA
          intro w _hw
          exact (two_mul (k4 w)).symm
    _ = ∫⁻ w in A, ENNReal.ofReal ((2 * ‖w - c‖)⁻¹) ∂(volume : Measure ℂ) := by
          apply setLIntegral_congr_fun hA
          intro w _hw
          exact quadratic_two_kernel4_eq_kernel2 c w

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

/-- The horizontal affine line through `c`. -/
def horizontalLineThrough (c : ℂ) : Set ℂ :=
  {w : ℂ | (w - c).im = 0}

lemma realAxis_eq_ker_imLm :
    ({z : ℂ | z.im = 0} : Set ℂ) = (LinearMap.ker (Complex.imLm : ℂ →ₗ[ℝ] ℝ) : Set ℂ) := by
  ext z
  simp

lemma imLm_ker_ne_top :
    LinearMap.ker (Complex.imLm : ℂ →ₗ[ℝ] ℝ) ≠ ⊤ := by
  intro htop
  have him : (Complex.imLm : ℂ →ₗ[ℝ] ℝ) = 0 := LinearMap.ker_eq_top.mp htop
  have hI : (Complex.imLm : ℂ →ₗ[ℝ] ℝ) Complex.I = (0 : ℂ →ₗ[ℝ] ℝ) Complex.I := by
    rw [him]
  norm_num at hI

lemma volume_realAxis_eq_zero :
    volume ({z : ℂ | z.im = 0} : Set ℂ) = 0 := by
  rw [realAxis_eq_ker_imLm]
  exact Measure.addHaar_submodule (volume : Measure ℂ)
    (LinearMap.ker (Complex.imLm : ℂ →ₗ[ℝ] ℝ)) imLm_ker_ne_top

lemma imagAxis_eq_ker_reLm :
    ({z : ℂ | z.re = 0} : Set ℂ) = (LinearMap.ker (Complex.reLm : ℂ →ₗ[ℝ] ℝ) : Set ℂ) := by
  ext z
  simp

lemma reLm_ker_ne_top :
    LinearMap.ker (Complex.reLm : ℂ →ₗ[ℝ] ℝ) ≠ ⊤ := by
  intro htop
  have hre : (Complex.reLm : ℂ →ₗ[ℝ] ℝ) = 0 := LinearMap.ker_eq_top.mp htop
  have hI : (Complex.reLm : ℂ →ₗ[ℝ] ℝ) 1 = (0 : ℂ →ₗ[ℝ] ℝ) 1 := by
    rw [hre]
  norm_num at hI

lemma volume_imagAxis_eq_zero :
    volume ({z : ℂ | z.re = 0} : Set ℂ) = 0 := by
  rw [imagAxis_eq_ker_reLm]
  exact Measure.addHaar_submodule (volume : Measure ℂ)
    (LinearMap.ker (Complex.reLm : ℂ →ₗ[ℝ] ℝ)) reLm_ker_ne_top

/-- Every horizontal affine line in the complex plane is Lebesgue-null. -/
theorem volume_horizontalLineThrough_eq_zero (c : ℂ) :
    volume (horizontalLineThrough c) = 0 := by
  have hpre :
      (fun z : ℂ => c + z) ⁻¹' horizontalLineThrough c = ({z : ℂ | z.im = 0} : Set ℂ) := by
    ext z
    simp [horizontalLineThrough]
  have h := measure_preimage_add (volume : Measure ℂ) c (horizontalLineThrough c)
  rw [hpre, volume_realAxis_eq_zero] at h
  exact h.symm

lemma measurableSet_horizontalLineThrough (c : ℂ) :
    MeasurableSet (horizontalLineThrough c) := by
  dsimp [horizontalLineThrough]
  exact (isClosed_eq (Complex.continuous_im.comp (continuous_id.sub continuous_const))
    continuous_const).measurableSet

/-- The quadratic preimage of the horizontal line through `c` is contained in the two coordinate
axes, hence is null. -/
theorem volume_quadratic_preimage_horizontalLineThrough_eq_zero (c : ℂ) :
    volume ((quadratic c) ⁻¹' horizontalLineThrough c) = 0 := by
  have hsubset :
      (quadratic c) ⁻¹' horizontalLineThrough c ⊆
        ({z : ℂ | z.re = 0} : Set ℂ) ∪ ({z : ℂ | z.im = 0} : Set ℂ) := by
    intro z hz
    have him : (z ^ 2).im = 0 := by
      simpa [horizontalLineThrough, quadratic_apply] using hz
    have hmul : z.re * z.im = 0 := by
      have htwo : (2 : ℝ) * (z.re * z.im) = 0 := by
        simpa [pow_two, Complex.mul_im, mul_assoc, mul_comm, mul_left_comm] using him
      nlinarith
    rcases mul_eq_zero.mp hmul with hre | him'
    · exact Or.inl hre
    · exact Or.inr him'
  have hunion_null :
      volume (({z : ℂ | z.re = 0} : Set ℂ) ∪ ({z : ℂ | z.im = 0} : Set ℂ)) = 0 :=
    measure_union_null volume_imagAxis_eq_zero volume_realAxis_eq_zero
  exact measure_mono_null hsubset hunion_null

/-- The quadratic preimage area formula. -/
theorem volume_preimage_quadratic_eq (c : ℂ) {A : Set ℂ} (hA : MeasurableSet A) :
    volume ((quadratic c) ⁻¹' A) =
      ∫⁻ w in A, ENNReal.ofReal ((2 * ‖w - c‖)⁻¹) ∂(volume : Measure ℂ) := by
  let H : Set ℂ := horizontalLineThrough c
  have hHmeas : MeasurableSet H := measurableSet_horizontalLineThrough c
  have hAoff : MeasurableSet (A \ H) := hA.diff hHmeas
  have hboundary :
      ∀ z : ℂ, quadratic c z ∈ A \ H → (starRingEnd ℂ (1 : ℂ) * z).re ≠ 0 := by
    intro z hz hline
    have hH : quadratic c z ∈ H := by
      have hre : z.re = 0 := by
        simpa using hline
      dsimp [H, horizontalLineThrough]
      simp [pow_two, Complex.mul_im, hre]
    exact hz.2 hH
  have hslit :=
    volume_quadratic_preimage_eq_lintegral_kernel_of_boundary_avoid
      (c := c) (v := 1) (A := A \ H) hAoff hboundary
  have hpre_ae :
      (quadratic c ⁻¹' A) =ᵐ[volume] (quadratic c ⁻¹' (A \ H)) := by
    rw [ae_eq_set]
    constructor
    · apply measure_mono_null ?_ (volume_quadratic_preimage_horizontalLineThrough_eq_zero c)
      intro z hz
      exact by_contra fun hzH => hz.2 ⟨hz.1, hzH⟩
    · apply measure_mono_null ?_ (by simp : volume (∅ : Set ℂ) = 0)
      intro z hz
      exact False.elim (hz.2 hz.1.1)
  have hmeasure :
      volume ((quadratic c) ⁻¹' A) = volume ((quadratic c) ⁻¹' (A \ H)) :=
    measure_congr hpre_ae
  have htarget_ae : A =ᵐ[volume] A \ H := by
    rw [ae_eq_set]
    constructor
    · apply measure_mono_null ?_ (volume_horizontalLineThrough_eq_zero c)
      intro w hw
      exact by_contra fun hwH => hw.2 ⟨hw.1, hwH⟩
    · apply measure_mono_null ?_ (by simp : volume (∅ : Set ℂ) = 0)
      intro w hw
      exact False.elim (hw.2 hw.1.1)
  have hintegral :
      (∫⁻ w in A, ENNReal.ofReal ((2 * ‖w - c‖)⁻¹) ∂(volume : Measure ℂ)) =
        ∫⁻ w in A \ H, ENNReal.ofReal ((2 * ‖w - c‖)⁻¹) ∂(volume : Measure ℂ) :=
    setLIntegral_congr htarget_ae
  rw [hmeasure, hslit]
  exact hintegral.symm

/-- Iterating one-step kernel bounds gives a block estimate for trapping-disk pullback volumes. -/
theorem volume_quadraticPreimageClosedBall_add_le_prod_step_kernel_bounds
    (c : ℂ) (n M : ℕ) (qstep : ℕ → ℝ≥0∞)
    (hkernel : ∀ j : ℕ, j < M → ∀ w ∈ quadraticPreimageClosedBall c (n + j),
      ENNReal.ofReal ((2 * ‖w - c‖)⁻¹) ≤ qstep j) :
    volume (quadraticPreimageClosedBall c (n + M)) ≤
      (∏ j ∈ Finset.range M, qstep j) * volume (quadraticPreimageClosedBall c n) := by
  induction M generalizing n with
  | zero =>
      simp
  | succ M ih =>
      have hprev :
          volume (quadraticPreimageClosedBall c (n + M)) ≤
            (∏ j ∈ Finset.range M, qstep j) *
              volume (quadraticPreimageClosedBall c n) :=
        ih n (fun j hj => hkernel j (Nat.lt_trans hj (Nat.lt_succ_self M)))
      have hlast :
          volume (quadraticPreimageClosedBall c (n + (M + 1))) ≤
            qstep M * volume (quadraticPreimageClosedBall c (n + M)) := by
        rw [show n + (M + 1) = n + M + 1 by omega,
          quadraticPreimageClosedBall_succ_eq_preimage,
          volume_preimage_quadratic_eq c
            (A := quadraticPreimageClosedBall c (n + M))
            (measurableSet_quadraticPreimageClosedBall c (n + M))]
        calc
          ∫⁻ w in quadraticPreimageClosedBall c (n + M),
              ENNReal.ofReal ((2 * ‖w - c‖)⁻¹) ∂(volume : Measure ℂ)
              ≤ ∫⁻ _w in quadraticPreimageClosedBall c (n + M),
                  qstep M ∂(volume : Measure ℂ) := by
                exact setLIntegral_mono'
                  (measurableSet_quadraticPreimageClosedBall c (n + M))
                  (fun w hw => hkernel M (Nat.lt_succ_self M) w hw)
          _ = qstep M * volume (quadraticPreimageClosedBall c (n + M)) := by
                rw [setLIntegral_const]
      calc
        volume (quadraticPreimageClosedBall c (n + (M + 1)))
            ≤ qstep M * volume (quadraticPreimageClosedBall c (n + M)) := hlast
        _ ≤ qstep M *
              ((∏ j ∈ Finset.range M, qstep j) *
                volume (quadraticPreimageClosedBall c n)) := by
              simpa [mul_assoc, mul_comm, mul_left_comm] using
                mul_le_mul_right hprev (qstep M)
        _ = (∏ j ∈ Finset.range (M + 1), qstep j) *
              volume (quadraticPreimageClosedBall c n) := by
              rw [Finset.prod_range_succ]
              ac_rfl

/-- An eventual block of one-step kernel bounds whose product is a contraction makes `K_c` null. -/
theorem volume_filledJulia_eq_zero_of_eventually_block_kernel_product
    {c : ℂ} {N M : ℕ} {q : ℝ≥0∞} (qstep : ℕ → ℝ≥0∞)
    (hM : 0 < M) (hq : q < 1)
    (hprod : (∏ j ∈ Finset.range M, qstep j) ≤ q)
    (hkernel : ∀ n : ℕ, N ≤ n → ∀ j : ℕ, j < M →
      ∀ w ∈ quadraticPreimageClosedBall c (n + j),
        ENNReal.ofReal ((2 * ‖w - c‖)⁻¹) ≤ qstep j) :
    volume (filledJulia c) = 0 := by
  apply volume_filledJulia_eq_zero_of_eventually_block_geometric_preimage_decay
      (c := c) (N := N) (M := M) hM hq
  intro n hn
  have hblock :=
    volume_quadraticPreimageClosedBall_add_le_prod_step_kernel_bounds
      c n M qstep (hkernel n hn)
  calc
    volume (quadraticPreimageClosedBall c (n + M))
        ≤ (∏ j ∈ Finset.range M, qstep j) *
            volume (quadraticPreimageClosedBall c n) := hblock
    _ ≤ q * volume (quadraticPreimageClosedBall c n) := by
          exact mul_le_mul_left hprod (volume (quadraticPreimageClosedBall c n))

/-- A finite block of strict distance lower bounds on `K_c`, whose one-step area kernels have
contracting product, implies `K_c` is null. Compactness promotes the strict `K_c` bounds to an
eventual tail of trapping-disk pullbacks, then `volume_filledJulia_eq_zero_of_eventually_block_kernel_product`
applies. -/
theorem volume_filledJulia_eq_zero_of_filledJulia_block_dist_bounds
    {c : ℂ} {M : ℕ} (rstep : ℕ → ℝ) {q : ℝ≥0∞}
    (hM : 0 < M) (hq : q < 1)
    (hprod :
      (∏ j ∈ Finset.range M, ENNReal.ofReal ((2 * rstep j)⁻¹)) ≤ q)
    (hrpos : ∀ j : ℕ, j < M → 0 < rstep j)
    (hdist : ∀ j : ℕ, j < M → ∀ w ∈ filledJulia c, rstep j < ‖w - c‖) :
    volume (filledJulia c) = 0 := by
  let U : ℕ → Set ℂ := fun j => {w : ℂ | rstep j < ‖w - c‖}
  have hUopen : ∀ j : ℕ, j < M → IsOpen (U j) := by
    intro j _hj
    dsimp [U]
    exact isOpen_lt continuous_const (by fun_prop)
  have hKU : ∀ j : ℕ, j < M → filledJulia c ⊆ U j := by
    intro j hj w hw
    exact hdist j hj w hw
  obtain ⟨N, hN⟩ :=
    exists_forall_quadraticPreimageClosedBall_add_subset_of_filledJulia_subset_open
      (c := c) M U hUopen hKU
  apply volume_filledJulia_eq_zero_of_eventually_block_kernel_product
      (c := c) (N := N) (M := M) (q := q)
      (fun j => ENNReal.ofReal ((2 * rstep j)⁻¹)) hM hq hprod
  intro n hn j hj w hw
  have hle : N + j ≤ n + j := Nat.add_le_add_right hn j
  have hwN : w ∈ quadraticPreimageClosedBall c (N + j) :=
    antitone_quadraticPreimageClosedBall c hle hw
  have hrlt : rstep j < ‖w - c‖ := hN j hj hwN
  have h2le : 2 * rstep j ≤ 2 * ‖w - c‖ := by nlinarith
  have h2pos : 0 < 2 * rstep j := by nlinarith [hrpos j hj]
  have hinv : (2 * ‖w - c‖)⁻¹ ≤ (2 * rstep j)⁻¹ := inv_anti₀ h2pos h2le
  exact ENNReal.ofReal_le_ofReal hinv

/-- Disconnected-facing block-distance gate. The remaining dynamical input for the full theorem is
exactly a finite block of strict `K_c`-distance lower bounds whose one-step kernel product is a
contraction. -/
theorem volume_filledJulia_eq_zero_of_disconnected_of_filledJulia_block_dist_bounds
    {c : ℂ} (_hc : Disconnected c) {M : ℕ} (rstep : ℕ → ℝ) {q : ℝ≥0∞}
    (hM : 0 < M) (hq : q < 1)
    (hprod :
      (∏ j ∈ Finset.range M, ENNReal.ofReal ((2 * rstep j)⁻¹)) ≤ q)
    (hrpos : ∀ j : ℕ, j < M → 0 < rstep j)
    (hdist : ∀ j : ℕ, j < M → ∀ w ∈ filledJulia c, rstep j < ‖w - c‖) :
    volume (filledJulia c) = 0 :=
  volume_filledJulia_eq_zero_of_filledJulia_block_dist_bounds
    (c := c) (M := M) rstep hM hq hprod hrpos hdist

/-- Disconnected parameters always give a positive `K_c`-separation scale from the critical value.
The missing final step is not positivity, but producing a finite block whose kernel product is
strictly below one. -/
theorem exists_filledJulia_criticalValue_dist_bounds_pos_of_disconnected {c : ℂ}
    (hc : Disconnected c) :
    ∃ r : ℝ, 0 < r ∧ ∀ w ∈ filledJulia c, r < ‖w - c‖ := by
  obtain ⟨ρ, hρ, hρle⟩ := exists_dist_filledJulia_criticalValue_pos_of_disconnected hc
  refine ⟨ρ / 2, by linarith, ?_⟩
  intro w hw
  have := hρle w hw
  linarith

/-- Kernel-bound nullity using the proved quadratic preimage area formula. -/
theorem volume_filledJulia_eq_zero_of_forall_dist_area {c : ℂ} {q : ℝ≥0∞}
    (hq : q < 1)
    (hkernel : ∀ n : ℕ, ∀ w ∈ quadraticPreimageClosedBall c n,
      ENNReal.ofReal ((2 * ‖w - c‖)⁻¹) ≤ q) :
    volume (filledJulia c) = 0 :=
  volume_filledJulia_eq_zero_of_kernel_bound hq
    (fun A hA => volume_preimage_quadratic_eq c (A := A) hA) hkernel

/-- If the whole trapping disk is separated from the critical value by distance strictly greater
than `1 / 2`, then the one-step area formula gives geometric decay and `K_c` is null. -/
theorem volume_filledJulia_eq_zero_of_forall_dist {c : ℂ}
    (hdist : ∀ w ∈ Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c),
      ((1 : ℝ) / 2) < ‖w - c‖) :
    volume (filledJulia c) = 0 := by
  let D : Set ℂ := Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c)
  have hcompact : IsCompact D := by
    dsimp [D]
    exact isCompact_closedBall (0 : ℂ) (quadraticEscapeRadius c)
  have hcont : ContinuousOn (fun w : ℂ => ‖w - c‖) D := by
    fun_prop
  have hdistD : ∀ w ∈ D, ((1 : ℝ) / 2) < ‖w - c‖ := by
    simpa [D] using hdist
  obtain ⟨a, ha_gt, ha_lower⟩ :=
    hcompact.exists_forall_le' (a := ((1 : ℝ) / 2)) hcont hdistD
  have ha_pos : 0 < a := by nlinarith
  have h2a_gt_one : 1 < 2 * a := by nlinarith
  have hq : ENNReal.ofReal ((2 * a)⁻¹) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact inv_lt_one_of_one_lt₀ h2a_gt_one
  apply volume_filledJulia_eq_zero_of_forall_dist_area
      (c := c) (q := ENNReal.ofReal ((2 * a)⁻¹)) hq
  intro n w hw
  have hwD : w ∈ D := quadraticPreimageClosedBall_subset_closedBall c n hw
  have ha_le : a ≤ ‖w - c‖ := ha_lower w hwD
  have h2le : 2 * a ≤ 2 * ‖w - c‖ := by nlinarith
  have h2apos : 0 < 2 * a := by nlinarith
  have hinv : (2 * ‖w - c‖)⁻¹ ≤ (2 * a)⁻¹ := inv_anti₀ h2apos h2le
  exact ENNReal.ofReal_le_ofReal hinv

/-- Eventual kernel-bound nullity using the proved quadratic preimage area formula. -/
theorem volume_filledJulia_eq_zero_of_eventually_forall_dist_area {c : ℂ} {N : ℕ}
    {q : ℝ≥0∞} (hq : q < 1)
    (hkernel : ∀ n : ℕ, N ≤ n → ∀ w ∈ quadraticPreimageClosedBall c n,
      ENNReal.ofReal ((2 * ‖w - c‖)⁻¹) ≤ q) :
    volume (filledJulia c) = 0 :=
  volume_filledJulia_eq_zero_of_eventually_kernel_bound hq
    (fun A hA => volume_preimage_quadratic_eq c (A := A) hA) hkernel

/-- If some trapping-disk pullback is separated from the critical value by distance strictly greater
than `1 / 2`, then all later pullbacks satisfy a uniform one-step contraction and `K_c` is null. -/
theorem volume_filledJulia_eq_zero_of_eventually_forall_dist {c : ℂ} {N : ℕ}
    (hdist : ∀ w ∈ quadraticPreimageClosedBall c N, ((1 : ℝ) / 2) < ‖w - c‖) :
    volume (filledJulia c) = 0 := by
  let S : Set ℂ := quadraticPreimageClosedBall c N
  have hcompact : IsCompact S := by
    dsimp [S]
    exact isCompact_quadraticPreimageClosedBall c N
  have hcont : ContinuousOn (fun w : ℂ => ‖w - c‖) S := by
    fun_prop
  have hdistS : ∀ w ∈ S, ((1 : ℝ) / 2) < ‖w - c‖ := by
    simpa [S] using hdist
  obtain ⟨a, ha_gt, ha_lower⟩ :=
    hcompact.exists_forall_le' (a := ((1 : ℝ) / 2)) hcont hdistS
  have ha_pos : 0 < a := by nlinarith
  have h2a_gt_one : 1 < 2 * a := by nlinarith
  have hq : ENNReal.ofReal ((2 * a)⁻¹) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact inv_lt_one_of_one_lt₀ h2a_gt_one
  apply volume_filledJulia_eq_zero_of_eventually_forall_dist_area
      (c := c) (N := N) (q := ENNReal.ofReal ((2 * a)⁻¹)) hq
  intro n hn w hw
  have hwS : w ∈ S := (antitone_quadraticPreimageClosedBall c hn) hw
  have ha_le : a ≤ ‖w - c‖ := ha_lower w hwS
  have h2le : 2 * a ≤ 2 * ‖w - c‖ := by nlinarith
  have h2apos : 0 < 2 * a := by nlinarith
  have hinv : (2 * ‖w - c‖)⁻¹ ≤ (2 * a)⁻¹ := inv_anti₀ h2apos h2le
  exact ENNReal.ofReal_le_ofReal hinv

/-- A strict distance lower bound on `K_c` itself can be promoted to a finite pullback-level
distance bound by compactness, then to nullity by the area formula. -/
theorem volume_filledJulia_eq_zero_of_filledJulia_dist_gt_half {c : ℂ}
    (hdist : ∀ w ∈ filledJulia c, ((1 : ℝ) / 2) < ‖w - c‖) :
    volume (filledJulia c) = 0 := by
  let U : Set ℂ := {w : ℂ | ((1 : ℝ) / 2) < ‖w - c‖}
  have hU : IsOpen U := by
    dsimp [U]
    exact isOpen_lt continuous_const (by fun_prop)
  have hKU : filledJulia c ⊆ U := by
    intro w hw
    exact hdist w hw
  obtain ⟨N, hN⟩ :=
    exists_quadraticPreimageClosedBall_subset_of_filledJulia_subset_open hU hKU
  exact volume_filledJulia_eq_zero_of_eventually_forall_dist (c := c) (N := N)
    (fun w hw => hN hw)

/-- Ball-disjointness form of the `K_c`-level separation criterion. -/
theorem volume_filledJulia_eq_zero_of_filledJulia_disjoint_ball_c_radius_gt_half
    {c : ℂ} {r : ℝ}
    (hrhalf : ((1 : ℝ) / 2) < r)
    (hdisj : Disjoint (Metric.ball c r) (filledJulia c)) :
    volume (filledJulia c) = 0 := by
  apply volume_filledJulia_eq_zero_of_filledJulia_dist_gt_half
  intro w hw
  have hwball : w ∉ Metric.ball c r := fun hwb => (Set.disjoint_left.mp hdisj hwb) hw
  have hnotlt : ¬ dist w c < r := fun h => hwball (Metric.mem_ball.mpr h)
  have hdist : r ≤ dist w c := le_of_not_gt hnotlt
  have hnorm : r ≤ ‖w - c‖ := by
    simpa [dist_eq_norm] using hdist
  linarith

/-- Separated-pullback nullity using the proved quadratic preimage area formula. -/
theorem volume_filledJulia_eq_zero_of_disjoint_ball_c_area
    {c : ℂ} {N : ℕ} {r : ℝ} {q : ℝ≥0∞}
    (hq : q < 1)
    (hr : 0 < r)
    (hdisj : Disjoint (Metric.ball c r) (quadraticPreimageClosedBall c N))
    (hqkernel : ENNReal.ofReal ((2 * r)⁻¹) ≤ q) :
    volume (filledJulia c) = 0 :=
  volume_filledJulia_eq_zero_of_disjoint_ball_c hq
    (fun A hA => volume_preimage_quadratic_eq c (A := A) hA) hr hdisj hqkernel

/-- A separated pullback level gives nullity when the separation radius is already large enough to
make the one-step quadratic area kernel a contraction. -/
theorem volume_filledJulia_eq_zero_of_disjoint_ball_c_radius_gt_half
    {c : ℂ} {N : ℕ} {r : ℝ}
    (hrhalf : ((1 : ℝ) / 2) < r)
    (hdisj : Disjoint (Metric.ball c r) (quadraticPreimageClosedBall c N)) :
    volume (filledJulia c) = 0 := by
  have hr : 0 < r := by nlinarith
  have h2r_gt_one : 1 < 2 * r := by nlinarith
  have hq : ENNReal.ofReal ((2 * r)⁻¹) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact inv_lt_one_of_one_lt₀ h2r_gt_one
  exact volume_filledJulia_eq_zero_of_disjoint_ball_c_area
    (c := c) (N := N) (r := r) (q := ENNReal.ofReal ((2 * r)⁻¹))
    hq hr hdisj le_rfl

/-- Quantitative first-pullback radius criterion for nullity. -/
theorem volume_filledJulia_eq_zero_of_first_pullback_radius {c : ℂ} {r : ℝ}
    (hrhalf : ((1 : ℝ) / 2) < r)
    (h2c : (2 : ℝ) ≤ ‖c‖) (hrc : r < ‖c‖)
    (hbig : 2 * ‖c‖ < (‖c‖ - r) ^ 2) :
    volume (filledJulia c) = 0 :=
  volume_filledJulia_eq_zero_of_disjoint_ball_c_radius_gt_half
    (c := c) (N := 1) (r := r) hrhalf
    (quadraticPreimageClosedBall_one_disjoint_ball_c_of_radius h2c hrc hbig)

/-- Large parameters give Lebesgue-null filled Julia sets by the explicit first-pullback
separation from the critical value. -/
theorem volume_filledJulia_eq_zero_of_four_le_norm {c : ℂ} (hc : (4 : ℝ) ≤ ‖c‖) :
    volume (filledJulia c) = 0 :=
  volume_filledJulia_eq_zero_of_disjoint_ball_c_radius_gt_half
    (c := c) (N := 1) (r := 1) (by norm_num)
    (quadraticPreimageClosedBall_one_disjoint_ball_c_of_four_le_norm hc)

/-- Parameters with `‖c‖ ≥ 3` give Lebesgue-null filled Julia sets by the explicit
first-pullback separation radius `51 / 100`. -/
theorem volume_filledJulia_eq_zero_of_three_le_norm {c : ℂ} (hc : (3 : ℝ) ≤ ‖c‖) :
    volume (filledJulia c) = 0 :=
  volume_filledJulia_eq_zero_of_disjoint_ball_c_radius_gt_half
    (c := c) (N := 1) (r := (51 : ℝ) / 100) (by norm_num)
    (quadraticPreimageClosedBall_one_disjoint_ball_c_of_three_le_norm hc)

/-- Parameters with `‖c‖ ≥ 73 / 25` give Lebesgue-null filled Julia sets by the explicit
first-pullback separation radius `501 / 1000`. -/
theorem volume_filledJulia_eq_zero_of_seventy_three_div_twenty_five_le_norm {c : ℂ}
    (hc : ((73 : ℝ) / 25) ≤ ‖c‖) :
    volume (filledJulia c) = 0 :=
  volume_filledJulia_eq_zero_of_disjoint_ball_c_radius_gt_half
    (c := c) (N := 1) (r := (501 : ℝ) / 1000) (by norm_num)
    (quadraticPreimageClosedBall_one_disjoint_ball_c_of_seventy_three_div_twenty_five_le_norm hc)

end

end Bottcher
