import GaloisForLFunctions.RHTower.ShiftedDirichletPolynomialUniqueness
import GaloisForLFunctions.HTGeometry.GreedyPhaseL2
import GaloisForLFunctions.HTGeometry.CauchyCircleAverageBound

/-!
# A target configuration with an isolated zero

Let `β_n(z) = b_n (n+α)^{-z}`, `α > 0`, with `Σ_n ∫₀^{2π} |β_n(c₀ + R₂e^{iθ})|² dθ < ∞`.  Beyond an index
`N₀`, group the terms into consecutive blocks whose circle `L²`-masses are at most `4^{-k}`, and choose unit
phases greedily inside each block.  The block sums are then `≤ (R₂/(R₂-R)) 2^{-k}` on the closed disc of
radius `R`, so the phased tail converges uniformly there.  If the polygon condition
`12B + 3|tail(c₀)| ≤ Σ_{n<N₀} |β_n(c₀)|` holds, the first `N₀` phases can be chosen to make the whole sum
vanish at `c₀`; two such choices differ by a nonzero shifted Dirichlet polynomial, so one of them is not
identically zero near `c₀` and has an isolated zero there.
-/

open Complex Real Filter Topology Metric
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

variable {α : ℝ}

/-- The terms `β_n(z) = b_n (n+α)^{-z}`. -/
def shiftedTerm (α : ℝ) (b : ℕ → ℂ) (n : ℕ) (z : ℂ) : ℂ := b n * (((n : ℝ) + α : ℝ) : ℂ) ^ (-z)

theorem differentiable_shiftedTerm (hα : 0 < α) (b : ℕ → ℂ) (n : ℕ) :
    Differentiable ℂ (shiftedTerm α b n) := by
  intro z
  have hne : (((n : ℝ) + α : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) + α := by positivity
    exact_mod_cast this.ne'
  exact (differentiableAt_const _).mul ((differentiableAt_id.neg).const_cpow (Or.inl hne))

/-- The circle trace `θ ↦ β_n(c₀ + R₂ e^{iθ})`. -/
def shiftedTrace (α : ℝ) (b : ℕ → ℂ) (c₀ R₂ : ℝ) (n : ℕ) (θ : ℝ) : ℂ :=
  shiftedTerm α b n (circleMap (c₀ : ℂ) R₂ θ)

theorem continuous_shiftedTrace (hα : 0 < α) (b : ℕ → ℂ) (c₀ R₂ : ℝ) (n : ℕ) :
    Continuous (shiftedTrace α b c₀ R₂ n) :=
  (differentiable_shiftedTerm hα b n).continuous.comp (continuous_circleMap _ _)

/-- `∫₀^{2π} |g| ≤ π ε + (1/(2ε)) ∫₀^{2π} |g|²`. -/
theorem integral_norm_le_of_circleMass {g : ℝ → ℂ} (hg : Continuous g) {ε : ℝ} (hε : 0 < ε) :
    ∫ θ in (0 : ℝ)..2 * π, ‖g θ‖ ≤ π * ε + 1 / (2 * ε) * circleMass g := by
  have hpt : ∀ θ, ‖g θ‖ ≤ ε / 2 + 1 / (2 * ε) * ‖g θ‖ ^ 2 := by
    intro θ
    have hid : ε / 2 + 1 / (2 * ε) * ‖g θ‖ ^ 2 - ‖g θ‖ = (‖g θ‖ - ε) ^ 2 / (2 * ε) := by
      field_simp; ring
    have : 0 ≤ (‖g θ‖ - ε) ^ 2 / (2 * ε) := by positivity
    linarith
  unfold circleMass
  calc ∫ θ in (0 : ℝ)..2 * π, ‖g θ‖ ≤ ∫ θ in (0 : ℝ)..2 * π, (ε / 2 + 1 / (2 * ε) * ‖g θ‖ ^ 2) :=
        intervalIntegral.integral_mono_on (by positivity) (hg.norm.intervalIntegrable _ _)
          ((continuous_const.add (continuous_const.mul (hg.norm.pow 2))).intervalIntegrable _ _)
          (fun θ _ => hpt θ)
    _ = π * ε + 1 / (2 * ε) * ∫ θ in (0 : ℝ)..2 * π, ‖g θ‖ ^ 2 := by
        have hi2 : IntervalIntegrable (fun θ => 1 / (2 * ε) * ‖g θ‖ ^ 2) MeasureTheory.volume 0 (2 * π) :=
          (continuous_const.mul (hg.norm.pow 2) :
            Continuous fun θ => 1 / (2 * ε) * ‖g θ‖ ^ 2).intervalIntegrable _ _
        rw [intervalIntegral.integral_add intervalIntegrable_const hi2,
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
        ring

/-- **Disc bound from circle mass.** An entire `h` with circle mass `≤ 4^{-k}` on radius `R₂` is
`≤ (R₂/(R₂-R)) 2^{-k}` on the closed disc of radius `R`. -/
theorem norm_le_of_circleMass_le {h : ℂ → ℂ} (hh : Differentiable ℂ h) {c₀ : ℂ} {R R₂ : ℝ}
    (hR : 0 ≤ R) (hRR : R < R₂) {k : ℕ}
    (hmass : circleMass (fun θ => h (circleMap c₀ R₂ θ)) ≤ (1 / 4 : ℝ) ^ k) {z : ℂ}
    (hz : z ∈ closedBall c₀ R) :
    ‖h z‖ ≤ R₂ / (R₂ - R) * (1 / 2 : ℝ) ^ k := by
  have hR₂ : 0 < R₂ := by linarith
  have hcav := norm_le_circle_average hR hRR hh.diffContOnCl (mem_closedBall.mp hz)
  have hcont : Continuous fun θ => h (circleMap c₀ R₂ θ) := hh.continuous.comp (continuous_circleMap _ _)
  have hε : (0 : ℝ) < (1 / 2) ^ k := by positivity
  have hint := integral_norm_le_of_circleMass hcont hε
  have h4 : (1 / 4 : ℝ) ^ k = ((1 / 2 : ℝ) ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hbound : ∫ θ in (0 : ℝ)..2 * π, ‖h (circleMap c₀ R₂ θ)‖ ≤ (π + 1 / 2) * (1 / 2 : ℝ) ^ k := by
    refine hint.trans ?_
    have : 1 / (2 * (1 / 2 : ℝ) ^ k) * circleMass (fun θ => h (circleMap c₀ R₂ θ)) ≤
        1 / (2 * (1 / 2 : ℝ) ^ k) * ((1 / 2 : ℝ) ^ k) ^ 2 := by
      rw [← h4]; gcongr
    have e : 1 / (2 * (1 / 2 : ℝ) ^ k) * ((1 / 2 : ℝ) ^ k) ^ 2 = 1 / 2 * (1 / 2 : ℝ) ^ k := by
      field_simp
    linarith
  have hK : 0 < R₂ / (R₂ - R) := div_pos hR₂ (by linarith)
  calc ‖h z‖ ≤ R₂ / (R₂ - R) / (2 * π) * ∫ θ in (0 : ℝ)..2 * π, ‖h (circleMap c₀ R₂ θ)‖ := hcav
    _ ≤ R₂ / (R₂ - R) / (2 * π) * ((π + 1 / 2) * (1 / 2 : ℝ) ^ k) := by gcongr
    _ ≤ R₂ / (R₂ - R) * (1 / 2 : ℝ) ^ k := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        have : (π + 1 / 2) ≤ 2 * π := by linarith [Real.pi_gt_three]
        calc R₂ / (R₂ - R) * ((π + 1 / 2) * (1 / 2 : ℝ) ^ k)
            ≤ R₂ / (R₂ - R) * ((2 * π) * (1 / 2 : ℝ) ^ k) := by gcongr
          _ = R₂ / (R₂ - R) * (1 / 2 : ℝ) ^ k * (2 * π) := by ring

section Schedule

variable (α : ℝ) (b : ℕ → ℂ) (c₀ R₂ : ℝ)

/-- Circle mass of the `n`-th term. -/
def termMass (n : ℕ) : ℝ := circleMass (shiftedTrace α b c₀ R₂ n)

/-- Tail masses `τ(N) = Σ_{n ≥ N} m_n`. -/
def tailMass (N : ℕ) : ℝ := ∑' n, termMass α b c₀ R₂ (n + N)

variable {α b c₀ R₂}

theorem termMass_nonneg (n : ℕ) : 0 ≤ termMass α b c₀ R₂ n := circleMass_nonneg _

theorem tailMass_succ (hQ : Summable (termMass α b c₀ R₂)) (N : ℕ) :
    tailMass α b c₀ R₂ N = termMass α b c₀ R₂ N + tailMass α b c₀ R₂ (N + 1) := by
  unfold tailMass
  have hs : Summable fun n => termMass α b c₀ R₂ (n + N) := (summable_nat_add_iff N).mpr hQ
  rw [hs.tsum_eq_zero_add]
  simp only [zero_add]
  congr 1
  refine tsum_congr fun n => ?_
  congr 1; ring

theorem tailMass_antitone (hQ : Summable (termMass α b c₀ R₂)) : Antitone (tailMass α b c₀ R₂) := by
  refine antitone_nat_of_succ_le fun N => ?_
  rw [tailMass_succ hQ N]; linarith [termMass_nonneg (α := α) (b := b) (c₀ := c₀) (R₂ := R₂) N]

theorem tendsto_tailMass : Tendsto (tailMass α b c₀ R₂) atTop (𝓝 0) :=
  tendsto_sum_nat_add (termMass α b c₀ R₂)

theorem sum_Ico_termMass_le (hQ : Summable (termMass α b c₀ R₂)) (M M' : ℕ) :
    ∑ n ∈ Finset.Ico M M', termMass α b c₀ R₂ n ≤ tailMass α b c₀ R₂ M := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hs : Summable fun n => termMass α b c₀ R₂ (n + M) := (summable_nat_add_iff M).mpr hQ
  calc ∑ k ∈ Finset.range (M' - M), termMass α b c₀ R₂ (M + k)
      = ∑ k ∈ Finset.range (M' - M), termMass α b c₀ R₂ (k + M) :=
        Finset.sum_congr rfl fun n _ => by rw [add_comm]
    _ ≤ ∑' k, termMass α b c₀ R₂ (k + M) := hs.sum_le_tsum _ (fun n _ => termMass_nonneg _)
    _ = tailMass α b c₀ R₂ M := rfl

variable (α b c₀ R₂)

/-- The least index with tail mass `≤ 4^{-k}`. -/
def schedIdx (k : ℕ) : ℕ := by
  classical
  exact if h : ∃ N, tailMass α b c₀ R₂ N ≤ (1 / 4 : ℝ) ^ k then Nat.find h else 0

/-- The block boundaries `N_0 = N₀ < N_1 < …`. -/
def sched (N₀ : ℕ) : ℕ → ℕ
  | 0 => N₀
  | k + 1 => N₀ + schedIdx α b c₀ R₂ (k + 1) + (k + 1)

variable {α b c₀ R₂}

theorem schedIdx_spec (k : ℕ) :
    tailMass α b c₀ R₂ (schedIdx α b c₀ R₂ k) ≤ (1 / 4 : ℝ) ^ k := by
  classical
  have hex : ∃ N, tailMass α b c₀ R₂ N ≤ (1 / 4 : ℝ) ^ k := by
    have hpos : (0 : ℝ) < (1 / 4 : ℝ) ^ k := by positivity
    obtain ⟨N, hN⟩ := (tendsto_order.mp tendsto_tailMass).2 _ hpos |>.exists
    exact ⟨N, hN.le⟩
  unfold schedIdx
  rw [dif_pos hex]
  exact Nat.find_spec hex

theorem schedIdx_mono {j k : ℕ} (h : j ≤ k) :
    schedIdx α b c₀ R₂ j ≤ schedIdx α b c₀ R₂ k := by
  classical
  have hexk : ∃ N, tailMass α b c₀ R₂ N ≤ (1 / 4 : ℝ) ^ k := ⟨_, schedIdx_spec k⟩
  have hexj : ∃ N, tailMass α b c₀ R₂ N ≤ (1 / 4 : ℝ) ^ j := ⟨_, schedIdx_spec j⟩
  unfold schedIdx
  rw [dif_pos hexk, dif_pos hexj]
  refine Nat.find_mono fun N hN => hN.trans ?_
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h

theorem sched_strictMono (N₀ : ℕ) :
    StrictMono (sched α b c₀ R₂ N₀) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  cases k with
  | zero => simp [sched]
  | succ k =>
    simp only [sched]
    have := schedIdx_mono (α := α) (b := b) (c₀ := c₀) (R₂ := R₂) (show k + 1 ≤ k + 1 + 1 by omega)
    omega

theorem sched_ge (N₀ k : ℕ) : N₀ ≤ sched α b c₀ R₂ N₀ k := by
  cases k with
  | zero => simp [sched]
  | succ k => simp only [sched]; omega

theorem tailMass_sched_le (hQ : Summable (termMass α b c₀ R₂)) {N₀ : ℕ}
    (h₀ : tailMass α b c₀ R₂ N₀ ≤ 1) (k : ℕ) :
    tailMass α b c₀ R₂ (sched α b c₀ R₂ N₀ k) ≤ (1 / 4 : ℝ) ^ k := by
  cases k with
  | zero => simpa [sched] using h₀
  | succ k =>
    refine (tailMass_antitone hQ (show schedIdx α b c₀ R₂ (k + 1) ≤ sched α b c₀ R₂ N₀ (k + 1) by
      simp only [sched]; omega)).trans (schedIdx_spec (k + 1))

end Schedule

section Blocks

variable (α : ℝ) (b : ℕ → ℂ) (c₀ R₂ : ℝ)

/-- The `k`-th block sum with phases `U k`. -/
private def blockSum (U : ℕ → ℕ → ℂ) (N₀ k : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ico (sched α b c₀ R₂ N₀ k) (sched α b c₀ R₂ N₀ (k + 1)), U k n * shiftedTerm α b n z

/-- The phased tail `Σ_k B_k(z)`. -/
def phasedTail (U : ℕ → ℕ → ℂ) (N₀ : ℕ) (z : ℂ) : ℂ := ∑' k, blockSum α b c₀ R₂ U N₀ k z

/-- The block containing `n`. -/
def blockOf (N₀ n : ℕ) : ℕ := by
  classical
  exact if h : ∃ k, n < sched α b c₀ R₂ N₀ (k + 1) then Nat.find h else 0

/-- The combined phases: `v n` below `N₀`, block phases above. -/
def combinedPhase (U : ℕ → ℕ → ℂ) (N₀ : ℕ) (v : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n < N₀ then v n else U (blockOf α b c₀ R₂ N₀ n) n

variable {α b c₀ R₂}

theorem blockOf_eq {N₀ k n : ℕ} (hlo : sched α b c₀ R₂ N₀ k ≤ n)
    (hhi : n < sched α b c₀ R₂ N₀ (k + 1)) : blockOf α b c₀ R₂ N₀ n = k := by
  classical
  have hex : ∃ j, n < sched α b c₀ R₂ N₀ (j + 1) := ⟨k, hhi⟩
  unfold blockOf
  rw [dif_pos hex]
  have hmono := sched_strictMono (α := α) (b := b) (c₀ := c₀) (R₂ := R₂) N₀
  apply le_antisymm
  · exact Nat.find_min' hex hhi
  · by_contra hlt
    push Not at hlt
    have hspec := Nat.find_spec hex
    have : sched α b c₀ R₂ N₀ (Nat.find hex + 1) ≤ sched α b c₀ R₂ N₀ k :=
      hmono.monotone (by omega)
    omega

theorem blockSum_eq_combined (U : ℕ → ℕ → ℂ) (N₀ : ℕ) (v : ℕ → ℂ) (k : ℕ) (z : ℂ) :
    blockSum α b c₀ R₂ U N₀ k z = ∑ n ∈ Finset.Ico (sched α b c₀ R₂ N₀ k) (sched α b c₀ R₂ N₀ (k + 1)),
      combinedPhase α b c₀ R₂ U N₀ v n * shiftedTerm α b n z := by
  unfold blockSum
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Ico] at hn
  have hge := sched_ge (α := α) (b := b) (c₀ := c₀) (R₂ := R₂) N₀ k
  unfold combinedPhase
  rw [if_neg (by omega), blockOf_eq hn.1 hn.2]

/-- **Partial sums along the block boundaries.** -/
theorem sum_sched_eq (U : ℕ → ℕ → ℂ) (N₀ : ℕ) (v : ℕ → ℂ) (k : ℕ) (z : ℂ) :
    ∑ n ∈ Finset.range (sched α b c₀ R₂ N₀ k), combinedPhase α b c₀ R₂ U N₀ v n * shiftedTerm α b n z =
      ∑ n ∈ Finset.range N₀, v n * shiftedTerm α b n z +
        ∑ j ∈ Finset.range k, blockSum α b c₀ R₂ U N₀ j z := by
  induction k with
  | zero =>
    simp only [sched, Finset.range_zero, Finset.sum_empty, add_zero]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_range] at hn
    simp [combinedPhase, hn]
  | succ k ih =>
    have hle : sched α b c₀ R₂ N₀ k ≤ sched α b c₀ R₂ N₀ (k + 1) :=
      (sched_strictMono N₀).monotone (Nat.le_succ k)
    rw [← Finset.sum_range_add_sum_Ico _ hle, ih, Finset.sum_range_succ, blockSum_eq_combined U N₀ v k z]
    ring

/-- **Uniform block bound.** -/
private theorem norm_blockSum_le (hα : 0 < α) {U : ℕ → ℕ → ℂ} {N₀ : ℕ} {R : ℝ} (hR : 0 ≤ R) (hRR : R < R₂)
    (hmass : ∀ k, circleMass (fun θ => blockSum α b c₀ R₂ U N₀ k (circleMap (c₀ : ℂ) R₂ θ)) ≤
      (1 / 4 : ℝ) ^ k) (k : ℕ) {z : ℂ} (hz : z ∈ closedBall (c₀ : ℂ) R) :
    ‖blockSum α b c₀ R₂ U N₀ k z‖ ≤ R₂ / (R₂ - R) * (1 / 2 : ℝ) ^ k := by
  have hd : Differentiable ℂ (blockSum α b c₀ R₂ U N₀ k) := by
    intro w
    unfold blockSum
    exact DifferentiableAt.fun_sum fun n _ =>
      (differentiableAt_const _).mul (differentiable_shiftedTerm hα b n w)
  exact norm_le_of_circleMass_le hd hR hRR (hmass k) hz

theorem summable_blockBound (R : ℝ) :
    Summable fun k : ℕ => R₂ / (R₂ - R) * (1 / 2 : ℝ) ^ k :=
  (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

/-- **The phased tail is holomorphic** on the open disc. -/
theorem differentiableOn_phasedTail (hα : 0 < α) {U : ℕ → ℕ → ℂ} {N₀ : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (hRR : R < R₂)
    (hmass : ∀ k, circleMass (fun θ => blockSum α b c₀ R₂ U N₀ k (circleMap (c₀ : ℂ) R₂ θ)) ≤
      (1 / 4 : ℝ) ^ k) :
    DifferentiableOn ℂ (phasedTail α b c₀ R₂ U N₀) (ball (c₀ : ℂ) R) := by
  unfold phasedTail
  refine differentiableOn_tsum_of_summable_norm (summable_blockBound (R₂ := R₂) R) (fun k => ?_) isOpen_ball
    (fun k w hw => norm_blockSum_le hα hR hRR hmass k (ball_subset_closedBall hw))
  intro w _
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold blockSum
  exact DifferentiableAt.fun_sum fun n _ =>
    (differentiableAt_const _).mul (differentiable_shiftedTerm hα b n w)

/-- **Tail remainder.** -/
theorem norm_phasedTail_sub_le (hα : 0 < α) {U : ℕ → ℕ → ℂ} {N₀ : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (hRR : R < R₂)
    (hmass : ∀ k, circleMass (fun θ => blockSum α b c₀ R₂ U N₀ k (circleMap (c₀ : ℂ) R₂ θ)) ≤
      (1 / 4 : ℝ) ^ k) (k : ℕ) {z : ℂ} (hz : z ∈ closedBall (c₀ : ℂ) R) :
    ‖phasedTail α b c₀ R₂ U N₀ z - ∑ j ∈ Finset.range k, blockSum α b c₀ R₂ U N₀ j z‖ ≤
      2 * (R₂ / (R₂ - R)) * (1 / 2 : ℝ) ^ k := by
  have hbd : ∀ j, ‖blockSum α b c₀ R₂ U N₀ j z‖ ≤ R₂ / (R₂ - R) * (1 / 2 : ℝ) ^ j :=
    fun j => norm_blockSum_le hα hR hRR hmass j hz
  have hsum : Summable fun j => blockSum α b c₀ R₂ U N₀ j z :=
    Summable.of_norm_bounded (summable_blockBound (R₂ := R₂) R) hbd
  unfold phasedTail
  rw [← hsum.sum_add_tsum_nat_add k, add_sub_cancel_left]
  have hs' : Summable fun j => ‖blockSum α b c₀ R₂ U N₀ (j + k) z‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => hbd (j + k))
      ((summable_nat_add_iff k).mpr (summable_blockBound (R₂ := R₂) R))
  refine (norm_tsum_le_tsum_norm hs').trans ?_
  have hgeo : ∑' j : ℕ, R₂ / (R₂ - R) * (1 / 2 : ℝ) ^ (j + k) = 2 * (R₂ / (R₂ - R)) * (1 / 2 : ℝ) ^ k := by
    simp_rw [pow_add]
    rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    ring
  rw [← hgeo]
  exact hs'.tsum_le_tsum (fun j => hbd (j + k))
    ((summable_nat_add_iff k).mpr (summable_blockBound (R₂ := R₂) R))

end Blocks

/-- **The target.** Under the polygon condition at `c₀` there are unit phases `u` and a function `f`,
holomorphic on the disc of radius `R`, with an isolated zero at `c₀` (nonvanishing on a small sphere),
which is the uniform limit on the closed disc of the phased partial sums along the block boundaries. -/
theorem exists_shifted_target (hα : 0 < α) (b : ℕ → ℂ) (c₀ : ℝ) {R R₂ : ℝ} (hR : 0 < R) (hRR : R < R₂)
    (hQ : Summable (termMass α b c₀ R₂)) {N₀ : ℕ} (h₀ : tailMass α b c₀ R₂ N₀ ≤ 1) {B : ℝ} (hB : 0 < B)
    (hbound : ∀ n < N₀, ‖shiftedTerm α b n c₀‖ ≤ B)
    (hmass : 12 * B + 6 * (R₂ / (R₂ - R)) ≤ ∑ n ∈ Finset.range N₀, ‖shiftedTerm α b n c₀‖) :
    ∃ (u : ℕ → ℂ) (f : ℂ → ℂ) (r : ℝ), (∀ n, ‖u n‖ = 1) ∧ DifferentiableOn ℂ f (ball (c₀ : ℂ) R) ∧
      f c₀ = 0 ∧ 0 < r ∧ r < R ∧ (∀ z ∈ sphere (c₀ : ℂ) r, f z ≠ 0) ∧
      ∀ k, ∀ z ∈ closedBall (c₀ : ℂ) R,
        ‖f z - ∑ n ∈ Finset.range (sched α b c₀ R₂ N₀ k), u n * shiftedTerm α b n z‖ ≤
          2 * (R₂ / (R₂ - R)) * (1 / 2 : ℝ) ^ k := by
  classical
  -- greedy block phases
  choose U hU hUmass using fun k => exists_unit_phases_circleMass_le (shiftedTrace α b c₀ R₂)
    (continuous_shiftedTrace hα b c₀ R₂)
    (Finset.Ico (sched α b c₀ R₂ N₀ k) (sched α b c₀ R₂ N₀ (k + 1)))
  have hmassk : ∀ k, circleMass (fun θ => blockSum α b c₀ R₂ U N₀ k (circleMap (c₀ : ℂ) R₂ θ)) ≤
      (1 / 4 : ℝ) ^ k := by
    intro k
    refine (hUmass k).trans ?_
    refine (sum_Ico_termMass_le hQ _ _).trans ?_
    exact tailMass_sched_le hQ h₀ k
  set K₁ : ℝ := R₂ / (R₂ - R) with hK₁
  have hK₁0 : 0 < K₁ := div_pos (by linarith) (by linarith)
  set T₀ : ℂ := phasedTail α b c₀ R₂ U N₀ c₀ with hT₀
  have hT₀n : ‖T₀‖ ≤ 2 * K₁ := by
    have h := norm_phasedTail_sub_le hα hR.le hRR hmassk 0 (z := (c₀ : ℂ)) (mem_closedBall_self hR.le)
    simpa using h
  -- polygon closure of the first `N₀` phases
  set w : ℕ → ℂ := fun n => shiftedTerm α b n c₀ with hw
  have hpoly : 12 * B + 3 * ‖-T₀‖ ≤ prefixMass w N₀ := by
    rw [norm_neg]; unfold prefixMass
    linarith
  obtain ⟨v₁, v₂, hv₁, hv₂, hs₁, hs₂, n₀, hn₀, hwn₀, hne⟩ :=
    exists_two_unit_polygons w N₀ (-T₀) hB (fun n hn => hbound n hn) hpoly
  set f : (ℕ → ℂ) → ℂ → ℂ := fun v z =>
    ∑ n ∈ Finset.range N₀, v n * shiftedTerm α b n z + phasedTail α b c₀ R₂ U N₀ z with hf
  have hfd : ∀ v, DifferentiableOn ℂ (f v) (ball (c₀ : ℂ) R) := by
    intro v
    refine DifferentiableOn.add ?_ (differentiableOn_phasedTail hα hR.le hRR hmassk)
    intro z _
    exact (DifferentiableAt.fun_sum fun n _ =>
      (differentiableAt_const _).mul (differentiable_shiftedTerm hα b n z)).differentiableWithinAt
  have hf0 : ∀ v : ℕ → ℂ, ∑ n ∈ Finset.range N₀, v n * w n = -T₀ → f v c₀ = 0 := by
    intro v hv
    simp only [hf]
    have : ∑ n ∈ Finset.range N₀, v n * shiftedTerm α b n c₀ = -T₀ := hv
    rw [this, ← hT₀]; ring
  -- one of the two is not locally zero
  have hnot : ¬ ((f v₁ =ᶠ[𝓝 (c₀ : ℂ)] 0) ∧ (f v₂ =ᶠ[𝓝 (c₀ : ℂ)] 0)) := by
    rintro ⟨h1, h2⟩
    have hdiff : shiftedDirichletPoly α N₀ (fun n => (v₁ n - v₂ n) * b n) =ᶠ[𝓝 (c₀ : ℂ)] 0 := by
      filter_upwards [h1, h2] with z hz1 hz2
      simp only [hf, Pi.zero_apply] at hz1 hz2
      simp only [shiftedDirichletPoly, Pi.zero_apply]
      have : ∑ n ∈ Finset.range N₀, (v₁ n - v₂ n) * b n * (((n : ℝ) + α : ℝ) : ℂ) ^ (-z) =
          ∑ n ∈ Finset.range N₀, v₁ n * shiftedTerm α b n z -
            ∑ n ∈ Finset.range N₀, v₂ n * shiftedTerm α b n z := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun n _ => ?_
        simp only [shiftedTerm]; ring
      rw [this]
      linear_combination hz1 - hz2
    have hc := shiftedDirichletPoly_coeff_eq_zero hα hdiff n₀ hn₀
    have hb0 : b n₀ = 0 := by
      rcases mul_eq_zero.mp hc with h | h
      · exact absurd (sub_eq_zero.mp h) hne
      · exact h
    apply hwn₀
    simp [hw, shiftedTerm, hb0]
  have hchoice : ∃ v : ℕ → ℂ, (∀ n, ‖v n‖ = 1) ∧ ∑ n ∈ Finset.range N₀, v n * w n = -T₀ ∧
      ¬ (f v =ᶠ[𝓝 (c₀ : ℂ)] 0) := by
    by_cases h1 : f v₁ =ᶠ[𝓝 (c₀ : ℂ)] 0
    · exact ⟨v₂, hv₂, hs₂, fun h2 => hnot ⟨h1, h2⟩⟩
    · exact ⟨v₁, hv₁, hs₁, h1⟩
  obtain ⟨v, hv, hvs, hvnz⟩ := hchoice
  have hanal : AnalyticAt ℂ (f v) (c₀ : ℂ) := (hfd v).analyticAt (isOpen_ball.mem_nhds (mem_ball_self hR))
  have hiso : ∀ᶠ z in 𝓝[≠] (c₀ : ℂ), f v z ≠ 0 :=
    (hanal.eventually_eq_zero_or_eventually_ne_zero).resolve_left hvnz
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hiso
  obtain ⟨ε, hε, hεball⟩ := hiso
  set r : ℝ := min ε R / 2 with hr
  have hr0 : 0 < r := by rw [hr]; exact half_pos (lt_min hε hR)
  have hrR : r < R := by rw [hr]; linarith [min_le_right ε R]
  have hrε : r < ε := by rw [hr]; linarith [min_le_left ε R]
  refine ⟨combinedPhase α b c₀ R₂ U N₀ v, f v, r, fun n => ?_, hfd v, hf0 v hvs, hr0, hrR, ?_, ?_⟩
  · unfold combinedPhase; split_ifs
    · exact hv n
    · exact hU _ n
  · intro z hz
    rw [mem_sphere] at hz
    refine hεball (by rw [hz]; exact hrε) ?_
    intro hzc
    rw [Set.mem_singleton_iff] at hzc
    rw [hzc, dist_self] at hz
    linarith
  · intro k z hz
    rw [sum_sched_eq U N₀ v k z]
    simp only [hf]
    rw [show ∑ n ∈ Finset.range N₀, v n * shiftedTerm α b n z + phasedTail α b c₀ R₂ U N₀ z -
        (∑ n ∈ Finset.range N₀, v n * shiftedTerm α b n z +
          ∑ j ∈ Finset.range k, blockSum α b c₀ R₂ U N₀ j z) =
        phasedTail α b c₀ R₂ U N₀ z - ∑ j ∈ Finset.range k, blockSum α b c₀ R₂ U N₀ j z by ring]
    exact norm_phasedTail_sub_le hα hR.le hRR hmassk k hz

end

end RHTower
