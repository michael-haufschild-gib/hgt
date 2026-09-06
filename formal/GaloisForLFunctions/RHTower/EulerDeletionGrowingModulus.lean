import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleConvergence
import GaloisForLFunctions.RHTower.DirichletUniformAbel

/-!
# Exact growing-modulus admission for literal deletion prefixes

For `0 < Re(s) <= 1`, the tails of all modulus-`q+1` deletion prefixes with
`q <= A(N)` vanish uniformly after cutoff `N` if and only if
`A(N) * (N+1)^(-Re(s))` tends to zero. No growth or monotonicity restriction
on `A` is assumed. For arbitrary `Re(s) > 0`, the same equivalence holds
when `A(N) <= N`.

A block Abel estimate supplies the upper bound. The first deletion event after
any cutoff supplies a matching lower bound. Consequently all-modulus uniformity
fails throughout the critical strip, independently of the value of zeta.
This is a periodic-series admission result, not an RH criterion or a new zero law.
-/

noncomputable section
open Filter Topology
open scoped BigOperators
namespace RHTower.DeletionModulusBoundary

/-- First `N` literal weighted jumps for actual modulus `q+1`. -/
abbrev deletionPrefix (q : ℕ) (s : ℂ) (N : ℕ) : ℂ :=
  GaloisForLFunctions.RHTower.dirichletPartialSum
    (eulerDeletionDirichletCoefficient q) N s

/-- One bound for every pair of tails and every modulus within a finite budget. -/
def TailBound (s : ℂ) (N A : ℕ) (ε : ℝ) : Prop :=
  ∀ q ≤ A, ∀ M ≥ N, ∀ K ≥ N, ‖deletionPrefix q s K - deletionPrefix q s M‖ ≤ ε

/-- Uniform Cauchy tails with a cutoff-dependent modulus budget. -/
def UniformTails (s : ℂ) (A : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, TailBound s N (A N) ε

/-- The finite block estimate is uniform over every modulus within the stated budget. -/
theorem tail_upper {s : ℂ} (hs : 0 < s.re) (N A : ℕ) :
    TailBound s N A (2 * (1 + ‖s‖ / s.re) *
      ((A : ℝ) * ((N : ℝ) + 1) ^ (-s.re))) := by
  have hbase : ∀ q ≤ A, ∀ M ≥ N, ∀ K ≥ M,
      ‖deletionPrefix q s K - deletionPrefix q s M‖ ≤
        2 * (1 + ‖s‖ / s.re) * ((A : ℝ) * ((N : ℝ) + 1) ^ (-s.re)) := by
    intro q hq M hM K hK
    have hb := GaloisForLFunctions.RHTower.norm_dirichletPartialSum_sub_le
      (eulerDeletionDirichletCoefficient_partialSum_norm_le q) hs hK
    have hp := Real.rpow_le_rpow_of_nonpos
      (show (0 : ℝ) < (N : ℝ) + 1 by positivity)
      (show (N : ℝ) + 1 ≤ (M : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right hM 1)
      (neg_nonpos.mpr hs.le)
    have hqR : (q : ℝ) ≤ A := by exact_mod_cast hq
    change ‖deletionPrefix q s K - deletionPrefix q s M‖ ≤ _ at hb
    calc
      ‖deletionPrefix q s K - deletionPrefix q s M‖ ≤
          2 * q * (1 + ‖s‖ / s.re) * ((M : ℝ) + 1) ^ (-s.re) := hb
      _ ≤ 2 * (1 + ‖s‖ / s.re) * ((A : ℝ) * ((N : ℝ) + 1) ^ (-s.re)) := by
        nlinarith [mul_le_mul hqR hp (Real.rpow_nonneg (by positivity) _) (by positivity : (0 : ℝ) ≤ A),
          show 0 ≤ 1 + ‖s‖ / s.re by positivity]
  intro q hq M hM K hK
  rcases le_total M K with h | h
  · exact hbase q hq M hM K h
  · rw [norm_sub_rev]
    exact hbase q hq K hK M h

/-- The first deletion after any cutoff occurs within one block. -/
theorem next_deletion (N q : ℕ) :
    ∃ k : ℕ, N < k ∧ k ≤ N + q + 1 ∧ q + 1 ∣ k := by
  refine ⟨(N / (q + 1) + 1) * (q + 1), ?_, ?_, by simp⟩
  · have hm := Nat.mod_lt N (Nat.succ_pos q)
    have he := Nat.mod_add_div N (q + 1)
    nlinarith
  · have hd := Nat.div_mul_le_self N (q + 1)
    nlinarith

/-- At a deletion event, the jump has its exact large norm. -/
theorem deletion_jump_norm (q k : ℕ) (s : ℂ) (hk : 0 < k) (hd : q + 1 ∣ k) :
    ‖deletionPrefix q s k - deletionPrefix q s (k - 1)‖ = (q : ℝ) * (k : ℝ) ^ (-s.re) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simp only [Nat.succ_sub_one, deletionPrefix,
    GaloisForLFunctions.RHTower.dirichletPartialSum, Finset.sum_range_succ, add_sub_cancel_left]
  have hc : eulerDeletionDirichletCoefficient q j = -(q : ℂ) := by
    simp [eulerDeletionDirichletCoefficient, blockDeletionCoefficient, hd]
  rw [hc, norm_mul, norm_neg, Complex.norm_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]
  simp

/-- A uniform tail bound must pay for an actual deletion within the next block. -/
theorem tail_lower {s : ℂ} (hs : 0 < s.re) {N A : ℕ} (hAN : A ≤ N)
    {ε : ℝ} (hε : TailBound s N A ε) :
    (A : ℝ) * (2 * ((N : ℝ) + 1)) ^ (-s.re) ≤ ε := by
  obtain ⟨k, hNk, hk, hd⟩ := next_deletion N A
  have hh := hε A le_rfl (k - 1) (by omega) k (by omega)
  rw [deletion_jump_norm A k s (by omega) hd] at hh
  have hkr : (k : ℝ) ≤ 2 * ((N : ℝ) + 1) := by exact_mod_cast (show k ≤ 2 * (N + 1) by omega)
  exact (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (show 0 < k by omega)) hkr
      (neg_nonpos.mpr hs.le)) (Nat.cast_nonneg A)).trans hh

/-- Exact admission criterion for a growing modulus budget bounded by the cutoff. -/
theorem uniformTails_iff_budget_decay {s : ℂ} (hs : 0 < s.re)
    (A : ℕ → ℕ) (hA : ∀ N, A N ≤ N) :
    UniformTails s A ↔
      Tendsto (fun N => (A N : ℝ) * ((N : ℝ) + 1) ^ (-s.re)) atTop (nhds 0) := by
  constructor
  · intro hu
    apply tendsto_order.2
    constructor
    · intro b hb
      exact Filter.Eventually.of_forall fun N => hb.trans_le (by positivity)
    · intro b hb
      have hd : 0 < (2 : ℝ) ^ (-s.re) := Real.rpow_pos_of_pos (by norm_num) _
      filter_upwards [hu ((2 : ℝ) ^ (-s.re) * b / 2) (by positivity)] with N hN
      have hl := tail_lower hs (hA N) hN
      rw [Real.mul_rpow (by norm_num) (by positivity)] at hl
      nlinarith
  · intro ht ε hε
    have ht' : Tendsto (fun N => 2 * (1 + ‖s‖ / s.re) *
        ((A N : ℝ) * ((N : ℝ) + 1) ^ (-s.re))) atTop (nhds 0) := by
      simpa using ht.const_mul (2 * (1 + ‖s‖ / s.re))
    filter_upwards [ht'.eventually (gt_mem_nhds hε)] with N hN
    intro q hq M hM K hK
    exact (tail_upper hs N (A N) q hq M hM K hK).trans hN.le

/-- A cutoff-scale budget carries a fixed positive tail oscillation when Re(s) <= 1. -/
theorem cutoff_tail_floor {s : ℂ} (hs : 0 < s.re) (hs1 : s.re ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : TailBound s N N ε) :
    (2 : ℝ) ^ (-s.re) / 2 ≤ ε := by
  have hl := tail_lower hs (le_refl N) hε
  rw [Real.mul_rpow (by norm_num) (by positivity)] at hl
  have hd : 0 < (2 : ℝ) ^ (-s.re) := Real.rpow_pos_of_pos (by norm_num) _
  have hnr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hb : 1 / 2 ≤ (N : ℝ) * ((N : ℝ) + 1) ^ (-s.re) := by
    calc
      (1 : ℝ) / 2 ≤ (N : ℝ) / ((N : ℝ) + 1) :=
        (le_div_iff₀ (by positivity)).2 (by linarith)
      _ = (N : ℝ) * ((N : ℝ) + 1) ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one, div_eq_mul_inv]
      _ ≤ (N : ℝ) * ((N : ℝ) + 1) ^ (-s.re) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg hs1))
          (Nat.cast_nonneg N)
  nlinarith

/-- Uniform tails force the budget below the cutoff eventually in the critical strip. -/
theorem budget_eventually_lt_cutoff {s : ℂ} (hs : 0 < s.re) (hs1 : s.re ≤ 1)
    {A : ℕ → ℕ} (hu : UniformTails s A) : ∀ᶠ N in atTop, A N < N := by
  have hd : 0 < (2 : ℝ) ^ (-s.re) := Real.rpow_pos_of_pos (by norm_num) _
  filter_upwards [hu ((2 : ℝ) ^ (-s.re) / 4) (by positivity),
    eventually_ge_atTop 1] with N hN hN1
  by_contra h
  have hNA : N ≤ A N := Nat.le_of_not_gt h
  have hf := cutoff_tail_floor hs hs1 hN1
    (show TailBound s N N ((2 : ℝ) ^ (-s.re) / 4) from
      fun q hq M hM K hK => hN q (hq.trans hNA) M hM K hK)
  linarith

/-- For arbitrary budgets, the same rate is necessary and sufficient in the critical strip. -/
theorem uniformTails_iff_budget_decay_critical {s : ℂ} (hs : 0 < s.re)
    (hs1 : s.re ≤ 1) (A : ℕ → ℕ) :
    UniformTails s A ↔
      Tendsto (fun N => (A N : ℝ) * ((N : ℝ) + 1) ^ (-s.re)) atTop (nhds 0) := by
  constructor
  · intro hu
    have hmin : UniformTails s (fun N => min (A N) N) := by
      intro ε hε
      filter_upwards [hu ε hε] with N hN
      exact fun q hq M hM K hK => hN q (hq.trans (min_le_left _ _)) M hM K hK
    have ht := (uniformTails_iff_budget_decay hs (fun N => min (A N) N)
      (fun N => min_le_right _ _)).1 hmin
    apply ht.congr'
    filter_upwards [budget_eventually_lt_cutoff hs hs1 hu] with N hN
    rw [min_eq_left hN.le]
  · intro ht ε hε
    have ht' : Tendsto (fun N => 2 * (1 + ‖s‖ / s.re) *
        ((A N : ℝ) * ((N : ℝ) + 1) ^ (-s.re))) atTop (nhds 0) := by
      simpa using ht.const_mul (2 * (1 + ‖s‖ / s.re))
    filter_upwards [ht'.eventually (gt_mem_nhds hε)] with N hN
    exact fun q hq M hM K hK => (tail_upper hs N (A N) q hq M hM K hK).trans hN.le

/-- Every cutoff-scale budget fails in the closed critical strip. -/
theorem not_uniformTails_cutoff {s : ℂ} (hs : 0 < s.re) (hs1 : s.re ≤ 1) :
    ¬ UniformTails s (fun N => N) := by
  intro hu
  have h := budget_eventually_lt_cutoff hs hs1 hu
  obtain ⟨N, hN⟩ := Filter.Eventually.exists h
  exact (lt_irrefl N) hN

/-- In particular no single cutoff controls all deletion moduli in the critical strip. -/
theorem not_all_moduli_uniform {s : ℂ} (hs : 0 < s.re) (hs1 : s.re ≤ 1) :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ q M K : ℕ,
      N ≤ M → N ≤ K → ‖deletionPrefix q s K - deletionPrefix q s M‖ ≤ ε) := by
  intro h
  apply not_uniformTails_cutoff hs hs1
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := h ε hε
  filter_upwards [eventually_ge_atTop N₀] with N hN
  intro q _ M hM K hK
  exact hN₀ q M K (hN.trans hM) (hN.trans hK)

end RHTower.DeletionModulusBoundary
