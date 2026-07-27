import GaloisForLFunctions.RHTower.HighExponentShellClockMeasure
import GaloisForLFunctions.RHTower.ArithmeticSchurExactNormRiggingNoGo
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Orthogonal replication of the zeta divisor and the scalar assembly boundary

The high-exponent shells give infinitely many pairwise disjoint nonnegative arithmetic sources.
Every shell of exponent at least twelve has the same strict right-half-plane divisor as completed
zeta, with multiplicity, and the same unit-rate exponential critical clock law.

This file adds the exact operator boundary needed to interpret the family.  The unit-residue scalar
codiagonal on finite shell-label packets is not sequentially closable in the Hilbert label space
`ℓ²(ℕ, ℝ)`.  Its graph-null sequence is the uniform average of the first `n + 1` shell labels:
its `ℓ²` norm tends to zero while its scalar response is identically one.  Thus a closed assembly
of the replicated divisor currents cannot erase the shell label through a unit-weight scalar row.

No zero-location hypothesis, RH assumption, or numerical computation is used.
-/

open Filter Topology
open scoped BigOperators ENNReal NNReal

namespace RHTower

noncomputable section

/-! ## Pairwise disjoint positive sectors -/

/-- Distinct shell indicators have pointwise-zero product.  This is the exact algebraic
orthogonality statement behind every diagonal weighted Hilbert realization of the shells. -/
theorem shellIndicator_mul_eq_zero_of_ne {m k n : ℕ} (hmk : m ≠ k) :
    shellIndicator m n * shellIndicator k n = 0 := by
  by_cases hm : shellIndicator m n = 0
  · simp [hm]
  · rw [shellIndicator_eq_zero_of_ne hmk hm, mul_zero]

/-! ## Unit-residue scalar assembly -/

/-- Hilbert space of square-summable real shell labels. -/
abbrev ShellLabelHilbert := lp (fun _ : ℕ => ℝ) 2

/-- Isometric coordinate inclusion of finite shell-label packets into `ℓ²(ℕ, ℝ)`. -/
def shellLabelEmbedding : (ℕ →₀ ℝ) →ₗ[ℝ] ShellLabelHilbert :=
  Finsupp.lsum ℝ fun m =>
    LinearMap.toSpanSingleton ℝ ShellLabelHilbert (lp.single 2 m (1 : ℝ))

/-- Unit-residue scalar codiagonal on finite shell-label packets. -/
def shellCodiagonal : (ℕ →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.lsum ℝ fun _ => LinearMap.id

@[simp] theorem shellLabelEmbedding_apply (f : ℕ →₀ ℝ) (k : ℕ) :
    shellLabelEmbedding f k = f k := by
  classical
  rw [shellLabelEmbedding, Finsupp.lsum_apply]
  change (f.sum fun m c => c • lp.single 2 m (1 : ℝ)) k = f k
  simp only [Finsupp.sum, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply]
  simp [lp.single_apply, Pi.single_apply, Finsupp.mem_support_iff]
  exact fun h => h.symm

theorem shellCodiagonal_apply (f : ℕ →₀ ℝ) :
    shellCodiagonal f = f.sum fun _ c => c := by
  rfl

/-- Uniform average of the first `n + 1` shell labels. -/
def shellAveragingPacket (n : ℕ) : ℕ →₀ ℝ :=
  (Finset.range (n + 1)).sum fun k => Finsupp.single k ((n + 1 : ℝ)⁻¹)

@[simp] theorem shellAveragingPacket_apply (n k : ℕ) :
    shellAveragingPacket n k =
      if k < n + 1 then (n + 1 : ℝ)⁻¹ else 0 := by
  classical
  simp [shellAveragingPacket, Finset.sum_ite_eq', Finsupp.single_apply]

/-- Every uniform averaging packet has scalar response one. -/
@[simp] theorem shellCodiagonal_averagingPacket (n : ℕ) :
    shellCodiagonal (shellAveragingPacket n) = 1 := by
  classical
  simp [shellCodiagonal, shellAveragingPacket, Finsupp.lsum_apply]
  have hne : (n + 1 : ℝ) ≠ 0 := by positivity
  exact mul_inv_cancel₀ hne

/-- The squared Hilbert norm of the `n`th averaging packet is exactly `1/(n+1)`. -/
theorem norm_sq_shellLabelEmbedding_averagingPacket (n : ℕ) :
    ‖shellLabelEmbedding (shellAveragingPacket n)‖ ^ 2 = (n + 1 : ℝ)⁻¹ := by
  have hnorm := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
    (shellLabelEmbedding (shellAveragingPacket n))
  have hnorm' :
      ‖shellLabelEmbedding (shellAveragingPacket n)‖ ^ 2 =
        ∑' k : ℕ, ‖shellLabelEmbedding (shellAveragingPacket n) k‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hnorm
  rw [hnorm', tsum_eq_sum (s := Finset.range (n + 1))]
  · have hterm : ∀ k ∈ Finset.range (n + 1),
        ‖shellLabelEmbedding (shellAveragingPacket n) k‖ ^ 2 =
          ((n + 1 : ℝ)⁻¹) ^ 2 := by
      intro k hk
      rw [shellLabelEmbedding_apply, shellAveragingPacket_apply]
      simp [Finset.mem_range.mp hk]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range]
    have hne : (n + 1 : ℝ) ≠ 0 := by positivity
    simp only [nsmul_eq_mul]
    push_cast
    field_simp
  · intro b hb
    rw [shellLabelEmbedding_apply, shellAveragingPacket_apply]
    have hle : n + 1 ≤ b := by simpa using hb
    simp [not_lt_of_ge hle]

/-- The averaging packets converge to zero in the Hilbert label space. -/
theorem tendsto_shellLabelEmbedding_averagingPacket :
    Tendsto (fun n => shellLabelEmbedding (shellAveragingPacket n))
      atTop (nhds 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε ^ 2)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hsq : ‖shellLabelEmbedding (shellAveragingPacket n)‖ ^ 2 < ε ^ 2 := by
    rw [norm_sq_shellLabelEmbedding_averagingPacket]
    have hn1 : 1 / ε ^ 2 < (n + 1 : ℝ) := by
      calc
        1 / ε ^ 2 < (N : ℝ) := by exact_mod_cast hN
        _ ≤ n := by exact_mod_cast hn
        _ < n + 1 := by norm_num
    have hnpos : (0 : ℝ) < n + 1 := by positivity
    rw [inv_lt_iff_one_lt_mul₀ hnpos]
    have heps : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hprod : 1 < (n + 1 : ℝ) * ε ^ 2 :=
      (div_lt_iff₀ heps).mp hn1
    nlinarith
  nlinarith [norm_nonneg (shellLabelEmbedding (shellAveragingPacket n))]

/-- The scalar response of the graph-null packets converges to the nonzero value one. -/
theorem tendsto_shellCodiagonal_averagingPacket :
    Tendsto (fun n => shellCodiagonal (shellAveragingPacket n))
      atTop (nhds 1) := by
  simpa only [shellCodiagonal_averagingPacket] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))

/-- **Scalar assembly no-go.**  The unit-residue codiagonal has no sequentially closable
realization on the Hilbert direct sum of shell labels. -/
theorem shellCodiagonal_not_closable :
    ¬ IsSequentiallyClosableBetween shellCodiagonal shellLabelEmbedding := by
  exact not_isSequentiallyClosableBetween_of_exact_norm_graphNull
    shellCodiagonal shellLabelEmbedding shellCodiagonal shellLabelEmbedding
    (fun _ => rfl) (fun _ => rfl) shellAveragingPacket 1
    tendsto_shellLabelEmbedding_averagingPacket
    tendsto_shellCodiagonal_averagingPacket one_ne_zero

/-! ## Consolidated replication theorem -/

/-- **Orthogonal zeta-divisor replication law.**  High-exponent shells are pairwise disjoint,
each carries the completed zeta divisor with multiplicity throughout the strict right half-plane,
and the unit-residue scalar map that forgets their labels is nonclosable on the Hilbert sum. -/
theorem highExponentShell_orthogonalDivisorReplication_scalarNoGo :
    (∀ m k n : ℕ, m ≠ k →
      shellIndicator m n * shellIndicator k n = 0) ∧
    (∀ m : ℕ, 12 ≤ m → ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 →
      analyticOrderAt (fun z => completedRiemannZeta z * shellMultiplier m z) s =
        analyticOrderAt completedRiemannZeta s) ∧
    ¬ IsSequentiallyClosableBetween shellCodiagonal shellLabelEmbedding := by
  refine ⟨?_, ?_, shellCodiagonal_not_closable⟩
  · exact fun _ _ _ hmk => shellIndicator_mul_eq_zero_of_ne hmk
  · exact fun _ hm _ hs hs1 =>
      analyticOrderAt_completedRiemannZeta_mul_shellMultiplier hm hs hs1

end

end RHTower
