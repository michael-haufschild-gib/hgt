import GaloisForLFunctions.BiScaleUncertainty.PrimeClockGraphCompactness
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalLogProfileTail
import Mathlib.Topology.Order.Compact

/-!
# Full graph decay and amplitude tightness of arithmetic clocks

The actual Abel profile and a uniform variation bound make a fixed-cutoff
clock tend to zero at both ends in the complete graph norm. Consequently
bounded total amplitude gives compactness without a restriction on centers.
-/

open MeasureTheory Finset Set Filter Topology RHTower RHTower.CHMDDoobGraph
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.BiScaleUncertainty.PrimeClock
noncomputable section
set_option autoImplicit false

theorem logProfile_zero_atTop : Tendsto criticalAbelLogProfile atTop (𝓝 0) := by
  have hi : Tendsto (fun t : ℝ => -(∫ u in Ioi t, criticalAbelLogVelocity u))
      atTop (𝓝 0) := by
    simpa using (tendsto_integral_Ioi_zero (f := criticalAbelLogVelocity)
      (μ := volume) tendsto_id).neg
  apply hi.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (criticalAbelLogProfile_eq_velocity_tail ht).symm

private theorem curve_tendsto_of_uniform (k : ℕ) {l : Filter ℝ}
    (hu : TendstoUniformly (criticalClockCutoff (cutoff k)) (fun _ => 0) l) :
    Tendsto (curve k) l (𝓝 0) := by
  let hχ := boundedVariationOn_of_contDiff_compact
    ((cutoff_contDiff k).of_le (by norm_num)) (cutoff_hasCompactSupport k)
  exact tendsto_bvLift_zero_of_uniform
    (fun t => criticalClockCutoff_boundedVariation (cutoff k) hχ t)
    (fun t => criticalClockCutoff_compact (cutoff k) (cutoff_hasCompactSupport k) t)
    (fun t => criticalClockCutoff_variation_bound (cutoff k) hχ t) hu

theorem curve_zero_atTop (k : ℕ) : Tendsto (curve k) atTop (𝓝 0) := by
  apply curve_tendsto_of_uniform
  have hcompact : IsCompact (tsupport (cutoff k)) := cutoff_hasCompactSupport k
  obtain ⟨R, hR⟩ := hcompact.bddAbove
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hnorm : Tendsto (fun t => ‖criticalAbelLogProfile t‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using logProfile_zero_atTop.norm
  obtain ⟨A, hA⟩ := eventually_atTop.mp (hnorm.eventually_lt_const hε)
  filter_upwards [eventually_ge_atTop (A + R)] with t ht
  intro x
  have hb : |criticalClockCutoff (cutoff k) t x| < ε := by
    by_cases hx : cutoff k x = 0
    · simpa only [criticalClockCutoff, hx, zero_mul, abs_zero] using hε
    · have hxR := hR (subset_tsupport (cutoff k) hx)
      have hf := hA (t-x) (by linarith)
      rw [Real.norm_eq_abs] at hf
      rw [criticalClockCutoff, abs_mul, abs_of_nonneg (cutoff_nonneg k x)]
      exact (mul_le_of_le_one_left (abs_nonneg _) (cutoff_le_one k x)).trans_lt hf
  simpa only [Real.dist_eq, sub_zero, zero_sub, abs_neg] using hb

theorem curve_zero_atBot (k : ℕ) : Tendsto (curve k) atBot (𝓝 0) := by
  apply curve_tendsto_of_uniform
  have hcompact : IsCompact (tsupport (cutoff k)) := cutoff_hasCompactSupport k
  obtain ⟨L, hL⟩ := hcompact.bddBelow
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [eventually_le_atBot L] with t ht
  intro x
  have hz : criticalClockCutoff (cutoff k) t x = 0 := by
    by_cases hx : cutoff k x = 0
    · simp only [criticalClockCutoff, hx, zero_mul]
    · have hxL := hL (subset_tsupport (cutoff k) hx)
      rw [criticalClockCutoff, criticalAbelLogProfile_zero_of_nonpos (by linarith), mul_zero]
  simpa only [hz, dist_self] using hε

/-- All logarithmic centers form one compact graph curve after adding its zero limit. -/
theorem isCompact_zero_range (k : ℕ) : IsCompact (insert 0 (range (curve k))) := by
  have h : Tendsto (curve k) (cocompact ℝ) (𝓝 0) := by
    rw [cocompact_eq_atBot_atTop]
    exact tendsto_sup.mpr ⟨curve_zero_atBot k, curve_zero_atTop k⟩
  exact h.isCompact_insert_range_of_cocompact (continuous_curve k)

def globalHull (k : ℕ) : Set SourceGraph := closure (convexHull ℝ (insert 0 (range (curve k))))

theorem isCompact_globalHull (k : ℕ) : IsCompact (globalHull k) :=
  isCompact_iff_totallyBounded_isComplete.mpr
    ⟨(totallyBounded_convexHull _ (isCompact_zero_range k).totallyBounded).closure,
      isClosed_closure.isComplete⟩

def globalEnvelope (k : ℕ) (C : ℝ) : Set SourceGraph :=
  (fun z : ℝ × SourceGraph => z.1 • z.2) '' (Icc 0 C ×ˢ globalHull k)

theorem isCompact_globalEnvelope (k : ℕ) (C : ℝ) : IsCompact (globalEnvelope k C) :=
  (isCompact_Icc.prod (isCompact_globalHull k)).image (continuous_fst.smul continuous_snd)

theorem packet_mem_globalEnvelope (k N : ℕ) (S : Finset ℕ) (C : ℝ)
    (hweight : (∑ p ∈ S, Real.sqrt N / (p : ℝ)) ≤ C) :
    packet k N S ∈ globalEnvelope k C := by
  classical
  have hfin : (Real.log ∘ (fun p : ℕ => (N : ℝ) / p) '' (S : Set ℕ)).Finite :=
    S.finite_toSet.image _
  obtain ⟨R, hR⟩ := hfin.bddAbove
  obtain ⟨T, hT⟩ := hfin.bddBelow
  have hp := packet_mem_envelope k N S T R C (fun p hp =>
    ⟨hT ⟨p, hp, rfl⟩, hR ⟨p, hp, rfl⟩⟩) hweight
  obtain ⟨z, hz, he⟩ := hp
  refine ⟨z, ⟨hz.1, ?_⟩, he⟩
  apply (closure_mono (convexHull_mono (show insert 0 (curve k '' Icc T R) ⊆
      insert 0 (range (curve k)) from ?_))) hz.2
  rintro x (rfl | ⟨t, _ht, rfl⟩)
  · exact mem_insert _ _
  · exact mem_insert_of_mem _ ⟨t, rfl⟩

/-- No center restriction: only the literal total amplitude and the fixed cutoff matter. -/
def amplitudeBounded (k : ℕ) (C : ℝ) : Set SourceGraph :=
  {q | ∃ N : ℕ, ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
    (∑ p ∈ S, Real.sqrt N / (p : ℝ)) ≤ C ∧ q = packet k N S}

theorem isCompact_closure_amplitudeBounded (k : ℕ) (C : ℝ) :
    IsCompact (closure (amplitudeBounded k C)) := by
  apply (isCompact_globalEnvelope k C).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isCompact_globalEnvelope k C).isClosed
  rintro q ⟨N, S, _hprime, hweight, rfl⟩
  exact packet_mem_globalEnvelope k N S C hweight

theorem packet_norm_le (k N : ℕ) (S : Finset ℕ) (δ : ℝ)
    (hcurve : ∀ p ∈ S, ‖curve k (Real.log ((N : ℝ) / p))‖ ≤ δ) :
    ‖packet k N S‖ ≤ δ * ∑ p ∈ S, Real.sqrt N / (p : ℝ) := by
  unfold packet
  calc
    _ ≤ ∑ p ∈ S, ‖canonicalPrimeGraphClockAtom k N p‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ S, (Real.sqrt N / (p : ℝ)) * δ := by
      apply sum_le_sum
      intro p hp
      rw [atom_norm]
      exact mul_le_mul_of_nonneg_left (hcurve p hp)
        (div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg p))
    _ = _ := by rw [← sum_mul, mul_comm]

/-- Bounded amplitude makes every fixed-cutoff packet with cofinal centers vanish,
including all singular prime edges. -/
theorem deep_packets_zero (k : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (N : ℕ → ℕ) (S : ℕ → Finset ℕ)
    (hcenter : ∀ n p, p ∈ S n → (n : ℝ) ≤ Real.log ((N n : ℝ) / p))
    (hweight : ∀ n, (∑ p ∈ S n, Real.sqrt (N n) / (p : ℝ)) ≤ C) :
    Tendsto (fun n => packet k (N n) (S n)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hδ : 0 < ε / (C + 1) := div_pos hε (by linarith)
  have hnorm : Tendsto (fun t => ‖curve k t‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using (curve_zero_atTop k).norm
  obtain ⟨R, hR⟩ := eventually_atTop.mp (hnorm.eventually_lt_const hδ)
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hnat.eventually (eventually_ge_atTop R)] with n hn
  have hp := packet_norm_le k (N n) (S n) (ε / (C + 1))
    (fun p hp => (hR _ (hn.trans (hcenter n p hp))).le)
  have hw := mul_le_mul_of_nonneg_left (hweight n) hδ.le
  have hid : ε / (C + 1) * (C + 1) = ε := div_mul_cancel₀ ε (by linarith)
  have hnorm : ‖packet k (N n) (S n)‖ < ε := by nlinarith
  simpa only [dist_zero_right] using hnorm

end
end GaloisForLFunctions.BiScaleUncertainty.PrimeClock
