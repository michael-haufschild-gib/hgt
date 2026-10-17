import GaloisForLFunctions.BiScaleUncertainty.InfiniteGridLimitEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Origin and tail decomposition of normalized correlation energy

The singular density has arbitrarily small integral on a sufficiently short origin
interval for each integrable kernel. Away from zero, actual source correlations have
an integrable common majorant, so pointwise convergence preserves the tail energy.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-- Normalized singular energy carried by a closed-right origin interval. -/
def correlationOriginEnergy (H : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ x in Ioc 0 a, (1 - H x) * archLevySinhWeight x

/-- Normalized singular energy strictly beyond a cutoff. -/
def correlationTailEnergy (H : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ x in Ioi a, (1 - H x) * archLevySinhWeight x

theorem correlationOriginEnergy_nonneg {H : ℝ → ℝ}
    (hH : ∀ x, |H x| ≤ 1) (a : ℝ) : 0 ≤ correlationOriginEnergy H a := by
  apply setIntegral_nonneg measurableSet_Ioc
  intro x hx
  exact mul_nonneg (sub_nonneg.mpr ((le_abs_self _).trans (hH x)))
    (archLevySinhWeight_pos hx.1).le

theorem correlationOriginEnergy_mono {H : ℝ → ℝ}
    (hi : IntegrableOn (fun x => (1 - H x) * archLevySinhWeight x) (Ioi 0))
    (hH : ∀ x, |H x| ≤ 1) {a b : ℝ} (hab : a ≤ b) :
    correlationOriginEnergy H a ≤ correlationOriginEnergy H b := by
  apply setIntegral_mono_set (hi.mono_set fun x hx => hx.1)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact mul_nonneg (sub_nonneg.mpr ((le_abs_self _).trans (hH x)))
      (archLevySinhWeight_pos hx.1).le
  · exact Eventually.of_forall fun x hx => ⟨hx.1, hx.2.trans hab⟩

/-- Every integrable singular density splits exactly into origin and tail pieces. -/
theorem correlation_energy_split {H : ℝ → ℝ}
    (hi : IntegrableOn (fun x => (1 - H x) * archLevySinhWeight x) (Ioi 0))
    {a : ℝ} (ha : 0 < a) :
    (∫ x in Ioi 0, (1 - H x) * archLevySinhWeight x) =
      correlationOriginEnergy H a + correlationTailEnergy H a := by
  rw [← Ioc_union_Ioi_eq_Ioi ha.le]
  exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hi.mono_set fun x hx => hx.1) (hi.mono_set fun x hx => ha.trans hx)

/-- Uniform error beyond a positive cutoff controls the complete energy tail there. -/
theorem correlationTailEnergy_abs_sub_le {G H : ℝ → ℝ}
    (hiG : IntegrableOn (fun x => (1 - G x) * archLevySinhWeight x) (Ioi 0))
    (hiH : IntegrableOn (fun x => (1 - H x) * archLevySinhWeight x) (Ioi 0))
    {a ε : ℝ} (ha : 0 < a) (hb : ∀ x, a < x → |G x - H x| ≤ ε) :
    |correlationTailEnergy G a - correlationTailEnergy H a| ≤
      ε * ∫ x in Ioi a, archLevySinhWeight x := by
  have hiGa := hiG.mono_set (show Ioi a ⊆ Ioi 0 from fun x hx => ha.trans hx)
  have hiHa := hiH.mono_set (show Ioi a ⊆ Ioi 0 from fun x hx => ha.trans hx)
  unfold correlationTailEnergy
  rw [← integral_sub hiGa hiHa, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ x in Ioi a, ‖(1 - G x) * archLevySinhWeight x -
        (1 - H x) * archLevySinhWeight x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioi a, ε * archLevySinhWeight x := by
      apply setIntegral_mono_on (hiGa.sub hiHa).norm
        ((integrableOn_archLevySinhWeight_Ioi ha).const_mul ε) measurableSet_Ioi
      intro x hx
      change ‖(1 - G x) * archLevySinhWeight x -
        (1 - H x) * archLevySinhWeight x‖ ≤ ε * archLevySinhWeight x
      have heq : (1 - G x) * archLevySinhWeight x -
          (1 - H x) * archLevySinhWeight x = (H x - G x) * archLevySinhWeight x := by ring
      rw [heq, Real.norm_eq_abs, abs_mul, abs_sub_comm,
        abs_of_pos (archLevySinhWeight_pos (ha.trans hx))]
      exact mul_le_mul_of_nonneg_right (hb x hx) (archLevySinhWeight_pos (ha.trans hx)).le
    _ = _ := integral_const_mul _ _

/-- Shrinking reciprocal origin intervals lose all energy of an integrable kernel. -/
theorem tendsto_correlationOriginEnergy_zero {H : ℝ → ℝ}
    (hi : IntegrableOn (fun x => (1 - H x) * archLevySinhWeight x) (Ioi 0)) :
    Tendsto (fun n : ℕ => correlationOriginEnergy H (1 / ((n : ℝ) + 1)))
      atTop (𝓝 0) := by
  have hanti : Antitone (fun n : ℕ => Ioc (0 : ℝ) (1 / ((n : ℝ) + 1))) := by
    intro i j hij x hx
    refine ⟨hx.1, hx.2.trans ?_⟩
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hempty : (⋂ n : ℕ, Ioc (0 : ℝ) (1 / ((n : ℝ) + 1))) = ∅ := by
    ext x
    simp only [mem_iInter, mem_Ioc, mem_empty_iff_false, iff_false]
    intro hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hx 0).1
    exact (not_lt_of_ge (hx n).2) hn
  have ht := tendsto_setIntegral_of_antitone (fun _ => measurableSet_Ioc) hanti
    (show ∃ n : ℕ, IntegrableOn (fun x => (1 - H x) * archLevySinhWeight x)
      (Ioc 0 (1 / ((n : ℝ) + 1))) from
        ⟨0, hi.mono_set (show Ioc 0 (1 / ((0 : ℕ) + 1 : ℝ)) ⊆ Ioi 0 from fun x hx => hx.1)⟩)
  rw [hempty] at ht
  simpa [correlationOriginEnergy] using ht

theorem exists_small_correlationOriginEnergy {H : ℝ → ℝ}
    (hi : IntegrableOn (fun x => (1 - H x) * archLevySinhWeight x) (Ioi 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ correlationOriginEnergy H a < ε := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_order.mp (tendsto_correlationOriginEnergy_zero hi)).2 ε hε)
  exact ⟨1 / ((N : ℝ) + 1), by positivity, hN N le_rfl⟩

/-- A finite family admits one common positive cutoff with small origin energy. -/
theorem exists_common_small_correlationOriginEnergy {ι : Type*} (s : Finset ι)
    (H : ι → ℝ → ℝ)
    (hi : ∀ i ∈ s, IntegrableOn (fun x => (1 - H i x) * archLevySinhWeight x) (Ioi 0))
    (hH : ∀ i ∈ s, ∀ x, |H i x| ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∀ i ∈ s, correlationOriginEnergy (H i) a < ε := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s his ih =>
    obtain ⟨a, ha, hai⟩ := exists_small_correlationOriginEnergy
      (hi i (Finset.mem_insert_self i s)) hε
    obtain ⟨b, hb, hbs⟩ := ih
      (fun j hj => hi j (Finset.mem_insert_of_mem hj))
      (fun j hj => hH j (Finset.mem_insert_of_mem hj))
    refine ⟨min a b, lt_min ha hb, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · exact (correlationOriginEnergy_mono (hi j (Finset.mem_insert_self j s))
        (hH j (Finset.mem_insert_self j s)) (min_le_left a b)).trans_lt hai
    · exact (correlationOriginEnergy_mono (hi j hj) (hH j hj)
        (min_le_right a b)).trans_lt (hbs j hjs)

variable {K : ℝ}

/-- Ordinary kernel energy equals the actual source's normalized energy. -/
theorem InfiniteGridEnergySource.integral_correlationLevyIntegrand
    (f : InfiniteGridEnergySource K) :
    (∫ x in Ioi 0, (1 - f.correlation x) * archLevySinhWeight x) =
      normalizedArchEnergy f.source := by
  rw [normalizedArchEnergy_eq_integral]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  dsimp [InfiniteGridEnergySource.correlation]
  field_simp [f.mass_pos.ne']

theorem InfiniteGridEnergySource.energy_split (f : InfiniteGridEnergySource K)
    {a : ℝ} (ha : 0 < a) :
    normalizedArchEnergy f.source = correlationOriginEnergy f.correlation a +
      correlationTailEnergy f.correlation a := by
  rw [← f.integral_correlationLevyIntegrand]
  exact correlation_energy_split f.integrable_correlationLevyIntegrand ha

/-- Even pointwise convergence preserves the complete energy tail beyond any positive cutoff. -/
theorem tendsto_correlationTailEnergy_of_pointwise (f : ℕ → InfiniteGridEnergySource K)
    {H : ℝ → ℝ} (h : ∀ x, Tendsto (fun n => (f n).correlation x) atTop (𝓝 (H x)))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => correlationTailEnergy (f n).correlation a) atTop
      (𝓝 (correlationTailEnergy H a)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => 2 * archLevySinhWeight x)
  · intro n
    exact ((f n).integrable_correlationLevyIntegrand.mono_set fun x hx => ha.trans hx).1
  · exact (integrableOn_archLevySinhWeight_Ioi ha).const_mul 2
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hw := (archLevySinhWeight_pos (ha.trans hx)).le
    have hb := (f n).abs_correlation_le_one x
    have hp : 0 ≤ 1 - (f n).correlation x := by linarith [le_abs_self ((f n).correlation x)]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp, abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_right (by linarith [(abs_le.mp hb).1]) hw
  · exact Eventually.of_forall fun x =>
      (tendsto_const_nhds.sub (h x)).mul_const (archLevySinhWeight x)

end

end GaloisForLFunctions.BiScaleUncertainty
