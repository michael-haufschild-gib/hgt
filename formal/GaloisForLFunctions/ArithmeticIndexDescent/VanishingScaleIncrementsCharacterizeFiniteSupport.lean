import GaloisForLFunctions.ArithmeticIndexDescent.BoundedSourceWork
import GaloisForLFunctions.ArithmeticIndexDescent.SourceWorkIncrementsPayForNewZeros

/-!
# Vanishing scale increments characterize finite off-line support

Monotonicity squeezes the completed arithmetic work at every real scale between
its natural-scale readings and the total copied energy. On the finite-energy
stratum this gives a real limit, so doubled-scale increments vanish. Conversely,
the annular quantum prevents infinite off-line support from having eventually
subquantum increments. No arithmetic upper estimate is assumed or supplied.
-/

noncomputable section

open Filter Set RHTower
open GaloisForLFunctions.ArithmeticElectrostatics
open scoped ENNReal Topology

namespace GaloisForLFunctions.ArithmeticIndexDescent

/-- Every completed scale reading lies below the total copied transverse energy. -/
theorem ofReal_dampedSourceWork_le_energy {R : ℝ} (hR : 4 ≤ R) :
    ENNReal.ofReal (xiDampedSourceWork R) ≤ xiCopyTransverseEnergy := by
  apply ge_of_tendsto xiDampedSourceWork_tendsto_energy
  obtain ⟨n, hn⟩ := exists_nat_ge R
  filter_upwards [eventually_ge_atTop n] with m hm
  have hnm : (n : ℝ) ≤ m := Nat.cast_le.mpr hm
  have hmR : R ≤ (m : ℝ) + 4 := by linarith only [hn, hnm]
  exact ENNReal.ofReal_le_ofReal (xiDampedSourceWork_monotoneOn hR
    (hR.trans hmR) hmR)

private theorem dampedSourceWork_nat_tendsto_real (hE : xiCopyTransverseEnergy ≠ ⊤) :
    Tendsto (fun n : ℕ => xiDampedSourceWork ((n : ℝ) + 4)) atTop
      (𝓝 xiCopyTransverseEnergy.toReal) := by
  have hc := (ENNReal.continuousAt_toReal hE).tendsto.comp
    xiDampedSourceWork_tendsto_energy
  have hnonneg (n : ℕ) : 0 ≤ xiDampedSourceWork ((n : ℝ) + 4) :=
    xiDampedSourceWork_nonneg (by
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith only [hn])
  convert hc using 1
  funext n
  exact (ENNReal.toReal_ofReal (hnonneg n)).symm

/-- Finite off-line support gives the actual real-scale limit, with all exterior rows retained. -/
theorem dampedSourceWork_tendsto_real_of_finite (hfin : offLineSupport.Finite) :
    Tendsto xiDampedSourceWork atTop (𝓝 xiCopyTransverseEnergy.toReal) := by
  have hE := (xiCopyTransverseEnergy_lt_top_iff.mpr hfin).ne
  have hnat := dampedSourceWork_nat_tendsto_real hE
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := (hnat.eventually (lt_mem_nhds
    (show xiCopyTransverseEnergy.toReal - ε < xiCopyTransverseEnergy.toReal by
      linarith only [hε]))).exists
  have hn4 : (4 : ℝ) ≤ (n : ℝ) + 4 := by
    have hn0 := Nat.cast_nonneg (α := ℝ) n
    linarith only [hn0]
  refine ⟨(n : ℝ) + 4, fun R hR => ?_⟩
  have hR4 := hn4.trans hR
  have hlo := xiDampedSourceWork_monotoneOn hn4 hR4 hR
  have hhi := ENNReal.toReal_mono hE (ofReal_dampedSourceWork_le_energy hR4)
  rw [ENNReal.toReal_ofReal (xiDampedSourceWork_nonneg hR4)] at hhi
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hhi)]
  linarith only [hn, hlo]

/-- The new work between a scale and its double. -/
def doubledSourceWorkIncrement (R : ℝ) : ℝ :=
  xiDampedSourceWork (2 * R) - xiDampedSourceWork R

theorem doubledSourceWorkIncrement_nonneg {R : ℝ} (hR : 4 ≤ R) :
    0 ≤ doubledSourceWorkIncrement R := by
  change 0 ≤ xiDampedSourceWork (2 * R) - xiDampedSourceWork R
  exact sub_nonneg.mpr (xiDampedSourceWork_monotoneOn hR
    (show 4 ≤ 2 * R by linarith only [hR]) (by linarith only [hR]))

private theorem tendsto_double_atTop : Tendsto (fun R : ℝ => 2 * R) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (b / 2)] with R hR
  linarith only [hR]

theorem doubledSourceWorkIncrement_tendsto_zero_of_finite (hfin : offLineSupport.Finite) :
    Tendsto doubledSourceWorkIncrement atTop (𝓝 0) := by
  change Tendsto (fun R : ℝ => xiDampedSourceWork (2 * R) - xiDampedSourceWork R)
    atTop (𝓝 0)
  have h := dampedSourceWork_tendsto_real_of_finite hfin
  simpa only [Function.comp_def, sub_self] using
    (h.comp tendsto_double_atTop).sub h

/-- A uniform eventual subquantum bound is exactly the finite-exception stratum. -/
theorem eventually_subquantum_increment_iff :
    (∀ᶠ R : ℝ in atTop, doubledSourceWorkIncrement R < 21 / 100) ↔
      offLineSupport.Finite := by
  constructor
  · intro h
    rcases finite_offLineSupport_or_arbitrarily_high_quantum_increments with hfin | hhigh
    · exact hfin
    obtain ⟨T, hT⟩ := eventually_atTop.mp h
    obtain ⟨R, hR, _, hquantum⟩ := hhigh T
    exact False.elim ((not_lt_of_ge hquantum) (hT R hR))
  · intro hfin
    exact (doubledSourceWorkIncrement_tendsto_zero_of_finite hfin).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 21 / 100))

/-- Arbitrarily sparse off-line escape still prevents the doubled-scale increments from vanishing. -/
theorem doubledSourceWorkIncrement_tendsto_zero_iff :
    Tendsto doubledSourceWorkIncrement atTop (𝓝 0) ↔ offLineSupport.Finite := by
  constructor
  · intro h
    exact eventually_subquantum_increment_iff.mp
      (h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 21 / 100)))
  · exact doubledSourceWorkIncrement_tendsto_zero_of_finite

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.ofReal_dampedSourceWork_le_energy
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.dampedSourceWork_tendsto_real_of_finite
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.eventually_subquantum_increment_iff
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.doubledSourceWorkIncrement_tendsto_zero_iff
