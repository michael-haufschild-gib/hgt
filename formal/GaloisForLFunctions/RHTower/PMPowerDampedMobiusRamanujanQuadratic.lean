import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanGram

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

theorem pmRamanujanPrimitive_im (q N : ℕ) : (pmRamanujanPrimitive q N).im = 0 := by
  rw [pmRamanujanPrimitive_eq_floor]
  simp [Complex.mul_im]

theorem pmPowerDampedRamanujanWeight_im {ε : ℝ} (hε : 0 < ε) (q : ℕ) :
    (pmPowerDampedRamanujanWeight ε q).im = 0 := by
  rw [pmPowerDampedRamanujanWeight_eq_ofReal hε]
  exact Complex.ofReal_im _

theorem pmPowerDampedRamanujanCumulativePrefix_eq_primitive (ε : ℝ) (Q N : ℕ) :
    pmPowerDampedRamanujanCumulativePrefix ε Q N =
      ∑ q ∈ Finset.range Q, pmPowerDampedRamanujanWeight ε (q+2)*
        pmRamanujanPrimitive (q+2) N := by
  unfold pmPowerDampedRamanujanCumulativePrefix pmPowerDampedRamanujanCenteredPrefix
  rw [Finset.sum_comm]
  simp_rw [pmRamanujanPrimitive, Finset.mul_sum]

theorem pmPowerDampedRamanujanCumulativePrefix_im {ε : ℝ} (hε : 0 < ε) (Q N : ℕ) :
    (pmPowerDampedRamanujanCumulativePrefix ε Q N).im = 0 := by
  rw [pmPowerDampedRamanujanCumulativePrefix_eq_primitive]
  simp [Complex.mul_im, pmPowerDampedRamanujanWeight_im hε, pmRamanujanPrimitive_im]

theorem pmPowerDampedRamanujanCumulativePrefix_re {ε : ℝ} (hε : 0 < ε) (Q N : ℕ) :
    (pmPowerDampedRamanujanCumulativePrefix ε Q N).re =
      ∑ q ∈ Finset.range Q, (pmPowerDampedRamanujanWeight ε (q+2)).re*
        (pmRamanujanPrimitive (q+2) N).re := by
  rw [pmPowerDampedRamanujanCumulativePrefix_eq_primitive]
  simp [Complex.mul_re, pmPowerDampedRamanujanWeight_im hε]

def pmPowerDampedRamanujanGramQuadratic (ε : ℝ) (Q : ℕ) : ℝ :=
  ∑ p ∈ Finset.range Q, ∑ q ∈ Finset.range Q,
    (pmPowerDampedRamanujanWeight ε (p+2)).re*
      (pmPowerDampedRamanujanWeight ε (q+2)).re*pmRamanujanPrimitiveGram (p+2) (q+2)

theorem pmPowerDampedRamanujanEnergyTerm_eq_gram {ε : ℝ} (hε : 0 < ε) (Q N : ℕ) :
    ‖pmPowerDampedRamanujanCumulativePrefix ε Q N‖^2/((N : ℝ)*((N : ℝ)+1)) =
      ∑ p ∈ Finset.range Q, ∑ q ∈ Finset.range Q,
        (pmPowerDampedRamanujanWeight ε (p+2)).re*
          (pmPowerDampedRamanujanWeight ε (q+2)).re*
            pmRamanujanPrimitiveGramTerm (p+2) (q+2) N := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    pmPowerDampedRamanujanCumulativePrefix_im hε]
  simp only [mul_zero, add_zero, pmPowerDampedRamanujanCumulativePrefix_re hε,
    Finset.sum_mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  unfold pmRamanujanPrimitiveGramTerm
  ring

theorem hasSum_pmPowerDampedRamanujanEnergyTerm {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    HasSum (fun N : ℕ => ‖pmPowerDampedRamanujanCumulativePrefix ε Q N‖^2/
      ((N : ℝ)*((N : ℝ)+1))) (pmPowerDampedRamanujanGramQuadratic ε Q) := by
  have hs : HasSum (fun N : ℕ =>
      ∑ p ∈ Finset.range Q, ∑ q ∈ Finset.range Q,
        (pmPowerDampedRamanujanWeight ε (p+2)).re*
          (pmPowerDampedRamanujanWeight ε (q+2)).re*
            pmRamanujanPrimitiveGramTerm (p+2) (q+2) N)
      (pmPowerDampedRamanujanGramQuadratic ε Q) := by
    apply hasSum_sum
    intro p hp
    apply hasSum_sum
    intro q hq
    exact (summable_pmRamanujanPrimitiveGramTerm (by omega : 1 < p+2)
      (by omega : 1 < q+2)).hasSum.mul_left _
  exact hs.congr_fun (pmPowerDampedRamanujanEnergyTerm_eq_gram hε Q)

theorem pmPowerDampedRamanujanPrefixEnergy_le_gram {ε : ℝ} (hε : 0 < ε) (Q T : ℕ) :
    pmPowerDampedRamanujanPrefixEnergy ε Q T ≤ pmPowerDampedRamanujanGramQuadratic ε Q := by
  have hs := hasSum_pmPowerDampedRamanujanEnergyTerm hε Q
  rw [← hs.tsum_eq]
  exact hs.summable.sum_le_tsum (Finset.Icc 1 T) (fun _ _ => by positivity)

theorem tendsto_pmPowerDampedRamanujanPrefixEnergy_gram {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    Tendsto (fun T : ℕ => pmPowerDampedRamanujanPrefixEnergy ε Q T)
      atTop (𝓝 (pmPowerDampedRamanujanGramQuadratic ε Q)) := by
  have hs := hasSum_pmPowerDampedRamanujanEnergyTerm hε Q
  have ht := (hasSum_nat_add_iff' 1).mpr hs
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, div_zero, sub_zero] at ht
  simpa only [pmPowerDampedRamanujanPrefixEnergy, sum_Icc_eq_sum_range_succ] using
    ht.tendsto_sum_nat

theorem pmPowerDampedRamanujan_budget_iff_gram {ε B : ℝ} (hε : 0 < ε) :
    (∀ Q T : ℕ, pmPowerDampedRamanujanPrefixEnergy ε Q T ≤ B) ↔
      (∀ Q : ℕ, pmPowerDampedRamanujanGramQuadratic ε Q ≤ B) := by
  constructor
  · intro h Q
    exact le_of_tendsto (tendsto_pmPowerDampedRamanujanPrefixEnergy_gram hε Q)
      (Eventually.of_forall (h Q))
  · intro h Q T
    exact (pmPowerDampedRamanujanPrefixEnergy_le_gram hε Q T).trans (h Q)

theorem pmPowerDampedFermiSource_memLp_of_ramanujan_gram {ε B : ℝ} (hε : 0 < ε)
    (hB : ∀ Q : ℕ, pmPowerDampedRamanujanGramQuadratic ε Q ≤ B) :
    MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  exact pmPowerDampedFermiSource_memLp_of_ramanujan_budget hε
    ((pmPowerDampedRamanujan_budget_iff_gram hε).mpr hB)

end RHTower
