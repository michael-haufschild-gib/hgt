import GaloisForLFunctions.ArithmeticIndexDescent.BoundedSourceWork
import GaloisForLFunctions.ArithmeticIndexDescent.TheEnergyStrictlyExceedsTheIndex

/-!
# A closed quantum threshold for arithmetic source work

Multiplicity-weighted energy is zero on the critical line and exceeds two if
there is an off-line quartet. Thus a cofinal sequence of damped source works at
most two already excludes every off-line zero. No upper bound on those works is
assumed or proved here: the theorem identifies the exact arithmetic target.

A positive finite Weil index is also detected without an epsilon loss: sufficiently
large damping scales, followed by sufficiently large height tapers, have source
work strictly above that entire integer index.
-/

open Filter RHTower Zeta23
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.ArithmeticElectrostatics
open scoped ENNReal Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

theorem xiCopyTransverseEnergy_eq_zero_iff : xiCopyTransverseEnergy = 0 ↔ RiemannHypothesis := by
  constructor
  · intro h
    have hle := divisorTransverseEnergy_le_xiCopyTransverseEnergy
    rw [h] at hle
    exact divisorTransverseEnergy_eq_zero_iff.mp (le_antisymm hle zero_le)
  · intro h
    have hterm (p q : XiZeroCopy) : copyAngularTerm p q = 0 :=
      copyAngularTerm_eq_zero_of_critical
        (xiZeroCopy_re_eq_half_of_riemannHypothesis h p)
        (xiZeroCopy_re_eq_half_of_riemannHypothesis h q)
    rw [xiCopyTransverseEnergy_eq_half_rowSum]
    simp only [copyAngularEnergy, hterm, tsum_zero, ENNReal.ofReal_zero,
      div_eq_mul_inv, zero_mul]

/-- The threshold is closed because every actual off-line quartet has a positive diagonal surplus. -/
theorem riemannHypothesis_iff_xiCopyTransverseEnergy_le_two :
    RiemannHypothesis ↔ xiCopyTransverseEnergy ≤ 2 := by
  constructor
  · intro h
    rw [xiCopyTransverseEnergy_eq_zero_iff.mpr h]
    exact zero_le
  · intro h
    exact riemannHypothesis_iff_divisorTransverseEnergy_le_two.mpr
      (divisorTransverseEnergy_le_xiCopyTransverseEnergy.trans h)

theorem xiDampedSourceWork_eq_zero_of_riemannHypothesis (h : RiemannHypothesis) (R : ℝ) :
    xiDampedSourceWork R = 0 := by
  have hdepth (p : XiZeroCopy) : xiSignedDepth p = 0 := by
    rw [xiSignedDepth, xiZeroCopy_re_eq_half_of_riemannHypothesis h p, sub_self]
  simp only [xiDampedSourceWork, xiDampedPairWork, hdepth, sub_self, add_zero,
    reflectedWork, reflectedEnergy, reflectedCross, transverseAngular,
    zero_pow (by decide : 2 ≠ 0), zero_div, zero_add, mul_zero, zero_mul, tsum_zero]

/-- A cofinal sequence of arithmetic work readings below the closed quantum threshold suffices. -/
theorem riemannHypothesis_iff_cofinally_dampedSourceWork_le_two :
    RiemannHypothesis ↔ ∀ M : ℕ, ∃ n ≥ M, xiDampedSourceWork ((n : ℝ) + 4) ≤ 2 := by
  constructor
  · intro h M
    exact ⟨M, le_rfl, by rw [xiDampedSourceWork_eq_zero_of_riemannHypothesis h]; norm_num⟩
  · intro h
    by_contra hRH
    have hE : (2 : ℝ≥0∞) < xiCopyTransverseEnergy :=
      lt_of_not_ge fun hle => hRH (riemannHypothesis_iff_xiCopyTransverseEnergy_le_two.mpr hle)
    have hevent := xiDampedSourceWork_tendsto_energy.eventually (lt_mem_nhds hE)
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hevent
    obtain ⟨n, hn, hwork⟩ := h M
    have hupper : ENNReal.ofReal (xiDampedSourceWork ((n : ℝ) + 4)) ≤ 2 := by
      simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hwork
    exact (not_lt_of_ge hupper) (hM n hn)

/-- Every positive index witness eventually forces finite arithmetic source work above its index. -/
theorem negIndex_eq_zero_or_eventually_sourceWork_gt_index {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) :
    hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) = 0 ∨
      ∀ᶠ n : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        (hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) : ℝ≥0∞)
          < ENNReal.ofReal (xiTaperedSourceWork ((n : ℝ) + 4) N) := by
  rcases negIndex_eq_zero_or_lt_divisorTransverseEnergy f hf hfc with hzero | hstrict
  · exact Or.inl hzero
  right
  have hE := hstrict.trans_le divisorTransverseEnergy_le_xiCopyTransverseEnergy
  filter_upwards [xiDampedSourceWork_tendsto_energy.eventually (lt_mem_nhds hE)] with n hn
  have hR : (4 : ℝ) ≤ (n : ℝ) + 4 := by
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith only [hn0]
  exact ((ENNReal.continuous_ofReal.tendsto _).comp
    (xiTaperedSourceWork_tendsto hR)).eventually (lt_mem_nhds hn)

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.riemannHypothesis_iff_cofinally_dampedSourceWork_le_two
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.negIndex_eq_zero_or_eventually_sourceWork_gt_index
