import GaloisForLFunctions.ArithmeticIndexDescent.TheIndexIsPaidByTransverseEnergy
import GaloisForLFunctions.ArithmeticElectrostatics.TheSelbergWorkExhaustsTheTransverseEnergy

/-!
# Arithmetic source work and finite negative-index witnesses

The distinct-zero transverse energy embeds in the multiplicity-weighted energy by
choosing one copy of each zero. Removing the rational height damping therefore
eventually pays any amount strictly below the negative index of a finite Weil Gram.
The comparison uses the full divisor and retains exterior interactions.
-/

open Filter Finset RHTower Zeta23
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.ArithmeticElectrostatics
open scoped ENNReal Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

/-- Select one analytic-multiplicity copy of each distinct zero. -/
def firstZeroCopy (j : XiDivisorSupport) : XiZeroCopy :=
  ⟨j, ⟨0, by have h := xi_divisor_pos_on_support j; omega⟩⟩

theorem firstZeroCopy_injective : Function.Injective firstZeroCopy := by
  intro j k h
  exact congrArg Sigma.fst h

/-- The diagonal convention agrees with the geometric ratio, whose value at zero is zero. -/
theorem angularEnergyTerm_eq_geometric (j k : XiDivisorSupport) :
    angularEnergyTerm j k =
      ((j : ℂ).re - (k : ℂ).re) ^ 2 / ‖(j : ℂ) - (k : ℂ)‖ ^ 2 := by
  classical
  rw [angularEnergyTerm]
  split_ifs with h
  · subst k
    simp
  · rw [Complex.sq_norm]

/-- Counting every multiplicity copy can only increase the distinct-zero energy. -/
theorem divisorTransverseEnergy_le_xiCopyTransverseEnergy :
    divisorTransverseEnergy ≤ xiCopyTransverseEnergy := by
  have hrow (j : XiDivisorSupport) :
      ENNReal.ofReal (angularEnergy j) = ∑' k : XiDivisorSupport,
        ENNReal.ofReal (((j : ℂ).re - (k : ℂ).re) ^ 2 / ‖(j : ℂ) - (k : ℂ)‖ ^ 2) := by
    rw [angularEnergy, ENNReal.ofReal_tsum_of_nonneg
      (angularEnergyTerm_nonneg j) (summable_angularEnergyTerm j)]
    exact tsum_congr fun k => congrArg ENNReal.ofReal (angularEnergyTerm_eq_geometric j k)
  let e : XiDivisorSupport × XiDivisorSupport → XiZeroCopy × XiZeroCopy :=
    fun jk => (firstZeroCopy jk.1, firstZeroCopy jk.2)
  have he : Function.Injective e := by
    intro a b h
    exact Prod.ext (firstZeroCopy_injective (congrArg Prod.fst h))
      (firstZeroCopy_injective (congrArg Prod.snd h))
  have hsum :
      (∑' jk : XiDivisorSupport × XiDivisorSupport,
        ENNReal.ofReal (((jk.1 : ℂ).re - (jk.2 : ℂ).re) ^ 2 /
          ‖(jk.1 : ℂ) - (jk.2 : ℂ)‖ ^ 2)) ≤
      ∑' pq : XiZeroCopy × XiZeroCopy,
        ENNReal.ofReal (((pq.1.1 : ℂ).re - (pq.2.1 : ℂ).re) ^ 2 /
          ‖(pq.1.1 : ℂ) - (pq.2.1 : ℂ)‖ ^ 2) :=
    Summable.tsum_le_tsum_of_inj e he (fun _ _ => zero_le) (fun _ => le_rfl)
      ENNReal.summable ENNReal.summable
  rw [divisorTransverseEnergy, xiCopyTransverseEnergy_eq_half_tsum]
  simp_rw [hrow]
  rw [← ENNReal.tsum_prod]
  exact div_le_div_right hsum

/-- Every negative square is paid in the full multiplicity-weighted source energy. -/
theorem negIndex_weilGram_le_xiCopyTransverseEnergy {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) :
    (hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) : ℝ≥0∞)
      ≤ xiCopyTransverseEnergy :=
  (negIndex_weilGram_le_divisorTransverseEnergy f hf hfc).trans
    divisorTransverseEnergy_le_xiCopyTransverseEnergy

/-- Every amount strictly below a finite index witness is eventually visible in arithmetic work. -/
theorem eventually_lt_dampedSourceWork_of_lt_negIndex {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) {b : ℝ≥0∞}
    (hb : b < (hermNegIndex
      (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) : ℝ≥0∞)) :
    ∀ᶠ n : ℕ in atTop, b < ENNReal.ofReal (xiDampedSourceWork ((n : ℝ) + 4)) :=
  xiDampedSourceWork_tendsto_energy.eventually
    (lt_mem_nhds (hb.trans_le (negIndex_weilGram_le_xiCopyTransverseEnergy f hf hfc)))

/-- A finite negative-index witness is detected by actual finite source work after the
height taper is removed at each sufficiently large damping scale. -/
theorem eventually_eventually_lt_sourceWork_of_lt_negIndex {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) {b : ℝ≥0∞}
    (hb : b < (hermNegIndex
      (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) : ℝ≥0∞)) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      b < ENNReal.ofReal (xiTaperedSourceWork ((n : ℝ) + 4) N) := by
  filter_upwards [eventually_lt_dampedSourceWork_of_lt_negIndex f hf hfc hb] with n hn
  have hR : (4 : ℝ) ≤ (n : ℝ) + 4 := by positivity
  exact ((ENNReal.continuous_ofReal.tendsto _).comp
    (xiTaperedSourceWork_tendsto hR)).eventually (lt_mem_nhds hn)

end GaloisForLFunctions.ArithmeticIndexDescent
