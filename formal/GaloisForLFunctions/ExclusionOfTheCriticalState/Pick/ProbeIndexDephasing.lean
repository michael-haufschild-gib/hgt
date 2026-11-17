import GaloisForLFunctions.HilbertMetric.QuantumInformation.CauchyDephasingLimit
import GaloisForLFunctions.ExclusionOfTheCriticalState.Certificates.WeilProbeCutBudget
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.TheRealProbeKernelIsAKreinForm
import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedPhaseInfiniteFockKernel


/-!
# Eventual positive definiteness of dephased Weil probe matrices

Distinct index rates suppress every off-diagonal coefficient. The limit
has the original strictly positive Weil diagonal, so all sufficiently
late finite iterates are positive definite. No positivity of the original
Weil matrix is assumed.
-/

noncomputable section
open Matrix Filter
open scoped Topology ComplexOrder
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeCuts
open Pick HilbertMetric.CauchyDephasing

/-- Finite Cauchy dephasing with distinct integer logarithmic rates. -/
def indexDephasedGram {n : ℕ} (k : ℕ) (p : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  coherence (i.val : ℝ) (j.val : ℝ) ^ k *
    bareMixedEnergy (probe (node (p i))) (probe (node (p j)))

private theorem safe_entry_symm (s t : ℝ) :
    bareMixedEnergy (probe (node s)) (probe (node t)) =
      bareMixedEnergy (probe (node t)) (probe (node s)) := by
  apply bareMixedEnergy_probe_symm <;> unfold node <;>
    linarith only [abs_nonneg s, abs_nonneg t]

/-- The real matrix is exactly the Cauchy channel applied to the actual complex Weil Gram. -/
theorem indexDephasedGram_map_complex {n : ℕ} (k : ℕ) (p : Fin n → ℝ) :
    (indexDephasedGram k p).map (algebraMap ℝ ℂ) =
      channelPower k (fun i : Fin n => (i.val : ℝ))
        (probeGram (fun i => node (p i))) := by
  ext i j
  change ((coherence (i.val : ℝ) (j.val : ℝ) ^ k *
      bareMixedEnergy (probe (node (p i))) (probe (node (p j))) : ℝ) : ℂ) =
    (coherence (i.val : ℝ) (j.val : ℝ) : ℂ) ^ k *
      (bareMixedEnergy (probe (node (p i))) (probe (node (p j))) : ℂ)
  rw [Complex.ofReal_mul, Complex.ofReal_pow]

/-- Every iterate is a real symmetric matrix. -/
theorem indexDephasedGram_isHermitian {n : ℕ} (k : ℕ) (p : Fin n → ℝ) :
    (indexDephasedGram k p).IsHermitian := by
  ext i j
  change indexDephasedGram k p j i = indexDephasedGram k p i j
  rw [indexDephasedGram, indexDephasedGram, coherence_symm, safe_entry_symm]

/-- Dephasing retains the original strictly positive diagonal. -/
theorem indexDephasedGram_diagonal {n : ℕ} (k : ℕ) (p : Fin n → ℝ) (i : Fin n) :
    indexDephasedGram k p i i =
      bareMixedEnergy (probe (node (p i))) (probe (node (p i))) := by
  simp only [indexDephasedGram, coherence_self, one_pow, one_mul]

/-- All entries remain strictly positive at every finite iterate. -/
theorem indexDephasedGram_entry_pos {n : ℕ} (k : ℕ) (p : Fin n → ℝ) (i j : Fin n) :
    0 < indexDephasedGram k p i j :=
  mul_pos (pow_pos (coherence_pos _ _) _) (probeEntry_pos _ _)

/-- The limit is exactly the original positive diagonal. -/
theorem indexDephasedGram_tendsto {n : ℕ} (p : Fin n → ℝ) :
    Tendsto (fun k => indexDephasedGram k p) atTop
      (𝓝 (diagonal fun i =>
        bareMixedEnergy (probe (node (p i))) (probe (node (p i))))) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  by_cases h : i = j
  · subst j
    simpa only [indexDephasedGram_diagonal, Matrix.diagonal_apply_eq] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        bareMixedEnergy (probe (node (p i))) (probe (node (p i)))) atTop _)
  · have hrate : (i.val : ℝ) ≠ (j.val : ℝ) := by
      intro he
      exact h (Fin.ext (by exact_mod_cast he))
    have hlt : coherence (i.val : ℝ) (j.val : ℝ) < 1 := by
      by_contra hn
      exact hrate ((coherence_eq_one_iff _ _).mp
        (le_antisymm (coherence_le_one _ _) (le_of_not_gt hn)))
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (coherence_pos (i.val : ℝ) (j.val : ℝ)).le hlt).mul_const
        (bareMixedEnergy (probe (node (p i))) (probe (node (p j))))
    simpa only [indexDephasedGram, Matrix.diagonal_apply, if_neg h, zero_mul] using ht

/-- Every finite safe Weil matrix becomes positive definite after sufficiently many steps. -/
theorem indexDephasedGram_eventually_posDef {n : ℕ} (p : Fin n → ℝ) :
    ∀ᶠ k in atTop, (indexDephasedGram k p).PosDef := by
  apply HTGeometry.posDef_eventually_of_tendsto
    (M₀ := diagonal fun i =>
      bareMixedEnergy (probe (node (p i))) (probe (node (p i))))
  · exact Matrix.PosDef.diagonal fun i => probeEntry_pos (p i) (p i)
  · exact Filter.Eventually.of_forall fun k => indexDephasedGram_isHermitian k p
  · intro i j
    exact ((tendsto_pi_nhds.mp (indexDephasedGram_tendsto p)) i |>
      tendsto_pi_nhds.mp) j

/-- The actual complex Weil matrix has positive semidefinite dephased tails. -/
theorem actualProbeGram_dephasing_eventually_posSemidef {n : ℕ} (p : Fin n → ℝ) :
    ∀ᶠ k in atTop, (channelPower k (fun i : Fin n => (i.val : ℝ))
      (probeGram (fun i => node (p i)))).PosSemidef := by
  filter_upwards [indexDephasedGram_eventually_posDef p] with k hk
  rw [← indexDephasedGram_map_complex]
  exact _root_.RHTower.realMatrix_posSemidef_map_complex _ hk.posSemidef

#print axioms indexDephasedGram_isHermitian
#print axioms indexDephasedGram_map_complex
#print axioms indexDephasedGram_entry_pos
#print axioms indexDephasedGram_tendsto
#print axioms indexDephasedGram_eventually_posDef
#print axioms actualProbeGram_dephasing_eventually_posSemidef
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeCuts
