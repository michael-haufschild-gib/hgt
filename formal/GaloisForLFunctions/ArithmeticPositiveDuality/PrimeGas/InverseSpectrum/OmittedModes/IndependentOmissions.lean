import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.FamilyLoss
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.ProgressionReadings

/-! # Independent omissions in disjoint occupation progressions -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap

variable {r : ℕ}

/-- One genuinely missing wave in each progression. -/
def laneWaves (u : Fin r → MissingWave) (i : Fin r) : Gas :=
  extendModes (progression i) (u i).val

private theorem separate_waves (u : Fin r → MissingWave) (i j : Fin r) (hij : i ≠ j) :
    inner ℂ (laneWaves u i) (laneWaves u j) = 0 :=
  extendModes_orthogonal (progression_separate hij) _ _

private theorem waves_nonzero (u : Fin r → MissingWave) (i : Fin r) : laneWaves u i ≠ 0 :=
  fun h => missingWave_ne_zero (u i) ((extendModes (progression i)).injective (h.trans (map_zero _).symm))

/-- A linear combination in the heat range must vanish separately in every omitted lane. -/
theorem lane_span_meets_heat (u : Fin r → MissingWave) {x : Gas}
    (hs : x ∈ familySpan (laneWaves u)) (hx : x ∈ LinearMap.range criticalOperator.toLinearMap) :
    x = 0 := by
  classical
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hs
  have hz (i : Fin r) : c i = 0 := by
    by_contra hn
    have hi := restrictModes_mem_heat (progression_increases i) hx
    rw [← hc,map_sum] at hi
    simp only [map_smul] at hi
    rw [Finset.sum_eq_single i (fun j _ hj => by
      change c j • restrictModes (progression i) (extendModes (progression j) (u j).val) = 0
      rw [restrict_extend_disjoint (progression_separate hj.symm),smul_zero])
      (fun h => (h (Finset.mem_univ i)).elim)] at hi
    change c i • restrictModes (progression i) (extendModes (progression i) (u i).val) ∈ _ at hi
    rw [restrict_extend] at hi
    exact (u i).property (((LinearMap.range criticalOperator.toLinearMap).smul_mem_iff hn).mp hi)
  rw [← hc]
  simp only [hz,zero_smul,Finset.sum_const_zero]

theorem laneFamily_conserves (u : Fin r → MissingWave) :
    Conserving (projected (omitFamily (laneWaves u))) := by
  let P := omitFamily (laneWaves u)
  rw [projected_conserves_iff]
  intro x y he
  have hk : criticalOperator (x-y) ∈ P.val.toLinearMap.ker := by
    change P.val (criticalOperator (x-y)) = 0
    rw [map_sub,map_sub,sub_eq_zero]
    exact he
  rw [omitFamily_ker] at hk
  have hz := lane_span_meets_heat u hk ⟨x-y,rfl⟩
  exact sub_eq_zero.mp (critical_injective (hz.trans (map_zero _).symm))

/-- Independent choices in the lanes give a physical rank-r reading equal to the sum of their costs. -/
theorem sum_lane_losses_mem (u : Fin r → MissingWave) :
    (∑ i, lineLoss (laneWaves u i)) ∈ lossesAtRank r := by
  refine ⟨omitFamily (laneWaves u),missingDimension_family (waves_nonzero u) (separate_waves u),
    laneFamily_conserves u,traceLoss_family (waves_nonzero u) (separate_waves u) ?_⟩
  intro i j hij
  obtain ⟨a,ha⟩ := heat_extendModes (progression i) (u i).val
  obtain ⟨b,hb⟩ := heat_extendModes (progression j) (u j).val
  change inner ℂ (criticalOperator (extendModes (progression i) _)) (criticalOperator (extendModes (progression j) _)) = 0
  rw [ha,hb]
  exact extendModes_orthogonal (progression_separate hij) a b

#print axioms lane_span_meets_heat
#print axioms laneFamily_conserves
#print axioms sum_lane_losses_mem

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
