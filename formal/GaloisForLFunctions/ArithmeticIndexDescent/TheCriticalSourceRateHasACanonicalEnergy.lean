import GaloisForLFunctions.ArithmeticIndexDescent.TheCriticalSourceRateIsMonotone
import GaloisForLFunctions.ArithmeticIndexDescent.TheSourceBudgetMakesTheIndexCostQuadratic

/-!
# The critical arithmetic source rate has a canonical height-square energy

Inverse-scale curvature bounds each normalized pair increment by its
nonnegative height-square limit. Positive summation then identifies the
real-scale source limit, including infinite energy. On finite off-line
support it equals the exact completed Laurent-source moment. The full
pair energy retains both the arithmetic index charges and every exterior
critical row; it is not asserted to be a positive semidefinite Gram kernel.
-/

noncomputable section

open Filter Set RHTower Zeta23
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.ArithmeticElectrostatics
open GaloisForLFunctions.ArithmeticCorrespondencePositivity
open scoped Topology ENNReal

namespace GaloisForLFunctions.ArithmeticIndexDescent

/-- Height-square reflected energy, normalized as the limit of one source-work summand. -/
def xiHeightSquarePairEnergy (p q : XiZeroCopy) : ℝ :=
  (3 / 8 : ℝ) * reflectedWork
    (xiSignedDepth p - xiSignedDepth q) (xiSignedDepth p + xiSignedDepth q)
    (xiZeroHeight p - xiZeroHeight q) (xiZeroHeight p ^ 2) (xiZeroHeight q ^ 2)

theorem xiQuadraticPairWork_quarter_tendsto (p q : XiZeroCopy) :
    Tendsto (fun R : ℝ => xiQuadraticPairWork R p q / 4) atTop
      (𝓝 (xiHeightSquarePairEnergy p q)) := by
  convert (xiQuadraticPairWork_tendsto p q).div_const 4 using 1
  congr 1
  unfold xiHeightSquarePairEnergy
  ring

/-- Nonnegativity follows before any infinite sum is taken. -/
theorem xiHeightSquarePairEnergy_nonneg (p q : XiZeroCopy) :
    0 ≤ xiHeightSquarePairEnergy p q := by
  apply ge_of_tendsto (xiQuadraticPairWork_quarter_tendsto p q)
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with R hR
  exact div_nonneg (xiQuadraticPairWork_nonneg hR p q) (by norm_num)

/-- Inverse-scale curvature supplies an exact pointwise majorant. -/
theorem xiQuadraticPairWork_quarter_le_heightSquareEnergy {R : ℝ} (hR : 4 ≤ R)
    (p q : XiZeroCopy) :
    xiQuadraticPairWork R p q / 4 ≤ xiHeightSquarePairEnergy p q := by
  apply ge_of_tendsto (xiQuadraticPairWork_quarter_tendsto p q)
  filter_upwards [eventually_ge_atTop R] with S hRS
  exact div_le_div_of_nonneg_right
    (xiQuadraticPairWork_monotoneOn p q
      (show 0 < R by linarith only [hR])
      (show 0 < S by linarith only [hR, hRS]) hRS) (by norm_num)

/-- A critical exterior row retains the off-line height weight; its own height weight cancels. -/
theorem xiHeightSquarePairEnergy_of_critical_right (p q : XiZeroCopy)
    (hq : xiSignedDepth q = 0) :
    xiHeightSquarePairEnergy p q = (3 / 4 : ℝ) * xiZeroHeight p ^ 2 *
      transverseAngular (xiSignedDepth p) (xiZeroHeight p - xiZeroHeight q) := by
  unfold xiHeightSquarePairEnergy
  rw [reflectedWork_eq_pair, hq]
  simp only [mul_zero, sub_zero, add_zero]
  unfold transverseAngular
  ring

/-- The canonical extended energy includes every ordered pair of multiplicity copies. -/
def xiCriticalSourceEnergy : ℝ≥0∞ :=
  ∑' pq : XiZeroCopy × XiZeroCopy, ENNReal.ofReal (xiHeightSquarePairEnergy pq.1 pq.2)

/-- Summable domination handles finite energy; large finite sums handle infinite energy. -/
private theorem realScale_positive_tsum_limit {ι : Type*}
    (f : ι → ℝ) (g : ℝ → ι → ℝ) (hf0 : ∀ i, 0 ≤ f i)
    (hg0 : ∀ R, 4 ≤ R → ∀ i, 0 ≤ g R i)
    (hgsum : ∀ R, 4 ≤ R → Summable (g R))
    (hdom : ∀ R, 4 ≤ R → ∀ i, g R i ≤ f i)
    (hlim : ∀ i, Tendsto (fun R => g R i) atTop (𝓝 (f i))) :
    Tendsto (fun R => ENNReal.ofReal (∑' i, g R i)) atTop
      (𝓝 (∑' i, ENNReal.ofReal (f i))) := by
  classical
  by_cases hf : Summable f
  · have hreal : Tendsto (fun R => ∑' i, g R i) atTop (𝓝 (∑' i, f i)) := by
      apply tendsto_tsum_of_dominated_convergence hf hlim
      filter_upwards [eventually_ge_atTop (4 : ℝ)] with R hR i
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 R hR i)]
      exact hdom R hR i
    have h := (ENNReal.continuous_ofReal.tendsto (∑' i, f i)).comp hreal
    rw [ENNReal.ofReal_tsum_of_nonneg hf0 hf] at h
    exact h
  · have htop : (∑' i, ENNReal.ofReal (f i)) = ⊤ := by
      by_contra h
      change (∑' i, ((f i).toNNReal : ℝ≥0∞)) ≠ ⊤ at h
      have hs := NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp h)
      exact hf (hs.congr (fun i => Real.coe_toNNReal (f i) (hf0 i)))
    rw [htop]
    apply ENNReal.tendsto_ofReal_atTop.comp
    refine tendsto_atTop.mpr fun b => ?_
    have hlarge : ∃ S : Finset ι, b < ∑ i ∈ S, f i := by
      by_contra h
      push Not at h
      exact hf (summable_of_sum_le hf0 h)
    obtain ⟨S, hS⟩ := hlarge
    have hSlim := tendsto_finsetSum S (fun i _ => hlim i)
    filter_upwards [hSlim.eventually (lt_mem_nhds hS), eventually_ge_atTop (4 : ℝ)]
      with R hR hfour
    exact hR.le.trans ((hgsum R hfour).sum_le_tsum S (fun i _ => hg0 R hfour i))

/-- The actual real-scale source rate converges to its full height-square pair energy. -/
theorem quadraticWorkIncrement_tendsto_criticalEnergy :
    Tendsto (fun R : ℝ => ENNReal.ofReal (quadraticWorkIncrement R)) atTop
      (𝓝 xiCriticalSourceEnergy) := by
  let f : XiZeroCopy × XiZeroCopy → ℝ := fun pq => xiHeightSquarePairEnergy pq.1 pq.2
  let g : ℝ → XiZeroCopy × XiZeroCopy → ℝ := fun R pq => xiQuadraticPairWork R pq.1 pq.2 / 4
  have hsum (R : ℝ) (hR : 4 ≤ R) : Summable (g R) := by
    exact ((xiQuadraticPairWork_summable hR).mul_left (1 / 4 : ℝ)).congr
      (fun pq => by dsimp only [g]; ring)
  have h := realScale_positive_tsum_limit f g
    (fun pq => xiHeightSquarePairEnergy_nonneg pq.1 pq.2)
    (fun R hR pq => div_nonneg (xiQuadraticPairWork_nonneg hR pq.1 pq.2) (by norm_num))
    hsum (fun R hR pq => xiQuadraticPairWork_quarter_le_heightSquareEnergy hR pq.1 pq.2)
    (fun pq => xiQuadraticPairWork_quarter_tendsto pq.1 pq.2)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with R hR
  congr 1
  dsimp only [g]
  rw [tsum_div_const, quadraticWorkIncrement_eq_tsum hR]

/-- Every finite scale lies below the canonical source energy. -/
theorem quadraticWorkIncrement_le_criticalEnergy {R : ℝ} (hR : 4 ≤ R) :
    ENNReal.ofReal (quadraticWorkIncrement R) ≤ xiCriticalSourceEnergy := by
  apply ge_of_tendsto quadraticWorkIncrement_tendsto_criticalEnergy
  filter_upwards [eventually_ge_atTop R] with S hRS
  exact ENNReal.ofReal_le_ofReal
    (quadraticWorkIncrement_monotoneOn hR (hR.trans hRS) hRS)

/-- On the finite stratum the canonical pair energy equals the full Laurent-source moment. -/
theorem criticalEnergy_eq_finiteSourceMoment (hfin : offLineSupport.Finite) :
    xiCriticalSourceEnergy = ENNReal.ofReal (quadraticPacketSourceMoment
      (offLineCopies_finite_of_offLineSupport_finite hfin).toFinset) :=
  tendsto_nhds_unique quadraticWorkIncrement_tendsto_criticalEnergy
    ((ENNReal.continuous_ofReal.tendsto _).comp (quadraticWorkIncrement_tendsto_sourceMoment hfin))

/-- Infinite support forces infinite canonical height-square source energy. -/
theorem criticalEnergy_eq_top_of_infinite (hinf : offLineSupport.Infinite) :
    xiCriticalSourceEnergy = ⊤ :=
  tendsto_nhds_unique quadraticWorkIncrement_tendsto_criticalEnergy
    (ENNReal.tendsto_ofReal_atTop.comp (quadraticWorkIncrement_tendsto_atTop_of_infinite hinf))

theorem criticalEnergy_ne_top_iff_finite :
    xiCriticalSourceEnergy ≠ ⊤ ↔ offLineSupport.Finite := by
  constructor
  · intro h
    by_contra hinf
    exact h (criticalEnergy_eq_top_of_infinite hinf)
  · intro hfin
    rw [criticalEnergy_eq_finiteSourceMoment hfin]
    exact ENNReal.ofReal_ne_top

theorem criticalEnergy_eq_zero_of_riemannHypothesis (hRH : RiemannHypothesis) :
    xiCriticalSourceEnergy = 0 := by
  apply tendsto_nhds_unique quadraticWorkIncrement_tendsto_criticalEnergy
  simpa only [quadraticWorkIncrement_eq_zero_of_riemannHypothesis hRH, ENNReal.ofReal_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ≥0∞)) atTop (𝓝 0))

/-- The closed exclusion quantum applies directly to the canonical full-pair energy. -/
theorem riemannHypothesis_iff_criticalEnergy_le_quantum :
    RiemannHypothesis ↔ xiCriticalSourceEnergy ≤ ENNReal.ofReal quadraticExclusionQuantum := by
  constructor
  · intro hRH
    rw [criticalEnergy_eq_zero_of_riemannHypothesis hRH]
    exact zero_le
  · intro hE
    apply riemannHypothesis_iff_cofinally_quadraticIncrement_le_exclusionQuantum.mpr
    intro T
    refine ⟨max T 4, le_max_left _ _, le_max_right _ _, ?_⟩
    have hbound := (quadraticWorkIncrement_le_criticalEnergy (le_max_right T 4)).trans hE
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    simpa only [ENNReal.toReal_ofReal (quadraticWorkIncrement_nonneg (le_max_right T 4)),
      ENNReal.toReal_ofReal quadraticExclusionQuantum_pos.le] using hreal

/-- Every finite smooth Weil index is charged in the canonical energy, including infinite energy. -/
theorem indexUnit_mul_negIndex_le_criticalEnergy {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) :
    ENNReal.ofReal (quadraticIndexUnit * (hermNegIndex
      (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) : ℝ)) ≤
        xiCriticalSourceEnergy := by
  rcases offLineSupport.finite_or_infinite with hfin | hinf
  · rw [criticalEnergy_eq_finiteSourceMoment hfin]
    exact ENNReal.ofReal_le_ofReal (indexUnit_mul_negIndex_le_sourceMoment hfin f hf hfc)
  · rw [criticalEnergy_eq_top_of_infinite hinf]
    exact le_top

/-- The arithmetic resolvent budget gives a quadratic index charge in the canonical energy. -/
theorem resolventIndexCharge_le_criticalEnergy {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) :
    ENNReal.ofReal (resolventIndexCharge
      (hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f))) ≤
        xiCriticalSourceEnergy := by
  rcases offLineSupport.finite_or_infinite with hfin | hinf
  · rw [criticalEnergy_eq_finiteSourceMoment hfin]
    exact ENNReal.ofReal_le_ofReal (resolventIndexCharge_le_sourceMoment hfin f hf hfc)
  · rw [criticalEnergy_eq_top_of_infinite hinf]
    exact le_top

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.quadraticWorkIncrement_tendsto_criticalEnergy
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.criticalEnergy_eq_finiteSourceMoment
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.criticalEnergy_ne_top_iff_finite
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.riemannHypothesis_iff_criticalEnergy_le_quantum
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.resolventIndexCharge_le_criticalEnergy
