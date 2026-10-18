import GaloisForLFunctions.RHTower.BaezDuarteBurnolMultiplicityAllZeros
import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem
import GaloisForLFunctions.RHTower.BaezDuarteMobiusCriticalTailObstruction

/-!
# Classical lower bounds for Báez–Duarte approximation

The multiplicity-weighted Burnol mass on the critical line is strictly positive,
by Hardy's theorem. It bounds the lower limit of `d_N² log N`. Separately, the
unweighted raw Möbius errors do not tend to zero. The logarithmic optimal-distance
bound is not a constant lower bound for the raw-error lower limit.
-/

open Filter Topology Complex
open scoped ENNReal

namespace RHTower

noncomputable section

/-- Burnol's mass, with conjugate critical zeros paired and multiplicities squared. -/
def burnolCriticalMass : ℝ≥0∞ :=
  ∑' ρ : criticalUpperZeros,
    ENNReal.ofReal (2 * (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 2)

/-- Hardy's theorem makes the critical-line Burnol mass strictly positive. -/
theorem burnolCriticalMass_pos : 0 < burnolCriticalMass := by
  obtain ⟨T, hT, hz⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨τ, hτ, hζ⟩ := hz T le_rfl
  have hτpos : 0 < τ := hT.trans_le hτ.1
  let ρ : criticalUpperZeros :=
    ⟨linePt τ, hζ, linePt_re τ, by simpa only [linePt_im] using hτpos⟩
  have hρ1 : (ρ : ℂ) ≠ 1 := by
    intro he
    have hre := congrArg Complex.re he
    change (linePt τ).re = (1 : ℂ).re at hre
    norm_num [linePt_re] at hre
  have hρ0 : (ρ : ℂ) ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    change (linePt τ).re = (0 : ℂ).re at hre
    norm_num [linePt_re] at hre
  have hm := (one_le_analyticOrderNatAt_and_iteratedDeriv_riemannZeta hρ1 ρ.2.1).1
  have hmpos : (0 : ℝ) < analyticOrderNatAt riemannZeta (ρ : ℂ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hnpos : 0 < ‖(ρ : ℂ)‖ := norm_pos_iff.mpr hρ0
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) (ENNReal.le_tsum ρ)

/-- Burnol's unconditional logarithmic lower bound, in the extended nonnegative reals. -/
theorem burnolCriticalMass_le_liminf_bdDistDiscrete :
    burnolCriticalMass ≤ atTop.liminf
      (fun N : ℕ => ENNReal.ofReal (bdDistDiscrete N ^ 2 * Real.log N)) := by
  apply (Filter.le_liminf_iff' (f := atTop)).mpr
  intro y hy
  have hyne : y ≠ ⊤ := ne_top_of_lt hy
  have h := eventually_le_bdDistDiscrete_sq_mul_log_of_lt_tsum_order
    (c := y.toReal) (by simpa only [burnolCriticalMass, ENNReal.ofReal_toReal hyne] using hy)
  filter_upwards [h] with N hN
  simpa only [ENNReal.ofReal_toReal hyne] using ENNReal.ofReal_le_ofReal hN

/-- The positive Burnol rate and raw Möbius nonconvergence are independent
unconditional baseline facts about the actual Báez–Duarte carrier. -/
theorem baezDuarte_classical_baseline :
    0 < burnolCriticalMass ∧
      burnolCriticalMass ≤ atTop.liminf
        (fun N : ℕ => ENNReal.ofReal (bdDistDiscrete N ^ 2 * Real.log N)) ∧
      ¬ Tendsto bdMobiusFullErrorEnergy atTop (𝓝 0) :=
  ⟨burnolCriticalMass_pos, burnolCriticalMass_le_liminf_bdDistDiscrete,
    not_tendsto_bdMobiusFullErrorEnergy_zero⟩

end

end RHTower
