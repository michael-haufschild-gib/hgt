import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheExponentOfTheAccumulatedGcdShortfall
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.SuperlinearOsgoodScale

/-!
# Osgood weighting on the arithmetic shortfall

The primitive of 1/(z(1+log(1/z))) in Borrin–Nariyoshi's Osgood
change of variable (arXiv:2608.08337, Lemma 3.2) becomes
log(1+log(1+D)) after setting z=1/(1+D) and reversing the sign.
Weighting each gcd shortfall by this primitive's right-endpoint
derivative has a convergent quadrature error. Exponentiating the sum
recovers the grid exponent up to a positive constant.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology
open GaloisForLFunctions.CumulativeQuadrature
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The shortfall at each step is discounted by its accumulated value and
by one additional logarithm of that value. -/
def gcdOsgoodSum (r : ℕ) : ℕ → ℝ := rightSum (powerGridGcdDeficit r) logLogScaleDeriv

private theorem deriv_anti : AntitoneOn logLogScaleDeriv (Set.Ici 0) := by
  intro a ha b _ hab
  have ha₀ := Set.mem_Ici.mp ha
  have h₁ := add_le_add_right hab (1:ℝ)
  have h₂ := Real.log_le_log (by linarith only [ha₀]) h₁
  have h := mul_le_mul h₁ (add_le_add_right h₂ 1)
    (zero_le_one.trans (one_le_one_add_log_one_add ha₀)) (by linarith only [ha₀,hab])
  exact one_div_le_one_div_of_le (logLogGrowth_pos ha₀) h

private theorem zero_origin (r : ℕ) : powerGridGcdDeficit r 0 = 0 := by simp [powerGridGcdDeficit]

private theorem osgood_defect (r k : ℕ) :
    defect (powerGridGcdDeficit r) logLogScaleDeriv k =
      logLogScale (powerGridGcdDeficit r k) - gcdOsgoodSum r k := by
  rw [defect, zero_origin]
  congr 1
  have hD : 0 ≤ powerGridGcdDeficit r k := Finset.sum_nonneg fun _ _ => le_max_right _ _
  have hi : Set.uIcc 0 (powerGridGcdDeficit r k) ⊆ Set.Ici 0 := by
    rw [Set.uIcc_of_le hD]; exact Set.Icc_subset_Ici_self
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_logLogScale (Set.mem_Ici.mp (hi ht))) (deriv_anti.mono hi).intervalIntegrable
  simpa only [show logLogScale 0 = 0 by simp [logLogScale], sub_zero] using h

/-- The loss in the Osgood sum has a finite part with an explicit tail
bound at every arithmetic endpoint. -/
theorem osgood_gcd_finite_part (r : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ Tendsto (fun k => logLogScale (powerGridGcdDeficit r k) - gcdOsgoodSum r k)
      atTop (𝓝 c) ∧ ∀ k, 0 ≤ c - (logLogScale (powerGridGcdDeficit r k)-gcdOsgoodSum r k) ∧
        c - (logLogScale (powerGridGcdDeficit r k)-gcdOsgoodSum r k) ≤
          Real.log 2 * logLogScaleDeriv (powerGridGcdDeficit r k) := by
  have ha : AntitoneOn logLogScaleDeriv (Set.Ici (powerGridGcdDeficit r 0)) := by
    rw [zero_origin]; exact deriv_anti
  obtain ⟨c,hc,he⟩ := limiting_defect (monotone_gcd_deficit r) ha
    (fun k => logLogScaleDeriv_nonneg (Finset.sum_nonneg (fun _ _ => le_max_right _ _) :
      0 ≤ powerGridGcdDeficit r k)) (fun k => (gcd_deficit_increment_bounds r k).2)
  have hp := (he 0).1
  simp only [defect, intervalIntegral.integral_same, rightSum, Finset.range_zero, Finset.sum_empty,
    sub_zero] at hp
  exact ⟨c,hp,hc.congr (osgood_defect r), fun k => by simpa only [osgood_defect] using he k⟩

/-- A positive normalization recovers the exact zero-width exponent from
the exponentially rescaled Osgood sum. -/
theorem calibrated_osgood_gcd_amplitude (s : ℕ) :
    ∃ A : ℝ, 0 < A ∧ A ≤ 1 ∧ Tendsto (fun k : ℕ => Real.exp (gcdOsgoodSum (s+2) k)/Real.log k)
      atTop (𝓝 (A*gcdGridExponent (s+2))) := by
  let r := s+2
  obtain ⟨c,hc,hlim,_⟩ := osgood_gcd_finite_part r
  have hl : Tendsto (fun k : ℕ => Real.log k) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hn := (tendsto_const_nhds (x := (1:ℝ))).div_atTop hl
  have hquot := hn.add (gcd_grid_logarithmic_exponent s)
  rw [zero_add] at hquot
  refine ⟨Real.exp (-c),Real.exp_pos _,Real.exp_le_one_iff.mpr (neg_nonpos.mpr hc),
    (hlim.neg.exp.mul hquot).congr fun k => ?_⟩
  have hD : 0 ≤ powerGridGcdDeficit r k := Finset.sum_nonneg fun _ _ => le_max_right _ _
  have harg : 0 < 1 + Real.log (1 + powerGridGcdDeficit r k) :=
    zero_lt_one.trans_le (one_le_one_add_log_one_add hD)
  change Real.exp (-(logLogScale (powerGridGcdDeficit r k) - gcdOsgoodSum r k)) *
    (1 / Real.log k + Real.log (1+powerGridGcdDeficit r k)/Real.log k) = _
  rw [neg_sub, Real.exp_sub, logLogScale, Real.exp_log harg, ←add_div]
  rw [← mul_div_assoc, div_mul_cancel₀ _ harg.ne']

/-- The amplitude vanishes precisely at or below the closed abscissa
threshold. This is an all-endpoint limit. -/
theorem osgood_gcd_amplitude_zero_iff (s : ℕ) :
    Tendsto (fun k : ℕ => Real.exp (gcdOsgoodSum (s+2) k)/Real.log k) atTop (𝓝 0) ↔
      _root_.RHTower.zetaZeroAbscissa ≤ ((s:ℝ)+1)/((s:ℝ)+2) := by
  obtain ⟨A,hA,_,ht⟩ := calibrated_osgood_gcd_amplitude s
  have hz : gcdGridExponent (s+2) = 0 ↔
      _root_.RHTower.zetaZeroAbscissa ≤ ((s:ℝ)+1)/((s:ℝ)+2) := by
    rw [gcdGridExponent, max_eq_left_iff, le_div_iff₀ (by positivity : 0 < (s:ℝ)+2)]
    push_cast
    constructor <;> intro h <;> linarith only [h]
  constructor
  · intro h
    exact hz.mp ((mul_eq_zero.mp (tendsto_nhds_unique ht h)).resolve_left hA.ne')
  · intro h
    rwa [hz.mpr h, mul_zero] at ht

#print axioms osgood_gcd_finite_part
#print axioms calibrated_osgood_gcd_amplitude
#print axioms osgood_gcd_amplitude_zero_iff

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
