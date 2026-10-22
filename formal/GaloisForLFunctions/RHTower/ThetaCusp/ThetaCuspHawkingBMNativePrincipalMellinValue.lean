import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativePrincipalPowerExpansion
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeCutoffMellinMeromorphy

/-! The original principal and cutoff moments have their complete three-power values. -/
open Complex MeasureTheory Set
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse
noncomputable section

/-- The three original principal coefficients applied to the derived cutoff continuation. -/
def nativePrincipalMomentContinuation (q : XiZeroCopy) (t : ℂ) : ℂ :=
  ∑ j : Fin 3, nativePrincipalPowerCoefficient q j*
    nativeCutoffMellinContinuation (t+nativePrincipalPowerExponent q j)

private theorem low_chamber (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) (j : Fin 3) :
    0 < (s-1+nativePrincipalPowerExponent q j).re := by
  simp only [Complex.add_re,Complex.sub_re,Complex.one_re]
  linarith [(nativePrincipalPowerExponent_re q j).1]

private theorem high_chamber (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) (j : Fin 3) :
    (nativePrincipalPowerExponent q j-s).re < 0 := by
  simp only [Complex.sub_re]
  linarith [(nativePrincipalPowerExponent_re q j).2]

/-- The actual complementary principal moment equals its full three-coefficient value. -/
theorem nativePrincipalRemainder_mellin_value (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) :
    (∫ y in Ioi (0:ℝ), (y:ℂ)^(s-2)*nativePrincipalRemainder q y) =
      nativePrincipalMomentContinuation q (s-1) := by
  have he := setIntegral_congr_fun (μ := volume) (s := Ioi (0:ℝ)) measurableSet_Ioi (fun (y : ℝ) hy => nativePrincipalRemainder_power_sum q s hy)
  have hi (j : Fin 3) : IntegrableOn (fun y : ℝ => nativePrincipalPowerCoefficient q j*
      ((1-cutoff ![0,y])*(y:ℂ)^((s-1+nativePrincipalPowerExponent q j)-1))) (Ioi (0:ℝ)) :=
    (nativeCutoffLowPower_integrable _ (low_chamber q s hs j)).const_mul _
  rw [he,integral_finsetSum _ (fun j _ => hi j)]
  unfold nativePrincipalMomentContinuation
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,nativeCutoffLowPower_value _ (low_chamber q s hs j)]

/-- The complete reflected cutoff moment has the negative of the reflected three-coefficient value. -/
theorem nativeSquareCutoffHeight_mellin_value (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) :
    (∫ y in Ioi (2:ℝ), (y:ℂ)^(-s-1)*nativeSquareCutoffHeight q y) =
      -nativePrincipalMomentContinuation q (-s) := by
  have he := setIntegral_congr_fun (μ := volume) (s := Ioi (2:ℝ)) measurableSet_Ioi
    (fun (y : ℝ) hy => nativeSquareCutoffHeight_power_sum q s (lt_trans (by norm_num : (0:ℝ)<2) hy))
  have hi (j : Fin 3) : IntegrableOn (fun y : ℝ => nativePrincipalPowerCoefficient q j*
      (cutoff ![0,y]*(y:ℂ)^((nativePrincipalPowerExponent q j-s)-1))) (Ioi (2:ℝ)) :=
    (nativeCutoffHighPower_integrable _ (high_chamber q s hs j)).const_mul _
  rw [he,integral_finsetSum _ (fun j _ => hi j)]
  unfold nativePrincipalMomentContinuation
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,nativeCutoffHighPower_value _ (high_chamber q s hs j),
    show nativePrincipalPowerExponent q j-s = -s+nativePrincipalPowerExponent q j by ring]
  ring

/-- The original finite principal moment is meromorphic for every complex testing shift. -/
theorem nativePrincipalMomentContinuation_meromorphic (q : XiZeroCopy) (t : ℂ) :
    MeromorphicAt (nativePrincipalMomentContinuation q) t := by
  apply MeromorphicAt.fun_sum
  intro j _
  apply analyticAt_const.meromorphicAt.mul
  exact (nativeCutoffMellinContinuation_meromorphic (t+nativePrincipalPowerExponent q j)).comp_analyticAt (g := fun v : ℂ => v+nativePrincipalPowerExponent q j) (x := t)
    (analyticAt_id.add analyticAt_const)

/-- Wherever its three displayed denominators are nonzero, the actual principal continuation is analytic. -/
theorem nativePrincipalMomentContinuation_analytic (q : XiZeroCopy) (t : ℂ)
    (ht : ∀ j : Fin 3, t+nativePrincipalPowerExponent q j ≠ 0) :
    AnalyticAt ℂ (nativePrincipalMomentContinuation q) t := by
  apply Finset.analyticAt_fun_sum Finset.univ
  intro j _
  exact analyticAt_const.mul ((nativeCutoffMellinContinuation_analytic (ht j)).comp (f := fun v : ℂ => v+nativePrincipalPowerExponent q j) (x := t)
    (analyticAt_id.add analyticAt_const))

end
end RHTower.D4BMJointSource
