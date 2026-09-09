import GaloisForLFunctions.HTGeometry.FokasLenellsRawMixedPrimitive

/-!
# Explicit evaluation of the actual second solution coefficient

The genuine second coefficient is diagonal in the initial vector. Its two
entries are expressed through the bounded mixed primitive J = integral q g′,
where g(x) = q(-x). Differentiating these formulas and checking the anchor
identifies them with the constructed integral coefficients.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

theorem rawReflectedProfile_hasDerivAt (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => q (-y)) (reflectedDerivative q x) x := by
  have hh := (q.hasDerivAt (-x)).scomp x (hasDerivAt_id x).neg
  convert! hh using 1
  simp only [reflectedDerivative,_root_.neg_apply,RHTower.negSchwartz'_apply,
    SchwartzMap.derivCLM_apply,neg_one_smul]

/-- At zero frequency the second integrand is diagonal and has an explicit local formula. -/
theorem rawSecondIntegrand_zero_apply (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    rawSecondIntegrand q 0 v x =
      (-reflectedDerivative q x*(q x-q 0)*v.1,
       -SchwartzMap.derivCLM ℂ ℂ q x*(q (-x)-q 0)*v.2) := by
  unfold rawSecondIntegrand
  simp only [Complex.ofReal_zero,zero_smul,add_zero,rawSolutionSlope_zero,
    rawDividedOperator_apply,rawLinearCoefficient,rawLinearPrimitive,
    zero_pow (by omega : 2 ≠ 0),mul_zero,neg_zero,FDNLS.staggerPhase,
    Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one]
  apply Prod.ext
  · simp only [Prod.snd_sub]
    ring_nf
    simp only [I_sq]
    ring
  · simp only [Prod.fst_sub]
    ring_nf
    simp only [I_sq]
    ring

def rawSecondPrimitive (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) : SpectralVector :=
  ((-rawMixedPrimitive q x+q 0*q (-x)-(q 0)^2)*v.1,
   (rawMixedPrimitive q x-q x*q (-x)+q 0*q x)*v.2)

theorem rawSecondPrimitive_hasDerivAt (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    HasDerivAt (rawSecondPrimitive q v) (rawSecondIntegrand q 0 v x) x := by
  have hq := q.hasDerivAt x
  have hg := rawReflectedProfile_hasDerivAt q x
  have hJ := rawMixedPrimitive_hasDerivAt q x
  have h1 := (((hJ.neg.add (hg.const_mul (q 0))).sub (hasDerivAt_const x ((q 0)^2))).mul_const v.1)
  have h2 := ((hJ.sub (hq.mul hg)).add (hq.const_mul (q 0))).mul_const v.2
  convert! h1.prodMk h2 using 1
  rw [rawSecondIntegrand_zero_apply]
  apply Prod.ext <;> simp only [SchwartzMap.derivCLM_apply] <;> ring

theorem rawSecondPrimitive_initial (q : SchwartzMap ℝ ℂ) (v : SpectralVector) :
    rawSecondPrimitive q v 0 = 0 := by
  simp only [rawSecondPrimitive,rawMixedPrimitive_initial,neg_zero]
  apply Prod.ext <;> simp only [Prod.fst_zero,Prod.snd_zero] <;> ring

/-- The explicitly evaluated primitive is the second coefficient of the actual original flow. -/
theorem rawSecondSlope_zero_eq (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    rawSecondSlope q 0 v x = rawSecondPrimitive q v x := by
  have hi : IntervalIntegrable (rawSecondIntegrand q 0 v) volume 0 x :=
    (rawSecondIntegrand_integrable q 0 v).intervalIntegrable
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => rawSecondPrimitive_hasDerivAt q v s) hi
  change (∫ s in (0 : ℝ)..x, rawSecondIntegrand q 0 v s) = rawSecondPrimitive q v x
  rw [hh,rawSecondPrimitive_initial,sub_zero]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
