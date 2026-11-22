import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedVariance.Renewal

/-!
# Four-strip continuation of the centered partition

Clearing both scale denominators gives a holomorphic numerator. The
identity principle identifies it with the original centered germ across
the full overlap, including removable clock points.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedVariance

open BalancedContinuation BalancedShift Filter Set
open scoped Topology

abbrev Region := {s : ℂ // -(7/2) < s.re}

def centeredNum (t : ExceptionalTime) (j : ℕ) (s : ℂ) :=
  denominator t j s*correctionTrace t j 1 (center t j) s +
    (quadraticNumerator t j s-s*(center t j:ℂ)*numerator t j (s+1))

theorem centeredNum_analytic (t : ExceptionalTime) (j : ℕ) (s : Strip) :
    AnalyticAt ℂ (centeredNum t j) s.val := by
  have h₁ : -(1/2) < (s.val+1).re := by rw [Complex.add_re,Complex.one_re]; linarith only [s.property]
  have hN := (numerator_analytic t j ⟨s.val+1,h₁⟩).comp (f := fun z : ℂ => z+1) (analyticAt_id.add analyticAt_const)
  exact ((scaleFactor_analytic _ _).mul (correction_analytic t j zero_lt_one
    (add_pos zero_lt_one (center_pos t j)) s)).add
    ((quadratic_analytic t j s).sub ((analyticAt_id.mul analyticAt_const).mul hN))

theorem centeredNum_physical (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 1/2 < z.re}) :
    centeredNum t j s.val = denominator t j s.val*physical t j s.val := by
  have h := extension_agrees t j ⟨center t j,by linarith only [center_pos t j]⟩ s
  simp only [extension,background,sub_self,mul_zero,zero_mul,add_zero] at h
  change _ = denominator t j s.val*partition t j (center t j) s.val
  rw [← h,centeredNum,mul_add,mul_div_cancel₀' _ (scale_right t j s)]

theorem centeredNum_clock (t : ExceptionalTime) (j : ℕ) (k : ℤ) :
    centeredNum t j (point t j k) = numerator t j (point t j k) := by
  let w := point t j k
  have h₁ : 1/2 < (w+1).re := by change (1/2:ℝ) < 1/2+1; norm_num
  have hz : denominator t j w = 0 := (scaleFactor_zero_iff _ _).mpr ⟨k,rfl⟩
  have h := digit_expansion t j ⟨w,by change -(1/2:ℝ) < 1/2; norm_num⟩
  change quadraticNumerator t j w = numerator t j w+w*_*_ at h
  rw [← scale_difference,hz,sub_zero] at h
  change centeredNum t j w = _
  rw [centeredNum,hz,zero_mul,zero_add,h,physical_num t j ⟨w+1,h₁⟩]
  ring

def fullNum (t : ExceptionalTime) (j : ℕ) (s : ℂ) :=
  regular t j 3 s*denominator t j (s+2)+varianceFactor t j s*centeredNum t j (s+2)

def fullScale (t : ExceptionalTime) (j : ℕ) (s : ℂ) := denominator t j s*denominator t j (s+2)

def continued (t : ExceptionalTime) (j : ℕ) (s : ℂ) := fullNum t j s/fullScale t j s

theorem varianceFactor_analytic (t : ExceptionalTime) (j : ℕ) (s : ℂ) : AnalyticAt ℂ (varianceFactor t j) s := by
  have hw := ((weight_entire (base_pos t j)).analyticAt (s+2)).comp (f := fun z : ℂ => z+2)
    (analyticAt_id.add analyticAt_const)
  exact (((((analyticAt_id.mul (analyticAt_id.add analyticAt_const)).mul analyticAt_const).mul analyticAt_const).mul hw).div
    analyticAt_const (by norm_num))

theorem movedScale_analytic (t : ExceptionalTime) (j : ℕ) (s : ℂ) :
    AnalyticAt ℂ (fun z => denominator t j (z+2)) s :=
  (scaleFactor_analytic _ _).comp (analyticAt_id.add analyticAt_const)

theorem fullNum_analytic (t : ExceptionalTime) (j : ℕ) (s : Region) : AnalyticAt ℂ (fullNum t j) s.val := by
  have hreg := regular_analytic t j 3 ⟨s.val,by norm_num at ⊢; linarith only [s.property]⟩
  have hm : -(3/2) < (s.val+2).re := by rw [Complex.add_re,Complex.ofNat_re]; linarith only [s.property]
  have hN := (centeredNum_analytic t j ⟨s.val+2,hm⟩).comp (f := fun z : ℂ => z+2)
    (analyticAt_id.add analyticAt_const)
  exact (hreg.mul (movedScale_analytic t j _)).add ((varianceFactor_analytic t j _).mul hN)

theorem scale_analytic (t : ExceptionalTime) (j : ℕ) (s : ℂ) : AnalyticAt ℂ (fullScale t j) s :=
  (scaleFactor_analytic _ _).mul (movedScale_analytic t j _)

theorem continued_meromorphic (t : ExceptionalTime) (j : ℕ) (s : Region) :
    MeromorphicAt (continued t j) s.val :=
  (fullNum_analytic t j s).meromorphicAt.div (scale_analytic t j _).meromorphicAt

private theorem physical_num (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 1/2 < z.re}) :
    fullNum t j s.val = fullScale t j s.val*physical t j s.val := by
  have h₂ : 1/2 < (s.val+2).re := by rw [Complex.add_re,Complex.ofNat_re]; linarith only [s.property]
  rw [fullNum,fullScale,centeredNum_physical t j ⟨s.val+2,h₂⟩]
  linear_combination -(denominator t j (s.val+2))*(variance_renewal t j s)

theorem continued_agrees (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 1/2 < z.re}) :
    continued t j s.val = physical t j s.val := by
  have h₂ : 1/2 < (s.val+2).re := by rw [Complex.add_re,Complex.ofNat_re]; linarith only [s.property]
  rw [continued,physical_num,mul_div_cancel_left₀ _ (mul_ne_zero (scale_right t j s) (scale_right t j ⟨s.val+2,h₂⟩))]

/-- Clearing scale factors compares the analytic numerators even at their common zeros. -/
theorem overlap (t : ExceptionalTime) (j : ℕ) (s : Strip) :
    fullNum t j s.val = centeredNum t j s.val*denominator t j (s.val+2) := by
  let U := {z : ℂ | -(3/2) < z.re}
  have hF : AnalyticOnNhd ℂ (fullNum t j) U := fun z hz =>
    fullNum_analytic t j ⟨z,by change -(3/2) < z.re at hz; linarith only [hz]⟩
  have hG : AnalyticOnNhd ℂ (fun z => centeredNum t j z*denominator t j (z+2)) U :=
    fun z hz => (centeredNum_analytic t j ⟨z,hz⟩).mul (movedScale_analytic t j z)
  have hc : Convex ℝ U := convex_halfSpace_gt Complex.reCLM.toLinearMap _
  have h₀ : (2:ℂ) ∈ U := by change -(3/2:ℝ) < 2; norm_num
  apply hF.eqOn_of_preconnected_of_eventuallyEq hG hc.isPreconnected h₀ _ s.property
  have hnh := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (2:ℂ) ∈ {z : ℂ | 1/2 < z.re} by change (1/2:ℝ) < 2; norm_num)
  filter_upwards [hnh] with z hz
  rw [physical_num t j ⟨z,hz⟩,centeredNum_physical t j ⟨z,hz⟩,fullScale]
  ring

#print axioms continued_agrees
#print axioms continued_meromorphic
#print axioms overlap

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedVariance
