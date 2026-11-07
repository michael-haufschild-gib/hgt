/-
Cubic cusp constant averages adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicConstantTermPole
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicCuspVolumeCoordinates
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicEisensteinEquation

/-!
# The nonzero residue of a compact cusp average

Integrate the constant Fourier mode over a compact height strip with the
actual hyperbolic volume. Its scattered height factor is positive at
`4/3`; the nonzero arithmetic residue therefore gives a nonzero averaged
residue. The incoming height term is analytic at that parameter.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified

lemma hyperbolicEisenstein_continuous (s : ℂ) (hs : 2<s.re) :
    Continuous (hyperbolicEisenstein s) := by
  exact (kernelQuotientEisenstein_contMDiff s hs).continuous.comp
    (continuous_integralOrbitProjection globalKubotaKernel)

lemma hyperbolicEisenstein_cusp_average (s : ℂ) (hs : 2<s.re) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume)=
      ∫v in Set.Icc (5:ℝ) 6,
        (((v:ℂ)^s+(v:ℂ)^(2-s)*((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0)*
          ((9*Real.sqrt 3/2:ℝ):ℂ))/(v:ℂ)^3 := by
  rw [cuspPeriodStrip_integral_coordinates _
    (hyperbolicEisenstein_continuous s hs).aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable _ (hyperbolicEisenstein_continuous s hs))]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
  have hh : (∫z in periodDomain,hyperbolicEisenstein s (cuspCoordinateLift (v,z)))=
      eisensteinFourierCoefficient v hpos s 0*((9*Real.sqrt 3/2:ℝ):ℂ) := by
    simp_rw [cuspCoordinateLift_positive v _ hpos,hyperbolicEisenstein_upperPoint]
    rw [eisensteinFourierCoefficient]
    simp only [cuspFrequency,map_zero,zero_div,neg_zero,zero_mul,
      AddChar.map_zero_eq_one,mul_one]
    exact (div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (by positivity))).symm
  dsimp only
  rw [hh,eisensteinConstantCoefficient_formula v hpos s hs]


def cuspMainHeightFactor (s : ℂ) : ℂ :=
  ((6:ℂ)^(s-2)-(5:ℂ)^(s-2))/(s-2)

def cuspScatterHeightFactor (s : ℂ) : ℂ :=
  ((5:ℂ)^(-s)-(6:ℂ)^(-s))/s

lemma cuspHeightPower_integrable (s : ℂ) :
    IntegrableOn (fun v : ℝ => (v:ℂ)^s) (Set.Icc (5:ℝ) 6) volume := by
  apply ContinuousOn.integrableOn_Icc
  intro v hv
  exact (Complex.continuousAt_ofReal_cpow_const v s (Or.inr (by linarith [hv.1]))).continuousWithinAt

lemma cuspMainHeightFactor_integral (s : ℂ) (hs : s≠2) :
    (∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(s-3))=cuspMainHeightFactor s := by
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (5:ℝ)≤6)]
  have hr : s-3≠(-1:ℂ) := by intro h; apply hs; linear_combination h
  rw [integral_cpow (Or.inr ⟨hr,by norm_num⟩)]
  change ((6:ℂ)^(s-3+1)-(5:ℂ)^(s-3+1))/(s-3+1)=_
  have he : s-3+1=s-2 := by ring
  rw [he]
  rfl

lemma cuspScatterHeightFactor_integral (s : ℂ) (hs : s≠0) :
    (∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-s-1))=cuspScatterHeightFactor s := by
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (5:ℝ)≤6)]
  have hr : -s-1≠(-1:ℂ) := by intro h; apply hs; linear_combination -h
  rw [integral_cpow (Or.inr ⟨hr,by norm_num⟩)]
  change ((6:ℂ)^(-s-1+1)-(5:ℂ)^(-s-1+1))/(-s-1+1)=_
  have he : -s-1+1=-s := by ring
  rw [he,cuspScatterHeightFactor]
  ring

lemma cuspMainHeightFactor_differentiableAt (s : ℂ) (hs : s≠2) :
    DifferentiableAt ℂ cuspMainHeightFactor s := by
  have hd : DifferentiableAt ℂ (fun z : ℂ => z-2) s := differentiableAt_id.sub_const 2
  exact ((hd.const_cpow (Or.inl (by norm_num))).sub
    (hd.const_cpow (Or.inl (by norm_num)))).div hd (sub_ne_zero.mpr hs)

lemma cuspScatterHeightFactor_differentiableAt (s : ℂ) (hs : s≠0) :
    DifferentiableAt ℂ cuspScatterHeightFactor s := by
  have hd : DifferentiableAt ℂ (fun z : ℂ => -z) s := differentiableAt_id.neg
  exact ((hd.const_cpow (Or.inl (by norm_num))).sub
    (hd.const_cpow (Or.inl (by norm_num)))).div differentiableAt_id hs

def cuspConstantAverage (s : ℂ) : ℂ :=
  ((9*Real.sqrt 3/2:ℝ):ℂ)*(cuspMainHeightFactor s+
    ((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0*cuspScatterHeightFactor s)

lemma hyperbolicEisenstein_cusp_average_eq (s : ℂ) (hs : 2<s.re) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume)=
      cuspConstantAverage s := by
  have hs2 : s≠2 := by intro he; subst s; norm_num at hs
  have hs0 : s≠0 := by intro he; subst s; norm_num at hs
  rw [hyperbolicEisenstein_cusp_average s hs]
  have heq : (∫v in Set.Icc (5:ℝ) 6,
      (((v:ℂ)^s+(v:ℂ)^(2-s)*((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0)*
        ((9*Real.sqrt 3/2:ℝ):ℂ))/(v:ℂ)^3)=
      ∫v in Set.Icc (5:ℝ) 6,((9*Real.sqrt 3/2:ℝ):ℂ)*
        ((v:ℂ)^(s-3)+(((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0)*(v:ℂ)^(-s-1)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith [hv.1])
    have h1 : (v:ℂ)^(s-3)=(v:ℂ)^s/(v:ℂ)^3 := by
      rw [Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    have h2 : (v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
      rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    dsimp only
    rw [h1,h2]
    ring
  rw [heq,integral_const_mul,integral_add (cuspHeightPower_integrable _)
    ((cuspHeightPower_integrable _).const_mul _),integral_const_mul,
    cuspMainHeightFactor_integral s hs2,cuspScatterHeightFactor_integral s hs0]
  rfl

lemma cuspConstantAverage_differentiableAt (s : ℂ) (hs : 4/3<s.re) (hs2 : s≠2) :
    DifferentiableAt ℂ cuspConstantAverage s := by
  have hs0 : s≠0 := by intro he; subst s; norm_num at hs
  have hs1 : s≠1 := by intro he; subst s; norm_num at hs
  have hsc : DifferentiableAt ℂ (fun z : ℂ => scatteringCoefficient z 0) s :=
    (arithmeticDirichletSeries_zero_differentiableAt s hs).div_const _
  exact ((cuspMainHeightFactor_differentiableAt s hs2).add
    ((((differentiableAt_const (Real.pi:ℂ)).div (differentiableAt_id.sub_const 1)
      (sub_ne_zero.mpr hs1)).mul hsc).mul
      (cuspScatterHeightFactor_differentiableAt s hs0))).const_mul _

lemma cuspScatterHeightFactor_center_re_pos :
    0<(cuspScatterHeightFactor (4/3:ℂ)).re := by
  have h5 := Complex.ofReal_cpow (by norm_num : (0:ℝ)≤5) (-(4/3:ℝ))
  have h6 := Complex.ofReal_cpow (by norm_num : (0:ℝ)≤6) (-(4/3:ℝ))
  norm_num only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat] at h5 h6
  have he : cuspScatterHeightFactor (4/3:ℂ)=
      (((5:ℝ)^(-(4/3:ℝ))-(6:ℝ)^(-(4/3:ℝ)))/(4/3:ℝ):ℝ) := by
    rw [cuspScatterHeightFactor,←h5,←h6]
    push_cast
    rfl
  rw [he,Complex.ofReal_re]
  apply div_pos
  · exact sub_pos.mpr (Real.rpow_lt_rpow_of_neg (by norm_num) (by norm_num) (by norm_num))
  · norm_num

def cuspConstantAverageResidue : ℂ :=
  ((9*Real.sqrt 3/2:ℝ):ℂ)*(3*(Real.pi:ℂ))*constantArithmeticResidue*
    cuspScatterHeightFactor (4/3:ℂ)

lemma cuspConstantAverageResidue_ne_zero : cuspConstantAverageResidue≠0 := by
  apply mul_ne_zero
  · exact mul_ne_zero (mul_ne_zero cusp_volume_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
      constantArithmeticResidue_ne_zero
  · intro he
    have hh := cuspScatterHeightFactor_center_re_pos
    rw [he,Complex.zero_re] at hh
    exact lt_irrefl 0 hh

lemma cuspConstantAverage_oneSidedResidue :
    Tendsto (fun x : ℝ => ((x:ℂ)-(4/3:ℂ))*cuspConstantAverage (x:ℂ))
      (𝓝[>] (4/3:ℝ)) (𝓝 cuspConstantAverageResidue) := by
  have harg : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] (4/3:ℝ)) (𝓝 (4/3:ℂ)) := by
    convert Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 ; norm_num
  have hlinear := harg.sub_const (4/3:ℂ)
  norm_num only [sub_self] at hlinear
  have hm := (cuspMainHeightFactor_differentiableAt (4/3:ℂ) (by norm_num)).continuousAt.tendsto.comp harg
  have hh := (cuspScatterHeightFactor_differentiableAt (4/3:ℂ) (by norm_num)).continuousAt.tendsto.comp harg
  have hpi : Tendsto (fun x : ℝ => (Real.pi:ℂ)/((x:ℂ)-1))
      (𝓝[>] (4/3:ℝ)) (𝓝 (3*(Real.pi:ℂ))) := by
    have hpiconst : Tendsto (fun _ : ℝ => (Real.pi:ℂ))
        (𝓝[>] (4/3:ℝ)) (𝓝 (Real.pi:ℂ)) := tendsto_const_nhds
    convert hpiconst.div (harg.sub_const 1) (by norm_num : (4/3:ℂ)-1≠0) using 1 <;> try rfl
    congr 1
    ring
  have hall := ((hlinear.mul hm).add
    ((hpi.mul scatteringCoefficient_zero_oneSidedResidue).mul hh)).const_mul
      ((9*Real.sqrt 3/2:ℝ):ℂ)
  convert hall using 1 <;> try rfl
  · ext x
    dsimp only [cuspConstantAverage,Function.comp_def]
    ring
  · simp only [zero_mul,zero_add,cuspConstantAverageResidue]
    ring_nf


#print axioms hyperbolicEisenstein_cusp_average_eq
#print axioms cuspConstantAverageResidue_ne_zero
#print axioms cuspConstantAverage_oneSidedResidue
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
