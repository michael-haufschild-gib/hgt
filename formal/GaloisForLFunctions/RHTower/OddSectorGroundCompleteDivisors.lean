import GaloisForLFunctions.RHTower.OddSectorGroundSpectralQuotient
import GaloisForLFunctions.RHTower.OddSectorGroundDivisionEigenvectors
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Completeness of the actual odd ground divisors

The common annihilator of every real squared-frequency ground divisor is
exactly the finite arithmetic ground radical. This removes the possible
infinite residual space left by finite cardinal interpolation. The proof
uses the compact normalized division operator, the actual corrected form,
and the origin derivative repair.
-/

open Complex Set Filter Topology
open scoped InnerProduct ComplexConjugate
noncomputable section
namespace RHTower.OddSector
open GaloisForLFunctions.HTGeometry.FourierLaplaceDivision
open CCMRealRootedGround CCMGroundStructure CCMGroundQuadrature

def oddGroundInvisibleSpace (a : SuzukiPositiveAperture)
    (G : CCMArchimedeanFormDomain a) : Submodule ℂ (CCMArchimedeanFormDomain a) where
  carrier := {u | ccmArchimedeanFormReflection a u = -u ∧
    ∀ v : CCMArchimedeanFormDomain a, IsOddGroundDivisor a G v →
      arithmeticShiftedForm a v u = 0}
  zero_mem' := by
    refine ⟨by simp,fun v _hv => ?_⟩
    unfold arithmeticShiftedForm arithmeticForm
    simp
  add_mem' := by
    rintro u v ⟨hu,hiu⟩ ⟨hv,hiv⟩
    refine ⟨by rw [map_add,hu,hv,neg_add],fun w hw => ?_⟩
    rw [arithmeticShiftedForm_add_right,hiu w hw,hiv w hw,add_zero]
  smul_mem' := by
    rintro c u ⟨hu,hiu⟩
    refine ⟨by rw [map_smul,hu,smul_neg],fun w hw => ?_⟩
    rw [arithmeticShiftedForm_smul_right,hiu w hw,mul_zero]

theorem oddGroundInvisibleSpace_isClosed (a : SuzukiPositiveAperture)
    (G : CCMArchimedeanFormDomain a) :
    IsClosed (oddGroundInvisibleSpace a G : Set (CCMArchimedeanFormDomain a)) := by
  change IsClosed ({u | ccmArchimedeanFormReflection a u = -u} ∩
    {u | ∀ v : CCMArchimedeanFormDomain a, IsOddGroundDivisor a G v →
      arithmeticShiftedForm a v u = 0})
  refine (isClosed_eq (ccmArchimedeanFormReflection a).continuous continuous_id.neg).inter ?_
  simp only [setOf_forall]
  exact isClosed_iInter fun v => isClosed_iInter fun _hv =>
    isClosed_eq (arithmeticShiftedForm_continuous_right a v) continuous_const

theorem oddGroundSpace_le_invisible (a : SuzukiPositiveAperture)
    (G : CCMArchimedeanFormDomain a) :
    oddArithmeticGroundSpace a ≤ oddGroundInvisibleSpace a G := by
  intro u hu
  exact ⟨hu.2,fun v _hv => arithmeticShiftedForm_ground_right a hu v⟩

theorem groundDivisionCLM_preserves_invisible (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    (b : ℝ) (hb : 0 < b)
    (hz : unitaryLaplace (timeRep a G) (I*(b : ℂ)) ≠ 0)
    {u : CCMArchimedeanFormDomain a} (hu : u ∈ oddGroundInvisibleSpace a G) :
    groundDivisionCLM a hG b hb hz u ∈ oddGroundInvisibleSpace a G := by
  refine ⟨groundDivisionCLM_odd a hG b hb hz u,fun v hv => ?_⟩
  obtain ⟨c,hc,hvo,hfac⟩ := hv
  rw [groundDivisionCLM_symmetric_form a hG b hb hz hvo hu.1,
    groundDivisionCLM_groundDivisor a hG b hb hz ⟨c,hc,hvo,hfac⟩,
    arithmeticShiftedForm_smul_left,hu.2 v ⟨c,hc,hvo,hfac⟩,mul_zero]

private theorem exists_imaginary_nonzero_of_deriv {F : ℂ → ℂ}
    (hF : HasDerivAt F (deriv F 0) 0) (hd : deriv F 0 ≠ 0) :
    ∃ b : ℝ, 0 < b ∧ F (I*(b : ℂ)) ≠ 0 := by
  have he : ∀ᶠ z in 𝓝[≠] (0 : ℂ), F z ≠ 0 := hF.eventually_ne hd
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhdsWithin_iff.mp he
  refine ⟨ε/2,by positivity,hball ?_⟩
  constructor
  · change dist (I*((ε/2 : ℝ) : ℂ)) 0 < ε
    rw [dist_zero_right,norm_mul,norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < ε/2)]
    linarith
  · exact mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr (by positivity : ε/2 ≠ 0))

/-- The imaginary normalization point always exists for the actual canonical
ground generator; it is not an added source premise. -/
theorem exists_oddGround_imaginary_anchor (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G) :
    ∃ b : ℝ, 0 < b ∧ unitaryLaplace (timeRep a G) (I*(b : ℂ)) ≠ 0 := by
  by_cases hd : deriv (unitaryLaplace (timeRep a G)) 0 = 0
  · obtain ⟨v,hv,hfac⟩ := exists_odd_origin_paired_div a hG.1.2 hd
    have hvd := oddGroundGenerator_origin_quotient_deriv_ne_zero a hG hv hfac
    obtain ⟨b,hb,hbz⟩ := exists_imaginary_nonzero_of_deriv (transform_hasDerivAt a v 0) hvd
    refine ⟨b,hb,?_⟩
    rw [hfac]
    exact mul_ne_zero (pow_ne_zero 2
      (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hb.ne'))) hbz
  · exact exists_imaginary_nonzero_of_deriv (transform_hasDerivAt a G 0) hd

/-- **Complete ground-divisor detection.** The only odd sources invisible to
every ground divisor are the actual arithmetic ground states. -/
theorem oddGroundInvisibleSpace_eq_ground (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G) :
    oddGroundInvisibleSpace a G = oddArithmeticGroundSpace a := by
  obtain ⟨b,hb,hz⟩ := exists_oddGround_imaginary_anchor a hG
  exact oddGroundSpace_eq_of_division_no_quotient_eigenvectors a hG b hb hz
    (oddGroundInvisibleSpace a G) (oddGroundInvisibleSpace_isClosed a G)
    (fun _ hu => hu.1) (oddGroundSpace_le_invisible a G)
    (fun _ hu => groundDivisionCLM_preserves_invisible a hG b hb hz hu)
    (fun μ u hu he => oddGround_of_invisible_division_eigenvector a hG b hb hz
      hu.1 hu.2 μ he)

/-- Vanishing at every nonzero generator zero, together with the necessary
origin derivative coordinate, detects the full ground radical exactly. -/
theorem oddGround_iff_all_zero_coordinates (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    (u : CCMArchimedeanFormDomain a) :
    u ∈ oddArithmeticGroundSpace a ↔
      ccmArchimedeanFormReflection a u = -u ∧
      (∀ z : ℂ, z ≠ 0 → unitaryLaplace (timeRep a G) z = 0 →
        unitaryLaplace (timeRep a u) z = 0) ∧
      (deriv (unitaryLaplace (timeRep a G)) 0 = 0 →
        deriv (unitaryLaplace (timeRep a u)) 0 = 0) := by
  constructor
  · intro hu
    refine ⟨hu.2,?_,?_⟩
    · obtain ⟨P,hP⟩ := hG.2.2 u hu
      intro z _hz0 hz
      rw [hP,hz,mul_zero]
    · intro hd
      obtain ⟨e,ρ,_heo,_hed,hρ,hrep,_hother⟩ := exists_oddGround_origin_representative a hG hd
      have hh := hrep u hu.2
      rw [arithmeticShiftedForm_ground_right a hu] at hh
      exact (mul_eq_zero.mp hh.symm).resolve_left (ofReal_ne_zero.mpr hρ.ne')
  · rintro ⟨hu,hzeros,horigin⟩
    rw [← oddGroundInvisibleSpace_eq_ground a hG]
    refine ⟨hu,?_⟩
    rintro v ⟨c,hc,hv,hfac⟩
    have hdiv : ∃ k : CCMArchimedeanFormDomain a, ∀ w : ℂ,
        unitaryLaplace (timeRep a u) w = (w^2-c)*unitaryLaplace (timeRep a k) w := by
      by_cases hc0 : c = 0
      · have hfun : unitaryLaplace (timeRep a G) =
            fun w : ℂ => w^2*unitaryLaplace (timeRep a v) w := by
          funext w
          simpa only [hc0,sub_zero] using hfac w
        have hder := (((hasDerivAt_id (0 : ℂ)).pow 2).mul (transform_hasDerivAt a v 0)).deriv
        have hdG : deriv (unitaryLaplace (timeRep a G)) 0 = 0 := by
          rw [hfun]
          simpa using hder
        obtain ⟨k,_hk,hkfac⟩ := exists_odd_origin_paired_div a hu (horigin hdG)
        exact ⟨k,fun w => by simpa only [hc0,sub_zero] using hkfac w⟩
      · obtain ⟨z,hzsq⟩ := IsAlgClosed.exists_pow_nat_eq c (n := 2) (by norm_num)
        have hz0 : z ≠ 0 := by
          intro hh
          simp only [hh,zero_pow two_ne_zero] at hzsq
          exact hc0 hzsq.symm
        have hGz : unitaryLaplace (timeRep a G) z = 0 := by
          rw [hfac,hzsq,sub_self,zero_mul]
        obtain ⟨k,_hk,hkfac⟩ := exists_odd_paired_div a hu hz0 (hzeros z hz0 hGz)
        exact ⟨k,fun w => by simpa only [hzsq] using hkfac w⟩
    obtain ⟨k,hk⟩ := hdiv
    have ht := arithmeticShiftedForm_quadratic_transfer a G u v k hc hfac hk
    rw [arithmeticShiftedForm_ground_left a hG.1] at ht
    exact ht.symm

/-- The actual canonical generator gives a complete zero-coordinate system
modulo the finite ground space, including the sole possible origin defect. -/
theorem exists_complete_oddGround_zero_coordinates (a : SuzukiPositiveAperture) :
    ∃ G : CCMArchimedeanFormDomain a, IsOddArithmeticGroundGenerator a G ∧
      ∀ u : CCMArchimedeanFormDomain a,
        u ∈ oddArithmeticGroundSpace a ↔
          ccmArchimedeanFormReflection a u = -u ∧
          (∀ z : ℂ, z ≠ 0 → unitaryLaplace (timeRep a G) z = 0 →
            unitaryLaplace (timeRep a u) z = 0) ∧
          (deriv (unitaryLaplace (timeRep a G)) 0 = 0 →
            deriv (unitaryLaplace (timeRep a u)) 0 = 0) := by
  obtain ⟨G,hG,_hcross,_hunique⟩ := exists_canonical_oddArithmeticGround_generator a
  exact ⟨G,hG,oddGround_iff_all_zero_coordinates a hG⟩

/-- Unconditional actual-source completeness, with the canonical generator
and all analytic construction data supplied by the existing ground theory. -/
theorem exists_complete_oddGround_divisors (a : SuzukiPositiveAperture) :
    ∃ G : CCMArchimedeanFormDomain a, IsOddArithmeticGroundGenerator a G ∧
      ∀ u : CCMArchimedeanFormDomain a,
        u ∈ oddArithmeticGroundSpace a ↔
          ccmArchimedeanFormReflection a u = -u ∧
          ∀ v : CCMArchimedeanFormDomain a, IsOddGroundDivisor a G v →
            arithmeticShiftedForm a v u = 0 := by
  obtain ⟨G,hG,_hcross,_hunique⟩ := exists_canonical_oddArithmeticGround_generator a
  refine ⟨G,hG,fun u => ?_⟩
  rw [← oddGroundInvisibleSpace_eq_ground a hG]
  rfl

end RHTower.OddSector
