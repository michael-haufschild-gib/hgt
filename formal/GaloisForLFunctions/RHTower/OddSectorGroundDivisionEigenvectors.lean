import GaloisForLFunctions.RHTower.OddSectorGroundDivisionCalculus

/-!
# Algebraic detection of division eigenvectors

Every non-ground eigenvector modulo the ground radical is detected by a
single paired ground divisor. The possible node at zero is tested by the
first derivative; this is essential when the canonical generator has a
triple zero at the origin.
-/

open Complex Set
open scoped InnerProduct ComplexConjugate
noncomputable section
namespace RHTower.OddSector
open GaloisForLFunctions.HTGeometry.FourierLaplaceDivision
open CCMRealRootedGround CCMGroundStructure CCMGroundQuadrature

/-- An actual odd form vector obtained by one real squared-frequency
division of the canonical ground generator. -/
def IsOddGroundDivisor (a : SuzukiPositiveAperture)
    (G v : CCMArchimedeanFormDomain a) : Prop :=
  ∃ c : ℂ, conj c = c ∧ ccmArchimedeanFormReflection a v = -v ∧
    ∀ w : ℂ, unitaryLaplace (timeRep a G) w =
      (w^2-c)*unitaryLaplace (timeRep a v) w

private theorem oddPart_of_odd (a : SuzukiPositiveAperture)
    {u : CCMArchimedeanFormDomain a} (hu : ccmArchimedeanFormReflection a u = -u) :
    ccmRestrictedWeilOddPart a u = u := by
  rw [ccmRestrictedWeilOddPart,hu,sub_neg_eq_add,← two_smul ℂ u,smul_smul,
    inv_mul_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0),one_smul]

/-- Every paired ground divisor is already an eigenvector of the normalized
division operator on the full form domain. -/
theorem groundDivisionCLM_groundDivisor (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    (b : ℝ) (hb : 0 < b)
    (hz : unitaryLaplace (timeRep a G) (I*(b : ℂ)) ≠ 0)
    {v : CCMArchimedeanFormDomain a} (hv : IsOddGroundDivisor a G v) :
    groundDivisionCLM a hG b hb hz v =
      (-(unitaryLaplace (timeRep a v) (I*(b : ℂ)) /
        unitaryLaplace (timeRep a G) (I*(b : ℂ)))) • v := by
  obtain ⟨c,_hc,hvo,hfac⟩ := hv
  let α := unitaryLaplace (timeRep a v) (I*(b : ℂ)) /
    unitaryLaplace (timeRep a G) (I*(b : ℂ))
  have ha : α*((I*(b : ℂ))^2-c) = 1 := by
    dsimp only [α]
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff hz).mpr
    rw [one_mul,mul_comm]
    exact (hfac (I*(b : ℂ))).symm
  rw [groundDivisionCLM_apply]
  apply eq_of_sq_mul_transform_eq a _ _ (I*(b : ℂ))
  intro w
  rw [← groundDivision_factor a hG (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hb.ne')) hz v]
  rw [groundDivisionInput,oddPart_of_odd a hvo]
  change (evalAt a w) (v-α • G) = _
  rw [map_sub,map_smul]
  simp only [evalAt_apply,unitaryLaplace_timeRep_smul]
  rw [hfac]
  linear_combination -(unitaryLaplace (timeRep a v) w)*ha

theorem oddArithmeticGround_quadratic_product (a : SuzukiPositiveAperture)
    {v u : CCMArchimedeanFormDomain a} (hv : v ∈ oddArithmeticGroundSpace a)
    (hu : ccmArchimedeanFormReflection a u = -u) (c : ℂ)
    (hfac : ∀ w : ℂ, unitaryLaplace (timeRep a u) w =
      (w^2-c)*unitaryLaplace (timeRep a v) w) :
    u ∈ oddArithmeticGroundSpace a := by
  have hmul : u+c • v ∈ oddArithmeticGroundSpace a :=
    oddArithmeticGround_mul_sq a hv (by rw [map_add,map_smul,hu,hv.2,smul_neg,neg_add])
      (fun w => by rw [unitaryLaplace_timeRep_add_smul,hfac]; ring)
  have hh := (oddArithmeticGroundSpace a).sub_mem hmul
    ((oddArithmeticGroundSpace a).smul_mem c hv)
  simpa only [add_sub_cancel_right] using hh

theorem groundDivisionCLM_mod_ground_kernel (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    (b : ℝ) (hb : 0 < b)
    (hz : unitaryLaplace (timeRep a G) (I*(b : ℂ)) ≠ 0)
    {u : CCMArchimedeanFormDomain a}
    (hu : ccmArchimedeanFormReflection a u = -u)
    (hd : groundDivisionCLM a hG b hb hz u ∈ oddArithmeticGroundSpace a) :
    u ∈ oddArithmeticGroundSpace a := by
  have hi : groundDivisionInput a G (I*(b : ℂ)) u ∈ oddArithmeticGroundSpace a := by
    apply oddArithmeticGround_quadratic_product a hd
    · unfold groundDivisionInput
      rw [map_sub,map_smul,ccmArchimedeanFormReflection_oddPart,hG.1.2,smul_neg,neg_sub]
      abel
    · intro w
      rw [groundDivisionCLM_apply]
      exact groundDivision_factor a hG _ hz u w
  have hh := (oddArithmeticGroundSpace a).add_mem hi
    ((oddArithmeticGroundSpace a).smul_mem
      (unitaryLaplace (timeRep a (ccmRestrictedWeilOddPart a u)) (I*(b : ℂ)) /
        unitaryLaplace (timeRep a G) (I*(b : ℂ))) hG.1)
  simpa only [groundDivisionInput,sub_add_cancel,oddPart_of_odd a hu] using hh

/-- A non-ground quotient eigenvalue is real, as forced by the actual form. -/
theorem groundDivision_mod_ground_eigenvalue_real (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    (b : ℝ) (hb : 0 < b)
    (hz : unitaryLaplace (timeRep a G) (I*(b : ℂ)) ≠ 0)
    {u : CCMArchimedeanFormDomain a} (hu : ccmArchimedeanFormReflection a u = -u)
    (hn : u ∉ oddArithmeticGroundSpace a) (μ : ℂ)
    (he : groundDivisionCLM a hG b hb hz u-μ • u ∈ oddArithmeticGroundSpace a) :
    conj μ = μ := by
  have hq : arithmeticShiftedForm a u u ≠ 0 := by
    intro h
    exact hn ((mem_oddArithmeticGroundSpace_iff a u).mpr ⟨hu,by rw [h]; rfl⟩)
  have hl := arithmeticShiftedForm_ground_left a he u
  have hr := arithmeticShiftedForm_ground_right a he u
  rw [arithmeticShiftedForm_sub_left,arithmeticShiftedForm_smul_left] at hl
  rw [arithmeticShiftedForm_sub_right,arithmeticShiftedForm_smul_right] at hr
  have hs := groundDivisionCLM_symmetric_form a hG b hb hz hu hu
  apply mul_right_cancel₀ hq
  linear_combination -hl + hr - hs

private theorem groundDivision_eigen_pair (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    (b : ℝ) (hb : 0 < b)
    (hz : unitaryLaplace (timeRep a G) (I*(b : ℂ)) ≠ 0)
    {u : CCMArchimedeanFormDomain a} (μ : ℂ)
    (he : groundDivisionCLM a hG b hb hz u-μ • u ∈ oddArithmeticGroundSpace a)
    (v : CCMArchimedeanFormDomain a) :
    arithmeticShiftedForm a (groundDivisionCLM a hG b hb hz u) v =
      conj μ*arithmeticShiftedForm a u v := by
  have hh := arithmeticShiftedForm_ground_left a he v
  rw [arithmeticShiftedForm_sub_left,arithmeticShiftedForm_smul_left] at hh
  exact sub_eq_zero.mp hh

/-- A quotient eigenvector annihilates every source divisible at its spectral
node, before any use of the generator's zero set. -/
theorem groundDivision_eigen_annihilates_divisible (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    (b : ℝ) (hb : 0 < b)
    (hz : unitaryLaplace (timeRep a G) (I*(b : ℂ)) ≠ 0)
    {u : CCMArchimedeanFormDomain a} (hu : ccmArchimedeanFormReflection a u = -u)
    (μ : ℂ) (hμ : μ ≠ 0) (hreal : conj μ = μ)
    (he : groundDivisionCLM a hG b hb hz u-μ • u ∈ oddArithmeticGroundSpace a)
    (v k : CCMArchimedeanFormDomain a)
    (hfac : ∀ w : ℂ, unitaryLaplace (timeRep a v) w =
      (w^2-((I*(b : ℂ))^2+μ⁻¹))*unitaryLaplace (timeRep a k) w) :
    arithmeticShiftedForm a u v = 0 := by
  let t := v+μ⁻¹ • k
  have ht (w : ℂ) : unitaryLaplace (timeRep a t) w =
      (w^2-(I*(b : ℂ))^2)*unitaryLaplace (timeRep a k) w := by
    rw [unitaryLaplace_timeRep_add_smul,hfac]
    ring
  have hc : conj ((I*(b : ℂ))^2) = (I*(b : ℂ))^2 := by
    simp only [map_pow,map_mul,Complex.conj_I,Complex.conj_ofReal,neg_mul,neg_sq]
  have hd (w : ℂ) : unitaryLaplace (timeRep a (groundDivisionInput a G (I*(b : ℂ)) u)) w =
      (w^2-(I*(b : ℂ))^2)*unitaryLaplace (timeRep a (groundDivisionCLM a hG b hb hz u)) w := by
    rw [groundDivisionCLM_apply]
    exact groundDivision_factor a hG _ hz u w
  have h := arithmeticShiftedForm_quadratic_transfer a
    (groundDivisionInput a G (I*(b : ℂ)) u) t
    (groundDivisionCLM a hG b hb hz u) k hc hd ht
  rw [groundDivisionInput,oddPart_of_odd a hu,arithmeticShiftedForm_sub_left,
    arithmeticShiftedForm_smul_left,arithmeticShiftedForm_ground_left a hG.1,
    mul_zero,sub_zero] at h
  dsimp only [t] at h
  rw [arithmeticShiftedForm_add_right,arithmeticShiftedForm_smul_right,
    groundDivision_eigen_pair a hG b hb hz μ he v,
    groundDivision_eigen_pair a hG b hb hz μ he k,hreal] at h
  have hcanc : μ⁻¹*(μ*arithmeticShiftedForm a u k) = arithmeticShiftedForm a u k := by
    rw [← mul_assoc,inv_mul_cancel₀ hμ,one_mul]
  rw [hcanc] at h
  have hzq : μ*arithmeticShiftedForm a u v = 0 := by linear_combination -h
  exact (mul_eq_zero.mp hzq).resolve_left hμ

/-- Every quotient eigenvector invisible to all actual ground divisors is
ground. No spectral sign or zero-set completeness is assumed. -/
theorem oddGround_of_invisible_division_eigenvector (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    (b : ℝ) (hb : 0 < b)
    (hz : unitaryLaplace (timeRep a G) (I*(b : ℂ)) ≠ 0)
    {u : CCMArchimedeanFormDomain a} (hu : ccmArchimedeanFormReflection a u = -u)
    (hinvis : ∀ v : CCMArchimedeanFormDomain a, IsOddGroundDivisor a G v →
      arithmeticShiftedForm a v u = 0)
    (μ : ℂ)
    (he : groundDivisionCLM a hG b hb hz u-μ • u ∈ oddArithmeticGroundSpace a) :
    u ∈ oddArithmeticGroundSpace a := by
  by_cases hμ : μ = 0
  · apply groundDivisionCLM_mod_ground_kernel a hG b hb hz hu
    simpa only [hμ,zero_smul,sub_zero] using he
  by_contra hn
  have hreal := groundDivision_mod_ground_eigenvalue_real a hG b hb hz hu hn μ he
  let c : ℂ := (I*(b : ℂ))^2+μ⁻¹
  have hc : conj c = c := by
    dsimp only [c]
    rw [map_add,map_inv₀,hreal]
    simp only [map_pow,map_mul,Complex.conj_I,Complex.conj_ofReal,neg_mul,neg_sq]
  have hpair (v k : CCMArchimedeanFormDomain a)
      (hfac : ∀ w : ℂ, unitaryLaplace (timeRep a v) w =
        (w^2-c)*unitaryLaplace (timeRep a k) w) : arithmeticShiftedForm a u v = 0 :=
    groundDivision_eigen_annihilates_divisible a hG b hb hz hu μ hμ hreal he v k hfac
  have hzero : arithmeticShiftedForm a u u = 0 := by
    by_cases hc0 : c = 0
    · have hvan (v : CCMArchimedeanFormDomain a)
          (hv : ccmArchimedeanFormReflection a v = -v)
          (hd : deriv (unitaryLaplace (timeRep a v)) 0 = 0) :
          arithmeticShiftedForm a u v = 0 := by
        obtain ⟨k,_hk,hfac⟩ := exists_odd_origin_paired_div a hv hd
        exact hpair v k (fun w => by simpa only [hc0,sub_zero] using hfac w)
      have href : ∃ v : CCMArchimedeanFormDomain a,
          ccmArchimedeanFormReflection a v = -v ∧
          deriv (unitaryLaplace (timeRep a v)) 0 ≠ 0 ∧ arithmeticShiftedForm a u v = 0 := by
        by_cases hdG : deriv (unitaryLaplace (timeRep a G)) 0 = 0
        · obtain ⟨v,hv,hfac⟩ := exists_odd_origin_paired_div a hG.1.2 hdG
          refine ⟨v,hv,oddGroundGenerator_origin_quotient_deriv_ne_zero a hG hv hfac,?_⟩
          rw [arithmeticShiftedForm_conj,
            hinvis v ⟨0,map_zero conj,hv,fun w => by simpa only [sub_zero] using hfac w⟩,
            map_zero]
        · exact ⟨G,hG.1.2,hdG,arithmeticShiftedForm_ground_right a hG.1 u⟩
      obtain ⟨v,hv,hvd,hq⟩ := href
      let α : ℂ := deriv (unitaryLaplace (timeRep a u)) 0 /
        deriv (unitaryLaplace (timeRep a v)) 0
      have hr := hvan (u-α • v)
        (by rw [map_sub,map_smul,hu,hv,smul_neg,neg_sub]; abel)
        (by rw [transform_deriv_sub,transform_deriv_smul];
            exact sub_eq_zero.mpr (div_mul_cancel₀ _ hvd).symm)
      rwa [arithmeticShiftedForm_sub_right,arithmeticShiftedForm_smul_right,
        hq,mul_zero,sub_zero] at hr
    · obtain ⟨z,hzsq⟩ := IsAlgClosed.exists_pow_nat_eq c (n := 2) (by norm_num)
      have hz0 : z ≠ 0 := by intro h; simp only [h,zero_pow two_ne_zero] at hzsq; exact hc0 hzsq.symm
      have hzreal : conj (z^2) = z^2 := by rw [hzsq,hc]
      have hvan (v : CCMArchimedeanFormDomain a)
          (hv : ccmArchimedeanFormReflection a v = -v)
          (hvz : unitaryLaplace (timeRep a v) z = 0) : arithmeticShiftedForm a u v = 0 := by
        obtain ⟨k,_hk,hfac⟩ := exists_odd_paired_div a hv hz0 hvz
        exact hpair v k (fun w => by simpa only [hzsq] using hfac w)
      have href : ∃ v : CCMArchimedeanFormDomain a,
          ccmArchimedeanFormReflection a v = -v ∧
          unitaryLaplace (timeRep a v) z ≠ 0 ∧ arithmeticShiftedForm a u v = 0 := by
        by_cases hGz : unitaryLaplace (timeRep a G) z = 0
        · obtain ⟨v,hv,hfac⟩ := exists_odd_paired_div a hG.1.2 hz0 hGz
          refine ⟨v,hv,oddGroundGenerator_quotient_eval_ne_zero a hG hz0 hzreal hv hfac,?_⟩
          rw [arithmeticShiftedForm_conj,hinvis v ⟨z^2,hzreal,hv,hfac⟩,map_zero]
        · exact ⟨G,hG.1.2,hGz,arithmeticShiftedForm_ground_right a hG.1 u⟩
      obtain ⟨v,hv,hvz,hq⟩ := href
      let α : ℂ := unitaryLaplace (timeRep a u) z / unitaryLaplace (timeRep a v) z
      have hr := hvan (u-α • v)
        (by rw [map_sub,map_smul,hu,hv,smul_neg,neg_sub]; abel)
        (by
          change (evalAt a z) (u-α • v) = 0
          rw [map_sub,map_smul]
          exact sub_eq_zero.mpr (div_mul_cancel₀ _ hvz).symm)
      rwa [arithmeticShiftedForm_sub_right,arithmeticShiftedForm_smul_right,
        hq,mul_zero,sub_zero] at hr
  exact hn ((mem_oddArithmeticGroundSpace_iff a u).mpr ⟨hu,by rw [hzero]; rfl⟩)

end RHTower.OddSector
