import GaloisForLFunctions.RHTower.CCMLocalTranslationRigidity
import GaloisForLFunctions.RHTower.CCMPrimePoleSchurConstrainedEscape
import GaloisForLFunctions.RHTower.GelfondSchneider

/-!
# The exact measurable kernel of the actual prime-edge form

Once the aperture contains a log-two cell and its log-three translate, zero
edge energy forces the full complex source to be a multiple of the Schur pole
profile. Both exact pole constraints remove that kernel. This is an exact
kernel theorem, not a uniform physical spectral gap: recurrent modulations
already disprove that stronger assertion.
-/

open Complex MeasureTheory Set Filter
open scoped InnerProduct
noncomputable section
namespace RHTower

private theorem edge_zero_local (a : SuzukiPositiveAperture)
    (h : ℝ) (f : suzukiApertureHilbert a)
    (he : ccmPrimePoleEdgeEnergy a h f.1 = 0) :
    CCMLocalTranslationInvariant (fun x => f.1 x / (primePoleProfile x : ℂ)) (-a.1) a.1 h := by
  have hz := (integral_eq_zero_iff_of_nonneg
    (ccmPrimePoleEdgeDensity_nonneg a h f.1)
    (integrable_ccmPrimePoleEdgeDensity a h f)).mp he
  filter_upwards [hz] with x hx hxi hxh
  have hmem : x ∈ centralInterval a.1 ∩ (fun y : ℝ => y+h) ⁻¹' centralInterval a.1 :=
    ⟨hxi,hxh⟩
  rw [ccmPrimePoleEdgeDensity, indicator_of_mem hmem] at hx
  have hden := (mul_pos (primePoleProfile_pos x) (primePoleProfile_pos (x+h))).ne'
  have hn := norm_eq_zero.mp (sq_eq_zero_iff.mp ((div_eq_zero_iff.mp hx).resolve_right hden))
  apply (div_eq_div_iff
    (Complex.ofReal_ne_zero.mpr (primePoleProfile_pos (x+h)).ne')
    (Complex.ofReal_ne_zero.mpr (primePoleProfile_pos x).ne')).mpr
  simpa only [mul_comm] using sub_eq_zero.mp hn

private theorem prime_edge_zero (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (he : ccmPrimePoleSchurEnergy a f.1 = 0)
    (n : ℕ) (hn : n.Prime) (hcut : n ≤ ⌊Real.exp (2*a.1)⌋₊) :
    ccmPrimePoleEdgeEnergy a (Real.log n) f.1 = 0 := by
  have hnon (m : ℕ) (_ : m ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊) :
      0 ≤ (ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
        ccmPrimePoleEdgeEnergy a (Real.log m) f.1 :=
    mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
      (ccmPrimePoleEdgeEnergy_nonneg a _ _)
  have ht := (Finset.sum_eq_zero_iff_of_nonneg hnon).mp he n
    (Finset.mem_Icc.mpr ⟨hn.two_le,hcut⟩)
  have hw : 0 < ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime hn]
    exact div_pos (Real.log_pos (by exact_mod_cast hn.one_lt))
      (Real.sqrt_pos.mpr (by exact_mod_cast hn.pos))
  exact (mul_eq_zero.mp ht).resolve_left hw.ne'

/-- Every zero-energy actual aperture source is a scalar multiple of the
positive Schur pole profile; no continuity of the source is required. -/
theorem exists_smul_ccmSchurPole_of_schurEnergy_zero
    (a : SuzukiPositiveAperture) (ha : Real.log 2 + Real.log 3 ≤ 2*a.1)
    (f : suzukiApertureHilbert a) (he : ccmPrimePoleSchurEnergy a f.1 = 0) :
    ∃ c : ℂ, f = c • ccmSchurPoleVector a := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hcut : 3 ≤ ⌊Real.exp (2*a.1)⌋₊ := Nat.le_floor
    ((Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 3)).mp (by linarith))
  let F : ℝ → ℂ := fun x => f.1 x / (primePoleProfile x : ℂ)
  have hF : Measurable F := (Lp.stronglyMeasurable f.1).measurable.div
    (Complex.measurable_ofReal.comp measurable_primePoleProfile)
  have hp := edge_zero_local a (Real.log 2) f
    (prime_edge_zero a f he 2 Nat.prime_two (by omega))
  have hq := edge_zero_local a (Real.log 3) f
    (prime_edge_zero a f he 3 Nat.prime_three hcut)
  have hirr : Irrational (Real.log 3 / Real.log 2) := by
    simpa only [Nat.cast_ofNat] using
      GaloisForLFunctions.RHTower.irrational_log_ratio Nat.prime_two Nat.prime_three (by omega)
  obtain ⟨c,hc⟩ := ae_eq_const_of_two_ccmLocalTranslations F hF (-a.1) a.1
    (Real.log 2) (Real.log 3) hlog2 hlog3.le (by linarith) hirr hp hq
  refine ⟨c, Subtype.ext ?_⟩
  apply Lp.ext
  have hf := indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1) f.1
  rw [indicatorCutoff_suzukiApertureHilbert] at hf
  filter_upwards [hc,hf,ccmSchurPoleVector_coeFn a,
    Lp.coeFn_smul c (ccmSchurPoleVector a).1] with x hc hf hw hs
  change f.1 x = (c • (ccmSchurPoleVector a).1) x
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hw]
  by_cases hx : x ∈ centralInterval a.1
  · rw [indicator_of_mem hx]
    exact (div_eq_iff (Complex.ofReal_ne_zero.mpr (primePoleProfile_pos x).ne')).mp (hc hx)
  · rw [hf, indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

/-- Exact physical pole orthogonality removes the complete Schur kernel. -/
theorem eq_zero_of_ccmSchurEnergy_zero_of_polar
    (a : SuzukiPositiveAperture) (ha : Real.log 2 + Real.log 3 ≤ 2*a.1)
    (f : suzukiApertureHilbert a)
    (hp : inner ℂ (ccmPolarApertureVector a (1/2)) f = 0)
    (hm : inner ℂ (ccmPolarApertureVector a (-1/2)) f = 0)
    (he : ccmPrimePoleSchurEnergy a f.1 = 0) : f = 0 := by
  obtain ⟨c,hc⟩ := exists_smul_ccmSchurPole_of_schurEnergy_zero a ha f he
  have hw : inner ℂ (ccmSchurPoleVector a) f = 0 := by
    rw [ccmSchurPoleVector, inner_add_left, hp, hm, add_zero]
  rw [hc, inner_smul_right (ccmSchurPoleVector a) (ccmSchurPoleVector a) c] at hw
  have hself : inner ℂ (ccmSchurPoleVector a) (ccmSchurPoleVector a) ≠ 0 :=
    fun h => ccmSchurPoleVector_ne_zero a (inner_self_eq_zero.mp h)
  have hc0 := (mul_eq_zero.mp hw).resolve_right hself
  rw [hc,hc0,zero_smul]

/-- On the genuine exactly constrained form domain, the edge kernel is zero.
This is compatible with the absence of any uniform physical-norm edge gap. -/
theorem ccmPolarConstrained_schurEnergy_eq_zero_iff
    (a : SuzukiPositiveAperture) (ha : Real.log 2 + Real.log 3 ≤ 2*a.1)
    (u : ccmPolarConstraintSubmodule a) :
    ccmPrimePoleSchurEnergy a (ccmArchimedeanFormToAperture a u.1).1 = 0 ↔ u = 0 := by
  constructor
  · intro he
    have hu : IsPolarConstrained a u.1 := u.2
    have hzero := eq_zero_of_ccmSchurEnergy_zero_of_polar a ha
      (ccmArchimedeanFormToAperture a u.1) hu.1 hu.2 he
    apply Subtype.ext
    apply ccmArchimedeanFormToAperture_injective a
    simpa only [ZeroMemClass.coe_zero, map_zero] using hzero
  · rintro rfl
    simp only [ZeroMemClass.coe_zero, map_zero]
    apply le_antisymm _ (ccmPrimePoleSchurEnergy_nonneg a _)
    have h := ccmPrimePoleSchurEnergy_le_two_envelope a (0 : suzukiApertureHilbert a)
    simpa only [ZeroMemClass.coe_zero, norm_zero, zero_pow two_ne_zero, mul_zero] using h

end RHTower
