import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheEvaluationGramsHaveTheirEndpointSlope
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelLemma410

/-!
# The Weil kernel vanishes with the aperture

A fixed positive enclosing Weil form controls physical mass. The exact
shrinking-support Fourier estimate then bounds each diagonal kernel by a
constant times the aperture length. The zero extension has no initial atom:
integrating the actual endpoint trace energy from zero recovers every Gram.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry
namespace WeilHilbertBeforeContact

/-- Fourier evaluation gains the exact shrinking-support factor `2a` in
squared physical norm. -/
theorem norm_eval_sq_le_aperture_mass (a : PrecontactAperture) (z : ℂ)
    (u : WeilHilbertBeforeContact a) :
    ‖eval a z u‖^2 ≤
      2*a.1.1*(Real.exp (a.1.1*|z.im|))^2*
        ‖ccmArchimedeanFormToAperture a.1 (toForm a u)‖^2 := by
  let f : SoninL2 := ccmArchimedeanFormToAperture a.1 (toForm a u)
  have hFourier := norm_suzukiCompactL2Fourier_le a.1.2.le f z
  have hmass := integral_norm_suzukiCutoff_sq_le a.1.2.le f
  have hnonneg : 0 ≤ ∫ x : ℝ, ‖(suzukiCutoff a.1.1 f) x‖ :=
    integral_nonneg fun _ => norm_nonneg _
  change ‖fourier a u z‖^2 ≤ _
  rw [fourier_eq_whole]
  change ‖suzukiCompactL2Fourier a.1.1 f z‖^2 ≤
    2*a.1.1*(Real.exp (a.1.1*|z.im|))^2*‖f‖^2
  calc
    _ ≤ ((∫ x : ℝ, ‖(suzukiCutoff a.1.1 f) x‖)*Real.exp (a.1.1*|z.im|))^2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hnonneg (Real.exp_pos _).le)).mpr hFourier
    _ = (∫ x : ℝ, ‖(suzukiCutoff a.1.1 f) x‖)^2*(Real.exp (a.1.1*|z.im|))^2 := mul_pow _ _ _
    _ ≤ (2*a.1.1*‖f‖^2)*(Real.exp (a.1.1*|z.im|))^2 :=
      mul_le_mul_of_nonneg_right hmass (sq_nonneg _)
    _ = _ := by ring

/-- Every smaller diagonal kernel is bounded linearly in aperture by the
ground-energy floor of one fixed enclosing space. -/
theorem groundEnergy_mul_kernel_le_aperture {a c : PrecontactAperture}
    (hac : a.1.1 ≤ c.1.1) (z : ℂ) :
    ccmRestrictedWeilGroundEnergy c.1*‖evalVector a z‖^2 ≤
      2*a.1.1*(Real.exp (c.1.1*|z.im|))^2 := by
  let v := evalVector a z
  let M := ‖ccmArchimedeanFormToAperture a.1 (toForm a v)‖
  let K := ‖v‖^2
  let μ := ccmRestrictedWeilGroundEnergy c.1
  let C := 2*a.1.1*(Real.exp (c.1.1*|z.im|))^2
  have hμ : 0 < μ := precontact_groundEnergy_pos c
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr (evalVector_ne_zero a z)
  have hK : 0 < K := by simpa only [K, pow_two] using mul_pos hvpos hvpos
  have hphysical :
      ccmArchimedeanFormEmbedding c.1 (toForm c (inclusion hac v)) =
        ccmArchimedeanFormEmbedding a.1 (toForm a v) := by
    rw [toForm_inclusion]
    exact ccmArchimedeanFormToAperture_coe_eq_of_val_eq
      (ArithmeticContinuationAndCriticalEnergy.apertureExt_val hac (toForm a v))
  have hmass : μ*M^2 ≤ K := by
    have hf := groundEnergy_mul_mass_le c (inclusion hac v)
    rw [(inclusion hac).norm_map] at hf
    change μ*‖ccmArchimedeanFormEmbedding c.1 (toForm c (inclusion hac v))‖^2 ≤ K at hf
    rw [hphysical] at hf
    exact hf
  have hF := norm_eval_sq_le_aperture_mass a z v
  have heval : ‖eval a z v‖ = K := by
    change ‖eval a z (evalVector a z)‖ = K
    rw [evalVector_self a z, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
  rw [heval] at hF
  have hexp : (Real.exp (a.1.1*|z.im|))^2 ≤ (Real.exp (c.1.1*|z.im|))^2 :=
    (sq_le_sq₀ (Real.exp_pos _).le (Real.exp_pos _).le).mpr
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hac (abs_nonneg _)))
  have hF' : K^2 ≤ C*M^2 := hF.trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp (mul_nonneg (by norm_num) a.1.2.le)) (sq_nonneg M))
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg (by norm_num) a.1.2.le) (sq_nonneg _)
  have hleft := mul_le_mul_of_nonneg_left hF' hμ.le
  have hright := mul_le_mul_of_nonneg_left hmass hC
  have hbound : μ*K^2 ≤ C*K := by nlinarith only [hleft, hright]
  change μ*K ≤ C
  by_contra hnot
  have hp := mul_pos hK (sub_pos.mpr (lt_of_not_ge hnot))
  nlinarith only [hbound, hp]

#print axioms groundEnergy_mul_kernel_le_aperture
end WeilHilbertBeforeContact
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower

namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
open _root_.RHTower CanonicalSystemOfTheWindowTower
open CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact
variable {ι : Type*} [Fintype ι]

/-- The zero extension has its literal zero value at aperture zero. -/
theorem evalGram_zero_aperture (α z : ι → ℂ) : evalGram α z 0 = 0 := by
  have hzero : (0 : ℝ) ∉ precontactSet := fun h => (lt_irrefl 0) h.1
  rw [evalGram, dif_neg hzero]

/-- The fixed-enclosure linear aperture bound holds for every finite Gram. -/
theorem groundEnergy_mul_evalGram_le_aperture (α z : ι → ℂ)
    {a c : PrecontactAperture} (hac : a.1.1 ≤ c.1.1) :
    ccmRestrictedWeilGroundEnergy c.1*evalGram α z a.1.1 ≤
      a.1.1*(2*(∑ i, ‖α i‖^2)*∑ i, (Real.exp (c.1.1*|(z i).im|))^2) := by
  let μ := ccmRestrictedWeilGroundEnergy c.1
  let C := ∑ i, ‖α i‖^2
  let S := ∑ i, (Real.exp (c.1.1*|(z i).im|))^2
  have hμ : 0 ≤ μ := (precontact_groundEnergy_pos c).le
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => sq_nonneg ‖α i‖
  have hs : μ*(∑ i, ‖evalVector a (z i)‖^2) ≤ 2*a.1.1*S := by
    have ht := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      groundEnergy_mul_kernel_le_aperture hac (z i))
    simpa only [← Finset.mul_sum, μ, S] using ht
  have hcs : ‖∑ i, α i • evalVector a (z i)‖^2 ≤ C*(∑ i, ‖evalVector a (z i)‖^2) :=
    HTGeometry.norm_sum_smul_sq_le α (fun i => evalVector a (z i))
  have hcs' := mul_le_mul_of_nonneg_left hcs hμ
  have hs' := mul_le_mul_of_nonneg_left hs hC
  have he : evalGram α z a.1.1 = ‖evalCombination α z a‖^2 := by
    rw [evalGram, dif_pos (show a.1.1 ∈ precontactSet from ⟨a.1.2, a.2⟩)]
    rfl
  rw [he]
  change μ*‖∑ i, α i • evalVector a (z i)‖^2 ≤ a.1.1*(2*C*S)
  nlinarith only [hcs', hs']

/-- Every finite Gram tends continuously to zero from nonnegative apertures. -/
theorem continuousWithinAt_evalGram_zero_aperture (α z : ι → ℂ)
    (c : PrecontactAperture) : ContinuousWithinAt (evalGram α z) (Ici 0) 0 := by
  let μ := ccmRestrictedWeilGroundEnergy c.1
  let C := 2*(∑ i, ‖α i‖^2)*∑ i, (Real.exp (c.1.1*|(z i).im|))^2
  let M := C/μ
  have hμ : 0 < μ := precontact_groundEnergy_pos c
  have ht : Tendsto (fun x : ℝ => x*M) (𝓝[≥] (0 : ℝ)) (𝓝 0) := by
    have hx : Tendsto (fun x : ℝ => x) (𝓝[≥] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [zero_mul] using hx.mul_const M
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [self_mem_nhdsWithin, ht.eventually (Iio_mem_nhds hε),
    (eventually_lt_nhds c.1.2).filter_mono nhdsWithin_le_nhds] with x hx hsmall hxc
  change 0 ≤ x at hx
  by_cases hx0 : x = 0
  · rw [hx0, dist_self]
    exact hε
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hpre : x ∈ precontactSet :=
    ⟨hxp, (EReal.coe_lt_coe_iff.mpr hxc).trans c.2⟩
  have hb : μ*evalGram α z x ≤ x*C := by
    simpa only [μ, C, toPrecontact] using
      groundEnergy_mul_evalGram_le_aperture α z (a := toPrecontact hpre) (c := c) hxc.le
  have hbound : evalGram α z x ≤ x*M := by
    have hb' : evalGram α z x ≤ (x*C)/μ :=
      (le_div_iff₀ hμ).mpr (by nlinarith only [hb])
    have he : (x*C)/μ = x*M := by dsimp only [M]; ring
    exact hb'.trans_eq he
  have hnonneg : 0 ≤ evalGram α z x := by
    rw [evalGram, dif_pos hpre]
    exact sq_nonneg _
  rw [evalGram_zero_aperture, Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact hbound.trans_lt hsmall

#print axioms groundEnergy_mul_evalGram_le_aperture
#print axioms continuousWithinAt_evalGram_zero_aperture

theorem evalGram_nonneg (α z : ι → ℂ) (x : ℝ) : 0 ≤ evalGram α z x := by
  classical
  unfold evalGram
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

/-- Compact precontact absolute continuity gives continuity at every
positive precontact aperture. -/
theorem continuousAt_evalGram (α z : ι → ℂ) {a : ℝ} (ha : a ∈ precontactSet) :
    ContinuousAt (evalGram α z) a := by
  obtain ⟨c, hac, hc⟩ := EReal.exists_between_coe_real ha.2
  have hac' : a < c := EReal.coe_lt_coe_iff.mp hac
  have hlo : a/2 < a := by linarith only [ha.1]
  have hlab : a/2 ≤ c := (hlo.trans hac').le
  have hs : Icc (a/2) c ⊆ precontactSet := by
    intro x hx
    exact ⟨(show 0 < a/2 from by linarith only [ha.1]).trans_le hx.1,
      (EReal.coe_le_coe_iff.mpr hx.2).trans_lt hc⟩
  apply (absolutelyContinuousOnInterval_evalGram α z hlab hs).continuousOn.continuousAt
  rw [uIcc_of_le hlab]
  exact Icc_mem_nhds hlo hac'

/-- The zero extension preserves monotonicity on every interval from zero
to a precontact aperture. -/
theorem monotoneOn_evalGram_from_zero (α z : ι → ℂ) (b : PrecontactAperture) :
    MonotoneOn (evalGram α z) (Icc 0 b.1.1) := by
  intro x hx y hy hxy
  by_cases hx0 : x = 0
  · rw [hx0, evalGram_zero_aperture]
    exact evalGram_nonneg α z y
  have hxp : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  have hprex : x ∈ precontactSet :=
    ⟨hxp, (EReal.coe_le_coe_iff.mpr hx.2).trans_lt b.2⟩
  have hprey : y ∈ precontactSet :=
    ⟨hxp.trans_le hxy, (EReal.coe_le_coe_iff.mpr hy.2).trans_lt b.2⟩
  exact monotoneOn_evalGram α z hprex hprey hxy

/-- The shrinking-support bound supplies the missing endpoint continuity
for the full interval starting at zero. -/
theorem continuousOn_evalGram_from_zero (α z : ι → ℂ) (b : PrecontactAperture) :
    ContinuousOn (evalGram α z) (Icc 0 b.1.1) := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    exact (continuousWithinAt_evalGram_zero_aperture α z b).mono (fun y hy => hy.1)
  have hpre : x ∈ precontactSet :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), (EReal.coe_le_coe_iff.mpr hx.2).trans_lt b.2⟩
  exact (continuousAt_evalGram α z hpre).continuousWithinAt

/-- Almost-everywhere density identification remains valid down to zero. -/
theorem evalDensity_ae_eq_endpointEnergy_from_zero (α z : ι → ℂ) (b : PrecontactAperture) :
    evalDensity α z =ᵐ[volume.restrict (uIoc 0 b.1.1)] evalGramEndpointEnergy α z := by
  have hm := monotoneOn_evalGram_from_zero α z b
  change ∀ᵐ x ∂volume.restrict (uIoc 0 b.1.1),
    deriv (evalGram α z) x = evalGramEndpointEnergy α z x
  rw [uIoc_of_le b.1.2.le, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hm.ae_differentiableWithinAt_of_mem, volume.ae_ne b.1.1] with x hx hxb hxI
  have hi : x ∈ Ioo 0 b.1.1 := ⟨hxI.1, lt_of_le_of_ne hxI.2 hxb⟩
  have hf := (hx ⟨hi.1.le, hi.2.le⟩).differentiableAt (Icc_mem_nhds hi.1 hi.2)
  have hpre : x ∈ precontactSet :=
    ⟨hi.1, (EReal.coe_lt_coe_iff.mpr hi.2).trans b.2⟩
  exact (hf.derivWithin (uniqueDiffWithinAt_Ioi x)).symm.trans
    ((hasDerivWithinAt_evalGram_right α z hpre).derivWithin (uniqueDiffWithinAt_Ioi x))

/-- The full Gram is the integral of its actual two-trace energy from
aperture zero, with no initial atom. -/
theorem integral_evalGramEndpointEnergy_from_zero (α z : ι → ℂ) (b : PrecontactAperture) :
    IntervalIntegrable (evalGramEndpointEnergy α z) volume 0 b.1.1 ∧
      (∫ x in (0 : ℝ)..b.1.1, evalGramEndpointEnergy α z x) = evalGram α z b.1.1 := by
  have hm : MonotoneOn (evalGram α z) (uIcc 0 b.1.1) := by
    simpa only [uIcc_of_le b.1.2.le] using monotoneOn_evalGram_from_zero α z b
  have he := evalDensity_ae_eq_endpointEnergy_from_zero α z b
  change deriv (evalGram α z) =ᵐ[volume.restrict (uIoc 0 b.1.1)] evalGramEndpointEnergy α z at he
  have hi := hm.intervalIntegrable_deriv.congr_ae he
  refine ⟨hi, ?_⟩
  have hvalue := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le b.1.2.le
    (continuousOn_evalGram_from_zero α z b)
    (fun x (hx : x ∈ Ioo 0 b.1.1) => hasDerivWithinAt_evalGram_right α z
      ⟨hx.1, (EReal.coe_lt_coe_iff.mpr hx.2).trans b.2⟩) hi
  simpa only [evalGram_zero_aperture, sub_zero] using hvalue

/-- Every finite Gram is absolutely continuous on its entire interval from
zero to any strictly precontact aperture. -/
theorem absolutelyContinuousOnInterval_evalGram_from_zero (α z : ι → ℂ)
    (b : PrecontactAperture) : AbsolutelyContinuousOnInterval (evalGram α z) 0 b.1.1 := by
  have hi := (integral_evalGramEndpointEnergy_from_zero α z b).1
  have hp := hi.absolutelyContinuousOnInterval_intervalIntegral
    (show (0 : ℝ) ∈ uIcc 0 b.1.1 from left_mem_uIcc)
  apply GaloisForLFunctions.RHTower.absolutelyContinuousOnInterval_congr_on ?_ hp
  intro x hx
  rw [uIcc_of_le b.1.2.le] at hx
  by_cases hx0 : x = 0
  · subst x
    change evalGram α z 0 = ∫ v in (0 : ℝ)..0, evalGramEndpointEnergy α z v
    rw [evalGram_zero_aperture, intervalIntegral.integral_same]
  have hpre : x ∈ precontactSet :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), (EReal.coe_le_coe_iff.mpr hx.2).trans_lt b.2⟩
  simpa only [toPrecontact] using
    (integral_evalGramEndpointEnergy_from_zero α z (toPrecontact hpre)).2.symm

#print axioms integral_evalGramEndpointEnergy_from_zero
#print axioms absolutelyContinuousOnInterval_evalGram_from_zero
end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
