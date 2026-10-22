import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilEvenSectorCrossZeros
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilFormTranslation
import GaloisForLFunctions.HTGeometry.L2CosineTranslationIndependence

/-!
# Strict aperture decrease inside the even polar sector

The heat-Hankel windows only see even sources. Ordinary translation leaves that
sector, so strict decrease of the full polar ground does not settle its aperture
geometry. Opposite translations repair this obstruction exactly.

If two even ground energies agreed, an extended minimizer would annihilate the
shifted form on the larger even sector. The cosine multiplier identity then puts
every sufficiently small symmetric translate in the same ground space. Arbitrarily
many such translates are independent, contradicting its finite multiplicity.

The argument retains the full prime--Gamma source and requires neither a parity
choice for the full ground nor quantitative coercivity or minimizer smoothness.
-/

open Complex MeasureTheory Set Filter
open scoped InnerProduct BigOperators
noncomputable section
namespace RHTower.CCMEvenSector
open RHTower.CCMRealRootedGround
open GaloisForLFunctions.HTGeometry

theorem isEven_of_val_eq {a b : SuzukiPositiveAperture}
    {u : CCMArchimedeanFormDomain a} {v : CCMArchimedeanFormDomain b}
    (hv : v.1 = u.1) (hu : IsEven a u) : IsEven b v := by
  apply Subtype.ext
  change ccmArchimedeanFourierReflection v.1 = v.1
  rw [hv]
  exact congrArg Subtype.val hu

theorem evenGroundEnergy_antitone : Antitone evenGroundEnergy := by
  intro a b hab
  obtain ⟨u, hp, he, hn, hQ⟩ := exists_evenGround a
  obtain ⟨v, hv⟩ := exists_ccmArchimedeanFormDomain_extension hab u
  have hpv := (isPolarConstrained_iff_of_val_eq hab hv).mpr hp
  have hev := isEven_of_val_eq hv he
  have hf := evenGroundEnergy_mul_le b v hpv hev
  rw [ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hab hv,
    norm_ccmArchimedeanFormToAperture_eq_of_val_eq hv, hn, one_pow, mul_one, hQ] at hf
  exact hf

private theorem reflection_phaseMul (h : ℝ) (u : CCMArchimedeanFourierL2) :
    ccmArchimedeanFourierReflection (ccmArchimedeanPhaseMul h u) =
      ccmArchimedeanPhaseMul (-h) (ccmArchimedeanFourierReflection u) := by
  apply Lp.ext
  have hp := (ccmArchimedeanPhaseMul_coeFn h u).comp_tendsto
    ccmArchimedeanFormMeasure_measurePreserving_neg.quasiMeasurePreserving.tendsto_ae
  filter_upwards [ccmArchimedeanFourierReflection_ae (ccmArchimedeanPhaseMul h u),
    ccmArchimedeanPhaseMul_coeFn (-h) (ccmArchimedeanFourierReflection u),
    ccmArchimedeanFourierReflection_ae u, hp] with x hr hph hu hp
  dsimp only [Function.comp_apply] at hp
  rw [hr, hph, hu, hp]
  congr 1
  simp only [MellinL2.fourierPhase, mul_neg, neg_mul]

/-- The sum of opposite translates preserves reflection parity and both pole zeros. -/
def cosineTranslate {a b : SuzukiPositiveAperture} (h : ℝ)
    (hab : a.1 + |h| ≤ b.1) : CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain b :=
  ccmArchimedeanFormTranslate h hab +
    ccmArchimedeanFormTranslate (-h) (by simpa only [abs_neg] using hab)

theorem cosineTranslate_isEven {a b : SuzukiPositiveAperture} (h : ℝ)
    (hab : a.1 + |h| ≤ b.1) {u : CCMArchimedeanFormDomain a} (hu : IsEven a u) :
    IsEven b (cosineTranslate h hab u) := by
  apply Subtype.ext
  change ccmArchimedeanFourierReflection
    (ccmArchimedeanPhaseMul h u.1 + ccmArchimedeanPhaseMul (-h) u.1) = _
  rw [map_add, reflection_phaseMul, reflection_phaseMul, neg_neg]
  have he : ccmArchimedeanFourierReflection u.1 = u.1 := congrArg Subtype.val hu
  rw [he]
  exact add_comm _ _

theorem cosineTranslate_isPolar {a b : SuzukiPositiveAperture} (h : ℝ)
    (hab : a.1 + |h| ≤ b.1) {u : CCMArchimedeanFormDomain a} (hu : IsPolarConstrained a u) :
    IsPolarConstrained b (cosineTranslate h hab u) :=
  (ccmPolarConstraintSubmodule b).add_mem (hu.translate _ _) (hu.translate _ _)

private theorem phase_sum (h x : ℝ) :
    MellinL2.fourierPhase h x + MellinL2.fourierPhase (-h) x =
      (2 * Real.cos (2 * Real.pi * (h * x)) : ℝ) := by
  simp only [MellinL2.fourierPhase, Real.fourierChar_apply]
  rw [show 2 * Real.pi * (-h * x) = -(2 * Real.pi * (h * x)) by ring]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.exp_ofReal_mul_I_re, Complex.ofReal_re, Real.cos_neg]
    ring
  · simp only [Complex.add_im, Complex.exp_ofReal_mul_I_im, Complex.ofReal_im, Real.sin_neg]
    ring

theorem cosineTranslate_coeFn {a b : SuzukiPositiveAperture} (h : ℝ)
    (hab : a.1 + |h| ≤ b.1) (u : CCMArchimedeanFormDomain a) :
    ((cosineTranslate h hab u).1 : ℝ → ℂ) =ᵐ[volume]
      fun x => (2 * Real.cos (2 * Real.pi * (h * x)) : ℂ) * (u.1 : ℝ → ℂ) x := by
  have hp := (ccmArchimedeanPhaseMul_coeFn h u.1).filter_mono
    (ae_mono volume_le_ccmArchimedeanFormMeasure)
  have hm := (ccmArchimedeanPhaseMul_coeFn (-h) u.1).filter_mono
    (ae_mono volume_le_ccmArchimedeanFormMeasure)
  have ha := (Lp.coeFn_add (ccmArchimedeanPhaseMul h u.1)
    (ccmArchimedeanPhaseMul (-h) u.1)).filter_mono
    (ae_mono volume_le_ccmArchimedeanFormMeasure)
  filter_upwards [hp, hm, ha] with x hp hm ha
  change (ccmArchimedeanPhaseMul h u.1 + ccmArchimedeanPhaseMul (-h) u.1 :
    CCMArchimedeanFourierL2) x = _
  rw [ha]
  simp only [Pi.add_apply]
  rw [hp, hm, ← add_mul, phase_sum]
  push_cast
  rfl

def shiftedQuadratic (a : SuzukiPositiveAperture) (E : ℝ) (u : CCMArchimedeanFormDomain a) : ℝ :=
  ccmRestrictedWeilSourceQuadratic a u - E * ‖ccmArchimedeanFormToAperture a u‖ ^ 2

theorem shiftedQuadratic_integrable (a : SuzukiPositiveAperture) (E : ℝ)
    (u : CCMArchimedeanFormDomain a) :
    Integrable fun x : ℝ => (levelSymbol a x - E) * ‖(u.1 : ℝ → ℂ) x‖ ^ 2 := by
  have hi := (integrable_levelSymbol_mul a u).sub
    ((integrable_norm_sq_unitaryLaplace a u).const_mul E)
  refine hi.congr ?_
  filter_upwards [freq_ae a u] with x hx
  simp only [Pi.sub_apply, hx]
  ring

theorem shiftedQuadratic_eq_integral (a : SuzukiPositiveAperture) (E : ℝ)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u) :
    shiftedQuadratic a E u = ∫ x : ℝ, (levelSymbol a x - E) * ‖(u.1 : ℝ → ℂ) x‖ ^ 2 := by
  rw [shiftedQuadratic, source_eq_integral a u hu, ← integral_norm_sq_eq,
    ← integral_const_mul, ← integral_sub (integrable_levelSymbol_mul a u)
      ((integrable_norm_sq_unitaryLaplace a u).const_mul E)]
  apply integral_congr_ae
  filter_upwards [freq_ae a u] with x hx
  rw [hx]
  ring

private theorem cosine_norm_identity (t : ℝ) (z : ℂ) :
    4 * ‖(2 * Real.cos t : ℂ) * z‖ ^ 2 =
      8 * ‖z‖ ^ 2 + ‖z + (2 * Real.cos (2 * t) : ℂ) * z‖ ^ 2 -
        ‖z - (2 * Real.cos (2 * t) : ℂ) * z‖ ^ 2 := by
  have hn (r : ℝ) : ‖(r : ℂ) * z‖ ^ 2 = r ^ 2 * ‖z‖ ^ 2 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hp : z + (2 * Real.cos (2 * t) : ℂ) * z =
      ((1 + 2 * Real.cos (2 * t) : ℝ) : ℂ) * z := by push_cast; ring
  have hm : z - (2 * Real.cos (2 * t) : ℂ) * z =
      ((1 - 2 * Real.cos (2 * t) : ℝ) : ℂ) * z := by push_cast; ring
  have hc : (2 * Real.cos t : ℂ) = ((2 * Real.cos t : ℝ) : ℂ) := by push_cast; rfl
  rw [hp, hm, hc, hn, hn, hn, Real.cos_two_mul]
  ring

/-- Exact cosine multiplier law for the complete source, with any mass shift. -/
theorem shiftedQuadratic_cosine_identity {a b : SuzukiPositiveAperture} (E h : ℝ)
    (hfit : a.1 + |h| ≤ b.1) (hfit₂ : a.1 + |2 * h| ≤ b.1)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u)
    (w : CCMArchimedeanFormDomain b) (hw : w.1 = u.1) :
    4 * shiftedQuadratic b E (cosineTranslate h hfit u) =
      8 * shiftedQuadratic b E w +
        shiftedQuadratic b E (w + cosineTranslate (2 * h) hfit₂ u) -
        shiftedQuadratic b E (w - cosineTranslate (2 * h) hfit₂ u) := by
  have hab : a.1 ≤ b.1 := by linarith [abs_nonneg h]
  have hpw := (isPolarConstrained_iff_of_val_eq hab hw).mpr hu
  have hps := cosineTranslate_isPolar h hfit hu
  have hpt := cosineTranslate_isPolar (2 * h) hfit₂ hu
  let s := cosineTranslate h hfit u
  let t := cosineTranslate (2 * h) hfit₂ u
  have hpa : IsPolarConstrained b (w + t) := (ccmPolarConstraintSubmodule b).add_mem hpw hpt
  have hpd : IsPolarConstrained b (w - t) := (ccmPolarConstraintSubmodule b).sub_mem hpw hpt
  have hia : Integrable (fun x : ℝ =>
      8 * ((levelSymbol b x - E) * ‖(w.1 : ℝ → ℂ) x‖ ^ 2) +
        (levelSymbol b x - E) * ‖((w + t).1 : ℝ → ℂ) x‖ ^ 2) :=
    ((shiftedQuadratic_integrable b E w).const_mul 8).add
      (shiftedQuadratic_integrable b E (w + t))
  change 4 * shiftedQuadratic b E s =
    8 * shiftedQuadratic b E w + shiftedQuadratic b E (w + t) - shiftedQuadratic b E (w - t)
  rw [shiftedQuadratic_eq_integral b E s hps, shiftedQuadratic_eq_integral b E w hpw,
    shiftedQuadratic_eq_integral b E (w + t) hpa, shiftedQuadratic_eq_integral b E (w - t) hpd,
    ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((shiftedQuadratic_integrable b E w).const_mul 8)
      (shiftedQuadratic_integrable b E (w + t)),
    ← integral_sub hia (shiftedQuadratic_integrable b E (w - t))]
  apply integral_congr_ae
  have ha := (Lp.coeFn_add w.1 t.1).filter_mono (ae_mono volume_le_ccmArchimedeanFormMeasure)
  have hd := (Lp.coeFn_sub w.1 t.1).filter_mono (ae_mono volume_le_ccmArchimedeanFormMeasure)
  filter_upwards [cosineTranslate_coeFn h hfit u, cosineTranslate_coeFn (2 * h) hfit₂ u,
    ha, hd] with x hs ht ha hd
  change 4 * ((levelSymbol b x - E) * ‖(s.1 : ℝ → ℂ) x‖ ^ 2) =
    8 * ((levelSymbol b x - E) * ‖(w.1 : ℝ → ℂ) x‖ ^ 2) +
      (levelSymbol b x - E) * ‖(w.1 + t.1 : CCMArchimedeanFourierL2) x‖ ^ 2 -
      (levelSymbol b x - E) * ‖(w.1 - t.1 : CCMArchimedeanFourierL2) x‖ ^ 2
  dsimp only [Pi.add_apply] at ha
  dsimp only [Pi.sub_apply] at hd
  rw [hs, ha, hd, hw, ht,
    show 2 * Real.pi * ((2 * h) * x) = 2 * (2 * Real.pi * (h * x)) by ring]
  linear_combination (levelSymbol b x - E) *
    cosine_norm_identity (2 * Real.pi * (h * x)) ((u.1 : ℝ → ℂ) x)

def evenPolarSubmodule (a : SuzukiPositiveAperture) : Submodule ℂ (CCMArchimedeanFormDomain a) where
  carrier := {u | IsPolarConstrained a u ∧ IsEven a u}
  add_mem' := fun hu hv => ⟨(ccmPolarConstraintSubmodule a).add_mem hu.1 hv.1, hu.2.add a hv.2⟩
  zero_mem' := ⟨isPolarConstrained_zero a, isEven_zero a⟩
  smul_mem' := fun c _ hu => ⟨hu.1.smul c, hu.2.smul a c⟩

theorem shiftedQuadratic_add_eq_sub_of_evenGround (a : SuzukiPositiveAperture)
    {u v : CCMArchimedeanFormDomain a} (hu : IsEvenGround a u)
    (hv : IsPolarConstrained a v) (hev : IsEven a v) :
    shiftedQuadratic a (evenGroundEnergy a) (u + v) =
      shiftedQuadratic a (evenGroundEnergy a) (u - v) := by
  let E := evenGroundEnergy a
  let K := ccmRestrictedWeilFormBirmanSchwinger a E
  let T : CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a :=
    ContinuousLinearMap.id ℂ _ - K
  have hnull : u ∈ compactConstrainedRadical (evenPolarSubmodule a) K := by
    apply mem_compactConstrainedRadical_of_null (evenPolarSubmodule a) K
      (ccmRestrictedWeilFormBirmanSchwinger_isSelfAdjoint a E)
    · intro z hz
      rw [ccmRestrictedWeil_shifted_diagonal]
      exact sub_nonneg.mpr (evenGroundEnergy_mul_le a z hz.1 hz.2)
    · exact ⟨hu.1, hu.2.1⟩
    · rw [ccmRestrictedWeil_shifted_diagonal, hu.2.2]
      exact sub_self _
  have hvu : inner ℂ v (T u) = 0 :=
    ((mem_compactConstrainedRadical (evenPolarSubmodule a) K u).mp hnull).2 v ⟨hv, hev⟩
  have hsym : (T : CCMArchimedeanFormDomain a →ₗ[ℂ] CCMArchimedeanFormDomain a).IsSymmetric := by
    intro x y
    change inner ℂ (x - K x) y = inner ℂ x (y - K y)
    have hs := (ccmRestrictedWeilFormBirmanSchwinger_isSelfAdjoint a E).isSymmetric x y
    change inner ℂ (K x) y = inner ℂ x (K y) at hs
    rw [inner_sub_left, inner_sub_right, hs]
  have huv : inner ℂ u (T v) = 0 := by
    have hs : inner ℂ (T u) v = inner ℂ u (T v) := hsym u v
    have hc := inner_conj_symm (𝕜 := ℂ) (T u) v
    rw [hvu, map_zero] at hc
    exact hs.symm.trans hc.symm
  have hdiag (z : CCMArchimedeanFormDomain a) :
      shiftedQuadratic a E z = (inner ℂ z (T z)).re :=
    (ccmRestrictedWeil_shifted_diagonal a E z).symm
  rw [hdiag, hdiag, map_add, map_sub, inner_add_left, inner_sub_left,
    inner_add_right, inner_add_right, inner_sub_right, inner_sub_right, hvu, huv]
  simp

theorem cosineTranslate_isEvenGround_of_plateau {a b : SuzukiPositiveAperture}
    (heq : evenGroundEnergy b = evenGroundEnergy a) (h : ℝ)
    (hfit : a.1 + |h| ≤ b.1) (hfit₂ : a.1 + |2 * h| ≤ b.1)
    {u : CCMArchimedeanFormDomain a} (hu : IsEvenGround a u) :
    IsEvenGround b (cosineTranslate h hfit u) := by
  have hab : a.1 ≤ b.1 := by linarith [abs_nonneg h]
  obtain ⟨w, hw⟩ := exists_ccmArchimedeanFormDomain_extension hab u
  have hpw := (isPolarConstrained_iff_of_val_eq hab hw).mpr hu.1
  have hew := isEven_of_val_eq hw hu.2.1
  have hwg : IsEvenGround b w := by
    refine ⟨hpw, hew, ?_⟩
    rw [ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hab hw,
      norm_ccmArchimedeanFormToAperture_eq_of_val_eq hw, heq]
    exact hu.2.2
  have hzero : shiftedQuadratic b (evenGroundEnergy b) w = 0 := by
    rw [shiftedQuadratic, hwg.2.2, sub_self]
  have hpair := shiftedQuadratic_add_eq_sub_of_evenGround b hwg
    (cosineTranslate_isPolar (2 * h) hfit₂ hu.1)
    (cosineTranslate_isEven (2 * h) hfit₂ hu.2.1)
  have hid := shiftedQuadratic_cosine_identity (evenGroundEnergy b) h hfit hfit₂ u hu.1 w hw
  rw [hzero, hpair] at hid
  refine ⟨cosineTranslate_isPolar h hfit hu.1, cosineTranslate_isEven h hfit hu.2.1, ?_⟩
  unfold shiftedQuadratic at hid
  linarith

/-- The actual even polar ground strictly decreases at every increase of aperture. -/
theorem strictAnti_evenGroundEnergy : StrictAnti evenGroundEnergy := by
  intro a b hab
  have habv : a.1 < b.1 := hab
  have hle := evenGroundEnergy_antitone hab.le
  by_contra hn
  have heq : evenGroundEnergy b = evenGroundEnergy a := le_antisymm hle (not_lt.mp hn)
  obtain ⟨u, hp, he, hun, huQ⟩ := exists_evenGround a
  have hug : IsEvenGround a u := ⟨hp, he, by rw [huQ, hun]; ring⟩
  haveI := finiteDimensional_evenGroundSubmodule b
  let n := Module.finrank ℂ (evenGroundSubmodule b) + 1
  let h : ℝ := (b.1 - a.1) / (2 * (n + 1))
  have hn0 : (0 : ℝ) < n + 1 := by positivity
  have hh : 0 < h := div_pos (sub_pos.mpr habv) (by positivity)
  have hfit₂ : ∀ i : Fin n, a.1 + |2 * (((i : ℝ) + 1) * h)| ≤ b.1 := by
    intro i
    have hi : (i : ℝ) + 1 ≤ n + 1 := by exact_mod_cast (by omega : i.val + 1 ≤ n + 1)
    rw [abs_of_nonneg (by positivity)]
    have hprod := mul_le_mul_of_nonneg_right hi (show 0 ≤ 2 * h by positivity)
    have heq : (2 * ((n : ℝ) + 1)) * h = b.1 - a.1 := by
      dsimp [h]
      exact mul_div_cancel₀ _ (by positivity)
    nlinarith
  have hfit : ∀ i : Fin n, a.1 + |((i : ℝ) + 1) * h| ≤ b.1 := by
    intro i
    have ht := hfit₂ i
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
    linarith [abs_nonneg (((i : ℝ) + 1) * h)]
  let v (i : Fin n) := cosineTranslate (((i : ℝ) + 1) * h) (hfit i) u
  have hvg : ∀ i, IsEvenGround b (v i) := fun i =>
    cosineTranslate_isEvenGround_of_plateau heq _ (hfit i) (hfit₂ i) hug
  let w (i : Fin n) : evenGroundSubmodule b := ⟨v i, hvg i⟩
  have hune : (ccmArchimedeanFormToAperture a u : SoninL2) ≠ 0 := by
    intro hz
    have hnorm : ‖(ccmArchimedeanFormToAperture a u : SoninL2)‖ = 1 := hun
    rw [hz, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hli := linearIndependent_arithmetic_cosine_translates n hh.ne' hune
  have hwli : LinearIndependent ℂ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hm := congrArg (fun z : evenGroundSubmodule b =>
      (ccmArchimedeanFormToAperture b z.1 : SoninL2)) hc
    have hm' : ∑ i : Fin n, c i •
        (ccmArchimedeanFormToAperture b (v i) : SoninL2) = 0 := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
        map_sum, map_smul, map_zero] using hm
    simp only [v, cosineTranslate, add_apply, map_add,
      Submodule.coe_add, ccmArchimedeanFormTranslate_physical] at hm'
    exact (Fintype.linearIndependent_iff.mp hli) c hm'
  have hdim := hwli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hdim
  dsimp [n] at hdim
  omega

/-- Zero energy cannot persist in the even sector after any aperture increase. -/
theorem evenGroundEnergy_neg_above_zero {a b : SuzukiPositiveAperture}
    (hab : a < b) (ha : evenGroundEnergy a = 0) : evenGroundEnergy b < 0 := by
  simpa only [ha] using strictAnti_evenGroundEnergy hab

end RHTower.CCMEvenSector
