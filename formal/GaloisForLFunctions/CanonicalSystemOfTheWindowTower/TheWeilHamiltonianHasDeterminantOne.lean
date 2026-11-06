import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilTowerHasItsPrecontactCanonicalSystem
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TranslationPreservesTheCompleteWeilForm

/-!
# The actual Weil Hamiltonian has determinant one

Translation turns a one-sided aperture extension into a shifted symmetric window.
A single entering collar supplies a variational lower bound on either shifted
kernel slope. Together the two bounds force the exact anchor-trace difference
`|τ_L(i)|² - |τ_R(i)|² = 2 K(i,i)`. Hence the actual precontact Hamiltonian
is positive definite with determinant one. The trace readouts polarize this
rigidity into the exact difference of the two endpoint densities.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact
open _root_.RHTower
open GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

/-- Translation acts on evaluation at `i` by the real character `exp(s)`. -/
private theorem fourier_translate_I {a b : PrecontactAperture} (s : ℝ)
    (hab : a.1.1+|s| ≤ b.1.1) (u : WeilHilbertBeforeContact a) :
    fourier b (translate s hab u) I = (Real.exp s : ℂ)*fourier a u I := by
  rw [fourier_translate]
  have he : -I*I*(s : ℂ) = (s : ℂ) := by
    rw [neg_mul, Complex.I_mul_I, neg_neg, one_mul]
  rw [he, ← Complex.ofReal_exp]

/-- Opposite translations give the literal inclusion into a larger window. -/
private theorem translate_back {a b c : PrecontactAperture} (s : ℝ)
    (hab : a.1.1+|s| ≤ b.1.1) (hbc : b.1.1+|-s| ≤ c.1.1)
    (hac : a.1.1 ≤ c.1.1) (u : WeilHilbertBeforeContact a) :
    translate (-s) hbc (translate s hab u) = inclusion hac u := by
  apply fourier_injective c
  funext z
  rw [fourier_translate, fourier_translate, fourier_inclusion, ← mul_assoc, ← Complex.exp_add]
  rw [show -I*z*((-s : ℝ) : ℂ)+ -I*z*(s : ℂ) = 0 by push_cast; ring,
    Complex.exp_zero, one_mul]

/-- Orthogonal evaluation residual after translating the smaller window. -/
private def translatedAnchorResidual {a b : PrecontactAperture} (s : ℝ)
    (hab : a.1.1+|s| ≤ b.1.1) : WeilHilbertBeforeContact b :=
  evalVector b I-(Real.exp s : ℂ) • translate s hab (evalVector a I)

/-- The residual norm is the exact difference of the translated diagonal kernels. -/
private theorem translatedAnchorResidual_norm {a b : PrecontactAperture} (s : ℝ)
    (hab : a.1.1+|s| ≤ b.1.1) :
    ‖translatedAnchorResidual s hab‖^2 =
      ‖evalVector b I‖^2-(Real.exp s)^2*‖evalVector a I‖^2 := by
  have hi : inner ℂ (evalVector b I) (translate s hab (evalVector a I)) =
      (Real.exp s : ℂ)*(‖evalVector a I‖ : ℂ)^2 := by
    rw [inner_evalVector]
    change fourier b (translate s hab (evalVector a I)) I = _
    rw [fourier_translate_I]
    change (Real.exp s : ℂ)*eval a I (evalVector a I) = _
    rw [evalVector_self]
  rw [translatedAnchorResidual, norm_sub_sq (𝕜 := ℂ), inner_smul_right, hi,
    norm_smul, (translate s hab).norm_map]
  have hRe (z : ℂ) : RCLike.re z = z.re := rfl
  simp only [hRe, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos s)]
  ring

/-- Translation carries the residual pairing to the full symmetric increment. -/
private theorem translatedAnchorResidual_pair {a b d : PrecontactAperture} (s : ℝ)
    (hab : a.1.1+|s| ≤ b.1.1) (hbd : b.1.1+|-s| ≤ d.1.1)
    (had : a.1.1 ≤ d.1.1) (v : WeilHilbertBeforeContact b) :
    inner ℂ v (translatedAnchorResidual s hab) =
      (Real.exp s : ℂ)*inner ℂ (translate (-s) hbd v) (evalVectorIncrement had I) := by
  have hev : eval b I v = (Real.exp s : ℂ)*eval d I (translate (-s) hbd v) := by
    change fourier b v I = (Real.exp s : ℂ)*fourier d (translate (-s) hbd v) I
    rw [fourier_translate_I, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
      add_neg_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]
  have hin : inner ℂ v (translate s hab (evalVector a I)) =
      inner ℂ (translate (-s) hbd v) (inclusion had (evalVector a I)) := by
    rw [← translate_back s hab hbd had (evalVector a I)]
    exact ((translate (-s) hbd).inner_map_map _ _).symm
  rw [translatedAnchorResidual, inner_sub_right, inner_smul_right, hin,
    evalVectorIncrement, inner_sub_right]
  have hel : inner ℂ v (evalVector b I) =
      (Real.exp s : ℂ)*inner ℂ (translate (-s) hbd v) (evalVector d I) := by
    rw [← inner_conj_symm (𝕜 := ℂ) (E := WeilHilbertBeforeContact b),
      ← inner_conj_symm (𝕜 := ℂ) (E := WeilHilbertBeforeContact d),
      inner_evalVector, inner_evalVector, hev, map_mul, Complex.conj_ofReal]
  rw [hel]
  ring

/-- Remove the evaluation character from the translated residual. -/
private def oneSidedAnchorResidual {a b : PrecontactAperture} (s : ℝ)
    (hab : a.1.1+|s| ≤ b.1.1) : WeilHilbertBeforeContact b :=
  (Real.exp (-s) : ℂ) • translatedAnchorResidual s hab

private theorem oneSidedAnchorResidual_norm {a b : PrecontactAperture} (s : ℝ)
    (hab : a.1.1+|s| ≤ b.1.1) :
    ‖oneSidedAnchorResidual s hab‖^2 =
      (Real.exp (-s))^2*‖evalVector b I‖^2-‖evalVector a I‖^2 := by
  have he : Real.exp (-s)*Real.exp s = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have he2 := congrArg (fun t : ℝ => t^2) he
  rw [oneSidedAnchorResidual, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow, translatedAnchorResidual_norm]
  linear_combination -‖evalVector a I‖^2*he2

private theorem oneSidedAnchorResidual_pair {a b d : PrecontactAperture} (s : ℝ)
    (hab : a.1.1+|s| ≤ b.1.1) (hbd : b.1.1+|-s| ≤ d.1.1)
    (had : a.1.1 ≤ d.1.1) (v : WeilHilbertBeforeContact b) :
    inner ℂ v (oneSidedAnchorResidual s hab) =
      inner ℂ (translate (-s) hbd v) (evalVectorIncrement had I) := by
  rw [oneSidedAnchorResidual, inner_smul_right,
    translatedAnchorResidual_pair s hab hbd had v, ← mul_assoc,
    ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel,
    Real.exp_zero, Complex.ofReal_one, one_mul]

/-- A constant collar trial extracts its normalized response from the residual energy. -/
private theorem singleCollar_variational {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (R v : H) (α : ℂ) {h L D : ℝ} (hh : 0 < h) (hL : 0 < L)
    (hv : ‖v‖^2 ≤ h*(L+D)) :
    2*((starRingEnd ℂ) α*(inner ℂ v R/((h*Real.sqrt L : ℝ) : ℂ))).re-
      (1+D/L)*‖α‖^2 ≤ ‖R‖^2/h := by
  let w : H := (Real.sqrt L : ℂ)⁻¹ • (α • v)
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hsC : (Real.sqrt L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hhC : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  have hw : ‖w‖^2 ≤ h*(1+D/L)*‖α‖^2 := by
    have hn : ‖w‖^2 = ‖α‖^2*‖v‖^2/L := by
      dsimp only [w]
      rw [norm_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs, mul_pow, mul_pow, inv_pow, Real.sq_sqrt hL.le]
      ring
    rw [hn]
    calc
      _ ≤ (‖α‖^2*(h*(L+D)))/L := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hv (sq_nonneg _)) hL.le
      _ = _ := by field_simp
  have hp : (inner ℂ w R).re =
      h*((starRingEnd ℂ) α*(inner ℂ v R/((h*Real.sqrt L : ℝ) : ℂ))).re := by
    have he : inner ℂ w R =
        (h : ℂ)*((starRingEnd ℂ) α*(inner ℂ v R/((h*Real.sqrt L : ℝ) : ℂ))) := by
      dsimp only [w]
      rw [inner_smul_left, inner_smul_left, map_inv₀, Complex.conj_ofReal]
      push_cast
      field_simp
    rw [he, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hnon := sq_nonneg ‖w-R‖
  rw [norm_sub_sq (𝕜 := ℂ)] at hnon
  change 0 ≤ ‖w‖^2-2*(inner ℂ w R).re+‖R‖^2 at hnon
  rw [hp] at hnon
  apply (le_div_iff₀ hh).mpr
  nlinarith only [hw, hnon]

/-- The variational value of a collar with its logarithmic leading energy. -/
private def singleCollarValue (α : ℂ) (D : ℝ) (m : ℝ → ℂ) (h : ℝ) : ℝ :=
  2*((starRingEnd ℂ) α*m h).re-(1+D/Real.log (1/h))*‖α‖^2

/-- The normalized collar response tends to its trace and attains the squared trace. -/
private theorem singleCollarValue_tendsto (α : ℂ) (D : ℝ) (m : ℝ → ℂ)
    (hm : Tendsto m (𝓝[>] (0 : ℝ)) (𝓝 α)) :
    Tendsto (singleCollarValue α D m) (𝓝[>] (0 : ℝ)) (𝓝 (‖α‖^2)) := by
  have hp : Tendsto (fun h => ((starRingEnd ℂ) α*m h).re)
      (𝓝[>] (0 : ℝ)) (𝓝 (‖α‖^2)) := by
    have hr := Complex.continuous_re.continuousAt.tendsto.comp
      (hm.const_mul ((starRingEnd ℂ) α))
    simpa only [Function.comp_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq] using hr
  have hL : Tendsto (fun h : ℝ => Real.log (1/h)) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [one_div, Real.log_inv, Function.comp_def] using
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hD : Tendsto (fun h : ℝ => 1+D/Real.log (1/h)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hi := (tendsto_inv_atTop_zero.comp hL).const_mul D
    simpa only [div_eq_mul_inv, mul_zero, add_zero, Function.comp_def] using
      tendsto_const_nhds.add hi
  have ht := (hp.const_mul 2).sub (hD.mul_const (‖α‖^2))
  rw [show 2*‖α‖^2-1*‖α‖^2 = ‖α‖^2 by ring] at ht
  exact ht

private def rightAnchorCollarValue {a c : PrecontactAperture} (hac : a.1.1 < c.1.1) : ℝ → ℝ :=
  singleCollarValue (evalRightEndpointTrace a I)
    (3+‖weilLogarithmicCorrection c.1‖+weilExteriorCrossingBound c.1)
    (fun h => inner ℂ (logarithmicIntervalSource 0 h)
      (suzukiPositiveZeroExtension (evalVectorRightCollarResidual hac.le I)) /
        ((h*Real.sqrt (Real.log (1/h)) : ℝ) : ℂ))

private def leftAnchorCollarValue {a c : PrecontactAperture} (hac : a.1.1 < c.1.1) : ℝ → ℝ :=
  singleCollarValue (evalLeftEndpointTrace a I)
    (3+‖weilLogarithmicCorrection c.1‖+weilExteriorCrossingBound c.1)
    (fun h => inner ℂ (logarithmicIntervalSource 0 h)
      (suzukiPositiveZeroExtension (evalVectorLeftCollarResidual hac.le I)) /
        ((h*Real.sqrt (Real.log (1/h)) : ℝ) : ℂ))

private theorem rightAnchorCollarValue_tendsto {a c : PrecontactAperture} (hac : a.1.1 < c.1.1) :
    Tendsto (rightAnchorCollarValue hac) (𝓝[>] (0 : ℝ)) (𝓝 (‖evalRightEndpointTrace a I‖^2)) :=
  singleCollarValue_tendsto _ _ _ (evalVectorRightCollarResidual_mean_limit hac I)

private theorem leftAnchorCollarValue_tendsto {a c : PrecontactAperture} (hac : a.1.1 < c.1.1) :
    Tendsto (leftAnchorCollarValue hac) (𝓝[>] (0 : ℝ)) (𝓝 (‖evalLeftEndpointTrace a I‖^2)) :=
  singleCollarValue_tendsto _ _ _ (evalVectorLeftCollarResidual_mean_limit hac I)

/-- Left and right entering collars bound the two one-sided diagonal increments. -/
private theorem shiftedCollar_values_le {a b d c : PrecontactAperture}
    (hac : a.1.1 < c.1.1) {h : ℝ} (hh : 0 < h) (hh1 : h < 1)
    (hha : h < 2*a.1.1) (hb : b.1.1 = a.1.1+h/2)
    (hd : d.1.1 = a.1.1+h) (hdc : d.1.1 ≤ c.1.1) :
    leftAnchorCollarValue hac h ≤
      ((Real.exp (h/2))^2*‖evalVector b I‖^2-‖evalVector a I‖^2)/h ∧
    rightAnchorCollarValue hac h ≤
      ((Real.exp (-(h/2)))^2*‖evalVector b I‖^2-‖evalVector a I‖^2)/h := by
  have ha0 : 0 ≤ a.1.1-h/2 := by linarith only [hha]
  have hbp : b.1.1 = (a.1.1-h/2)+h := by rw [hb]; ring
  -- Reverse translation turns these collars into the old window’s literal entering intervals.
  obtain ⟨l,r,hl,hr⟩ := exists_constantCollar_pair b ha0 hh hbp
  have hs : 0 ≤ h/2 := (div_pos hh (by norm_num)).le
  have habR : a.1.1+|h/2| ≤ b.1.1 := by rw [abs_of_nonneg hs, hb]
  have habL : a.1.1+|-(h/2)| ≤ b.1.1 := by rw [abs_neg]; exact habR
  have hbdL : b.1.1+|-(-(h/2))| ≤ d.1.1 := by
    rw [neg_neg, abs_of_nonneg hs, hb, hd]
    linarith only
  have hbdR : b.1.1+|-(h/2)| ≤ d.1.1 := by
    rw [abs_neg, abs_of_nonneg hs, hb, hd]
    linarith only
  have had : a.1.1 ≤ d.1.1 := by rw [hd]; exact le_add_of_nonneg_right hh.le
  let ld := translate (-(-(h/2))) hbdL l
  let rd := translate (-(h/2)) hbdR r
  have hld : ccmArchimedeanFormEmbedding d.1 (toForm d ld) =
      logarithmicIntervalSource (-a.1.1-h) (-a.1.1) := by
    dsimp only [ld]
    rw [physical_translate, hl, logarithmicIntervalSource_translation]
    congr 1 <;> ring
  have hrd : ccmArchimedeanFormEmbedding d.1 (toForm d rd) =
      logarithmicIntervalSource a.1.1 (a.1.1+h) := by
    dsimp only [rd]
    rw [physical_translate, hr, logarithmicIntervalSource_translation]
    congr 1 <;> ring
  have hEl : ‖l‖^2 ≤
      h*(Real.log (1/h)+(3+‖weilLogarithmicCorrection c.1‖+weilExteriorCrossingBound c.1)) := by
    have he := constantCollar_pair_energy_upper_in_enclosure hdc a.1.2 hh hh1.le ld rd hld hrd 1 0
    simp only [one_smul, zero_smul, add_zero, norm_one, norm_zero, one_pow,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_one] at he
    rw [show ‖ld‖ = ‖l‖ from (translate (-(-(h/2))) hbdL).norm_map l] at he
    convert he using 1
    ring
  have hEr : ‖r‖^2 ≤
      h*(Real.log (1/h)+(3+‖weilLogarithmicCorrection c.1‖+weilExteriorCrossingBound c.1)) := by
    have he := constantCollar_pair_energy_upper_in_enclosure hdc a.1.2 hh hh1.le ld rd hld hrd 0 1
    simp only [one_smul, zero_smul, zero_add, norm_one, norm_zero, one_pow,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_one] at he
    rw [show ‖rd‖ = ‖r‖ from (translate (-(h/2)) hbdR).norm_map r] at he
    convert he using 1
    ring
  have hpL : inner ℂ l (oneSidedAnchorResidual (-(h/2)) habL) =
      inner ℂ (logarithmicIntervalSource 0 h)
        (suzukiPositiveZeroExtension (evalVectorLeftCollarResidual hac.le I)) := by
    rw [oneSidedAnchorResidual_pair (-(h/2)) habL hbdL had]
    exact inner_constantLeftCollar_increment had hdc I h ld hld
  have hpR : inner ℂ r (oneSidedAnchorResidual (h/2) habR) =
      inner ℂ (logarithmicIntervalSource 0 h)
        (suzukiPositiveZeroExtension (evalVectorRightCollarResidual hac.le I)) := by
    rw [oneSidedAnchorResidual_pair (h/2) habR hbdR had]
    exact inner_constantRightCollar_increment had hdc I h rd hrd
  have hL : 0 < Real.log (1/h) := Real.log_pos ((one_lt_div hh).mpr hh1)
  constructor
  · have he := singleCollar_variational (oneSidedAnchorResidual (-(h/2)) habL) l
      (evalLeftEndpointTrace a I) hh hL hEl
    rw [hpL, oneSidedAnchorResidual_norm, neg_neg] at he
    exact he
  · have he := singleCollar_variational (oneSidedAnchorResidual (h/2) habR) r
      (evalRightEndpointTrace a I) hh hL hEr
    rw [hpR, oneSidedAnchorResidual_norm] at he
    exact he

private def shiftedDiagonal (a σ h : ℝ) : ℝ := Real.exp (σ*h)*diagonalEvalGram I (a+h/2)

/-- Affine aperture transport and the translation character determine both slopes. -/
private theorem shiftedDiagonal_right_deriv {a : ℝ} (ha : a ∈ precontactSet) (σ : ℝ) :
    HasDerivWithinAt (shiftedDiagonal a σ)
      (σ*diagonalEvalGram I a+diagonalEndpointEnergy I a/2) (Ioi 0) 0 := by
  have hc : HasDerivAt (fun h : ℝ => a+h/2) (1/2) 0 :=
    ((hasDerivAt_id (0 : ℝ)).div_const 2).const_add a
  have hqa : HasDerivWithinAt (diagonalEvalGram I) (diagonalEndpointEnergy I a)
      (Ioi a) (a+(0 : ℝ)/2) := by
    simpa only [zero_div, add_zero] using hasDerivWithinAt_diagonalEvalGram_right I ha
  have hm : MapsTo (fun h : ℝ => a+h/2) (Ioi 0) (Ioi a) := by
    intro h hh
    change a < a+h/2
    exact lt_add_of_pos_right a (div_pos hh (by norm_num))
  have hq := hqa.comp 0 hc.hasDerivWithinAt hm
  have he : HasDerivAt (fun h : ℝ => Real.exp (σ*h)) σ 0 := by
    simpa only [id_eq, mul_zero, Real.exp_zero, mul_one, one_mul] using
      ((hasDerivAt_id (0 : ℝ)).const_mul σ).exp
  have h := he.hasDerivWithinAt.mul hq
  change HasDerivWithinAt (shiftedDiagonal a σ) _ (Ioi 0) 0 at h
  simpa only [Function.comp_def, mul_zero, zero_mul, Real.exp_zero, zero_div, add_zero,
    one_mul, div_eq_mul_inv] using h

private theorem shiftedDiagonal_slope_tendsto {a : ℝ} (ha : a ∈ precontactSet) (σ : ℝ) :
    Tendsto (fun h : ℝ => (Real.exp (σ*h)*diagonalEvalGram I (a+h/2)-diagonalEvalGram I a)/h)
      (𝓝[>] (0 : ℝ)) (𝓝 (σ*diagonalEvalGram I a+diagonalEndpointEnergy I a/2)) := by
  have ht := (hasDerivWithinAt_iff_tendsto_slope'
    (self_notMem_Ioi : (0 : ℝ) ∉ Ioi 0)).mp (shiftedDiagonal_right_deriv ha σ)
  have hfun : slope (shiftedDiagonal a σ) 0 = fun h : ℝ =>
      (Real.exp (σ*h)*diagonalEvalGram I (a+h/2)-diagonalEvalGram I a)/h := by
    funext h
    rw [slope_def_field]
    simp only [shiftedDiagonal, mul_zero, Real.exp_zero, zero_div, add_zero, one_mul, sub_zero]
  rw [hfun] at ht
  exact ht

/-- Small collars fit inside a fixed precontact enclosure. -/
private theorem eventually_shiftedCollar_values_le {a c : PrecontactAperture} (hac : a.1.1 < c.1.1) :
    ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      leftAnchorCollarValue hac h ≤
        (Real.exp h*diagonalEvalGram I (a.1.1+h/2)-diagonalEvalGram I a.1.1)/h ∧
      rightAnchorCollarValue hac h ≤
        (Real.exp (-h)*diagonalEvalGram I (a.1.1+h/2)-diagonalEvalGram I a.1.1)/h := by
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds (mul_pos (by norm_num : (0 : ℝ) < 2) a.1.2)).filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds (sub_pos.mpr hac)).filter_mono nhdsWithin_le_nhds] with h hh hh1 hha hhc
  change 0 < h at hh
  have hdc : a.1.1+h < c.1.1 := by linarith only [hhc]
  have hbc : a.1.1+h/2 < c.1.1 := by linarith only [hdc,hh]
  let B : PrecontactAperture := ⟨⟨a.1.1+h/2, add_pos a.1.2 (div_pos hh (by norm_num))⟩,
    (EReal.coe_lt_coe_iff.mpr hbc).trans c.2⟩
  let D : PrecontactAperture := ⟨⟨a.1.1+h, add_pos a.1.2 hh⟩,
    (EReal.coe_lt_coe_iff.mpr hdc).trans c.2⟩
  have he := shiftedCollar_values_le (b := B) (d := D) hac hh hh1 hha rfl rfl hdc.le
  have hexp (t : ℝ) : (Real.exp (t/2))^2 = Real.exp t := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hexpn : (Real.exp (-(h/2)))^2 = Real.exp (-h) := by
    rw [show -(h/2) = (-h)/2 by ring, hexp]
  rw [hexp h, hexpn] at he
  have hqB : diagonalEvalGram I (a.1.1+h/2) = ‖evalVector B I‖^2 :=
    diagonalEvalGram_eq_norm I B
  rw [hqB, diagonalEvalGram_eq_norm I a]
  exact he

/-- The actual anchor traces have energy difference exactly twice the diagonal kernel. -/
theorem evalVector_anchorTrace_energy_difference (a : PrecontactAperture) :
    ‖evalVectorLeftTrace a I‖^2-‖evalVectorRightTrace a I‖^2 = 2*‖evalVector a I‖^2 := by
  have ha : a.1.1 ∈ precontactSet := ⟨a.1.2,a.2⟩
  obtain ⟨c,hac,hc⟩ := EReal.exists_between_coe_real a.2
  have hac' : a.1.1 < c := EReal.coe_lt_coe_iff.mp hac
  let C : PrecontactAperture := ⟨⟨c,a.1.2.trans hac'⟩,hc⟩
  have hlimL : Tendsto
      (fun h : ℝ => (Real.exp h*diagonalEvalGram I (a.1.1+h/2)-diagonalEvalGram I a.1.1)/h)
      (𝓝[>] (0 : ℝ)) (𝓝 (diagonalEvalGram I a.1.1+diagonalEndpointEnergy I a.1.1/2)) := by
    simpa only [one_mul] using shiftedDiagonal_slope_tendsto ha 1
  have hlimR : Tendsto
      (fun h : ℝ => (Real.exp (-h)*diagonalEvalGram I (a.1.1+h/2)-diagonalEvalGram I a.1.1)/h)
      (𝓝[>] (0 : ℝ)) (𝓝 (-diagonalEvalGram I a.1.1+diagonalEndpointEnergy I a.1.1/2)) := by
    simpa only [neg_one_mul] using shiftedDiagonal_slope_tendsto ha (-1)
  -- The two lower bounds squeeze the trace difference to the translation character.
  have hl := le_of_tendsto_of_tendsto (leftAnchorCollarValue_tendsto (a := a) (c := C) hac') hlimL
    ((eventually_shiftedCollar_values_le (a := a) (c := C) hac').mono fun _ h => h.1)
  have hr := le_of_tendsto_of_tendsto (rightAnchorCollarValue_tendsto (a := a) (c := C) hac') hlimR
    ((eventually_shiftedCollar_values_le (a := a) (c := C) hac').mono fun _ h => h.2)
  have hq := diagonalEvalGram_eq_norm I a
  have hE : diagonalEndpointEnergy I a.1.1 =
      ‖evalVectorLeftTrace a I‖^2+‖evalVectorRightTrace a I‖^2 := by
    rw [diagonalEndpointEnergy, dif_pos ha]
    rfl
  rw [hq,hE] at hl hr
  change ‖evalVectorLeftTrace a I‖^2 ≤ _ at hl
  change ‖evalVectorRightTrace a I‖^2 ≤ _ at hr
  linarith only [hl,hr]

/-- The trace-derived Hamiltonian has determinant one at every precontact aperture. -/
theorem canonicalHamiltonian_determinant_one {base a : ℝ} (ha : a ∈ precontactSet) :
    canonicalHamiltonianOne base a*canonicalHamiltonianTwo base a = 1 := by
  rw [canonicalHamiltonian_determinant ha, evalVector_anchorTrace_energy_difference]
  have hq : diagonalEvalGram I a = ‖evalVector (toPrecontact ha) I‖^2 :=
    diagonalEvalGram_eq_norm I (toPrecontact ha)
  rw [hq, div_self, one_pow]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (norm_ne_zero_iff.mpr (evalVector_ne_zero _ _)))

/-- Both diagonal Hamiltonian entries are strictly positive before contact. -/
theorem canonicalHamiltonian_pos {base a : ℝ} (ha : a ∈ precontactSet) :
    0 < canonicalHamiltonianOne base a ∧ 0 < canonicalHamiltonianTwo base a := by
  have hn := canonicalHamiltonian_nonneg base ha
  have hp := canonicalHamiltonian_determinant_one (base := base) ha
  have hne : canonicalHamiltonianOne base a*canonicalHamiltonianTwo base a ≠ 0 := by
    rw [hp]
    exact one_ne_zero
  exact ⟨lt_of_le_of_ne hn.1 (ne_of_apply_ne (fun x => x*canonicalHamiltonianTwo base a)
    (by simpa only [zero_mul] using hne.symm)),
    lt_of_le_of_ne hn.2 (ne_of_apply_ne (fun x => canonicalHamiltonianOne base a*x)
    (by simpa only [mul_zero] using hne.symm))⟩

#print axioms evalVector_anchorTrace_energy_difference
#print axioms canonicalHamiltonian_determinant_one
#print axioms canonicalHamiltonian_pos

/-- The difference of the actual endpoint densities is the spectral translation flux. -/
theorem evalVector_endpoint_flux (w z : ℂ) {a : ℝ} (ha : a ∈ precontactSet) :
    (starRingEnd ℂ) (evalVectorLeftTrace (toPrecontact ha) z)*evalVectorLeftTrace (toPrecontact ha) w-
      (starRingEnd ℂ) (evalVectorRightTrace (toPrecontact ha) z)*evalVectorRightTrace (toPrecontact ha) w =
      I*((starRingEnd ℂ) w-z)*precontactKernel w z a := by
  have hn : ‖evalVector (toPrecontact ha) I‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (evalVector_ne_zero _ _)
  have hl : ‖evalVectorLeftTrace (toPrecontact ha) I‖^2 =
      (evalVectorLeftTrace (toPrecontact ha) I).re^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, evalVectorLeftTrace_I_im]
    ring
  have hr : ‖evalVectorRightTrace (toPrecontact ha) I‖^2 =
      (evalVectorRightTrace (toPrecontact ha) I).re^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, evalVectorRightTrace_I_im]
    ring
  have hd := evalVector_anchorTrace_energy_difference (toPrecontact ha)
  rw [hl,hr] at hd
  -- The two trace-readout coefficients have product exactly one half.
  have hc : 2*
      (((evalVectorLeftTrace (toPrecontact ha) I).re+(evalVectorRightTrace (toPrecontact ha) I).re)/
        (2*‖evalVector (toPrecontact ha) I‖))*
      (((evalVectorLeftTrace (toPrecontact ha) I).re-(evalVectorRightTrace (toPrecontact ha) I).re)/
        (2*‖evalVector (toPrecontact ha) I‖)) = 1 := by
    field_simp [hn]
    nlinarith only [hd]
  have hcC := congrArg (fun t : ℝ => (t : ℂ)) hc
  push_cast at hcC
  have hCD : ((starRingEnd ℂ) w-z)*precontactKernel w z a =
      normalizedCanonicalA z a*(starRingEnd ℂ) (normalizedCanonicalB w a)-
        normalizedCanonicalB z a*(starRingEnd ℂ) (normalizedCanonicalA w a) := by
    simpa only [canonicalSolutionA, canonicalSolutionB, precontactCanonicalGauge,
      intervalIntegral.integral_same, neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul] using
      canonicalSystem_christoffelDarboux a w z ha
  rw [evalVectorLeftTrace_canonical_readout z ha, evalVectorLeftTrace_canonical_readout w ha,
    evalVectorRightTrace_canonical_readout z ha, evalVectorRightTrace_canonical_readout w ha]
  rw [show I*((starRingEnd ℂ) w-z)*precontactKernel w z a =
    I*(((starRingEnd ℂ) w-z)*precontactKernel w z a) by ring, hCD]
  simp only [map_add, map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal,
    starRingEnd_self_apply]
  push_cast
  linear_combination I*(normalizedCanonicalA z a*(starRingEnd ℂ) (normalizedCanonicalB w a)-
    normalizedCanonicalB z a*(starRingEnd ℂ) (normalizedCanonicalA w a))*hcC

#print axioms evalVector_endpoint_flux

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact
