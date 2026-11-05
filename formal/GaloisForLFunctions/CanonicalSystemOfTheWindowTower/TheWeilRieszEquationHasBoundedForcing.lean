import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLocalWeilKernelIsHermiteBiehler
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.PositiveLevelTruncationsStayInTheWeilDomain

/-!
# Bounded forcing in the actual Weil Riesz equation

The completed real graph decomposition preserves the exact mixed Weil form.
Its two coordinates in a Fourier-evaluation Riesz vector have mass-relative
forcing bounds, obtained from the literal Fourier integral on nonnegative tests.
-/

open MeasureTheory Set Filter Complex
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

open _root_.RHTower _root_.RHTower.CHMDDoobGraph _root_.RHTower.CHMDPolar

namespace WeilHilbertBeforeContact

/-- A completed real inverse-Doob graph vector in the unshifted complex Weil space. -/
def ofRealGraph (a : PrecontactAperture) (p : apertureGraphCompletion a.1) :
    WeilHilbertBeforeContact a :=
  (toForm a).symm (apertureGraphWeilEquiv a.1 p).val

theorem toForm_ofRealGraph (a : PrecontactAperture) (p : apertureGraphCompletion a.1) :
    toForm a (ofRealGraph a p) = (apertureGraphWeilEquiv a.1 p).val :=
  (toForm a).apply_symm_apply _

theorem ofRealGraph_add (a : PrecontactAperture) (p q : apertureGraphCompletion a.1) :
    ofRealGraph a (p + q) = ofRealGraph a p + ofRealGraph a q := by
  unfold ofRealGraph
  rw [map_add]
  exact map_add (toForm a).symm _ _

theorem ofRealGraph_neg (a : PrecontactAperture) (p : apertureGraphCompletion a.1) :
    ofRealGraph a (-p) = -ofRealGraph a p := by
  unfold ofRealGraph
  rw [map_neg]
  exact map_neg (toForm a).symm _

theorem norm_ofRealGraph_sq (a : PrecontactAperture) (p : apertureGraphCompletion a.1) :
    ‖ofRealGraph a p‖ ^ 2 = weilForm p.val := by
  rw [norm_sq_eq_weil, toForm_ofRealGraph]
  have h := apertureWeilSignedQuotient_weil a.1 (apertureGraphWeilEquiv a.1 p)
  change quotientWeilForm (signedQuotientMk
    ((apertureGraphWeilEquiv a.1).symm (apertureGraphWeilEquiv a.1 p)).val) = _ at h
  rw [ContinuousLinearEquiv.symm_apply_apply, quotientWeilForm_mk] at h
  exact h.symm

private theorem weilBilin_add_left (p q r : SourceGraph) :
    weilBilin (p + q) r = weilBilin p r + weilBilin q r := by
  have h := weilBilin_sub_left (p + q) p r
  rw [add_sub_cancel_left] at h
  linarith only [h]

private theorem weilBilin_add_right (p q r : SourceGraph) :
    weilBilin p (q + r) = weilBilin p q + weilBilin p r := by
  rw [weilBilin_comm p, weilBilin_add_left, weilBilin_comm q p, weilBilin_comm r p]

/-- Polarization identifies the completed real graph form with the exact Weil inner product. -/
theorem inner_ofRealGraph (a : PrecontactAperture) (p q : apertureGraphCompletion a.1) :
    inner ℂ (ofRealGraph a p) (ofRealGraph a q) = (weilBilin p.val q.val : ℂ) := by
  have hnorm := norm_ofRealGraph_sq a (p + q)
  rw [ofRealGraph_add, norm_add_sq (𝕜 := ℂ) (E := WeilHilbertBeforeContact a),
    norm_ofRealGraph_sq, norm_ofRealGraph_sq] at hnorm
  have hpolar : weilForm (p.val + q.val) =
      weilForm p.val + 2 * weilBilin p.val q.val + weilForm q.val := by
    simp only [weilForm_eq_weilBilin, weilBilin_add_left, weilBilin_add_right,
      weilBilin_comm q.val p.val]
    ring
  change _ = weilForm (p.val + q.val) at hnorm
  rw [hpolar] at hnorm
  change weilForm p.val +
      2 * (inner ℂ (ofRealGraph a p) (ofRealGraph a q)).re + weilForm q.val =
    weilForm p.val + 2 * weilBilin p.val q.val + weilForm q.val at hnorm
  apply Complex.ext
  · change _ = weilBilin p.val q.val
    linarith only [hnorm]
  · rw [inner_eq_weil, toForm_ofRealGraph, toForm_ofRealGraph]
    exact apertureWeilCompletion_weil_im_eq_zero a.1
      (apertureGraphWeilEquiv a.1 p).property (apertureGraphWeilEquiv a.1 q).property

theorem exists_real_graph_decomposition (a : PrecontactAperture)
    (v : WeilHilbertBeforeContact a) :
    ∃ p r : apertureGraphCompletion a.1, v = ofRealGraph a p + I • ofRealGraph a r := by
  obtain ⟨p, r, hv, _⟩ := exists_apertureWeilCompletion_complex_decomposition a.1 (toForm a v)
  refine ⟨(apertureGraphWeilEquiv a.1).symm p, (apertureGraphWeilEquiv a.1).symm r, ?_⟩
  apply (toForm a).injective
  rw [map_add, map_smul, toForm_ofRealGraph, toForm_ofRealGraph,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact hv

theorem fourier_ofRealGraph (a : PrecontactAperture) (p : apertureGraphCompletion a.1)
    (z : ℂ) :
    fourier a (ofRealGraph a p) z =
      suzukiCompactL2Fourier a.1.1 (graphPhysicalSource p.val) z := by
  rw [fourier_eq_whole, toForm_ofRealGraph]
  change suzukiCompactL2Fourier a.1.1
    (ccmArchimedeanFormEmbedding a.1 (apertureGraphWeilEquiv a.1 p).val) z = _
  rw [apertureGraphWeilEquiv_physical]

theorem norm_eval_ofRealGraph_le_mass (a : PrecontactAperture)
    (p : apertureGraphCompletion a.1) (z : ℂ)
    (hn : ∀ᵐ x ∂massMeasure, 0 ≤ p.val.val.fst x) :
    ‖eval a z (ofRealGraph a p)‖ ≤
      Real.exp (a.1.1 * |z.im|) * ∫ x, p.val.val.fst x ∂massMeasure := by
  let F := p.val.val.fst
  have hnV : ∀ᵐ x ∂volume, 0 ≤ F x := by
    exact volume_absolutelyContinuous_mass.ae_le hn
  have hi : Integrable F massMeasure := (Lp.memLp F).integrable (by norm_num)
  have hiw : Integrable (fun x => massDensity x * F x) :=
    (integrable_weighted_iff volume continuous_massDensity.measurable
      (Eventually.of_forall fun x => (massDensity_pos x).le) F).mp hi
  have hs := physicalSource_supported_of_mem_apertureGraphCompletion a.1 p.property
  have hphys : Integrable (graphPhysicalSource p.val) := by
    simpa only [hs] using integrable_suzukiCutoff a.1.1 (graphPhysicalSource p.val)
  have hL1 : (∫ x, ‖graphPhysicalSource p.val x‖) ≤ ∫ x, F x ∂massMeasure := by
    rw [integral_mass]
    apply integral_mono_ae hphys.norm hiw
    filter_upwards [graphPhysicalSource_ae p.val, hnV] with x hx hn
    rw [hx, Complex.norm_real, Real.norm_eq_abs]
    change |riemannKernelReal x * F x| ≤ massDensity x * F x
    rw [abs_of_nonneg (mul_nonneg (riemannKernelReal_pos x).le hn), massDensity]
    have h := mul_le_mul_of_nonneg_left (Real.one_le_cosh (x / 2))
      (mul_nonneg (riemannKernelReal_pos x).le hn)
    nlinarith only [h]
  change ‖fourier a (ofRealGraph a p) z‖ ≤ _
  rw [fourier_ofRealGraph]
  have he := norm_suzukiCompactL2Fourier_le a.1.2.le (graphPhysicalSource p.val) z
  rw [hs] at he
  exact he.trans (by
    rw [mul_comm (Real.exp _)]
    exact mul_le_mul_of_nonneg_right hL1 (Real.exp_pos _).le)

/-- Both real Riesz coordinates have bounded Fourier forcing relative to positive test mass. -/
theorem riesz_real_graph_forcing (a : PrecontactAperture) (z : ℂ) :
    ∃ p r : apertureGraphCompletion a.1,
      evalVector a z = ofRealGraph a p + I • ofRealGraph a r ∧
      ∀ q : apertureGraphCompletion a.1,
        (∀ᵐ x ∂massMeasure, 0 ≤ q.val.val.fst x) →
        |weilBilin p.val q.val| ≤
          Real.exp (a.1.1 * |z.im|) * ∫ x, q.val.val.fst x ∂massMeasure ∧
        |weilBilin r.val q.val| ≤
          Real.exp (a.1.1 * |z.im|) * ∫ x, q.val.val.fst x ∂massMeasure := by
  obtain ⟨p, r, hv⟩ := exists_real_graph_decomposition a (evalVector a z)
  refine ⟨p, r, hv, fun q hq => ?_⟩
  have he := inner_evalVector a z (ofRealGraph a q)
  rw [hv, inner_add_left (E := WeilHilbertBeforeContact a),
    inner_smul_left (E := WeilHilbertBeforeContact a), inner_ofRealGraph, inner_ofRealGraph,
    Complex.conj_I] at he
  have hre : (eval a z (ofRealGraph a q)).re = weilBilin p.val q.val := by
    rw [← he]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.neg_re, Complex.I_re, neg_zero, zero_mul,
      Complex.ofReal_im, mul_zero, sub_zero, add_zero]
  have him : (eval a z (ofRealGraph a q)).im = -weilBilin r.val q.val := by
    rw [← he]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.neg_im, Complex.I_im, Complex.ofReal_re,
      Complex.neg_re, Complex.I_re, neg_zero, zero_mul, zero_add,
      neg_one_mul]
  have hb := norm_eval_ofRealGraph_le_mass a q z hq
  constructor
  · rw [← hre]
    exact (Complex.abs_re_le_norm _).trans hb
  · have h := (Complex.abs_im_le_norm (eval a z (ofRealGraph a q))).trans hb
    simpa only [him, abs_neg] using h

#print axioms riesz_real_graph_forcing

end WeilHilbertBeforeContact
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
