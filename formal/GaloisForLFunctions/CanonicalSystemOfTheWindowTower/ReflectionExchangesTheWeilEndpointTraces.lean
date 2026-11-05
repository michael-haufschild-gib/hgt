import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilRieszVectorsHaveNormalizedEndpointTraces
import GaloisForLFunctions.RHTower.L2FourierConjugation

/-!
# Reflection symmetry of the actual Weil endpoint traces

Physical reflection is unitary for the complete unshifted Weil form. It
reverses the Fourier parameter and exchanges the two normalized endpoint
readouts of the unique continuous Riesz representative.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry
namespace WeilHilbertBeforeContact

/-- Physical reflection on the complete precontact Weil space. -/
def reflection (a : PrecontactAperture) :
    WeilHilbertBeforeContact a →ₗᵢ[ℂ] WeilHilbertBeforeContact a where
  toFun u := fromFormCLM a (ccmArchimedeanFormReflection a.1 (toForm a u))
  map_add' u v := by simp only [map_add]
  map_smul' c u := by simp only [map_smul, RingHom.id_apply]
  norm_map' u := by
    have hs : ‖fromFormCLM a (ccmArchimedeanFormReflection a.1 (toForm a u))‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [norm_sq_eq_weil, norm_sq_eq_weil, toForm_fromForm,
        ccmRestrictedWeilForm_self_re_eq_source, ccmRestrictedWeilForm_self_re_eq_source,
        ccmRestrictedWeilSourceQuadratic_reflection]
    exact le_antisymm ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs.le)
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs.ge)

theorem reflection_involutive (a : PrecontactAperture) (u : WeilHilbertBeforeContact a) :
    reflection a (reflection a u) = u := by
  change fromFormCLM a (ccmArchimedeanFormReflection a.1
    (toForm a (fromFormCLM a (ccmArchimedeanFormReflection a.1 (toForm a u))))) = u
  rw [toForm_fromForm, ccmArchimedeanFormReflection_involutive, fromForm_toForm]

/-- Reflection acts on the literal physical source, without a representative choice. -/
theorem physical_reflection (a : PrecontactAperture) (u : WeilHilbertBeforeContact a) :
    ccmArchimedeanFormEmbedding a.1 (toForm a (reflection a u)) =
      l2Reflection (ccmArchimedeanFormEmbedding a.1 (toForm a u)) := by
  change ccmArchimedeanFormEmbedding a.1
    (ccmArchimedeanFormReflection a.1 (toForm a u)) = _
  simpa only [ccmArchimedeanFormToAperture_coe] using
    ccmArchimedeanFormToAperture_reflection a.1 (toForm a u)

theorem fourier_reflection (a : PrecontactAperture) (u : WeilHilbertBeforeContact a) (z : ℂ) :
    fourier a (reflection a u) z = fourier a u (-z) := by
  rw [fourier_eq_whole, fourier_eq_whole]
  have hcut (v : WeilHilbertBeforeContact a) : suzukiCutoff a.1.1
      (ccmArchimedeanFormToAperture a.1 (toForm a v) : SoninL2) =
      (ccmArchimedeanFormToAperture a.1 (toForm a v) : SoninL2) :=
    indicatorCutoff_suzukiApertureHilbert a.1 _
  unfold suzukiCompactL2Fourier
  change (∫ x : ℝ, (suzukiCutoff a.1.1
      (ccmArchimedeanFormToAperture a.1 (toForm a (reflection a u)) : SoninL2)) x *
        Complex.exp (I * z * (x : ℂ))) =
    ∫ x : ℝ, (suzukiCutoff a.1.1
      (ccmArchimedeanFormToAperture a.1 (toForm a u) : SoninL2)) x *
        Complex.exp (I * (-z) * (x : ℂ))
  rw [hcut, hcut]
  change (∫ x : ℝ, ccmArchimedeanFormEmbedding a.1 (toForm a (reflection a u)) x *
    Complex.exp (I * z * (x : ℂ))) = _
  rw [physical_reflection]
  calc
    _ = ∫ x : ℝ, ccmArchimedeanFormEmbedding a.1 (toForm a u) (-x) *
        Complex.exp (I * (-z) * ((-x : ℝ) : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [l2Reflection_ae (ccmArchimedeanFormEmbedding a.1 (toForm a u))] with x hx
      rw [hx, Complex.ofReal_neg]
      congr 2
      ring
    _ = _ := integral_neg_eq_self
      (fun x : ℝ => ccmArchimedeanFormEmbedding a.1 (toForm a u) x *
        Complex.exp (I * (-z) * (x : ℂ))) volume

/-- The physical reflection of the evaluation vector at `z` is the vector at `-z`. -/
theorem evalVector_reflection (a : PrecontactAperture) (z : ℂ) :
    reflection a (evalVector a z) = evalVector a (-z) := by
  apply ext_inner_right ℂ (E := WeilHilbertBeforeContact a)
  intro u
  calc
    inner ℂ (reflection a (evalVector a z)) u =
        inner ℂ (reflection a (evalVector a z)) (reflection a (reflection a u)) := by
          rw [reflection_involutive]
    _ = inner ℂ (evalVector a z) (reflection a u) := (reflection a).inner_map_map _ _
    _ = fourier a (reflection a u) z := inner_evalVector a z _
    _ = fourier a u (-z) := fourier_reflection a u z
    _ = inner ℂ (evalVector a (-z)) u := (inner_evalVector a (-z) u).symm

/-- Reflection symmetry holds pointwise for the unique continuous actual representative. -/
theorem evalVectorContinuousRepresentative_neg (a : PrecontactAperture) (z : ℂ) (x : ℝ) :
    evalVectorContinuousRepresentative a (-z) x = evalVectorContinuousRepresentative a z (-x) := by
  have hc : Continuous (fun x : ℝ => evalVectorContinuousRepresentative a z (-x)) :=
    (continuous_evalVectorContinuousRepresentative a z).comp continuous_neg
  have he := (evalVectorContinuousRepresentative_ae a z).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  have hp := physical_reflection a (evalVector a z)
  rw [evalVector_reflection] at hp
  have ha : (fun x : ℝ => evalVectorContinuousRepresentative a z (-x)) =ᵐ[volume]
      (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a (-z))) : ℝ → ℂ) := by
    rw [hp]
    exact he.trans (l2Reflection_ae _).symm
  exact (congrFun (evalVectorContinuousRepresentative_unique a (-z) hc ha) x).symm

private theorem physical_smoothCore_ae (a : PrecontactAperture) (v : SuzukiTaSmoothCore a.1) :
    (ccmArchimedeanFormEmbedding a.1 (toForm a (smoothCore a v)) : ℝ → ℂ) =ᵐ[volume] v := by
  change (ccmArchimedeanFormEmbedding a.1
    (suzukiTaSmoothCoreToSource a.1 v).toCCMFormVector : ℝ → ℂ) =ᵐ[volume] v
  have h := (suzukiTaSmoothCoreToSource a.1 v).toCCMFormVector_physical_coeFn
  simp only [ccmArchimedeanFormToAperture_coe] at h
  filter_upwards [h] with x hx
  exact hx

/-- The completed sharp involution is literal conjugate reflection of the physical source. -/
theorem physical_sharp (a : PrecontactAperture) (u : WeilHilbertBeforeContact a) :
    ccmArchimedeanFormEmbedding a.1 (toForm a (sharp a u)) =
      star (l2Reflection (ccmArchimedeanFormEmbedding a.1 (toForm a u))) := by
  let J : WeilHilbertBeforeContact a →L[ℂ] SoninL2 :=
    (ccmArchimedeanFormEmbedding a.1).comp (toFormCLM a)
  have hc : Continuous (fun u : WeilHilbertBeforeContact a => J (sharp a u)) :=
    J.continuous.comp (sharp a).continuous
  have hd : Continuous (fun u : WeilHilbertBeforeContact a => star (l2Reflection (J u))) :=
    continuous_lpStar.comp (l2Reflection.continuous.comp J.continuous)
  have he := hc.ext_on (denseRange_nativeSmoothCore a) hd (by
    rintro _ ⟨v, rfl⟩
    dsimp only
    rw [sharp_smoothCore]
    apply Lp.ext
    have hl := physical_smoothCore_ae a (sharpCore a v)
    have hr := physical_smoothCore_ae a v
    have hrn := hr.comp_tendsto
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
    filter_upwards [hl, hrn, Lp.coeFn_star (l2Reflection (J (smoothCore a v))),
      l2Reflection_ae (J (smoothCore a v))] with x hxl hxr hs hrf
    change ccmArchimedeanFormEmbedding a.1 (toForm a (smoothCore a (sharpCore a v))) x = _
    rw [hxl, hs, Pi.star_apply, hrf]
    change (starRingEnd ℂ) (v (-x)) = (starRingEnd ℂ) (J (smoothCore a v) (-x))
    exact congrArg (starRingEnd ℂ) hxr.symm)
  exact congrFun he u

/-- The continuous representative respects conjugate reflection at every point. -/
theorem evalVectorContinuousRepresentative_conj (a : PrecontactAperture) (z : ℂ) (x : ℝ) :
    evalVectorContinuousRepresentative a ((starRingEnd ℂ) z) x =
      (starRingEnd ℂ) (evalVectorContinuousRepresentative a z (-x)) := by
  have hc : Continuous (fun x : ℝ =>
      (starRingEnd ℂ) (evalVectorContinuousRepresentative a z (-x))) :=
    Complex.continuous_conj.comp
      ((continuous_evalVectorContinuousRepresentative a z).comp continuous_neg)
  have he := (evalVectorContinuousRepresentative_ae a z).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  have hp := physical_sharp a (evalVector a z)
  rw [evalVector_sharp] at hp
  have ha : (fun x : ℝ => (starRingEnd ℂ) (evalVectorContinuousRepresentative a z (-x))) =ᵐ[volume]
      (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a ((starRingEnd ℂ) z))) : ℝ → ℂ) := by
    rw [hp]
    filter_upwards [he, Lp.coeFn_star
      (l2Reflection (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z)))),
      l2Reflection_ae (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z)))]
      with x hx hs hr
    rw [hs, Pi.star_apply, hr]
    exact congrArg (starRingEnd ℂ) hx
  exact (congrFun (evalVectorContinuousRepresentative_unique a ((starRingEnd ℂ) z) hc ha) x).symm

/-- The exact left normalized trace, expressed by its absolutely convergent renewal integral. -/
def evalVectorLeftTrace (a : PrecontactAperture) (z : ℂ) : ℂ :=
  ∫ y : ℝ, (logarithmicCausalKernel y : ℂ) * (evalVectorLeftEndpointForcing a z : RealLineL2) y

/-- The exact right normalized trace of the same physical Riesz source. -/
def evalVectorRightTrace (a : PrecontactAperture) (z : ℂ) : ℂ :=
  ∫ y : ℝ, (logarithmicCausalKernel y : ℂ) * (evalVectorRightEndpointForcing a z : RealLineL2) y

/-- Reversing the Fourier parameter exchanges the actual normalized endpoint traces. -/
theorem evalVectorRightTrace_eq_leftTrace_neg (a : PrecontactAperture) (z : ℂ) :
    evalVectorRightTrace a z = evalVectorLeftTrace a (-z) := by
  have hr := evalVectorContinuousRepresentative_right_normalized_limit a z
  have hl := evalVectorContinuousRepresentative_left_normalized_limit a (-z)
  have he : (fun t : ℝ => evalVectorContinuousRepresentative a (-z) (t-a.1.1) *
      (Real.sqrt (Real.log (1/t)) : ℂ)) =
    (fun t : ℝ => evalVectorContinuousRepresentative a z (a.1.1-t) *
      (Real.sqrt (Real.log (1/t)) : ℂ)) := by
    funext t
    rw [evalVectorContinuousRepresentative_neg, neg_sub]
  rw [he] at hl
  exact tendsto_nhds_unique hr hl

/-- Conjugation also exchanges the two actual normalized readouts. -/
theorem evalVectorLeftTrace_conj (a : PrecontactAperture) (z : ℂ) :
    evalVectorLeftTrace a ((starRingEnd ℂ) z) = (starRingEnd ℂ) (evalVectorRightTrace a z) := by
  have hl := evalVectorContinuousRepresentative_left_normalized_limit a ((starRingEnd ℂ) z)
  have hr := Complex.continuous_conj.continuousAt.tendsto.comp
    (evalVectorContinuousRepresentative_right_normalized_limit a z)
  have he : (fun t : ℝ => evalVectorContinuousRepresentative a ((starRingEnd ℂ) z) (t-a.1.1) *
      (Real.sqrt (Real.log (1/t)) : ℂ)) =
    (fun t : ℝ => (starRingEnd ℂ) (evalVectorContinuousRepresentative a z (a.1.1-t) *
      (Real.sqrt (Real.log (1/t)) : ℂ))) := by
    funext t
    rw [evalVectorContinuousRepresentative_conj, neg_sub, map_mul, Complex.conj_ofReal]
  rw [he] at hl
  exact tendsto_nhds_unique hl hr

/-- At zero frequency the left and right traces agree. -/
theorem evalVectorRightTrace_zero (a : PrecontactAperture) :
    evalVectorRightTrace a 0 = evalVectorLeftTrace a 0 := by
  simpa only [neg_zero] using evalVectorRightTrace_eq_leftTrace_neg a 0

/-- The common zero-frequency normalized trace is real. -/
theorem evalVectorLeftTrace_zero_im (a : PrecontactAperture) :
    (evalVectorLeftTrace a 0).im = 0 := by
  have h := evalVectorLeftTrace_conj a 0
  rw [map_zero, evalVectorRightTrace_zero] at h
  have hi := congrArg Complex.im h
  rw [Complex.conj_im] at hi
  linarith only [hi]

#print axioms reflection
#print axioms evalVector_reflection
#print axioms evalVectorContinuousRepresentative_neg
#print axioms evalVectorRightTrace_eq_leftTrace_neg
#print axioms physical_sharp
#print axioms evalVectorContinuousRepresentative_conj
#print axioms evalVectorLeftTrace_conj
#print axioms evalVectorLeftTrace_zero_im
end WeilHilbertBeforeContact
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
