import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceMomentSpatial
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceWronskianContinuation

/-! The original continued response satisfies the literal forced radial master as a QNM germ. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The first spatial jet of the actual continued response. -/
def continuedResponseFirst (s chi a J K : ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  normalizableFirst w chi b*continuedHorizonMoment s chi a J K b w+
    horizonFirst w chi b*continuedOuterMoment s chi a J K b w

/-- The second jet retains the moving-endpoint source jump with its full normalization. -/
def continuedResponseSecond (s chi a J K : ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  normalizableSecond w chi b*continuedHorizonMoment s chi a J K b w+
    horizonSecond w chi b*continuedOuterMoment s chi a J K b w+
      (normalizableFirst w chi b*horizon w chi b-horizonFirst w chi b*normalizable w chi b)*
        continuedSourceProfile s a J K w b/(-connection w chi)

/-- Both continued Green jets are actual spatial derivatives in the full first-subtraction strip. -/
theorem continuedResponse_hasDerivAt (s chi a J K w : ℂ) (hw : w.im ≠ 0)
    (hwre : -2 < w.re) {b : ℝ} (hb : b ∈ Ioo 0 1) :
    HasDerivAt (fun t => continuedResponse s chi a J K t w) (continuedResponseFirst s chi a J K b w) b ∧
    HasDerivAt (fun t => continuedResponseFirst s chi a J K t w) (continuedResponseSecond s chi a J K b w) b := by
  have hA := continuedHorizonMoment_hasDerivAt s chi a J K w hw hwre hb
  have hB := continuedOuterMoment_hasDerivAt s chi a J K w hb
  obtain ⟨hH,hH1⟩ := horizon_derivatives_continued (w := w) (chi := chi) hb
  obtain ⟨hN,hN1⟩ := normalizable_derivatives_continued (w := w) (chi := chi) hb
  constructor
  · convert! (hN.mul hA).add (hH.mul hB) using 1
    dsimp [continuedResponseFirst]
    ring
  · convert! (hN1.mul hA).add (hH1.mul hB) using 1
    dsimp [continuedResponseSecond]
    ring

/-- Actual first and second derivatives agree with the displayed continued jets. -/
theorem continuedResponse_deriv_eq (s chi a J K w : ℂ) (hw : w.im ≠ 0)
    (hwre : -2 < w.re) {b : ℝ} (hb : b ∈ Ioo 0 1) :
    deriv (fun t => continuedResponse s chi a J K t w) b = continuedResponseFirst s chi a J K b w ∧
    deriv (deriv (fun t => continuedResponse s chi a J K t w)) b = continuedResponseSecond s chi a J K b w := by
  have hd := continuedResponse_hasDerivAt s chi a J K w hw hwre hb
  refine ⟨hd.1.deriv,?_⟩
  apply HasDerivAt.deriv
  apply hd.2.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hb] with t ht
  exact (continuedResponse_hasDerivAt s chi a J K w hw hwre ht).1.deriv

/-- Off the actual connection zeros, the continued response solves the original radial master
with the literal continued source and actual derivatives. -/
theorem continuedResponse_original_equation (s chi a J K w : ℂ) (hw : w.im ≠ 0)
    (hwre : -2 < w.re) (hc : connection w chi ≠ 0) {b : ℝ} (hb : b ∈ Ioo 0 1) :
    D4BMPhysicalMaster.radialJet (Complex.I*w) chi b
      (continuedResponse s chi a J K b w)
      (deriv (fun t => continuedResponse s chi a J K t w) b)
      (deriv (deriv (fun t => continuedResponse s chi a J K t w)) b) =
      (Real.sqrt (1-b):ℂ)*continuedSourceProfile s a J K w b/2 := by
  obtain ⟨hd,hdd⟩ := continuedResponse_deriv_eq s chi a J K w hw hwre hb
  rw [hd,hdd]
  have hH := horizon_equation_continued (chi := chi) hw hb
  have hN := normalizable_equation_continued (w := w) (chi := chi) hb
  have hW := wronskian_eq_continued w chi hw hb
  have hs : (Real.sqrt (1-b):ℂ)^2=1-(b:ℂ) := by
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hb.2.le)
  dsimp [wronskian,integratingFactor] at hW
  rw [power_half_eq_sqrt (sub_nonneg.mpr hb.2.le)] at hW
  dsimp [D4BMPhysicalMaster.radialJet] at hH hN
  calc
    _ = (b:ℂ)*(1-b)*(normalizableFirst w chi b*horizon w chi b-
        horizonFirst w chi b*normalizable w chi b)*continuedSourceProfile s a J K w b/(-connection w chi) := by
      dsimp [continuedResponse,continuedResponseFirst,continuedResponseSecond,D4BMPhysicalMaster.radialJet]
      linear_combination (continuedHorizonMoment s chi a J K b w)*hN+
        (continuedOuterMoment s chi a J K b w)*hH
    _ = (Real.sqrt (1-b):ℂ)*((b:ℂ)*(Real.sqrt (1-b):ℂ)*
        (horizon w chi b*normalizableFirst w chi b-horizonFirst w chi b*normalizable w chi b))*
          continuedSourceProfile s a J K w b/(-connection w chi) := by
      rw [← hs]
      ring
    _ = (Real.sqrt (1-b):ℂ)*(-connection w chi/2)*continuedSourceProfile s a J K w b/(-connection w chi) := by rw [hW]
    _ = _ := by field_simp [hc]

/-- The original forced radial equation holds as a punctured frequency germ, including at
connection zeros. No nonresonance, endpoint-integrability or assigned-jet premise is supplied. -/
theorem continuedResponse_original_equation_germ (s chi a J K w : ℂ) (hw : w.im ≠ 0)
    (hwre : -2 < w.re) {b : ℝ} (hb : b ∈ Ioo 0 1) :
    ∀ᶠ u in 𝓝[≠] w, D4BMPhysicalMaster.radialJet (Complex.I*u) chi b
      (continuedResponse s chi a J K b u)
      (deriv (fun t => continuedResponse s chi a J K t u) b)
      (deriv (deriv (fun t => continuedResponse s chi a J K t u)) b) =
      (Real.sqrt (1-b):ℂ)*continuedSourceProfile s a J K u b/2 := by
  have hi := (Complex.continuous_im.continuousAt.eventually_ne hw).filter_mono
    (show 𝓝[≠] w ≤ 𝓝 w from inf_le_left)
  have hr := (Complex.continuous_re.continuousAt.eventually_const_lt hwre).filter_mono
    (show 𝓝[≠] w ≤ 𝓝 w from inf_le_left)
  filter_upwards [hi,hr,connection_eventually_ne_zero w chi hw] with u hui hur huc
  exact continuedResponse_original_equation s chi a J K u hui hur huc hb

/-- At every Xi fundamental QNM, the actual continued native response retains its original
forced radial equation as a germ. This does not identify a full joint physical left residue. -/
theorem continuedResponse_allXi_fundamental_original_equation (q : XiZeroCopy) (s a J K : ℂ) :
    ∀ w ∈ ({-Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q),
      -Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)} : Set ℂ),
    ∀ b ∈ Ioo (0:ℝ) 1, ∀ᶠ u in 𝓝[≠] w,
      D4BMPhysicalMaster.radialJet (Complex.I*u)
        (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q)) b
        (continuedResponse s (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q)) a J K b u)
        (deriv (fun t => continuedResponse s (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q)) a J K t u) b)
        (deriv (deriv (fun t => continuedResponse s (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q)) a J K t u)) b) =
        (Real.sqrt (1-b):ℂ)*continuedSourceProfile s a J K u b/2 := by
  have hq := thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q
  have hs := abs_im_xiSpectralPoint_lt_half q
  rw [abs_lt] at hs
  have hstrip : ∀ w ∈ ({-Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q),
      -Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)} : Set ℂ),
      w.im ≠ 0 ∧ -2 < w.re := by
    intro w hw
    simp only [mem_insert_iff,mem_singleton_iff] at hw
    rcases hw with rfl | rfl <;>
      simp only [thetaCuspHawkingTopologicalBlackHoleQNMPlus,thetaCuspHawkingTopologicalBlackHoleQNMMinus,
        thetaCuspHawkingTopologicalBlackHoleAngularMomentum,thetaCuspHawkingTopologicalBlackHoleConformalDecay,
        Complex.mul_im,Complex.mul_re,Complex.sub_re,Complex.sub_im,Complex.neg_re,Complex.neg_im,
        Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,Complex.add_re,Complex.add_im,Complex.div_re,Complex.div_im]
    all_goals norm_num
    · exact ⟨hq,by linarith [hs.1]⟩
    · exact ⟨hq,by linarith [hs.2]⟩
  intro w hw b hb
  exact continuedResponse_original_equation_germ s _ a J K w (hstrip w hw).1 (hstrip w hw).2 hb

end
end RHTower.D4BMLaplaceRadial
