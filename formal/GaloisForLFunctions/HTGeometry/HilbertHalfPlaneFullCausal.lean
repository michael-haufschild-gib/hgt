import GaloisForLFunctions.HTGeometry.HilbertHalfPlaneCausal

/-! Every positive Fourier line represents the same original Hilbert-valued causal datum. -/
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory Set Filter Topology FourierTransform
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace CauchyBoundedHilbertMap
variable (F : CauchyBoundedHilbertMap H)

private def linePreimageAt (s : ℝ) (hs : 0 < s) : Lp H 2 (volume : Measure ℝ) :=
  𝓕⁻ (F.lineVector s hs)

private theorem linePreimageAt_probe_ae (s : ℝ) (hs : 0 < s) (L : H →L[ℂ] ℂ) :
    (fun t => L (F.linePreimageAt s hs t)) =ᵐ[volume]
      (hardyPreimage (fun w => L (F.value w)) s ((F.probe_hardy L).memLp s hs) : ℝ → ℂ) := by
  have h : L.compLp (F.linePreimageAt s hs) =
      hardyPreimage (fun w => L (F.value w)) s ((F.probe_hardy L).memLp s hs) := by
    unfold linePreimageAt hardyPreimage
    rw [compLp_fourierInv]
    congr 1
  have he := L.coeFn_compLp (F.linePreimageAt s hs)
  rw [h] at he
  exact Filter.EventuallyEq.symm he

omit [CompleteSpace H] in
private theorem damp_memLp {f : ℝ → H} (hf : MemLp f 2 (volume.restrict (Ioi (0:ℝ))))
    (s : ℝ) (hs : 0 ≤ s) :
    MemLp (fun t => expRay (s:ℂ) t • f t) 2 (volume.restrict (Ioi (0:ℝ))) := by
  apply MemLp.mono' hf.norm
    ((continuous_expRay _).aestronglyMeasurable.smul hf.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖expRay (s:ℂ) t • f t‖ ≤ ‖f t‖
  rw [norm_smul]
  have hb : ‖expRay (s:ℂ) t‖ ≤ 1 := by
    rw [norm_expRay,Complex.ofReal_re]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hs ht.le))
  exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq (one_mul _)

private theorem expRay_real (s t : ℝ) : expRay (s:ℂ) t = (Real.exp (-(s*t)):ℂ) := by
  simp [expRay,Complex.ofReal_exp]

/-- The original causal vector admits every strictly positive exponential damping in L². -/
theorem causalDatum_memLp_pos (s : ℝ) (hs : 0 < s) :
    MemLp (fun t => expRay (s:ℂ) t • F.causalDatum t) 2 (volume.restrict (Ioi (0:ℝ))) := by
  let Q := F.linePreimageAt s hs
  let A := fun t => expRay (s:ℂ) t • F.linePreimage t
  let B := fun t => expRay (1:ℂ) t • Q t
  have hA : MemLp A 2 (volume.restrict (Ioi (0:ℝ))) :=
    damp_memLp ((Lp.memLp F.linePreimage).restrict _) s hs.le
  have hB : MemLp B 2 (volume.restrict (Ioi (0:ℝ))) :=
    damp_memLp ((Lp.memLp Q).restrict _) 1 zero_le_one
  have hp (v : H) : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), inner ℂ v (A t-B t) = 0 := by
    let L : H →L[ℂ] ℂ := innerSL ℂ v
    filter_upwards [ae_restrict_of_ae (F.linePreimage_probe_ae L),
      ae_restrict_of_ae (F.linePreimageAt_probe_ae s hs L),
      ae_restrict_of_ae (hardyDatum_weight_ae (F.probe_hardy L) one_pos),
      ae_restrict_of_ae (hardyDatum_weight_ae (F.probe_hardy L) hs)] with t h1 hs' hw1 hws
    change L (A t-B t) = 0
    simp only [A,B,map_sub,map_smul,smul_eq_mul]
    change expRay (s:ℂ) t*L (F.linePreimage t)-expRay (1:ℂ) t*L (F.linePreimageAt s hs t)=0
    rw [h1,hs',← hw1,← hws]
    have he1 : expRay (1:ℂ) t = (Real.exp (-(1*t)):ℂ) := by
      simpa only [Complex.ofReal_one] using expRay_real (1:ℝ) t
    rw [expRay_real s t,he1]
    ring
  have hz := bochnerL2_ae_zero_on_of_inner_probes (fun t => A t-B t) (hA.sub hB)
    Set.univ MeasurableSet.univ (fun v => (hp v).mono (fun t ht _ => ht))
  apply ((Lp.memLp Q).restrict (Ioi (0:ℝ))).ae_eq
  filter_upwards [hz] with t ht
  have he := sub_eq_zero.mp (ht (Set.mem_univ t))
  have hd : expRay (1:ℂ) t • (expRay (s:ℂ) t • F.causalDatum t) = A t := by
    rw [smul_comm,F.causalDatum_damping]
  have h := smul_right_injective H (show expRay (1:ℂ) t ≠ 0 from Complex.exp_ne_zero _)
    (hd.trans he)
  exact h.symm

/-- The vector Laplace integral converges throughout the full open right half-plane. -/
theorem causalDatum_integrable_rightHalfPlane (w : ℂ) (hw : 0 < w.re) :
    IntegrableOn (fun t => expRay w t • F.causalDatum t) (Ioi (0:ℝ)) := by
  let s := w.re/2
  have hs : 0 < s := by dsimp only [s]; positivity
  have he : 0 < (w-(s:ℂ)).re := by simp only [Complex.sub_re,Complex.ofReal_re]; dsimp only [s]; linarith
  have hE := memLp_two_expRay_restrict he 0
  have hP := F.causalDatum_memLp_pos s hs
  have hi : IntegrableOn (fun t => expRay (w-(s:ℂ)) t • (expRay (s:ℂ) t • F.causalDatum t)) (Ioi (0:ℝ)) :=
    (hE.norm.integrable_mul hP.norm).mono' (hE.aestronglyMeasurable.smul hP.aestronglyMeasurable)
      (Eventually.of_forall (fun t => (norm_smul _ _).le))
  apply hi.congr
  filter_upwards [] with t
  simp only [smul_smul,expRay,← Complex.exp_add]
  congr 2
  ring

/-- Every positive-frequency transform recovers the given original analytic vector. -/
theorem causalDatum_laplace_rightHalfPlane (w : ℂ) (hw : 0 < w.re) :
    (∫ t in Ioi (0:ℝ), expRay w t • F.causalDatum t) = F.value w := by
  apply ext_inner_left ℂ
  intro v
  let L : H →L[ℂ] ℂ := innerSL ℂ v
  change L (∫ t in Ioi (0:ℝ), expRay w t • F.causalDatum t) = L (F.value w)
  calc
    _ = ∫ t in Ioi (0:ℝ), L (expRay w t • F.causalDatum t) :=
      (L.integral_comp_comm (F.causalDatum_integrable_rightHalfPlane w hw)).symm
    _ = laplaceRay (hardyDatum _ (F.probe_hardy L)) w := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (F.causalDatum_probe L)] with t ht
      rw [map_smul,smul_eq_mul,ht,mul_comm]
    _ = _ := (isHalfPlaneHardy_eq_laplaceRay (F.probe_hardy L) hw).symm

end CauchyBoundedHilbertMap
end
end GaloisForLFunctions.HTGeometry
