import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointCausalLaplace

/-! Exponentially damped causal kernels and their exact shifted transforms. -/
namespace RHTower.D4BMJointWave
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def waveDampedKernel (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) (c t : ℝ) : H :=
  expRay c t • waveCausalKernel J hJ F δ hδ t

theorem waveDampedKernel_memLp (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) (c : ℝ) (hc : 2*δ ≤ c) :
    MemLp (waveDampedKernel J hJ F δ hδ c) 2 (volume.restrict (Ioi (0:ℝ))) := by
  let Q := waveLinePreimage J hJ F δ hδ δ hδ
  have hQ := (Lp.memLp Q).restrict (Ioi (0:ℝ))
  have hm : MemLp (fun t => expRay ((c:ℂ)-2*δ) t • Q t) 2
      (volume.restrict (Ioi (0:ℝ))) := by
    apply MemLp.mono' hQ.norm
      ((continuous_expRay _).aestronglyMeasurable.smul hQ.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have he : ‖expRay ((c:ℂ)-2*δ) t‖ ≤ 1 := by
      rw [norm_expRay]
      apply Real.exp_le_one_iff.mpr
      have hr : ((c:ℂ)-2*δ).re = c-2*δ := by simp
      rw [hr]
      have ht' : 0 < t := ht
      nlinarith
    change ‖expRay ((c:ℂ)-2*δ) t • Q t‖ ≤ ‖Q t‖
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans_eq (one_mul _)
  change MemLp (fun t => expRay c t • waveCausalKernel J hJ F δ hδ t) 2
    (volume.restrict (Ioi (0:ℝ)))
  simpa only [waveCausalKernel_integrand] using hm

private theorem expRay_mul (w z : ℂ) (t : ℝ) :
    expRay w t * expRay z t = expRay (w+z) t := by
  simp only [expRay,← Complex.exp_add]
  congr 1
  ring

theorem waveDampedKernel_laplace_probe (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) (c : ℝ) (hc : 2*δ ≤ c)
    (ℓ : H →L[ℂ] ℂ) (w : ℂ) (hw : 0 < w.re) :
    laplaceRay (fun t => ℓ (waveDampedKernel J hJ F δ hδ c t)) w =
      ℓ (waveSpatialResolvent J (w+c) F) := by
  have hcw : 2*δ < (w+(c:ℂ)).re := by
    simp only [Complex.add_re,Complex.ofReal_re]
    linarith
  calc
    _ = ∫ t in Ioi (0:ℝ), ℓ (expRay (w+c) t • waveCausalKernel J hJ F δ hδ t) := by
      unfold laplaceRay
      apply integral_congr_ae
      apply Eventually.of_forall
      intro t
      simp only [waveDampedKernel,map_smul,smul_eq_mul]
      rw [← expRay_mul]
      ring
    _ = ℓ (∫ t in Ioi (0:ℝ), expRay (w+c) t • waveCausalKernel J hJ F δ hδ t) :=
      ℓ.integral_comp_comm (waveCausalKernel_integrable J hJ F δ hδ (w+c) hcw)
    _ = _ := congrArg ℓ (waveCausalKernel_laplace J hJ F δ hδ (w+c) hcw)

end
end RHTower.D4BMJointWave
