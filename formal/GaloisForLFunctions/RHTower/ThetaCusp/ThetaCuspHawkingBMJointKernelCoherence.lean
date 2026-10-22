import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointKernelDamping
import GaloisForLFunctions.HTGeometry.LaplaceRayInjective

/-! Fourier-line choices yield one causal kernel by injectivity of the actual Laplace transform. -/
namespace RHTower.D4BMJointWave
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Independent positive damping choices give the same actual kernel on the positive time ray. -/
theorem waveCausalKernel_independent_on_ray (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    waveCausalKernel J hJ F δ hδ =ᵐ[volume.restrict (Ioi (0:ℝ))]
      waveCausalKernel J hJ F ε hε := by
  let c : ℝ := 2*δ+2*ε
  have hcδ : 2*δ ≤ c := by dsimp [c]; linarith
  have hcε : 2*ε ≤ c := by dsimp [c]; linarith
  let A := waveDampedKernel J hJ F δ hδ c
  let B := waveDampedKernel J hJ F ε hε c
  have hA : MemLp A 2 (volume.restrict (Ioi (0:ℝ))) := waveDampedKernel_memLp J hJ F δ hδ c hcδ
  have hB : MemLp B 2 (volume.restrict (Ioi (0:ℝ))) := waveDampedKernel_memLp J hJ F ε hε c hcε
  have hprobe : ∀ v : H, ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), inner ℂ v (A t-B t) = 0 := by
    intro v
    let ℓ : H →L[ℂ] ℂ := innerSL ℂ v
    have ha := ℓ.comp_memLp' hA
    have hb := ℓ.comp_memLp' hB
    have hz := ae_eq_zero_of_laplaceRay_eq_zero (ha.sub hb) (fun w hw => by
      change (∫ t in Ioi (0:ℝ), (ℓ (A t)-ℓ (B t))*expRay w t) = 0
      simp_rw [sub_mul]
      have hsub := integral_sub (integrableOn_laplaceRay ha hw) (integrableOn_laplaceRay hb hw)
      simp only [Function.comp_def] at hsub
      rw [hsub]
      change laplaceRay (fun t => ℓ (waveDampedKernel J hJ F δ hδ c t)) w -
        laplaceRay (fun t => ℓ (waveDampedKernel J hJ F ε hε c t)) w = 0
      rw [waveDampedKernel_laplace_probe J hJ F δ hδ c hcδ ℓ w hw,
        waveDampedKernel_laplace_probe J hJ F ε hε c hcε ℓ w hw,sub_self])
    filter_upwards [hz] with t ht
    rw [inner_sub_right]
    exact ht
  have hz := bochnerL2_ae_zero_on_of_inner_probes (fun t => A t-B t) (hA.sub hB)
    Set.univ MeasurableSet.univ (fun v => (hprobe v).mono (fun t ht _ => ht))
  filter_upwards [hz] with t ht
  have he := ht (Set.mem_univ t)
  change expRay c t • waveCausalKernel J hJ F δ hδ t -
    expRay c t • waveCausalKernel J hJ F ε hε t = 0 at he
  exact smul_right_injective H (show expRay (c:ℂ) t ≠ 0 from Complex.exp_ne_zero _)
    (sub_eq_zero.mp he)

/-- Causal support completes the independence statement on the whole real time axis. -/
theorem waveCausalKernel_independent (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    waveCausalKernel J hJ F δ hδ =ᵐ[volume] waveCausalKernel J hJ F ε hε := by
  have hp := (ae_restrict_iff' measurableSet_Ioi).mp
    (waveCausalKernel_independent_on_ray J hJ F δ ε hδ hε)
  have hn : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0:ℝ))] with t ht
    simpa using ht
  filter_upwards [hp,hn,waveCausalKernel_support J hJ F δ hδ,
    waveCausalKernel_support J hJ F ε hε] with t ht h0 hδt hεt
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · rw [hδt hneg,hεt hneg]
  · exact ht hpos

/-- The fixed kernel admits every strictly positive exponential damping. -/
theorem waveDampedKernel_memLp_pos (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) (c : ℝ) (hc : 0 < c) :
    MemLp (waveDampedKernel J hJ F δ hδ c) 2 (volume.restrict (Ioi (0:ℝ))) := by
  have he : 0 < c/4 := by positivity
  have hm := waveDampedKernel_memLp J hJ F (c/4) he c (by linarith)
  apply hm.ae_eq
  filter_upwards [waveCausalKernel_independent_on_ray J hJ F (c/4) δ he hδ] with t ht
  exact congrArg (fun u : H => expRay c t • u) ht

end
end RHTower.D4BMJointWave
