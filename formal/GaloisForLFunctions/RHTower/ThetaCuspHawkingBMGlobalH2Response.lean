import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGlobalCutoffLaplacian

/-!
The actual global response has local H¹, H², L² Laplacian and Fourier-L¹ regularity across all modular seams.
-/

open MeasureTheory TemperedDistribution
open scoped ContDiff ENNReal SchwartzMap LineDeriv Laplacian
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse GaloisForLFunctions.HTGeometry
noncomputable section

private theorem global_local_sobolev_zero (g : PlanarChartTest) (u : Space) :
    MemSobolev 0 2 (g.localDistribution u) :=
  memSobolev_zero_iff.mpr ⟨g.localVector u,rfl⟩

theorem global_sum_sobolev {s : ℝ} {f : Fin 2 → 𝓢'(ℂ,ℂ)}
    (hf : ∀ i, MemSobolev s 2 (f i)) : MemSobolev s 2 (∑ i, f i) := by
  simpa only [Fin.sum_univ_two] using (hf 0).add (hf 1)

private theorem global_response_regularity_step (q : XiZeroCopy) (minusBranch : Bool)
    (s : ℝ) (hs : s ≤ 1)
    (hh : ∀ g : PlanarChartTest, MemSobolev s 2
      (g.localDistribution (embedding (weakResponse q minusBranch)))) (g : PlanarChartTest) :
    MemSobolev (s+1) 2 (g.localDistribution (embedding (weakResponse q minusBranch))) := by
  have hscalar (a : PlanarChartTest) := (hh a).mono (show s-1 ≤ s by linarith)
  have hsource (a : PlanarChartTest) :=
    (global_local_sobolev_zero a (forcingVector q minusBranch)).mono (show s-1 ≤ 0 by linarith)
  have hl : MemSobolev (s-1) 2
      (Δ (g.localDistribution (embedding (weakResponse q minusBranch)))) := by
    rw [full_response_global_cutoff_laplacian]
    have hD := global_sum_sobolev (fun i =>
      (hh (g.derivative (direction i))).lineDerivOp (m := direction i))
    exact (((hD.smul (2:ℂ)).sub (hscalar g.laplacianTest)).add
      ((hscalar (g.divHeight 2)).smul (parameter q minusBranch))).add (hsource (g.divHeight 2))
  have hout := planar_sobolev_gain_two (hscalar g) hl
  convert hout using 1
  ring

/-- The actual global response has one Sobolev derivative on every compact chart,
including charts crossing either modular seam. All cutoff terms are retained. -/
theorem full_response_global_local_H1 (q : XiZeroCopy) (minusBranch : Bool) (g : PlanarChartTest) :
    MemSobolev 1 2 (g.localDistribution (embedding (weakResponse q minusBranch))) := by
  simpa only [zero_add] using global_response_regularity_step q minusBranch 0 (by norm_num)
    (fun a => global_local_sobolev_zero a _) g

/-- The actual global response has two Sobolev derivatives on every compact chart.
The second elliptic gain uses the original full forcing and no lifted-frame hypothesis. -/
theorem full_response_global_local_H2 (q : XiZeroCopy) (minusBranch : Bool) (g : PlanarChartTest) :
    MemSobolev 2 2 (g.localDistribution (embedding (weakResponse q minusBranch))) := by
  have h := global_response_regularity_step q minusBranch 1 le_rfl
    (full_response_global_local_H1 q minusBranch) g
  norm_num at h ⊢
  exact h

/-- Every localized actual global response has an L² distributional Laplacian. -/
theorem full_response_global_local_laplacian_L2 (q : XiZeroCopy) (minusBranch : Bool)
    (g : PlanarChartTest) :
    ∃ v : Lp ℂ 2 (volume : Measure ℂ),
      Δ (g.localDistribution (embedding (weakResponse q minusBranch))) = (v : 𝓢'(ℂ,ℂ)) := by
  apply memSobolev_zero_iff.mp
  have h := (full_response_global_local_H2 q minusBranch g).laplacian
  simpa only [sub_self] using h

/-- The actual response has an integrable localized Fourier transform on every
chart, including charts crossing side identifications and elliptic fixed points. -/
theorem full_response_global_local_fourier_L1 (q : XiZeroCopy) (minusBranch : Bool)
    (g : PlanarChartTest) :
    ∃ v : Lp ℂ 1 (volume : Measure ℂ), FourierTransform.fourier
      (g.localDistribution (embedding (weakResponse q minusBranch))) = (v : 𝓢'(ℂ,ℂ)) :=
  (full_response_global_local_H2 q minusBranch g).fourier_memL1 (by norm_num)

end
end RHTower.D4BMModularCore
