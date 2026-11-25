import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.LineActions
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.LocalZeros
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.RatioDirections

/-! # Almost-sure exclusion of exponential relations between normalized energies -/

open Set Filter Matrix Topology MeasureTheory Metric Finset
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
noncomputable section

private theorem action_sub {I : Type*} [Fintype I] (u v E : I → ℝ) (i j : I) :
    normalizedAction (fun l => u l-v l) E i j=normalizedAction u E i j-normalizedAction v E i j := by
  simp only [normalizedAction,sub_mul,sum_sub_distrib,sub_div]

/-- For balanced spectral weights whose differences meet the complement
of the closing pair, every fixed nontrivial exponential sum of their
normalized actions vanishes only on a null set of simple couplings. -/
theorem normalized_exponential_zero_null {n D : ℕ} {P : Fin n → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ l, (P l).IsHermitian) (hs : SpectrumEscapesRealRelations (range (spectralEnsembleMatrix P)))
    (i j : Fin D) (hij : i≠j) {L : Type*} [Fintype L] (w : L → Fin D → ℝ)
    (hb : ∀ l, ∑ t, w l t=0) (hout : ∀ u v, u≠v → ∃ t, t≠i ∧ t≠j ∧ w u t≠w v t)
    {χ : ℂ} (hχ : χ≠0) (a : L → ℂ) (ha : ∃ u, a u≠0) :
    volume {x ∈ simpleEnsembleLocus hP | ∑ u, a u*Complex.exp
      (χ*(normalizedAction (w u) (sortedEnsembleSpectrum hP x) i j:ℝ))=0}=0 := by
  classical
  let E := sortedEnsembleSpectrum hP
  let U := simpleEnsembleLocus hP
  let F (x : Fin n → ℝ) := ∑ u, a u*Complex.exp (χ*(normalizedAction (w u) (E x) i j:ℝ))
  have hF : AnalyticOnNhd ℝ F U := by
    intro x hx
    apply Finset.analyticAt_fun_sum
    intro u _
    have hE := analyticAt_sortedEnsembleSpectrum hP hx
    have hA : AnalyticAt ℝ (fun y => normalizedAction (w u) (E y) i j) x :=
      (Finset.analyticAt_fun_sum _ fun l _ => analyticAt_const.mul (hE l)).div ((hE i).sub (hE j))
        (sub_ne_zero.mpr ((injective_sortedEnsembleSpectrum hP hx).ne hij))
    have hc : AnalyticAt ℝ (fun y => χ*(normalizedAction (w u) (E y) i j:ℝ)) x :=
      analyticAt_const.mul ((Complex.ofRealCLM.analyticAt _).comp hA)
    exact analyticAt_const.mul (analyticAt_cexp.restrictScalars.comp hc)
  apply analytic_zero_null (isOpen_simpleEnsembleLocus hP) hF
  intro x hx r hr hsub
  let J := {p : L × L // p.1≠p.2}
  let W (p : J) (t : Fin D) := w p.val.1 t-w p.val.2 t
  have hb' (p : J) : ∑ t, W p t=0 := by simp only [W,sum_sub_distrib,hb,sub_zero]
  have ho (p : J) : ∃ t, t≠i ∧ t≠j ∧ W p t≠0 := by
    obtain ⟨t,h1,h2,h3⟩ := hout _ _ p.property
    exact ⟨t,h1,h2,sub_ne_zero.mpr h3⟩
  obtain ⟨y,hy,hdir⟩ := exists_distinct_ratios hP hs hij W hb' ho
    (fun p => normalizedAction (W p) (E x) i j) isOpen_ball ⟨x,mem_ball_self hr,hx⟩
  have hseg (t : ℝ) (ht : t∈Set.Icc 0 1) : x+t • (y-x)∈U :=
    hsub ((convex_ball x r).add_smul_sub_mem (mem_ball_self hr) hy.1 ht)
  have hd (u v : L) (huv : u≠v) :
      normalizedAction (w u) (E x) i j-normalizedAction (w v) (E x) i j ≠
      normalizedAction (w u) (E y) i j-normalizedAction (w v) (E y) i j := by
    let p : J := ⟨(u,v),huv⟩
    have hv : normalizedAction (W p) (E y) i j ≠ normalizedAction (W p) (E x) i j := hdir p
    simpa only [W,p,action_sub] using hv.symm
  obtain ⟨f,hf,halg,hreal,hneq⟩ := line_actions hP x y i j hij w hχ hseg hd
  by_contra! hz
  have ht : Tendsto (fun t : ℝ => x+t • (y-x)) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x+t • (y-x)) := continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul,add_zero] using hc.tendsto 0
  have he : ∀ᶠ t : ℝ in 𝓝 0, ∑ u, a u*Complex.exp (f u t)=0 := by
    filter_upwards [hreal,ht (ball_mem_nhds x hr)] with t ht' hball
    simpa only [ht',F] using hz _ hball
  obtain ⟨u,hu⟩ := ha
  exact hu (exp_sum_real_slice f hf halg hneq a he u)

#print axioms normalized_exponential_zero_null
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
