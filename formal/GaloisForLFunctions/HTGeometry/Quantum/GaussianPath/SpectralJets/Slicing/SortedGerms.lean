import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Slicing.RealDerivatives
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.ComplexChart

/-! # Real sorted eigenvalues and holomorphic root germs -/

open Matrix MvPolynomial Filter Topology Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {n D : ℕ}

/-- At a simple Hermitian spectrum a continuous characteristic root agrees
locally on the real slice with one fixed sorted eigenvalue. -/
theorem branch_sorted_germ {P : Fin n → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian)
    {x : Fin n → ℝ} (hi : Function.Injective (sortedEnsembleSpectrum hP x))
    {f : (Fin n → ℂ) → ℂ} (hf : ContinuousAt f (realEmbed x))
    (hz : ∀ᶠ z in 𝓝 (realEmbed x), matrixCharpolyRelation (∑ i, z i • P i,f z) = 0) :
    ∃ j, (fun y => f (realEmbed y)) =ᶠ[𝓝 x] fun y => (sortedEnsembleSpectrum hP y j : ℂ) := by
  let e (j : Fin D) (y : Fin n → ℝ) : ℂ := sortedEnsembleSpectrum hP y j
  have hmem : ∀ᶠ y in 𝓝 x, ∃ i, f (realEmbed y) = e i y := by
    filter_upwards [(continuous_realEmbed.tendsto x) hz] with y hy
    obtain ⟨l,hl⟩ := exists_eigenvalue_eq_of_charpolyDet_eq_zero (isHermitian_spectralEnsembleMatrix hP y) hy
    obtain ⟨s,hs⟩ := exists_sortedTuple_eq (isHermitian_spectralEnsembleMatrix hP y).eigenvalues l
    exact ⟨s,hl.trans (congrArg Complex.ofReal hs)⟩
  obtain ⟨j,hj⟩ := hmem.self_of_nhds
  have hsep (i : Fin D) : ∀ᶠ y in 𝓝 x, f (realEmbed y) = e i y → i=j := by
    by_cases hij : i=j
    · exact .of_forall fun _ _ => hij
    · have he : ContinuousAt (e i) x := Complex.continuous_ofReal.continuousAt.comp
        (((continuous_apply i).comp (continuous_sortedEnsembleSpectrum hP)).continuousAt)
      have hn : f (realEmbed x)-e i x ≠ 0 := by
        rw [hj]
        exact sub_ne_zero.mpr fun h => hij (hi (Complex.ofReal_injective h.symm))
      have hdiff := ((hf.comp continuous_realEmbed.continuousAt).sub he).eventually_ne hn
      filter_upwards [hdiff] with y hy heq
      exact (hy (sub_eq_zero.mpr heq)).elim
  refine ⟨j,?_⟩
  filter_upwards [hmem,eventually_all.mpr hsep] with y ⟨i,hi'⟩ hy
  rwa [← hy i hi']

/-- Each real mixed derivative is analytic where the real function is the
restriction of a holomorphic germ. -/
theorem analyticAt_realMixed_of_germ {x : Fin n → ℝ} {f : (Fin n → ℂ) → ℂ} {g : (Fin n → ℝ) → ℝ}
    (hf : AnalyticAt ℂ f (realEmbed x)) (hg : (fun y => f (realEmbed y)) =ᶠ[𝓝 x] fun y => (g y : ℂ))
    (w : List (Fin n)) : AnalyticAt ℝ (realMixed w g) x := by
  apply (analyticAt_re_comp_realEmbed (mixed_analyticAt hf w)).congr
  filter_upwards [(continuous_realEmbed.tendsto x) hf.eventually_analyticAt,hg.eventually_nhds] with y hy hgy
  exact congrArg Complex.re (mixed_of_real_germ hy hgy w)

/-- A root on a simple analytic germ has the polynomial quotient expression
for every mixed derivative throughout a neighborhood of its base point. -/
theorem eventually_mixed_quotient (p : MvPolynomial (Option (Fin n)) ℂ)
    {x : Fin n → ℂ} {f : (Fin n → ℂ) → ℂ} (hf : AnalyticAt ℂ f x)
    (hz : ∀ᶠ y in 𝓝 x, onRoot p f y = 0) (hs : onRoot (pderiv none p) f x ≠ 0)
    (w : List (Fin n)) :
    ∀ᶠ y in 𝓝 x, mixed w f y = onRoot (numerator p w) f y / onRoot (pderiv none p) f y^(2*w.length) := by
  have hc : ContinuousAt (onRoot (pderiv none p) f) x := by
    apply (contDiff_mvPolynomial_eval _).continuous.continuousAt.comp
    apply continuousAt_pi.mpr
    intro o
    cases o with
    | none => exact hf.continuousAt
    | some i => exact (continuous_apply i).continuousAt
  obtain ⟨U,hU,ho,hx⟩ := eventually_nhds_iff.mp ((hf.eventually_analyticAt.and hz).and (hc.eventually_ne hs))
  filter_upwards [ho.mem_nhds hx] with y hy
  have hb := onRoot_numerator p f ho (fun z h => (hU z h).1.1.differentiableAt.differentiableWithinAt)
    (fun z h => (hU z h).1.2) (fun z h => (hU z h).2) w y hy
  exact (eq_div_iff (pow_ne_zero _ (hU y hy).2)).mpr (by rw [hb,mul_comm])

#print axioms branch_sorted_germ
#print axioms eventually_mixed_quotient
end
end GaloisForLFunctions.HTGeometry.SpectralJets
