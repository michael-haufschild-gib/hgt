import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.PencilRoots
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Slicing.SortedGerms

/-! # Sorted physical energies restrict to algebraic germs on affine coupling lines -/

open Matrix Filter Topology Polynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
noncomputable section

/-- Each sorted energy on a real coupling line through a simple spectrum
extends locally to a holomorphic germ algebraic over the rational
functions of the complexified line parameter. -/
theorem line_energy_germ {n D : ℕ} {P : Fin n → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (x d : Fin n → ℝ)
    (hx : Function.Injective (isHermitian_spectralEnsembleMatrix hP x).eigenvalues) (j : Fin D) :
    ∃ f : ℂ → ℂ, ∃ hf : AnalyticAt ℂ f 0,
      IsAlgebraic (RatFunc ℂ) (ofMero f hf.meromorphicAt) ∧
      (fun t : ℝ => f t) =ᶠ[𝓝 0] fun t => (sortedEnsembleSpectrum hP (fun a => x a+t*d a) j : ℂ) := by
  obtain ⟨F,ha,h0,hr⟩ := exists_analyticBranches_spectralEnsemble hP x hx
  let i := Tuple.sort (isHermitian_spectralEnsembleMatrix hP x).eigenvalues j
  obtain ⟨l,hl⟩ := branch_sorted_germ hP (injective_sortedTuple hx) (ha i).continuousAt (hr i)
  have he : l=j := (injective_sortedTuple hx) (Complex.ofReal_injective ((hl.self_of_nhds).symm.trans (h0 i)))
  subst l
  let line (z : ℂ) (a : Fin n) := (x a:ℂ)+z*(d a:ℂ)
  let rline (t : ℝ) (a : Fin n) := x a+t*d a
  have l0 : line 0=realEmbed x := by funext a; simp [line,realEmbed]
  have r0 : rline 0=x := by funext a; simp [rline]
  have hline : AnalyticAt ℂ line 0 := by
    apply AnalyticAt.pi
    intro a
    exact analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  have hf : AnalyticAt ℂ (fun z => F i (line z)) 0 :=
    (l0.symm ▸ ha i).comp hline
  refine ⟨_,hf,?_,?_⟩
  · let M : Matrix (Fin D) (Fin D) ℂ[X] := of fun u v =>
      ∑ a, (C (x a:ℂ)+X*C (d a:ℂ))*C (P a u v)
    have hm (z : ℂ) : M.map (Polynomial.evalRingHom z)=∑ a, line z a • P a := by
      ext u v
      simp [M,line,Matrix.map_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
    apply algebraic_pencil_root M hf.meromorphicAt
    have ht : Tendsto line (𝓝[≠] (0:ℂ)) (𝓝 (realEmbed x)) :=
      l0 ▸ hline.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    filter_upwards [ht (hr i)] with z hz
    rw [hm]
    exact hz
  · have hc : Continuous rline := continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const)
    have ht : Tendsto rline (𝓝 0) (𝓝 x) := r0 ▸ hc.tendsto 0
    filter_upwards [ht hl] with t hh
    have heq : line (t:ℂ)=realEmbed (rline t) := by funext a; simp [line,rline,realEmbed]
    rw [heq]
    exact hh

#print axioms line_energy_germ
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
