import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicTimes.PolynomialTime

/-! # Transfer of exclusion at algebraic times from rational to almost all couplings -/

open Set MeasureTheory Filter Topology Polynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicTimes
noncomputable section

/-- A real-analytic observable avoiding zero at every algebraic time
over rational couplings almost surely avoids zero at every time
algebraic over the field of the actual couplings. -/
theorem ae_algebraic_time_transfer {m : ℕ} {W : Set ((Fin m → ℝ) × ℝ)}
    (hW : IsOpen W) {G : (Fin m → ℝ) × ℝ → ℂ} (hG : AnalyticOnNhd ℝ G W)
    (hsep : ∀ (x : Fin m → ℚ) (t : ℝ), (fun i => (x i:ℝ),t)∈W →
      IsAlgebraic ℚ t → G (fun i => (x i:ℝ),t)≠0) :
    ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)), ∀ t, (x,t)∈W → IsAlgebraic (parameterField x) t → G (x,t)≠0 := by
  letI : Countable (Parameters m) := AddMonoidAlgebra.coeff_injective.countable
  let δ (q : (Parameters m)[X]) (u : (Fin m → ℝ) × ℝ) := timeValue q.derivative u
  let U (q : (Parameters m)[X]) := W ∩ {u | δ q u≠0}
  let B (q : (Parameters m)[X]) := {p∈U q | timeValue q p=0 ∧
    fderiv ℝ (timeValue q) p (0,1)≠0 ∧ G p=0}
  have hz (q : (Parameters m)[X]) : volume (Prod.fst '' B q)=0 := by
    have hc : Continuous (δ q) := continuous_iff_continuousAt.mpr fun u => (analytic_timeValue q.derivative u).continuousAt
    have ho : IsOpen (U q) := hW.inter (isOpen_ne_fun hc continuous_const)
    have hd : DenseRange (fun x : Fin m → ℚ => fun i => (x i:ℝ)) := DenseRange.piMap fun _ => Rat.denseRange_cast
    apply projection_simple_root_null ho (fun u _ => analytic_timeValue q u) (hG.mono inter_subset_left) hd
    rintro _ ⟨x,rfl⟩ t hu h
    exact hsep x t hu.1 (rational_specialization x t q h hu.2)
  filter_upwards [ae_all_iff.mpr fun q => measure_eq_zero_iff_ae_notMem.mp (hz q)] with x hx t hw ht hzero
  obtain ⟨q,hq,hd⟩ := exists_simple_time_equation x ht
  exact hx q ⟨(x,t),⟨hw,hd⟩,hq,(timeValue_vertical q x t).trans_ne hd,hzero,rfl⟩

#print axioms ae_algebraic_time_transfer
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicTimes
