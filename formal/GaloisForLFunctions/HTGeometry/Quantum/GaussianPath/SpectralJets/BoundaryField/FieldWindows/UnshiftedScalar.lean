import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.FieldWindows.InverseTime
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCouplings.TerminalField
import GaloisForLFunctions.HTGeometry.JointHardEventMeasurability

/-! # Inverse-time scalar fields at the original Gaussian draw -/
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.FieldWindows
open PrefixCouplings
noncomputable section

private def scalarWindow (k C : ℕ) (ε : ℝ) : Set PathPauliDisorder :=
  {ω | ∀ T : ℝ, (C:ℝ)^2 ≤ T → ∃ u : Icc (0:ℝ) 1,
    Metric.infDist (unitaryEvolution (boundaryHamiltonian ω k ((C:ℝ)/T*u)) T)
      (phaseCircuitMatrixImageAtMost (k+3) 0) ≤ ε}

private theorem field_closed_sublevel (k : ℕ) (T ε : ℝ) :
    IsClosed {p : PathPauliDisorder × ℝ |
      Metric.infDist (unitaryEvolution (boundaryHamiltonian p.1 k p.2) T)
        (phaseCircuitMatrixImageAtMost (k+3) 0) ≤ ε} := by
  let f := fun p : PathPauliDisorder × ℝ => (boundaryHamiltonian p.1 k p.2,T)
  have hf : Continuous f := (continuous_boundary_draw k).prodMk continuous_const
  have hu := (continuous_unitaryEvolution (d:=Fin (k+3) → Bool)).comp hf
  have hd := (Metric.continuous_infDist_pt (phaseCircuitMatrixImageAtMost (k+3) 0)).comp hu
  exact isClosed_le hd continuous_const

private theorem closed_scalarWindow (k C : ℕ) (ε : ℝ) : IsClosed (scalarWindow k C ε) := by
  let S (T : ℝ) := {p : PathPauliDisorder×Icc (0:ℝ) 1 |
    Metric.infDist (unitaryEvolution (boundaryHamiltonian p.1 k ((C:ℝ)/T*p.2)) T)
      (phaseCircuitMatrixImageAtMost (k+3) 0) ≤ ε}
  have hS (T : ℝ) : IsClosed (S T) := by
    let f := fun p : PathPauliDisorder × Icc (0:ℝ) 1 => (p.1,(C:ℝ)/T*(p.2:ℝ))
    have hv : Continuous (fun p : PathPauliDisorder × Icc (0:ℝ) 1 => (p.2:ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    have hf : Continuous f := continuous_fst.prodMk ((continuous_const (y:=(C:ℝ)/T)).mul hv)
    exact (field_closed_sublevel k T ε).preimage hf
  have he : scalarWindow k C ε=⋂ T : ℝ, ⋂ (_ : (C:ℝ)^2 ≤ T), Prod.fst '' (S T) := by
    ext ω
    simp only [scalarWindow,mem_setOf_eq,mem_iInter,mem_image]
    constructor
    · intro h T ht
      obtain ⟨u,hu⟩ := h T ht
      exact ⟨(ω,u),hu,rfl⟩
    · intro h T ht
      obtain ⟨⟨v,u⟩,hu,rfl⟩ := h T ht
      exact ⟨u,hu⟩
  rw [he]
  exact isClosed_iInter fun T => isClosed_iInter fun _ => isClosedMap_fst_of_compactSpace _ (hS T)

/-- For any prescribed physical tolerance the original unmodified Gaussian
draw is almost surely an inverse-time baseline on every prefix. -/
theorem gaussian_unshifted_inverse_scalar (ε : ℝ) (hε : ε∈Ioo (0:ℝ) (Real.sqrt 2)) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∃ C : ℕ, 1≤C ∧ ∀ T : ℝ, (C:ℝ)^2≤T →
      ∃ z∈Icc (0:ℝ) ((C:ℝ)/T), HasProjectiveCircuitApproximation (k+3) ε 0
        (unitaryEvolution (boundaryHamiltonian ω k z) T) := by
  apply ae_all_iff.mpr
  intro k
  let G := ⋃ C : ℕ, ⋃ (_ : 1≤C), scalarWindow k C ε
  have hG : MeasurableSet G := MeasurableSet.iUnion fun C => MeasurableSet.iUnion fun _ =>
    (closed_scalarWindow k C ε).measurableSet
  have ha : ∀ᵐ ω ∂pathPauliDisorderLaw, ω∈G := by
    apply ae_of_resampled_coordinate (gaussianReal 0 1) (terminalCoordinate k) G hG
    filter_upwards [gaussian_inverse_time_scalar_field] with ω hω
    obtain ⟨B,hB,hbase⟩ := hω k
    let i := terminalCoordinate k
    let Bad := (fun y : ℝ => y-ω i) ⁻¹' B
    have hBad : Bad.Countable := hB.preimage (fun a b h => by simpa using h)
    letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hBad.measure_zero (gaussianReal 0 1))] with y hy
    let b := y-ω i
    obtain ⟨M,hM,hret⟩ := hbase b hy ε hε
    obtain ⟨C,hC⟩ := exists_nat_gt M
    have hC1 : 1 ≤ C := by exact_mod_cast (hM.trans hC.le : (1:ℝ) ≤ C)
    refine mem_iUnion.mpr ⟨C,mem_iUnion.mpr ⟨hC1,?_⟩⟩
    intro T ht
    have hm := zero_lt_one.trans_le hM
    have hc := hm.trans hC
    have ht0 := (sq_pos_of_pos hc).trans_le ht
    obtain ⟨z,hz,hfit⟩ := hret T ((pow_le_pow_left₀ hm.le hC.le 2).trans ht)
    let w := (C:ℝ)/T
    have hw : 0 < w := div_pos hc ht0
    have hspan : z-b ≤ w := by
      change z-b ≤ (C:ℝ)/T
      linarith only [hz.2,div_le_div_of_nonneg_right hC.le ht0.le]
    let u : Icc (0:ℝ) 1 := ⟨(z-b)/w,div_nonneg (sub_nonneg.mpr hz.1) hw.le,(div_le_one hw).mpr hspan⟩
    refine ⟨u,?_⟩
    have he : b+w*(u:ℝ)=z := by change b+w*((z-b)/w)=z; rw [mul_div_cancel₀ _ hw.ne']; ring
    change Metric.infDist (unitaryEvolution (boundaryHamiltonian (Function.update ω i y) k (w*u)) T) _ ≤ ε
    rw [boundary_update,show y-ω (terminalCoordinate k)+w*(u:ℝ)=z from he]
    exact (hasProjectiveCircuitApproximation_iff_infDist _ 0 _).mp hfit
  filter_upwards [ha] with ω hω
  obtain ⟨C,h⟩ := mem_iUnion.mp hω
  obtain ⟨hC,hh⟩ := mem_iUnion.mp h
  refine ⟨C,hC,?_⟩
  intro T ht
  have hc : 0 < (C:ℝ) := by exact_mod_cast (show 0<C by omega)
  have ht0 := (sq_pos_of_pos hc).trans_le ht
  have hw := (div_pos hc ht0).le
  obtain ⟨u,hu⟩ := hh T ht
  exact ⟨_,⟨mul_nonneg hw u.2.1,mul_le_of_le_one_right hw u.2.2⟩,
    (hasProjectiveCircuitApproximation_iff_infDist _ 0 _).mpr hu⟩

#print axioms gaussian_unshifted_inverse_scalar
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.FieldWindows
