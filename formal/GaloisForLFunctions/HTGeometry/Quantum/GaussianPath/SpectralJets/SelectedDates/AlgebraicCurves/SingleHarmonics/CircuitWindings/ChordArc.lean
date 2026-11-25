import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance

/-! # A common chord center bounds the enclosing arc of spectator phases -/

open Real Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
open SharpOccupation
noncomputable section

private theorem chord_shift (a b h : ℝ) :
    ‖Complex.exp (((a+h:ℝ):ℂ)*Complex.I)-Complex.exp (((b+h:ℝ):ℂ)*Complex.I)‖ =
    ‖Complex.exp ((a:ℂ)*Complex.I)-Complex.exp ((b:ℂ)*Complex.I)‖ := by
  simp only [Complex.ofReal_add,add_mul,Complex.exp_add,←sub_mul,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one]

/-- Subtracting the line phase from the evolution angle transfers the
same global scalar to the center of every resulting chord. -/
theorem chord_exchange (θ β γ : ℝ) :
    ‖Complex.exp (((θ-β:ℝ):ℂ)*Complex.I)-Complex.exp ((γ:ℂ)*Complex.I)‖ =
    ‖Complex.exp (((θ-γ:ℝ):ℂ)*Complex.I)-Complex.exp ((β:ℂ)*Complex.I)‖ := by
  rw [←chord_shift (θ-β) γ β,←chord_shift (θ-γ) β γ,sub_add_cancel,sub_add_cancel,add_comm γ β]

/-- Unit phases lying within chord error ε of the same scalar occupy at
most the physical arc fraction 2 arcsin(ε/2)/π of a turn. -/
theorem enclosing_of_common_chord {I : Type*} [Fintype I] [Nonempty I]
    (θ : I→ℝ) (c : ℝ) {ε : ℝ} (hε : ε∈Ioo (0:ℝ) (sqrt 2))
    (hc : ∀ i, ‖Complex.exp ((θ i:ℂ)*Complex.I)-Complex.exp ((c:ℂ)*Complex.I)‖≤ε) :
    (fun i => ((θ i/(2*π):ℝ):UnitAddCircle))∈enclosingUnitArc (physicalArc ε) := by
  obtain ⟨hx,ht⟩ := physicalArc_spec hε.1 hε.2
  let x := physicalArc ε
  let r : Icc (0:ℝ) (1/2) := ⟨x,hx.1.le,hx.2.le⟩
  apply (mem_enclosingUnitArc_iff_spectralEnclosingArcLength θ r).mpr
  have hrad (i : I) : circDist (θ i) c ≤ π*x := by
    have h := hc i
    rw [norm_expI_sub_eq_sin_circDist,←ht] at h
    change 2*sin (circDist (θ i) c/2)≤2*sin (π*x/2) at h
    have ha := circDist_nonneg (θ i) c
    have hb := circDist_le_pi (θ i) c
    have hpx := mul_nonneg pi_pos.le hx.1.le
    have hx₁ : x ≤ 1 := hx.2.le.trans (by norm_num)
    have hpx₁ := mul_le_of_le_one_right pi_pos.le hx₁
    have hle := Real.strictMonoOn_sin.le_iff_le
      (show circDist (θ i) c/2∈Icc (-(π/2)) (π/2) from
        ⟨by linarith only [ha,pi_pos],by linarith only [hb]⟩)
      (show π*x/2∈Icc (-(π/2)) (π/2) from
        ⟨by linarith only [hpx,pi_pos],by linarith only [hpx₁]⟩)
    have hhalf := hle.mp (le_of_mul_le_mul_left h zero_lt_two)
    linarith only [hhalf]
  exact (spectralEnclosingArcLength_le_twice_radius θ c (π*x) hrad).trans_eq (mul_assoc ..).symm

#print axioms enclosing_of_common_chord
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
