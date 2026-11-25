import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.OppositeConfigurations
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.CutDeterminant
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralEnclosingArc
import GaloisForLFunctions.QuantumAlg.Util.Complex

/-! # A scalar-error floor from opposite computational configurations -/
open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
open SpanningDensity
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ
variable {n : ℕ}

private theorem phase_lipschitz (t a b : ℝ) :
    ‖phase t a - phase t b‖ ≤ |t| * |a-b| := by
  have he : phase t a-phase t b=(phase t (a-b)-1)*phase t b := by
    rw [sub_mul,one_mul,←phase_add,sub_add_cancel]
  rw [he,norm_mul,phase_norm,mul_one]
  simpa only [phase,mul_comm Complex.I, Real.norm_eq_abs,abs_neg,abs_mul] using
    Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(t*(a-b)))

/-- A pair of diagonal-energy phases is at most twice the scalar
error apart, up to the survival-amplitude errors in its two columns. -/
private theorem scored_pair (u : PathShell n) (x y : Fin (n+2) → Bool) (t : ℝ) (z : ℂ) :
    let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian _⟩
    ‖phase t (pathDiagEnergy u x-pathDiagEnergy u y)-1‖ ≤
      2*(‖unitaryEvolution H.val t-z • (1 : Reg (n+2))‖+|t| *(sqrt 21*‖u‖)) := by
  intro H
  have hb (i : Fin (n+2) → Bool) :
      ‖phase t (pathDiagEnergy u i)-z‖ ≤ ‖unitaryEvolution H.val t-z • (1 : Reg (n+2))‖+|t| *(sqrt 21*‖u‖) := by
    have he := norm_entry_le_l2_opNorm (unitaryEvolution H.val t-z • 1) i i
    simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one] at he
    have hd := path_diagonal_phase u i t
    change ‖unitaryEvolution H.val t i i-phase t (pathDiagEnergy u i)‖ ≤ _ at hd
    have hh := norm_sub_le_norm_sub_add_norm_sub (phase t (pathDiagEnergy u i)) (unitaryEvolution H.val t i i) z
    rw [norm_sub_rev (phase t (pathDiagEnergy u i)) (unitaryEvolution H.val t i i)] at hh
    linarith only [he,hd,hh]
  have hp : ‖phase t (pathDiagEnergy u x)-phase t (pathDiagEnergy u y)‖ =
      ‖phase t (pathDiagEnergy u x-pathDiagEnergy u y)-1‖ := by
    nth_rw 1 [show pathDiagEnergy u x = (pathDiagEnergy u x-pathDiagEnergy u y)+pathDiagEnergy u y by ring]
    rw [phase_add,←sub_one_mul,norm_mul,phase_norm,mul_one]
  have hh := norm_sub_le_norm_sub_add_norm_sub (phase t (pathDiagEnergy u x)) z (phase t (pathDiagEnergy u y))
  rw [hp,norm_sub_rev z] at hh
  linarith only [hh,hb x,hb y]

/-- Every attainable longitudinal target angle gives a lower bound
against arbitrary complex scalars, including those inside the unit disk. -/
theorem paired_angle_scalar_floor (u : PathShell n) (z : ℂ) {t θ : ℝ} (ht : 0<t) (hθ : 0≤θ) (hπ : θ≤π)
    (hm : θ ≤ 2*t * ∑ i : Fin (n+2), |u (.inl (i,2))|) :
    let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian _⟩
    sin (θ/2) ≤ ‖unitaryEvolution H.val t-z • (1 : Reg (n+2))‖ + (sqrt 21+2)*t*‖u‖ := by
  intro H
  let y := θ/t
  have hy : |y| ≤ 2 * ∑ i : Fin (n+2), |u (.inl (i,2))| := by
    rw [abs_of_nonneg (div_nonneg hθ ht.le),div_le_iff₀ ht]
    linarith only [hm]
  obtain ⟨x,hx⟩ := pair_near u y hy
  let E := pathDiagEnergy u x-pathDiagEnergy u (fun i => !(x i))
  have herr := (phase_lipschitz t E y).trans (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
  have hc := scored_pair u x (fun i => !(x i)) t z
  change ‖phase t E-1‖ ≤ _ at hc
  have he : ‖phase t y-1‖ = 2*sin (θ/2) := by
    have hy' : t*y=θ := by dsimp only [y]; field_simp
    rw [phase,hy']
    have hid := norm_expI_sub_eq_sin_circDist (-θ) 0
    simpa only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,circDist_eq_abs_of_le_pi
      (a := -θ) (b := 0) (by simpa [abs_of_nonneg hθ] using hπ),sub_zero,abs_neg,abs_of_nonneg hθ] using hid
  have hh := norm_sub_le_norm_sub_add_norm_sub (phase t y) (phase t E) 1
  rw [he,norm_sub_rev (phase t y)] at hh
  rw [abs_of_pos ht] at herr hc
  linarith only [hh,herr,hc]

/-- Every attainable longitudinal target angle bounds the best empty
circuit error, uniformly in the target and configuration. -/
theorem paired_angle_floor (u : PathShell n) {t θ : ℝ} (ht : 0<t) (hθ : 0≤θ) (hπ : θ≤π)
    (hm : θ ≤ 2*t * ∑ i : Fin (n+2), |u (.inl (i,2))|) :
    let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian _⟩
    sin (θ/2) ≤ orbitCircuitDistance H 0 t + (sqrt 21+2)*t*‖u‖ := by
  intro H
  obtain ⟨z,_,C,hC,herr⟩ := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val t)
    0 (orbitCircuitDistance H 0 t)).mpr le_rfl
  rw [zeroGateCircuit_eval C hC] at herr
  exact (paired_angle_scalar_floor u z ht hθ hπ hm).trans (add_le_add herr le_rfl)

#print axioms paired_angle_scalar_floor

end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
