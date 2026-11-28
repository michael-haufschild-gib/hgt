import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.ClockCell
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings.CircuitColumns

/-! # Retaining the fitting global phase in the circuit winding lift -/

open Matrix Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
open SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings SharpOccupation
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ
private abbrev phase (a : ℝ) := Complex.exp ((a:ℂ)*Complex.I)

/-- Circuit diagonal arguments in the energy basis, measured in turns. -/
def circuitTurns (W : unitary (Mat I)) (i : I) := (W.val i i).arg/(2*π)

/-- Exact projective operator fit to a laboratory unitary in the energy basis. -/
def circuitDates (W : unitary (Mat I)) (A : I → ℝ) (ε : ℝ) : Set ℝ :=
  {t | ∃ p : ℝ, ‖(anglePacket fun i => 2*π*(t*A i-p)).val-W.val‖≤ε}

private theorem column (W : unitary (Mat I)) (f : I → ℝ) {ε : ℝ}
    (he : ε<sqrt 2) (h : ‖(anglePacket f).val-W.val‖≤ε) (i : I) :
    ‖phase (f i)-phase (2*π*circuitTurns W i)‖≤ε := by
  let Φ := Matrix.toEuclideanCLM (𝕜:=ℂ) (n:=I)
  let v : EuclideanSpace ℂ I := EuclideanSpace.single i 1
  let w := Φ W.val v
  let D := (anglePacket f).val
  have hv : ‖v‖=1 := by simp only [v,PiLp.norm_single,norm_one]
  have hw : ‖w‖=1 := (norm_apply_of_mem_unitary (Unitary.map_mem Φ W.2) v).trans hv
  have hd : Φ D v=phase (f i) • v := by
    ext j
    change (Matrix.diagonal (fun j => phase (f j)) *ᵥ v.ofLp) j=phase (f i)*v j
    rw [mulVec_diagonal]
    by_cases hj : j=i
    · subst j; rfl
    · simp [v,EuclideanSpace.single,hj]
  have hh : ‖phase (f i) • v-w‖≤ε := by
    change ‖phase (f i) • v-Φ W.val v‖≤ε
    rw [←hd,←_root_.sub_apply,←map_sub]
    refine ((Φ (D-W.val)).le_opNorm v).trans ?_
    rwa [hv,mul_one,Matrix.l2_opNorm_toEuclideanCLM]
  have hinner : inner ℂ v w=W.val i i := by
    rw [show v=EuclideanSpace.single i 1 from rfl,EuclideanSpace.inner_single_left]
    change _*(W.val *ᵥ (Pi.single i 1)) i=_
    rw [mulVec_single_one]
    simp
  have hs := sharp_line_chord v w hv hw (phase (f i)) (Complex.norm_exp_ofReal_mul_I _) (hh.trans_lt he)
  rw [hinner] at hs
  rw [show 2*π*circuitTurns W i=(W.val i i).arg by dsimp only [circuitTurns]; field_simp]
  exact hs.trans hh

private theorem turn_lift (a b : ℝ) {ε : ℝ} (he : ε∈Ioo (0:ℝ) (sqrt 2))
    (hch : ‖phase (2*π*a)-phase (2*π*b)‖≤ε) :
    |a-b-(round (a-b):ℝ)|≤physicalArc ε/2 := by
  let x := physicalArc ε
  let D := circDist (2*π*a) (2*π*b)
  obtain ⟨hx,het⟩ := physicalArc_spec he.1 he.2
  have hD : 0≤D := circDist_nonneg ..
  have hD' : D≤π := circDist_le_pi ..
  have hpx : 0≤π*x := mul_nonneg pi_pos.le hx.1.le
  have hpx' : π*x≤π := mul_le_of_le_one_right pi_pos.le (hx.2.le.trans (by norm_num))
  rw [norm_expI_sub_eq_sin_circDist,←het] at hch
  change 2*sin (D/2)≤2*sin (π*x/2) at hch
  have hd := Real.strictMonoOn_sin.le_iff_le
    (show D/2∈Icc (-(π/2)) (π/2) by constructor <;> linarith only [hD,hD',pi_pos])
    (show π*x/2∈Icc (-(π/2)) (π/2) by constructor <;> linarith only [hpx,hpx',pi_pos])
  have hr := hd.mp (le_of_mul_le_mul_left hch zero_lt_two)
  have heq : D=2*π*|a-b-(round (a-b):ℝ)| := by
    dsimp only [D,circDist,phaseGap]
    rw [←mul_sub,mul_div_cancel_left₀ _ two_pi_pos.ne',←mul_sub,abs_mul,abs_of_pos two_pi_pos]
  rw [heq] at hr
  apply le_of_mul_le_mul_left (a:=2*π) _ two_pi_pos
  change _ ≤ 2*π*(x/2)
  linarith only [hr]

theorem packet_lift (A : I → ℝ) (m : I → ℤ) (t p : ℝ) :
    (anglePacket fun i => 2*π*(t*A i-(m i:ℝ)-p)).val=
      (anglePacket fun i => 2*π*(t*A i-p)).val := by
  apply congrArg Matrix.diagonal
  funext i
  change Complex.exp _=Complex.exp _
  have he : ((2*π*(t*A i-(m i:ℝ)-p):ℝ):ℂ)*Complex.I =
      ((-m i:ℤ):ℂ)*(2*π*Complex.I)+((2*π*(t*A i-p):ℝ):ℂ)*Complex.I := by push_cast; ring
  rw [he,Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,one_mul]

/-- Exact projective visits are precisely the union of their lifted operator fits.
The angular restriction uses the actual fitting phase and keeps the original error. -/
theorem date_iff_lift (W : unitary (Mat I)) (A : I → ℝ) {ε t : ℝ} (he : ε∈Ioo (0:ℝ) (sqrt 2)) :
    t∈circuitDates W A ε ↔ ∃ m : I → ℤ, t∈wordDates W A (circuitTurns W) m (physicalArc ε) ε := by
  constructor
  · rintro ⟨p,hp⟩
    let m (i : I) := round (t*A i-p-circuitTurns W i)
    refine ⟨m,p,?_,?_⟩
    · intro i
      have hh := turn_lift (t*A i-p) (circuitTurns W i) he (column W _ he.2 hp i)
      rw [show t*A i-(circuitTurns W i+(m i:ℝ))-p=t*A i-p-circuitTurns W i-(m i:ℝ) by ring]
      exact hh
    · rwa [packet_lift]
  · rintro ⟨m,p,_,hp⟩
    exact ⟨p,packet_lift A m t p ▸ hp⟩

#print axioms date_iff_lift
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
