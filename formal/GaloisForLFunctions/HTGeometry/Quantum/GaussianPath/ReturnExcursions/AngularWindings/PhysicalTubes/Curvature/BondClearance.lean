import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Curvature.SquaredError
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.BudgetComparisons.BondTies
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ElapsedWindow.ContactMargin

/-! # Strict first-return improvement from a deeper fit on the entering winding -/

open Matrix Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
open PhaseBoundary.FiniteCertificates.BudgetComparisons PrecisionReturns
noncomputable section

/-- The gain in squared error towards a stricter fit is linear in the
interpolation fraction. A bond sweep transports that gain back to the
original date with only quadratic loss. The interpolation fraction balances
the linear gain against that loss. -/
theorem sweep_clearance_of_winding {n : ℕ} (h : PathShell n) (s : ℕ) (C : TwoQubitCircuit (n+2))
    (hC : C.gateCount ≤ s) (m : (Fin (n+2) → Bool) → ℤ) {v u x ε η : ℝ}
    (hx : x≤1/2) (hε : ε^2<2) (hη : 0≤η) (hbetter : η<ε) :
    let H := generator h
    let V := H.2.isHermitian.eigenvectorUnitary
    let W := V⁻¹*C.eval*V
    let A (i : Fin (n+2) → Bool) := -H.2.isHermitian.eigenvalues i/(2*π)
    v∈wordDates W A (circuitTurns W) m x ε → u∈wordDates W A (circuitTurns W) m x η →
      let D := 84*‖h‖^2*(u-v)^2
      let g := ε^2-η^2
      let r := min 1 (g/(1+4*ε*D))
      0<r*g/(4*ε) ∧ orbitCircuitDistance H (s+(n+1)) v≤ε-r*g/(4*ε) := by
  intro H V W A hv hu D g r
  have hε₀ := hη.trans_lt hbetter
  have hsq := (sq_lt_sq₀ hη hε₀.le).mpr hbetter
  have hg : 0<g := sub_pos.mpr hsq
  have hD : 0≤D := by dsimp only [D]; positivity
  have hden : 0<1+4*ε*D := by positivity
  have hr : 0<r := lt_min zero_lt_one (div_pos hg hden)
  have hr₁ : r≤1 := min_le_left ..
  have hr₂ := (le_div_iff₀ hden).mp (show r≤g/(1+4*ε*D) from min_le_right ..)
  let t := v+r*(u-v)
  obtain ⟨z,hz,hfit⟩ := laboratory_winding_secant H C.eval m hx hε (hsq.trans hε) hv hu r ⟨hr.le,hr₁⟩
  let y := ‖unitaryEvolution H.val t-z • C.eval.val‖
  have hy : 0≤y := norm_nonneg _
  have hy₂ : y^2≤ε^2-r*g := by
    apply hfit.trans_eq
    dsimp only [g]
    ring
  have hye : y≤ε := (sq_le_sq₀ hy hε₀.le).mp (hy₂.trans (sub_le_self _ (mul_nonneg hr.le hg.le)))
  have hcost : orbitCircuitDistance H s t≤y :=
    (hasProjectiveCircuitApproximation_iff_infDist ..).mp ⟨z,hz,C,hC,le_rfl⟩
  have hclose : orbitCircuitDistance H (s+(n+1)) v≤y+D*r^2 := by
    apply (bond_increment h s v t).trans
    apply add_le_add hcost
    rw [sq_abs]
    exact le_of_eq (by dsimp only [t,D]; ring)
  have hgain : r*g≤(ε-y)*(2*ε) := by
    calc
      r*g ≤ (ε-y)*(ε+y) := by nlinarith only [hy₂]
      _ ≤ (ε-y)*(2*ε) := mul_le_mul_of_nonneg_left (by linarith only [hye]) (sub_nonneg.mpr hye)
  have h₄ : 0<4*ε := by positivity
  refine ⟨div_pos (mul_pos hr hg) h₄,hclose.trans ?_⟩
  have hmargin : r*g/(4*ε)≤ε-(y+D*r^2) := (div_le_iff₀ h₄).mpr (by
    nlinarith only [hgain,mul_le_mul_of_nonneg_left hr₂ hr.le,sq_nonneg r])
  linarith only [hmargin]

/-- If the first contact has a deeper fit on its own winding, one additional
sweep strictly advances the first visit at the prescribed tolerance. -/
theorem earlier_first_visit_of_winding {n : ℕ} (h : PathShell n) (a : ℝ) (s : ℕ)
    (C : TwoQubitCircuit (n+2)) (hC : C.gateCount ≤ s) (m : (Fin (n+2) → Bool) → ℤ)
    {u x ε η : ℝ} (hx : x≤1/2) (hε : ε^2<2) (hη : 0≤η) (hbetter : η<ε) :
    let H := generator h
    let V := H.2.isHermitian.eigenvectorUnitary
    let W := V⁻¹*C.eval*V
    let A (i : Fin (n+2) → Bool) := -H.2.isHermitian.eigenvalues i/(2*π)
    let v := firstVisit H a s ε
    ε<orbitCircuitDistance H s a → v∈wordDates W A (circuitTurns W) m x ε →
      u∈wordDates W A (circuitTurns W) m x η → firstVisit H a (s+(n+1)) ε<v := by
  intro H V W A v hfar hv hu
  obtain ⟨hg,hbound⟩ := sweep_clearance_of_winding h s C hC m hx hε hη hbetter hv hu
  exact ElapsedWindow.strict_of_first_margin H a s _ (hη.trans_lt hbetter) hfar
    (hbound.trans_lt (sub_lt_self _ hg))


#print axioms earlier_first_visit_of_winding
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
