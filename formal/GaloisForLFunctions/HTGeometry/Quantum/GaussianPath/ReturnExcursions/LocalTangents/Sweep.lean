import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.BudgetComparisons.BondTies
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.NoncontextualDynamics
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage

/-! # Local affine improvements are attainable with one bond sweep -/

open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.LocalTangents
open PhaseBoundary.FiniteCertificates.BudgetComparisons
open private signed_bond_step from
  GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.BudgetComparisons.BondTies
open private evolutionLinearTerm norm_unitaryEvolution_sub_linear_le from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.NoncontextualDynamics
noncomputable section
abbrev Register (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- First-order laboratory rotation of a circuit by an arbitrary path Hamiltonian.
The scalar shift includes the free global phase. -/
def direction {n : ℕ} (Q : Register (n+2)) (y : PathShell n) (c : ℝ) : Register (n+2) :=
  ((-Complex.I) • (scalarCenteredHamiltonian (generator y) c).val)*Q

/-- A bond sweep follows any local affine direction to quadratic accuracy.
The comparison uses the same circuit and includes its physical global phase. -/
theorem tangent_sweep {n : ℕ} (C : TwoQubitCircuit (n+2)) {z : ℂ} (hz : ‖z‖=1)
    (y : PathShell n) (c : ℝ) :
    let Q := z • C.eval.val
    ∃ B≥(0:ℝ), ∀ r≥(0:ℝ), ∃ D : TwoQubitCircuit (n+2), D.gateCount ≤ C.gateCount+(n+1) ∧
      ∃ w : ℂ, ‖w‖=1 ∧ ‖Q+r • direction Q y c-w • D.eval.val‖≤B*r^2 := by
  intro Q
  let L := scalarCenteredHamiltonian (generator y) c
  refine ⟨84*‖y‖^2+‖L.val‖^2/2,by positivity,?_⟩
  intro r hr
  have hsim : orbitCircuitDistance L (n+1) r≤84*‖y‖^2*r^2 := by
    rw [show orbitCircuitDistance L (n+1)=orbitCircuitDistance (generator y) (n+1) from
      orbitCircuitDistance_scalarCentered (generator y) _ c]
    exact (hasProjectiveCircuitApproximation_iff_infDist ..).mp (by
      simpa only [abs_of_nonneg hr] using signed_bond_step y r)
  obtain ⟨w,hw,D,hD,hmat⟩ := (hasProjectiveCircuitApproximation_iff_infDist ..).mpr hsim
  refine ⟨D.mul C,(Nat.add_le_add_left hD C.gateCount),w*z,by rw [norm_mul,hw,hz,mul_one],?_⟩
  have hlin : Q+r • direction Q y c=(1+evolutionLinearTerm L.val r)*Q := by
    dsimp only [direction,evolutionLinearTerm,L]
    rw [add_mul,one_mul,Matrix.smul_mul,Matrix.smul_mul,←Complex.coe_smul r _,smul_smul]
  have hprod : (w • D.eval.val)*Q=(w*z) • (D.mul C).eval.val := by
    rw [TwoQubitCircuit.mul_eval]
    change (w • D.eval.val)*(z • C.eval.val)=(w*z) • (D.eval.val*C.eval.val)
    rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  have hnorm (A : Register (n+2)) : ‖A*Q‖=‖A‖ := by
    dsimp only [Q]
    rw [Matrix.mul_smul,norm_smul,hz,one_mul,CStarRing.norm_mul_mem_unitary _ C.eval.2]
  have hstep := norm_unitaryEvolution_sub_linear_le L.val L.2 r hr
  rw [hlin,←hprod,←sub_mul,hnorm]
  calc
    _ ≤ ‖(1+evolutionLinearTerm L.val r)-unitaryEvolution L.val r‖+
      ‖unitaryEvolution L.val r-w • D.eval.val‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ (r*‖L.val‖)^2/2+84*‖y‖^2*r^2 := add_le_add ((norm_sub_rev ..).le.trans hstep) hmat
    _ = _ := by ring

/-- If a local tangent displacement reduces the full operator error, a circuit
using at most one additional bond sweep strictly reduces it at the same date. -/
theorem improve_affine_fit {n : ℕ} (U : Register (n+2)) (C : TwoQubitCircuit (n+2))
    {z : ℂ} (hz : ‖z‖=1) (y : PathShell n) (c : ℝ) :
    let Q := z • C.eval.val
    ‖U-(Q+direction Q y c)‖<‖U-Q‖ →
      ∃ D : TwoQubitCircuit (n+2), D.gateCount ≤ C.gateCount+(n+1) ∧
        ∃ w : ℂ, ‖w‖=1 ∧ ‖U-w • D.eval.val‖<‖U-Q‖ := by
  intro Q hgain
  obtain ⟨B,hB,hsim⟩ := tangent_sweep C hz y c
  let G := direction Q y c
  let e := ‖U-Q‖
  let f := ‖U-(Q+G)‖
  have hg : 0<e-f := sub_pos.mpr hgain
  have hden : 0<B+1 := by linarith only [hB]
  obtain ⟨r,hr,hsmall⟩ := exists_between (lt_min zero_lt_one (div_pos hg hden))
  have hr₁ := hsmall.trans_le (min_le_left ..)
  have hr₂ := (lt_div_iff₀ hden).mp (hsmall.trans_le (min_le_right ..))
  obtain ⟨D,hD,w,hw,hfit⟩ := hsim r hr.le
  refine ⟨D,hD,w,hw,?_⟩
  have hc : ‖U-(Q+r • G)‖≤(1-r)*e+r*f := by
    rw [show U-(Q+r • G)=(1-r) • (U-Q)+r • (U-(Q+G)) by module]
    apply (norm_add_le ..).trans
    simp only [norm_smul,Real.norm_of_nonneg hr.le,Real.norm_of_nonneg (sub_nonneg.mpr hr₁.le),e,f,le_refl]
  apply (norm_sub_le_norm_sub_add_norm_sub U (Q+r • G) _).trans_lt
  apply (add_le_add hc hfit).trans_lt
  change (1-r)*e+r*f+B*r^2<e
  nlinarith only [mul_lt_mul_of_pos_left hr₂ hr,sq_nonneg r]

#print axioms improve_affine_fit
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.LocalTangents
