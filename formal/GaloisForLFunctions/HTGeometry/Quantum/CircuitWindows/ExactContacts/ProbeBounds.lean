import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.GateAnnihilator
import GaloisForLFunctions.HTGeometry.MvPolynomialSmooth
import GaloisForLFunctions.HTGeometry.ProjectiveContinuousCircuitConeLaw

/-! # Quantitative separation by circuit polynomials in operator norm -/
open MvPolynomial Metric
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ExactContacts
noncomputable section
private abbrev State (n : ℕ) := Fin n → Bool
private abbrev Reg (n : ℕ) := Matrix (State n) (State n) ℂ

private def probeMap {n r : ℕ} (w : Fin r → State n × State n → ℂ) :
    Reg n →ₗ[ℂ] (Fin r → ℂ) where
  toFun M i := ∑ p, w i p * M p.1 p.2
  map_add' M B := by
    ext i
    simp only [Matrix.add_apply,mul_add,Finset.sum_add_distrib,Pi.add_apply]
  map_smul' z M := by
    ext i
    simp only [Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring

/-- The polynomial that vanishes on every exact projective endpoint is
bounded by Kε on the entire physical ε-tube in the unit ball. -/
theorem projective_gate_probe_bound {n r : ℕ} (s : ℕ) (hr : s*16+1<r)
    (w : Fin r → State n × State n → ℂ) :
    ∃ F : MvPolynomial (Fin r) ℂ, F≠0 ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (M : Reg n) (ε : ℝ), ‖M‖≤1 → HasProjectiveCircuitApproximation n ε s M →
      ∀ z : ℂ, ‖z‖=1 → ‖aeval (fun i => z*∑ p, w i p*M p.1 p.2) F‖ ≤ K*ε := by
  classical
  obtain ⟨F,hF,hzero⟩ := projective_gate_annihilator s hr w
  let B := LinearMap.toContinuousLinearMap (probeMap w)
  obtain ⟨L,hL,hlip⟩ := exists_lipschitz_mvPolynomial_eval F 0 ‖B‖
  refine ⟨F,hF,L*‖B‖,mul_nonneg hL B.opNorm_nonneg,?_⟩
  intro M ε hM ⟨c,hc,U,hU,he⟩ z hz
  let X := z • M
  let Y := (z*c) • U.eval.val
  have hmem (A : Reg n) (ha : ‖A‖≤1) : B A∈closedBall 0 ‖B‖ := by
    rw [mem_closedBall,dist_zero_right]
    exact (B.le_opNorm A).trans (mul_le_of_le_one_right B.opNorm_nonneg ha)
  have hx : ‖X‖≤1 := by simpa only [X,norm_smul,hz,one_mul] using hM
  have hy : ‖Y‖≤1 := by
    dsimp only [Y]
    rw [norm_smul,norm_mul,hz,hc,CStarRing.norm_of_mem_unitary U.eval.2,one_mul,one_mul]
  have hd : ‖X-Y‖≤ε := by simpa only [X,Y,←smul_smul,←smul_sub,norm_smul,hz,one_mul] using he
  have hprobe (a : ℂ) (A : Reg n) : B (a • A)=(fun i => a*∑ p, w i p*A p.1 p.2) := by
    rw [map_smul]; rfl
  have hzy : eval (B Y) F=0 := by
    dsimp only [Y]
    rw [hprobe,←MvPolynomial.aeval_eq_eval]
    exact hzero U hU (z*c)
  have hh := hlip _ (hmem X hx) _ (hmem Y hy)
  rw [hzy,sub_zero,←map_sub] at hh
  rw [←hprobe,MvPolynomial.aeval_eq_eval]
  exact hh.trans ((mul_le_mul_of_nonneg_left ((B.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left hd B.opNorm_nonneg)) hL).trans_eq (mul_assoc ..).symm)

#print axioms projective_gate_probe_bound
end
end GaloisForLFunctions.HTGeometry.ExactContacts
