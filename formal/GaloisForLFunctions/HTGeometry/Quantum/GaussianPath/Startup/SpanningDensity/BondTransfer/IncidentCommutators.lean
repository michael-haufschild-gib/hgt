import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.RelativeRemainder
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.IncidentMass
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.PauliTerm
import GaloisForLFunctions.HTGeometry.Quantum.LocalPacketComparison

/-! # Local mass controls the first-order error when an interaction is erased -/

open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open LocalPatches
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ
local instance (N : ℕ) : CStarAlgebra (Reg N) where
variable {n : ℕ}

private theorem bracket_norm (x j : Reg (n+2)) : ‖bracketStep j x‖≤2*‖x‖*‖j‖ := by
  exact ((norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))).trans_eq (by ring)

/-- Terms outside the support of x commute exactly. Only the incident
coefficient mass enters its initial speed. -/
theorem incident_speed (u : PathShell n) (S : Finset (Fin (n+2))) (x : Reg (n+2))
    (hx : IsSiteSupported S x) :
    ‖bracketStep ((-Complex.I) • pathHamiltonian u) x‖≤
      2*‖x‖*(∑ l∈S.biUnion pathIncidentLabels, |u l|) := by
  let H := pathHamiltonian u
  let B := pathHamiltonianOnSites Sᶜ u
  have hc : x*B=B*x := (commute_of_isSiteSupported_disjoint disjoint_compl_right hx
    (pathHamiltonianOnSites_isSiteSupported Sᶜ u)).eq
  have he : bracketStep ((-Complex.I) • H) x =
      (-Complex.I) • bracketStep (H-B) x := by
    simp only [bracketStep,Matrix.mul_smul,Matrix.smul_mul,mul_sub,sub_mul,hc]
    rw [←smul_sub]
    congr 1
    abel
  change ‖bracketStep ((-Complex.I) • H) x‖≤_
  rw [he,norm_smul,norm_neg,Complex.norm_I,one_mul]
  exact (bracket_norm x (H-B)).trans (mul_le_mul_of_nonneg_left
    (FirstAscent.incident_deletion S u) (by positivity))

/-- Erasing a locally supported skew generator j changes the transported
observable first by t times its commutator. The error is proportional to
the erased strength even when the full chain has large norm. -/
theorem local_erasure (u : PathShell n) (S : Finset (Fin (n+2))) (x j : Reg (n+2))
    (hx : IsSiteSupported S x) (hS : IsSiteSupported S j) (hj : j∈skewAdjoint (Reg (n+2)))
    (t : ℝ) (ht : 0≤t) :
    let k := (-Complex.I) • pathHamiltonian u
    let E := ∑ l∈S.biUnion pathIncidentLabels, |u l|
    ‖transported k t x-transported (k-j) t x-t • bracketStep j x‖≤
      t^2*(4*‖x‖*‖j‖*(2*E+‖j‖)) := by
  intro k E
  have hk : k∈skewAdjoint (Reg (n+2)) := by
    have he : k=∑ l, pathTermGenerator u l := by
      dsimp only [k]
      rw [pathHamiltonian_eq_sum,Finset.smul_sum]
      rfl
    rw [he]
    exact (skewAdjoint _).sum_mem fun l _ => (pathTerm_properties u l).2.1
  have h := relative_remainder (k-j) j x ((skewAdjoint _).sub_mem hk hj) hj t ht
  rw [sub_add_cancel] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg t)
  let p := bracketStep j x
  have hp : IsSiteSupported S p := by
    dsimp only [p,bracketStep]
    rw [sub_eq_add_neg]
    exact (hx.matrix_mul hS).add (hS.matrix_mul hx).neg
  have h₁ : ‖bracketStep (k-j) x‖≤2*‖x‖*E+2*‖x‖*‖j‖ := by
    rw [show bracketStep (k-j) x=bracketStep k x-p by dsimp only [p,bracketStep]; noncomm_ring]
    exact (norm_sub_le _ _).trans (add_le_add (incident_speed u S x hx) (bracket_norm x j))
  have hE : 0≤E := sum_nonneg fun _ _ => abs_nonneg _
  have h₂ := (incident_speed u S p hp).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (bracket_norm x j) zero_le_two) hE)
  change 2*‖j‖*‖bracketStep (k-j) x‖+‖bracketStep k p‖≤_
  nlinarith only [mul_le_mul_of_nonneg_left h₁ (show 0≤2*‖j‖ by positivity),h₂]

#print axioms local_erasure
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
