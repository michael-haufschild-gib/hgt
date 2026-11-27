import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.IncidentSupport
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.IncidentCommutators
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.RangeLocality

/-! # Truncation of physical Heisenberg evolution at a fixed radius -/
open Finset Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open LocalPatches RepeatedGates.PhysicalBlocks.CollectiveSignals
open private conjugate_difference from GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.InteractionPicture
open private iter_norm from GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.RangeLocality
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ
local instance (n : ℕ) : CStarAlgebra (Reg n) where
variable {n : ℕ}

/-- All interactions meeting the indicated set, including bonds leaving it. -/
def incidentGenerator (u : PathShell n) (S : Finset (Fin (n+2))) :=
  (-Complex.I) • (pathHamiltonian u-pathHamiltonianOnSites Sᶜ u)

private theorem discard_exterior (u : PathShell n) (S : Finset (Fin (n+2))) {x : Reg n}
    (hx : IsSiteSupported S x) :
    bracketStep ((-Complex.I) • pathHamiltonian u) x=bracketStep (incidentGenerator u S) x := by
  have hc := (commute_of_isSiteSupported_disjoint disjoint_compl_right hx
    (pathHamiltonianOnSites_isSiteSupported Sᶜ u)).eq
  simp only [incidentGenerator,bracketStep,Matrix.mul_smul,Matrix.smul_mul,mul_sub,sub_mul,hc,←smul_sub]
  congr 1
  abel

private theorem bracket_support (u : PathShell n) (S : Finset (Fin (n+2))) {x : Reg n}
    (hx : IsSiteSupported S x) :
    IsSiteSupported (incidentSites S) (bracketStep ((-Complex.I) • pathHamiltonian u) x) := by
  rw [discard_exterior u S hx,bracketStep,sub_eq_add_neg]
  have hJ : IsSiteSupported (incidentSites S) (incidentGenerator u S) :=
    IsSiteSupported.complex_smul _ (incident_difference_supported u S)
  have hx' := IsSiteSupported.mono (show S⊆incidentSites S from subset_union_left) hx
  exact (hx'.matrix_mul hJ).add ((hJ.matrix_mul hx').neg)

/-- The first p nested commutators agree with those obtained by retaining
only the interactions meeting the p-neighborhood of the initial support.
The norm error depends only on the mass in this neighborhood. -/
theorem local_transport_error (u : PathShell n) (S : Finset (Fin (n+2))) {x : Reg n}
    (hx : IsSiteSupported S x) (p : ℕ) (t : ℝ) (ht : 0≤t) :
    let T := incidentSites^[p] S
    let E := ∑ l∈T.biUnion pathIncidentLabels, |u l|
    ‖transported ((-Complex.I) • pathHamiltonian u) t x-transported (incidentGenerator u T) t x‖≤
      2*((2*E)^p*‖x‖)*t^p := by
  intro T E
  let N (i : ℕ) := incidentSites^[i] S
  let a := (-Complex.I) • pathHamiltonian u
  let b := incidentGenerator u T
  have monoN : Monotone N := monotone_nat_of_le_succ fun i => by
    change incidentSites^[i] S⊆incidentSites^[i+1] S
    rw [Function.iterate_succ_apply']
    exact subset_union_left
  have hs : ∀ i≤p, IsSiteSupported (N i) ((bracketStep b)^[i] x) := by
    intro i
    induction i with
    | zero => exact fun _ => hx
    | succ i ih =>
      intro hi
      have hi' : i≤p := by omega
      have h := ih hi'
      change IsSiteSupported (incidentSites^[i+1] S) ((bracketStep b)^[i+1] x)
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply',
        ←discard_exterior u T (IsSiteSupported.mono (monoN hi') h)]
      exact bracket_support u (N i) h
  have he (i : ℕ) (hi : i<p) :
      bracketStep a ((bracketStep b)^[i] x)=bracketStep b ((bracketStep b)^[i] x) :=
    discard_exterior u T (IsSiteSupported.mono (monoN hi.le) (hs i hi.le))
  have skew (H : Reg n) (hH : IsSelfAdjoint H) : (-Complex.I) • H∈skewAdjoint (Reg n) := by
    change star ((-Complex.I) • H)=-((-Complex.I) • H)
    rw [star_smul,hH.star_eq,star_neg,Complex.star_def,Complex.conj_I,neg_neg,neg_smul,neg_neg]
  have hb := skew _ ((isSelfAdjoint_pathHamiltonian u).sub (isSelfAdjoint_pathHamiltonianOnSites Tᶜ u))
  have h := conjugate_difference a b (skew _ (isSelfAdjoint_pathHamiltonian u)) hb p x he t ht
  have hE : ‖b‖≤E := by
    dsimp only [b,incidentGenerator]
    rw [norm_smul,norm_neg,Complex.norm_I,one_mul]
    exact FirstAscent.incident_deletion T u
  have hj := (iter_norm b x p).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (mul_nonneg zero_le_two (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hE zero_le_two) p) (norm_nonneg _))
  exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hj zero_le_two) (pow_nonneg ht _))

#print axioms local_transport_error
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
