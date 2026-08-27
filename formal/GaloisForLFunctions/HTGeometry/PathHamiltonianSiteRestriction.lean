import GaloisForLFunctions.HTGeometry.NearestNeighborPathSpectrumRealRelationEscape
import GaloisForLFunctions.HTGeometry.PauliOperatorNormSandwich
import GaloisForLFunctions.HTGeometry.PathChainLabelIdentification
import GaloisForLFunctions.HTGeometry.PathDiagonalCarrier
import GaloisForLFunctions.HTGeometry.SiteSupportedEvolutionFactorization

/-!
# Restricting a path Hamiltonian by physical site packet

Keep exactly those onsite and nearest-neighbour Pauli words whose nonidentity support lies in a
chosen packet.  The resulting generator is intrinsically supported on that packet and remains
self-adjoint.  This is the exact truncation needed for mobile-cut thermodynamic arguments.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : ℕ}

/-- A path-shell word has no nonidentity letter outside `S`. -/
def PathWordSupportedIn (S : Finset (Fin (n + 2))) (l : PathLabel n) : Prop :=
  ∀ v, v ∉ S → pathWord l v = none

instance instDecidablePathWordSupportedIn (S : Finset (Fin (n + 2))) (l : PathLabel n) :
    Decidable (PathWordSupportedIn S l) := Classical.propDecidable _

/-- Keep the Pauli terms lying wholly inside `S`. -/
def pathHamiltonianOnSites (S : Finset (Fin (n + 2))) (u : PathShell n) :
    Matrix (FiniteQubitConfiguration (Fin (n + 2)))
      (FiniteQubitConfiguration (Fin (n + 2))) ℂ :=
  ∑ l : PathLabel n,
    ((((if PathWordSupportedIn S l then u l else 0) : ℝ) : ℂ) •
      finitePauliMatrix (pathWord l))

/-- Coefficient shell obtained by zeroing every word not wholly supported in `S`. -/
def pathShellOnSites (S : Finset (Fin (n + 2))) (u : PathShell n) : PathShell n :=
  WithLp.toLp 2 fun l => if PathWordSupportedIn S l then u l else 0

namespace IsSiteSupported

/-- Complex scaling preserves intrinsic site support. -/
theorem complex_smul {V : Type*} {A : V → Type*} {S : Finset V}
    {H : Matrix ((v : V) → A v) ((v : V) → A v) ℂ}
    (c : ℂ) (hH : IsSiteSupported S H) :
    IsSiteSupported S (c • H) := by
  refine ⟨fun x y hxy => ?_, fun x y x' y' h₁ h₂ h₃ h₄ => ?_⟩
  · simp [Matrix.smul_apply, hH.1 x y hxy]
  · simp [Matrix.smul_apply, hH.2 x y x' y' h₁ h₂ h₃ h₄]

end IsSiteSupported

/-- The packet-restricted path Hamiltonian acts only on that packet. -/
theorem pathHamiltonianOnSites_isSiteSupported
    (S : Finset (Fin (n + 2))) (u : PathShell n) :
    IsSiteSupported S (pathHamiltonianOnSites S u) := by
  classical
  unfold pathHamiltonianOnSites
  refine Finset.sum_induction _ (IsSiteSupported S)
    (fun _ _ h₁ h₂ => IsSiteSupported.add h₁ h₂) (IsSiteSupported.zero S) ?_
  intro l hluniv
  by_cases hl : PathWordSupportedIn S l
  · exact IsSiteSupported.complex_smul _
      (finitePauliMatrix_isSiteSupported_of_eq_none S (pathWord l) hl)
  · simpa [hl] using (IsSiteSupported.zero S)

theorem pathHamiltonianOnSites_eq_pathHamiltonian_pathShellOnSites
    (S : Finset (Fin (n + 2))) (u : PathShell n) :
    pathHamiltonianOnSites S u = pathHamiltonian (pathShellOnSites S u) := by
  rw [pathHamiltonian_eq_sum]
  rfl

theorem pathShellOnSites_isDiag
    {S : Finset (Fin (n + 2))} {u : PathShell n}
    (hu : ∀ l : PathLabel n, ¬IsDiagLabel l → u l = 0) :
    ∀ l : PathLabel n, ¬IsDiagLabel l → pathShellOnSites S u l = 0 := by
  intro l hl
  unfold pathShellOnSites
  by_cases hs : PathWordSupportedIn S l
  · simp [hs, hu l hl]
  · simp [hs]

theorem pathHamiltonianOnSites_eq_diagonal
    (S : Finset (Fin (n + 2))) (u : PathShell n)
    (hu : ∀ l : PathLabel n, ¬IsDiagLabel l → u l = 0) :
    pathHamiltonianOnSites S u =
      Matrix.diagonal (fun x => ((pathDiagEnergy (pathShellOnSites S u) x : ℝ) : ℂ)) := by
  rw [pathHamiltonianOnSites_eq_pathHamiltonian_pathShellOnSites]
  exact pathHamiltonian_eq_diagonal _ (pathShellOnSites_isDiag hu)

/-- Packet restriction preserves self-adjointness. -/
theorem isSelfAdjoint_pathHamiltonianOnSites
    (S : Finset (Fin (n + 2))) (u : PathShell n) :
    IsSelfAdjoint (pathHamiltonianOnSites S u) := by
  unfold pathHamiltonianOnSites
  exact isSelfAdjoint_pauliCombination (fun l : PathLabel n => pathWord l)
    (fun l => if PathWordSupportedIn S l then u l else 0)

/-- Restriction to every site returns the original path Hamiltonian. -/
theorem pathHamiltonianOnSites_univ (u : PathShell n) :
    pathHamiltonianOnSites Finset.univ u = pathHamiltonian u := by
  rw [pathHamiltonian_eq_sum]
  unfold pathHamiltonianOnSites
  apply Finset.sum_congr rfl
  intro l hl
  simp [PathWordSupportedIn]

/-- A mobile-cut reference keeps the actual generator on `S` and a chosen center on `T`. -/
def pathHamiltonianPacketReference
    (S T : Finset (Fin (n + 2))) (u center : PathShell n) :
    Matrix (FiniteQubitConfiguration (Fin (n + 2)))
      (FiniteQubitConfiguration (Fin (n + 2))) ℂ :=
  pathHamiltonianOnSites S u + pathHamiltonianOnSites T center

/-- Real coefficient retained by the mobile-cut reference. -/
def pathPacketReferenceCoeff
    (S T : Finset (Fin (n + 2))) (u center : PathShell n) (l : PathLabel n) : ℝ :=
  (if PathWordSupportedIn S l then u l else 0) +
    (if PathWordSupportedIn T l then center l else 0)

theorem pathHamiltonianPacketReference_eq_sum
    (S T : Finset (Fin (n + 2))) (u center : PathShell n) :
    pathHamiltonianPacketReference S T u center =
      ∑ l : PathLabel n,
        (((pathPacketReferenceCoeff S T u center l : ℝ) : ℂ) •
          finitePauliMatrix (pathWord l)) := by
  classical
  unfold pathHamiltonianPacketReference pathHamiltonianOnSites pathPacketReferenceCoeff
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  push_cast
  exact (add_smul _ _ _).symm

theorem pathHamiltonian_sub_packetReference_eq_sum
    (S T : Finset (Fin (n + 2))) (u center : PathShell n) :
    pathHamiltonian u - pathHamiltonianPacketReference S T u center =
      ∑ l : PathLabel n,
        ((((u l - pathPacketReferenceCoeff S T u center l : ℝ) : ℂ)) •
          finitePauliMatrix (pathWord l)) := by
  rw [pathHamiltonian_eq_sum, pathHamiltonianPacketReference_eq_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  push_cast
  exact (sub_smul _ _ _).symm

/-- Operator-norm error is bounded by the omitted/changed coefficient `ℓ1` mass. -/
theorem norm_pathHamiltonian_sub_packetReference_le
    (S T : Finset (Fin (n + 2))) (u center : PathShell n) :
    ‖pathHamiltonian u - pathHamiltonianPacketReference S T u center‖ ≤
      ∑ l : PathLabel n, |u l - pathPacketReferenceCoeff S T u center l| := by
  rw [pathHamiltonian_sub_packetReference_eq_sum]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun l _ => ?_)
  rw [norm_smul, norm_finitePauliMatrix, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- Evolution of a mobile-cut reference factorizes into its two physical packets. -/
theorem unitaryEvolution_pathHamiltonianPacketReference
    {S T : Finset (Fin (n + 2))} (hST : Disjoint S T)
    (u center : PathShell n) (t : ℝ) :
    unitaryEvolution (pathHamiltonianPacketReference S T u center) t =
      unitaryEvolution (pathHamiltonianOnSites S u) t *
        unitaryEvolution (pathHamiltonianOnSites T center) t := by
  exact unitaryEvolution_add_of_isSiteSupported_disjoint hST
    (pathHamiltonianOnSites_isSiteSupported S u)
    (pathHamiltonianOnSites_isSiteSupported T center) t

end

end GaloisForLFunctions.HTGeometry
