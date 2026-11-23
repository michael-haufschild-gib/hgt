import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitDeletionBound
import GaloisForLFunctions.HTGeometry.SiteFactorLiftedSpectrum
import GaloisForLFunctions.HTGeometry.PathHamiltonianSiteRestriction
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.NearbySpectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-! # A spectral lower bound from the number of touched wires -/
open Matrix
open scoped Matrix.Norms.L2Operator Kronecker
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation
noncomputable section

/-- Every spectral point of a site-supported operator is a root of the
local characteristic polynomial, even if the operator is non-Hermitian. -/
theorem supported_spectrum_count {N m : ℕ} {S : Finset (Fin N)}
    {U : Matrix (Fin N → Bool) (Fin N → Bool) ℂ} (hU : IsSiteSupported S U)
    (f : Fin m → ℂ) (hi : Function.Injective f) (hf : ∀ i, f i ∈ spectrum ℂ U) :
    m ≤ 2^S.card := by
  classical
  let A := fun _ : Fin N => Bool
  obtain ⟨B,hB⟩ := exists_liftLocalMatrix_of_isSiteSupported hU
  let e := configurationSplitEquiv A S
  have hroot (i : Fin m) : f i ∈ B.charpoly.roots.toFinset := by
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots B.charpoly_monic.ne_zero).mpr
    have hu := Matrix.mem_spectrum_iff_isRoot_charpoly.mp (hf i)
    rw [Polynomial.IsRoot,Matrix.eval_charpoly,hB,←Matrix.det_reindex_self e,
      reindex_scalarSub_liftLocalMatrix,Matrix.det_kronecker,Matrix.det_one,one_pow,mul_one] at hu
    rw [Polynomial.IsRoot,Matrix.eval_charpoly]
    exact eq_zero_of_pow_eq_zero hu
  have hcard : m ≤ B.charpoly.roots.toFinset.card := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      (Finset.card_le_card_of_injOn f (fun i _ => hroot i) hi.injOn :
        (Finset.univ : Finset (Fin m)).card ≤ B.charpoly.roots.toFinset.card)
  apply hcard.trans (B.charpoly.roots.toFinset_card_le.trans ((Polynomial.card_roots' _).trans_eq ?_))
  simp [LocalConfiguration]

/-- A phase multiple of an s-gate circuit can contain at most 4^s
distinct spectral points, independently of the number of spectator wires. -/
theorem circuit_spectrum_count {N m : ℕ} (C : TwoQubitCircuit N) (z : ℂ)
    (f : Fin m → ℂ) (hi : Function.Injective f) (hf : ∀ i, f i ∈ spectrum ℂ (z • C.eval.val)) :
    m ≤ 4^C.gateCount := by
  apply (supported_spectrum_count (IsSiteSupported.complex_smul z C.isSiteSupported_touchedSites) f hi hf).trans
  calc 2^C.touchedSites.card ≤ 2^(2*C.gateCount) := Nat.pow_le_pow_right (by decide) C.card_touchedSites_le
       _ = _ := by rw [pow_mul]; rfl

/-- Each of m well-separated spectral points needs a distinct circuit
eigenvalue. This excludes all s-gate approximants when four to the
power s is smaller than m, at any tolerance strictly below r. -/
theorem circuit_exclusion_of_separated_spectrum {N m s : ℕ}
    (U : Matrix (Fin N → Bool) (Fin N → Bool) ℂ) (v : Fin m → ℂ)
    (hv : ∀ i, v i ∈ spectrum ℂ U) {ε r : ℝ} (hr : ε < r)
    (hsep : ∀ i j, i ≠ j → 2*r ≤ ‖v i-v j‖) (hm : 4^s < m) :
    ¬HasProjectiveCircuitApproximation N ε s U := by
  rintro ⟨z,_,C,hC,hfit⟩
  letI : CStarAlgebra (Matrix (Fin N → Bool) (Fin N → Bool) ℂ) := {}
  letI : IsStarNormal (z • C.eval.val) := by
    constructor
    change star (z • C.eval.val)*(z • C.eval.val)=(z • C.eval.val)*star (z • C.eval.val)
    rw [star_smul,smul_mul_smul_comm,smul_mul_smul_comm,C.eval.property.1,C.eval.property.2,mul_comm]
  obtain ⟨f,hi,hf⟩ := separated_spectrum_count v hv (hfit.trans_lt hr) hsep
  exact hm.not_ge ((circuit_spectrum_count C z f hi hf).trans (Nat.pow_le_pow_right (by decide) hC))

#print axioms circuit_spectrum_count
#print axioms circuit_exclusion_of_separated_spectrum
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation
