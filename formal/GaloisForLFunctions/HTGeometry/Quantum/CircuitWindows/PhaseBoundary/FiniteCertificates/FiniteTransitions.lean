import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.OrbitContacts
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.SpectralFlow
import GaloisForLFunctions.HTGeometry.RealAnalyticZeroFiniteness

/-! # Locally finite transitions at every positive physical circuit-distance level -/

open Set Metric Filter Topology Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
noncomputable section

private theorem analytic_entryEval {N d : ℕ} (e : Bits N ≃ Fin (d+1)) (H : selfAdjoint (Square (Bits N)))
    (p : EntryPolynomial N ℝ) : AnalyticOnNhd ℝ (fun t => entryEval (RingHom.id ℝ) (relativeOrbit e H t) p) univ := by
  let κ := RingHom.id ℝ
  have coord (k : Bits N × Bits N × Bool) :
      AnalyticOnNhd ℝ (fun t => entryEval κ (relativeOrbit e H t) (MvPolynomial.X k)) univ := by
    obtain ⟨i,j,b⟩ := k
    have ha := spectral_entries_analytic e (hermitianEigenbasisUnitary H.2.isHermitian)
      (H.2.isHermitian.eigenvalues ∘ e.symm) 0 i j
    simp only [add_zero] at ha
    cases b
    · simpa only [entryEval,MvPolynomial.eval₂Hom_X',Bool.false_eq_true,if_false,relativeOrbit] using ha.1
    · simpa only [entryEval,MvPolynomial.eval₂Hom_X',if_true,relativeOrbit] using ha.2
  induction p using MvPolynomial.induction_on with
  | C r => simp only [entryEval,MvPolynomial.eval₂Hom_C]; exact analyticOnNhd_const
  | add p q hp hq => simpa only [map_add,Pi.add_def] using hp.add hq
  | mul_X p i hp => simpa only [map_mul,Pi.mul_def] using hp.mul (coord i)

/-- A fixed finite family of nontrivial polynomial tests over the coefficient ring covers
the entire frontier of the physical distance level. -/
theorem orbit_level_tests {R : Type*} [CommRing R] (κ : R →+* ℝ) {N d : ℕ} (e : Bits N ≃ Fin (d+1)) (H : selfAdjoint (Square (Bits N)))
    (s : ℕ) (r : R) (hε : 0<κ r) :
    let ev (t : ℝ) := entryEval κ (relativeOrbit e H t)
    ∃ F : Finset (EntryPolynomial N R), (∀ p∈F, ∃ u, ev u p≠0) ∧
      ∀ t∈frontier {u | orbitCircuitDistance H s u=κ r}, ∃ p∈F, ev t p=0 := by
  let f := orbitCircuitDistance H s
  have hc : Continuous f := (orbitCircuitDistance_lipschitz H s).continuous
  obtain ⟨F,hF,hzero⟩ := matrix_level_equations κ _ (continuous_relativeOrbit e H) s r
  refine ⟨F,hF,?_⟩
  intro t hfront
  have he : f t=κ r := frontier_subset_iff_isClosed.mpr (isClosed_eq hc continuous_const) hfront
  have near : t∈closure {u | 0<f u ∧ f u≠κ r} := by
    have hoff : ∃ᶠ u in 𝓝 t, f u≠κ r := by
      exact not_eventually.mp (fun h => hfront.2 (mem_interior_iff_mem_nhds.mpr h))
    exact mem_closure_iff_frequently.mpr (hoff.and_eventually
      (hc.continuousAt.eventually (lt_mem_nhds (hε.trans_eq he.symm))) |>.mono (fun _ h => ⟨h.2,h.1⟩))
  exact hzero t ((infDist_relativeOrbit ..).trans he) (by
    simpa only [infDist_relativeOrbit] using near)

/-- All changes into or out of a fixed distance level form a finite set
on each compact time interval. The Hamiltonian can have repeated or
resonant energies, and the contact can have any order of tangency. -/
theorem finite_level_frontier {N : ℕ} (H : selfAdjoint (Square (Bits N))) (s : ℕ) {ε : ℝ}
    (hε : 0<ε) (a b : ℝ) : (Icc a b ∩ frontier {t | orbitCircuitDistance H s t=ε}).Finite := by
  classical
  let d := 2^N-1
  let e : Bits N ≃ Fin (d+1) := (Fintype.equivFin _).trans (finCongr (by
    have hn := Nat.two_pow_pos N
    simp only [Bits,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
    dsimp only [d]; omega))
  let ev (t : ℝ) := entryEval (RingHom.id ℝ) (relativeOrbit e H t)
  obtain ⟨F,hF,hzero⟩ := orbit_level_tests (RingHom.id ℝ) e H s ε hε
  have hf (p) (hp : p∈F) : (Icc a b ∩ (fun t => ev t p) ⁻¹' {0}).Finite := by
    obtain ⟨v,hv⟩ := hF p hp
    exact finite_zeros_of_analyticOnNhd isPreconnected_univ (analytic_entryEval e H p)
      (mem_univ v) hv isCompact_Icc (subset_univ _)
  apply (F.finite_toSet.biUnion hf).subset
  rintro t ⟨ht,hfront⟩
  obtain ⟨p,hp,hp0⟩ := hzero t hfront
  exact mem_iUnion.mpr ⟨p,mem_iUnion.mpr ⟨hp,ht,hp0⟩⟩

#print axioms finite_level_frontier
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
