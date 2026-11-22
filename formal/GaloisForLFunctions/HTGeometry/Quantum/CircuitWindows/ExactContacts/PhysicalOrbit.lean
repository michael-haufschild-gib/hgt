import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.ProbeBounds
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.PhasePolynomial
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.GaussianRate
import GaloisForLFunctions.HTGeometry.ProjectiveOperatorNormReturnTarget

/-! # Locally finite exact short-circuit dates on a fixed Gaussian trajectory -/
open Filter Set MeasureTheory Matrix MvPolynomial
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ExactContacts
noncomputable section
private abbrev State (n : ℕ) := Fin n→Bool
private abbrev Reg (n : ℕ) := Matrix (State n) (State n) ℂ

private theorem diag_probe {n : ℕ} (V M : Reg n) (j : State n) :
    (∑ p : State n × State n, (star V j p.1*V p.2 j)*M p.1 p.2)=(star V*M*V) j j := by
  rw [mul_assoc (star V) M V]
  simp only [Fintype.sum_prod_type,Matrix.mul_apply,Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

/-- A single nonzero polynomial in the relative phases has magnitude at
most Lε at every physical ε-visit, uniformly in the absolute date. -/
theorem orbit_probe_bound {n : ℕ} (H : selfAdjoint (Reg n)) (s : ℕ)
    (hs : s*16+1<2^n-1) :
    let E := H.2.isHermitian.eigenvalues
    let r : State n := fun _ => false
    let f := projectiveFrequency E r
    ∃ F : MvPolynomial {i // i≠r} ℂ, F≠0 ∧ ∃ L : ℝ, 0≤L ∧ ∀ t ε : ℝ,
      HasProjectiveCircuitApproximation n ε s (unitaryEvolution H.val t) →
        ‖aeval (fun i => energyPhase (f i) t) F‖ ≤ L*ε := by
  classical
  intro E r f
  let I := {i : State n // i≠r}
  let e := Fintype.equivFin I
  let V : Reg n := H.2.isHermitian.eigenvectorUnitary
  let j (i : Fin (Fintype.card I)) := (e.symm i).val
  let w (i : Fin (Fintype.card I)) (p : State n×State n) := star V (j i) p.1*V p.2 (j i)
  have hd : Fintype.card I=2^n-1 := by
    change Fintype.card {i : State n // ¬i=r}=_
    rw [Fintype.card_subtype_compl (fun i : State n => i=r),Fintype.card_subtype_eq]
    simp only [State,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
  obtain ⟨p,hp,L,hL,hbound⟩ := projective_gate_probe_bound s (hs.trans_eq hd.symm) w
  refine ⟨rename e.symm p,fun he => hp ((MvPolynomial.rename_injective e.symm e.symm.injective) (he.trans (map_zero _).symm)),L,hL,?_⟩
  intro t ε ht
  let U := unitaryEvolution H.val t
  have hVV : star V*V=1 := (Unitary.mem_iff.mp H.2.isHermitian.eigenvectorUnitary.2).1
  let D : Reg n := Matrix.diagonal (fun l => anchorPhase E l t)
  have hD : star V*unitaryEvolution H.val t*V=D := calc
    _ = star V*(V*D*star V)*V := by rw [unitaryEvolution_spectral H.2.isHermitian t]; rfl
    _ = (star V*V)*D*(star V*V) := by simp only [mul_assoc]
    _ = D := by rw [hVV,one_mul,mul_one]
  have hphase (i : Fin (Fintype.card I)) :
      (anchorPhase E r t)⁻¹*(∑ q, w i q*U q.1 q.2)=energyPhase (f (e.symm i)) t := calc
    _ = (anchorPhase E r t)⁻¹*(star V*unitaryEvolution H.val t*V) (j i) (j i) := by
      exact congrArg _ (diag_probe V U (j i))
    _ = (anchorPhase E r t)⁻¹*anchorPhase E (j i) t := by rw [hD]; simp only [D,Matrix.diagonal_apply_eq]
    _ = _ := by
      simp only [anchorPhase,energyPhase,←Complex.exp_neg,←Complex.exp_add]
      congr 1
      dsimp only [f,projectiveFrequency,j]
      push_cast
      ring
  rw [aeval_rename]
  have hh := hbound U ε (CStarRing.norm_of_mem_unitary (unitaryEvolution_mem_unitary H.2 t)).le ht
    (anchorPhase E r t)⁻¹ (by simp [anchorPhase,Complex.norm_exp])
  simpa only [hphase,Function.comp_def] using hh

/-- On each original Gaussian prefix with N≥3, all exact visits to at most
s gates, 16s<2ᴺ−1, form a finite set on every compact interval. -/
theorem gaussian_finite_exact_circuit_dates :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k s : ℕ, 16*s < 2^(k+3)-1 →
      let N := k+3
      let H := pathHamiltonian (pathPauliDisorderShell ω (k+1))
      ∀ a b : ℝ, {t∈Icc a b | HasProjectiveCircuitApproximation N 0 s (unitaryEvolution H t)}.Finite := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  intro k s hs N K a b
  let H : selfAdjoint (Reg N) := ⟨K,isSelfAdjoint_pathHamiltonian _⟩
  have hd : 2^(k+3)=2^k*8 := by rw [pow_add]; norm_num
  have hsize : s*16+1<2^N-1 := by dsimp only [N]; omega
  obtain ⟨F,hF,L,_,h⟩ := orbit_probe_bound H s hsize
  have hm := maximallyProjectiveEnergy_projectiveFrequency_independent _ (hω k) (fun _ => false)
  exact (finite_phase_zeros hm hF a b).subset fun t ht =>
    ⟨ht.1,norm_le_zero_iff.mp (by simpa only [mul_zero] using h t 0 ht.2)⟩

#print axioms gaussian_finite_exact_circuit_dates
end
end GaloisForLFunctions.HTGeometry.ExactContacts
