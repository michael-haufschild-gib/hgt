import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EigenlineSignals.AnalyticSignal
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EigenlineSignals.ReflectionEcho
import GaloisForLFunctions.HTGeometry.Quantum.AttainedOrbitCircuitMaximum

/-! # All-pair information flow along the actual Gaussian orbit -/
open Matrix MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EigenlineSignals
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n→Bool) (Fin n→Bool) ℂ

/-- A spectral reflection can be approached on every maximally projective
prefix, including those shorter than a quantitative filling threshold. -/
private theorem marked_visit {N d : ℕ} (e : (Fin N→Bool) ≃ Fin (d+1))
    (H : selfAdjoint (Reg N)) (hi : MaximallyProjectiveEnergy H.property.isHermitian.eigenvalues)
    (j : Fin d) :
    let V := hermitianEigenbasisUnitary H.property.isHermitian
    let R := twist (-1) (marked V (e.symm j.succ))
    ∃ t z, ‖z‖=1 ∧ ‖R-z • unitaryEvolution H.val t‖ < 1/80 := by
  intro V R
  let E := fun i => H.property.isHermitian.eigenvalues (e.symm i)
  let x := anchoredBooleanProjectivePhase (fun i : Fin d => decide (i=j))
  have he : projectiveSpectralMatrix e V x=R :=
    (projectiveSpectralMatrix_anchoredBooleanProjectivePhase e V _).trans (single_reflection e V j)
  let S := (projectiveSpectralMatrix e V) ⁻¹' Metric.ball R (1/80)
  have hs : IsOpen S := Metric.isOpen_ball.preimage (continuous_projectiveSpectralMatrix e V)
  have hn : S.Nonempty := ⟨x,by change dist _ R < 1/80; rw [he,dist_self]; norm_num⟩
  obtain ⟨L,_,hh⟩ := denseAddOrbit_open_hits_syndetically (RHTower.projectivePhysicalPhaseFlowHom E)
    (RHTower.denseRange_projectivePhysicalPhaseFlowHom E (maximallyProjectiveEnergy_equiv e.symm hi)) hs hn
  obtain ⟨t,_,ht⟩ := hh 0
  let z := Complex.exp (-(Complex.I*(t*E 0)))
  have hz : ‖z‖=1 := by simp [z,Complex.norm_exp]
  refine ⟨t,z⁻¹,by simp [norm_inv,hz],?_⟩
  rw [move_phase _ _ _ hz,unitaryEvolution_eq_anchorPhase_smul_projectiveSpectralMatrix e H.property.isHermitian]
  change ‖z • _-z • R‖ < 1/80
  rw [←smul_sub,norm_smul,hz,one_mul]
  simpa only [S,mem_preimage,Metric.mem_ball,dist_eq_norm] using ht

/-- For each ordered pair of sites a fixed pair of onsite unitary probes
transmits at every time outside a locally finite set. Every prefix shares
the same full-measure set of physical coefficients. -/
theorem gaussian_all_pair_signals :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ i j : Fin N, i ≠ j → ∃ A B : Reg N, IsSiteSupported {i} A ∧ IsSiteSupported {j} B ∧
        A ∈ unitary _ ∧ B ∈ unitary _ ∧ ∀ a b : ℝ,
        (Icc a b ∩ {t | Commute (star (unitaryEvolution H.val t)*A*unitaryEvolution H.val t) B}).Finite := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω k
  intro N H i j hij
  let d := 2^N-1
  have hD : 1 < 2^N := one_lt_pow₀ (by norm_num) (by dsimp [N]; omega)
  let e : (Fin N→Bool) ≃ Fin (d+1) := (Fintype.equivFin _).trans (finCongr (by
    simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]; dsimp [d]; omega))
  let j₀ : Fin d := ⟨0,by dsimp [d]; omega⟩
  let V := hermitianEigenbasisUnitary H.property.isHermitian
  let r := e.symm j₀.succ
  let R : Matrix.unitaryGroup (Fin N→Bool) ℂ :=
    ⟨twist (-1) (marked V r),twist_unitary (marked_self V r) (marked_square V r) _ (by norm_num)⟩
  obtain ⟨u,z,hz,hclose⟩ := marked_visit e H (hω k) j₀
  obtain ⟨A,B,hs,ht,hA,hB,hsig⟩ := marked_chord_signal V r (-1) hij
  refine ⟨A,B,hs,ht,hA,hB,?_⟩
  apply finite_silent_dates H A B (u:=u)
  intro hcomm
  let U : Matrix.unitaryGroup (Fin N→Bool) ℂ := ⟨_,unitaryEvolution_mem_unitary H.property u⟩
  have he := SpanningDensity.projective_missing_signal_bound U R z hz A B
    (CStarRing.norm_of_mem_unitary hA).le (CStarRing.norm_of_mem_unitary hB).le hcomm
  have h := hsig.trans he
  change ‖1-(-1:ℂ)‖ ≤ 4*‖R.val-z • U.val‖ at h
  norm_num at h
  change ‖R.val-z • U.val‖ < 1/80 at hclose
  linarith only [h,hclose]

/-- Exact circuits below the all-pair communication count can occur only
at finitely many dates in any compact observation interval. -/
theorem gaussian_all_pair_exact_cost :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ a b : ℝ, (Icc a b ∩ {t | ∃ s < N-1+(N-1)/2,
        HasProjectiveCircuitApproximation N 0 s (unitaryEvolution H.val t)}).Finite := by
  classical
  filter_upwards [gaussian_all_pair_signals] with ω hω k
  intro N H a b
  let Pair := {p : Fin N×Fin N // p.1 ≠ p.2}
  have hp (p : Pair) := hω k p.val.1 p.val.2 p.property
  choose A B hA hB hu hv hf using hp
  let F (p : Pair) := Icc a b ∩ {t | Commute (star (unitaryEvolution H.val t)*A p*unitaryEvolution H.val t) (B p)}
  apply (Set.finite_iUnion (fun p : Pair => (show (F p).Finite from hf p a b))).subset
  rintro t ⟨ht,s,hs,z,hz,C,hC,herr⟩
  obtain ⟨i,j,hij,hm⟩ := RepeatedGates.missing_ordered_pair (by dsimp [N]; omega) C (hC.trans_lt hs)
  let p : Pair := ⟨(i,j),hij⟩
  refine Set.mem_iUnion.mpr ⟨p,ht,?_⟩
  let U : Matrix.unitaryGroup (Fin N→Bool) ℂ := ⟨_,unitaryEvolution_mem_unitary H.property t⟩
  have he := SpanningDensity.missing_signal_bound C U z hz (A p) (B p)
    (CStarRing.norm_of_mem_unitary (hu p)).le (CStarRing.norm_of_mem_unitary (hv p)).le
    (hm _ _ (hA p) (hB p))
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (he.trans (by linarith only [herr])))

#print axioms gaussian_all_pair_signals
#print axioms gaussian_all_pair_exact_cost
end
end GaloisForLFunctions.HTGeometry.EigenlineSignals
