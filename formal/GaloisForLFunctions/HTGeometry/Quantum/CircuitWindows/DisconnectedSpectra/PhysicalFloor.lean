import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.DisconnectedSpectra.TensorObstruction
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.DisconnectedSpectra.Factorization
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # Every exact nonzero Gaussian evolution requires a connected circuit -/
open MeasureTheory Set Matrix Filter Topology
open scoped Kronecker Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.DisconnectedSpectra
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n→Bool) (Fin n→Bool) ℂ

private theorem unitary_reindex {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (q : I ≃ J) (U : Matrix.unitaryGroup I ℂ) :
    (Matrix.reindexAlgEquiv ℂ ℂ q) U.val∈Matrix.unitaryGroup J ℂ := by
  let Φ := Matrix.reindexAlgEquiv ℂ ℂ q
  have h := Unitary.mem_iff.mp U.2
  apply Unitary.mem_iff.mpr
  constructor
  · change Φ (star U.val)*Φ U.val=1
    rw [←map_mul,h.1,map_one]
  · change Φ U.val*Φ (star U.val)=1
    rw [←map_mul,h.2,map_one]

/-- On a positive compact time interval, one accuracy excludes every
circuit with fewer than N−1 gates, including circuits touching every
site. The accuracy may depend on the interval and the prefix. -/
theorem gaussian_disconnected_compact_floor :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ a b : ℝ, 0<a → a≤b → ∃ δ > 0, ∀ t∈Icc a b, ∀ s : ℕ, s+1<N →
        ¬HasProjectiveCircuitApproximation N δ s (unitaryEvolution H.val t) := by
  classical
  filter_upwards [gaussian_no_tensor_product] with ω hω k
  intro N H a b ha hab
  let s := N-2
  have hs : s+1<N := by dsimp [s,N]; omega
  have hd (t : ℝ) (ht : a≤t) : 0<orbitCircuitDistance H s t := by
    by_contra! hzero
    obtain ⟨z,hz,C,hC,he⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ s 0).mpr hzero
    have heq := sub_eq_zero.mp (norm_le_zero_iff.mp he)
    obtain ⟨S,hS,hB,hfac⟩ := disconnected_factor (show 3≤N by dsimp [N]; omega) C (by omega)
    obtain ⟨A,B,hAB⟩ := hfac
    let L := LocalConfiguration (fun _ : Fin N => Bool) S
    let R := OutsideConfiguration (fun _ : Fin N => Bool) S
    let m := Fintype.card L
    let n := Fintype.card R
    let el := Fintype.equivFin L
    let er := Fintype.equivFin R
    let q := (configurationSplitEquiv (fun _ : Fin N => Bool) S).trans (el.prodCongr er)
    let Φ := Matrix.reindexAlgEquiv ℂ ℂ q
    have hL : m=2^S.card := by simp [m,L,LocalConfiguration]
    have hR : n=2^Sᶜ.card := by simp [n,R,OutsideConfiguration,Fintype.card_subtype_compl,Finset.card_compl]
    have hm : 2 ≤ m := (show 2^1 ≤ 2^S.card from Nat.pow_le_pow_right (by decide) hS).trans_eq hL.symm
    have hn : 3 ≤ n := (by decide : 3≤2^2).trans
      ((Nat.pow_le_pow_right (by decide : 0<2) hB).trans_eq hR.symm)
    let α := Matrix.reindex el el A
    let β := Matrix.reindex er er B
    have hprod : Φ C.eval.val=α ⊗ₖ β := by
      change Matrix.reindex (el.prodCongr er) (el.prodCongr er)
        (Matrix.reindex (configurationSplitEquiv (fun _ : Fin N => Bool) S)
          (configurationSplitEquiv (fun _ : Fin N => Bool) S) C.eval.val)=_
      rw [hAB]
      rfl
    let U := H.2.isHermitian.eigenvectorUnitary
    let W : Matrix.unitaryGroup (Fin m × Fin n) ℂ := ⟨Φ U.val,unitary_reindex q U⟩
    let f := fun i => energyPhase t (H.2.isHermitian.eigenvalues i)
    have hdiag : Φ (diagonal f)=diagonal (fun i => f (q.symm i)) := by
      ext i j
      change (diagonal f) (q.symm i) (q.symm j)=_
      by_cases hh : i=j
      · subst j; simp
      · rw [diagonal_apply_ne _ (q.symm.injective.ne hh),diagonal_apply_ne _ hh]
    have hspec : Φ (unitaryEvolution H.val t)=W.val*diagonal (fun i => f (q.symm i))*star W.val := by
      rw [unitaryEvolution_spectral H.2.isHermitian]
      change Φ (U.val*diagonal f*star U.val)=_
      rw [map_mul,map_mul,hdiag]
      rfl
    apply hω k m n hm hn q.symm t (ha.trans_le ht).ne' (z • α) β W
    rw [Matrix.smul_kronecker,←hprod,←map_smul,←heq]
    exact hspec
  obtain ⟨t,ht,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab)
    (orbitCircuitDistance_lipschitz H s).continuous.continuousOn
  refine ⟨orbitCircuitDistance H s t/2,half_pos (hd t ht.1),?_⟩
  rintro u hu j hj ⟨z,hz,C,hC,he⟩
  have hfit := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val u) s _).mp
    ⟨z,hz,C,hC.trans (by dsimp [s]; omega),he⟩
  exact (half_lt_self (hd t ht.1)).not_ge ((hmin hu).trans hfit)

/-- Starting from any positive date on the sampled orbit, the elapsed
wait to a circuit of fewer than N−1 gates tends to infinity as the
tolerance tends to zero. This includes origins chosen after the draw. -/
theorem gaussian_disconnected_wait_diverges :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ a > 0, ∀ s : ℕ, s+1<N →
        Tendsto (fun ε => PrecisionReturns.firstVisit H a s ε-a) (𝓝[>] (0:ℝ)) atTop := by
  filter_upwards [gaussian_disconnected_compact_floor] with ω hω k
  intro N H a ha s hs
  refine tendsto_atTop.mpr fun M => ?_
  obtain ⟨δ,hδ,havoid⟩ := hω k a (max a (M+a)) ha (le_max_left ..)
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  let v := PrecisionReturns.firstVisit H a s ε
  obtain ⟨hav,z,hz,C,hC,he⟩ := (PrecisionReturns.firstVisit_isLeast H a s hε.1).1
  apply le_of_not_gt
  intro h
  exact havoid v ⟨hav,((sub_lt_iff_lt_add.mp h).le.trans (le_max_right ..))⟩ s hs
    ⟨z,hz,C,hC,he.trans hε.2.le⟩

#print axioms gaussian_disconnected_wait_diverges
#print axioms gaussian_disconnected_compact_floor
end
end GaloisForLFunctions.HTGeometry.DisconnectedSpectra
