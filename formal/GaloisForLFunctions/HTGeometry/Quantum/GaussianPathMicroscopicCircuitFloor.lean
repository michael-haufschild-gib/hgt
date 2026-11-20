import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathCoefficientMass
import GaloisForLFunctions.HTGeometry.Quantum.PathPauliSpectralWidth
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitDeletionBound
import GaloisForLFunctions.HTGeometry.AveragedCentralizerProjectionFloor

/-!
# An extensive gate floor in an inverse-bandwidth window

For one infinite iid Gaussian Pauli chain, almost surely all sufficiently
long open segments require linearly many gates on an interval of times
of order the inverse number of sites. Gate count uses arbitrary two-site
special unitaries, with a free global phase.
-/
open Matrix Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

private theorem path_norm_le_mass_bound {n : ℕ} (u : PathShell n) {b : ℝ}
    (hm : ‖u‖^2 ≤ b*((n+2:ℕ):ℝ)) :
    2 * ‖pathHamiltonian u‖ ≤ (12+b)*((n+2:ℕ):ℝ) := by
  let D : ℝ := Fintype.card (PathLabel n)
  have hD : D ≤ 12*((n+2:ℕ):ℝ) := by
    change ((Fintype.card (PathLabel n):ℕ):ℝ) ≤ _
    simp [PathLabel,Fintype.card_sum,Fintype.card_prod]
    linarith
  have hs : (Real.sqrt D)^2 = D := Real.sq_sqrt (Nat.cast_nonneg _)
  have ht : ‖pathHamiltonian u‖ ≤ Real.sqrt D * ‖u‖ := norm_pathHamiltonian_le u
  nlinarith only [hs,ht,sq_nonneg (Real.sqrt D - ‖u‖),hm,hD]

/-- Almost surely, all sufficiently long segments have a positive-width
interval on the inverse-system-size time scale on which every physical circuit accurate
to within one quarter needs at least a fixed fraction of the sites in
gates. The interval is centered at half the period of the spectral diameter. -/
theorem gaussian_path_microscopic_quarter_error_floor :
    ∃ A B W c : ℝ, 0 < A ∧ 0 < B ∧ 0 < W ∧ 0 < c ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
        let u := pathPauliDisorderShell ω n
        let N : ℝ := n+2
        let E := (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues
        ∃ i j, (∀ k l, E k - E l ≤ E i - E j) ∧
          let t := Real.pi/(E i - E j)
          A ≤ N*t ∧ N*t ≤ B ∧ ∀ τ : ℝ, N * |t-τ| ≤ W →
            ∀ (C : TwoQubitCircuit (n+2)) (z : ℂ),
              ‖unitaryEvolution (pathHamiltonian u) τ - z • (C.eval : Reg (n+2))‖ ≤ 1/4 →
                c*N ≤ C.gateCount := by
  obtain ⟨a,b,ha,hb,hall⟩ := gaussian_path_eventual_coefficient_mass
  let K := 12+b
  have hk : 0 < K := by dsimp [K]; linarith
  refine ⟨Real.pi/K,Real.pi/(2*a),1/(2*K),a^2/(168*Real.pi^2*b),
    div_pos Real.pi_pos hk,by positivity,by positivity,by positivity,?_⟩
  filter_upwards [hall] with ω hω
  filter_upwards [hω] with n hn
  let N : ℝ := n+2
  have hnpos : 0 < N := by dsimp [N]; positivity
  let u := pathPauliDisorderShell ω n
  let H := pathHamiltonian u
  let hH := (isSelfAdjoint_pathHamiltonian u).isHermitian
  let E := hH.eigenvalues
  have hm : ‖u‖^2 ≤ b*N := by simpa [u,N] using hn.2
  have hZ : a*N ≤ ∑ s : Fin (n+2), |u (.inl (s,2))| := by simpa [u,N] using hn.1
  have hnorm : 2*‖H‖ ≤ K*N := by simpa [K,N,H] using path_norm_le_mass_bound u hn.2
  obtain ⟨i,j,hlo,hmax⟩ := exists_path_spectral_width_ge_onsite u
  let d := E i - E j
  change 2 * _ ≤ d at hlo
  have hdlo : 2*a*N ≤ d := by linarith only [hZ,hlo]
  have hd : 0 < d := lt_of_lt_of_le (by positivity) hdlo
  have hdhi : d ≤ K*N := by
    have hi := (abs_le.mp (abs_eigenvalue_le_l2_opNorm hH i)).2
    have hj := (abs_le.mp (abs_eigenvalue_le_l2_opNorm hH j)).1
    change E i ≤ ‖H‖ at hi
    change -‖H‖ ≤ E j at hj
    dsimp [d]; linarith only [hi,hj,hnorm]
  let t := Real.pi/d
  refine ⟨i,j,hmax,?_,?_,?_⟩
  · change Real.pi/K ≤ N*(Real.pi/d)
    rw [← mul_div_assoc,div_le_div_iff₀ hk hd]
    nlinarith only [mul_le_mul_of_nonneg_left hdhi Real.pi_pos.le]
  · change N*(Real.pi/d) ≤ Real.pi/(2*a)
    rw [← mul_div_assoc,div_le_div_iff₀ hd (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_left hdlo Real.pi_pos.le]
  intro τ hτ C z herr
  change N*|t-τ| ≤ 1/(2*K) at hτ
  let e := ‖unitaryEvolution H t - z • (C.eval : Reg (n+2))‖
  have hspeed : ‖H‖*|t-τ| ≤ 1/4 := by
    have h := (le_div_iff₀ (show 0 < 2*K by positivity)).mp hτ
    nlinarith only [h,mul_le_mul_of_nonneg_right hnorm (abs_nonneg (t-τ))]
  have he : e ≤ 1/2 := by
    have hx := norm_sub_le_norm_sub_add_norm_sub (unitaryEvolution H t)
      (unitaryEvolution H τ) (z • (C.eval : Reg (n+2)))
    have hy := norm_unitaryEvolution_time_sub_le (isSelfAdjoint_pathHamiltonian u) t τ
    change ‖unitaryEvolution H t - unitaryEvolution H τ‖ ≤ ‖H‖*|t-τ| at hy
    change ‖unitaryEvolution H τ - z • (C.eval : Reg (n+2))‖ ≤ 1/4 at herr
    change e ≤ _ at hx
    linarith only [hx,hy,hspeed,herr]
  have hdef : 1/2 ≤ max 0 (1-e) := le_trans (by linarith only [he]) (le_max_right _ _)
  have hg := path_half_gap_gate_count_bound u i j C z
  change (max 0 (1-e) * |d|)^2 ≤ 168*Real.pi^2*C.gateCount*‖u‖^2 at hg
  rw [abs_of_pos hd] at hg
  have hdeficit : a*N ≤ max 0 (1-e)*d := by
    nlinarith only [hdlo,mul_le_mul_of_nonneg_right hdef hd.le]
  have hs := (pow_le_pow_left₀ (mul_nonneg ha.le hnpos.le) hdeficit 2).trans hg
  have hx := hs.trans (mul_le_mul_of_nonneg_left hm (by positivity))
  change a^2/(168*Real.pi^2*b)*N ≤ C.gateCount
  rw [div_mul_eq_mul_div₀,div_le_iff₀ (by positivity)]
  apply (mul_le_mul_iff_left₀ hnpos).mp
  linarith only [hx]

/-- Almost surely, all sufficiently long segments have a positive-width
interval on the inverse-system-size time scale on which every one-tenth
accurate physical circuit needs at least a fixed fraction of the sites in
gates. The interval is centered at half the period of the spectral diameter. -/
theorem gaussian_path_microscopic_circuit_floor :
    ∃ A B W c : ℝ, 0 < A ∧ 0 < B ∧ 0 < W ∧ 0 < c ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
        let u := pathPauliDisorderShell ω n
        let N : ℝ := n+2
        let E := (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues
        ∃ i j, (∀ k l, E k - E l ≤ E i - E j) ∧
          let t := Real.pi/(E i - E j)
          A ≤ N*t ∧ N*t ≤ B ∧ ∀ τ : ℝ, N * |t-τ| ≤ W →
            ∀ (C : TwoQubitCircuit (n+2)) (z : ℂ),
              ‖unitaryEvolution (pathHamiltonian u) τ - z • (C.eval : Reg (n+2))‖ ≤ 1/10 →
                c*N ≤ C.gateCount := by
  obtain ⟨A,B,W,c,hA,hB,hW,hc,h⟩ := gaussian_path_microscopic_quarter_error_floor
  refine ⟨A,B,W,c,hA,hB,hW,hc,?_⟩
  filter_upwards [h] with ω hω
  filter_upwards [hω] with n hn
  obtain ⟨i,j,hmax,hlo,hhi,hw⟩ := hn
  exact ⟨i,j,hmax,hlo,hhi,fun τ ht C z he => hw τ ht C z (he.trans (by norm_num))⟩

/-- For every time origin, circuits at the two ends of an inverse-bandwidth
lag pay an extensive total cost. A subextensive dip consequently has
extensive circuit cost in windows on both sides, at the same accuracy. -/
theorem gaussian_pauli_rebound_at_every_circuit_dip :
    ∃ A B W c : ℝ, 0 < A ∧ 0 < B ∧ 0 < W ∧ 0 < c ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
        let u := pathPauliDisorderShell ω n
        let N : ℝ := n+2
        let E := (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues
        ∃ i j, (∀ k l, E k-E l ≤ E i-E j) ∧
          let t := Real.pi/(E i-E j)
          A ≤ N*t ∧ N*t ≤ B ∧ ∀ τ : ℝ, N*|t-τ| ≤ W → ∀ v : ℝ, ∀ s r : ℕ,
            HasProjectiveCircuitApproximation (n+2) (1/10:ℝ) s (unitaryEvolution (pathHamiltonian u) v) →
            HasProjectiveCircuitApproximation (n+2) (1/10:ℝ) r (unitaryEvolution (pathHamiltonian u) (v+τ)) →
            c*N ≤ (s:ℝ)+r := by
  obtain ⟨A,B,W,c,hA,hB,hW,hc,h⟩ := gaussian_path_microscopic_quarter_error_floor
  refine ⟨A,B,W,c,hA,hB,hW,hc,?_⟩
  filter_upwards [h] with ω hω
  filter_upwards [hω] with n hn
  obtain ⟨i,j,hmax,hlo,hhi,hw⟩ := hn
  refine ⟨i,j,hmax,hlo,hhi,?_⟩
  intro τ ht v s r hv he
  let u := pathPauliDisorderShell ω n
  let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
  by_contra! hsmall
  have hh : ProjectiveCircuitSeparated (n+2) (1/4:ℝ) (r+s) (unitaryEvolution H.val τ) := by
    intro z _ C hC
    by_contra! happrox
    have hfloor := hw τ ht C z happrox
    have hcost : (C.gateCount:ℝ) ≤ (r:ℝ)+s := by exact_mod_cast hC
    linarith only [hfloor,hcost,hsmall]
  have hc' := projectiveCircuitSeparated_unitaryEvolution_backward_cone H
    (by omega : s ≤ r+s) hh (hv.neg_time H) (by norm_num : (1/10:ℝ)+1/10 ≤ 1/4)
  rw [show τ-(-v) = v+τ by ring,Nat.add_sub_cancel] at hc'
  obtain ⟨z,hz,C,hC,heC⟩ := he
  exact (not_lt_of_ge heC) (hc' z hz C hC)

#print axioms gaussian_path_microscopic_circuit_floor
#print axioms gaussian_pauli_rebound_at_every_circuit_dip
end
end GaloisForLFunctions.HTGeometry
