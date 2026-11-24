import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralArcs.GateLower
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralArcs.TwoDateUpper
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPauliPrefixPhaseLaw

/-! # Optimal common tolerance for two physical circuit visits at a fixed lag -/

open Real Set MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralArcs
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Smallest common error achievable arbitrarily closely by two visits,
the first at or after a and the second t later. -/
def pairError {n : ℕ} (H : selfAdjoint (Reg n)) (i j : ℕ) (a t : ℝ) :=
  sInf ((fun v => max (orbitCircuitDistance H i v) (orbitCircuitDistance H j (v+t))) '' Ici a)

theorem pairError_le {n : ℕ} (H : selfAdjoint (Reg n)) (i j : ℕ) {a v : ℝ} (hv : a≤v) (t : ℝ) :
    pairError H i j a t ≤ max (orbitCircuitDistance H i v) (orbitCircuitDistance H j (v+t)) := by
  let M := fun u => max (orbitCircuitDistance H i u) (orbitCircuitDistance H j (u+t))
  have hb : BddBelow (M '' Ici a) := ⟨0,fun _ ⟨u,_,hu⟩ => hu ▸
    (Metric.infDist_nonneg : 0 ≤ orbitCircuitDistance H i u).trans (le_max_left ..)⟩
  exact csInf_le hb ⟨v,hv,rfl⟩

/-- A strict margin above the infimum is realized by actual future dates. -/
theorem pairError_lt_iff {n : ℕ} (H : selfAdjoint (Reg n)) (i j : ℕ) (a t e : ℝ) :
    pairError H i j a t < e ↔ ∃ v ≥ a,
      orbitCircuitDistance H i v < e ∧ orbitCircuitDistance H j (v+t) < e := by
  let M := fun v => max (orbitCircuitDistance H i v) (orbitCircuitDistance H j (v+t))
  constructor
  · intro h
    obtain ⟨_,⟨v,ha,rfl⟩,hv⟩ := exists_lt_of_csInf_lt (s:=M '' Ici a) ⟨_,a,Set.mem_Ici.mpr (le_refl a),rfl⟩ h
    exact ⟨v,ha,(max_lt_iff.mp hv).1,(max_lt_iff.mp hv).2⟩
  · rintro ⟨v,hv,h₁,h₂⟩
    exact (pairError_le H i j hv t).trans_lt (max_lt h₁ h₂)

private theorem half_empty {n : ℕ} (H : selfAdjoint (Reg n)) (t : ℝ) :
    halfChord (orbitCircuitDistance H 0 t)=2*sin (orbitSpectralEnclosingArcLength H t/8) := by
  let L := orbitSpectralEnclosingArcLength H t
  have h₀ : 0≤L := spectralEnclosingArcLength_nonneg _
  have hπ : L<2*π := spectralEnclosingArcLength_lt_two_pi _
  rw [halfChord,orbitCircuitDistance_zeroGate_eq_enclosingArc]
  change 2*sin (arcsin (2*sin (L/4)/2)/2)=2*sin (L/8)
  rw [show 2*sin (L/4)/2=sin (L/4) by ring,
    arcsin_sin (by linarith only [h₀,pi_pos]) (by linarith only [hπ]),
    show L/4/2=L/8 by ring]

/-- The joint infimum lies between the bisected chords of the combined
gate budget and of the empty circuit at the lag itself. -/
theorem joint_bounds {n d : ℕ} (e : (Fin n→Bool) ≃ Fin (d+1))
    (H : selfAdjoint (Reg n)) (hm : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues)
    (i j : ℕ) (a t : ℝ) : pairError H i j a t ∈
      Icc (halfChord (orbitCircuitDistance H (i+j) t)) (halfChord (orbitCircuitDistance H 0 t)) := by
  let M := fun v => max (orbitCircuitDistance H i v) (orbitCircuitDistance H j (v+t))
  have hl (v) : halfChord (orbitCircuitDistance H (i+j) t) ≤ M v := halfChord_le_pair H i j v t
  have hb : BddBelow (M '' Ici a) := ⟨_,fun _ ⟨v,_,hv⟩ => hv ▸ hl v⟩
  refine ⟨le_csInf ⟨M a,⟨a,Set.mem_Ici.mpr (le_refl a),rfl⟩⟩ (fun _ ⟨v,_,hv⟩ => hv ▸ hl v),?_⟩
  apply le_of_forall_gt_imp_ge_of_dense
  intro ε he
  rw [half_empty] at he
  obtain ⟨_,_,h⟩ := syndetic_pair_above_half_arc e H hm t ε he
  obtain ⟨v,hv,h₁,h₂⟩ := h a
  exact (csInf_le hb ⟨v,hv.1,rfl⟩).trans (max_le
    ((budget_antitone H (Nat.zero_le i) v).trans h₁.le)
    ((budget_antitone H (Nat.zero_le j) (v+t)).trans h₂.le))

/-- Almost surely on every physical prefix with at least three sites,
the best common empty error over future pairs is exactly the bisected
spectral chord. All lags and observation origins share the same draw. -/
theorem gaussian_empty_pair :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let H : selfAdjoint (Reg (k+3)) := ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))⟩
      ∀ a t : ℝ, pairError H 0 0 a t=2*sin (orbitSpectralEnclosingArcLength H t/8) := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hh k
  intro H a t
  let N := k+3
  have hp : 0 < (2:ℕ)^N := by positivity
  let e := (qubitConfigFin N).trans (finCongr (show 2^N=2^N-1+1 by omega))
  have hb := joint_bounds e H (hh k) 0 0 a t
  exact (le_antisymm hb.2 hb.1).trans (half_empty H t)

#print axioms gaussian_empty_pair

/-- At the critical common tolerance √2 every prescribed lag occurs
between two strict empty fits, with bounded gaps in their starting dates. -/
theorem gaussian_pairs_at_sqrt_two :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let H : selfAdjoint (Reg (k+3)) := ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))⟩
      ∀ t : ℝ, ∃ G : ℝ, 0≤G ∧ ∀ a : ℝ, ∃ v∈Icc a (a+G),
        orbitCircuitDistance H 0 v < sqrt 2 ∧ orbitCircuitDistance H 0 (v+t) < sqrt 2 := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hh k
  intro H t
  let N := k+3
  have hp : 0 < (2:ℕ)^N := by positivity
  let e := (qubitConfigFin N).trans (finCongr (show 2^N=2^N-1+1 by omega))
  apply syndetic_pair_above_half_arc e H (hh k)
  let L := orbitSpectralEnclosingArcLength H t
  have h0 : 0≤L := spectralEnclosingArcLength_nonneg _
  have hL : L<2*π := spectralEnclosingArcLength_lt_two_pi _
  have hs : sin (L/8) < sin (π/4) := strictMonoOn_sin
    ⟨by linarith only [h0,pi_pos],by linarith only [hL,pi_pos]⟩
    ⟨by linarith only [pi_pos],by linarith only [pi_pos]⟩ (by linarith only [hL])
  rw [sin_pi_div_four] at hs
  change 2*sin (L/8)<sqrt 2
  linarith only [hs]

#print axioms gaussian_pairs_at_sqrt_two
end
end GaloisForLFunctions.HTGeometry.SpectralArcs
