import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.GapClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.Classes
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.PhaseCenters
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.CollisionRank.GaussianForest

/-! # A first collision for every prescribed partition of the physical spectrum -/

open Real Filter MeasureTheory Set Finset
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
open Winding.CollisionRank
noncomputable section

/-- For any surjective coloring of the D energy levels by m colors, the
spectrum comes within ε of a packet constant on each color before every
precision exponent greater than D−m−1. -/
theorem gaussian_partition_clock :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
      ∀ (J : Type) [Fintype J] (f : (Fin N→Bool) → J), Function.Surjective f →
        ∀ n : ℕ, 0<n → 2^N-Fintype.card J=n+1 → ∀ a > (0:ℝ), ∀ hi > (n:ℝ),
          ∀ᶠ ε in 𝓝[>] (0:ℝ), ∃ t ≥ a, log t/log (1/ε) < hi ∧ ∃ p : J → ℂ,
            (∀ b, ‖p b‖=1) ∧ ∀ i, ‖anchorPhase E i t-p (f i)‖≤ε := by
  classical
  filter_upwards [gaussian_forest_ratios,gaussian_path_all_prefixes_maximally_projective] with ω hF hsimple k
  intro N E J _ f hsur n hn hD a ha hi hhi
  let I := Fin N → Bool
  have hsize : Fintype.card I-(Finset.univ.image f).card=n+1 := by
    rw [Finset.image_univ_of_surjective hsur,card_univ]
    simpa only [I,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] using hD
  choose config hinv using hsur
  have hh := enumerate_classes f
  dsimp only at hh
  rw [hsize] at hh
  obtain ⟨rep,l,_,hrep,hli,hd,hex⟩ := hh
  let root := fun j => rep (l j)
  let g := fun j => E (l j)-E (root j)
  have hdis (i j) : root i≠l j := hd _ _
  have hg : g 0≠0 := fun he => hdis 0 0 ((hsimple k).injective (sub_eq_zero.mp he)).symm
  have hy := hF k n l root hn hli hdis
  let K := 1/(2*π)
  have hK : 0<K := one_div_pos.mpr two_pi_pos
  have hret := optimal_gap_window hn g hg hy ha hK (Nat.cast_pos.mpr hn) hhi
  filter_upwards [hret,self_mem_nhdsWithin] with ε ht (he : 0<ε)
  obtain ⟨t,hat,hr,hu⟩ := ht.2
  let p := fun b => anchorPhase E (rep (config b)) t
  refine ⟨t,hat,hu,p,(fun _ => by simp [p,anchorPhase,Complex.norm_exp]),?_⟩
  intro i
  change ‖anchorPhase E i t-anchorPhase E (rep (config (f i))) t‖≤ε
  rw [hrep _ _ (hinv (f i))]
  rcases hex i with h|⟨j,rfl⟩
  · rw [←h,sub_self,norm_zero]; exact he.le
  · have hb := chord_of_gap E (l j) (rep (l j)) t (hr j)
    have heq : 2*π*(K*ε)=ε := by dsimp only [K]; field_simp [pi_ne_zero]
    exact hb.trans_eq heq

#print axioms gaussian_partition_clock
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
