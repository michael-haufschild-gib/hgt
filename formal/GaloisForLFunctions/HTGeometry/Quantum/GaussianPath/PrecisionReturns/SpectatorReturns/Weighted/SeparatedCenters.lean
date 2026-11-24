import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.Weighted.PacketFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.GateFloor

/-! # Separation of phase centers in the first packet-return window -/

open Filter Finset Set MeasureTheory Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns.Weighted
noncomputable section

/-- In the first precision window of a packet with m occupied centers,
no two centers can approach one another at a positive power of ε.
The assertion is simultaneous over times and assignments. -/
theorem gaussian_early_packet_separation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k n m : ℕ,
      let N := k+3
      let I := Fin N→Bool
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
      ∀ (_ : 0 < m), m+(n+1)=2^N → ∀ a β : ℝ, 0<a → 0<β → β≤1 →
        ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ t≥a, log t/log (1/ε)≤(n:ℝ)+β/2 →
          ∀ f : I→ℂ, (Finset.univ.image f).card ≤ m → (∀ i, ‖anchorPhase E i t-f i‖<2*ε) →
          (Finset.univ.image f).card = m ∧ ∀ i j, f i≠f j → ε^β<‖f i-f j‖ := by
  classical
  filter_upwards [gaussian_center_floor,gaussian_joined_gap_floor] with ω hfloor hjoin k n m
  intro N I E hm hD a β ha hβ hβ'
  let L := (n:ℝ)+β/2
  have hL : 0≤L := by dsimp only [L]; positivity
  have hL₁ : L<(n+1:ℕ) := by push_cast; dsimp only [L]; linarith only [hβ']
  have hLβ : L<(n:ℝ)+β := by dsimp only [L]; linarith only [hβ]
  have hsize : (m-1)+(n+1+1) ≤ 2^N := by omega
  have hc := hfloor k a ha (n+1) (m-1) (Nat.succ_pos _) hsize L hL₁
  have hj := hjoin k n a 3 β L ha (by norm_num) hβ hβ' hL hLβ
  filter_upwards [hc,hj,Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hc hj he
  intro t hat htime f hcount hnear
  have hcard : (Finset.univ.image f).card = m := by
    apply le_antisymm hcount
    by_contra! hlt
    exact htime.not_gt (hc t hat f (by omega) hnear)
  refine ⟨hcard,?_⟩
  intro i j hdiff
  by_contra! hclose
  have hdim : Fintype.card I=2^N := by simp only [I,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
  have hs : Fintype.card I-(Finset.univ.image f).card=n+1 := by rw [hdim,hcard]; omega
  have hh := enumerate_classes f
  dsimp only at hh
  rw [hs] at hh
  obtain ⟨rep,l,hrep,_,hi,hd,_⟩ := hh
  let r := fun a => rep (l a)
  have hxy : rep i≠rep j := fun h => hdiff ((hrep i).symm.trans ((congrArg f h).trans (hrep j)))
  apply htime.not_gt (hj l r (rep i) (rep j) hi (fun a b => hd _ _) hxy (hd i) (hd j) t hat ?_ ?_)
  · intro v
    have h := gap_of_shared_center E (l v) (r v) t (hnear (l v))
      (by rw [←hrep (l v)]; exact hnear (r v))
    exact ⟨h.choose,h.choose_spec.trans_le (by linarith only [he.1])⟩
  have hεβ : ε≤ε^β := by simpa only [rpow_one] using rpow_le_rpow_of_exponent_ge he.1 he.2.le hβ'
  have hpos := rpow_pos_of_pos he.1 β
  have h₁ := hnear (rep i)
  have h₂ := hnear (rep j)
  rw [hrep] at h₁ h₂
  have htri := norm_sub_le_norm_sub_add_norm_sub (anchorPhase E (rep j) t) (f j) (f i)
  rw [norm_sub_rev (f j) (f i)] at htri
  exact gap_of_shared_center E _ _ t (z:=f i) (by linarith only [h₁,hεβ,hpos])
    (by linarith only [h₂,hclose,htri,hεβ,hpos])

#print axioms gaussian_early_packet_separation
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns.Weighted
