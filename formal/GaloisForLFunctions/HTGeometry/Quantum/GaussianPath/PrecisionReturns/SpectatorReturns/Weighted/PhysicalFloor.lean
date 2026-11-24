import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.Weighted.SeparatedCenters
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.ActiveWires
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.PhysicalDelay

/-! # Physical cost at the first return with spectators in a free basis -/

open Finset Filter Set Real MeasureTheory Matrix
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns.Weighted
noncomputable section

private theorem center_span {N : ℕ} (H : selfAdjoint (Register N)) {t ε δ : ℝ}
    (f : (Fin N→Bool)→ℂ) (hnear : ∀ i, ‖anchorPhase H.2.isHermitian.eigenvalues i t-f i‖ < 2*ε)
    (hfit : HasProjectiveCircuitApproximation N δ 0 (unitaryEvolution H.val t)) (i j : Fin N→Bool) :
    ‖f i-f j‖ ≤ 4*ε+2*δ := by
  obtain ⟨z,_,C,hc,hfit⟩ := hfit
  rw [zeroGateCircuit_eval C hc] at hfit
  let F i := anchorPhase H.2.isHermitian.eigenvalues i t
  have hz (a) : ‖F a-z‖ ≤ δ := (spectral_point_scalar_error_le H.2.isHermitian a t z).trans hfit
  have hdist (a) : ‖f a-z‖ ≤ 2*ε+δ := by
    apply (norm_sub_le_norm_sub_add_norm_sub (f a) (F a) z).trans
    rw [norm_sub_rev (f a)]; exact add_le_add (hnear a).le (hz a)
  have htri := norm_sub_le_norm_sub_add_norm_sub (f i) z (f j)
  rw [norm_sub_rev z] at htri
  linarith only [htri,hdist i,hdist j]

/-- Any early m-center fit with m > 1 excludes every disconnected physical
circuit at precision ε^β. Both its date and its phase assignment can vary. -/
theorem gaussian_physical_floor_in_packet_window :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k n m : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))⟩
      ∀ (_ : 1 < m), m+(n+1)=2^N → ∀ a β : ℝ, 0 < a → 0 < β →
        ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ t ≥ a, log t/log (1/ε) ≤ (n:ℝ)+min β 1/4 →
          ∀ f : (Fin N→Bool)→ℂ, (Finset.univ.image f).card ≤ m →
          (∀ i, ‖anchorPhase H.2.isHermitian.eigenvalues i t-f i‖ < 2*ε) →
          ∀ s : ℕ, HasProjectiveCircuitApproximation N (ε^β) s (unitaryEvolution H.val t) → N-1 ≤ s := by
  classical
  filter_upwards [gaussian_early_packet_separation,DisconnectedReturns.gaussian_disconnected_scalar_return]
    with ω hsep hdisc k n m
  intro N H hm hM a β ha hβ
  let α := min β 1/2
  have hα : 0 < α := half_pos (lt_min hβ zero_lt_one)
  have h₂ : 2*α=min β 1 := by dsimp only [α]; ring
  have hα' : α ≤ 1 := by linarith only [h₂,min_le_right β 1,hα]
  obtain ⟨A,hA,hcontrol⟩ := hdisc (k+1)
  have hsmall : Tendsto (fun ε : ℝ => (4+2*A)*ε^α) (𝓝[>] 0) (𝓝 0) := by
    have hh : ContinuousAt (fun ε : ℝ => (4+2*A)*ε^α) 0 :=
      continuousAt_const.mul (continuousAt_rpow_const 0 α (Or.inr hα.le))
    simpa only [zero_rpow hα.ne',mul_zero] using hh.tendsto.mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  filter_upwards [hsep k n m (by omega) hM a α ha hα hα',hsmall.eventually_lt_const zero_lt_one,
    Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hs hsmall he
  intro t hat ht f hcard hnear s hfit
  by_contra! hshort
  have hscalar := hcontrol t (ε^β) s (by dsimp only [N] at hshort; omega) hfit
  have heq : min β 1/4=α/2 := by dsimp only [α]; ring
  rw [heq] at ht
  obtain ⟨hc,hfar⟩ := hs t hat ht f hcard hnear
  have hmany : 1 < (Finset.univ.image f).card := by rw [hc]; exact hm
  obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp hmany
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
  have hwide := hfar i j hxy
  have hnarrow := center_span H f hnear hscalar i j
  have h₁ : ε ≤ ε^(2*α) := by rw [h₂]; simpa only [rpow_one] using
    rpow_le_rpow_of_exponent_ge he.1 he.2.le (min_le_right β 1)
  have hβ' : ε^β ≤ ε^(2*α) := by rw [h₂]; exact rpow_le_rpow_of_exponent_ge he.1 he.2.le (min_le_left β 1)
  have hsquare : ε^(2*α)=ε^α*ε^α := by rw [two_mul,rpow_add he.1]
  have hp := mul_le_mul_of_nonneg_right hsmall.le (rpow_nonneg he.1.le α)
  rw [one_mul, mul_assoc,←hsquare] at hp
  linarith only [hwide,hnarrow,h₁,mul_le_mul_of_nonneg_left hβ' hA.le,hp]


/-- At the first fit on a proper nonempty set of active wires in any
basis, the physical approximation still requires a spanning budget
even at every positive power of the free-basis error. -/
theorem gaussian_first_spectator_physical_floor :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))⟩
      ∀ a > (0:ℝ), ∀ b : ℕ, 0 < b → b < N → ∀ β > (0:ℝ), ∀ᶠ ε in 𝓝[>] (0:ℝ),
        let v := firstSupportedDate H a b ε
        ∀ s : ℕ, HasProjectiveCircuitApproximation N (ε^β) s (unitaryEvolution H.val v) → N-1 ≤ s := by
  classical
  filter_upwards [gaussian_physical_floor_in_packet_window,gaussian_active_wire_date]
    with ω hfloor hdate k
  intro N H a ha b hb hbN β hβ
  let m := 2^b
  let n := 2^N-m-1
  have hm : 1 < m := (by decide : 1 < 2^1).trans_le (Nat.pow_le_pow_right (by decide) hb)
  have hpow : 2^b ≤ (2:ℕ)^(k+2) := Nat.pow_le_pow_right (by decide) (by dsimp only [N] at hbN; omega)
  have hD : (2:ℕ)^N=2*2^(k+2) := by change 2^(k+2+1)=_; rw [pow_succ,Nat.mul_comm]
  have hM : m+(n+1)=2^N := by dsimp only [n,m]; omega
  have htime := (hdate k b hbN a ha).eventually_lt_const
    (lt_add_of_pos_right (n:ℝ) (div_pos (lt_min hβ zero_lt_one) (by norm_num : (0:ℝ) < 4)))
  filter_upwards [hfloor k n m hm hM a β ha hβ,htime,self_mem_nhdsWithin] with ε h ht (he : 0 < ε)
  intro v
  obtain ⟨hat,S,hS,V,B,hB,hfitB⟩ := (firstSupportedDate_isLeast H a b he).1
  obtain ⟨f,hcard,hnear⟩ := centers_of_supported_fit H v V hB (B.property.1.trans B.property.2.symm) he hfitB
  exact h v hat ht.le f (hcard.trans (Nat.pow_le_pow_right (by decide) hS)) hnear

/-- At the actual first one-gate date with a free basis, even loosening
the physical error to any positive power of ε requires at least N−1 gates. -/
theorem gaussian_first_one_gate_physical_floor :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))⟩
      ∀ a > (0:ℝ), ∀ β > (0:ℝ), ∀ᶠ ε in 𝓝[>] (0:ℝ),
        let v := SpectralApproximation.firstVisit H a 1 ε
        ∀ s : ℕ, HasProjectiveCircuitApproximation N (ε^β) s (unitaryEvolution H.val v) → N-1 ≤ s := by
  filter_upwards [gaussian_physical_floor_in_packet_window,gaussian_one_gate_dates] with ω hfloor hdate k
  intro N H a ha β hβ
  let n := 2^N-5
  have hD : 8 ≤ (2:ℕ)^N := (by decide : 8 ≤ 2^3).trans (Nat.pow_le_pow_right (by decide) (by dsimp only [N]; omega))
  have hM : 4+(n+1)=2^N := by dsimp only [n]; omega
  have htime := (hdate k a ha).1.eventually_lt_const
    (lt_add_of_pos_right (n:ℝ) (div_pos (lt_min hβ zero_lt_one) (by norm_num : (0:ℝ) < 4)))
  filter_upwards [hfloor k n 4 (by decide) hM a β ha hβ,htime,self_mem_nhdsWithin] with ε h ht (he : 0 < ε)
  intro v
  obtain ⟨hat,V,z,hz,C,hC,hfit⟩ := (SpectralApproximation.firstVisit_isLeast H a 1 he).1
  obtain ⟨f,hcard,hnear⟩ := centers_of_fit H v V C z he hfit
  have hle : 4^C.gateCount ≤ 4 := by
    simpa only [pow_one] using (show 4^C.gateCount ≤ 4^1 from Nat.pow_le_pow_right (by decide) hC)
  exact h v hat ht.le f (hcard.trans hle) hnear

#print axioms gaussian_first_spectator_physical_floor
#print axioms gaussian_first_one_gate_physical_floor
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns.Weighted
