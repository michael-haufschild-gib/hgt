import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.LocalizedCuts.CoherentEcho.PhysicalBand
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.Passages.PowerBand

/-! # First robust passage at the coherent quartic onset -/
open Real MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open RepeatedGates.PhysicalBlocks
noncomputable section
private abbrev frozen (ω : PathPauliDisorder) (n : ℕ) :
    selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ) :=
  ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩

/-- The first passage after any affordable visit has fourth power at
most the larger of the coherent onset to the fourth power and the
excess gate fraction. Both estimates hold on one frozen chain. -/
theorem gaussian_coherent_first_passage :
    ∃ b>(0:ℝ), ∃ D>(0:ℝ), ∃ L>(0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N : ℝ := (n+1:ℕ)
      ∀ (v : ℝ) (r q : ℕ), let m : ℝ := (2*r+q:ℕ)
        m≤b*N →
        HasProjectiveCircuitApproximation (n+2) (1/10) r (unitaryEvolution (frozen ω n).val v) →
        ∀ ρ∈Icc (9/80:ℝ) (1/8),
          let τ := firstExcessAfter ω n (r+q) v ρ
          let f (x : ℝ) := orbitCircuitDistance (frozen ω n) (n+1+(r+q)) (v+x)
          τ∈Icc 0 1 ∧ τ^4≤ max ((D/N^9)^(4/49:ℝ)) (m/(b*N)) ∧ L≤((n+2:ℕ):ℝ)*τ^2 ∧
            f τ=ρ ∧ ∀ x∈Ico 0 τ, f x<ρ := by
  obtain ⟨b,hb,D,hD,hw⟩ := gaussian_coherent_quartic_band
  let s (n : ℕ) := (D/((n+1:ℕ):ℝ)^9)^(1/49:ℝ)
  have h := first_passage_of_power_band s (by decide : 4≠0) hb (by
    filter_upwards [hw] with ω hω
    filter_upwards [hω,eventually_ge_atTop ⌈D⌉₊] with n hn hk
    let N : ℝ := (n+1:ℕ)
    have hN : (1:ℝ)≤((n+1:ℕ):ℝ) := by exact_mod_cast (show 1≤n+1 from Nat.succ_le_succ (Nat.zero_le n))
    have hp : 0<N^9 := pow_pos (zero_lt_one.trans_le hN) _
    have hle : D≤N^9 := calc
      D ≤ (n:ℝ) := (Nat.le_ceil D).trans (Nat.cast_le.mpr hk)
      _ ≤ N := Nat.cast_le.mpr (Nat.le_succ n)
      _ ≤ _ := by simpa only [pow_one] using pow_le_pow_right₀ hN (by decide : 1≤9)
    have he : (s n)^49=D/N^9 := by
      change ((D/N^9)^(1/49:ℝ))^49=D/N^9
      rw [←rpow_natCast,←rpow_mul (div_pos hD hp).le,show (1/49:ℝ)*(49:ℕ)=1 by norm_num,rpow_one]
    have hs : 0<s n := rpow_pos_of_pos (div_pos hD hp) _
    refine ⟨hs,rpow_le_one (div_pos hD hp).le ((div_le_one hp).mpr hle) (by norm_num),?_⟩
    intro t ht
    have hh := pow_le_pow_left₀ hs.le ht.1 49
    rw [he] at hh
    exact hn t ⟨hs.trans_le ht.1,ht.2⟩ (by linarith only [(div_le_iff₀ hp).mp hh]))
  refine ⟨b,hb,D,hD,?_⟩
  have hpow (n : ℕ) : (s n)^4=(D/((n+1:ℕ):ℝ)^9)^(4/49:ℝ) := by
    dsimp only [s]
    rw [←rpow_natCast,←rpow_mul (by positivity)]
    norm_num
  simpa only [hpow] using h

#print axioms gaussian_coherent_first_passage
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
