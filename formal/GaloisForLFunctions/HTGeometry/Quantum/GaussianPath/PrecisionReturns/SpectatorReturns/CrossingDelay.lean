import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.ActiveWires
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.PhysicalDelay

/-! # Spectator and physical waiting times from the first robust crossing -/

open Filter Real MeasureTheory Set
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
noncomputable section

/-- From the same first robust crossing, the physical wait below the
spanning budget divided by the first b-active-wire wait in a free basis
has precision exponent 2ᵇ−1. The physical tolerance may be rescaled by
any constant on the fixed prefix. -/
theorem gaussian_wire_delay_at_crossing :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ > 0, orbitCircuitDistance H P σ=9/80 ∧
        (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
        ∀ b s : ℕ, b<N → s+1<N → ∀ c > (0:ℝ),
          Tendsto (fun ε => log ((firstVisit H σ s (c*ε)-σ)/(firstSupportedDate H σ b ε-σ))/log (1/ε))
            (𝓝[>] 0) (𝓝 ((2^b-1:ℕ):ℝ)) := by
  filter_upwards [gaussian_active_wire_date,DisconnectedReturns.gaussian_disconnected_crossing_first_wait]
    with ω hwire hcross
  filter_upwards [hcross] with k hk
  intro N H P
  obtain ⟨σ,hσ,hit,hbefore,hphys⟩ := hk
  refine ⟨σ,hσ,hit,hbefore,?_⟩
  intro b s hb hs c hc
  have hD : (2:ℕ)^N=2*2^(k+2) := by change 2^(k+2+1)=_; rw [pow_succ,Nat.mul_comm]
  have hp : (2:ℕ)^b ≤ 2^(k+2) := Nat.pow_le_pow_right (by decide) (by dsimp only [N] at hb; omega)
  have hM : 4 ≤ (2:ℕ)^(k+2) := (by decide : 4≤2^2).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hbpos : 0<(2:ℕ)^b := by positivity
  have h₁ : 0<((2^N-2:ℕ):ℝ) := by exact_mod_cast (show 0<2^N-2 by omega)
  have h₂ : 0<((2^N-2^b-1:ℕ):ℝ) := by exact_mod_cast (show 0<2^N-2^b-1 by omega)
  let U := fun ε => firstSupportedDate H σ b ε
  have hu := elapsed_exponent (v:=U) hσ h₂
    (fun ε he => (firstSupportedDate_isLeast H σ b he).1.1) (hwire k b hb σ hσ)
  have hv := Jumps.scaled_exponent hc (hphys s hs)
  have h := log_ratio_of_exponents h₁ h₂ hv hu
  have he : ((2^N-2:ℕ):ℝ)-((2^N-2^b-1:ℕ):ℝ)=((2^b-1:ℕ):ℝ) := by
    apply sub_eq_iff_eq_add.mpr
    exact_mod_cast (show 2^N-2=(2^b-1)+(2^N-2^b-1) by omega)
  rw [he] at h
  exact h

#print axioms gaussian_wire_delay_at_crossing
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
