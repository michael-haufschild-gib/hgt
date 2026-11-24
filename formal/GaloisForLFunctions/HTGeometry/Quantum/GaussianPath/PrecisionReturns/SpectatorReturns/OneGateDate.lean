import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.GateFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.PartitionClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.OneGatePacket

/-! # Exact first-return exponent for one gate in a free basis -/

open Real Filter MeasureTheory Set Finset
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
open Winding.CollisionRank
noncomputable section

/-- On every typical fixed prefix, allowing a new basis at the date
of the fit changes the one-gate first-return exponent from D−2 to D−5.
Four equal-multiplicity packets attain the latter exponent. -/
theorem gaussian_one_gate_dates :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ a > (0:ℝ),
        Tendsto (fun ε => log (SpectralApproximation.firstVisit H a 1 ε)/log (1/ε))
          (𝓝[>] 0) (𝓝 ((2^N-5:ℕ):ℝ)) ∧
        Tendsto (fun ε => log (firstVisit H a 1 ε)/log (1/ε))
          (𝓝[>] 0) (𝓝 ((2^N-2:ℕ):ℝ)) := by
  classical
  filter_upwards [gaussian_free_basis_gate_floor,gaussian_partition_clock,
    gaussian_first_return_precision_exponent] with ω hfloor hpart hphys k
  intro N H a ha
  refine ⟨?_,(hphys k a ha 1 (by omega)).2.1⟩
  let I := Fin N → Bool
  let n := 2^N-5
  have hD : 8 ≤ (2:ℕ)^N := (by decide : 8 ≤ 2^3).trans
    (Nat.pow_le_pow_right (by decide) (by dsimp only [N]; omega))
  have hn : 0<n := by dsimp only [n]; omega
  have hcard : 4^1+(n+1) ≤ 2^N := by rw [pow_one]; dsimp only [n]; omega
  apply tendsto_order.mpr
  constructor
  · intro lo hlo
    filter_upwards [hfloor k a ha n 1 hn hcard lo hlo,self_mem_nhdsWithin] with ε hl (he : 0<ε)
    have hh := (SpectralApproximation.firstVisit_isLeast H a 1 he).1
    exact hl _ hh.1 hh.2
  intro hi hhi
  let A : Fin N := ⟨0,by dsimp only [N]; omega⟩
  let B : Fin N := ⟨1,by dsimp only [N]; omega⟩
  have hab : A≠B := fun he => Nat.zero_ne_one (congrArg Fin.val he)
  let f (i : I) := (i A,i B)
  have hsize : 2^N-Fintype.card (Bool×Bool)=n+1 := by
    rw [Fintype.card_prod,Fintype.card_bool]; dsimp only [n]; omega
  have hret := hpart k (Bool×Bool) f (two_bits_surjective A B hab) n hn hsize a ha hi hhi
  filter_upwards [hret,Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε ht he
  obtain ⟨t,hat,hu,p,hp,hnear⟩ := ht
  have hfit := one_gate_of_four_packets H A B hab p hp hnear
  have hfirst := SpectralApproximation.firstVisit_isLeast H a 1 he.1
  exact (div_le_div_of_nonneg_right (log_le_log (ha.trans_le hfirst.1.1) (hfirst.2 ⟨hat,hfit⟩))
    (log_pos ((one_lt_div he.1).mpr he.2)).le).trans_lt hu

#print axioms gaussian_one_gate_dates
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
