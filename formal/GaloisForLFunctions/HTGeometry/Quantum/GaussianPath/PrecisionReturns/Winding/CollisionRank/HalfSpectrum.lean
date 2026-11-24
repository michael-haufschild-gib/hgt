import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.CollisionRank.AdaptiveModuli

/-! # Half the spectrum modulo inverse precision at a first circuit return -/

open Filter Set Real MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.CollisionRank
open EmptyVisitFlux SharpOccupation
noncomputable section

/-- At every sufficiently accurate first visit by fewer than N−1 gates,
every modulus of size at least inverse precision distinguishes at least
half the Hilbert dimension in nonzero winding residues. -/
theorem gaussian_half_spectrum_residues :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let w := fun i => -H.2.isHermitian.eigenvalues i/(2*π)
      ∃ A > (0:ℝ), ∀ a > (0:ℝ), ∀ s : ℕ, s+1 < N →
        ∀ᶠ ε in 𝓝[>] (0:ℝ),
          let t := firstVisit H a s ε
          let R := physicalArc (A*ε)
          (∃ b z, Anchored w t R b z) ∧
            ∀ b z, Anchored w t R b z → ∀ d : ℕ, 1/ε ≤ (d:ℝ) →
              2^(k+2) ≤ (residues z d).card := by
  filter_upwards [gaussian_adaptive_modulus_rank] with ω hh k
  intro N H w
  obtain ⟨A,hA,h⟩ := hh k
  refine ⟨A,hA,?_⟩
  intro a ha s hs
  let M := 2^(k+2)
  let D := 2^N
  have hM : 2 ≤ M := (by decide : 2 ≤ 2^2).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hD : D = 2*M := by change 2^(k+2+1)=2*2^(k+2); rw [pow_succ,Nat.mul_comm]
  let n := M-1
  have hn : n+1=M := by dsimp only [n]; omega
  have hN : 0<n := by omega
  have hsize : n+2 ≤ D := by omega
  have hcast : ((D-2:ℕ):ℝ) = 2*(n:ℝ) := by exact_mod_cast (show D-2=2*n by omega)
  have hth : (((D-2:ℕ):ℝ)-(n:ℝ))/((n:ℝ)+1)<1 := by
    rw [hcast]
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith
  filter_upwards [h a ha s hs n hN hsize 1 hth,Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hh hε
  intro t R
  refine ⟨hh.1,?_⟩
  intro b z hz d hd
  have he : 1 < 1/ε := (one_lt_div hε.1).mpr hε.2
  have hd' : 0<d := Nat.cast_pos.mp (zero_lt_one.trans (he.trans_le hd))
  have hl : 1 ≤ log (d : ℝ) / log (1/ε) :=
    (le_div_iff₀ (log_pos he)).mpr (by simpa only [one_mul] using log_le_log (one_div_pos.mpr hε.1) hd)
  have hcard : D ≤ (residues z d).card+n+1 := hh.2 b z hz d hd' hl
  change M ≤ _
  omega

#print axioms gaussian_half_spectrum_residues
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.CollisionRank
