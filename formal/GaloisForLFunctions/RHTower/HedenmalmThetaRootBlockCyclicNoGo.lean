import GaloisForLFunctions.RHTower.HedenmalmThetaSourceConormalSocle
import GaloisForLFunctions.RHTower.SymplecticCyclicObstruction

/-!
# Cyclic no-go for the fixed Hedenmalm theta carrier

A finite-dimensional nilpotent endomorphism with one-dimensional kernel has one complete Jordan
chain.  Here this is upgraded from the corpus's nilpotency-index statement to a literal cyclic
vector.  Since every nonzero root block of the fixed theta-source inverse has one-dimensional
kernel, every such block is cyclic.

Consequently the actual theta root-block operator cannot be self-adjoint for any nondegenerate
alternating bilinear form.  Functional-equation reflection pairs the distinct `mu` and `-mu`
blocks, but does not manufacture the second local channel required by Kramers degeneracy at one
spectral point.  This is a carrier-specific obstruction, not a parity or RH result.
-/

open Complex Module
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Coordinate-free one-chain criterion in cyclic-vector form.  Nilpotence and a
one-dimensional kernel produce a vector whose first `finrank` iterates form a basis. -/
theorem exists_cyclicVector_of_isNilpotent_of_finrank_ker_eq_one
    (N : Module.End ℂ V) (hN : IsNilpotent N)
    (hker : finrank ℂ (LinearMap.ker N) = 1) :
    ∃ v : V, CyclicVector N v := by
  let d := finrank ℂ V
  have hdimpos : 0 < d := by
    have hkerpos : 0 < finrank ℂ (LinearMap.ker N) := by omega
    exact lt_of_lt_of_le hkerpos (Submodule.finrank_le (LinearMap.ker N))
  have hpowd : N ^ d = 0 := by
    exact pow_finrank_eq_zero_of_isNilpotent N hN
  have htopne : N ^ (d - 1) ≠ 0 := by
    exact pow_finrank_sub_one_ne_zero_of_finrank_ker_eq_one N hker
  obtain ⟨v, hv⟩ : ∃ v : V, (N ^ (d - 1)) v ≠ 0 := by
    by_contra hall
    push Not at hall
    apply htopne
    ext x
    simpa using hall x
  let b : Fin d → V := fun i => (N ^ (i : ℕ)) v
  have hb : LinearIndependent ℂ b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    induction i using Fin.strong_induction_on with
    | h j ih =>
        have happ := congrArg (fun w => (N ^ (d - 1 - (j : ℕ))) w) hg
        have happ' :
            (∑ k : Fin d,
              g k • (N ^ (d - 1 - (j : ℕ) + (k : ℕ))) v) = 0 := by
          simpa [b, map_sum, map_smul, ← Module.End.mul_apply, ← pow_add] using happ
        have hsum :
            (∑ k : Fin d,
              g k • (N ^ (d - 1 - (j : ℕ) + (k : ℕ))) v) =
                g j • (N ^ (d - 1)) v := by
          classical
          calc
            (∑ k : Fin d,
                g k • (N ^ (d - 1 - (j : ℕ) + (k : ℕ))) v) =
                g j • (N ^ (d - 1 - (j : ℕ) + (j : ℕ))) v := by
              apply Finset.sum_eq_single j
              · intro k _ hkj
                by_cases hlt : k < j
                · rw [ih k hlt]
                  simp
                · have hjk : (j : ℕ) < (k : ℕ) := by omega
                  have hexp : d ≤ d - 1 - (j : ℕ) + (k : ℕ) := by omega
                  rw [pow_eq_zero_of_le hexp hpowd]
                  simp
              · simp
            _ = g j • (N ^ (d - 1)) v := by
              have hjd : (j : ℕ) < d := j.isLt
              rw [Nat.sub_add_cancel (Nat.le_sub_one_of_lt hjd)]
        rw [hsum] at happ'
        exact (smul_eq_zero.mp happ').resolve_right hv
  have hbtop : Submodule.span ℂ (Set.range b) = ⊤ :=
    hb.span_eq_top_of_card_eq_finrank' (by simp [d])
  refine ⟨v, ?_⟩
  rw [CyclicVector]
  apply top_unique
  rw [← hbtop]
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  exact ⟨(i : ℕ), rfl⟩

namespace HedenmalmThetaSource

/-- Every nonzero fixed theta-source root block has one complete Jordan channel. -/
theorem exists_cyclicVector_thetaRootNilpotentPart (mu : ThetaNonzeroSpectrum) :
    ∃ v : ThetaRootBlock mu, CyclicVector (thetaRootNilpotentPart mu) v :=
  exists_cyclicVector_of_isNilpotent_of_finrank_ker_eq_one
    (thetaRootNilpotentPart mu) (thetaRootNilpotentPart_isNilpotent mu)
    (finrank_ker_thetaRootNilpotentPart_eq_one mu)

/-- The fixed theta-source root block cannot itself realize the proposed Kramers/symplectic
doubling.  Any successful parity carrier must add genuinely new local arithmetic structure. -/
theorem thetaRootBlockOperator_not_symplectically_selfAdjoint
    (mu : ThetaNonzeroSpectrum) (omega : LinearMap.BilinForm ℂ (ThetaRootBlock mu))
    (hnd : omega.Nondegenerate) (halt : omega.IsAlt) :
    ¬ ∀ x y, omega (thetaRootBlockOperator mu x) y =
      omega x (thetaRootBlockOperator mu y) := by
  intro hK
  have hdimpos : 0 < finrank ℂ (ThetaRootBlock mu) := by
    have hkerpos : 0 < finrank ℂ (LinearMap.ker (thetaRootNilpotentPart mu)) := by
      rw [finrank_ker_thetaRootNilpotentPart_eq_one]
      omega
    exact lt_of_lt_of_le hkerpos
      (Submodule.finrank_le (LinearMap.ker (thetaRootNilpotentPart mu)))
  letI : Nontrivial (ThetaRootBlock mu) := Module.nontrivial_of_finrank_pos hdimpos
  have hN : ∀ x y, omega (thetaRootNilpotentPart mu x) y =
      omega x (thetaRootNilpotentPart mu y) := by
    intro x y
    change omega (thetaRootBlockOperator mu x - (mu : ℂ) • x) y =
      omega x (thetaRootBlockOperator mu y - (mu : ℂ) • y)
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply]
    rw [hK x y]
  obtain ⟨v, hv⟩ := exists_cyclicVector_thetaRootNilpotentPart mu
  exact not_cyclicVector_of_symplectic hnd halt hN v hv

end HedenmalmThetaSource

end

end RHTower
