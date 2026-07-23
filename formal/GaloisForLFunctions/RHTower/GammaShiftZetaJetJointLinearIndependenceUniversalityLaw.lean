import GaloisForLFunctions.RHTower.GammaShiftZetaJetFlag

/-!
# Gamma-shift/zeta-jet joint linear-independence universality

The eventual nonvanishing mixed Gamma/zeta Casoratian has a function-space consequence absent from
its determinant formulation: every finite packet of confluent jets at distinct Gamma shifts is
jointly linearly independent from every finite initial packet of Riemann-zeta jets.
-/

namespace GaloisForLFunctions.RHTower

open Filter Matrix

noncomputable section

/-- Combined function family formed from confluent jets at finite Gamma shifts and an initial
packet of Riemann-zeta jets. -/
def gammaZetaJetMixedFamily {r q : ℕ}
    (shift : Fin r → ℂ) (mult : Fin r → ℕ) :
    Fin (gammaJetOrder mult + q) → ℂ → ℂ :=
  Fin.addCases
    (fun a z => iteratedDeriv (gammaJetSlotOrder mult a) Complex.Gamma
      (z + shift (gammaJetSlotNode mult a)))
    (fun j z => iteratedDeriv (j : ℕ) riemannZeta z)

@[simp]
theorem gammaZetaJetMixedMatrix_apply_eq_mixedFamily {r q : ℕ}
    (s : ℂ) (shift : Fin r → ℂ) (mult : Fin r → ℕ)
    (row col : Fin (gammaJetOrder mult + q)) :
    gammaZetaJetMixedMatrix (q := q) s shift mult
        (fun (j : Fin q) z => iteratedDeriv (j : ℕ) riemannZeta z) row col =
      gammaZetaJetMixedFamily (q := q) shift mult col (s + (row : ℕ)) := by
  refine Fin.addCases ?_ ?_ col
  · intro a
    simp only [gammaZetaJetMixedMatrix, gammaZetaJetMixedFamily, Fin.addCases_left]
    congr 1
    ring
  · intro j
    simp [gammaZetaJetMixedMatrix, gammaZetaJetMixedFamily]

/-- **Gamma-shift/zeta-jet joint linear-independence universality law.** For arbitrary finite
distinct Gamma shifts, arbitrary confluent multiplicities, and arbitrary zeta-jet cutoff, the
combined functions are linearly independent over `ℂ`. The proof extracts one invertible evaluation
packet from the eventual mixed-determinant theorem; no pole-free hypothesis remains in the
function-space conclusion. -/
theorem gammaZetaJetMixedFamily_linearIndependent {r q : ℕ}
    (shift : Fin r → ℂ) (mult : Fin r → ℕ)
    (hshift : Function.Injective shift) :
    LinearIndependent ℂ (gammaZetaJetMixedFamily (q := q) shift mult) := by
  classical
  obtain ⟨x, hdet⟩ :=
    (gammaZetaJetMixedMatrix_det_ne_zero_eventually
      (q := q) shift mult hshift).exists
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hmul :
      (gammaZetaJetMixedMatrix (q := q) (x : ℂ) shift mult
        (fun (j : Fin q) z => iteratedDeriv (j : ℕ) riemannZeta z)).mulVec c = 0 := by
    funext row
    have hrow := congrFun hc ((x : ℂ) + (row : ℕ))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hrow
    simpa [Matrix.mulVec, dotProduct, mul_comm] using hrow
  have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  exact fun i => congrFun hc0 i

end

end GaloisForLFunctions.RHTower
