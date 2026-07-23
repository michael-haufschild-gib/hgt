import GaloisForLFunctions.RHTower.GammaShiftZetaJetFlag

/-!
# Gamma-shift/Dirichlet-series joint linear-independence universality

The eventual augmented Gamma/Dirichlet determinant forces a global function-space statement: any
Dirichlet series whose coefficient sequence has a finite first nonzero term is jointly linearly
independent from every finite confluent packet at distinct Gamma shifts.
-/

namespace GaloisForLFunctions.RHTower

open Matrix

noncomputable section

/-- Combined family of confluent shifted-Gamma jets and one supplied function. -/
def gammaJetDirichletMixedFamily {r : ℕ}
    (shift : Fin r → ℂ) (mult : Fin r → ℕ) (D : ℂ → ℂ) :
    Fin (gammaJetOrder mult + 1) → ℂ → ℂ :=
  fun col => Fin.lastCases D
    (fun a z => iteratedDeriv (gammaJetSlotOrder mult a) Complex.Gamma
      (z + shift (gammaJetSlotNode mult a))) col

@[simp]
theorem gammaJetAugmentedMatrix_apply_eq_mixedFamily {r : ℕ}
    (s : ℂ) (shift : Fin r → ℂ) (mult : Fin r → ℕ) (D : ℂ → ℂ)
    (row col : Fin (gammaJetOrder mult + 1)) :
    gammaJetAugmentedMatrix s shift mult D row col =
      gammaJetDirichletMixedFamily shift mult D col (s + (row : ℕ)) := by
  refine Fin.lastCases ?_ ?_ col
  · simp [gammaJetAugmentedMatrix, gammaJetDirichletMixedFamily]
  · intro a
    simp only [gammaJetAugmentedMatrix, gammaJetDirichletMixedFamily,
      Fin.lastCases_castSucc]
    congr 1
    ring

/-- **Gamma-shift/Dirichlet-series joint linear-independence universality law.** If `c (a + 1)` is
the first nonzero Dirichlet coefficient and the absolute-convergence abscissa is finite, its
`LSeries` is jointly linearly independent from all prescribed confluent jets at arbitrary finite
distinct Gamma shifts. Eventual determinant nonvanishing supplies an invertible consecutive-value
packet, leaving no analytic side condition in the function-space conclusion. -/
theorem gammaJetLSeriesMixedFamily_linearIndependent {r : ℕ}
    (c : ℕ → ℂ) (a : ℕ) (hzero : ∀ m ≤ a, c m = 0) (ha : c (a + 1) ≠ 0)
    (hc : LSeries.abscissaOfAbsConv c < ⊤)
    (shift : Fin r → ℂ) (mult : Fin r → ℕ)
    (hshift : Function.Injective shift) :
    LinearIndependent ℂ
      (gammaJetDirichletMixedFamily shift mult (fun z => LSeries c z)) := by
  classical
  obtain ⟨x, hdet⟩ :=
    (gammaJetAugmentedMatrix_LSeries_det_ne_zero_eventually
      c a hzero ha hc shift mult hshift).exists
  rw [Fintype.linearIndependent_iff]
  intro coeff hcoeff
  have hmul :
      (gammaJetAugmentedMatrix (x : ℂ) shift mult
        (fun z => LSeries c z)).mulVec coeff = 0 := by
    funext row
    have hrow := congrFun hcoeff ((x : ℂ) + (row : ℕ))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hrow
    simpa [Matrix.mulVec, dotProduct, mul_comm] using hrow
  have hc0 : coeff = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  exact fun i => congrFun hc0 i

end

end GaloisForLFunctions.RHTower
