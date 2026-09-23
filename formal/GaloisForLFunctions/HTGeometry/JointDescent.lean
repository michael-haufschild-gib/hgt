/-
# Descending the joint criticality product to the shell coordinates

The algebra equivalence between the joint ring and the iterated one intertwines relabelling of the
spectral variables with relabelling of the outer variables.  The criticality product is invariant
under the former, hence symmetric as an iterated polynomial, hence -- by the trace representation --
the evaluation of a single real polynomial in the shell coordinates.

Main results:
* `rename_sumAlgEquiv` — the equivalence intertwines the two relabellings.
* `isSymmetric_sumAlgEquiv_jointCriticalProduct` — the descended product is symmetric.
* `exists_shellPoly_jointCriticalProduct` — **the shell polynomial of the criticality product**.
-/
import GaloisForLFunctions.HTGeometry.JointCriticalSymmetry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

/-- The equivalence intertwines relabelling of the spectral variables with relabelling of the outer
variables. -/
theorem rename_sumAlgEquiv (τ : Equiv.Perm (Fin D)) (B : MvPolynomial (Fin D ⊕ Fin N) ℝ) :
    MvPolynomial.rename (τ : Fin D → Fin D)
        ((MvPolynomial.sumAlgEquiv ℝ (Fin D) (Fin N)) B)
      = (MvPolynomial.sumAlgEquiv ℝ (Fin D) (Fin N))
          (MvPolynomial.rename (Sum.map (τ : Fin D → Fin D) (id : Fin N → Fin N)) B) := by
  induction B using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p x hp =>
      rcases x with j | a
      · simp [hp]
      · simp [hp]

/-- The descended criticality product is symmetric in the spectral variables. -/
theorem isSymmetric_sumAlgEquiv_jointCriticalProduct (M : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ)
    (k : Fin D → ℝ) :
    ((MvPolynomial.sumAlgEquiv ℝ (Fin D) (Fin N)) (jointCriticalProduct M c k)).IsSymmetric := by
  intro τ
  rw [rename_sumAlgEquiv, rename_sumMap_jointCriticalProduct]

/-- **The shell polynomial of the criticality product.**  Its value at a coordinate vector is the
joint product evaluated at that vector and at the spectrum it determines. -/
theorem exists_shellPoly_jointCriticalProduct {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (M : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) (k : Fin D → ℝ) :
    ∃ G : MvPolynomial (Fin N) ℝ, ∀ θ : Fin N → ℝ,
      MvPolynomial.eval θ G
        = MvPolynomial.eval
            (Sum.elim (fun i => (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i) θ)
            (jointCriticalProduct M c k) := by
  obtain ⟨G, hG⟩ := exists_shellPoly_of_isSymmetric_over hP
    ((MvPolynomial.sumAlgEquiv ℝ (Fin D) (Fin N)) (jointCriticalProduct M c k))
    (isSymmetric_sumAlgEquiv_jointCriticalProduct M c k)
  refine ⟨G, fun θ => ?_⟩
  rw [← hG θ, eval_sumAlgEquiv_jointGradingBridge]

end

end GaloisForLFunctions.HTGeometry
