import GaloisForLFunctions.HTGeometry.AllJetLevelSet
import GaloisForLFunctions.HTGeometry.CoordDerivChainRule

/-!
# The shift of a jet relation

Differentiating a polynomial relation among the phase jets replaces each jet by
its successor, weighted by the corresponding partial derivative.  That
operation is itself a polynomial operation: the *jet shift* of a relation in
`N` jets is a relation in `N + 1` jets.

The shift preserves the leading coefficient: the partial derivative of the
shifted relation with respect to its top variable is the renamed partial
derivative of the original relation with respect to its own top variable.  So a
relation whose separant does not vanish at a point produces an infinite family
of relations, one for each jet, all with nonvanishing leading coefficient at
that point.
-/

open Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-- The jet shift of a polynomial relation. -/
private def jetShift {N : ℕ} (Q : MvPolynomial (Fin N) ℂ) :
    MvPolynomial (Fin (N + 1)) ℂ :=
  ∑ i : Fin N, MvPolynomial.rename Fin.castSucc (MvPolynomial.pderiv i Q)
    * MvPolynomial.X i.succ

/-- **The jet shift computes the derivative of a jet relation.** -/
theorem jetRelationEval_jetShift {U : Set (d → ℂ)} (omega : d → ℝ)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F U) {N : ℕ}
    (Q : MvPolynomial (Fin N) ℂ) {z : d → ℂ} (hz : z ∈ U) :
    jetRelationEval omega F (jetShift Q) z
      = torusDerivation omega (jetRelationEval omega F Q) z := by
  rw [torusDerivation_jetRelationEval omega hF Q hz, jetRelationEval, jetShift,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_rename]
  rfl

/-- **The jet shift preserves the leading coefficient.** -/
theorem pderiv_last_jetShift {N : ℕ} (Q : MvPolynomial (Fin (N + 1)) ℂ) :
    MvPolynomial.pderiv (Fin.last (N + 1)) (jetShift Q)
      = MvPolynomial.rename Fin.castSucc
          (MvPolynomial.pderiv (Fin.last N) Q) := by
  classical
  have hzero : ∀ R : MvPolynomial (Fin (N + 1)) ℂ,
      MvPolynomial.pderiv (Fin.last (N + 1))
        (MvPolynomial.rename Fin.castSucc R) = 0 := by
    intro R
    refine MvPolynomial.pderiv_eq_zero_of_notMem_vars fun hmem => ?_
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ _ hmem)
    exact Fin.castSucc_ne_last a ha
  rw [jetShift, map_sum, Finset.sum_eq_single (Fin.last N)]
  · rw [Derivation.leibniz, MvPolynomial.pderiv_X, hzero, smul_zero, add_zero,
      Fin.succ_last, Pi.single_apply, if_pos rfl, smul_eq_mul, mul_one]
  · intro i _ hi
    have hne : i.succ ≠ Fin.last (N + 1) := by
      intro hcon
      rw [← Fin.succ_last] at hcon
      exact hi (Fin.succ_injective _ hcon)
    rw [Derivation.leibniz, MvPolynomial.pderiv_X, hzero, smul_zero, add_zero,
      Pi.single_apply, if_neg hne, smul_zero]
  · intro hj
    exact absurd (Finset.mem_univ (Fin.last N)) hj

/-- Iterating the jet shift, keeping the top index visible. -/
def jetShiftIter : ∀ (m : ℕ) {N : ℕ}, MvPolynomial (Fin (N + 1)) ℂ →
    MvPolynomial (Fin (N + m + 1)) ℂ
  | 0, _, Q => Q
  | m + 1, _, Q => jetShift (jetShiftIter m Q)

theorem jetShiftIter_succ {N m : ℕ} (Q : MvPolynomial (Fin (N + 1)) ℂ) :
    jetShiftIter (m + 1) Q = jetShift (jetShiftIter m Q) := rfl

/-- **All shifts of a vanishing relation vanish.** -/
theorem jetRelationEval_jetShift_eq_zero {U : Set (d → ℂ)} (hU : IsOpen U)
    (omega : d → ℝ) {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F U) {N : ℕ}
    {Q : MvPolynomial (Fin N) ℂ}
    (hQ : ∀ z ∈ U, jetRelationEval omega F Q z = 0) :
    ∀ z ∈ U, jetRelationEval omega F (jetShift Q) z = 0 := by
  intro z hz
  rw [jetRelationEval_jetShift omega hF Q hz]
  have hcong := torusDerivation_congr hU omega
    (F := jetRelationEval omega F Q) (G := fun _ => (0 : ℂ)) hQ z hz
  rw [hcong, torusDerivation_const]

/-- **Every iterate of a vanishing relation vanishes.** -/
theorem jetRelationEval_jetShiftIter_eq_zero {U : Set (d → ℂ)} (hU : IsOpen U)
    (omega : d → ℝ) {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F U) {N : ℕ}
    {Q : MvPolynomial (Fin (N + 1)) ℂ}
    (hQ : ∀ z ∈ U, jetRelationEval omega F Q z = 0) (m : ℕ) :
    ∀ z ∈ U, jetRelationEval omega F (jetShiftIter m Q) z = 0 := by
  induction m with
  | zero => exact hQ
  | succ m ih =>
      rw [jetShiftIter_succ]
      exact jetRelationEval_jetShift_eq_zero hU omega hF ih

/-- **Every iterate has the same leading coefficient value.** -/
theorem eval_pderiv_last_jetShiftIter (omega : d → ℝ) (F : (d → ℂ) → ℂ)
    {N : ℕ} (Q : MvPolynomial (Fin (N + 1)) ℂ) (z : d → ℂ) (m : ℕ) :
    MvPolynomial.eval (fun i : Fin (N + m + 1) => phaseJet omega F (i : ℕ) z)
        (MvPolynomial.pderiv (Fin.last (N + m)) (jetShiftIter m Q))
      = MvPolynomial.eval (fun i : Fin (N + 1) => phaseJet omega F (i : ℕ) z)
        (MvPolynomial.pderiv (Fin.last N) Q) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      show MvPolynomial.eval
          (fun i : Fin (N + m + 1 + 1) => phaseJet omega F (i : ℕ) z)
          (MvPolynomial.pderiv (Fin.last (N + m + 1))
            (jetShift (jetShiftIter m Q))) = _
      rw [pderiv_last_jetShift, MvPolynomial.eval_rename, ← ih]
      rfl

end

end GaloisForLFunctions.HTGeometry
