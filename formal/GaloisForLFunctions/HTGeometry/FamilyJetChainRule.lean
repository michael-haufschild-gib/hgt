import GaloisForLFunctions.HTGeometry.LogarithmicDerivativeObstruction

/-!
# The chain rule for full jet polynomials of a family

A differential relation for a finite family is a polynomial in the spectral variable and all jets of
all members.  Differentiating such an expression along the curve is the jet-like derivation which
sends the spectral variable to one and each jet to the next.

This is the family version of the single-function jet chain rule, and the untruncated one: the jets
run over all of `ℕ`, so the derivation stays inside the ring.  It is the engine which turns an
analytic differential relation into an algebraic identity in the jet polynomial ring.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Topology

noncomputable section

/-- Jet coordinates of a finite family: the spectral variable and all jets of all members. -/
abbrev FullJetIndex (m : ℕ) := Unit ⊕ Fin m × ℕ

/-- The full jet vector of a family at a point. -/
def fullJetVec {m : ℕ} (sigma : Fin m → ℂ → ℂ) (w : ℂ) : FullJetIndex m → ℂ :=
  Sum.elim (fun _ => w) (fun p => iteratedDeriv p.2 (sigma p.1) w)

@[simp]
theorem fullJetVec_inl {m : ℕ} (sigma : Fin m → ℂ → ℂ) (w : ℂ) (u : Unit) :
    fullJetVec sigma w (Sum.inl u) = w := rfl

@[simp]
theorem fullJetVec_inr {m : ℕ} (sigma : Fin m → ℂ → ℂ) (w : ℂ) (i : Fin m) (k : ℕ) :
    fullJetVec sigma w (Sum.inr (i, k)) = iteratedDeriv k (sigma i) w := rfl

/-- The total derivative on full jet coordinates: the spectral variable has derivative one, each jet
becomes the next. -/
def fullJetShift (m : ℕ) : FullJetIndex m → MvPolynomial (FullJetIndex m) ℂ :=
  Sum.elim (fun _ => 1) (fun p => MvPolynomial.X (Sum.inr (p.1, p.2 + 1)))

theorem totalDegree_fullJetShift_le (m : ℕ) (v : FullJetIndex m) :
    (fullJetShift m v).totalDegree ≤ 1 := by
  rcases v with ⟨⟩ | ⟨i, k⟩
  · rw [fullJetShift, Sum.elim_inl, MvPolynomial.totalDegree_one]
    exact Nat.zero_le 1
  · rw [fullJetShift, Sum.elim_inr, MvPolynomial.totalDegree_X]

/-- The total derivation on full jet polynomials. -/
def fullJetDerivation (m : ℕ) :
    Derivation ℂ (MvPolynomial (FullJetIndex m) ℂ) (MvPolynomial (FullJetIndex m) ℂ) :=
  jetLikeDerivation (fullJetShift m)

theorem totalDegree_fullJetDerivation_le {m : ℕ} (P : MvPolynomial (FullJetIndex m) ℂ) :
    (fullJetDerivation m P).totalDegree ≤ P.totalDegree :=
  totalDegree_jetLikeDerivation_le (totalDegree_fullJetShift_le m) P

/-- Evaluating a full jet polynomial along a smooth family is differentiable. -/
theorem differentiableAt_eval_fullJetVec {m : ℕ} {U : Set ℂ} (hU : IsOpen U)
    {sigma : Fin m → ℂ → ℂ} (hs : ∀ i, ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (sigma i) w) {z : ℂ}
    (hz : z ∈ U) (P : MvPolynomial (FullJetIndex m) ℂ) :
    DifferentiableAt ℂ (fun w => MvPolynomial.eval (fullJetVec sigma w) P) z := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.eval_C]
      exact differentiableAt_const a
  | add p q hp hq =>
      simp only [map_add]
      exact hp.add hq
  | mul_X p v hp =>
      simp only [map_mul, MvPolynomial.eval_X]
      rcases v with ⟨⟩ | ⟨i, k⟩
      · simp only [fullJetVec_inl]
        exact hp.mul differentiableAt_id
      · simp only [fullJetVec_inr]
        exact hp.mul (differentiableAt_iteratedDeriv_of_contDiffAt hU (hs i) hz k)

/-- **The full jet chain rule.**  Differentiating the evaluation of a full jet polynomial along a
smooth family is evaluating its total derivation. -/
theorem deriv_eval_fullJetVec {m : ℕ} {U : Set ℂ} (hU : IsOpen U)
    {sigma : Fin m → ℂ → ℂ} (hs : ∀ i, ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (sigma i) w) {z : ℂ}
    (hz : z ∈ U) (P : MvPolynomial (FullJetIndex m) ℂ) :
    deriv (fun w => MvPolynomial.eval (fullJetVec sigma w) P) z
      = MvPolynomial.eval (fullJetVec sigma z) (fullJetDerivation m P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.eval_C, fullJetDerivation]
      rw [show jetLikeDerivation (fullJetShift m) (MvPolynomial.C a) = 0 from ?_, map_zero]
      · exact deriv_const z a
      · have hCa : (MvPolynomial.C a : MvPolynomial (FullJetIndex m) ℂ)
            = algebraMap ℂ (MvPolynomial (FullJetIndex m) ℂ) a := rfl
        rw [hCa]
        exact (jetLikeDerivation (fullJetShift m)).map_algebraMap a
  | add p q hp hq =>
      have hdp := differentiableAt_eval_fullJetVec hU hs hz p
      have hdq := differentiableAt_eval_fullJetVec hU hs hz q
      simp only [map_add]
      rw [deriv_fun_add hdp hdq, hp, hq]
  | mul_X p v hp =>
      have hdp := differentiableAt_eval_fullJetVec hU hs hz p
      rcases v with ⟨⟩ | ⟨i, k⟩
      · have hdid : DifferentiableAt ℂ (fun w : ℂ => w) z := differentiableAt_id
        simp only [map_mul, MvPolynomial.eval_X, fullJetVec_inl]
        rw [deriv_fun_mul hdp hdid, hp, deriv_id'']
        simp only [fullJetDerivation, Derivation.leibniz, jetLikeDerivation_X, fullJetShift,
          Sum.elim_inl, smul_eq_mul, map_add, map_mul, MvPolynomial.eval_X, map_one,
          fullJetVec_inl]
        ring
      · have hdjet := differentiableAt_iteratedDeriv_of_contDiffAt hU (hs i) hz k
        have hsucc : deriv (fun w => iteratedDeriv k (sigma i) w) z
            = iteratedDeriv (k + 1) (sigma i) z := by
          rw [iteratedDeriv_succ]
        simp only [map_mul, MvPolynomial.eval_X, fullJetVec_inr]
        rw [deriv_fun_mul hdp hdjet, hp, hsucc]
        simp only [fullJetDerivation, Derivation.leibniz, jetLikeDerivation_X, fullJetShift,
          Sum.elim_inr, smul_eq_mul, map_add, map_mul, MvPolynomial.eval_X, fullJetVec_inr]
        ring

end

end GaloisForLFunctions.HTGeometry
