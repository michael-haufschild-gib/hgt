import GaloisForLFunctions.Hurwitz.ContinuedJointLadderIndependence
import GaloisForLFunctions.Hurwitz.JointHypertranscendence

/-!
# Unrestricted joint hypertranscendence of the continued Hurwitz family

The all-order continued differential ladder converts jet relations to ladder relations.  Augmented
rational independence excludes every Pochhammer resonance, so diagonal scaling is invertible.
-/

open Complex HurwitzZetaShift Polynomial HurwitzOrbit

namespace HurwitzJointLadder

open HurwitzLadder HurwitzJointOrbit HurwitzZetaContinuation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Augmented rational independence excludes every zero of every ascending Pochhammer factor. -/
theorem ascPochhammer_eval_ne_zero_of_exponentFamily_linearIndependent
    {s : ι → ℂ} (hsQ : LinearIndependent ℚ (exponentFamily s)) (j : ι) (n : ℕ) :
    (ascPochhammer ℂ n).eval (s j) ≠ 0 := by
  rw [ne_eq, ascPochhammer_eval_eq_zero_iff]
  push Not
  intro k hk heq
  let g : Option ι → ℚ := fun x =>
    match x with
    | none => k
    | some i => if i = j then 1 else 0
  have hrel : ∑ x : Option ι, g x • exponentFamily s x = 0 := by
    rw [Fintype.sum_option]
    simp only [g, exponentFamily, Rat.smul_def, mul_one]
    simp [heq]
  have hc := Fintype.linearIndependent_iff.mp hsQ g hrel (some j)
  simp [g] at hc

/-- **Unrestricted finite-family joint hypertranscendence in the shift variable.** -/
theorem continued_joint_hzeta_hypertranscendental_in_shift_of_linearIndependent
    {s : ι → ℂ} (hsQ : LinearIndependent ℚ (exponentFamily s))
    (N : ℕ) (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ))
    (hrel : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun jk => iteratedDeriv (jk.2 : ℕ) (continuedHzeta (s jk.1)) a) P = 0) :
    P = 0 := by
  let c : (ι × Fin (N + 1)) → ℂ := fun jk =>
    (-1 : ℂ) ^ (jk.2 : ℕ) * (ascPochhammer ℂ (jk.2 : ℕ)).eval (s jk.1)
  have hc : ∀ jk, c jk ≠ 0 := by
    intro jk
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (ascPochhammer_eval_ne_zero_of_exponentFamily_linearIndependent
        hsQ jk.1 (jk.2 : ℕ))
  let P' := hzetaJetDiagonalScale c P
  have hrel' : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun jk => continuedHzeta (s jk.1 + (jk.2 : ℕ)) a) P' = 0 := by
    intro a ha
    change MvPolynomial.eval₂ (Polynomial.evalRingHom a)
      (fun jk => continuedHzeta (s jk.1 + (jk.2 : ℕ)) a)
      (hzetaJetDiagonalScale c P) = 0
    rw [eval₂_hzetaJetDiagonalScale]
    have hjet :
        (fun jk => c jk * continuedHzeta (s jk.1 + (jk.2 : ℕ)) a) =
          fun jk => iteratedDeriv (jk.2 : ℕ) (continuedHzeta (s jk.1)) a := by
      funext jk
      exact (continuedHzeta_iteratedDeriv (jk.2 : ℕ) ha).symm
    rw [hjet]
    exact hrel a ha
  have hP' : P' = 0 :=
    continued_joint_hurwitz_ladder_independence_of_linearIndependent hsQ N P' hrel'
  change hzetaJetDiagonalScale c P = 0 at hP'
  have hinv := congrArg (hzetaJetDiagonalScale (fun i => (c i)⁻¹)) hP'
  rw [hzetaJetDiagonalScale_inv_apply c hc P] at hinv
  simpa using hinv

end HurwitzJointLadder
