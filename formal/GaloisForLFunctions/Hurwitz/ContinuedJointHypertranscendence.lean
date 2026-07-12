import GaloisForLFunctions.Hurwitz.ContinuedJointLadderIndependence
import GaloisForLFunctions.Hurwitz.ContinuedJointLadderResidueIndependence
import GaloisForLFunctions.Hurwitz.JointHypertranscendence
import GaloisForLFunctions.HTGeometry.RationalCoefficientClearing

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
    push_cast
    rw [heq]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · simp
  have hc := Fintype.linearIndependent_iff.mp hsQ g hrel (some j)
  simp [g] at hc

/-- A nonintegral exponent avoids every ascending-Pochhammer zero. -/
theorem ascPochhammer_eval_ne_zero_of_nonintegral {s : ℂ}
    (hs : ∀ m : ℤ, s ≠ (m : ℂ)) (n : ℕ) :
    (ascPochhammer ℂ n).eval s ≠ 0 := by
  rw [ne_eq, ascPochhammer_eval_eq_zero_iff]
  push Not
  intro k _ heq
  apply hs (-k)
  push_cast
  exact heq

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

/-- **Exact-residue joint hypertranscendence in the shift variable.** -/
theorem continued_joint_hzeta_hypertranscendental_in_shift_of_integerResidueSeparated
    {s : ι → ℂ} (hnonintegral : ∀ j m, s j ≠ (m : ℂ))
    (hseparated : ∀ i j, i ≠ j → ∀ m : ℤ, s i - s j ≠ (m : ℂ))
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
      (ascPochhammer_eval_ne_zero_of_nonintegral (hnonintegral jk.1) (jk.2 : ℕ))
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
    continued_joint_hurwitz_ladder_independence_of_integerResidueSeparated
      hnonintegral hseparated N P' hrel'
  change hzetaJetDiagonalScale c P = 0 at hP'
  have hinv := congrArg (hzetaJetDiagonalScale (fun i => (c i)⁻¹)) hP'
  rw [hzetaJetDiagonalScale_inv_apply c hc P] at hinv
  simpa using hinv

/-- Unrestricted rational-coefficient joint hypertranscendence in the canonical
denominator-cleared functional semantics. -/
theorem continued_joint_hzeta_rational_hypertranscendental_in_shift_of_linearIndependent
    {s : ι → ℂ} (hsQ : LinearIndependent ℚ (exponentFamily s))
    (N : ℕ) (Q : MvPolynomial (ι × Fin (N + 1)) (RatFunc ℂ))
    (hrel : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun jk => iteratedDeriv (jk.2 : ℕ) (continuedHzeta (s jk.1)) a)
        (GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients Q) = 0) :
    Q = 0 := by
  have hclear := continued_joint_hzeta_hypertranscendental_in_shift_of_linearIndependent
    hsQ N (GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients Q) hrel
  by_contra hQ
  exact GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients_ne_zero Q hQ hclear

/-- Rational-coefficient form of exact-residue joint hypertranscendence. -/
theorem continued_joint_hzeta_rational_hypertranscendental_in_shift_of_integerResidueSeparated
    {s : ι → ℂ} (hnonintegral : ∀ j m, s j ≠ (m : ℂ))
    (hseparated : ∀ i j, i ≠ j → ∀ m : ℤ, s i - s j ≠ (m : ℂ))
    (N : ℕ) (Q : MvPolynomial (ι × Fin (N + 1)) (RatFunc ℂ))
    (hrel : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun jk => iteratedDeriv (jk.2 : ℕ) (continuedHzeta (s jk.1)) a)
        (GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients Q) = 0) :
    Q = 0 := by
  have hclear :=
    continued_joint_hzeta_hypertranscendental_in_shift_of_integerResidueSeparated
      hnonintegral hseparated N
        (GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients Q) hrel
  by_contra hQ
  exact GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients_ne_zero Q hQ hclear

end HurwitzJointLadder
