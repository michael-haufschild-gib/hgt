import GaloisForLFunctions.Hurwitz.JointLadderIndependence
import GaloisForLFunctions.Hurwitz.Hypertranscendence
import GaloisForLFunctions.HTGeometry.RationalCoefficientClearing

open Complex HurwitzZetaShift Polynomial HurwitzOrbit

namespace HurwitzJointLadder

open HurwitzLadder HurwitzJointOrbit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Intrinsic rational-coefficient joint ladder independence.**  In the canonical
denominator-cleared functional semantics, no nonzero relation over `ℂ(a)` couples a finite family
of Hurwitz ladders whose monodromy monomials are pairwise distinct. -/
theorem joint_hurwitz_ladder_rational_independence
    {s : ι → ℂ} (hs1 : ∀ j, 1 < (s j).re)
    (hmono : Function.Injective (monomialValue (fun j => monoScalar (s j))))
    (N : ℕ) (Q : MvPolynomial (ι × Fin (N + 1)) (RatFunc ℂ))
    (hrel : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun jk => hzeta (s jk.1 + ((jk.2 : ℕ) : ℂ)) a)
        (GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients Q) = 0) :
    Q = 0 := by
  have hclear := joint_hurwitz_ladder_independence hs1 hmono N
    (GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients Q) hrel
  by_contra hQ
  exact GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients_ne_zero Q hQ hclear

/-- Rational linear independence of `1` and the exponents implies rational-coefficient joint
independence of every finite union of their Hurwitz ladders. -/
theorem joint_hurwitz_ladder_rational_independence_of_linearIndependent
    {s : ι → ℂ} (hs1 : ∀ j, 1 < (s j).re)
    (hsQ : LinearIndependent ℚ (exponentFamily s))
    (N : ℕ) (Q : MvPolynomial (ι × Fin (N + 1)) (RatFunc ℂ))
    (hrel : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun jk => hzeta (s jk.1 + ((jk.2 : ℕ) : ℂ)) a)
        (GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients Q) = 0) :
    Q = 0 :=
  joint_hurwitz_ladder_rational_independence hs1
    (monomialValue_monoScalar_injective_of_linearIndependent s hsQ) N Q hrel

/-- A finite family of Hurwitz zeta functions is jointly hypertranscendental in the shift variable
when the monomials in its monodromy scalars are pairwise distinct. -/
theorem joint_hzeta_hypertranscendental_in_shift
    {s : ι → ℂ} (hs1 : ∀ j, 1 < (s j).re)
    (hmono : Function.Injective (monomialValue (fun j => monoScalar (s j))))
    (N : ℕ) (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ))
    (hrel : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun jk => iteratedDeriv (jk.2 : ℕ) (hzeta (s jk.1)) a) P = 0) :
    P = 0 := by
  let c : (ι × Fin (N + 1)) → ℂ := fun jk =>
    (-1 : ℂ) ^ (jk.2 : ℕ) * (ascPochhammer ℂ (jk.2 : ℕ)).eval (s jk.1)
  have hc : ∀ jk, c jk ≠ 0 := by
    intro jk
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (ascPochhammer_eval_ne_zero_of_one_lt_re (jk.2 : ℕ) (hs1 jk.1))
  let P' := hzetaJetDiagonalScale c P
  have hrel' : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun jk => hzeta (s jk.1 + ((jk.2 : ℕ) : ℂ)) a) P' = 0 := by
    intro a ha
    change MvPolynomial.eval₂ (Polynomial.evalRingHom a)
      (fun jk => hzeta (s jk.1 + ((jk.2 : ℕ) : ℂ)) a)
      (hzetaJetDiagonalScale c P) = 0
    rw [eval₂_hzetaJetDiagonalScale]
    have hjet : (fun jk => c jk * hzeta (s jk.1 + ((jk.2 : ℕ) : ℂ)) a) =
        fun jk => iteratedDeriv (jk.2 : ℕ) (hzeta (s jk.1)) a := by
      funext jk
      exact (hzeta_iteratedDeriv (jk.2 : ℕ) (hs1 jk.1) (a := a) ha).symm
    rw [hjet]
    exact hrel a ha
  have hP' : P' = 0 := joint_hurwitz_ladder_independence hs1 hmono N P' hrel'
  change hzetaJetDiagonalScale c P = 0 at hP'
  have hinv := congrArg (hzetaJetDiagonalScale (fun i => (c i)⁻¹)) hP'
  rw [hzetaJetDiagonalScale_inv_apply c hc P] at hinv
  simpa using hinv

/-- **Joint hypertranscendence of a finite Hurwitz family.**  If `1` and the exponents `(s_j)`
are linearly independent over `ℚ`, then every finite union of the differential jets of
`a ↦ ζ(s_j,a)` is algebraically independent over `ℂ[a]`.  In particular there is no mixed
algebraic differential equation coupling the family. -/
theorem joint_hzeta_hypertranscendental_in_shift_of_linearIndependent
    {s : ι → ℂ} (hs1 : ∀ j, 1 < (s j).re)
    (hsQ : LinearIndependent ℚ (exponentFamily s))
    (N : ℕ) (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ))
    (hrel : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun jk => iteratedDeriv (jk.2 : ℕ) (hzeta (s jk.1)) a) P = 0) :
    P = 0 :=
  joint_hzeta_hypertranscendental_in_shift hs1
    (monomialValue_monoScalar_injective_of_linearIndependent s hsQ) N P hrel

/-- **Intrinsic rational-coefficient joint hypertranscendence.**  In the canonical
denominator-cleared functional semantics, no nonzero differential relation over `ℂ(a)` couples a
finite Hurwitz family whose monodromy monomials are pairwise distinct. -/
theorem joint_hzeta_rational_hypertranscendental_in_shift
    {s : ι → ℂ} (hs1 : ∀ j, 1 < (s j).re)
    (hmono : Function.Injective (monomialValue (fun j => monoScalar (s j))))
    (N : ℕ) (Q : MvPolynomial (ι × Fin (N + 1)) (RatFunc ℂ))
    (hrel : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun jk => iteratedDeriv (jk.2 : ℕ) (hzeta (s jk.1)) a)
        (GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients Q) = 0) :
    Q = 0 := by
  have hclear := joint_hzeta_hypertranscendental_in_shift
    hs1 hmono N (GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients Q) hrel
  by_contra hQ
  exact GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients_ne_zero Q hQ hclear

/-- **Rational-coefficient joint hypertranscendence.**  In the canonical denominator-cleared
functional semantics, no nonzero differential relation over `ℂ(a)` couples a rationally independent
finite Hurwitz family. -/
theorem joint_hzeta_rational_hypertranscendental_in_shift_of_linearIndependent
    {s : ι → ℂ} (hs1 : ∀ j, 1 < (s j).re)
    (hsQ : LinearIndependent ℚ (exponentFamily s))
    (N : ℕ) (Q : MvPolynomial (ι × Fin (N + 1)) (RatFunc ℂ))
    (hrel : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun jk => iteratedDeriv (jk.2 : ℕ) (hzeta (s jk.1)) a)
        (GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients Q) = 0) :
    Q = 0 :=
  joint_hzeta_rational_hypertranscendental_in_shift hs1
    (monomialValue_monoScalar_injective_of_linearIndependent s hsQ) N Q hrel

/-- **Arbitrary-family ladder law.**  Every finite subfamily of an arbitrarily indexed rationally
independent exponent family has rational-coefficient joint Hurwitz-ladder independence. -/
theorem joint_hurwitz_ladder_rational_independence_on_finset
    {κ : Type*} [DecidableEq κ] {s : κ → ℂ} (hs1 : ∀ j, 1 < (s j).re)
    (hsQ : LinearIndependent ℚ (exponentFamily s))
    (J : Finset κ) (N : ℕ)
    (Q : MvPolynomial (J × Fin (N + 1)) (RatFunc ℂ))
    (hrel : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun jk => hzeta (s jk.1.1 + ((jk.2 : ℕ) : ℂ)) a)
        (GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients Q) = 0) :
    Q = 0 := by
  classical
  let sJ : J → ℂ := fun j => s j.1
  have hs1J : ∀ j, 1 < (sJ j).re := fun j => hs1 j.1
  have hsQJ : LinearIndependent ℚ (exponentFamily sJ) := by
    simpa [sJ] using! exponentFamily_linearIndependent_comp s hsQ
      (fun j : J => j.1) Subtype.val_injective
  exact joint_hurwitz_ladder_rational_independence_of_linearIndependent
    hs1J hsQJ N Q hrel

/-- **Arbitrary-family differential law.**  Every finite mixed jet packet drawn from an
arbitrarily indexed rationally independent exponent family is algebraically independent over
`ℂ(a)` in the canonical denominator-cleared functional semantics. -/
theorem joint_hzeta_rational_hypertranscendental_on_finset
    {κ : Type*} [DecidableEq κ] {s : κ → ℂ} (hs1 : ∀ j, 1 < (s j).re)
    (hsQ : LinearIndependent ℚ (exponentFamily s))
    (J : Finset κ) (N : ℕ)
    (Q : MvPolynomial (J × Fin (N + 1)) (RatFunc ℂ))
    (hrel : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun jk => iteratedDeriv (jk.2 : ℕ) (hzeta (s jk.1.1)) a)
        (GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients Q) = 0) :
    Q = 0 := by
  classical
  let sJ : J → ℂ := fun j => s j.1
  have hs1J : ∀ j, 1 < (sJ j).re := fun j => hs1 j.1
  have hsQJ : LinearIndependent ℚ (exponentFamily sJ) := by
    simpa [sJ] using! exponentFamily_linearIndependent_comp s hsQ
      (fun j : J => j.1) Subtype.val_injective
  exact joint_hzeta_rational_hypertranscendental_in_shift_of_linearIndependent
    hs1J hsQJ N Q hrel

end HurwitzJointLadder
