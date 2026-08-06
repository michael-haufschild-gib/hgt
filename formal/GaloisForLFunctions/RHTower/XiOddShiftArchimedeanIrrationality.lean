import GaloisForLFunctions.HTGeometry.DigammaHalfTranslateIndependent
import GaloisForLFunctions.RHTower.XiEvenShiftDivisorRationality

/-!
# The odd shift-one archimedean correction is not rational

The archimedean correction at an even shift is an explicit rational telescope.  At the shift one it
is not: the closed form

  `logDeriv archFactor (s+1) - logDeriv archFactor s
     = 1/(s+1) - 1/(s-1) + ψ((s+1)/2)/2 - ψ(s/2)/2`

carries both digamma modes with opposite nonzero weights, and the two modes are independent over the
rational functions.  Substituting `s = 2z` turns them into `ψ(z)` and `ψ(z+1/2)`, so half-translate
digamma independence applies directly.

This is the negative half of the parity dichotomy: parity balance is not merely a convenient
sufficient condition for rationality of the archimedean correction, it is genuinely needed already
for the single odd shift.
-/

namespace RHTower

open Complex

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Closed form at shift one.** An explicit rational part plus the half-difference of the two
digamma modes. -/
theorem xiTransverseShiftArchimedeanCorrection_one_closed {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    xiTransverseShiftArchimedeanCorrection 1 s =
      1 / (s + 1) - 1 / (s - 1) +
        (Complex.digamma ((s + 1) / 2) / 2 - Complex.digamma (s / 2) / 2) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hs1re : 0 < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hs1ne0 : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have hs1ne1 : s + 1 ≠ 1 := by
    intro h
    exact hs0 (by linear_combination h)
  rw [xiTransverseShiftArchimedeanCorrection, Nat.cast_one,
    logDeriv_archFactor_closed hs1re hs1ne0 hs1ne1,
    logDeriv_archFactor_closed hs hs0 h1,
    gammaRealLogConnection, gammaRealLogConnection,
    show s + 1 - 1 = s by ring]
  ring

/-- **Shift one is not rational.** No quotient of polynomials agrees with the shift-one archimedean
correction on the right half-plane. -/
theorem xiTransverseShiftArchimedeanCorrection_one_not_rational :
    ¬ ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧ ∀ s : ℂ, 0 < s.re → s ≠ 1 → Q.eval s ≠ 0 →
        xiTransverseShiftArchimedeanCorrection 1 s = P.eval s / Q.eval s := by
  rintro ⟨P, Q, hQ, hrel⟩
  classical
  have hev : ∀ (R : Polynomial ℂ) (z : ℂ),
      (R.comp (Polynomial.C 2 * Polynomial.X)).eval z = R.eval (2 * z) := by
    intro R z
    simp [Polynomial.eval_comp]
  set P₂ : Polynomial ℂ := P.comp (Polynomial.C 2 * Polynomial.X) with hP₂
  set Q₂ : Polynomial ℂ := Q.comp (Polynomial.C 2 * Polynomial.X) with hQ₂
  have hQ2ne : Q₂ ≠ 0 := by
    intro h0
    refine hQ (Polynomial.funext fun w => ?_)
    have hz := congrArg (Polynomial.eval (w / 2)) h0
    rw [hQ₂, hev] at hz
    rw [show 2 * (w / 2) = w by ring] at hz
    simpa using hz
  set L1 : Polynomial ℂ := Polynomial.C 2 * Polynomial.X + 1 with hL1
  set L2 : Polynomial ℂ := Polynomial.C 2 * Polynomial.X - 1 with hL2
  have hL1eval : ∀ z : ℂ, L1.eval z = 2 * z + 1 := by intro z; simp [hL1]
  have hL2eval : ∀ z : ℂ, L2.eval z = 2 * z - 1 := by intro z; simp [hL2]
  set D : Polynomial ℂ := Q₂ * L1 * L2 with hD
  set N : Polynomial ℂ := P₂ * L1 * L2 - Q₂ * L2 + Q₂ * L1 with hN
  have hL1ne : L1 ≠ 0 := by
    intro h0
    have := congrArg (Polynomial.eval (0 : ℂ)) h0
    rw [hL1eval] at this
    norm_num at this
  have hL2ne : L2 ≠ 0 := by
    intro h0
    have := congrArg (Polynomial.eval (0 : ℂ)) h0
    rw [hL2eval] at this
    norm_num at this
  have hDne : D ≠ 0 := by
    rw [hD]
    exact mul_ne_zero (mul_ne_zero hQ2ne hL1ne) hL2ne
  have hkey := digamma_half_translate_independent_of_quotient (E := -(1 / 2 : ℂ))
    (O := (1 / 2 : ℂ)) (P := N) (Q := D) hDne
    (T := ({(1 / 2 : ℂ)} : Set ℂ)) (Set.finite_singleton _) ?_
  · have hE : (-(1 / 2 : ℂ)) = 0 := hkey.1
    norm_num at hE
  · intro z hz hzT hDz
    have hDzval : Q₂.eval z * L1.eval z * L2.eval z ≠ 0 := by
      rw [hD] at hDz
      simpa using hDz
    have hQ2z : Q₂.eval z ≠ 0 := by
      intro h0
      exact hDzval (by rw [h0]; ring)
    have hL1z : L1.eval z ≠ 0 := by
      intro h0
      exact hDzval (by rw [h0]; ring)
    have hL2z : L2.eval z ≠ 0 := by
      intro h0
      exact hDzval (by rw [h0]; ring)
    have h2zre : 0 < (2 * z).re := by
      simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]
      linarith
    have h2zne1 : 2 * z ≠ 1 := by
      intro h0
      exact hzT (by simpa using (by linear_combination h0 / 2 : z = 1 / 2))
    have hQz : Q.eval (2 * z) ≠ 0 := by
      rw [hQ₂, hev] at hQ2z
      exact hQ2z
    have hclosed := xiTransverseShiftArchimedeanCorrection_one_closed h2zre h2zne1
    have hrel' := hrel (2 * z) h2zre h2zne1 hQz
    rw [hrel', show (2 * z + 1) / 2 = z + 1 / 2 by ring,
      show (2 * z) / 2 = z by ring] at hclosed
    have h2z1 : (2 * z + 1 : ℂ) ≠ 0 := by rwa [hL1eval] at hL1z
    have h2z2 : (2 * z - 1 : ℂ) ≠ 0 := by rwa [hL2eval] at hL2z
    have hNz : N.eval z =
        P.eval (2 * z) * (2 * z + 1) * (2 * z - 1) - Q.eval (2 * z) * (2 * z - 1) +
          Q.eval (2 * z) * (2 * z + 1) := by
      rw [hN]
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul]
      rw [hL1eval, hL2eval, hP₂, hQ₂, hev, hev]
    have hDzeq : D.eval z = Q.eval (2 * z) * (2 * z + 1) * (2 * z - 1) := by
      rw [hD]
      simp only [Polynomial.eval_mul]
      rw [hL1eval, hL2eval, hQ₂, hev]
    have hNdiv : (P.eval (2 * z) * (2 * z + 1) * (2 * z - 1) - Q.eval (2 * z) * (2 * z - 1) +
          Q.eval (2 * z) * (2 * z + 1)) / (Q.eval (2 * z) * (2 * z + 1) * (2 * z - 1))
        = P.eval (2 * z) / Q.eval (2 * z) - 1 / (2 * z + 1) + 1 / (2 * z - 1) := by
      field_simp
    rw [hNz, hDzeq, hNdiv]
    linear_combination -hclosed

end

end RHTower
