import GaloisForLFunctions.HTGeometry.GammaStirlingLadderPolynomial

/-!
# The shifted Stirling ladder polynomial

`finite-archimedean-gamma-product-boundary-law` §5 needs the residues of `ψ(s+μ)` at `s^{-m}` for
every `m`, not only for `m ≤ 4`.  Expanding the unshifted ladder at `z = s+μ` would require a
binomial-series remainder at every order; telescoping *directly in `s`* avoids that entirely,
because the only new ingredient is the single rational function `1/(s+μ) = u/(1+μu)`.

Clearing `(1+u)^M (1+μu)` from the one-step difference of `ψ(s+μ) - log s + ∑_{m<M} d_m s^{-(m+1)}`
gives a polynomial `Q_M` obeying the *same* linear recursion as `ladderPoly`, with the same forced
coefficient `ladderCoeffOf`: the factor `1 + μX` has constant term `1`, so it never touches the
degree `M+2` obstruction, and the extra `μ` only shifts the base case from `0` to `-μX²`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- If `q` vanishes at `0`, the degree-one coefficient of `p * q` sees only `p.coeff 0`. -/
theorem coeff_one_mul_of_X_dvd {p q : ℂ[X]} (hq : (X : ℂ[X]) ∣ q) :
    (p * q).coeff 1 = p.coeff 0 * q.coeff 1 := by
  obtain ⟨q', rfl⟩ := hq
  have h1 : p * (X * q') = X * (p * q') := by ring
  have h2 : ((X : ℂ[X]) * (p * q')).coeff (0 + 1) = (p * q').coeff 0 :=
    Polynomial.coeff_X_mul _ 0
  have h3 : ((X : ℂ[X]) * q').coeff (0 + 1) = q'.coeff 0 := Polynomial.coeff_X_mul _ 0
  simp only [Nat.zero_add] at h2 h3
  rw [h1, h2, h3, Polynomial.mul_coeff_zero]

theorem coeff_zero_one_add_C_mul_X (mu : ℂ) : ((1 : ℂ[X]) + C mu * X).coeff 0 = 1 := by
  simp

/-- The shifted ladder polynomial: the cleared numerator of the one-step difference of
`ψ(s+μ) - log s + ∑_{m<M} d_m s^{-(m+1)}`. -/
def shiftLadderPoly (mu : ℂ) : ℕ → ℂ[X]
  | 0 => -(C mu) * X ^ 2
  | (M + 1) =>
      (1 + X) * shiftLadderPoly mu M
        - C ((-1) ^ (M + 1) / ((M : ℂ) + 2))
            * (X ^ (M + 2) * ((1 + X) ^ (M + 1) * (1 + C mu * X)))
        + C (ladderCoeffOf (shiftLadderPoly mu M) M)
            * (X ^ (M + 1) * ((1 + C mu * X) * (1 - (1 + X) ^ (M + 1))))

/-- The `M`-th shifted ladder coefficient. -/
def shiftLadderCoeff (mu : ℂ) (M : ℕ) : ℂ := ladderCoeffOf (shiftLadderPoly mu M) M

theorem shiftLadderPoly_succ (mu : ℂ) (M : ℕ) :
    shiftLadderPoly mu (M + 1) =
      (1 + X) * shiftLadderPoly mu M
        - C ((-1) ^ (M + 1) / ((M : ℂ) + 2))
            * (X ^ (M + 2) * ((1 + X) ^ (M + 1) * (1 + C mu * X)))
        + C (shiftLadderCoeff mu M)
            * (X ^ (M + 1) * ((1 + C mu * X) * (1 - (1 + X) ^ (M + 1)))) := rfl

/-- **The shifted ladder polynomial vanishes to order `M+2`.** -/
theorem X_pow_dvd_shiftLadderPoly (mu : ℂ) : ∀ M : ℕ,
    ((X : ℂ[X]) ^ (M + 2)) ∣ shiftLadderPoly mu M := by
  intro M
  induction M with
  | zero =>
      refine ⟨-(C mu), ?_⟩
      rw [shiftLadderPoly]
      ring
  | succ M ih =>
      have hcM : (shiftLadderPoly mu M).coeff (M + 1) = 0 :=
        (Polynomial.X_pow_dvd_iff.mp ih) (M + 1) (by omega)
      have hd1 : ((X : ℂ[X]) ^ (M + 2)) ∣ (1 + X) * shiftLadderPoly mu M := ih.mul_left _
      have hd2 : ((X : ℂ[X]) ^ (M + 2)) ∣
          C ((-1 : ℂ) ^ (M + 1) / ((M : ℂ) + 2))
            * (X ^ (M + 2) * ((1 + X) ^ (M + 1) * (1 + C mu * X))) :=
        (dvd_mul_right _ _).mul_left _
      have hd3 : ((X : ℂ[X]) ^ (M + 2)) ∣
          C (shiftLadderCoeff mu M)
            * (X ^ (M + 1) * ((1 + C mu * X) * (1 - (1 + X) ^ (M + 1)))) := by
        refine Dvd.dvd.mul_left ?_ _
        have hx : (X : ℂ[X]) ∣ (1 + C mu * X) * (1 - (1 + X) ^ (M + 1)) :=
          Dvd.dvd.mul_left (X_dvd_one_sub_one_add_X_pow (M + 1)) _
        have h := mul_dvd_mul_left ((X : ℂ[X]) ^ (M + 1)) hx
        simpa [pow_succ] using h
      have hdvd2 : ((X : ℂ[X]) ^ (M + 2)) ∣ shiftLadderPoly mu (M + 1) := by
        rw [shiftLadderPoly_succ]
        exact dvd_add (dvd_sub hd1 hd2) hd3
      have hkey : (shiftLadderPoly mu (M + 1)).coeff (M + 2) = 0 := by
        have hne : ((M : ℂ) + 1) ≠ 0 := by
          have h := Nat.cast_add_one_ne_zero (R := ℂ) M
          simpa using h
        have e1 : ((1 + X : ℂ[X]) * shiftLadderPoly mu M).coeff (M + 2)
            = (shiftLadderPoly mu M).coeff (M + 2) + (shiftLadderPoly mu M).coeff (M + 1) := by
          rw [add_mul, one_mul, Polynomial.coeff_add]
          congr 1
          exact Polynomial.coeff_X_mul _ (M + 1)
        have e2 : (C ((-1 : ℂ) ^ (M + 1) / ((M : ℂ) + 2))
            * (X ^ (M + 2) * ((1 + X) ^ (M + 1) * (1 + C mu * X)))).coeff (M + 2)
            = (-1 : ℂ) ^ (M + 1) / ((M : ℂ) + 2) := by
          rw [Polynomial.coeff_C_mul]
          have hs := Polynomial.coeff_X_pow_mul
            (((1 + X : ℂ[X]) ^ (M + 1)) * (1 + C mu * X)) (M + 2) 0
          rw [zero_add] at hs
          rw [hs, Polynomial.mul_coeff_zero, coeff_zero_one_add_X_pow,
            coeff_zero_one_add_C_mul_X, mul_one, mul_one]
        have e3 : (C (shiftLadderCoeff mu M)
            * (X ^ (M + 1) * ((1 + C mu * X) * (1 - (1 + X) ^ (M + 1))))).coeff (M + 2)
            = shiftLadderCoeff mu M * (-((M : ℂ) + 1)) := by
          rw [Polynomial.coeff_C_mul]
          have hidx : M + 2 = 1 + (M + 1) := by omega
          have hshift : ((X : ℂ[X]) ^ (M + 1)
              * ((1 + C mu * X) * (1 - (1 + X) ^ (M + 1)))).coeff (M + 2)
              = (((1 : ℂ[X]) + C mu * X) * (1 - (1 + X) ^ (M + 1))).coeff 1 := by
            rw [hidx]
            exact Polynomial.coeff_X_pow_mul _ (M + 1) 1
          rw [hshift, coeff_one_mul_of_X_dvd (X_dvd_one_sub_one_add_X_pow (M + 1)),
            coeff_zero_one_add_C_mul_X, Polynomial.coeff_sub, coeff_one_one_add_X_pow,
            Polynomial.coeff_one]
          norm_num
        rw [shiftLadderPoly_succ, Polynomial.coeff_add, Polynomial.coeff_sub, e1, e2, e3, hcM]
        rw [shiftLadderCoeff, ladderCoeffOf]
        have hsign : ((-1 : ℂ)) ^ (M + 1) = -((-1 : ℂ) ^ M) := by rw [pow_succ]; ring
        rw [hsign]
        field_simp
        ring
      rw [Polynomial.X_pow_dvd_iff]
      intro d hd
      rcases Nat.lt_or_ge d (M + 2) with h | h
      · exact (Polynomial.X_pow_dvd_iff.mp hdvd2) d h
      · have : d = M + 2 := by omega
        rw [this]; exact hkey

end

end GaloisForLFunctions.HTGeometry
