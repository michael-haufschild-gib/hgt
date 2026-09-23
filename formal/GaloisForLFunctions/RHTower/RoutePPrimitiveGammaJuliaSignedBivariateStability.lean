import GaloisForLFunctions.RHTower.RoutePPrimitiveJointDepthGammaJuliaLogKreinMatrixCompletion
import GaloisForLFunctions.HTGeometry.HermitianInertia

/-!
# Route P primitive Gamma--Julia signed bivariate stability

P-G105F constructs full prime-log Julia--Krein completion `B tensor H`, where `H=LGL` is the
positive source Gram in reciprocal-promotion coordinates.  A one-variable determinant forgets
which Julia channel carries negative orientation.  This file retains that distinction by the
signed row pencil

```text
P_H(z,w) = I + ((diag(z,w) B) tensor H).
```

It is exactly left channel action on P-G105F completed matrix, so no incidence is discarded.  For
each nonnegative eigenvalue `lambda` of `H`, its determinant factor is

```text
1 + lambda z/64 - lambda w - lambda^(2 : ℕ) z w.
```

If `lambda>0` and this factor vanished, then

```text
w = (1 + lambda z/64) / (lambda (1 + lambda z)).
```

This real Möbius map has negative orientation determinant `-63 lambda^(2 : ℕ)/64`, hence sends upper
half-plane to lower half-plane.  The zero eigenvalue factor is one.  Unitary diagonalization is
used only in proof: original pencil retains all off-diagonal prime/depth/ordinate incidence.

This closes finite signed bivariate Krein stability.  It does not identify channel variables with
a physical Stokes current, prove cofinal stability, or identify a limiting divisor with Xi.
-/

open Complex Matrix Set
open scoped Kronecker ComplexOrder

namespace RHTower

noncomputable section

/-- Independent spectral variables on child and negative-pivot Julia channels. -/
def routePPrimitiveGammaJuliaSignedChannelDiagonal (z w : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![z, 0; 0, w]

/-- Universal eigenchannel factor of the signed Julia--Krein pencil. -/
def routePPrimitiveGammaJuliaSignedBivariateFactor (lam : ℝ) (z w : ℂ) : ℂ :=
  1 + (lam / 64 : ℂ) * z - (lam : ℂ) * w - (lam ^ (2 : ℕ) : ℂ) * z * w

/-- Full signed bivariate pencil over an arbitrary finite source matrix. -/
def routePPrimitiveGammaJuliaSignedBivariatePencil {N : ℕ}
    (H : Matrix (Fin N) (Fin N) ℂ) (z w : ℂ) :
    Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ :=
  1 + ((routePPrimitiveGammaJuliaSignedChannelDiagonal z w *
    routePPrimitiveBurnolJuliaKreinBlock) ⊗ₖ H)

/-- Exact determinant of one signed Julia eigenchannel. -/
theorem routePPrimitiveGammaJuliaSignedBivariateFactor_det
    (lam : ℝ) (z w : ℂ) :
    (1 + (lam : ℂ) •
      (routePPrimitiveGammaJuliaSignedChannelDiagonal z w *
        routePPrimitiveBurnolJuliaKreinBlock)).det =
      routePPrimitiveGammaJuliaSignedBivariateFactor lam z w := by
  rw [Matrix.det_fin_two]
  have hr : routeEPCubicFourthDepthJuliaDefect ^ (2 : ℕ) = (63 / 64 : ℝ) := by
    have h := routeEPCubicFourthDepthJulia_pythagoras
    norm_num [routeEPCubicFourthDepthNormalizedContraction] at h
    nlinarith
  have hd : (routeEPCubicFourthDepthJuliaDefect : ℂ) ^ (2 : ℕ) = 63 / 64 := by
    calc
      (routeEPCubicFourthDepthJuliaDefect : ℂ) ^ (2 : ℕ) =
          ((routeEPCubicFourthDepthJuliaDefect ^ (2 : ℕ) : ℝ) : ℂ) :=
        (Complex.ofReal_pow _ _).symm
      _ = ((63 / 64 : ℝ) : ℂ) := congrArg (fun x : ℝ => (x : ℂ)) hr
      _ = 63 / 64 := Complex.ofReal_div _ _
  simp [routePPrimitiveGammaJuliaSignedChannelDiagonal,
    routePPrimitiveBurnolJuliaKreinBlock,
    routePPrimitiveGammaJuliaSignedBivariateFactor]
  ring_nf
  rw [hd]
  ring

/-- The zero relation's real Möbius solver maps upper half-plane strictly to lower half-plane. -/
theorem routePPrimitiveGammaJuliaSignedMobius_im_neg
    (lam : ℝ) (hlam : 0 < lam) (z : ℂ) (hz : 0 < z.im) :
    (((1 : ℂ) + (lam / 64 : ℂ) * z) /
      ((lam : ℂ) * ((1 : ℂ) + (lam : ℂ) * z))).im < 0 := by
  rw [Complex.div_im]
  have hden : 0 < Complex.normSq ((lam : ℂ) * ((1 : ℂ) + (lam : ℂ) * z)) := by
    apply Complex.normSq_pos.mpr
    apply mul_ne_zero
    · exact Complex.ofReal_ne_zero.mpr hlam.ne'
    · intro h
      have him := congrArg Complex.im h
      simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, zero_add, Complex.zero_im] at him
      nlinarith
  have hnum :
      (((1 : ℂ) + (lam / 64 : ℂ) * z).im *
          ((lam : ℂ) * ((1 : ℂ) + (lam : ℂ) * z)).re -
        ((1 : ℂ) + (lam / 64 : ℂ) * z).re *
          ((lam : ℂ) * ((1 : ℂ) + (lam : ℂ) * z)).im) =
        -(63 / 64 : ℝ) * lam ^ (2 : ℕ) * z.im := by
    norm_num [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Complex.add_re, Complex.one_re,
      Complex.mul_re, sub_zero, zero_add]
    ring
  rw [← sub_div, hnum]
  apply div_neg_of_neg_of_pos _ hden
  nlinarith [sq_pos_of_pos hlam]

/-- Every nonnegative eigenchannel factor is bivariate upper-half-plane stable. -/
theorem routePPrimitiveGammaJuliaSignedBivariateFactor_stable
    (lam : ℝ) (hlam : 0 ≤ lam) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    routePPrimitiveGammaJuliaSignedBivariateFactor lam z w ≠ 0 := by
  intro hzero
  rcases hlam.eq_or_lt with rfl | hlam
  · norm_num [routePPrimitiveGammaJuliaSignedBivariateFactor] at hzero
  · have hden : (lam : ℂ) * ((1 : ℂ) + (lam : ℂ) * z) ≠ 0 := by
      apply mul_ne_zero
      · exact Complex.ofReal_ne_zero.mpr hlam.ne'
      · intro h
        have him := congrArg Complex.im h
        simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, add_zero, zero_add, Complex.zero_im] at him
        nlinarith
    have hw_eq : w = ((1 : ℂ) + (lam / 64 : ℂ) * z) /
        ((lam : ℂ) * ((1 : ℂ) + (lam : ℂ) * z)) := by
      apply (eq_div_iff hden).2
      dsimp [routePPrimitiveGammaJuliaSignedBivariateFactor] at hzero
      linear_combination -hzero
    rw [hw_eq] at hw
    exact (not_lt_of_ge
      (le_of_lt (routePPrimitiveGammaJuliaSignedMobius_im_neg lam hlam z hz))) hw

/-- The pencil is literal signed left channel action on the full Julia--Krein completion. -/
theorem routePPrimitiveGammaJuliaSignedBivariatePencil_eq_left_action {N : ℕ}
    (H : Matrix (Fin N) (Fin N) ℂ) (z w : ℂ) :
    routePPrimitiveGammaJuliaSignedBivariatePencil H z w =
      1 + ((routePPrimitiveGammaJuliaSignedChannelDiagonal z w ⊗ₖ
          (1 : Matrix (Fin N) (Fin N) ℂ)) *
        (routePPrimitiveBurnolJuliaKreinBlock ⊗ₖ H)) := by
  rw [routePPrimitiveGammaJuliaSignedBivariatePencil]
  congr 1
  rw [← Matrix.mul_kronecker_mul]
  simp

/-- Exact spectral factorization of the full signed pencil.  Diagonalization occurs only here. -/
theorem routePPrimitiveGammaJuliaSignedBivariatePencil_det_eq_prod_eigenfactors
    {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian) (z w : ℂ) :
    (routePPrimitiveGammaJuliaSignedBivariatePencil H z w).det =
      ∏ i, routePPrimitiveGammaJuliaSignedBivariateFactor (hH.eigenvalues i) z w := by
  let U : Matrix (Fin N) (Fin N) ℂ := hH.eigenvectorUnitary
  let A : Matrix (Fin 2) (Fin 2) ℂ :=
    routePPrimitiveGammaJuliaSignedChannelDiagonal z w *
      routePPrimitiveBurnolJuliaKreinBlock
  let Q : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ :=
    (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ U
  have hU : Uᴴ * U = 1 := by
    change (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)ᴴ *
        (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) = 1
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self _
  have hQ : Qᴴ * Q = 1 := by
    dsimp only [Q]
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.conjTranspose_one, Matrix.one_mul, hU,
      Matrix.one_kronecker_one]
  have hUH : Uᴴ * H * U =
      Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) := by
    exact GaloisForLFunctions.HTGeometry.conjTranspose_mul_mul_eigenvectorUnitary hH
  have hconj :
      Qᴴ * routePPrimitiveGammaJuliaSignedBivariatePencil H z w * Q =
        1 + A ⊗ₖ Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) := by
    rw [routePPrimitiveGammaJuliaSignedBivariatePencil, Matrix.mul_add, Matrix.add_mul]
    rw [Matrix.mul_one, hQ]
    congr 1
    change Qᴴ * (A ⊗ₖ H) * Q = _
    dsimp only [Q]
    rw [Matrix.conjTranspose_kronecker]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hUH]
  have hdet_conj :
      (Qᴴ * routePPrimitiveGammaJuliaSignedBivariatePencil H z w * Q).det =
        (routePPrimitiveGammaJuliaSignedBivariatePencil H z w).det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    have hdetQ : Qᴴ.det * Q.det = 1 := by
      rw [← Matrix.det_mul, hQ, Matrix.det_one]
    calc
      Qᴴ.det * (routePPrimitiveGammaJuliaSignedBivariatePencil H z w).det * Q.det =
          (Qᴴ.det * Q.det) *
            (routePPrimitiveGammaJuliaSignedBivariatePencil H z w).det := by ring
      _ = (routePPrimitiveGammaJuliaSignedBivariatePencil H z w).det := by
        rw [hdetQ, one_mul]
  have hblock :
      1 + A ⊗ₖ Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) =
        Matrix.blockDiagonal (fun i : Fin N =>
          1 + ((hH.eigenvalues i : ℝ) : ℂ) • A) := by
    rw [Matrix.kronecker_diagonal]
    ext ⟨a, i⟩ ⟨b, j⟩
    by_cases hij : i = j
    · subst j
      simp [Matrix.blockDiagonal_apply_eq, Matrix.one_apply]
    · simp [Matrix.blockDiagonal_apply_ne _ _ _ hij, hij]
  rw [← hdet_conj, hconj, hblock, Matrix.det_blockDiagonal]
  apply Finset.prod_congr rfl
  intro i _hi
  exact routePPrimitiveGammaJuliaSignedBivariateFactor_det (hH.eigenvalues i) z w

/-- Prime-log diagonal is Hermitian because its entries are real prime logarithms. -/
theorem routePPrimitiveJointDepthPrimeLogDiagonal_conjTranspose {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) :
    (routePPrimitiveJointDepthPrimeLogDiagonal pe)ᴴ =
      routePPrimitiveJointDepthPrimeLogDiagonal pe := by
  rw [routePPrimitiveJointDepthPrimeLogDiagonal, diagonal_conjTranspose]
  congr 1
  funext i
  change star ((Real.log (pe i).1 : ℂ)) = (Real.log (pe i).1 : ℂ)
  rw [← starRingEnd_apply, Complex.conj_ofReal]

/-- Actual prime-log-conjugated P-G186 window Gram is positive semidefinite. -/
theorem routePPrimitiveBurnolPrimeLogConjugate_posSemidef {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    (routePPrimitiveJointDepthPrimeLogConjugate pe
      (routePPrimitiveBurnolWindowGramMatrix pe kappa)).PosSemidef := by
  have h := (routePPrimitiveBurnolWindowGramMatrix_posSemidef pe kappa).conjTranspose_mul_mul_same
    (routePPrimitiveJointDepthPrimeLogDiagonal pe)
  rw [routePPrimitiveJointDepthPrimeLogDiagonal_conjTranspose] at h
  exact h

/-- Actual finite prime-log Gamma--Julia signed pencil over P-G186 source incidence. -/
def routePPrimitiveBurnolGammaJuliaSignedBivariatePencil {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) (z w : ℂ) :
    Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ :=
  routePPrimitiveGammaJuliaSignedBivariatePencil
    (routePPrimitiveJointDepthPrimeLogConjugate pe
      (routePPrimitiveBurnolWindowGramMatrix pe kappa)) z w

/-- Actual pencil is signed left action on P-G105F's full completed matrix. -/
theorem routePPrimitiveBurnolGammaJuliaSignedBivariatePencil_eq_completed_left_action
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) (z w : ℂ) :
    routePPrimitiveBurnolGammaJuliaSignedBivariatePencil pe kappa z w =
      1 + ((routePPrimitiveGammaJuliaSignedChannelDiagonal z w ⊗ₖ
          (1 : Matrix (Fin N) (Fin N) ℂ)) *
        routePPrimitiveBurnolGammaJuliaLogKreinCompletedMatrix pe kappa) := by
  rw [routePPrimitiveBurnolGammaJuliaSignedBivariatePencil,
    routePPrimitiveGammaJuliaSignedBivariatePencil_eq_left_action,
    routePPrimitiveBurnolGammaJuliaLogKreinCompletedMatrix,
    routePPrimitiveJointDepthGammaJuliaLogKreinCompletedMatrix]

/-- Exact eigenfactor product for actual full finite prime-log completed incidence. -/
theorem routePPrimitiveBurnolGammaJuliaSignedBivariatePencil_det_eq_prod_eigenfactors
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) (z w : ℂ) :
    (routePPrimitiveBurnolGammaJuliaSignedBivariatePencil pe kappa z w).det =
      ∏ i, routePPrimitiveGammaJuliaSignedBivariateFactor
        ((routePPrimitiveBurnolPrimeLogConjugate_posSemidef pe kappa).isHermitian.eigenvalues i)
        z w := by
  rw [routePPrimitiveBurnolGammaJuliaSignedBivariatePencil]
  exact routePPrimitiveGammaJuliaSignedBivariatePencil_det_eq_prod_eigenfactors _
    (routePPrimitiveBurnolPrimeLogConjugate_posSemidef pe kappa).isHermitian z w

/-- **P-G105G finite stability.** Actual full completed pencil never vanishes when both signed
channel variables lie in the open upper half-plane. -/
theorem routePPrimitiveBurnolGammaJuliaSignedBivariatePencil_stable
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    (routePPrimitiveBurnolGammaJuliaSignedBivariatePencil pe kappa z w).det ≠ 0 := by
  rw [routePPrimitiveBurnolGammaJuliaSignedBivariatePencil_det_eq_prod_eigenfactors]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _hi
  exact routePPrimitiveGammaJuliaSignedBivariateFactor_stable _
    ((routePPrimitiveBurnolPrimeLogConjugate_posSemidef pe kappa).eigenvalues_nonneg i) hz hw

/-- P-G105G capstone: premise-free actual-window family, exact factorization, and full bivariate
upper-half-plane stability. -/
theorem routePPrimitiveBurnol_GammaJulia_signedBivariateStability
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    (∀ z w : ℂ, 0 < z.im → 0 < w.im →
      (routePPrimitiveBurnolGammaJuliaSignedBivariatePencil pe kappa z w).det ≠ 0) ∧
    (∀ z w : ℂ,
      (routePPrimitiveBurnolGammaJuliaSignedBivariatePencil pe kappa z w).det =
        ∏ i, routePPrimitiveGammaJuliaSignedBivariateFactor
          ((routePPrimitiveBurnolPrimeLogConjugate_posSemidef pe kappa).isHermitian.eigenvalues i)
          z w) :=
  ⟨fun _ _ => routePPrimitiveBurnolGammaJuliaSignedBivariatePencil_stable pe kappa,
    routePPrimitiveBurnolGammaJuliaSignedBivariatePencil_det_eq_prod_eigenfactors pe kappa⟩

end
end RHTower
