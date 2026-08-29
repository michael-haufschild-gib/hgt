import GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeSourcePositiveFiniteModuleNoGo

/-!
# No infinite scalar contravariant form for the full source-positive theta sl₂ carrier

The finite trace obstruction does not disappear on the full infinite polynomial carrier.
Two exact source witnesses impose incompatible star signs.  The affine vacuum extension
`E 1 = 0`, `F B = -1` forces a scalar adjoint coefficient to vanish.  The positive
lowest-weight string `F r = 0`, `H r = 2r` forces that same coefficient to be negative.

The result needs neither finite dimensionality nor completeness.  It rules out the full-carrier
scalar Shapovalov/contravariant-form ansatz for the remaining theta rank-three D1 gate.  It does
not rule out a proper carrier excluding the affine vacuum extension, a non-scalar adjoint law,
an indefinite/Krein form, or a direct cross-scale congruence.
-/

open Complex Real

namespace HTGeometry

noncomputable section

/-- Minimal scalar-sesquilinear positive form required by a scalar contravariant ansatz.
Hermitian symmetry and additivity are deliberately not assumed: the obstruction only needs the
two scalar laws and strict positivity on nonzero diagonal vectors. -/
structure ModularThetaSourcePositiveScalarContravariantForm (c : ℝ) where
  pair : ModularThetaSourcePositivePolynomial →
    ModularThetaSourcePositivePolynomial → ℂ
  smul_left : ∀ (a : ℂ) (p q : ModularThetaSourcePositivePolynomial),
    pair (a • p) q = star a * pair p q
  smul_right : ∀ (a : ℂ) (p q : ModularThetaSourcePositivePolynomial),
    pair p (a • q) = a * pair p q
  positive : ∀ p : ModularThetaSourcePositivePolynomial,
    p ≠ 0 → 0 < (pair p p).re
  contravariant : ∀ p q : ModularThetaSourcePositivePolynomial,
    pair (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E p) q =
      pair p ((c : ℂ) •
        modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F q)

/-- The raising Lie derivative kills the vacuum polynomial. -/
theorem modularThetaSourcePositiveFieldLie_sl2E_one :
    modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E
      (1 : ModularThetaSourcePositivePolynomial) = 0 := by
  simp [modularThetaSourcePositiveFieldLie]

/-- The lowering Lie derivative sends the affine clock coordinate `B` to `-1`. -/
theorem modularThetaSourcePositiveFieldLie_sl2F_B :
    modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F
      (MvPolynomial.X .B) = -(1 : ModularThetaSourcePositivePolynomial) := by
  apply MvPolynomial.funext
  intro v
  simp [modularThetaSourcePositiveFieldLie,
    modularThetaSourcePositiveSl2F,
    modularThetaSourcePositiveLoweringField]

/-- The horizontal adapted coordinate `r=U+3B` is a nonzero polynomial. -/
theorem modularThetaSourcePositiveSl2R_ne_zero :
    modularThetaSourcePositiveSl2R ≠ 0 := by
  intro h
  have hv := congrArg
    (MvPolynomial.eval (fun i => match i with
      | .U => (1 : ℂ)
      | .B => 0
      | .Q => 0)) h
  simp [modularThetaSourcePositiveSl2R] at hv

/-- The adapted coordinate `r` is a lowest-weight vector. -/
theorem modularThetaSourcePositiveFieldLie_sl2F_R :
    modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F
      modularThetaSourcePositiveSl2R = 0 := by
  apply MvPolynomial.funext
  intro v
  simp [modularThetaSourcePositiveFieldLie,
    modularThetaSourcePositiveSl2F,
    modularThetaSourcePositiveLoweringField,
    modularThetaSourcePositiveSl2R]

/-- The Cartan weight of `r` is exactly two. -/
theorem modularThetaSourcePositiveFieldLie_sl2H_R :
    modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2H
      modularThetaSourcePositiveSl2R =
        (2 : ℂ) • modularThetaSourcePositiveSl2R := by
  apply MvPolynomial.funext
  intro v
  simp [modularThetaSourcePositiveFieldLie,
    modularThetaSourcePositiveSl2H,
    modularThetaSourcePositiveScaleField,
    modularThetaSourcePositiveSl2R]
  ring

/-- Raising `r` is nonzero; at the zero source state its value is exactly six. -/
theorem modularThetaSourcePositiveFieldLie_sl2E_R_ne_zero :
    modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E
      modularThetaSourcePositiveSl2R ≠ 0 := by
  intro h
  have hv := congrArg (MvPolynomial.eval (fun _ => (0 : ℂ))) h
  simp [modularThetaSourcePositiveFieldLie,
    modularThetaSourcePositiveSl2E,
    modularThetaSourcePositiveVectorField,
    modularThetaSourcePositiveLoweringField,
    modularThetaSourcePositiveSl2R] at hv
  norm_num at hv

/-- The lowest-weight relation forced by `[E,F]=H`: `F(E r)=-2r`. -/
theorem modularThetaSourcePositiveFieldLie_sl2F_sl2E_R :
    modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F
      (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E
        modularThetaSourcePositiveSl2R) =
      (-2 : ℂ) • modularThetaSourcePositiveSl2R := by
  have h := modularThetaSourcePositiveFieldLie_sl2_ef
    modularThetaSourcePositiveSl2R
  rw [modularThetaSourcePositiveFieldLie_sl2F_R,
    modularThetaSourcePositiveFieldLie_sl2H_R] at h
  have hEzero :
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E
        (0 : ModularThetaSourcePositivePolynomial) = 0 := by
    simp [modularThetaSourcePositiveFieldLie]
  rw [hEzero] at h
  have hneg := congrArg Neg.neg h
  simpa using hneg

/-- **Vacuum rigidity.** The affine extension `(1,B)` forces every scalar contravariant
coefficient to vanish. -/
theorem modularThetaSourcePositive_scalarContravariant_eq_zero_of_vacuum
    (c : ℝ) (B : ModularThetaSourcePositiveScalarContravariantForm c) :
    c = 0 := by
  have h := B.contravariant
    (1 : ModularThetaSourcePositivePolynomial) (MvPolynomial.X .B)
  rw [modularThetaSourcePositiveFieldLie_sl2E_one,
    modularThetaSourcePositiveFieldLie_sl2F_B] at h
  have hleft := B.smul_left (0 : ℂ)
    (1 : ModularThetaSourcePositivePolynomial) (MvPolynomial.X .B)
  have hright := B.smul_right (-(c : ℂ))
    (1 : ModularThetaSourcePositivePolynomial)
    (1 : ModularThetaSourcePositivePolynomial)
  have hpair : B.pair
      (1 : ModularThetaSourcePositivePolynomial)
      ((c : ℂ) • -(1 : ModularThetaSourcePositivePolynomial)) =
      (-(c : ℂ)) * B.pair 1 1 := by
    rw [show (c : ℂ) • -(1 : ModularThetaSourcePositivePolynomial) =
      (-(c : ℂ)) • (1 : ModularThetaSourcePositivePolynomial) by module]
    exact hright
  have hzero : B.pair 0 (MvPolynomial.X .B) = 0 := by
    simpa using hleft
  rw [hzero, hpair] at h
  have hre := congrArg Complex.re h
  have hpos := B.positive (1 : ModularThetaSourcePositivePolynomial) one_ne_zero
  simp at hre
  rcases hre with hc | hp
  · exact hc
  · exfalso
    linarith

/-- **Lowest-weight sign rigidity.** The positive string generated by `r` forces every scalar
contravariant coefficient to have the noncompact sign. -/
theorem modularThetaSourcePositive_scalarContravariant_neg_of_lowestWeight
    (c : ℝ) (B : ModularThetaSourcePositiveScalarContravariantForm c) :
    c < 0 := by
  let eR := modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E
    modularThetaSourcePositiveSl2R
  have h := B.contravariant modularThetaSourcePositiveSl2R eR
  change B.pair eR eR = B.pair modularThetaSourcePositiveSl2R
    ((c : ℂ) • modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F eR) at h
  rw [show modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F eR =
    (-2 : ℂ) • modularThetaSourcePositiveSl2R by
      exact modularThetaSourcePositiveFieldLie_sl2F_sl2E_R] at h
  have hright := B.smul_right ((c : ℂ) * (-2 : ℂ))
    modularThetaSourcePositiveSl2R modularThetaSourcePositiveSl2R
  rw [smul_smul, hright] at h
  have hre := congrArg Complex.re h
  have hposR := B.positive modularThetaSourcePositiveSl2R
    modularThetaSourcePositiveSl2R_ne_zero
  have hposER := B.positive eR modularThetaSourcePositiveFieldLie_sl2E_R_ne_zero
  simp at hre
  nlinarith

/-- **Infinite full-carrier no-go.** No real scalar makes the exact source-positive polynomial
`sl₂` action contravariant for a positive scalar-sesquilinear form.  Vacuum rigidity forces the
scalar to be zero, while lowest-weight sign rigidity forces it to be negative. -/
theorem modularThetaSourcePositive_no_infinite_scalarContravariantForm :
    ¬ ∃ (c : ℝ), Nonempty
      (ModularThetaSourcePositiveScalarContravariantForm c) := by
  rintro ⟨c, ⟨B⟩⟩
  have hz := modularThetaSourcePositive_scalarContravariant_eq_zero_of_vacuum c B
  have hn := modularThetaSourcePositive_scalarContravariant_neg_of_lowestWeight c B
  linarith

end

end HTGeometry
