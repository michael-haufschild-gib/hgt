import GaloisForLFunctions.HTGeometry.HahnDilation
import GaloisForLFunctions.HTGeometry.HahnLeadingCoefficient

/-!
# The multi-graded Newton model

The value group `Lex (Fin n → ℤ)` records the exponent of each coordinate separately, so the
coordinate derivations are graded operators: `∂/∂X_j` shifts the `j`-th component by one and
multiplies the coefficient by the exponent.  That is exactly the invariant a several-variable
Newton-corner degeneration has to propagate.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries

/-- The multi-degree group of `n` coordinates. -/
abbrev mgDeg (n : ℕ) : Type := Lex (Fin n → ℤ)

/-- The `j`-th component of a multi-degree, as an additive character. -/
def mgComp (n : ℕ) (j : Fin n) : mgDeg n →+ ℂ where
  toFun γ := ((ofLex γ j : ℤ) : ℂ)
  map_zero' := by
    show (((0 : Fin n → ℤ) j : ℤ) : ℂ) = 0
    rw [Pi.zero_apply]
    norm_num
  map_add' a b := by
    have h : (ofLex (a + b) j) = ofLex a j + ofLex b j := rfl
    show ((ofLex (a + b) j : ℤ) : ℂ) = ((ofLex a j : ℤ) : ℂ) + ((ofLex b j : ℤ) : ℂ)
    rw [h]
    push_cast
    ring

/-- The multi-degree of `X_j`: exponent one in the `j`-th coordinate. -/
def mgUnit (n : ℕ) (j : Fin n) : mgDeg n := toLex (Pi.single j (-1 : ℤ))

/-- The multi-degree shift produced by `∂/∂X_j`. -/
def mgStep (n : ℕ) (j : Fin n) : mgDeg n := toLex (Pi.single j (1 : ℤ))

/-- The `j`-th coordinate, as a Hahn monomial. -/
noncomputable def mgX (n : ℕ) (j : Fin n) : HahnSeries (mgDeg n) ℂ :=
  HahnSeries.single (mgUnit n j) 1

/-- The `j`-th Euler operator: multiplication by the `j`-th exponent. -/
noncomputable def mgEuler (n : ℕ) (j : Fin n) :
    Derivation ℤ (HahnSeries (mgDeg n) ℂ) (HahnSeries (mgDeg n) ℂ) :=
  hahnDerivation (mgComp n j)

/-- The monomial by which the `j`-th Euler operator is rescaled. -/
noncomputable def mgShift (n : ℕ) (j : Fin n) : HahnSeries (mgDeg n) ℂ :=
  HahnSeries.single (mgStep n j) (1 : ℂ)

/-- The `j`-th coordinate derivation, `-∂/∂X_j` up to the sign that the Jacobian criterion
does not see. -/
noncomputable def mgPartial (n : ℕ) (j : Fin n) :
    Derivation ℤ (HahnSeries (mgDeg n) ℂ) (HahnSeries (mgDeg n) ℂ) :=
  (mgShift n j) • mgEuler n j

theorem coeff_mgPartial (n : ℕ) (j : Fin n) (f : HahnSeries (mgDeg n) ℂ) (γ : mgDeg n) :
    (mgPartial n j f).coeff (γ + mgStep n j) = ((ofLex γ j : ℤ) : ℂ) * f.coeff γ := by
  have hd : mgPartial n j f = (mgShift n j) * hahnGrade (mgComp n j) f := by
    show ((mgShift n j) • (mgEuler n j)) f = _
    simp only [Derivation.coe_smul, Pi.smul_apply, smul_eq_mul]
    rfl
  rw [hd, mgShift, HahnSeries.coeff_single_mul, coeff_hahnGrade]
  have hidx : γ + mgStep n j - mgStep n j = γ := by ring
  rw [hidx]
  show 1 * (((ofLex γ j : ℤ) : ℂ) * f.coeff γ) = _
  ring

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open HahnSeries

/-- **The coordinate derivations act on boundary coefficients by the exponent.** -/
theorem hasLeadAt_mgPartial {n : ℕ} {j : Fin n} {f : HahnSeries (mgDeg n) ℂ} {d : mgDeg n} {c : ℂ}
    (h : HasLeadAt f d c) :
    HasLeadAt (mgPartial n j f) (d + mgStep n j) (((ofLex d j : ℤ) : ℂ) * c) := by
  constructor
  · intro k hk
    have hd : mgPartial n j f = (mgShift n j) * hahnGrade (mgComp n j) f := by
      show ((mgShift n j) • (mgEuler n j)) f = _
      simp only [Derivation.coe_smul, Pi.smul_apply, smul_eq_mul]
      rfl
    rw [hd, mgShift, HahnSeries.coeff_single_mul, coeff_hahnGrade]
    have hlt : k - mgStep n j < d := by
      have hstep : k - mgStep n j + mgStep n j = k := by ring
      refine lt_of_add_lt_add_right (a := mgStep n j) ?_
      rw [hstep]
      exact hk
    rw [h.1 _ hlt]
    ring
  · rw [coeff_mgPartial, h.2]

end GaloisForLFunctions.HTGeometry
