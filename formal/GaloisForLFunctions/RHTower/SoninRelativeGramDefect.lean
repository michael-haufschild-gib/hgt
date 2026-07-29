/-
# The principal-relative Sonin Gram defect

The residual Gram `R†R` squares every Euler coefficient and therefore cannot by itself recover
the logarithmic prime modes.  The relative Gram defect keeps the principal corner `P`:

`(P + cR)†(P + cR) - P†P
  = c P†R + star(c) R†P + star(c)c R†R`.

Thus the actual Sonin source has a canonical term linear in the logarithmic Euler coefficient.
The whole defect is Hilbert--Schmidt without an extra hypothesis; only the quadratic remainder is
automatically trace class.  Producing a scalar relative trace from the linear cross term remains
the source-side open core.
-/
import GaloisForLFunctions.RHTower.SoninTimeBandHilbertSchmidt

noncomputable section

namespace RHTower

open ContinuousLinearMap

private theorem sonin_adjoint_add
    (S T : SoninL2 →L[Complex] SoninL2) :
    ContinuousLinearMap.adjoint (S + T) =
      ContinuousLinearMap.adjoint S + ContinuousLinearMap.adjoint T := by
  let adj : (SoninL2 →L[Complex] SoninL2) ≃ₗᵢ⋆[Complex]
      (SoninL2 →L[Complex] SoninL2) := ContinuousLinearMap.adjoint
  exact adj.map_add S T

private theorem sonin_adjoint_sub
    (S T : SoninL2 →L[Complex] SoninL2) :
    ContinuousLinearMap.adjoint (S - T) =
      ContinuousLinearMap.adjoint S - ContinuousLinearMap.adjoint T := by
  let adj : (SoninL2 →L[Complex] SoninL2) ≃ₗᵢ⋆[Complex]
      (SoninL2 →L[Complex] SoninL2) := ContinuousLinearMap.adjoint
  exact adj.map_sub S T

private theorem sonin_adjoint_mul
    (S T : SoninL2 →L[Complex] SoninL2) :
    ContinuousLinearMap.adjoint (S * T) =
      ContinuousLinearMap.adjoint T * ContinuousLinearMap.adjoint S := by
  exact ContinuousLinearMap.adjoint_comp S T

theorem sonin_adjoint_smul (c : Complex)
    (T : SoninL2 →L[Complex] SoninL2) :
    ContinuousLinearMap.adjoint (c • T) =
      star c • ContinuousLinearMap.adjoint T := by
  change star (c • T) = star c • star T
  rw [star_smul]

/-- Difference between the actual one-scale Sonin Gram and the formal-principal Gram. -/
def centralSoninRelativeGramDefect
    (a p : ℝ) (hp : 1 < p) : SoninL2 →L[Complex] SoninL2 :=
  ContinuousLinearMap.adjoint
      (crossBoundary (centralSoninProjection a) (dilationSum p hp)) *
      crossBoundary (centralSoninProjection a) (dilationSum p hp) -
    ContinuousLinearMap.adjoint (centralSoninPrincipalDilationCorner a p hp) *
      centralSoninPrincipalDilationCorner a p hp

/-- The part of the relative Gram defect which is linear in the principal-subtracted residual. -/
def centralSoninRelativeGramLinearCross
    (a p : ℝ) (hp : 1 < p) : SoninL2 →L[Complex] SoninL2 :=
  ContinuousLinearMap.adjoint (centralSoninPrincipalDilationCorner a p hp) *
      centralSoninDilationCornerResidual a p hp +
    ContinuousLinearMap.adjoint (centralSoninDilationCornerResidual a p hp) *
      centralSoninPrincipalDilationCorner a p hp

/-- Exact principal-linear/quadratic decomposition of the unweighted relative Gram defect. -/
theorem centralSoninRelativeGramDefect_eq_linearCross_add_energy
    (a p : ℝ) (hp : 1 < p) :
    centralSoninRelativeGramDefect a p hp =
      centralSoninRelativeGramLinearCross a p hp +
        centralSoninDilationCornerResidualEnergy a p hp := by
  let A := crossBoundary (centralSoninProjection a) (dilationSum p hp)
  let P := centralSoninPrincipalDilationCorner a p hp
  let R := centralSoninDilationCornerResidual a p hp
  have hA : A = R + P := by
    simp only [A, R, centralSoninDilationCornerResidual]
    abel
  simp only [centralSoninRelativeGramDefect,
    centralSoninRelativeGramLinearCross,
    centralSoninDilationCornerResidualEnergy]
  change ContinuousLinearMap.adjoint A * A - ContinuousLinearMap.adjoint P * P =
    ContinuousLinearMap.adjoint P * R + ContinuousLinearMap.adjoint R * P +
      ContinuousLinearMap.adjoint R * R
  rw [hA, sonin_adjoint_add]
  noncomm_ring

/-- The principal/residual cross term is unconditionally Hilbert--Schmidt. -/
theorem centralSoninRelativeGramLinearCross_isHilbertSchmidt
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    IsHilbertSchmidt (centralSoninRelativeGramLinearCross a p hp) := by
  have hR := centralSoninDilationCornerResidual_isHilbertSchmidt a p ha hp
  exact (hR.comp_left
    (ContinuousLinearMap.adjoint (centralSoninPrincipalDilationCorner a p hp))).add
    (hR.adjoint.comp_right (centralSoninPrincipalDilationCorner a p hp))

/-- The full relative Gram defect is unconditionally Hilbert--Schmidt. -/
theorem centralSoninRelativeGramDefect_isHilbertSchmidt
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    IsHilbertSchmidt (centralSoninRelativeGramDefect a p hp) := by
  rw [centralSoninRelativeGramDefect_eq_linearCross_add_energy]
  have hR := centralSoninDilationCornerResidual_isHilbertSchmidt a p ha hp
  exact (centralSoninRelativeGramLinearCross_isHilbertSchmidt a p ha hp).add
    (hR.adjoint.comp_right (centralSoninDilationCornerResidual a p hp))

/-- A relative Gram defect is self-adjoint before any trace or spectral interpretation. -/
theorem adjoint_centralSoninRelativeGramDefect
    (a p : ℝ) (hp : 1 < p) :
    ContinuousLinearMap.adjoint (centralSoninRelativeGramDefect a p hp) =
      centralSoninRelativeGramDefect a p hp := by
  rw [centralSoninRelativeGramDefect, sonin_adjoint_sub,
    sonin_adjoint_mul, sonin_adjoint_mul, adjoint_adjoint, adjoint_adjoint]

/-- Principal-relative Gram defect after weighting the actual residual by `c`. -/
def centralSoninWeightedRelativeGramDefect
    (a p : ℝ) (hp : 1 < p) (c : Complex) : SoninL2 →L[Complex] SoninL2 :=
  let P := centralSoninPrincipalDilationCorner a p hp
  let R := centralSoninDilationCornerResidual a p hp
  ContinuousLinearMap.adjoint (P + c • R) * (P + c • R) -
    ContinuousLinearMap.adjoint P * P

/-- **Linear Euler interface.**  The principal-relative defect contains `c` and `star c`
linearly; only its residual energy uses the squared coefficient `star c * c`. -/
theorem centralSoninWeightedRelativeGramDefect_eq
    (a p : ℝ) (hp : 1 < p) (c : Complex) :
    centralSoninWeightedRelativeGramDefect a p hp c =
      c • (ContinuousLinearMap.adjoint
          (centralSoninPrincipalDilationCorner a p hp) *
            centralSoninDilationCornerResidual a p hp) +
      star c • (ContinuousLinearMap.adjoint
          (centralSoninDilationCornerResidual a p hp) *
            centralSoninPrincipalDilationCorner a p hp) +
      (star c * c) • centralSoninDilationCornerResidualEnergy a p hp := by
  let P := centralSoninPrincipalDilationCorner a p hp
  let R := centralSoninDilationCornerResidual a p hp
  simp only [centralSoninWeightedRelativeGramDefect,
    centralSoninDilationCornerResidualEnergy]
  change ContinuousLinearMap.adjoint (P + c • R) * (P + c • R) -
      ContinuousLinearMap.adjoint P * P =
    c • (ContinuousLinearMap.adjoint P * R) +
      star c • (ContinuousLinearMap.adjoint R * P) +
        (star c * c) • (ContinuousLinearMap.adjoint R * R)
  rw [sonin_adjoint_add, sonin_adjoint_smul]
  apply ContinuousLinearMap.ext
  intro x
  simp only [mul_apply_eq_comp, _root_.add_apply,
    _root_.sub_apply, _root_.smul_apply, map_add, map_smul]
  module

/-- Weighting does not reintroduce a Schatten hypothesis: the full relative defect remains
Hilbert--Schmidt for every scalar coefficient. -/
theorem centralSoninWeightedRelativeGramDefect_isHilbertSchmidt
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) (c : Complex) :
    IsHilbertSchmidt (centralSoninWeightedRelativeGramDefect a p hp c) := by
  rw [centralSoninWeightedRelativeGramDefect_eq]
  have hR := centralSoninDilationCornerResidual_isHilbertSchmidt a p ha hp
  exact ((hR.comp_left
      (ContinuousLinearMap.adjoint (centralSoninPrincipalDilationCorner a p hp))).smul c).add
    ((hR.adjoint.comp_right
      (centralSoninPrincipalDilationCorner a p hp)).smul (star c)) |>.add
      ((hR.adjoint.comp_right
        (centralSoninDilationCornerResidual a p hp)).smul (star c * c))

/-- The principal-relative Gram defect at the actual prime-power scale, weighted by the exact
logarithmic Euler coefficient used by the Sonin tail. -/
def centralSoninPrimePowerRelativeGramDefect
    (a : ℝ) (pk : Nat.Primes × ℕ) : SoninL2 →L[Complex] SoninL2 :=
  centralSoninWeightedRelativeGramDefect a (soninPrimePowerScale pk)
    (one_lt_soninPrimePowerScale pk) (soninLogPrimePowerCoefficient pk)

/-- The prime-power relative defect is Hilbert--Schmidt with no source hypothesis. -/
theorem centralSoninPrimePowerRelativeGramDefect_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    IsHilbertSchmidt (centralSoninPrimePowerRelativeGramDefect a pk) := by
  exact centralSoninWeightedRelativeGramDefect_isHilbertSchmidt a
    (soninPrimePowerScale pk) ha (one_lt_soninPrimePowerScale pk)
    (soninLogPrimePowerCoefficient pk)

/-- At every prime power the relative defect exposes the unsquared logarithmic coefficient in
its two principal/residual cross terms.  The coefficient is squared only in the final
trace-class residual energy. -/
theorem centralSoninPrimePowerRelativeGramDefect_eq
    (a : ℝ) (pk : Nat.Primes × ℕ) :
    centralSoninPrimePowerRelativeGramDefect a pk =
      soninLogPrimePowerCoefficient pk •
        (ContinuousLinearMap.adjoint
          (centralSoninPrincipalDilationCorner a (soninPrimePowerScale pk)
            (one_lt_soninPrimePowerScale pk)) *
          centralSoninPrimePowerResidual a pk) +
      star (soninLogPrimePowerCoefficient pk) •
        (ContinuousLinearMap.adjoint (centralSoninPrimePowerResidual a pk) *
          centralSoninPrincipalDilationCorner a (soninPrimePowerScale pk)
            (one_lt_soninPrimePowerScale pk)) +
      (star (soninLogPrimePowerCoefficient pk) * soninLogPrimePowerCoefficient pk) •
        centralSoninDilationCornerResidualEnergy a (soninPrimePowerScale pk)
          (one_lt_soninPrimePowerScale pk) := by
  exact centralSoninWeightedRelativeGramDefect_eq a (soninPrimePowerScale pk)
    (one_lt_soninPrimePowerScale pk) (soninLogPrimePowerCoefficient pk)

end RHTower
