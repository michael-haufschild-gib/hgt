import GaloisForLFunctions.FamilyContinuationTheory.TheLocalFactorOfThePoissonSeriesIsExplicit
import GaloisForLFunctions.FamilyContinuationTheory.TheSeriesOfAMultiplicativeFunctionIsItsEulerProduct
import GaloisForLFunctions.FamilyContinuationTheory.TheCorrectionOfThePrincipalRowIsAConvergentEulerProduct

/-!
# The principal row is an Euler product

The row `u = 1` of the Poisson series of the cubic-theta probe has, at a primary prime `π ∤ 6` with
`N(π) = Q`, `κ = ᾱ η_π`, `X = Q^{−x}`, `Y = Q^{−w}`, `V = Q^{−6z}`, `R = κ⁶ Q⁴ X⁶ V`, the local sum

`P = (1 − V)⁻¹ + Y (1 − Y)⁻¹ + (1 − R)⁻¹ (R (1 − Q⁻¹)(1 − V)⁻¹ + Y R − η_π X
      − η_π (Q − 1) X Y V (1 − V)⁻¹)`   (`principalSum`, `hasSum_localTerm_one`),

the specialization `j = 0`, `ρ = 1` of the complete local identity. Its correction
`H = P (1 − V)(1 − Y)/(1 − η_π X)` (`principalH`) is, at the double residue `w = 1`, `z = 1/6`,
the local factor `h(s) = (1 − q²)(1 − q (R − D)/(1 − D))/(1 − R)` of the correction of the target
(`principalH_residue`), with the phase `A = κ⁶ = ᾱ⁶ η_π⁶`.

On `Re x ≥ 3`, `Re w ≥ 3`, `Re z ≥ 2` the excess mass of the local series is at most `8 N(π)^{−2}`
(`tsum_norm_localTerm_one_sub_one_le`); the general Euler product then makes the principal row
the product of the local sums over the good primes.
-/

noncomputable section

open scoped BigOperators Classical ComplexConjugate

namespace GaloisForLFunctions.FamilyContinuationTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

/-- The local sum of the principal row. -/
def principalSum (Q κ ηp X Y V : ℂ) : ℂ :=
  (1 - V)⁻¹ + Y * (1 - Y)⁻¹ + (1 - κ ^ 6 * Q ^ 4 * X ^ 6 * V)⁻¹ *
    (κ ^ 6 * Q ^ 4 * X ^ 6 * V * (1 - Q⁻¹) * (1 - V)⁻¹ + Y * (κ ^ 6 * Q ^ 4 * X ^ 6 * V) -
      ηp * X - ηp * (Q - 1) * X * Y * V * (1 - V)⁻¹)

/-- The local correction of the principal row: the local sum with the Euler factors of
`ζ(6z) ζ(w)/L(x, η)` removed. -/
def principalH (Q κ ηp X Y V : ℂ) : ℂ :=
  principalSum Q κ ηp X Y V * (1 - V) * (1 - Y) / (1 - ηp * X)

/-- **At the double residue the correction is the local factor of the target.** For `Q > 0`,
`H(Q^{−s}, Q⁻¹, Q⁻¹) = h(s)` with the phase `κ⁶`. -/
theorem principalH_residue {Q : ℝ} (hQ : 0 < Q) (κ ηp s : ℂ)
    (hD : 1 - ηp * (Q : ℂ) ^ (-s) ≠ 0) (hR : 1 - κ ^ 6 * (Q : ℂ) ^ (3 - 6 * s) ≠ 0)
    (hq : 1 - (Q : ℂ)⁻¹ ≠ 0) :
    principalH Q κ ηp ((Q : ℂ) ^ (-s)) (Q : ℂ)⁻¹ (Q : ℂ)⁻¹ =
      principalLocalFactor Q (κ ^ 6) ηp s := by
  have hQ0 : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  have hX6 : ((Q : ℂ) ^ (-s)) ^ 6 = (Q : ℂ) ^ (-(6 * s)) := by
    rw [← Complex.cpow_nat_mul]
    ring_nf
  have h36 : (Q : ℂ) ^ (3 - 6 * s) = (Q : ℂ) ^ 3 * (Q : ℂ) ^ (-(6 * s)) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hQ0, show ((3 : ℂ)) = ((3 : ℕ) : ℂ) by norm_num,
      Complex.cpow_natCast]
  have hQ1 : (Q : ℂ) - 1 ≠ 0 := by
    intro h
    apply hq
    rw [show (Q : ℂ) = 1 by linear_combination h, inv_one, sub_self]
  unfold principalH principalSum principalLocalFactor
  rw [hX6]
  rw [h36] at hR ⊢
  have hRR : κ ^ 6 * (Q : ℂ) ^ 4 * (Q : ℂ) ^ (-(6 * s)) * (Q : ℂ)⁻¹ =
      κ ^ 6 * ((Q : ℂ) ^ 3 * (Q : ℂ) ^ (-(6 * s))) := by
    field_simp
  rw [hRR]
  generalize (Q : ℂ) ^ (-(6 * s)) = E at hR ⊢
  generalize (Q : ℂ) ^ (-s) = X at hD ⊢
  field_simp
  ring

end GaloisForLFunctions.FamilyContinuationTheory
