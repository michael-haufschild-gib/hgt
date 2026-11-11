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
  generalize κ ^ 6 * ((Q : ℂ) ^ 3 * (Q : ℂ) ^ (-(6 * s))) = R at hR ⊢
  generalize (Q : ℂ) ^ (-s) = X at hD ⊢
  field_simp
  ring

section Prime

variable (π : O) [NeZero π] [hP : (Ideal.span {π}).IsMaximal] (hlam : lambda ∉ Ideal.span {π})
  (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1)

theorem one_not_mem_span_prime : (1 : O) ∉ Ideal.span {π} := fun h =>
  (prime_of_isMaximal_span π).not_unit (isUnit_of_dvd_one (Ideal.mem_span_singleton.mp h))

omit [NeZero π] in
theorem sexticChar_mk_one :
    complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 1) = 1 := by
  rw [map_one, MulChar.map_one]

include hlam h2 hprim in
/-- **The local sum of the principal row.** -/
theorem hasSum_localTerm_one (ηp X Y V : ℂ) (hV : ‖V‖ < 1) (hY : ‖Y‖ < 1)
    (hR : ‖primeR π ηp X V‖ < 1) :
    HasSum (localTerm π ηp X Y V 1 0) (principalSum (primeQ π) (primeKappa π ηp) ηp X Y V) := by
  have hρ := sexticChar_mk_one π hlam
  have h := hasSum_localTerm π hlam h2 hprim ηp X Y V (one_not_mem_span_prime π) (j := 0)
    (by norm_num) hV (by rwa [hρ, one_mul]) hR
  convert h using 1
  simp [Fin.sum_univ_two, baseSum]
  unfold principalSum primeR
  ring

include hlam h2 hprim in
/-- **The excess mass of the principal local series.** If `‖V‖, ‖Y‖, ‖X‖, ‖R‖` and
`‖Q − 1‖ ‖X‖ ‖Y‖` are at most `δ ≤ 1/4`, the norm series exceeds `1` by at most `8δ`. -/
theorem tsum_norm_localTerm_one_sub_one_le (ηp X Y V : ℂ) {δ : ℝ} (hδ : δ ≤ 1 / 4)
    (hV : ‖V‖ ≤ δ) (hY : ‖Y‖ ≤ δ) (hX : ‖X‖ ≤ δ) (hR : ‖primeR π ηp X V‖ ≤ δ)
    (hQXY : ‖primeQ π - 1‖ * ‖X‖ * ‖Y‖ ≤ δ) (hη : ‖ηp‖ ≤ 1)
    (hq : ‖1 - (primeQ π)⁻¹‖ ≤ 1) :
    ∑' d, ‖localTerm π ηp X Y V 1 0 d‖ - 1 ≤ 8 * δ := by
  have hρ := sexticChar_mk_one π hlam
  have hV1 : ‖V‖ < 1 := by linarith
  have hY1 : ‖Y‖ < 1 := by linarith
  have hR1 : ‖primeR π ηp X V‖ < 1 := by linarith
  rw [(hasSum_norm_localTerm π hlam h2 hprim ηp X Y V (one_not_mem_span_prime π) (j := 0)
    (by norm_num) hV1 (by rwa [hρ, one_mul]) hR1).tsum_eq,
    sum_tsum_norm_base_zero π hlam h2 hprim ηp X Y V (one_not_mem_span_prime π) hV1]
  simp only [hρ, one_mul, inv_one, mul_one, ↓reduceIte]
  set a := ‖V‖
  set b := ‖Y‖
  set r := ‖primeR π ηp X V‖
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hr0 : 0 ≤ r := norm_nonneg _
  have hδ0 : 0 ≤ δ := ha0.trans hV
  -- the four norm masses
  have m1 : ‖primeR π ηp X V * (1 - (primeQ π)⁻¹)‖ ≤ δ := by
    rw [norm_mul]
    calc r * ‖1 - (primeQ π)⁻¹‖ ≤ r * 1 := mul_le_mul_of_nonneg_left hq hr0
      _ ≤ δ := by linarith
  have m2 : ‖Y * primeR π ηp X V‖ ≤ δ / 4 := by
    rw [norm_mul]
    calc b * r ≤ (1 / 4) * δ := mul_le_mul (by linarith) hR hr0 (by norm_num)
      _ = δ / 4 := by ring
  have m3 : ‖ηp * X‖ ≤ δ := by
    rw [norm_mul]
    calc ‖ηp‖ * ‖X‖ ≤ 1 * δ := mul_le_mul hη hX (norm_nonneg _) zero_le_one
      _ = δ := one_mul δ
  have m4 : ‖ηp * (primeQ π - 1) * X * Y‖ ≤ δ := by
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖ηp‖ * ‖primeQ π - 1‖ * ‖X‖ * ‖Y‖ = ‖ηp‖ * (‖primeQ π - 1‖ * ‖X‖ * ‖Y‖) := by ring
      _ ≤ 1 * δ := mul_le_mul hη hQXY (by positivity) zero_le_one
      _ = δ := one_mul δ
  -- the three geometric denominators
  have ia : (1 - a)⁻¹ ≤ 4 / 3 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have ib : (1 - b)⁻¹ ≤ 4 / 3 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have ir : (1 - r)⁻¹ ≤ 4 / 3 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have ia0 : 0 ≤ (1 - a)⁻¹ := inv_nonneg.mpr (by linarith)
  have ib0 : 0 ≤ (1 - b)⁻¹ := inv_nonneg.mpr (by linarith)
  have ir0 : 0 ≤ (1 - r)⁻¹ := inv_nonneg.mpr (by linarith)
  have ha1 : (1 - a)⁻¹ - 1 = a * (1 - a)⁻¹ := by
    have h1a : 1 - a ≠ 0 := (show (0 : ℝ) < 1 - a by linarith).ne'
    field_simp
    ring
  have hinner : ‖primeR π ηp X V * (1 - (primeQ π)⁻¹)‖ * (1 - a)⁻¹ + ‖Y * primeR π ηp X V‖ +
      ‖ηp * X‖ + ‖ηp * (primeQ π - 1) * X * Y‖ * a * (1 - a)⁻¹ ≤ 3 * δ := by
    have t1 : ‖primeR π ηp X V * (1 - (primeQ π)⁻¹)‖ * (1 - a)⁻¹ ≤ δ * (4 / 3) :=
      mul_le_mul m1 ia ia0 hδ0
    have t4 : ‖ηp * (primeQ π - 1) * X * Y‖ * a * (1 - a)⁻¹ ≤ δ * (1 / 4) * (4 / 3) :=
      mul_le_mul (mul_le_mul m4 (by linarith) ha0 hδ0) ia ia0 (by positivity)
    linarith
  have hfirst : (1 - a)⁻¹ - 1 ≤ δ * (4 / 3) := by
    rw [ha1]
    exact mul_le_mul hV ia ia0 hδ0
  have hsecond : b * (1 - b)⁻¹ ≤ δ * (4 / 3) := mul_le_mul hY ib ib0 hδ0
  have hthird : (1 - r)⁻¹ * (‖primeR π ηp X V * (1 - (primeQ π)⁻¹)‖ * (1 - a)⁻¹ +
      ‖Y * primeR π ηp X V‖ + ‖ηp * X‖ + ‖ηp * (primeQ π - 1) * X * Y‖ * a * (1 - a)⁻¹) ≤
        4 / 3 * (3 * δ) :=
    mul_le_mul ir hinner (by positivity) (by norm_num)
  linarith

end Prime

end GaloisForLFunctions.FamilyContinuationTheory
