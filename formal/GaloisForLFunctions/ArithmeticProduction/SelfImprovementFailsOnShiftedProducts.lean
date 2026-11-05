import GaloisForLFunctions.RHTower.SymmetricShiftFunctionalEquation
import GaloisForLFunctions.RHTower.ChebyshevErrorExponentLaw
import GaloisForLFunctions.RHTower.XiZeroCopyPremiseDischarges
import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.RHTower.XiExplicitFormulaLogDeriv
import GaloisForLFunctions.RHTower.XiEntireReal

/-!
# Self-improvement of a strip fails on shifted products

The statement `Θ < 1 ⇒ Θ = ½` (B57) has the shape of a theorem about Euler products with a functional equation.  The shifted products
`F_a(s) = ξ(s + a) ξ(s − a)` have an Euler product `ζ(s+a)ζ(s−a)` with coefficients `Λ(n)(n^a + n^{−a})` on prime powers, and the same line
reflection as `ξ` (`RHTower.xi_symmetricShiftProduct_lineReflect`).  Their zeros are `ρ ∓ a`, so their width is exactly `Θ + a`
(`shiftedWidth_eq`), and in particular it exceeds `½`.

* **Class-wide self-improvement is false or vacuous** (`selfImprovement_on_shifts_iff`): `Θ_a < 1 ⇒ Θ_a = ½` holds for all
  `0 < a < ½` if and only if `Θ = 1`.  So a self-improvement theorem valid for all Euler products with functional equation would prove the zeros of
  `ζ` approach `Re s = 1`, the opposite of RH.
* **The surviving invariant** (`shiftedWidth_sub_eq`, `coefficient_exponent_lower_bound`): the coefficient-corrected width `Θ_a − a` equals `Θ` for every
  shift, and the coefficient at a prime is at least `p^a log p`.  So a proof of self-improvement must use the Ramanujan bound `Λ_F(n) ≪ Λ(n)`, or the
  degree, which the shifted family violates.
-/

noncomputable section

open Complex Set

namespace GaloisForLFunctions.ArithmeticProduction

open _root_.RHTower

/-- The width of the shifted product `ξ(s + a) ξ(s − a)`. -/
def shiftedWidth (a : ℝ) : ℝ := sSup {x : ℝ | ∃ z : ℂ, symmetricShiftProduct xi a z = 0 ∧ z.re = x}

/-- Zeros of `ξ` have real part at most `Θ`. -/
theorem re_le_zeroReSup_of_xi_eq_zero {ρ : ℂ} (hρ : xi ρ = 0) : ρ.re ≤ zeroReSup := by
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  rw [← hq]
  exact re_le_zeroReSup q

/-- Below `Θ` there is a zero of `ξ` with larger real part. -/
theorem exists_xi_zero_re_gt {b : ℝ} (hb : b < zeroReSup) : ∃ ρ : ℂ, xi ρ = 0 ∧ b < ρ.re := by
  obtain ⟨q, hq⟩ := exists_re_gt_of_lt_zeroReSup_unconditional hb
  exact ⟨(q.1 : ℂ), xi_xiZeroCopy_eq_zero q, hq⟩

/-- There is a zero of `ξ` on the critical line (Hardy), so `Θ ≥ ½`. -/
theorem half_le_zeroReSup : 1 / 2 ≤ zeroReSup := by
  obtain ⟨t, -, ht0⟩ := exists_Xi_zero_gt 1
  have hxi : xi (1 / 2 + (t : ℂ) * I) = 0 := by
    rw [xi_eq_XiC_comp]
    have e : ((1 / 2 + (t : ℂ) * I - 1 / 2) * -I) = (t : ℂ) := by
      ring_nf
      simp [Complex.I_sq]
    rw [e, XiC_ofReal, ht0]
    simp
  have h := re_le_zeroReSup_of_xi_eq_zero hxi
  simpa using h

/-- **The width of a shifted product.** -/
theorem shiftedWidth_eq {a : ℝ} (ha : 0 ≤ a) : shiftedWidth a = zeroReSup + a := by
  unfold shiftedWidth
  refine IsLUB.csSup_eq ⟨?_, ?_⟩ ?_
  · rintro x ⟨z, hz, rfl⟩
    rcases mul_eq_zero.mp hz with h | h
    · have h1 := re_le_zeroReSup_of_xi_eq_zero h
      have h2 : (z + (a : ℂ)).re = z.re + a := by simp
      rw [h2] at h1
      linarith
    · have h1 := re_le_zeroReSup_of_xi_eq_zero h
      have h2 : (z - (a : ℂ)).re = z.re - a := by simp
      rw [h2] at h1
      linarith
  · intro u hu
    by_contra hlt
    have hlt' : u < zeroReSup + a := not_le.mp hlt
    obtain ⟨ρ, hρ, hre⟩ := exists_xi_zero_re_gt (b := u - a) (by linarith)
    have hz : symmetricShiftProduct xi a (ρ + (a : ℂ)) = 0 :=
      (symmetricShiftProduct_zero_translates xi a hρ).1
    have h1 : (ρ + (a : ℂ)).re ≤ u := hu ⟨_, hz, rfl⟩
    have h2 : (ρ + (a : ℂ)).re = ρ.re + a := by simp
    rw [h2] at h1
    linarith
  · obtain ⟨ρ, hρ, -⟩ := exists_xi_zero_re_gt (b := zeroReSup - 1) (by linarith)
    exact ⟨_, _, (symmetricShiftProduct_zero_translates xi a hρ).1, rfl⟩

/-- The coefficient-corrected width of every shift is `Θ`. -/
theorem shiftedWidth_sub_eq {a : ℝ} (ha : 0 ≤ a) : shiftedWidth a - a = zeroReSup := by
  rw [shiftedWidth_eq ha]
  ring

/-- **Self-improvement on the shifted family is the statement `Θ = 1`.** -/
theorem selfImprovement_on_shifts_iff :
    (∀ a : ℝ, 0 < a → a < 1 / 2 → shiftedWidth a < 1 → shiftedWidth a = 1 / 2) ↔ zeroReSup = 1 := by
  have hle := zeroReSup_le_one
  have hge := half_le_zeroReSup
  constructor
  · intro h
    by_contra hne
    have hlt : zeroReSup < 1 := lt_of_le_of_ne hle hne
    set a : ℝ := (1 - zeroReSup) / 2 with ha
    have ha0 : 0 < a := by rw [ha]; linarith
    have ha1 : a < 1 / 2 := by rw [ha]; linarith
    have hw : shiftedWidth a = (1 + zeroReSup) / 2 := by
      rw [shiftedWidth_eq ha0.le, ha]
      ring
    have h1 := h a ha0 ha1 (by rw [hw]; linarith)
    rw [hw] at h1
    linarith
  · intro h a ha0 _ hlt
    rw [shiftedWidth_eq ha0.le, h] at hlt
    linarith

/-- Unconditionally, some shift has a width in `[¾, 1)` unless `Θ = 1`: the Euler-product class contains strips that do not collapse. -/
theorem exists_shift_width_strictly_inside (hΘ : zeroReSup < 1) :
    ∃ a : ℝ, 0 < a ∧ 1 / 2 < shiftedWidth a ∧ shiftedWidth a < 1 := by
  have hge := half_le_zeroReSup
  refine ⟨(1 - zeroReSup) / 2, by linarith, ?_, ?_⟩
  · rw [shiftedWidth_eq (by linarith)]
    linarith
  · rw [shiftedWidth_eq (by linarith)]
    linarith

/-- The prime-power coefficients of the logarithmic derivative of `ζ(s+a)ζ(s−a)`. -/
def shiftedWeight (a : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ a + (n : ℝ) ^ (-a))

/-- **Coefficient exponent.**  At a prime, the coefficient is at least `p^a log p`: the shifted family is not Ramanujan. -/
theorem coefficient_exponent_lower_bound {a : ℝ} {p : ℕ} (hp : p.Prime) :
    (p : ℝ) ^ a * Real.log p ≤ shiftedWeight a p := by
  unfold shiftedWeight
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have h : 0 ≤ (p : ℝ) ^ (-a) := Real.rpow_nonneg (Nat.cast_nonneg p) _
  nlinarith

/-- The shifted product keeps the line reflection of `ξ`, with root number `1`. -/
theorem shiftedProduct_lineReflect (a : ℝ) (s : ℂ) :
    symmetricShiftProduct xi a (lineReflect s) =
      (starRingEnd ℂ) (symmetricShiftProduct xi a s) :=
  xi_symmetricShiftProduct_lineReflect a s

end GaloisForLFunctions.ArithmeticProduction
