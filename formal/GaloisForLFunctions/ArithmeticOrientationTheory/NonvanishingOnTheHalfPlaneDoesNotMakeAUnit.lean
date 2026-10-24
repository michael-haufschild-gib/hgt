import GaloisForLFunctions.ArithmeticOrientationTheory.AKernelBoundedBelowOnTheHalfPlaneIsAUnit
import GaloisForLFunctions.ArithmeticOrientationTheory.TheObstructionCountIsTheCodimensionOfTheRepairingIdeal

/-!
# Nonvanishing on the half-plane does not make a unit

The uniform bound in the half-plane Wiener lemma (`isUnit_iff_exists_le_norm_lSeries`) cannot be
weakened to nonvanishing.  The kernel `f = δ₁ − ½√2 δ₂ + ½√3 δ₃` of `𝒲_{1/2}` has Bohr transform
`1 − ½ω(2) + ½ω(3)`:

* `L(f, s) ≠ 0` on `Re s ≥ ½` (`lSeries_threeTermKernel_ne_zero`): a zero forces `2^{½−s} = 1` and
  `3^{½−s} = −1`, hence `3^{2k} = 2^{2l+1}`;
* `f` is not a unit (`not_isUnit_threeTermKernel`): `f̂` vanishes at the Bohr point
  `ω(2) = 1, ω(3) = −1`, which the line `Re s = ½` approaches (Kronecker) but never reaches.
-/

open ArithmeticFunction LSeries Complex

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open WienerAlgebraAt

noncomputable section
set_option autoImplicit false

/-- `δ₁ − ½√2 δ₂ + ½√3 δ₃` in `𝒲_{1/2}`. -/
def threeTermKernel : WienerAlgebraAt (1 / 2) :=
  1 - (1 / 2 : ℂ) • ((2 : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) • pointMass 2) +
    (1 / 2 : ℂ) • ((3 : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) • pointMass 3)

theorem bohrEval_threeTermKernel (ω : BohrPoint) :
    bohrEval (1 / 2) threeTermKernel.toFn ω = 1 - ω.ω 2 / 2 + ω.ω 3 / 2 := by
  rw [← bohrCharacter_apply, threeTermKernel, map_add, map_sub, _root_.map_one, map_smul,
    map_smul, map_smul, map_smul, bohrCharacter_apply, bohrCharacter_apply, toFn_pointMass,
    toFn_pointMass, bohrEval_pointMass two_ne_zero, bohrEval_pointMass three_ne_zero, smul_eq_mul,
    smul_eq_mul, smul_eq_mul, smul_eq_mul]
  have h2 : (2 : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; norm_num
  have h3 : (3 : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; norm_num
  push_cast at h2 h3 ⊢
  field_simp

/-- The Bohr point with `ω(3) = −1` and `ω(p) = 1` at every other prime. -/
def flipThreePoint : BohrPoint :=
  BohrPoint.ofPrimes (fun p => if p = 3 then -1 else 1) fun p _ => by split_ifs <;> simp

/-- **Not a unit**: `f̂` vanishes at `ω(2) = 1, ω(3) = −1`. -/
theorem not_isUnit_threeTermKernel : ¬ IsUnit threeTermKernel := by
  rw [isUnit_iff_forall_bohrEval_ne_zero, not_forall]
  refine ⟨flipThreePoint, ?_⟩
  have h2 : flipThreePoint.ω 2 = 1 :=
    (BohrPoint.ofPrimes_apply_prime _ Nat.prime_two).trans (if_neg (by norm_num))
  have h3 : flipThreePoint.ω 3 = -1 :=
    (BohrPoint.ofPrimes_apply_prime _ Nat.prime_three).trans (if_pos rfl)
  rw [not_not, bohrEval_threeTermKernel, h2, h3]
  norm_num

/-- **No zero on the closed half-plane** `Re s ≥ ½`. -/
theorem lSeries_threeTermKernel_ne_zero {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) :
    LSeries (⇑threeTermKernel.toFn) s ≠ 0 := by
  rw [← bohrEval_halfPlanePoint _ s hs, bohrEval_threeTermKernel]
  set ω := halfPlanePoint (1 / 2) s hs
  intro h0
  -- `ω(2) − ω(3) = 2` with both in the unit disk forces `ω(2) = 1`, `ω(3) = −1`.
  have hab : ω.ω 2 - ω.ω 3 = 2 := by linear_combination -2 * h0
  have ha := ω.norm_le_one 2
  have hb := ω.norm_le_one 3
  have hre : (ω.ω 2).re - (ω.ω 3).re = 2 := by simpa using congrArg Complex.re hab
  have hra := (abs_le.1 ((Complex.abs_re_le_norm (ω.ω 2)).trans ha)).2
  have hrb := (abs_le.1 ((Complex.abs_re_le_norm (ω.ω 3)).trans hb)).1
  have hsq : ∀ z : ℂ, ‖z‖ ≤ 1 → z.re ^ 2 = 1 → z.im = 0 := fun z hz hz1 => by
    have h := Complex.sq_norm z
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg z, sq_nonneg z.im]
  have hra1 : (ω.ω 2).re = 1 := by linarith
  have hrb1 : (ω.ω 3).re = -1 := by linarith
  have hw2 : ω.ω 2 = 1 := Complex.ext (by simpa using hra1) (by
    simpa using hsq _ ha (by rw [hra1]; norm_num))
  have hw3 : ω.ω 3 = -1 := Complex.ext (by simpa using hrb1) (by
    simpa using hsq _ hb (by rw [hrb1]; norm_num))
  -- In exponential form: `2^w = 1`, `3^w = −1` with `w = ½ − s`.
  set w : ℂ := ((1 / 2 : ℝ) : ℂ) - s
  have hlog : ∀ x : ℝ, 0 < x → Complex.log (x : ℂ) = (Real.log x : ℂ) := fun x hx =>
    (ofReal_log hx.le).symm
  have hcpow : ∀ n : ℕ, n ≠ 0 → ω.ω n = exp ((Real.log n : ℂ) * w) := fun n hn => by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    simp only [ω, halfPlanePoint, hn, if_false]
    rw [cpow_def_of_ne_zero hn', ← ofReal_natCast, hlog _ hpos]
  have e2 := hcpow 2 two_ne_zero
  have e3 := hcpow 3 three_ne_zero
  rw [hw2] at e2
  rw [hw3, ← exp_pi_mul_I] at e3
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 e2.symm
  obtain ⟨l, hl⟩ := Complex.exp_eq_exp_iff_exists_int.1 e3.symm
  push_cast at hk hl
  have hπ : (Real.pi : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero) I_ne_zero
  have hreal : ((2 * k * Real.log 3 - (1 + 2 * l) * Real.log 2 : ℝ) : ℂ) * (Real.pi * I) = 0 := by
    push_cast
    linear_combination (Real.log 2 : ℂ) * hl - (Real.log 3 : ℂ) * hk
  have hreal' : 2 * k * Real.log 3 = (1 + 2 * l) * Real.log 2 := by
    have := (mul_eq_zero.1 hreal).resolve_right hπ
    rw [ofReal_eq_zero] at this
    linarith
  have hz : (3 : ℝ) ^ (2 * k) = (2 : ℝ) ^ (1 + 2 * l) := by
    rw [← Real.rpow_intCast, ← Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num),
      Real.rpow_def_of_pos (by norm_num)]
    push_cast
    congr 1
    linarith
  have hk0 : k = 0 := by have := int_eq_zero_of_three_zpow_eq_two_zpow hz; omega
  rw [hk0] at hk
  have hw0 : w = 0 := by
    have hl2 : (Real.log 2 : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.log_pos one_lt_two).ne'
    rw [Int.cast_zero, zero_mul] at hk
    exact (mul_eq_zero.1 hk).resolve_left hl2
  rw [hw0, mul_zero, Complex.exp_zero] at e3
  rw [exp_pi_mul_I] at e3
  norm_num at e3

end

end GaloisForLFunctions.ArithmeticOrientationTheory
