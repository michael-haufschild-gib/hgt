import GaloisForLFunctions.RHTower.CCMCyclotomicAlgebraicIntegrality
import GaloisForLFunctions.QuantumAlg.Primitives.QNN.Designs.QubitTwoDesign
import Mathlib.Data.Rat.Lemmas

/-!
# The trace--norm entrance to the CCM quadratic intersection

The cyclotomic coefficient theorem places the literal CCM Lambert coefficients
in `ℤ^cyc[1/2]`.  The next arithmetic step of CCM Theorem 5.6 concerns their
intersection with `ℚ(√2)`.  This module formalizes the part of the standard
quadratic-field proof that is independent of the remaining rational-denominator
parity argument:

* integrality of a rational scalar after a faithful characteristic-zero
  extension reflects back to `ℚ` and hence to `ℤ`;
* `ℚ(√2)` is a field, using the irrationality of `√2`;
* quadratic conjugation preserves integrality, so an integral element has
  integral rational trace and norm.

The exact final residue is intentionally not asserted here: from integral
trace and norm one still has to prove the classical parity classification
`O_{ℚ(√2)} = ℤ[√2]`, then localize at two.  No intersection conclusion is
smuggled in as an assumption.
-/

namespace RHTower

noncomputable section

open QuantumAlg.QubitTwoDesign

/-- A rational scalar that is integral after a faithful characteristic-zero
extension was already integral over `ℤ`, hence is an integer. -/
theorem ccm_rat_exists_int_of_isIntegral_image
    {K : Type*} [Field K] [CharZero K] [Algebra ℚ K] [IsScalarTower ℤ ℚ K]
    {q : ℚ} (hq : IsIntegral ℤ (algebraMap ℚ K q)) :
    ∃ z : ℤ, (z : ℚ) = q := by
  have hq' : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff (R := ℤ) (algebraMap ℚ K).injective).mp hq
  exact IsIntegrallyClosedIn.isIntegral_iff.mp hq'

private theorem ccm_sqrtTwoRat_no_root (r : ℚ) : r ^ 2 ≠ (2 : ℚ) + 0 * r := by
  intro h
  apply (irrational_sqrt_ratCast_iff_of_nonneg (q := (2 : ℚ)) (by norm_num)).mp
    irrational_sqrt_two
  refine ⟨r, ?_⟩
  simpa [pow_two] using h.symm

private local instance ccm_sqrtTwoRat_not_square : Fact
    (∀ r : ℚ, r ^ 2 ≠ (2 : ℚ) + 0 * r) := ⟨ccm_sqrtTwoRat_no_root⟩

/-- The nontrivial quadratic automorphism of the literal carrier
`ℚ(√2) = QuadraticAlgebra ℚ 2 0`, regarded over the integer base. -/
noncomputable def ccmSqrtTwoRatConj : SqrtTwoRat →ₐ[ℤ] SqrtTwoRat where
  toRingHom := starRingEnd SqrtTwoRat
  commutes' z := by
    apply QuadraticAlgebra.ext <;> simp

/-- The trace of a literal `ℚ(√2)` element is its rational scalar
`2 * re`. -/
theorem ccm_sqrtTwoRat_trace_eq (x : SqrtTwoRat) :
    x + star x = algebraMap ℚ SqrtTwoRat ((2 : ℚ) * x.re) := by
  rcases x with ⟨a, b⟩
  change ({ re := a, im := b } : SqrtTwoRat) + star { re := a, im := b } =
    { re := (2 : ℚ) * a, im := 0 }
  apply QuadraticAlgebra.ext
  · simp
    ring
  · simp

/-- The norm of a literal `ℚ(√2)` element is its rational scalar
`re^2 - 2 * im^2`. -/
theorem ccm_sqrtTwoRat_norm_eq (x : SqrtTwoRat) :
    x * star x = algebraMap ℚ SqrtTwoRat
      (x.re ^ 2 - (2 : ℚ) * x.im ^ 2) := by
  rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  simp [QuadraticAlgebra.norm_def, pow_two]
  ring

/-- An element integral over `ℤ` in the literal CCM quadratic carrier has
integral rational trace. -/
theorem ccm_sqrtTwoRat_trace_exists_int {x : SqrtTwoRat} (hx : IsIntegral ℤ x) :
    ∃ z : ℤ, (z : ℚ) = (2 : ℚ) * x.re := by
  apply ccm_rat_exists_int_of_isIntegral_image (K := SqrtTwoRat)
  rw [← ccm_sqrtTwoRat_trace_eq]
  exact hx.add (hx.map ccmSqrtTwoRatConj)

/-- An element integral over `ℤ` in the literal CCM quadratic carrier has
integral rational norm. -/
theorem ccm_sqrtTwoRat_norm_exists_int {x : SqrtTwoRat} (hx : IsIntegral ℤ x) :
    ∃ z : ℤ, (z : ℚ) = x.re ^ 2 - (2 : ℚ) * x.im ^ 2 := by
  apply ccm_rat_exists_int_of_isIntegral_image (K := SqrtTwoRat)
  rw [← ccm_sqrtTwoRat_norm_eq]
  exact hx.mul (hx.map ccmSqrtTwoRatConj)

private theorem ccm_rat_exists_int_of_sq_eq_int_div_two {b : ℚ} {r : ℤ}
    (h : b * b = (r : ℚ) / (2 : ℚ)) : ∃ z : ℤ, (z : ℚ) = b := by
  have hden : b.den * b.den = ((r : ℚ) / (2 : ℚ)).den := by
    rw [← h, Rat.mul_self_den]
  have hden_dvd : ((r : ℚ) / (2 : ℚ)).den ∣ 2 := by
    have h' := Rat.den_dvd r 2
    exact_mod_cast h'
  have hsq_dvd : b.den * b.den ∣ 2 := by
    rw [hden]
    exact hden_dvd
  have hbden_dvd_sq : b.den ∣ b.den * b.den := dvd_mul_right b.den b.den
  have hbden_dvd_two : b.den ∣ 2 := hbden_dvd_sq.trans hsq_dvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hbden_dvd_two with hden1 | hden2
  · exact ⟨b.num, Rat.coe_int_num_of_den_eq_one hden1⟩
  · norm_num [hden2] at hsq_dvd

private theorem ccm_no_rat_sq_eq_int_div_eight_of_odd {b : ℚ} {r : ℤ}
    (hr : Odd r) (h : b * b = (r : ℚ) / (8 : ℚ)) : False := by
  have hden : b.den * b.den = ((r : ℚ) / (8 : ℚ)).den := by
    rw [← h, Rat.mul_self_den]
  have hcop_two : r.natAbs.Coprime 2 := hr.natAbs.coprime_two_right
  have hcop_eight : r.natAbs.Coprime 8 := by
    simpa using hcop_two.pow_right 3
  have hden_eight : ((r : ℚ) / (8 : ℚ)).den = 8 := by
    have h' := Rat.den_div_eq_of_coprime (a := r) (b := 8) (by norm_num) hcop_eight
    exact_mod_cast h'
  have hsq : b.den * b.den = 8 := hden.trans hden_eight
  have hbden_dvd : b.den ∣ 8 := by
    rw [← hsq]
    exact dvd_mul_right _ _
  have hle : b.den ≤ 8 := Nat.le_of_dvd (by norm_num) hbden_dvd
  interval_cases hb : b.den <;> norm_num [hb] at hsq

private theorem ccm_rat_coefficients_integral_of_trace_norm {a b : ℚ}
    (htrace : ∃ m : ℤ, (m : ℚ) = (2 : ℚ) * a)
    (hnorm : ∃ q : ℤ, (q : ℚ) = a ^ 2 - (2 : ℚ) * b ^ 2) :
    ∃ u v : ℤ, (u : ℚ) = a ∧ (v : ℚ) = b := by
  rcases htrace with ⟨m, hm⟩
  rcases hnorm with ⟨q, hq⟩
  rcases Int.even_or_odd m with heven | hodd
  · rcases heven with ⟨n, hn⟩
    have ha : a = (n : ℚ) := by
      have hn' : (m : ℚ) = (n : ℚ) + n := by exact_mod_cast hn
      linarith [hm, hn']
    have hb_sq : b * b = ((n ^ 2 - q : ℤ) : ℚ) / (2 : ℚ) := by
      calc
        b * b = ((n : ℚ) ^ 2 - (q : ℚ)) / (2 : ℚ) := by
          rw [ha] at hq
          linarith [hq]
        _ = ((n ^ 2 - q : ℤ) : ℚ) / (2 : ℚ) := by
          push_cast
          ring
    rcases ccm_rat_exists_int_of_sq_eq_int_div_two hb_sq with ⟨v, hv⟩
    exact ⟨n, v, ha.symm, hv⟩
  · let r : ℤ := m ^ 2 - 4 * q
    have hm_sq : (m : ℚ) ^ 2 = ((2 : ℚ) * a) ^ 2 :=
      congrArg (fun x : ℚ => x ^ 2) hm
    have hrel : (m : ℚ) ^ 2 - (4 : ℚ) * q = (8 : ℚ) * (b * b) := by
      nlinarith [hm_sq, hq]
    have hb_sq : b * b = (r : ℚ) / (8 : ℚ) := by
      dsimp [r]
      push_cast
      field_simp
      linarith [hrel]
    have hr : Odd r := by
      dsimp [r]
      exact hodd.pow.sub_even ⟨2 * q, by ring⟩
    exact (ccm_no_rat_sq_eq_int_div_eight_of_odd hr hb_sq).elim

/-- The trace--norm parity classification in the literal quadratic carrier:
every element integral over `ℤ` in `ℚ(√2)` has integer coordinates. -/
theorem ccm_sqrtTwoRat_integral_has_integer_coefficients {x : SqrtTwoRat}
    (hx : IsIntegral ℤ x) :
    ∃ a b : ℤ, (a : ℚ) = x.re ∧ (b : ℚ) = x.im := by
  exact ccm_rat_coefficients_integral_of_trace_norm
    (ccm_sqrtTwoRat_trace_exists_int hx) (ccm_sqrtTwoRat_norm_exists_int hx)

private def ccmSqrtTwoRatGenerator : SqrtTwoRat := ⟨0, 1⟩

private theorem ccmSqrtTwoRatGenerator_sq : ccmSqrtTwoRatGenerator ^ 2 = (2 : SqrtTwoRat) := by
  change ({ re := (0 : ℚ), im := 1 } : SqrtTwoRat) ^ 2 = { re := (2 : ℚ), im := 0 }
  apply QuadraticAlgebra.ext <;> norm_num [ccmSqrtTwoRatGenerator, pow_two,
    QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]

private theorem ccmSqrtTwoRatGenerator_integral : IsIntegral ℤ ccmSqrtTwoRatGenerator := by
  refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
  rw [ccmSqrtTwoRatGenerator_sq]
  exact isIntegral_algebraMap

/-- Conversely, integer coordinates in the literal `1, √2` basis are integral over `ℤ`. -/
theorem ccm_sqrtTwoRat_integral_of_integer_coefficients {x : SqrtTwoRat}
    {a b : ℤ} (ha : (a : ℚ) = x.re) (hb : (b : ℚ) = x.im) : IsIntegral ℤ x := by
  have hrepr : x = algebraMap ℤ SqrtTwoRat a +
      algebraMap ℤ SqrtTwoRat b * ccmSqrtTwoRatGenerator := by
    apply QuadraticAlgebra.ext <;> simp [ccmSqrtTwoRatGenerator, ha, hb]
  rw [hrepr]
  exact isIntegral_algebraMap.add
    (isIntegral_algebraMap.mul ccmSqrtTwoRatGenerator_integral)

/-- Exact integral-closure classification for the literal quadratic carrier. -/
theorem ccm_sqrtTwoRat_isIntegral_iff_integer_coefficients (x : SqrtTwoRat) :
    IsIntegral ℤ x ↔ ∃ a b : ℤ, (a : ℚ) = x.re ∧ (b : ℚ) = x.im := by
  constructor
  · exact ccm_sqrtTwoRat_integral_has_integer_coefficients
  · rintro ⟨a, b, ha, hb⟩
    exact ccm_sqrtTwoRat_integral_of_integer_coefficients ha hb

end
end RHTower
