import Mathlib

/-!
# Irrationality of `e^n` for positive integers `n`

Mathlib proves `π` irrational but not `e^n`; this module builds the Hermite integral proof of
`Irrational (Real.exp n)` for `n ≥ 1`, and the integer corollary `Irrational (Real.exp k)` for
`k ≠ 0`.  It is the transcendence input needed to convert the multiplicative independence of the
primes into Kronecker independence of `{log p}` on the compact circle `ℝ/ℤ`.

The proof: for `A ≥ 1` fix the polynomial `f = Xᵐ (A - X)ᵐ ∈ ℤ[X]` and its alternating antiderivative
`F = Σ_{j≤2m} (-1)ʲ Dʲ f`.  Then `F + F' = f` (the derivative telescopes, `Dⱼ f` dies past degree
`2m`), so `d/dx (eˣ · F(x)/m!) = eˣ · f(x)/m!`.  The endpoint values `F(0)/m!`, `F(A)/m!` are integers
(each `Dʲf` value at `0` and `A` is `j!·(coeff)`, divisible by `m!`).  Hence `q · Iₘ ∈ ℤ` where
`Iₘ = ∫₀^A eˣ f(x)/m! dx` and `e^A = p/q`.  But `0 < Iₘ ≤ e^A A^{2m+1}/m! → 0`, giving `0 < q Iₘ < 1`
for large `m` — an impossible integer.

This module is deliberately self-contained (`import Mathlib`).
-/

open Polynomial

namespace GaloisForLFunctions
namespace RHTower

noncomputable section HermiteAlgebra

variable (A m : ℕ)

/-- The Hermite base polynomial `Xᵐ (A - X)ᵐ ∈ ℤ[X]`, with a root of order `m` at both `0` and `A`. -/
def hermiteP : ℤ[X] := X ^ m * (C (A : ℤ) - X) ^ m

/-- The `j`-th signed derivative term `(-1)ʲ · Dʲ f`. -/
def hermiteTerm (j : ℕ) : ℤ[X] := C ((-1 : ℤ) ^ j) * (derivative^[j] (hermiteP A m))

/-- The Hermite antiderivative polynomial `F = Σ_{j≤2m} (-1)ʲ Dʲ f ∈ ℤ[X]`. -/
def hermiteF : ℤ[X] := ∑ j ∈ Finset.range (2 * m + 1), hermiteTerm A m j

theorem hermiteTerm_zero : hermiteTerm A m 0 = hermiteP A m := by
  simp [hermiteTerm]

/-- `f = Xᵐ(A-X)ᵐ` has degree `≤ 2m`. -/
theorem hermiteP_natDegree_le : (hermiteP A m).natDegree ≤ 2 * m := by
  refine le_trans (natDegree_mul_le) ?_
  have h1 : (X ^ m : ℤ[X]).natDegree ≤ m := natDegree_X_pow_le m
  have h2 : ((C (A : ℤ) - X) ^ m).natDegree ≤ m := by
    refine le_trans (natDegree_pow_le) ?_
    have hle : (C (A : ℤ) - X).natDegree ≤ 1 := by
      refine le_trans (natDegree_sub_le _ _) ?_
      simp [natDegree_X]
    calc m * (C (A : ℤ) - X).natDegree ≤ m * 1 := by gcongr
      _ = m := by ring
  omega

/-- Past degree `2m` the derivative of `f` vanishes. -/
theorem derivative_iterate_hermiteP_high :
    derivative^[2 * m + 1] (hermiteP A m) = 0 :=
  iterate_derivative_eq_zero (lt_of_le_of_lt (hermiteP_natDegree_le A m) (by omega))

theorem hermiteTerm_high : hermiteTerm A m (2 * m + 1) = 0 := by
  simp [hermiteTerm, derivative_iterate_hermiteP_high A m]

/-- The derivative of the `j`-th term is the negative of the `(j+1)`-th: the alternating sign makes
the family telescope under `D`. -/
theorem derivative_hermiteTerm (j : ℕ) :
    derivative (hermiteTerm A m j) = - hermiteTerm A m (j + 1) := by
  unfold hermiteTerm
  rw [derivative_C_mul, ← Function.iterate_succ_apply' derivative j, pow_succ, map_mul, map_neg,
    map_one]
  ring

/-- **The Hermite identity** `F + F' = f`.  The signed derivative sum telescopes: only the `j = 0`
term (`f`) and the vanishing top term survive. -/
theorem hermiteF_add_derivative :
    hermiteF A m + derivative (hermiteF A m) = hermiteP A m := by
  have hderiv : derivative (hermiteF A m)
      = -∑ j ∈ Finset.range (2 * m + 1), hermiteTerm A m (j + 1) := by
    unfold hermiteF
    rw [map_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => derivative_hermiteTerm A m j
  have hshift : ∑ j ∈ Finset.range (2 * m + 1), hermiteTerm A m (j + 1)
      = (hermiteF A m + hermiteTerm A m (2 * m + 1)) - hermiteTerm A m 0 := by
    have h1 := Finset.sum_range_succ' (hermiteTerm A m) (2 * m + 1)
    have h2 := Finset.sum_range_succ (hermiteTerm A m) (2 * m + 1)
    have hkey : (∑ j ∈ Finset.range (2 * m + 1), hermiteTerm A m (j + 1)) + hermiteTerm A m 0
        = hermiteF A m + hermiteTerm A m (2 * m + 1) := by
      rw [← h1, h2]; rfl
    linear_combination hkey
  rw [hderiv, hshift, hermiteTerm_high, hermiteTerm_zero]
  abel

/-! ### Integrality of the endpoint values -/

/-- `f = Xᵐ(A-X)ᵐ` has vanishing coefficients below degree `m`. -/
theorem hermiteP_coeff_eq_zero {j : ℕ} (hj : j < m) : (hermiteP A m).coeff j = 0 := by
  unfold hermiteP
  rw [mul_comm, coeff_mul_X_pow']
  simp [Nat.not_le.mpr hj]

/-- `m! ∣ (Dʲ f).eval 0` for every `j`: below `m` the coefficient vanishes, and at or above `m` the
factor `j!` already contains `m!`. -/
theorem factorial_dvd_iterate_deriv_eval_zero (j : ℕ) :
    (m.factorial : ℤ) ∣ (derivative^[j] (hermiteP A m)).eval 0 := by
  have hval : (derivative^[j] (hermiteP A m)).eval 0
      = (j.factorial : ℤ) * (hermiteP A m).coeff j := by
    rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative]
    simp [Nat.descFactorial_self]
  rw [hval]
  rcases lt_or_ge j m with hlt | hge
  · rw [hermiteP_coeff_eq_zero A m hlt]; simp
  · exact Dvd.dvd.mul_right (by exact_mod_cast Nat.factorial_dvd_factorial hge) _

/-- `f(A - X) = f(X)`, so `f` also has a root of order `m` at `A`; its `A`-taylor coefficients below
`m` vanish. -/
theorem taylor_hermiteP_coeff_eq_zero {j : ℕ} (hj : j < m) :
    (taylor (A : ℤ) (hermiteP A m)).coeff j = 0 := by
  have hinner : (C (A : ℤ) - (X + C (A : ℤ))) = -X := by ring
  have hcomp : taylor (A : ℤ) (hermiteP A m)
      = (X + C (A : ℤ)) ^ m * (-1 : ℤ[X]) ^ m * X ^ m := by
    rw [taylor_apply]
    unfold hermiteP
    rw [mul_comp, pow_comp, pow_comp, X_comp, sub_comp, C_comp, X_comp, hinner,
      neg_eq_neg_one_mul (X : ℤ[X]), mul_pow]
    ring
  rw [hcomp, coeff_mul_X_pow']
  simp [Nat.not_le.mpr hj]

/-- `m! ∣ (Dʲ f).eval A` for every `j`, by the `A`-taylor version of
`factorial_dvd_iterate_deriv_eval_zero`. -/
theorem factorial_dvd_iterate_deriv_eval_A (j : ℕ) :
    (m.factorial : ℤ) ∣ (derivative^[j] (hermiteP A m)).eval (A : ℤ) := by
  have hval : (derivative^[j] (hermiteP A m)).eval (A : ℤ)
      = (j.factorial : ℤ) * (taylor (A : ℤ) (hermiteP A m)).coeff j := by
    have h := congrFun (factorial_smul_hasseDeriv (R := ℤ) j) (hermiteP A m)
    rw [← h, LinearMap.smul_apply, eval_smul, nsmul_eq_mul, ← taylor_coeff]
  rw [hval]
  rcases lt_or_ge j m with hlt | hge
  · rw [taylor_hermiteP_coeff_eq_zero A m hlt]; simp
  · exact Dvd.dvd.mul_right (by exact_mod_cast Nat.factorial_dvd_factorial hge) _

theorem factorial_dvd_hermiteF_eval_zero :
    (m.factorial : ℤ) ∣ (hermiteF A m).eval 0 := by
  unfold hermiteF
  rw [eval_finsetSum]
  refine Finset.dvd_sum fun j _ => ?_
  unfold hermiteTerm
  rw [eval_mul, eval_C]
  exact Dvd.dvd.mul_left (factorial_dvd_iterate_deriv_eval_zero A m j) _

theorem factorial_dvd_hermiteF_eval_A :
    (m.factorial : ℤ) ∣ (hermiteF A m).eval (A : ℤ) := by
  unfold hermiteF
  rw [eval_finsetSum]
  refine Finset.dvd_sum fun j _ => ?_
  unfold hermiteTerm
  rw [eval_mul, eval_C]
  exact Dvd.dvd.mul_left (factorial_dvd_iterate_deriv_eval_A A m j) _

end HermiteAlgebra

/-! ## The Hermite integral and the irrationality argument -/

noncomputable section HermiteAnalysis

open MeasureTheory intervalIntegral

variable (A m : ℕ)

/-- Real image of the base polynomial `f = Xᵐ(A-X)ᵐ`. -/
def hermitePℝ : ℝ[X] := (hermiteP A m).map (Int.castRingHom ℝ)

/-- Real image of the antiderivative polynomial `F`. -/
def hermiteFℝ : ℝ[X] := (hermiteF A m).map (Int.castRingHom ℝ)

theorem hermitePℝ_eval (x : ℝ) : (hermitePℝ A m).eval x = x ^ m * ((A : ℝ) - x) ^ m := by
  unfold hermitePℝ hermiteP
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_C,
    Polynomial.map_X, eval_mul, eval_pow, eval_sub, eval_C, eval_X, Int.coe_castRingHom,
    Int.cast_natCast]

/-- The real Hermite identity `Fℝ + Fℝ' = fℝ`, the image of `hermiteF_add_derivative`. -/
theorem hermiteFℝ_add_derivative :
    hermiteFℝ A m + derivative (hermiteFℝ A m) = hermitePℝ A m := by
  unfold hermiteFℝ hermitePℝ
  rw [derivative_map, ← Polynomial.map_add, hermiteF_add_derivative]

/-- The endpoint values of `Fℝ` are the real images of the integer endpoint values of `F`. -/
theorem hermiteFℝ_eval_intCast (a : ℤ) :
    (hermiteFℝ A m).eval (a : ℝ) = (((hermiteF A m).eval a : ℤ) : ℝ) := by
  unfold hermiteFℝ
  have hpt : (a : ℝ) = (Int.castRingHom ℝ) a := rfl
  rw [hpt, eval_map, eval₂_at_apply]
  rfl

/-- The endpoint value of `Fℝ` at a natural point, as the real image of the integer value. -/
theorem hermiteFℝ_eval_natCast (a : ℕ) :
    (hermiteFℝ A m).eval (a : ℝ) = (((hermiteF A m).eval (a : ℤ) : ℤ) : ℝ) := by
  have hc : ((a : ℤ) : ℝ) = (a : ℝ) := by push_cast; ring
  rw [← hc, hermiteFℝ_eval_intCast]

/-- `d/dx (eˣ · Fℝ(x)) = eˣ · fℝ(x)`: the product rule plus the Hermite identity. -/
theorem hasDerivAt_hermite (x : ℝ) :
    HasDerivAt (fun t => Real.exp t * (hermiteFℝ A m).eval t)
      (Real.exp x * (hermitePℝ A m).eval x) x := by
  have h1 : HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp x
  have h2 : HasDerivAt (fun t => (hermiteFℝ A m).eval t)
      ((derivative (hermiteFℝ A m)).eval x) x := (hermiteFℝ A m).hasDerivAt x
  have hm := h1.mul h2
  apply hm.congr_deriv
  rw [← hermiteFℝ_add_derivative A m, eval_add, mul_add]

/-- The integrand `eˣ · fℝ(x)`. -/
def hermiteIntegrand (x : ℝ) : ℝ := Real.exp x * (hermitePℝ A m).eval x

theorem continuous_hermiteIntegrand : Continuous (hermiteIntegrand A m) :=
  Real.continuous_exp.mul (hermitePℝ A m).continuous

/-- The Hermite integral `∫₀^A eˣ f(x) dx` (without the `m!` normalization). -/
def hermiteBigI : ℝ := ∫ x in (0 : ℝ)..(A : ℝ), hermiteIntegrand A m x

/-- **Fundamental theorem of calculus for the Hermite integral.** -/
theorem hermiteBigI_eq :
    hermiteBigI A m
      = Real.exp A * (hermiteFℝ A m).eval (A : ℝ) - (hermiteFℝ A m).eval 0 := by
  unfold hermiteBigI hermiteIntegrand
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_hermite A m x)
    ((continuous_hermiteIntegrand A m).intervalIntegrable _ _)]
  simp

/-- The integrand is strictly positive on `(0, A)`, so the integral is positive. -/
theorem hermiteBigI_pos (hA : 1 ≤ A) : 0 < hermiteBigI A m := by
  apply intervalIntegral_pos_of_pos_on
    ((continuous_hermiteIntegrand A m).intervalIntegrable _ _)
  · intro x hx
    obtain ⟨hx0, hxA⟩ := hx
    simp only [hermiteIntegrand, hermitePℝ_eval]
    apply mul_pos (Real.exp_pos x)
    exact mul_pos (pow_pos hx0 m) (pow_pos (by linarith) m)
  · exact_mod_cast hA

/-- The integrand is bounded by `e^A · A^{2m}` on `[0, A]`, so the integral is at most
`e^A · A^{2m+1}`. -/
theorem hermiteBigI_le (hA : 1 ≤ A) :
    hermiteBigI A m ≤ Real.exp A * (A : ℝ) ^ (2 * m + 1) := by
  have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hbound : ∀ x ∈ Set.uIoc (0 : ℝ) (A : ℝ),
      ‖hermiteIntegrand A m x‖ ≤ Real.exp A * (A : ℝ) ^ (2 * m) := by
    intro x hx
    rw [Set.uIoc_of_le (by positivity)] at hx
    obtain ⟨hx0, hxA⟩ := hx
    simp only [hermiteIntegrand, hermitePℝ_eval]
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · have hexp : Real.exp x ≤ Real.exp A := Real.exp_le_exp.mpr hxA
      have hp1 : x ^ m ≤ (A : ℝ) ^ m := pow_le_pow_left₀ hx0.le hxA m
      have hp2 : ((A : ℝ) - x) ^ m ≤ (A : ℝ) ^ m :=
        pow_le_pow_left₀ (by linarith) (by linarith) m
      calc Real.exp x * (x ^ m * ((A : ℝ) - x) ^ m)
          ≤ Real.exp A * ((A : ℝ) ^ m * (A : ℝ) ^ m) := by
            apply mul_le_mul hexp _ (by positivity) (Real.exp_pos A).le
            exact mul_le_mul hp1 hp2 (by positivity) (by positivity)
        _ = Real.exp A * (A : ℝ) ^ (2 * m) := by rw [← pow_add]; ring_nf
    · apply mul_nonneg (Real.exp_pos x).le
      exact mul_nonneg (pow_nonneg hx0.le m) (pow_nonneg (by linarith) m)
  have hnorm : ‖hermiteBigI A m‖ ≤ Real.exp A * (A : ℝ) ^ (2 * m) * |(A : ℝ) - 0| :=
    norm_integral_le_of_norm_le_const hbound
  have hpos : (0 : ℝ) ≤ hermiteBigI A m := by
    unfold hermiteBigI
    apply intervalIntegral.integral_nonneg (by positivity)
    intro x hx
    simp only [hermiteIntegrand, hermitePℝ_eval]
    apply mul_nonneg (Real.exp_pos x).le
    exact mul_nonneg (pow_nonneg hx.1 m) (pow_nonneg (by linarith [hx.2]) m)
  rw [Real.norm_eq_abs, abs_of_nonneg hpos] at hnorm
  calc hermiteBigI A m ≤ Real.exp A * (A : ℝ) ^ (2 * m) * |(A : ℝ) - 0| := hnorm
    _ = Real.exp A * (A : ℝ) ^ (2 * m + 1) := by
        rw [sub_zero, abs_of_nonneg (by positivity)]; ring

end HermiteAnalysis

/-- **`e^A` is irrational for every positive integer `A`.**  The Hermite integral
`Iₘ = ∫₀^A eˣ f(x)/m! dx` with `f = Xᵐ(A-X)ᵐ` satisfies `q·Iₘ ∈ ℤ` if `e^A = p/q`, yet
`0 < q Iₘ ≤ q e^A A^{2m+1}/m! → 0`, forcing an impossible integer in `(0,1)` for large `m`. -/
theorem exp_nat_irrational {A : ℕ} (hA : 1 ≤ A) : Irrational (Real.exp A) := by
  intro hmem
  obtain ⟨r, hr⟩ := hmem
  have hden : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hqexp : (r.den : ℝ) * Real.exp A = (r.num : ℝ) := by
    rw [← hr, Rat.cast_def]
    field_simp
  -- the ratio bound sequence tends to 0
  have htend : Filter.Tendsto
      (fun m : ℕ => (r.den : ℝ) * Real.exp A * (A : ℝ) ^ (2 * m + 1) / (m.factorial : ℝ))
      Filter.atTop (nhds 0) := by
    have hs : Filter.Tendsto (fun m : ℕ => ((A : ℝ) ^ 2) ^ m / (m.factorial : ℝ))
        Filter.atTop (nhds 0) := (Real.summable_pow_div_factorial _).tendsto_atTop_zero
    have hcm := hs.const_mul ((r.den : ℝ) * Real.exp A * (A : ℝ))
    rw [mul_zero] at hcm
    refine hcm.congr (fun m => ?_)
    rw [← pow_mul (A : ℝ) 2 m, pow_succ (A : ℝ) (2 * m)]
    ring
  have hev : ∀ᶠ m : ℕ in Filter.atTop,
      (r.den : ℝ) * Real.exp A * (A : ℝ) ^ (2 * m + 1) / (m.factorial : ℝ) < 1 :=
    htend.eventually (eventually_lt_nhds (by norm_num))
  obtain ⟨m, hmlt⟩ := hev.exists
  -- integer endpoint values
  obtain ⟨gA, hgA⟩ := factorial_dvd_hermiteF_eval_A A m
  obtain ⟨g0, hg0⟩ := factorial_dvd_hermiteF_eval_zero A m
  have hfact : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have heA : (hermiteFℝ A m).eval (A : ℝ) = (((hermiteF A m).eval (A : ℤ) : ℤ) : ℝ) :=
    hermiteFℝ_eval_natCast A m A
  have he0 : (hermiteFℝ A m).eval 0 = (((hermiteF A m).eval 0 : ℤ) : ℝ) := by
    simpa using hermiteFℝ_eval_intCast A m 0
  -- q · bigI = m! · Z with Z = p·gA - q·g0
  set Z : ℤ := r.num * gA - r.den * g0 with hZ
  have hqbig : (r.den : ℝ) * hermiteBigI A m = (m.factorial : ℝ) * (Z : ℝ) := by
    rw [hermiteBigI_eq, heA, he0, hgA, hg0, hZ]
    push_cast
    linear_combination ((m.factorial : ℝ) * (gA : ℝ)) * hqexp
  -- positivity forces Z ≥ 1
  have hbigpos : 0 < hermiteBigI A m := hermiteBigI_pos A m hA
  have hmulpos : (0 : ℝ) < (m.factorial : ℝ) * (Z : ℝ) := by rw [← hqbig]; exact mul_pos hden hbigpos
  have hZpos : 0 < Z := by
    by_contra hcon
    rw [not_lt] at hcon
    have hZle : (Z : ℝ) ≤ 0 := by exact_mod_cast hcon
    nlinarith [hmulpos, mul_nonpos_of_nonneg_of_nonpos hfact.le hZle]
  -- combine: m! ≤ q bigI ≤ q e^A A^{2m+1}
  have hlow : (m.factorial : ℝ) ≤ (r.den : ℝ) * hermiteBigI A m := by
    rw [hqbig]
    have h1 : (1 : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hZpos
    nlinarith [hfact, h1]
  have hhigh : (r.den : ℝ) * hermiteBigI A m
      ≤ (r.den : ℝ) * (Real.exp A * (A : ℝ) ^ (2 * m + 1)) :=
    mul_le_mul_of_nonneg_left (hermiteBigI_le A m hA) hden.le
  have hchain : (m.factorial : ℝ) ≤ (r.den : ℝ) * Real.exp A * (A : ℝ) ^ (2 * m + 1) := by
    calc (m.factorial : ℝ) ≤ (r.den : ℝ) * hermiteBigI A m := hlow
      _ ≤ (r.den : ℝ) * (Real.exp A * (A : ℝ) ^ (2 * m + 1)) := hhigh
      _ = (r.den : ℝ) * Real.exp A * (A : ℝ) ^ (2 * m + 1) := by ring
  rw [div_lt_one hfact] at hmlt
  linarith

/-- **`e^k` is irrational for every nonzero integer `k`.**  For `k ≥ 1` this is
`exp_nat_irrational`; for `k ≤ -1`, `e^k = 1/e^{-k}` is irrational because `e^{-k}` is. -/
theorem exp_int_irrational {k : ℤ} (hk : k ≠ 0) : Irrational (Real.exp k) := by
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · have hnat : Irrational (Real.exp ((-k).toNat : ℝ)) := exp_nat_irrational (by omega)
    have hcast : ((-k).toNat : ℝ) = -(k : ℝ) := by
      have hz : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have : ((-k).toNat : ℝ) = ((-k : ℤ) : ℝ) := by exact_mod_cast hz
      rw [this]; push_cast; ring
    rw [hcast] at hnat
    have hflip : Real.exp (k : ℝ) = (Real.exp (-(k : ℝ)))⁻¹ := by rw [Real.exp_neg, inv_inv]
    rw [hflip]
    exact hnat.inv
  · have hnat : Irrational (Real.exp (k.toNat : ℝ)) := exp_nat_irrational (by omega)
    have hcast : (k.toNat : ℝ) = (k : ℝ) := by
      have hz : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (by omega)
      exact_mod_cast hz
    rwa [hcast] at hnat

end RHTower
end GaloisForLFunctions
