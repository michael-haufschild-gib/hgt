import GaloisForLFunctions.ArithmeticEffectivityTheory.TheFourierCoefficientsOfTheTorsionMeasure

/-!
# The logarithmic energy of roots of unity

The roots of unity of order dividing `a` and those of order dividing `b` are two finite cycles on the
characteristic circle. Their **archimedean intersection** — the logarithmic energy
`J(a, b) = Σ_{ζ^a = 1} Σ_{η^b = 1, η ≠ ζ} log |ζ − η|` — has a closed form:

    J(a, b) = gcd(a, b) · log lcm(a, b)               (`logEnergy_eq`).

* **The circle sum at `1`** (`sum_log_norm_one_sub_nthRoots`): `Σ_{θ^b = 1, θ ≠ 1} log |1 − θ| =
  log b`, from `Λ(d) = Σ_{θ prim d} log |1 − θ|` and `Σ_{d ∣ b} Λ(d) = log b`.
* **The potential of `μ_b`** (`sum_log_norm_sub_nthRoots`): at a point `ζ` it is `log |ζ^b − 1|`, and
  `log b` on `μ_b` itself (the derivative of `X^b − 1`).
* **Power maps** (`sum_nthRoots_comp_pow`): `ζ ↦ ζ^b` maps `μ_a` onto `μ_{a/gcd(a,b)}`, each point
  `gcd(a, b)` times.

The integers of the formula are orders of finite groups: `gcd(a, b) = |μ_a ∩ μ_b|` and
`lcm(a, b) = |μ_a μ_b|`. The archimedean energy of two torsion cycles is the size of their
intersection times the log-order of the cycle they generate — the product formula for the
resultant of `X^a − 1` and `X^b − 1`, read on the circle.

(In the sums the coincident pairs `η = ζ` contribute `log 0 = 0`.)
-/

noncomputable section

open Polynomial Finset Complex
open scoped Real

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

/-- The `n`-th roots of unity split by exact order (real-valued version). -/
theorem sum_nthRoots_eq_sum_divisors_real (n : ℕ) (f : ℂ → ℝ) :
    ∑ ζ ∈ nthRootsFinset n (1 : ℂ), f ζ = ∑ d ∈ n.divisors, ∑ ζ ∈ primitiveRoots d ℂ, f ζ := by
  classical
  rw [IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots, sum_biUnion]
  intro a ha b hb hab
  have ha0 : 0 < a := Nat.pos_of_mem_divisors ha
  have hb0 : 0 < b := Nat.pos_of_mem_divisors hb
  exact disjoint_left.mpr fun ζ hza hzb =>
    hab (((mem_primitiveRoots ha0).mp hza).unique ((mem_primitiveRoots hb0).mp hzb))

/-- **The circle sum at `1`**: `Σ_{θ^b = 1} log |1 − θ| = log b`. -/
theorem sum_log_norm_one_sub_nthRoots {b : ℕ} (_hb : 0 < b) :
    ∑ θ ∈ nthRootsFinset b (1 : ℂ), Real.log ‖1 - θ‖ = Real.log b := by
  rw [sum_nthRoots_eq_sum_divisors_real, ← ArithmeticFunction.vonMangoldt_sum]
  refine sum_congr rfl fun d hd => ?_
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hd0.ne') with h | h
  · subst h
    simp [ArithmeticFunction.vonMangoldt_apply_one]
  · exact (vonMangoldt_eq_sum_log_norm_one_sub h).symm

theorem norm_eq_one_of_mem_nthRoots {b : ℕ} (hb : 0 < b) {ζ : ℂ}
    (hζ : ζ ∈ nthRootsFinset b (1 : ℂ)) : ‖ζ‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hb 1).mp hζ) hb.ne'

/-- **The potential of `μ_b`** at a point `ζ`: `log |ζ^b − 1|`, or `log b` on `μ_b`. -/
theorem sum_log_norm_sub_nthRoots {b : ℕ} (hb : 0 < b) (ζ : ℂ) :
    ∑ η ∈ nthRootsFinset b (1 : ℂ), Real.log ‖ζ - η‖ =
      if ζ ^ b = 1 then Real.log b else Real.log ‖ζ ^ b - 1‖ := by
  have hω := Complex.isPrimitiveRoot_exp b hb.ne'
  split_ifs with h
  · have hζ0 : ζ ≠ 0 := by rintro rfl; simp [zero_pow hb.ne'] at h
    have hζn : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h hb.ne'
    rw [← sum_log_norm_one_sub_nthRoots hb]
    refine sum_nbij' (fun η => ζ⁻¹ * η) (fun θ => ζ * θ) ?_ ?_ ?_ ?_ ?_
    · intro η hη
      rw [Polynomial.mem_nthRootsFinset hb] at hη ⊢
      rw [mul_pow, inv_pow, h, hη, inv_one, one_mul]
    · intro θ hθ
      rw [Polynomial.mem_nthRootsFinset hb] at hθ ⊢
      rw [mul_pow, h, hθ, one_mul]
    · intro η _; simp [hζ0]
    · intro θ _; simp [hζ0]
    · intro η _
      rw [show ζ - η = ζ * (1 - ζ⁻¹ * η) by field_simp, norm_mul, hζn, one_mul]
  · have hprod := congrArg (eval ζ) (X_pow_sub_one_eq_prod hb hω)
    simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at hprod
    rw [hprod, norm_prod, Real.log_prod]
    intro η hη
    have hη1 := (Polynomial.mem_nthRootsFinset hb 1).mp hη
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun he => h (he ▸ hη1))

/-- A periodic power sum: if `x^m = 1` then `Σ_{j < k m} F(x^j) = k Σ_{i < m} F(x^i)`. -/
theorem sum_range_mul_pow_periodic {x : ℂ} {m : ℕ} (hx : x ^ m = 1) (F : ℂ → ℝ) (k : ℕ) :
    ∑ j ∈ range (k * m), F (x ^ j) = k * ∑ i ∈ range m, F (x ^ i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, sum_range_add, ih]
    have : ∀ i, x ^ (k * m + i) = x ^ i := fun i => by
      rw [pow_add, pow_mul', hx, one_pow, one_mul]
    simp only [this]
    push_cast; ring

/-- **Power maps on `μ_a`**: `Σ_{ζ^a = 1} G(ζ^b) = gcd(a, b) · Σ_{θ^{a/gcd} = 1} G(θ)`. -/
theorem sum_nthRoots_comp_pow {a : ℕ} (ha : 0 < a) (b : ℕ) (G : ℂ → ℝ) :
    ∑ ζ ∈ nthRootsFinset a (1 : ℂ), G (ζ ^ b) =
      Nat.gcd a b * ∑ θ ∈ nthRootsFinset (a / Nat.gcd a b) (1 : ℂ), G θ := by
  set g := Nat.gcd a b with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left b ha
  have hga : g ∣ a := Nat.gcd_dvd_left a b
  have hgb : g ∣ b := Nat.gcd_dvd_right a b
  set m := a / g with hm
  have hm0 : 0 < m := Nat.div_pos (Nat.le_of_dvd ha hga) hg0
  have hω := Complex.isPrimitiveRoot_exp a ha.ne'
  set ω := Complex.exp (2 * π * I / a)
  -- `ω^b` is a primitive `m`-th root of unity
  have hωg : IsPrimitiveRoot (ω ^ g) m := hω.pow_of_dvd hg0.ne' hga
  have hcop : (b / g).Coprime m := (Nat.coprime_div_gcd_div_gcd hg0).symm
  have hωb : IsPrimitiveRoot (ω ^ b) m := by
    have := hωg.pow_of_coprime (b / g) hcop
    rwa [← pow_mul, Nat.mul_div_cancel' hgb] at this
  rw [nthRootsFinset_eq_image ha hω, sum_image fun i hi j hj hij =>
    hω.pow_inj (mem_range.mp hi) (mem_range.mp hj) hij,
    nthRootsFinset_eq_image hm0 hωb, sum_image fun i hi j hj hij =>
    hωb.pow_inj (mem_range.mp hi) (mem_range.mp hj) hij]
  simp_rw [← pow_mul, mul_comm _ b, pow_mul]
  have hagm : a = g * m := (Nat.mul_div_cancel' hga).symm
  conv_lhs => rw [hagm]
  exact sum_range_mul_pow_periodic hωb.pow_eq_one G g

/-- The logarithmic energy of `μ_a` against `μ_b`. -/
def logEnergy (a b : ℕ) : ℝ :=
  ∑ ζ ∈ nthRootsFinset a (1 : ℂ), ∑ η ∈ nthRootsFinset b (1 : ℂ), Real.log ‖ζ - η‖

/-- **`J(a, b) = gcd(a, b) · log lcm(a, b)`.** -/
theorem logEnergy_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    logEnergy a b = Nat.gcd a b * Real.log (Nat.lcm a b) := by
  set g := Nat.gcd a b
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left b ha
  have hga : g ∣ a := Nat.gcd_dvd_left a b
  have hm0 : 0 < a / g := Nat.div_pos (Nat.le_of_dvd ha hga) hg0
  set H : ℂ → ℝ := fun θ => if θ = 1 then Real.log b else Real.log ‖θ - 1‖
  have hinner : ∀ ζ : ℂ, ∑ η ∈ nthRootsFinset b (1 : ℂ), Real.log ‖ζ - η‖ = H (ζ ^ b) := by
    intro ζ
    rw [sum_log_norm_sub_nthRoots hb]
  rw [logEnergy, sum_congr rfl fun ζ _ => hinner ζ, sum_nthRoots_comp_pow ha b H]
  have hsplit : ∀ θ : ℂ, H θ = Real.log ‖1 - θ‖ + if θ = 1 then Real.log b else 0 := by
    intro θ
    by_cases h : θ = 1
    · simp [H, h]
    · simp [H, h, norm_sub_rev]
  rw [sum_congr rfl fun θ _ => hsplit θ, sum_add_distrib, sum_log_norm_one_sub_nthRoots hm0,
    sum_ite_eq', if_pos ((Polynomial.mem_nthRootsFinset hm0 1).mpr (one_pow _))]
  have hlcm : (Nat.lcm a b : ℝ) = (a / g : ℕ) * b := by
    rw [Nat.lcm, ← Nat.div_mul_right_comm hga]; push_cast; ring
  rw [hlcm, Real.log_mul (by exact_mod_cast hm0.ne') (by exact_mod_cast hb.ne')]

end GaloisForLFunctions.ArithmeticEffectivityTheory
