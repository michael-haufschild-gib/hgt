import GaloisForLFunctions.HTGeometry.PolynomialHeatProduct

/-!
# Heated quadratic factors and factorial coefficient bounds

**Heated even polynomials** (`coeff_forwardPolyHeat_expand_two`).  For `p(x) = R(x²)`,

  `[x^{2l}] e^{sD²} p = Σ_k s^k/k! · (2l+2k)!/(2l)! · [y^{l+k}] R`.

**Heated quadratic factors** (`forwardPolyHeat_expand_quadratic`).

  `e^{sD²}(1 + b x² + c x⁴) = (1 + 2sb + 12s²c) + (b + 12sc) x² + c x⁴`.

So `1 + b x² + c x⁴` becomes coefficient-positive under the heat `s` iff `c ≥ 0`,
`b + 12sc ≥ 0` and `1 + 2sb + 12s²c ≥ 0` (`coeffNonneg_forwardPolyHeat_expand_quadratic`).

**Factorial coefficient bounds** (`FactorialCoeffBound`).  `|[y^m] p| ≤ C ρ^m/m!` for all `m`.
The bound is multiplicative: constants multiply and rates add (`FactorialCoeffBound.mul`), by
the binomial identity `Σ_{i+j=m} a^i/i! · b^j/j! = (a+b)^m/m!`.  The heat weights
`s^k/k! · (2l+2k)!/(2l)!` grow like `(4s)^k k!`, and against a factorial bound of rate `ρ` they
are summable once `8sρ < 1` (`heatWeight_mul_pow_div_factorial_le`).
-/

open Polynomial Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `(n + 2k)₍₂ₖ₎ = (n + 2k)!/n!`. -/
theorem descFactorial_two_mul_cast (n k : ℕ) :
    (((n + 2 * k).descFactorial (2 * k) : ℕ) : ℝ) = (n + 2 * k).factorial / n.factorial := by
  have h := Nat.factorial_mul_descFactorial (show 2 * k ≤ n + 2 * k by omega)
  rw [show n + 2 * k - 2 * k = n by omega] at h
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  rw [eq_div_iff hn, mul_comm]
  exact_mod_cast h

/-- **Heated even polynomials.**
`[x^{2l}] e^{sD²} R(x²) = Σ_k s^k/k! · (2l+2k)!/(2l)! · [y^{l+k}] R`. -/
theorem coeff_forwardPolyHeat_expand_two (s : ℝ) (R : ℝ[X]) (l : ℕ) {N : ℕ}
    (hN : R.natDegree < N) :
    (forwardPolyHeat s (expand ℝ 2 R)).coeff (2 * l) = ∑ k ∈ range N,
      s ^ k / k.factorial * ((2 * l + 2 * k).factorial / (2 * l).factorial) * R.coeff (l + k) := by
  rw [forwardPolyHeat_eq_sum (N := N) (by rw [natDegree_expand]; omega), finsetSum_coeff]
  refine sum_congr rfl fun k _ => ?_
  have he : (expand ℝ 2 R).coeff (2 * l + 2 * k) = R.coeff (l + k) := by
    rw [show 2 * l + 2 * k = (l + k) * 2 by ring, coeff_expand_mul (by norm_num)]
  rw [coeff_C_mul, coeff_iterate_derivative, nsmul_eq_mul, descFactorial_two_mul_cast, he]
  ring

theorem forwardPolyHeat_one (s : ℝ) : forwardPolyHeat s 1 = 1 := by
  rw [← C_1, forwardPolyHeat_C]

theorem forwardPolyHeat_X (s : ℝ) : forwardPolyHeat s X = X := by
  have h := forwardPolyHeat_X_mul s 1
  rw [mul_one, forwardPolyHeat_one, derivative_one, mul_zero, add_zero, mul_one] at h
  exact h

theorem forwardPolyHeat_X_pow_two (s : ℝ) : forwardPolyHeat s (X ^ 2) = X ^ 2 + C (2 * s) := by
  have h := forwardPolyHeat_X_mul s X
  rw [forwardPolyHeat_X, derivative_X, mul_one] at h
  rw [pow_two, h]

theorem forwardPolyHeat_X_pow_three (s : ℝ) :
    forwardPolyHeat s (X ^ 3) = X ^ 3 + C (6 * s) * X := by
  have h := forwardPolyHeat_X_mul s (X ^ 2)
  rw [forwardPolyHeat_X_pow_two] at h
  rw [show (X : ℝ[X]) ^ 3 = X * X ^ 2 by ring, h, derivative_add, derivative_C, derivative_X_pow]
  simp only [map_mul, map_ofNat, Nat.cast_ofNat, add_zero]
  ring

theorem forwardPolyHeat_X_pow_four (s : ℝ) :
    forwardPolyHeat s (X ^ 4) = X ^ 4 + C (12 * s) * X ^ 2 + C (12 * s ^ 2) := by
  have h := forwardPolyHeat_X_mul s (X ^ 3)
  rw [forwardPolyHeat_X_pow_three] at h
  rw [show (X : ℝ[X]) ^ 4 = X * X ^ 3 by ring, h, derivative_add, derivative_X_pow,
    derivative_C_mul, derivative_X]
  simp only [map_mul, map_ofNat, map_pow, Nat.cast_ofNat]
  ring

/-- **Heated quadratic factors.**
`e^{sD²}(1 + b x² + c x⁴) = (1 + 2sb + 12s²c) + (b + 12sc) x² + c x⁴`. -/
theorem forwardPolyHeat_expand_quadratic (s b c : ℝ) :
    forwardPolyHeat s (expand ℝ 2 (1 + C b * X + C c * X ^ 2)) =
      C (1 + 2 * s * b + 12 * s ^ 2 * c) + C (b + 12 * s * c) * X ^ 2 + C c * X ^ 4 := by
  have e : expand ℝ 2 (1 + C b * X + C c * X ^ 2) = 1 + C b * X ^ 2 + C c * X ^ 4 := by
    simp only [map_add, map_one, map_mul, map_pow, expand_C, expand_X]
    ring
  rw [e, forwardPolyHeat_add, forwardPolyHeat_add, forwardPolyHeat_one, forwardPolyHeat_C_mul,
    forwardPolyHeat_C_mul, forwardPolyHeat_X_pow_two, forwardPolyHeat_X_pow_four]
  simp only [map_add, map_mul, map_pow, map_ofNat, map_one]
  ring

theorem coeffNonneg_C_add_C_mul_X_sq_add {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) :
    CoeffNonneg (C α + C β * X ^ 2 + C γ * X ^ 4) := by
  intro n
  simp only [coeff_add, coeff_C, coeff_C_mul_X_pow]
  split_ifs <;> linarith

/-- **Positivity of a heated quadratic factor.** -/
theorem coeffNonneg_forwardPolyHeat_expand_quadratic {s b c : ℝ} (hc : 0 ≤ c)
    (h1 : 0 ≤ b + 12 * s * c) (h0 : 0 ≤ 1 + 2 * s * b + 12 * s ^ 2 * c) :
    CoeffNonneg (forwardPolyHeat s (expand ℝ 2 (1 + C b * X + C c * X ^ 2))) := by
  rw [forwardPolyHeat_expand_quadratic]
  exact coeffNonneg_C_add_C_mul_X_sq_add h0 h1 hc

/-! ## Factorial coefficient bounds -/

/-- `|[y^m] p| ≤ C ρ^m/m!` for every `m`. -/
def FactorialCoeffBound (C ρ : ℝ) (p : ℝ[X]) : Prop :=
  ∀ m, |p.coeff m| ≤ C * ρ ^ m / m.factorial

/-- `Σ_{i+j=m} a^i/i! · b^j/j! = (a+b)^m/m!`. -/
theorem sum_antidiagonal_pow_div_factorial (a b : ℝ) (m : ℕ) :
    ∑ x ∈ antidiagonal m, a ^ x.1 / x.1.factorial * (b ^ x.2 / x.2.factorial) =
      (a + b) ^ m / m.factorial := by
  rw [(Commute.all a b).add_pow', Finset.sum_div]
  refine sum_congr rfl fun x hx => ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hx
  have h := Nat.choose_mul_factorial_mul_factorial (show x.1 ≤ x.1 + x.2 by omega)
  rw [show x.1 + x.2 - x.1 = x.2 by omega] at h
  have h' : ((m.choose x.1 : ℕ) : ℝ) * x.1.factorial * x.2.factorial = m.factorial := by
    rw [← hx]; exact_mod_cast h
  have h1 : (x.1.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h2 : (x.2.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h3 : ((m.choose x.1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  rw [nsmul_eq_mul, ← h']
  field_simp

theorem FactorialCoeffBound.mul {C₁ C₂ ρ₁ ρ₂ : ℝ} {f g : ℝ[X]}
    (hf : FactorialCoeffBound C₁ ρ₁ f) (hg : FactorialCoeffBound C₂ ρ₂ g) :
    FactorialCoeffBound (C₁ * C₂) (ρ₁ + ρ₂) (f * g) := by
  intro m
  rw [coeff_mul]
  calc |∑ x ∈ antidiagonal m, f.coeff x.1 * g.coeff x.2|
      ≤ ∑ x ∈ antidiagonal m, |f.coeff x.1 * g.coeff x.2| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ antidiagonal m, C₁ * ρ₁ ^ x.1 / x.1.factorial * (C₂ * ρ₂ ^ x.2 / x.2.factorial) := by
        refine sum_le_sum fun x _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hf _) (hg _) (abs_nonneg _) ((abs_nonneg _).trans (hf _))
    _ = C₁ * C₂ * ∑ x ∈ antidiagonal m, ρ₁ ^ x.1 / x.1.factorial * (ρ₂ ^ x.2 / x.2.factorial) := by
        rw [mul_sum]
        refine sum_congr rfl fun x _ => ?_
        ring
    _ = C₁ * C₂ * (ρ₁ + ρ₂) ^ m / m.factorial := by
        rw [sum_antidiagonal_pow_div_factorial, mul_div_assoc]

theorem factorialCoeffBound_one : FactorialCoeffBound 1 0 (1 : ℝ[X]) := by
  intro m
  rcases m with _ | m
  · simp
  · simp [coeff_one]

theorem FactorialCoeffBound.prod {ι : Type*} (S : Finset ι) {f : ι → ℝ[X]} {C ρ : ι → ℝ}
    (hf : ∀ i ∈ S, FactorialCoeffBound (C i) (ρ i) (f i)) :
    FactorialCoeffBound (∏ i ∈ S, C i) (∑ i ∈ S, ρ i) (∏ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using factorialCoeffBound_one
  | insert a S ha ih =>
    rw [prod_insert ha, prod_insert ha, sum_insert ha]
    exact FactorialCoeffBound.mul (hf a (mem_insert_self a S))
      (ih fun i hi => hf i (mem_insert_of_mem hi))

theorem FactorialCoeffBound.mono {C C' ρ ρ' : ℝ} {p : ℝ[X]} (h : FactorialCoeffBound C ρ p)
    (hC : C ≤ C') (hρ : 0 ≤ ρ) (hρ' : ρ ≤ ρ') : FactorialCoeffBound C' ρ' p := by
  intro m
  refine (h m).trans ?_
  have hC0 : 0 ≤ C := by
    have := (abs_nonneg _).trans (h 0)
    simpa using this
  exact div_le_div_of_nonneg_right (mul_le_mul hC (pow_le_pow_left₀ hρ hρ' m) (by positivity)
    (hC0.trans hC)) (by positivity)

/-- A quadratic `1 + b y + c y²` with `|b| ≤ Kρ` and `|c| ≤ Kρ²/2` has the bound `(K, ρ)`. -/
theorem factorialCoeffBound_quadratic {K ρ b c : ℝ} (hK : 1 ≤ K) (hρ : 0 ≤ ρ)
    (hb : |b| ≤ K * ρ) (hc : |c| ≤ K * ρ ^ 2 / 2) :
    FactorialCoeffBound K ρ (1 + C b * X + C c * X ^ 2) := by
  intro m
  rcases m with _ | _ | _ | m
  · simp
    linarith
  · simpa [coeff_one] using hb
  · simpa [coeff_X, coeff_one] using hc
  · simp only [coeff_add, coeff_one, coeff_C_mul, coeff_X, coeff_X_pow]
    simp only [show m + 1 + 1 + 1 ≠ 0 by omega, show (1 : ℕ) ≠ m + 1 + 1 + 1 by omega,
      show m + 1 + 1 + 1 ≠ 2 by omega, if_false, mul_zero, add_zero, abs_zero]
    positivity

/-! ## Heat weights against factorial bounds -/

/-- `(2m)! ≤ 4^m (m!)²`. -/
theorem factorial_two_mul_le (m : ℕ) :
    ((2 * m).factorial : ℝ) ≤ 4 ^ m * (m.factorial : ℝ) ^ 2 := by
  have h := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
  rw [show 2 * m - m = m by omega] at h
  have hc : ((2 * m).choose m : ℝ) ≤ 4 ^ m := by
    have := Nat.choose_le_two_pow (2 * m) m
    rw [pow_mul] at this
    exact_mod_cast this
  rw [← h]
  push_cast
  nlinarith [sq_nonneg (m.factorial : ℝ), (Nat.cast_nonneg _ : (0 : ℝ) ≤ (2 * m).choose m)]

/-- `(l + k)! ≤ 2^{l+k} l! k!`. -/
theorem factorial_add_le_two_pow_mul (l k : ℕ) :
    ((l + k).factorial : ℝ) ≤ 2 ^ (l + k) * l.factorial * k.factorial := by
  have h := Nat.add_choose_mul_factorial_mul_factorial l k
  have hc : ((l + k).choose k : ℝ) ≤ 2 ^ (l + k) := by exact_mod_cast Nat.choose_le_two_pow _ _
  rw [← h]
  push_cast
  have : (0 : ℝ) ≤ l.factorial * k.factorial := by positivity
  nlinarith

/-- **Heat weights against a factorial bound.**
`s^k/k! · (2l+2k)!/(2l)! · ρ^{l+k}/(l+k)! ≤ l! (8ρ)^l/(2l)! · (8sρ)^k`. -/
theorem heatWeight_mul_pow_div_factorial_le {s ρ : ℝ} (hs : 0 ≤ s) (hρ : 0 ≤ ρ) (l k : ℕ) :
    s ^ k / k.factorial * ((2 * l + 2 * k).factorial / (2 * l).factorial) *
        (ρ ^ (l + k) / (l + k).factorial) ≤
      l.factorial * (8 * ρ) ^ l / (2 * l).factorial * (8 * s * ρ) ^ k := by
  have h1 := factorial_two_mul_le (l + k)
  have h2 := factorial_add_le_two_pow_mul l k
  rw [show 2 * (l + k) = 2 * l + 2 * k by ring] at h1
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hl2 : (0 : ℝ) < (2 * l).factorial := by exact_mod_cast Nat.factorial_pos _
  have hm : (0 : ℝ) < (l + k).factorial := by exact_mod_cast Nat.factorial_pos _
  have hsk : 0 ≤ s ^ k * ρ ^ (l + k) := by positivity
  have key : s ^ k * ρ ^ (l + k) * (2 * l + 2 * k).factorial ≤
      s ^ k * ρ ^ (l + k) * (4 ^ (l + k) * (2 ^ (l + k) * l.factorial * k.factorial) *
        (l + k).factorial) := by
    refine mul_le_mul_of_nonneg_left (h1.trans ?_) hsk
    rw [sq, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) hm.le
  have e1 : s ^ k / k.factorial * ((2 * l + 2 * k).factorial / (2 * l).factorial) *
      (ρ ^ (l + k) / (l + k).factorial) = s ^ k * ρ ^ (l + k) * (2 * l + 2 * k).factorial /
        (k.factorial * (2 * l).factorial * (l + k).factorial) := by
    field_simp
  have e2 : l.factorial * (8 * ρ) ^ l / (2 * l).factorial * (8 * s * ρ) ^ k =
      s ^ k * ρ ^ (l + k) * (4 ^ (l + k) * (2 ^ (l + k) * l.factorial * k.factorial) *
        (l + k).factorial) / (k.factorial * (2 * l).factorial * (l + k).factorial) := by
    have e8l : (8 * ρ) ^ l = 4 ^ l * 2 ^ l * ρ ^ l := by
      rw [show (8 : ℝ) * ρ = 4 * 2 * ρ by norm_num, mul_pow, mul_pow]
    have e8k : (8 * s * ρ) ^ k = 4 ^ k * 2 ^ k * s ^ k * ρ ^ k := by
      rw [show (8 : ℝ) * s * ρ = 4 * 2 * s * ρ by norm_num, mul_pow, mul_pow, mul_pow]
    rw [e8l, e8k]
    field_simp
    ring
  rw [e1, e2]
  exact div_le_div_of_nonneg_right key (by positivity)

/-! ## Heat and Taylor shifts -/

private theorem derivative_taylor_eq (r : ℝ) (p : ℝ[X]) :
    derivative (taylor r p) = taylor r (derivative p) := by
  rw [taylor_apply, taylor_apply, derivative_comp, derivative_add, derivative_X, derivative_C,
    add_zero, one_mul]

theorem iterate_derivative_taylor (r : ℝ) (p : ℝ[X]) (k : ℕ) :
    derivative^[k] (taylor r p) = taylor r (derivative^[k] p) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, derivative_taylor_eq,
      Function.iterate_succ_apply']

/-- The heat commutes with Taylor shifts: `e^{sD²}(p(· + r)) = (e^{sD²}p)(· + r)`. -/
theorem forwardPolyHeat_taylor (s r : ℝ) (p : ℝ[X]) :
    forwardPolyHeat s (taylor r p) = taylor r (forwardPolyHeat s p) := by
  unfold forwardPolyHeat
  rw [natDegree_taylor, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [taylor_mul, taylor_C, iterate_derivative_taylor]

/-- `[x^n] p(x + r) = Σ_j C(n+j, n) [x^{n+j}] p · r^j`. -/
theorem coeff_taylor_eq_sum (r : ℝ) (p : ℝ[X]) (n : ℕ) {N : ℕ} (hN : p.natDegree < N) :
    (taylor r p).coeff n = ∑ j ∈ range N, ((n + j).choose n : ℝ) * p.coeff (n + j) * r ^ j := by
  rw [taylor_coeff, eval_eq_sum_range' (n := N) (by rw [natDegree_hasseDeriv]; omega)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hasseDeriv_coeff, add_comm j n]

theorem coeff_forwardPolyHeat_expand_two_odd (s : ℝ) (R : ℝ[X]) (l : ℕ) :
    (forwardPolyHeat s (expand ℝ 2 R)).coeff (2 * l + 1) = 0 := by
  unfold forwardPolyHeat
  rw [finsetSum_coeff]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [coeff_C_mul, coeff_iterate_derivative, coeff_expand (by norm_num)]
  have : ¬ (2 ∣ 2 * l + 1 + 2 * k) := by omega
  rw [if_neg this, smul_zero, mul_zero]

/-- The Taylor shift of an even quartic. -/
theorem taylor_C_add_C_mul_X_sq_add (r α β γ : ℝ) :
    taylor r (C α + C β * X ^ 2 + C γ * X ^ 4) =
      C (α + β * r ^ 2 + γ * r ^ 4) + C (2 * β * r + 4 * γ * r ^ 3) * X +
        C (β + 6 * γ * r ^ 2) * X ^ 2 + C (4 * γ * r) * X ^ 3 + C γ * X ^ 4 := by
  rw [taylor_apply]
  simp only [add_comp, mul_comp, pow_comp, C_comp, X_comp]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  ring

theorem coeffNonneg_quartic {a₀ a₁ a₂ a₃ a₄ : ℝ} (h₀ : 0 ≤ a₀) (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂)
    (h₃ : 0 ≤ a₃) (h₄ : 0 ≤ a₄) :
    CoeffNonneg (C a₀ + C a₁ * X + C a₂ * X ^ 2 + C a₃ * X ^ 3 + C a₄ * X ^ 4) := by
  intro n
  simp only [coeff_add, coeff_C, coeff_C_mul_X_pow, coeff_C_mul_X]
  split_ifs <;> linarith

/-- **Positivity of a shifted heated quadratic factor.**  For `r ≥ 0`, the heated factor
`e^{sD²}(1 + b x² + c x⁴)` has nonnegative Taylor coefficients at `r` when `c ≥ 0`,
`b + 12sc + 2cr² ≥ 0` and its value at `r` is nonnegative. -/
theorem coeffNonneg_taylor_forwardPolyHeat_expand_quadratic {s b c r : ℝ} (hr : 0 ≤ r)
    (hc : 0 ≤ c) (h1 : 0 ≤ b + 12 * s * c + 2 * c * r ^ 2)
    (h0 : 0 ≤ (1 + 2 * s * b + 12 * s ^ 2 * c) + (b + 12 * s * c) * r ^ 2 + c * r ^ 4) :
    CoeffNonneg (taylor r (forwardPolyHeat s (expand ℝ 2 (1 + C b * X + C c * X ^ 2)))) := by
  rw [forwardPolyHeat_expand_quadratic, taylor_C_add_C_mul_X_sq_add]
  refine coeffNonneg_quartic h0 ?_ ?_ (by positivity) hc
  · have : 2 * (b + 12 * s * c) * r + 4 * c * r ^ 3 = 2 * r * (b + 12 * s * c + 2 * c * r ^ 2) := by
      ring
    rw [this]; positivity
  · nlinarith [sq_nonneg r]

/-- **Closure under products, at a shifted centre.** -/
theorem coeffNonneg_taylor_forwardPolyHeat_prod {s : ℝ} (hs : 0 ≤ s) (r : ℝ) {ι : Type*}
    (S : Finset ι) {f : ι → ℝ[X]} (hf : ∀ i ∈ S, CoeffNonneg (taylor r (forwardPolyHeat s (f i)))) :
    CoeffNonneg (taylor r (forwardPolyHeat s (∏ i ∈ S, f i))) := by
  rw [← forwardPolyHeat_taylor, show taylor r (∏ i ∈ S, f i) = taylorAlgHom r (∏ i ∈ S, f i) from
    rfl, map_prod]
  exact coeffNonneg_forwardPolyHeat_prod hs S fun i hi => by
    rw [show taylorAlgHom r (f i) = taylor r (f i) from rfl, forwardPolyHeat_taylor]; exact hf i hi

theorem coeffNonneg_taylor_forwardPolyHeat_mul {s : ℝ} (hs : 0 ≤ s) (r : ℝ) {p q : ℝ[X]}
    (hp : CoeffNonneg (taylor r (forwardPolyHeat s p)))
    (hq : CoeffNonneg (taylor r (forwardPolyHeat s q))) :
    CoeffNonneg (taylor r (forwardPolyHeat s (p * q))) := by
  rw [← forwardPolyHeat_taylor, taylor_mul]
  rw [← forwardPolyHeat_taylor] at hp hq
  exact coeffNonneg_forwardPolyHeat_mul hs hp hq

/-- **Heated coefficients under a factorial bound.**  If `|[y^m] R| ≤ C ρ^m/m!` and `8sρ ≤ 1/2`,
then `|[x^{2l}] e^{sD²} R(x²)| ≤ 2C · l! (8ρ)^l/(2l)!`. -/
theorem abs_coeff_forwardPolyHeat_expand_two_le {s C ρ : ℝ} (hs : 0 ≤ s) (hρ : 0 < ρ)
    (h8 : 8 * s * ρ ≤ 1 / 2) {R : ℝ[X]} (hR : FactorialCoeffBound C ρ R) (l : ℕ) :
    |(forwardPolyHeat s (expand ℝ 2 R)).coeff (2 * l)| ≤
      2 * C * (l.factorial * (8 * ρ) ^ l / (2 * l).factorial) := by
  have hC0 : 0 ≤ C := by simpa using (abs_nonneg _).trans (hR 0)
  set G : ℝ := l.factorial * (8 * ρ) ^ l / (2 * l).factorial with hG
  have hG0 : 0 ≤ G := by positivity
  rw [coeff_forwardPolyHeat_expand_two s R l (N := R.natDegree + 1) (by omega)]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ range (R.natDegree + 1),
        |s ^ k / k.factorial * ((2 * l + 2 * k).factorial / (2 * l).factorial) * R.coeff (l + k)|
      ≤ ∑ k ∈ range (R.natDegree + 1), C * G * (1 / 2) ^ k := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hw : 0 ≤ s ^ k / k.factorial * ((2 * l + 2 * k).factorial / (2 * l).factorial) := by
          positivity
        rw [abs_mul, abs_of_nonneg hw]
        calc s ^ k / k.factorial * ((2 * l + 2 * k).factorial / (2 * l).factorial) *
              |R.coeff (l + k)|
            ≤ s ^ k / k.factorial * ((2 * l + 2 * k).factorial / (2 * l).factorial) *
                (C * ρ ^ (l + k) / (l + k).factorial) := mul_le_mul_of_nonneg_left (hR _) hw
          _ = C * (s ^ k / k.factorial * ((2 * l + 2 * k).factorial / (2 * l).factorial) *
                (ρ ^ (l + k) / (l + k).factorial)) := by ring
          _ ≤ C * (G * (8 * s * ρ) ^ k) :=
              mul_le_mul_of_nonneg_left (heatWeight_mul_pow_div_factorial_le hs hρ.le l k) hC0
          _ ≤ C * G * (1 / 2) ^ k := by
              rw [← mul_assoc]
              exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h8 k)
                (mul_nonneg hC0 hG0)
    _ = C * G * ∑ k ∈ range (R.natDegree + 1), (1 / 2 : ℝ) ^ k := by rw [Finset.mul_sum]
    _ ≤ C * G * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (mul_nonneg hC0 hG0)
    _ = 2 * C * G := by ring

end

end GaloisForLFunctions.HTGeometry
