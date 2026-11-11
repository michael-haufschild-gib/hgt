import GaloisForLFunctions.FamilyContinuationTheory.ThePoissonCoefficientOfAPrimePowerIsExplicit

/-!
# The local factor of the Poisson series is explicit

At a primary prime `π ∤ 6` with `N(π) = Q`, `|π| = N`, `α = π/N`, sextic residue character `χ`,
`ε = χ(−1)`, `c₄ = χ(4)`, Gauss sums `G_r` and quadratic phase `Γ = Γ(π)`, the Gauss sums obey

* `G₁ G₅ = ε Q`, `G₂ G₄ = Q`, `G₃ = N Γ`, `Γ² = ε`, `c₄³ = 1`, `c₄ G₁ G₂ = −π G₃`.

The local term of the Poisson series of the cubic-theta probe (`localTerm`) at the exponents
`(e, l, k, m)` (squarefree part, cube part, row twist, sixth-power part of the frequency
`H = u π^{j+6m}`, `π ∤ u`, `ρ = χ(u)`) is
`(ᾱ η_π)^t K(π^k, π^e, π^l; H) (X/N)^e (X³/Q)^l (Y/Q)^k V^m`, `t = e + 3l`,
with `X = Q^{−x}`, `Y = Q^{−w}`, `V = Q^{−6z}`. On each family of exponents it is geometric in
`R = (ᾱη_π)⁶ Q⁴ X⁶ V` (`localTerm_*`), and the local series sums to the closed form of the scalar
Euler identity.
-/

noncomputable section

open scoped BigOperators Classical ComplexConjugate

namespace GaloisForLFunctions.FamilyContinuationTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

/-- `G(φ) G(φ⁻¹) = φ(−1) #F` for a nontrivial character and a primitive additive character. -/
theorem gaussSum_mul_gaussSum_inv_char {F : Type*} [Field F] [Fintype F] {φ : MulChar F ℂ}
    (hφ : φ ≠ 1) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    gaussSum φ ψ * gaussSum φ⁻¹ ψ = φ (-1) * Fintype.card F := by
  rw [← mul_gaussSum_inv_eq_gaussSum φ⁻¹, mul_left_comm, gaussSum_mul_gaussSum_eq_card hφ hψ,
    MulChar.inv_apply', inv_neg_one]

section Prime

variable (π : O) [NeZero π] [hP : (Ideal.span {π}).IsMaximal] (hlam : lambda ∉ Ideal.span {π})
  (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1)

/-! ### The prime constants -/

omit [NeZero π] in
/-- `χ^r = χ^{r mod 6}`. -/
theorem complexSexticChar_pow_mod (r : ℕ) :
    complexSexticChar (Ideal.span {π}) hlam ^ r =
      complexSexticChar (Ideal.span {π}) hlam ^ (r % 6) := by
  conv_lhs => rw [← Nat.mod_add_div r 6, pow_add, pow_mul,
    (complexSexticChar_powers (Ideal.span {π}) hlam).2.2, one_pow, mul_one]

omit hP in
/-- `#(O/(π)) = Q`. -/
theorem card_quot_eq_absNorm :
    (Fintype.card (O ⧸ Ideal.span {π}) : ℂ) = (Ideal.absNorm (Ideal.span {π}) : ℂ) :=
  card_quot_span π

include hlam hprim in
/-- `|π|² = Q`. -/
theorem norm_sq_eq_absNorm :
    (‖ringComplex π‖ : ℂ) ^ 2 = (Ideal.absNorm (Ideal.span {π}) : ℂ) := by
  rw [norm_sq_ringComplex π hlam hprim, card_quot_eq_absNorm]

omit hP in
theorem norm_ringComplex_ne_zero : (‖ringComplex π‖ : ℂ) ≠ 0 := by
  exact_mod_cast norm_ne_zero_iff.mpr fun h => NeZero.ne π (ringComplex_injective
    (by rw [h, map_zero]))

omit hP in
/-- `ᾱ π = |π|` for `α = π/|π|`. -/
theorem conj_alpha_mul :
    conj (ringComplex π / (‖ringComplex π‖ : ℂ)) * ringComplex π = (‖ringComplex π‖ : ℂ) := by
  have hN := norm_ringComplex_ne_zero π
  rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, mul_comm, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.ofReal_pow, sq, mul_div_assoc, div_self hN, mul_one]

include h2 in
/-- **`G₁ G₅ = ε Q`, `G₂ G₄ = Q`, `G₃² = ε Q`**: `G_r G_{6−r} = χ^r(−1) Q` for `6 ∤ r`. -/
theorem gauss_mul_gauss_compl (r : ℕ) (hr : ¬ 6 ∣ r) (hr6 : r ≤ 6) :
    gaussSum (complexSexticChar (Ideal.span {π}) hlam ^ r) (principalTraceChar π (NeZero.ne π)) *
      gaussSum (complexSexticChar (Ideal.span {π}) hlam ^ (6 - r))
        (principalTraceChar π (NeZero.ne π)) =
      complexSexticChar (Ideal.span {π}) hlam (-1) ^ r * (Ideal.absNorm (Ideal.span {π}) : ℂ) := by
  letI : Field (O ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  set χ := complexSexticChar (Ideal.span {π}) hlam
  have h6 := (complexSexticChar_powers (Ideal.span {π}) hlam).2.2
  have hne : χ ^ r ≠ 1 := fun h => hr ((complexSexticChar_pow_eq_one_iff π hlam h2 r).mp h)
  have hinv : χ ^ (6 - r) = (χ ^ r)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_add, Nat.sub_add_cancel hr6, h6])
  rw [hinv, gaussSum_mul_gaussSum_inv_char hne (principalTraceChar_primitive π (NeZero.ne π)),
    card_quot_eq_absNorm, MulChar.pow_apply' χ (show r ≠ 0 by rintro rfl; exact hr (dvd_zero 6))]

include h2 in
/-- **`G₃ = N Γ`.** -/
theorem gauss_three_eq :
    gaussSum (complexSexticChar (Ideal.span {π}) hlam ^ 3) (principalTraceChar π (NeZero.ne π)) =
      (‖ringComplex π‖ : ℂ) * fixedDualAverage π := by
  letI : Field (O ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  have htr : quadraticTraceGauss π (NeZero.ne π) =
      gaussSum (complexQuadraticChar (Ideal.span {π})) (principalTraceChar π (NeZero.ne π)) := by
    have h := sum_traceChar_mul_sq π h2 (u := 1) one_ne_zero
    simp only [one_mul, MulChar.map_one] at h
    rw [quadraticTraceGauss_eq_sum, h]
  rw [(complexSexticChar_powers (Ideal.span {π}) hlam).2.1, ← htr,
    ← normalizedQuadraticTraceGauss_eq_fixedDualAverage π (NeZero.ne π),
    normalizedQuadraticTraceGauss, mul_div_cancel₀ _ (norm_ringComplex_ne_zero π)]

include h2 hprim in
/-- **`Γ² = ε`.** -/
theorem gamma_sq_eq_sextic :
    fixedDualAverage π ^ 2 = complexSexticChar (Ideal.span {π}) hlam (-1) := by
  rw [gamma_sq_eq π hlam h2 hprim, ← (complexSexticChar_powers (Ideal.span {π}) hlam).2.1,
    MulChar.pow_apply' _ (by norm_num), pow_succ, mulChar_neg_one_sq, one_mul]

include h2 in
/-- **`c₄³ = 1`**: `4` is a square. -/
theorem sexticChar_four_pow_three :
    complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 4) ^ 3 = 1 := by
  letI : Field (O ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  have h20 : Ideal.Quotient.mk (Ideal.span {π}) 2 ≠ 0 := fun h =>
    h2 (Ideal.Quotient.eq_zero_iff_mem.mp h)
  rw [← MulChar.pow_apply' _ (by norm_num), (complexSexticChar_powers (Ideal.span {π}) hlam).2.1,
    show (4 : O) = 2 ^ 2 by norm_num, map_pow, complexQuadraticChar, MulChar.ringHomComp_apply,
    quadraticChar_sq_one' h20, map_one]

omit [NeZero π] in
/-- A unit residue has a sixth root of unity as character value. -/
theorem sexticChar_pow_six (x : O ⧸ Ideal.span {π}) (hx : IsUnit x) :
    complexSexticChar (Ideal.span {π}) hlam x ^ 6 = 1 := by
  rw [← MulChar.pow_apply' _ (by norm_num), (complexSexticChar_powers (Ideal.span {π}) hlam).2.2,
    MulChar.one_apply hx]

omit [NeZero π] in
theorem sexticChar_ne_zero (x : O ⧸ Ideal.span {π}) (hx : IsUnit x) :
    complexSexticChar (Ideal.span {π}) hlam x ≠ 0 :=
  (hx.map _).ne_zero

/-! ### The local term -/

/-- `|π|` as a complex number. -/
def primeNorm : ℂ := (‖ringComplex π‖ : ℂ)

/-- `Q = N(π)` as a complex number. -/
def primeQ : ℂ := (Ideal.absNorm (Ideal.span {π}) : ℂ)

/-- `κ = ᾱ η_π`, `α = π/|π|`. -/
def primeKappa (ηp : ℂ) : ℂ := conj (ringComplex π / primeNorm π) * ηp

/-- `R = κ⁶ Q⁴ X⁶ V`. -/
def primeR (ηp X V : ℂ) : ℂ := primeKappa π ηp ^ 6 * primeQ π ^ 4 * X ^ 6 * V

/-- The local term of the Poisson series at the exponents `v = (e, l, k, m)`: squarefree part
`π^e`, cube part `π^l`, row twist `π^k` and frequency `H = u π^{j+6m}`. -/
def localTerm (ηp X Y V : ℂ) (u : O) (j : ℕ) (v : Fin 2 × ℕ × ℕ × ℕ) : ℂ :=
  primeKappa π ηp ^ ((v.1 : ℕ) + 3 * v.2.1) *
    correctedCoeff (π ^ v.2.2.1) (π ^ (v.1 : ℕ)) (π ^ v.2.1) (u * π ^ (j + 6 * v.2.2.2)) *
      (X / primeNorm π) ^ (v.1 : ℕ) * (X ^ 3 / primeQ π) ^ v.2.1 * (Y / primeQ π) ^ v.2.2.1 *
        V ^ v.2.2.2

include h2 hprim in
/-- **The local term through the Poisson coefficient.** With `t = e + 3l`, `ρ = χ(u)`:
the coefficient is `ε^{tk} γ₂(π^e) (c̄₄^t Γ^{t mod 2})⁻¹ ρ^k ρ^{−t} F(π^k, π^t; π^{j+6m})`. -/
theorem localTerm_eq (ηp X Y V : ℂ) {u : O} (hu : u ∉ Ideal.span {π}) (j : ℕ) (e : Fin 2)
    (l k m : ℕ) :
    localTerm π ηp X Y V u j (e, l, k, m) =
      primeKappa π ηp ^ ((e : ℕ) + 3 * l) *
        (complexSexticChar (Ideal.span {π}) hlam (-1) ^ (((e : ℕ) + 3 * l) * k) *
          thetaGauss (π ^ (e : ℕ)) *
          (conj (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 4)) ^ ((e : ℕ) + 3 * l) *
            fixedDualAverage π ^ (((e : ℕ) + 3 * l) % 2))⁻¹ *
          (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) ^ k *
            (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) ^ ((e : ℕ) + 3 * l))⁻¹ *
              poissonCoeff (π ^ k) (π ^ ((e : ℕ) + 3 * l)) (π ^ (j + 6 * m)))) *
        (X / primeNorm π) ^ (e : ℕ) * (X ^ 3 / primeQ π) ^ l * (Y / primeQ π) ^ k * V ^ m := by
  unfold localTerm
  dsimp only
  rw [correctedCoeff_prime_pow π h2, quadraticPhase_self π hlam h2 hprim,
    thetaPhase_prime_pow π hlam h2 hprim, poissonCoeff_unit_mul π hlam h2 hprim k _ hu]

omit hP in
theorem primeQ_ne_zero : primeQ π ≠ 0 := by
  rw [primeQ, ← card_quot_span]
  exact_mod_cast Fintype.card_ne_zero

/-- A root of unity of order dividing `d` reduces its exponents modulo `d`. -/
theorem pow_eq_pow_mod {z : ℂ} {d : ℕ} (hz : z ^ d = 1) (n : ℕ) : z ^ n = z ^ (n % d) := by
  conv_lhs => rw [← Nat.div_add_mod n d, pow_add, pow_mul, hz, one_pow, one_mul]

include h2 in
/-- `c̄₄³ = 1`. -/
theorem conj_sexticChar_four_pow_three :
    conj (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 4)) ^ 3 = 1 := by
  rw [← map_pow, sexticChar_four_pow_three π hlam h2, map_one]

/-! ### The families of exponents -/

/-! ### Periodicity of the local term -/

/-- **The layer values are periodic**: `L_{r+6}(n+6, j+6) = Q⁶ L_r(n, j)`. -/
theorem sexticLayer_shift (r : ℕ) {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    sexticLayer π hlam (r + 6) (n + 6) (j + 6) = primeQ π ^ 6 * sexticLayer π hlam r n j := by
  have hχ : complexSexticChar (Ideal.span {π}) hlam ^ (r + 6) =
      complexSexticChar (Ideal.span {π}) hlam ^ r := by
    rw [pow_add, (complexSexticChar_powers (Ideal.span {π}) hlam).2.2, mul_one]
  unfold sexticLayer
  rw [hχ, show (Ideal.absNorm (Ideal.span {π}) : ℂ) = primeQ π from rfl,
    show n + 6 - 1 = (n - 1) + 6 by omega]
  by_cases h6 : 6 ∣ r
  · rw [if_pos ((Nat.dvd_add_self_right).mpr h6), if_pos h6]
    simp only [show n + 6 ≤ j + 6 ↔ n ≤ j by omega, show n - 1 + 6 ≤ j + 6 ↔ n - 1 ≤ j by omega]
    split_ifs <;> ring
  · rw [if_neg (fun h => h6 ((Nat.dvd_add_self_right).mp h)), if_neg h6]
    simp only [show j + 6 = n - 1 + 6 ↔ j = n - 1 by omega]
    split_ifs <;> ring

include hlam h2 hprim in
/-- **The Poisson values are periodic**: `F(π^k, π^{t+6}; π^{j+6}) = Q⁶ F(π^k, π^t; π^j)` for
`t ≥ 1`. -/
theorem poissonCoeff_shift {t : ℕ} (ht : 1 ≤ t) (k j : ℕ) :
    poissonCoeff (π ^ k) (π ^ (t + 6)) (π ^ (j + 6)) =
      primeQ π ^ 6 * poissonCoeff (π ^ k) (π ^ t) (π ^ j) := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · rw [poissonCoeff_pow_zero_left π hlam h2 hprim (by omega),
        poissonCoeff_pow_zero_left π hlam h2 hprim ht, sexticLayer_shift π hlam _ ht]
    · rw [poissonCoeff_pow_one_left π hlam h2 hprim (by omega),
        poissonCoeff_pow_one_left π hlam h2 hprim ht, show t + 6 - 1 = (t - 1) + 6 by omega,
        show t + 6 + 1 = (t + 1) + 6 by omega, sexticLayer_shift π hlam _ (by omega)]
      ring
  · rw [poissonCoeff_pow_eq_zero π hlam h2 hprim (by omega) hk,
      poissonCoeff_pow_eq_zero π hlam h2 hprim ht hk, mul_zero]

include hlam h2 hprim in
/-- **Below the layer the Poisson value vanishes**: `F(π^k, π^t; π^j) = 0` for `j + 1 < t`. -/
theorem poissonCoeff_eq_zero_below {t j : ℕ} (hjt : j + 1 < t) (k : ℕ) :
    poissonCoeff (π ^ k) (π ^ t) (π ^ j) = 0 := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · rw [poissonCoeff_pow_zero_left π hlam h2 hprim (by omega)]
      unfold sexticLayer
      split_ifs <;> first | omega | simp
    · rw [poissonCoeff_pow_one_left π hlam h2 hprim (by omega)]
      unfold sexticLayer
      split_ifs <;> first | omega | simp
  · exact poissonCoeff_pow_eq_zero π hlam h2 hprim (by omega) hk _

include hlam h2 hprim in
/-- The local term vanishes below the layer: `j + 6m + 1 < e + 3l`. -/
theorem localTerm_eq_zero_below (ηp X Y V : ℂ) {u : O} (hu : u ∉ Ideal.span {π}) (j : ℕ)
    (e : Fin 2) (l k m : ℕ) (h : j + 6 * m + 1 < (e : ℕ) + 3 * l) :
    localTerm π ηp X Y V u j (e, l, k, m) = 0 := by
  rw [localTerm_eq π hlam h2 hprim ηp X Y V hu j e l k m,
    poissonCoeff_eq_zero_below π hlam h2 hprim h]
  simp

/-- The coefficient of the local term at `t = e + 3l` and the frequency `π^{j'}`:
`ε^{tk} γ₂(π^e) (c̄₄^t Γ^{t mod 2})⁻¹ ρ^k ρ^{−t} F(π^k, π^t; π^{j'})`. -/
def localCoef (u : O) (e t k j' : ℕ) : ℂ :=
  complexSexticChar (Ideal.span {π}) hlam (-1) ^ (t * k) * thetaGauss (π ^ e) *
    (conj (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 4)) ^ t *
      fixedDualAverage π ^ (t % 2))⁻¹ *
    (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) ^ k *
      (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) ^ t)⁻¹ *
        poissonCoeff (π ^ k) (π ^ t) (π ^ j'))

include h2 hprim in
theorem localTerm_eq_coef (ηp X Y V : ℂ) {u : O} (hu : u ∉ Ideal.span {π}) (j : ℕ) (e : Fin 2)
    (l k m : ℕ) :
    localTerm π ηp X Y V u j (e, l, k, m) =
      primeKappa π ηp ^ ((e : ℕ) + 3 * l) * localCoef π hlam u e ((e : ℕ) + 3 * l) k (j + 6 * m) *
        (X / primeNorm π) ^ (e : ℕ) * (X ^ 3 / primeQ π) ^ l * (Y / primeQ π) ^ k * V ^ m :=
  localTerm_eq π hlam h2 hprim ηp X Y V hu j e l k m

include h2 hprim in
/-- The coefficient is periodic: `C(e, t+6, k, j'+6) = Q⁶ C(e, t, k, j')` for `t ≥ 1`. -/
theorem localCoef_shift {u : O} (hu : u ∉ Ideal.span {π}) (e : ℕ) {t : ℕ} (ht : 1 ≤ t)
    (k j' : ℕ) :
    localCoef π hlam u e (t + 6) k (j' + 6) = primeQ π ^ 6 * localCoef π hlam u e t k j' := by
  have hρ := sexticChar_pow_six π hlam _ (unit_mk_of_not_mem π hu)
  have hc := conj_sexticChar_four_pow_three π hlam h2
  have hε := mulChar_neg_one_sq (complexSexticChar (Ideal.span {π}) hlam)
  have e1 : complexSexticChar (Ideal.span {π}) hlam (-1) ^ ((t + 6) * k) =
      complexSexticChar (Ideal.span {π}) hlam (-1) ^ (t * k) := by
    rw [show (t + 6) * k = t * k + 2 * (3 * k) by ring, pow_add,
      pow_mul (complexSexticChar (Ideal.span {π}) hlam (-1)) 2 (3 * k), hε, one_pow, mul_one]
  have e2 : conj (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 4)) ^ (t + 6) =
      conj (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 4)) ^ t := by
    rw [show t + 6 = t + 3 * 2 by rfl, pow_add, pow_mul, hc, one_pow, mul_one]
  have e3 : complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) ^ (t + 6) =
      complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) ^ t := by
    rw [pow_add, hρ, mul_one]
  unfold localCoef
  rw [e1, e2, e3, show (t + 6) % 2 = t % 2 by omega, poissonCoeff_shift π hlam h2 hprim ht]
  ring

include hlam h2 hprim in
/-- **Periodicity of the local term.** For `e + 3l ≥ 1`, raising the cube exponent by two and
the sixth-power exponent of the frequency by one multiplies the term by `R`. -/
theorem localTerm_shift (ηp X Y V : ℂ) {u : O} (hu : u ∉ Ideal.span {π}) (j : ℕ) (e : Fin 2)
    (l k m : ℕ) (ht : 1 ≤ (e : ℕ) + 3 * l) :
    localTerm π ηp X Y V u j (e, l + 2, k, m + 1) =
      primeR π ηp X V * localTerm π ηp X Y V u j (e, l, k, m) := by
  have hQ := primeQ_ne_zero π
  rw [localTerm_eq_coef π hlam h2 hprim ηp X Y V hu j e (l + 2) k (m + 1),
    localTerm_eq_coef π hlam h2 hprim ηp X Y V hu j e l k m,
    show (e : ℕ) + 3 * (l + 2) = ((e : ℕ) + 3 * l) + 6 by ring,
    show j + 6 * (m + 1) = (j + 6 * m) + 6 by ring, localCoef_shift π hlam h2 hprim hu _ ht]
  have key : primeQ π ^ 6 * (X ^ 3 / primeQ π) ^ 2 = primeQ π ^ 4 * X ^ 6 := by
    field_simp
  generalize localCoef π hlam u (e : ℕ) ((e : ℕ) + 3 * l) k (j + 6 * m) = C
  generalize (X / primeNorm π) ^ (e : ℕ) = A
  generalize (Y / primeQ π) ^ k = B
  unfold primeR
  rw [pow_add (primeKappa π ηp), pow_add (X ^ 3 / primeQ π), pow_succ V]
  linear_combination (primeKappa π ηp ^ ((e : ℕ) + 3 * l) * primeKappa π ηp ^ 6 * C * A *
    (X ^ 3 / primeQ π) ^ l * B * V ^ m * V) * key

include hlam h2 hprim in
/-- **A family of exponents is geometric in `R`.** For `e + 3l₀ ≥ 1` and `j < 6`, the term at
`(e, l₀ + 2r, k, m)` is `R^r` times the base term at `(e, l₀, k, m − r)`, and zero for `m < r`. -/
theorem localTerm_family (ηp X Y V : ℂ) {u : O} (hu : u ∉ Ideal.span {π}) {j : ℕ} (hj : j < 6)
    (e : Fin 2) (l₀ k : ℕ) (ht : 1 ≤ (e : ℕ) + 3 * l₀) (r m : ℕ) :
    localTerm π ηp X Y V u j (e, l₀ + 2 * r, k, m) =
      if r ≤ m then primeR π ηp X V ^ r * localTerm π ηp X Y V u j (e, l₀, k, m - r) else 0 := by
  induction r generalizing m with
  | zero => simp
  | succ r ih =>
    rcases m with _ | m
    · rw [if_neg (by omega)]
      exact localTerm_eq_zero_below π hlam h2 hprim ηp X Y V hu j e _ k 0 (by omega)
    · rw [show l₀ + 2 * (r + 1) = (l₀ + 2 * r) + 2 by ring,
        localTerm_shift π hlam h2 hprim ηp X Y V hu j e _ k m (by omega), ih m]
      by_cases hrm : r ≤ m
      · rw [if_pos hrm, if_pos (by omega), show m + 1 - (r + 1) = m - r by omega, pow_succ]
        ring
      · rw [if_neg hrm, if_neg (by omega), mul_zero]

/-! ### The Gauss sums through `G₁`, `Γ`, `c₄` -/

omit hP in
theorem ringComplex_ne_zero : ringComplex π ≠ 0 := fun h =>
  NeZero.ne π (ringComplex_injective (by rw [h, map_zero]))

include h2 in
theorem fixedDualAverage_prime_ne_zero : fixedDualAverage π ≠ 0 :=
  gamma_ne_zero (prime_odd π h2)

include h2 in
theorem sexticChar_four_ne_zero :
    complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 4) ≠ 0 := by
  intro h0
  have h := sexticChar_four_pow_three π hlam h2
  rw [h0] at h
  norm_num at h

include h2 in
/-- `c̄₄ = c₄⁻¹`. -/
theorem conj_sexticChar_four :
    conj (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 4)) =
      (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 4))⁻¹ := by
  set c := complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 4)
  have h3 := sexticChar_four_pow_three π hlam h2
  have hn : ‖c‖ = 1 := by
    have := congrArg norm h3
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) (by norm_num)).mp this
  have hc0 : c ≠ 0 := sexticChar_four_ne_zero π hlam h2
  refine eq_inv_of_mul_eq_one_left ?_
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
  norm_num

include hlam hprim in
/-- `Q = N²`. -/
theorem primeQ_eq : primeQ π = primeNorm π ^ 2 := (norm_sq_eq_absNorm π hlam hprim).symm

/-- `κ π = N η_π`. -/
theorem primeKappa_mul (ηp : ℂ) : primeKappa π ηp * ringComplex π = primeNorm π * ηp := by
  unfold primeKappa primeNorm
  rw [mul_right_comm, conj_alpha_mul]

include h2 in
theorem gauss_one_ne_zero :
    gaussSum (complexSexticChar (Ideal.span {π}) hlam) (principalTraceChar π (NeZero.ne π)) ≠ 0 := by
  intro h0
  have h := gauss_mul_gauss_compl π hlam h2 1 (by norm_num) (by norm_num)
  rw [pow_one, h0, zero_mul] at h
  have hε : complexSexticChar (Ideal.span {π}) hlam (-1) ≠ 0 := by
    intro h1
    have := mulChar_neg_one_sq (complexSexticChar (Ideal.span {π}) hlam)
    rw [h1] at this
    norm_num at this
  exact mul_ne_zero (pow_ne_zero 1 hε) (primeQ_ne_zero π) h.symm

include h2 hprim in
/-- `G₅ = ε N² / G₁`. -/
theorem gauss_five_eq :
    gaussSum (complexSexticChar (Ideal.span {π}) hlam ^ 5) (principalTraceChar π (NeZero.ne π)) =
      complexSexticChar (Ideal.span {π}) hlam (-1) * primeNorm π ^ 2 /
        gaussSum (complexSexticChar (Ideal.span {π}) hlam) (principalTraceChar π (NeZero.ne π)) := by
  have h := gauss_mul_gauss_compl π hlam h2 1 (by norm_num) (by norm_num)
  rw [pow_one, pow_one, show (Ideal.absNorm (Ideal.span {π}) : ℂ) = primeQ π from rfl,
    primeQ_eq π hlam hprim] at h
  rw [eq_div_iff (gauss_one_ne_zero π hlam h2), mul_comm]
  exact h

include h2 hprim in
/-- `G₂ = −π N Γ / (c₄ G₁)`. -/
theorem gauss_two_eq :
    gaussSum (complexSexticChar (Ideal.span {π}) hlam ^ 2) (principalTraceChar π (NeZero.ne π)) =
      -ringComplex π * primeNorm π * fixedDualAverage π /
        (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 4) *
          gaussSum (complexSexticChar (Ideal.span {π}) hlam) (principalTraceChar π (NeZero.ne π))) := by
  have h := sextic_gauss_product π hlam h2 hprim
  rw [gauss_three_eq π hlam h2] at h
  rw [eq_div_iff (mul_ne_zero (sexticChar_four_ne_zero π hlam h2) (gauss_one_ne_zero π hlam h2))]
  rw [show (‖ringComplex π‖ : ℂ) = primeNorm π from rfl,
    ← map_ofNat (Ideal.Quotient.mk (Ideal.span {π})) 4] at h
  linear_combination h

include h2 hprim in
/-- `G₄ = −N c₄ G₁ / (π Γ)`. -/
theorem gauss_four_eq :
    gaussSum (complexSexticChar (Ideal.span {π}) hlam ^ 4) (principalTraceChar π (NeZero.ne π)) =
      -(primeNorm π * complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 4) *
        gaussSum (complexSexticChar (Ideal.span {π}) hlam) (principalTraceChar π (NeZero.ne π))) /
          (ringComplex π * fixedDualAverage π) := by
  have h := gauss_mul_gauss_compl π hlam h2 2 (by norm_num) (by norm_num)
  rw [mulChar_neg_one_sq, one_mul, show (Ideal.absNorm (Ideal.span {π}) : ℂ) = primeQ π from rfl,
    primeQ_eq π hlam hprim, gauss_two_eq π hlam h2 hprim] at h
  have hπ := ringComplex_ne_zero π
  have hΓ := fixedDualAverage_prime_ne_zero π h2
  have hc := sexticChar_four_ne_zero π hlam h2
  have hg := gauss_one_ne_zero π hlam h2
  have hN : primeNorm π ≠ 0 := norm_ringComplex_ne_zero π
  rw [eq_div_iff (mul_ne_zero hπ hΓ)]
  field_simp at h
  linear_combination -h

include h2 hprim in
/-- `γ₂(π) = −π Γ / (c₄ G₁)`. -/
theorem thetaGauss_prime_eq :
    thetaGauss (π ^ 1) = -ringComplex π * fixedDualAverage π /
      (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 4) *
        gaussSum (complexSexticChar (Ideal.span {π}) hlam) (principalTraceChar π (NeZero.ne π))) := by
  rw [thetaGauss_congr (pow_one π), thetaGauss_prime π hlam h2 hprim, gauss_two_eq π hlam h2 hprim]
  have hN : primeNorm π ≠ 0 := norm_ringComplex_ne_zero π
  rw [show (‖ringComplex π‖ : ℂ) = primeNorm π from rfl]
  field_simp

end Prime

end GaloisForLFunctions.FamilyContinuationTheory
