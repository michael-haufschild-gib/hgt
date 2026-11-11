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


/-! ### Geometric sums -/

/-- A point mass. -/
theorem hasSum_point (i₀ : ℕ) (a : ℂ) : HasSum (fun i : ℕ => if i = i₀ then a else 0) a :=
  hasSum_ite_eq i₀ a

theorem summable_norm_point (i₀ : ℕ) (a : ℂ) :
    Summable (fun i : ℕ => ‖if i = i₀ then a else 0‖) := by
  refine summable_of_ne_finset_zero (s := {i₀}) fun i hi => ?_
  rw [if_neg (by simpa using hi), norm_zero]

/-- A geometric tail after an arbitrary first term: `a, c, cV, cV², …`. -/
theorem hasSum_shift_geom (a c V : ℂ) (hV : ‖V‖ < 1) :
    HasSum (fun i : ℕ => if i = 0 then a else c * V ^ (i - 1)) (a + c * (1 - V)⁻¹) := by
  refine (hasSum_nat_add_iff' 1).mp ?_
  simp only [Nat.add_sub_cancel, Finset.range_one, Finset.sum_singleton, ↓reduceIte,
    Nat.add_one_ne_zero, add_sub_cancel_left]
  exact (hasSum_geometric_of_norm_lt_one hV).mul_left c

theorem summable_norm_shift_geom (a c V : ℂ) (hV : ‖V‖ < 1) :
    Summable (fun i : ℕ => ‖if i = 0 then a else c * V ^ (i - 1)‖) := by
  refine (summable_nat_add_iff 1).mp ?_
  simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false, norm_mul, norm_pow]
  exact (summable_geometric_of_lt_one (norm_nonneg _) hV).mul_left _

/-- A geometric sequence after an arbitrary first term: `a, cV, cV², …`. -/
theorem hasSum_geom_from (a c V : ℂ) (hV : ‖V‖ < 1) :
    HasSum (fun i : ℕ => if i = 0 then a else c * V ^ i) (a + c * V * (1 - V)⁻¹) := by
  have h := hasSum_shift_geom a (c * V) V hV
  convert h using 2 with i
  split_ifs with hi
  · rfl
  · rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hi)]

theorem summable_norm_geom_from (a c V : ℂ) (hV : ‖V‖ < 1) :
    Summable (fun i : ℕ => ‖if i = 0 then a else c * V ^ i‖) := by
  refine (summable_nat_add_iff 1).mp ?_
  simp only [Nat.add_one_ne_zero, if_false, norm_mul, norm_pow]
  exact ((summable_geometric_of_lt_one (norm_nonneg _) hV).comp_injective
    (add_left_injective 1)).mul_left _


/-- A point mass under a side condition. -/
theorem hasSum_point_and (i₀ : ℕ) (P : Prop) [Decidable P] (a : ℂ) :
    HasSum (fun i : ℕ => if i = i₀ ∧ P then a else 0) (if P then a else 0) := by
  convert hasSum_point i₀ (if P then a else 0) using 1
  funext i
  by_cases hi : i = i₀ <;> by_cases hP : P <;> simp [hi, hP]

theorem summable_norm_point_and (i₀ : ℕ) (P : Prop) [Decidable P] (a : ℂ) :
    Summable (fun i : ℕ => ‖if i = i₀ ∧ P then a else 0‖) := by
  refine summable_of_ne_finset_zero (s := {i₀}) fun i hi => ?_
  rw [if_neg (fun h => by simp [h.1] at hi), norm_zero]

/-- **A geometric block.** If `φ` has sum `Φ` with summable norms and `‖R‖ < 1`, the double
series `Σ_{r ≤ m} R^r φ(m − r)` has sum `(1 − R)⁻¹ Φ`. -/
theorem hasSum_block {φ : ℕ → ℂ} {Φ R : ℂ} (hφ : HasSum φ Φ) (hφn : Summable fun i => ‖φ i‖)
    (hR : ‖R‖ < 1) :
    HasSum (fun p : ℕ × ℕ => if p.1 ≤ p.2 then R ^ p.1 * φ (p.2 - p.1) else 0)
      ((1 - R)⁻¹ * Φ) := by
  let g : ℕ × ℕ → ℕ × ℕ := fun q => (q.1, q.1 + q.2)
  have hg : Function.Injective g := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [g, Prod.mk.injEq] at h
    ext <;> omega
  have hvan : ∀ p : ℕ × ℕ, p ∉ Set.range g →
      (if p.1 ≤ p.2 then R ^ p.1 * φ (p.2 - p.1) else 0) = 0 := by
    rintro ⟨r, m⟩ hp
    rw [if_neg]
    intro hrm
    exact hp ⟨(r, m - r), by simp only [g]; ext <;> simp; omega⟩
  refine (hg.hasSum_iff hvan).mp ?_
  have hprod := (hasSum_geometric_of_norm_lt_one hR).mul hφ
    (summable_mul_of_summable_norm (by simpa using summable_geometric_of_lt_one (norm_nonneg _) hR)
      hφn)
  have hcomp : (fun p : ℕ × ℕ => if p.1 ≤ p.2 then R ^ p.1 * φ (p.2 - p.1) else 0) ∘ g =
      fun x : ℕ × ℕ => R ^ x.1 * φ x.2 := by
    funext q
    simp only [Function.comp, g, Nat.le_add_right, if_true, Nat.add_sub_cancel_left]
  rw [hcomp]
  exact hprod


/-! ### The blocks of exponents -/

/-- The least cube exponent of the family `(e, l mod 2)` with `e + 3l ≥ 1`. -/
def blockBase (e p : Fin 2) : ℕ := if e = 0 ∧ p = 0 then 2 else (p : ℕ)

/-- The exponents of a block: `none` is the row `t = 0` (`(k, m) ↦ (0, 0, k, m)`); `some (e, p, k)`
is the family `(r, m) ↦ (e, l₀ + 2r, k, m)`, `l₀ = blockBase e p`. -/
def blockMap : Option (Fin 2 × Fin 2 × Fin 2) → ℕ × ℕ → Fin 2 × ℕ × ℕ × ℕ
  | none => fun q => (0, 0, q.1, q.2)
  | some b => fun q => (b.1, blockBase b.1 b.2.1 + 2 * q.1, (b.2.2 : ℕ), q.2)

theorem blockMap_injective (b : Option (Fin 2 × Fin 2 × Fin 2)) :
    Function.Injective (blockMap b) := by
  rcases b with _ | b
  · rintro ⟨a, c⟩ ⟨a', c'⟩ h
    simp only [blockMap, Prod.mk.injEq, true_and] at h
    rw [h.1, h.2]
  · rintro ⟨a, c⟩ ⟨a', c'⟩ h
    simp only [blockMap, Prod.mk.injEq, true_and, add_right_inj] at h
    ext <;> omega

theorem blockMap_disjoint {b b' : Option (Fin 2 × Fin 2 × Fin 2)} (hne : b ≠ b') :
    Disjoint (Set.range (blockMap b)) (Set.range (blockMap b')) := by
  rw [Set.disjoint_left]
  rintro _ ⟨q, rfl⟩ ⟨q', h⟩
  rcases b with _ | ⟨e, p, k⟩ <;> rcases b' with _ | ⟨e', p', k'⟩
  · exact hne rfl
  · fin_cases e' <;> fin_cases p' <;> fin_cases k' <;>
      simp [blockMap, blockBase, Prod.ext_iff] at h
  · fin_cases e <;> fin_cases p <;> fin_cases k <;>
      simp [blockMap, blockBase, Prod.ext_iff] at h <;> omega
  · fin_cases e <;> fin_cases p <;> fin_cases k <;> fin_cases e' <;> fin_cases p' <;>
      fin_cases k' <;> simp [blockMap, blockBase, Prod.ext_iff] at h hne <;> omega

/-- Every exponent with `e + 3l = 0` or `k ≤ 1` lies in a block. -/
theorem exists_blockMap (v : Fin 2 × ℕ × ℕ × ℕ) (hv : ((v.1 : ℕ) = 0 ∧ v.2.1 = 0) ∨ v.2.2.1 ≤ 1) :
    ∃ b q, blockMap b q = v := by
  obtain ⟨e, l, k, m⟩ := v
  by_cases h0 : (e : ℕ) = 0 ∧ l = 0
  · refine ⟨none, (k, m), ?_⟩
    have he : e = 0 := Fin.ext h0.1
    simp [blockMap, he, h0.2]
  · have hk : k ≤ 1 := hv.resolve_left h0
    refine ⟨some (e, ⟨l % 2, Nat.mod_lt _ (by norm_num)⟩, ⟨k, by omega⟩),
      ((l - blockBase e ⟨l % 2, Nat.mod_lt _ (by norm_num)⟩) / 2, m), ?_⟩
    simp only [blockMap, Prod.mk.injEq, true_and, and_true]
    unfold blockBase
    split_ifs with h
    · have h1 : l % 2 = 0 := by simpa [Fin.ext_iff] using h.2
      have h2 : l ≠ 0 := fun hl => h0 ⟨by rw [h.1]; rfl, hl⟩
      omega
    · simp only [Fin.val_mk]
      omega

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

omit hP in
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

/-! ### The base terms of the families -/

include hlam h2 hprim in
/-- **The rows with `t = 0`**: `V^m` for `k = 0`, `(ρY)^k` for `k ≥ 1`, `m = j = 0`. -/
theorem localTerm_T0 (ηp X Y V : ℂ) {u : O} (hu : u ∉ Ideal.span {π}) (j k m : ℕ) :
    localTerm π ηp X Y V u j (0, 0, k, m) =
      if k = 0 then V ^ m else if m = 0 ∧ j = 0 then
        (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) * Y) ^ k else 0 := by
  have hQ := primeQ_ne_zero π
  rw [localTerm_eq_coef π hlam h2 hprim ηp X Y V hu j 0 0 k m]
  unfold localCoef
  rw [show ((0 : Fin 2) : ℕ) = 0 from rfl, show 0 + 3 * 0 = 0 from rfl,
    thetaGauss_of_eq_one (pow_zero π)]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [poissonCoeff_of_eq_one (pow_zero π) (pow_zero π), if_pos rfl]
    simp
  · rw [poissonCoeff_pow_zero_right π hlam h2 hprim hk, if_neg (Nat.pos_iff_ne_zero.mp hk),
      show (Ideal.absNorm (Ideal.span {π}) : ℂ) = primeQ π from rfl]
    by_cases hc : m = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := hc
      rw [if_pos rfl, if_pos ⟨rfl, rfl⟩]
      simp only [Fin.val_zero, pow_zero, mul_zero, zero_mul, Nat.zero_mod, inv_one, mul_one,
        one_mul, div_pow, mul_pow]
      field_simp
    · rw [if_neg (by omega), if_neg hc]
      simp

include hlam h2 hprim in
/-- **Base of `(0, 2r+2)`, `k = 0`.** -/
theorem localTerm_A0 (ηp X Y V : ℂ) {u : O} (hu : u ∉ Ideal.span {π}) {j : ℕ} (hj : j < 6)
    (i : ℕ) :
    localTerm π ηp X Y V u j (0, 2, 0, i) =
      if i = 0 then (if j = 5 then -(primeKappa π ηp ^ 6 * primeQ π ^ 3 * X ^ 6) else 0)
      else primeR π ηp X V * (1 - (primeQ π)⁻¹) * V ^ (i - 1) := by
  have hQ := primeQ_ne_zero π
  have hρ := sexticChar_pow_six π hlam _ (unit_mk_of_not_mem π hu)
  have hc := conj_sexticChar_four_pow_three π hlam h2
  rw [localTerm_eq_coef π hlam h2 hprim ηp X Y V hu j 0 2 0 i]
  unfold localCoef
  rw [show ((0 : Fin 2) : ℕ) = 0 from rfl, show 0 + 3 * 2 = 6 from rfl,
    thetaGauss_of_eq_one (pow_zero π),
    poissonCoeff_pow_zero_left π hlam h2 hprim (by norm_num)]
  unfold sexticLayer
  rw [if_pos (dvd_refl 6), show (Ideal.absNorm (Ideal.span {π}) : ℂ) = primeQ π from rfl,
    show (6 : ℕ) = 3 * 2 from rfl, pow_mul (conj _), hc, show 3 * 2 = 6 from rfl, hρ]
  simp only [Fin.val_zero, pow_zero, mul_zero, one_pow, one_mul, inv_one, mul_one,
    show (6 : ℕ) % 2 = 0 from rfl, show (6 : ℕ) - 1 = 5 from rfl]
  rcases i with _ | i
  · by_cases hj5 : j = 5
    · subst hj5
      simp (disch := omega) only [if_pos, if_neg, ite_true]
      field_simp
      ring
    · simp (disch := omega) only [if_pos, if_neg]
      simp
  · simp (disch := omega) only [if_pos, if_neg]
    unfold primeR
    rw [show i + 1 - 1 = i by omega, pow_succ V]
    field_simp

include hlam h2 hprim in
/-- **Base of `(0, 2r+2)`, `k = 1`.** -/
theorem localTerm_A1 (ηp X Y V : ℂ) {u : O} (hu : u ∉ Ideal.span {π}) {j : ℕ} (hj : j < 6)
    (i : ℕ) :
    localTerm π ηp X Y V u j (0, 2, 1, i) =
      if i = 1 ∧ j = 0 then
        complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) * Y * primeR π ηp X V
      else 0 := by
  have hQ := primeQ_ne_zero π
  have hρ := sexticChar_pow_six π hlam _ (unit_mk_of_not_mem π hu)
  have hρ0 := sexticChar_ne_zero π hlam _ (unit_mk_of_not_mem π hu)
  have hc := conj_sexticChar_four_pow_three π hlam h2
  have hε := mulChar_neg_one_sq (complexSexticChar (Ideal.span {π}) hlam)
  have hN : primeNorm π ≠ 0 := norm_ringComplex_ne_zero π
  have hg := gauss_one_ne_zero π hlam h2
  rw [localTerm_eq_coef π hlam h2 hprim ηp X Y V hu j 0 2 1 i]
  unfold localCoef
  rw [show ((0 : Fin 2) : ℕ) = 0 from rfl, show 0 + 3 * 2 = 6 from rfl,
    thetaGauss_of_eq_one (pow_zero π),
    poissonCoeff_pow_one_left π hlam h2 hprim (by norm_num)]
  unfold sexticLayer
  rw [if_neg (by norm_num), show (Ideal.absNorm (Ideal.span {π}) : ℂ) = primeQ π from rfl,
    show (6 : ℕ) = 3 * 2 from rfl, pow_mul (conj _), hc, show 3 * 2 = 6 from rfl, hρ]
  simp only [Fin.val_zero, pow_zero, one_pow, one_mul, inv_one, mul_one,
    show (6 : ℕ) % 2 = 0 from rfl, show (6 : ℕ) - 1 = 5 from rfl, show (6 : ℕ) + 1 - 1 = 6 from rfl]
  by_cases hcnd : i = 1 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := hcnd
    simp (disch := omega) only [if_pos, if_neg, and_self, ite_true]
    rw [gauss_five_eq π hlam h2 hprim, primeQ_eq π hlam hprim]
    unfold primeR
    rw [primeQ_eq π hlam hprim]
    field_simp
    linear_combination (primeKappa π ηp ^ 6 * X ^ 6 * Y * V *
      (complexSexticChar (Ideal.span {π}) hlam (-1) ^ 6 + complexSexticChar (Ideal.span {π}) hlam (-1) ^ 4
        + complexSexticChar (Ideal.span {π}) hlam (-1) ^ 2 + 1)) * hε
  · rw [if_neg (by omega), if_neg hcnd]
    simp

include hlam h2 hprim in
/-- **Base of `(1, 2r)`, `k = 0`.** -/
theorem localTerm_B0 (ηp X Y V : ℂ) {u : O} (hu : u ∉ Ideal.span {π}) (j i : ℕ) :
    localTerm π ηp X Y V u j (1, 0, 0, i) =
      if i = 0 ∧ j = 0 then
        -(ηp * (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u))⁻¹ * X) else 0 := by
  have hρ0 := sexticChar_ne_zero π hlam _ (unit_mk_of_not_mem π hu)
  have hN : primeNorm π ≠ 0 := norm_ringComplex_ne_zero π
  have hg := gauss_one_ne_zero π hlam h2
  have hΓ := fixedDualAverage_prime_ne_zero π h2
  have hc0 := sexticChar_four_ne_zero π hlam h2
  have hπ := ringComplex_ne_zero π
  rw [localTerm_eq_coef π hlam h2 hprim ηp X Y V hu j 1 0 0 i]
  unfold localCoef
  rw [show ((1 : Fin 2) : ℕ) = 1 from rfl, show 1 + 3 * 0 = 1 from rfl,
    poissonCoeff_pow_zero_left π hlam h2 hprim le_rfl]
  unfold sexticLayer
  rw [if_neg (by norm_num)]
  by_cases hcnd : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := hcnd
    rw [if_pos rfl, if_pos ⟨rfl, rfl⟩, thetaGauss_prime_eq π hlam h2 hprim,
      conj_sexticChar_four π hlam h2]
    have hκ := primeKappa_mul π ηp
    generalize primeKappa π ηp = κ at hκ ⊢
    obtain rfl : ηp = κ * ringComplex π / primeNorm π := by
      rw [eq_div_iff hN, mul_comm ηp, hκ]
    simp only [Fin.val_one, pow_zero, pow_one, mul_zero, one_mul, mul_one,
      show (1 : ℕ) % 2 = 1 from rfl, show (1 : ℕ) - 1 = 0 from rfl]
    field_simp
  · rw [if_neg (by omega), if_neg hcnd]
    simp

include hlam h2 hprim in
/-- **Base of `(1, 2r)`, `k = 1`.** -/
theorem localTerm_B1 (ηp X Y V : ℂ) {u : O} (hu : u ∉ Ideal.span {π}) (j i : ℕ) :
    localTerm π ηp X Y V u j (1, 0, 1, i) =
      if 1 ≤ i ∨ 2 ≤ j then -(ηp * (primeQ π - 1) * X * Y * V ^ i)
      else if j = 1 then ηp * X * Y else 0 := by
  have hQ := primeQ_ne_zero π
  have hN : primeNorm π ≠ 0 := norm_ringComplex_ne_zero π
  have hg := gauss_one_ne_zero π hlam h2
  have hΓ := fixedDualAverage_prime_ne_zero π h2
  have hc0 := sexticChar_four_ne_zero π hlam h2
  have hπ := ringComplex_ne_zero π
  have hρ0 := sexticChar_ne_zero π hlam _ (unit_mk_of_not_mem π hu)
  have hε := mulChar_neg_one_sq (complexSexticChar (Ideal.span {π}) hlam)
  rw [localTerm_eq_coef π hlam h2 hprim ηp X Y V hu j 1 0 1 i]
  unfold localCoef
  rw [show ((1 : Fin 2) : ℕ) = 1 from rfl, show 1 + 3 * 0 = 1 from rfl,
    poissonCoeff_pow_one_left π hlam h2 hprim le_rfl]
  unfold sexticLayer
  rw [if_pos (by norm_num), thetaGauss_prime_eq π hlam h2 hprim, conj_sexticChar_four π hlam h2,
    show (Ideal.absNorm (Ideal.span {π}) : ℂ) = primeQ π from rfl]
  have hκ := primeKappa_mul π ηp
  generalize primeKappa π ηp = κ at hκ ⊢
  obtain rfl : ηp = κ * ringComplex π / primeNorm π := by
    rw [eq_div_iff hN, mul_comm ηp, hκ]
  simp only [Fin.val_one, pow_zero, pow_one, one_mul, mul_one,
    show (1 : ℕ) % 2 = 1 from rfl, show (1 : ℕ) - 1 = 0 from rfl, show (1 : ℕ) + 1 = 2 from rfl,
    show (2 : ℕ) - 1 = 1 from rfl]
  by_cases h1 : 1 ≤ i ∨ 2 ≤ j
  · simp (disch := omega) only [if_pos, if_neg]
    field_simp
    linear_combination (-(κ * (primeQ π - 1) * X * Y * V ^ i)) * hε
  · rw [if_neg h1]
    by_cases hj1 : j = 1
    · subst hj1
      have hi : i = 0 := by omega
      subst hi
      simp (disch := omega) only [if_pos, if_neg, ite_true]
      field_simp
      linear_combination (κ * primeQ π * X * Y) * hε
    · simp (disch := omega) only [if_pos, if_neg]
      simp

include hlam h2 hprim in
/-- **Base of `(0, 2r+1)`, `k = 0`.** -/
theorem localTerm_C0 (ηp X Y V : ℂ) {u : O} (hu : u ∉ Ideal.span {π}) (j i : ℕ) :
    localTerm π ηp X Y V u j (0, 1, 0, i) =
      if i = 0 ∧ j = 2 then primeKappa π ηp ^ 3 *
        (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) ^ 3)⁻¹ *
          primeNorm π ^ 3 * X ^ 3 else 0 := by
  have hN : primeNorm π ≠ 0 := norm_ringComplex_ne_zero π
  have hΓ := fixedDualAverage_prime_ne_zero π h2
  have hρ0 := sexticChar_ne_zero π hlam _ (unit_mk_of_not_mem π hu)
  have hc := conj_sexticChar_four_pow_three π hlam h2
  rw [localTerm_eq_coef π hlam h2 hprim ηp X Y V hu j 0 1 0 i]
  unfold localCoef
  rw [show ((0 : Fin 2) : ℕ) = 0 from rfl, show 0 + 3 * 1 = 3 from rfl,
    thetaGauss_of_eq_one (pow_zero π), poissonCoeff_pow_zero_left π hlam h2 hprim (by norm_num)]
  unfold sexticLayer
  rw [if_neg (by norm_num), hc, show (Ideal.absNorm (Ideal.span {π}) : ℂ) = primeQ π from rfl]
  by_cases hcnd : i = 0 ∧ j = 2
  · obtain ⟨rfl, rfl⟩ := hcnd
    rw [if_pos rfl, if_pos ⟨rfl, rfl⟩, gauss_three_eq π hlam h2, primeQ_eq π hlam hprim]
    simp only [pow_zero, pow_one, mul_zero, one_mul, mul_one,
      show (3 : ℕ) % 2 = 1 from rfl, show (3 : ℕ) - 1 = 2 from rfl]
    rw [show (‖ringComplex π‖ : ℂ) = primeNorm π from rfl]
    field_simp
  · rw [if_neg (by omega), if_neg hcnd]
    simp

include hlam h2 hprim in
/-- **Base of `(0, 2r+1)`, `k = 1`.** -/
theorem localTerm_C1 (ηp X Y V : ℂ) {u : O} (hu : u ∉ Ideal.span {π}) (j i : ℕ) :
    localTerm π ηp X Y V u j (0, 1, 1, i) =
      if i = 0 ∧ j = 3 then -(ηp * (primeKappa π ηp ^ 2 *
        conj (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 4))) *
          (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) ^ 2)⁻¹ *
            primeQ π ^ 2 * X ^ 3 * Y) else 0 := by
  have hN : primeNorm π ≠ 0 := norm_ringComplex_ne_zero π
  have hΓ := fixedDualAverage_prime_ne_zero π h2
  have hρ0 := sexticChar_ne_zero π hlam _ (unit_mk_of_not_mem π hu)
  have hc := conj_sexticChar_four_pow_three π hlam h2
  have hc0 := sexticChar_four_ne_zero π hlam h2
  have hg := gauss_one_ne_zero π hlam h2
  have hπ := ringComplex_ne_zero π
  have hε := mulChar_neg_one_sq (complexSexticChar (Ideal.span {π}) hlam)
  rw [localTerm_eq_coef π hlam h2 hprim ηp X Y V hu j 0 1 1 i]
  unfold localCoef
  rw [show ((0 : Fin 2) : ℕ) = 0 from rfl, show 0 + 3 * 1 = 3 from rfl,
    thetaGauss_of_eq_one (pow_zero π), poissonCoeff_pow_one_left π hlam h2 hprim (by norm_num)]
  unfold sexticLayer
  rw [if_neg (by norm_num), hc, show (Ideal.absNorm (Ideal.span {π}) : ℂ) = primeQ π from rfl]
  by_cases hcnd : i = 0 ∧ j = 3
  · obtain ⟨rfl, rfl⟩ := hcnd
    rw [if_pos rfl, if_pos ⟨rfl, rfl⟩, gauss_two_eq π hlam h2 hprim, primeQ_eq π hlam hprim,
      conj_sexticChar_four π hlam h2]
    have hκ := primeKappa_mul π ηp
    generalize primeKappa π ηp = κ at hκ ⊢
    obtain rfl : ηp = κ * ringComplex π / primeNorm π := by
      rw [eq_div_iff hN, mul_comm ηp, hκ]
    simp only [pow_zero, pow_one, mul_zero, one_mul, mul_one,
      show (3 : ℕ) % 2 = 1 from rfl, show (3 : ℕ) - 1 = 2 from rfl, show (3 : ℕ) + 1 = 4 from rfl,
      show (4 : ℕ) - 1 = 3 from rfl]
    field_simp
    set ε := complexSexticChar (Ideal.span {π}) hlam (-1)
    linear_combination (-(κ ^ 3 * X ^ 3 * Y * (ε ^ 2 + 1))) * hε
  · rw [if_neg (by omega), if_neg hcnd]
    simp

include hlam h2 hprim in
/-- **Base of `(1, 2r+1)`, `k = 0`.** -/
theorem localTerm_D0 (ηp X Y V : ℂ) {u : O} (hu : u ∉ Ideal.span {π}) (j i : ℕ) :
    localTerm π ηp X Y V u j (1, 1, 0, i) =
      if i = 0 ∧ j = 3 then (primeKappa π ηp ^ 2 *
        conj (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 4))) ^ 2 *
          (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) ^ 4)⁻¹ *
            primeQ π ^ 2 * X ^ 4 else 0 := by
  have hN : primeNorm π ≠ 0 := norm_ringComplex_ne_zero π
  have hΓ := fixedDualAverage_prime_ne_zero π h2
  have hρ0 := sexticChar_ne_zero π hlam _ (unit_mk_of_not_mem π hu)
  have hc3 := sexticChar_four_pow_three π hlam h2
  have hc0 := sexticChar_four_ne_zero π hlam h2
  have hg := gauss_one_ne_zero π hlam h2
  have hπ := ringComplex_ne_zero π
  rw [localTerm_eq_coef π hlam h2 hprim ηp X Y V hu j 1 1 0 i]
  unfold localCoef
  rw [show ((1 : Fin 2) : ℕ) = 1 from rfl, show 1 + 3 * 1 = 4 from rfl,
    poissonCoeff_pow_zero_left π hlam h2 hprim (by norm_num)]
  unfold sexticLayer
  rw [if_neg (by norm_num), show (Ideal.absNorm (Ideal.span {π}) : ℂ) = primeQ π from rfl]
  by_cases hcnd : i = 0 ∧ j = 3
  · obtain ⟨rfl, rfl⟩ := hcnd
    rw [if_pos rfl, if_pos ⟨rfl, rfl⟩, gauss_four_eq π hlam h2 hprim, primeQ_eq π hlam hprim,
      conj_sexticChar_four π hlam h2, thetaGauss_prime_eq π hlam h2 hprim]
    simp only [pow_zero, pow_one, mul_zero, one_mul, mul_one,
      show (4 : ℕ) % 2 = 0 from rfl, show (4 : ℕ) - 1 = 3 from rfl]
    field_simp
    set c := complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 4)
    linear_combination (primeKappa π ηp ^ 4 * X ^ 4 * (c ^ 3 + 1)) * hc3
  · rw [if_neg (by omega), if_neg hcnd]
    simp

include hlam h2 hprim in
/-- **Base of `(1, 2r+1)`, `k = 1`.** -/
theorem localTerm_D1 (ηp X Y V : ℂ) {u : O} (hu : u ∉ Ideal.span {π}) (j i : ℕ) :
    localTerm π ηp X Y V u j (1, 1, 1, i) =
      if i = 0 ∧ j = 4 then -(ηp * primeKappa π ηp ^ 3 *
        (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) ^ 3)⁻¹ *
          primeNorm π ^ 5 * X ^ 4 * Y) else 0 := by
  have hN : primeNorm π ≠ 0 := norm_ringComplex_ne_zero π
  have hΓ := fixedDualAverage_prime_ne_zero π h2
  have hρ0 := sexticChar_ne_zero π hlam _ (unit_mk_of_not_mem π hu)
  have hc3 := sexticChar_four_pow_three π hlam h2
  have hc0 := sexticChar_four_ne_zero π hlam h2
  have hg := gauss_one_ne_zero π hlam h2
  have hπ := ringComplex_ne_zero π
  have hε := mulChar_neg_one_sq (complexSexticChar (Ideal.span {π}) hlam)
  have hΓ2 := gamma_sq_eq_sextic π hlam h2 hprim
  rw [localTerm_eq_coef π hlam h2 hprim ηp X Y V hu j 1 1 1 i]
  unfold localCoef
  rw [show ((1 : Fin 2) : ℕ) = 1 from rfl, show 1 + 3 * 1 = 4 from rfl,
    poissonCoeff_pow_one_left π hlam h2 hprim (by norm_num)]
  unfold sexticLayer
  rw [if_neg (by norm_num), show (Ideal.absNorm (Ideal.span {π}) : ℂ) = primeQ π from rfl]
  by_cases hcnd : i = 0 ∧ j = 4
  · obtain ⟨rfl, rfl⟩ := hcnd
    rw [if_pos rfl, if_pos ⟨rfl, rfl⟩, gauss_three_eq π hlam h2, primeQ_eq π hlam hprim,
      conj_sexticChar_four π hlam h2, thetaGauss_prime_eq π hlam h2 hprim]
    have hκ := primeKappa_mul π ηp
    generalize primeKappa π ηp = κ at hκ ⊢
    obtain rfl : ηp = κ * ringComplex π / primeNorm π := by
      rw [eq_div_iff hN, mul_comm ηp, hκ]
    simp only [pow_zero, pow_one, one_mul, mul_one,
      show (4 : ℕ) % 2 = 0 from rfl, show (4 : ℕ) - 1 = 3 from rfl, show (4 : ℕ) + 1 = 5 from rfl,
      show (5 : ℕ) - 1 = 4 from rfl]
    rw [show (‖ringComplex π‖ : ℂ) = primeNorm π from rfl]
    field_simp
    set ε := complexSexticChar (Ideal.span {π}) hlam (-1)
    set c := complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 4)
    linear_combination (-(κ ^ 4 * X ^ 4 * Y * ε ^ 5 * c ^ 3)) * hΓ2 +
      (-(κ ^ 4 * X ^ 4 * Y * c ^ 3 * (ε ^ 4 + ε ^ 2 + 1))) * hε + (-(κ ^ 4 * X ^ 4 * Y)) * hc3
  · rw [if_neg (by omega), if_neg hcnd]
    simp

/-! ### The local identity -/

/-- The sums of the base terms of the eight families `(e, l mod 2, k)`. -/
def baseSum (ηp X Y V : ℂ) (u : O) (j : ℕ) (e p k : Fin 2) : ℂ :=
  if e = 0 then
    if p = 0 then
      (if k = 0 then
        (if j = 5 then -(primeKappa π ηp ^ 6 * primeQ π ^ 3 * X ^ 6) else 0) +
          primeR π ηp X V * (1 - (primeQ π)⁻¹) * (1 - V)⁻¹
      else if j = 0 then
        complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) * Y * primeR π ηp X V
      else 0)
    else
      (if k = 0 then
        (if j = 2 then primeKappa π ηp ^ 3 *
          (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) ^ 3)⁻¹ *
            primeNorm π ^ 3 * X ^ 3 else 0)
      else if j = 3 then -(ηp * (primeKappa π ηp ^ 2 *
        conj (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 4))) *
          (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) ^ 2)⁻¹ *
            primeQ π ^ 2 * X ^ 3 * Y) else 0)
  else
    if p = 0 then
      (if k = 0 then
        (if j = 0 then
          -(ηp * (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u))⁻¹ * X) else 0)
      else if 2 ≤ j then -(ηp * (primeQ π - 1) * X * Y) * (1 - V)⁻¹
      else (if j = 1 then ηp * X * Y else 0) + -(ηp * (primeQ π - 1) * X * Y) * V * (1 - V)⁻¹)
    else
      (if k = 0 then
        (if j = 3 then (primeKappa π ηp ^ 2 *
          conj (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 4))) ^ 2 *
            (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) ^ 4)⁻¹ *
              primeQ π ^ 2 * X ^ 4 else 0)
      else if j = 4 then -(ηp * primeKappa π ηp ^ 3 *
        (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) ^ 3)⁻¹ *
          primeNorm π ^ 5 * X ^ 4 * Y) else 0)

include h2 hprim in
/-- The base series of each family has its sum, with summable norms. -/
theorem hasSum_base (ηp X Y V : ℂ) {u : O} (hu : u ∉ Ideal.span {π}) {j : ℕ} (hj : j < 6)
    (hV : ‖V‖ < 1) (e p k : Fin 2) :
    HasSum (fun i => localTerm π ηp X Y V u j (e, blockBase e p, (k : ℕ), i))
        (baseSum π hlam ηp X Y V u j e p k) ∧
      Summable (fun i => ‖localTerm π ηp X Y V u j (e, blockBase e p, (k : ℕ), i)‖) := by
  fin_cases e <;> fin_cases p <;> fin_cases k
  · simp only [blockBase, baseSum]
    simp only [Fin.zero_eta, Fin.isValue, and_self, ↓reduceIte, Fin.val_zero]
    simp only [localTerm_A0 π hlam h2 hprim ηp X Y V hu hj]
    exact ⟨hasSum_shift_geom _ _ V hV, summable_norm_shift_geom _ _ V hV⟩
  · simp only [blockBase, baseSum]
    simp only [Fin.zero_eta, Fin.isValue, and_self, ↓reduceIte, Fin.mk_one, Fin.val_one,
      one_ne_zero]
    simp only [localTerm_A1 π hlam h2 hprim ηp X Y V hu hj]
    exact ⟨hasSum_point_and 1 _ _, summable_norm_point_and 1 _ _⟩
  · simp only [blockBase, baseSum]
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.val_one, one_ne_zero, and_false,
      ↓reduceIte, Fin.val_zero]
    simp only [localTerm_C0 π hlam h2 hprim ηp X Y V hu]
    exact ⟨hasSum_point_and 0 _ _, summable_norm_point_and 0 _ _⟩
  · simp only [blockBase, baseSum]
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.val_one, one_ne_zero, and_false,
      ↓reduceIte]
    simp only [localTerm_C1 π hlam h2 hprim ηp X Y V hu]
    exact ⟨hasSum_point_and 0 _ _, summable_norm_point_and 0 _ _⟩
  · simp only [blockBase, baseSum]
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, one_ne_zero, false_and, ↓reduceIte,
      Fin.val_zero]
    simp only [localTerm_B0 π hlam h2 hprim ηp X Y V hu]
    exact ⟨hasSum_point_and 0 _ _, summable_norm_point_and 0 _ _⟩
  · simp only [blockBase, baseSum]
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, one_ne_zero, false_and, ↓reduceIte,
      Fin.val_zero, Fin.val_one]
    simp only [localTerm_B1 π hlam h2 hprim ηp X Y V hu]
    by_cases h2j : 2 ≤ j
    · simp only [h2j, or_true, ↓reduceIte]
      refine ⟨(hasSum_geometric_of_norm_lt_one hV).mul_left _, ?_⟩
      simp only [norm_mul, norm_pow]
      exact (summable_geometric_of_lt_one (norm_nonneg _) hV).mul_left _
    · simp only [h2j, or_false, ↓reduceIte]
      have hfun : (fun i : ℕ => if 1 ≤ i then -(ηp * (primeQ π - 1) * X * Y * V ^ i)
          else if j = 1 then ηp * X * Y else 0) = fun i : ℕ => if i = 0 then
            (if j = 1 then ηp * X * Y else 0) else -(ηp * (primeQ π - 1) * X * Y) * V ^ i := by
        funext i
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · simp
        · rw [if_pos hi, if_neg (by omega)]
          ring
      rw [hfun]
      exact ⟨hasSum_geom_from _ _ V hV, summable_norm_geom_from _ _ V hV⟩
  · simp only [blockBase, baseSum]
    simp only [Fin.isValue, Fin.mk_one, one_ne_zero, false_and, ↓reduceIte, Fin.val_one,
      Fin.val_zero]
    simp only [localTerm_D0 π hlam h2 hprim ηp X Y V hu]
    exact ⟨hasSum_point_and 0 _ _, summable_norm_point_and 0 _ _⟩
  · simp only [blockBase, baseSum]
    simp only [Fin.isValue, Fin.mk_one, one_ne_zero, false_and, ↓reduceIte, Fin.val_one]
    simp only [localTerm_D1 π hlam h2 hprim ηp X Y V hu]
    exact ⟨hasSum_point_and 0 _ _, summable_norm_point_and 0 _ _⟩

end Prime

end GaloisForLFunctions.FamilyContinuationTheory
