import GaloisForLFunctions.FamilyContinuationTheory.TheOddPowerOfAGaussSumCarriesTheMoebiusSign

/-!
# The Möbius parity of a Gauss monomial

Multiplying `r ≥ 1` nontrivial finite-field Gauss sums `g(χ₁) ⋯ g(χ_r)` contracts adjacent pairs
through the two elementary Gauss–Jacobi laws:
* `g(α) g(β) = J(α, β) g(α β)` when `α β ≠ 1`, trading one Gauss sum for one nontrivial Jacobi sum;
* `g(α) g(α⁻¹) = α(−1) #F` when `α β = 1`, trading two Gauss sums for one power of `#F` and a sign.

Let `Π = ∏_{i=1}^r χ_i` and put `δ_Π = 0` when `Π = 1` and `δ_Π = 1` when `Π ≠ 1`.

1. **Exact conservation law (`GaussMonomialFactorization`, `gaussMonomialFactorization`):**
   Every nonempty list `L` of nontrivial multiplicative characters on a finite field `F` factors
   `(L.map (gaussSum · ψ)).prod` in `R` as
   `ε · (#F)^P · (∏_{(α, β)} J(α, β)) · (if Π = 1 then 1 else g(Π))`,
   with `ε² = 1`, nontrivial Jacobi pairs `(α, β)`, and exact count conservation
   `r = J_# + 2 P + δ_Π` (`P ≥ 1` when `Π = 1`). When `χ_i^n = 1` (`n > 2`, `n ∣ #F − 1`) and `μ`
   is a primitive `n`-th root of unity, the Jacobi product lies in
   `(−1)^{r − δ_Π} + (μ − 1)² ℤ[μ]` (`exists_gaussMonomial_eq_mod_sub_one_sq`).
2. **Cyclotomic sign non-degeneracy and Hasse–Davenport reduction
   (`not_dvd_two_sub_one_of_odd_prime_pow`, `neg_one_ne_one_mod_sub_one_sq_of_odd_prime_pow`,
   `jacobiSum_quadraticChar_eq`, `gaussSum_mul_inv_mul_quadraticChar_eq`):**
   In any characteristic-zero integral domain `R`, for any odd prime power `p^{k+1}` and primitive
   `p^{k+1}`-th root of unity `μ`, `2` is not a `ℤ[μ]`-multiple of `μ − 1`, so `−1` and `+1` are
   distinct modulo `(μ − 1)²`. For any odd-order character `χ` paired with `χ⁻¹ q` (`q` quadratic,
   `ringChar F ≠ 2`), Hasse–Davenport reduces `g(χ) g(χ⁻¹ q) = χ(4) J(χ, χ) g(q)` directly to the
   odd-order Jacobi sum `J(χ, χ)`.
3. **Quadratic stripping and character-order trichotomy (`IsMoebiusSignedTuple`,
   `mulChar_hasUniqueOrderTwo`, `nonQuadraticPart_isMoebiusSigned`,
   `two_le_length_nonQuadraticPart`, `three_orders_of_prod_eq_one`,
   `quadratic_product_order_trichotomy`):**
   In any commutative group with at most one element of order `2` (in particular `MulChar F R`),
   removing all elements of order `2` preserves `Π² = 1` and the Möbius parity law
   `(Π = 1 ∧ Odd r) ∨ (Π ≠ 1 ∧ Even r)`, forcing at least two elements of order `≥ 3` and fixing
   the exact order trichotomy `(m, 2m)`, `(2m₀, m₀)`, or `(4u, 4u)` when two non-quadratic factors
   have quadratic product.
-/

open scoped BigOperators NumberField

namespace GaloisForLFunctions.FamilyContinuationTheory

section GaussMonomialFactorization

variable {F : Type*} [Field F] [Fintype F] {R : Type*} [CommRing R] [IsDomain R]

/-- Inverse-character Gauss-sum contraction `g(χ) g(χ⁻¹) = χ(−1) #F` over an integral domain. -/
theorem gaussSum_mul_inv_eq_sign_card {χ : MulChar F R} {ψ : AddChar F R}
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum χ⁻¹ ψ = χ (-1) * Fintype.card F := by
  have hneg : (-1 : F)⁻¹ = -1 := by rw [inv_neg, inv_one]
  rw [← mul_gaussSum_inv_eq_gaussSum χ⁻¹, mul_left_comm, gaussSum_mul_gaussSum_eq_card hχ hψ,
    MulChar.inv_apply', hneg]

private theorem list_prod_pow_eq_one {G : Type*} [CommMonoid G] {L : List G} {n : ℕ}
    (h : ∀ x ∈ L, x ^ n = 1) : L.prod ^ n = 1 := by
  induction L with
  | nil => simp
  | cons a tl ih =>
    rw [List.prod_cons, mul_pow, h a List.mem_cons_self, one_mul]
    exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- Exact Jacobi-sum and `#F`-power factorization data for a nonempty product of nontrivial
Gauss sums along `L : List (MulChar F R)`. -/
structure GaussMonomialFactorization [DecidableEq (MulChar F R)]
    (ψ : AddChar F R) (L : List (MulChar F R)) where
  /-- Parity sign accumulated from inverse-pair contractions `g(α) g(α⁻¹) = α(−1) #F`. -/
  sign : R
  /-- Exponent of `#F` accumulated from inverse-pair contractions. -/
  cardPow : ℕ
  /-- Nontrivial Jacobi-sum pairs `(α, β)` accumulated from non-inverse contractions. -/
  jacobiPairs : List (MulChar F R × MulChar F R)
  sign_sq : sign ^ 2 = 1
  sign_eq_one_of_even_chars : (∀ χ ∈ L, χ (-1) = 1) → sign = 1
  jacobiPairs_nontrivial : ∀ p ∈ jacobiPairs, p.1 ≠ 1 ∧ p.2 ≠ 1 ∧ p.1 * p.2 ≠ 1
  jacobiPairs_pow_eq_one :
    ∀ n : ℕ, (∀ χ ∈ L, χ ^ n = 1) → ∀ p ∈ jacobiPairs, p.1 ^ n = 1 ∧ p.2 ^ n = 1
  /-- Exact conservation law `r = J_# + 2 P + δ_Π`. -/
  conservation :
    L.length = jacobiPairs.length + 2 * cardPow + (if L.prod = 1 then 0 else 1)
  /-- Trivial total product requires at least one `#F` contraction. -/
  pos_cardPow_of_prod_eq_one : L.prod = 1 → 1 ≤ cardPow
  /-- Exact algebraic factorization of `∏_{χ ∈ L} g(χ)` in `R`. -/
  prod_eq :
    (L.map fun χ => gaussSum χ ψ).prod =
      sign * (Fintype.card F : R) ^ cardPow *
        (jacobiPairs.map fun p => jacobiSum p.1 p.2).prod *
        (if L.prod = 1 then 1 else gaussSum L.prod ψ)

/-- Constructive Jacobi factorization of any nonempty list of nontrivial Gauss sums. -/
noncomputable def gaussMonomialFactorization [DecidableEq (MulChar F R)]
    {ψ : AddChar F R} (hψ : ψ.IsPrimitive) :
    ∀ {L : List (MulChar F R)}, L ≠ [] → (∀ χ ∈ L, χ ≠ 1) → GaussMonomialFactorization ψ L
  | [], hne, _ => absurd rfl hne
  | [χ], _, hL =>
    have hχ : χ ≠ 1 := hL χ List.mem_cons_self
    have hprod : ([χ] : List (MulChar F R)).prod = χ := by simp
    { sign := 1
      cardPow := 0
      jacobiPairs := []
      sign_sq := one_pow 2
      sign_eq_one_of_even_chars := fun _ => rfl
      jacobiPairs_nontrivial := by simp
      jacobiPairs_pow_eq_one := by simp
      conservation := by simp [hprod, hχ]
      pos_cardPow_of_prod_eq_one := fun h1 => absurd (hprod ▸ h1) hχ
      prod_eq := by simp [hprod, hχ] }
  | χ :: χ' :: tl, _, hL =>
    have hχ : χ ≠ 1 := hL χ List.mem_cons_self
    have htl_ne : χ' :: tl ≠ [] := List.cons_ne_nil χ' tl
    have htl : ∀ φ ∈ χ' :: tl, φ ≠ 1 := fun φ hφ => hL φ (List.mem_cons_of_mem _ hφ)
    let ih := gaussMonomialFactorization hψ htl_ne htl
    if hP : (χ' :: tl).prod = 1 then
      have hcons_prod : (χ :: χ' :: tl).prod = χ := by
        rw [List.prod_cons, hP, mul_one]
      { sign := ih.sign
        cardPow := ih.cardPow
        jacobiPairs := ih.jacobiPairs
        sign_sq := ih.sign_sq
        sign_eq_one_of_even_chars := fun hev =>
          ih.sign_eq_one_of_even_chars fun φ hφ => hev φ (List.mem_cons_of_mem _ hφ)
        jacobiPairs_nontrivial := ih.jacobiPairs_nontrivial
        jacobiPairs_pow_eq_one := fun n hn =>
          ih.jacobiPairs_pow_eq_one n fun φ hφ => hn φ (List.mem_cons_of_mem _ hφ)
        conservation := by
          have hc := ih.conservation
          rw [if_pos hP, add_zero] at hc
          rw [hcons_prod, if_neg hχ]
          simp only [List.length_cons] at hc ⊢
          omega
        pos_cardPow_of_prod_eq_one := fun h1 => absurd (hcons_prod ▸ h1) hχ
        prod_eq := by
          have hp := ih.prod_eq
          rw [if_pos hP, mul_one] at hp
          rw [hcons_prod, if_neg hχ, List.map_cons, List.prod_cons, hp]
          ring }
    else if hmul : χ * (χ' :: tl).prod = 1 then
      have hcons_prod : (χ :: χ' :: tl).prod = 1 := by
        rw [List.prod_cons, hmul]
      have hinv : (χ' :: tl).prod = χ⁻¹ := eq_inv_of_mul_eq_one_right hmul
      { sign := χ (-1) * ih.sign
        cardPow := ih.cardPow + 1
        jacobiPairs := ih.jacobiPairs
        sign_sq := by
          rw [mul_pow, ih.sign_sq, mul_one, ← map_pow, neg_one_sq, map_one]
        sign_eq_one_of_even_chars := fun hev => by
          rw [hev χ List.mem_cons_self, one_mul]
          exact ih.sign_eq_one_of_even_chars fun φ hφ => hev φ (List.mem_cons_of_mem _ hφ)
        jacobiPairs_nontrivial := ih.jacobiPairs_nontrivial
        jacobiPairs_pow_eq_one := fun n hn =>
          ih.jacobiPairs_pow_eq_one n fun φ hφ => hn φ (List.mem_cons_of_mem _ hφ)
        conservation := by
          have hc := ih.conservation
          rw [if_neg hP] at hc
          rw [if_pos hcons_prod]
          simp only [List.length_cons] at hc ⊢
          omega
        pos_cardPow_of_prod_eq_one := fun _ => Nat.le_add_left 1 _
        prod_eq := by
          have hp := ih.prod_eq
          rw [if_neg hP] at hp
          rw [if_pos hcons_prod, mul_one, List.map_cons, List.prod_cons, hp, hinv]
          calc gaussSum χ ψ * (ih.sign * (Fintype.card F : R) ^ ih.cardPow *
                (ih.jacobiPairs.map fun p => jacobiSum p.1 p.2).prod * gaussSum χ⁻¹ ψ)
              = ih.sign * (Fintype.card F : R) ^ ih.cardPow *
                  (ih.jacobiPairs.map fun p => jacobiSum p.1 p.2).prod *
                  (gaussSum χ ψ * gaussSum χ⁻¹ ψ) := by ring
            _ = ih.sign * (Fintype.card F : R) ^ ih.cardPow *
                  (ih.jacobiPairs.map fun p => jacobiSum p.1 p.2).prod *
                  (χ (-1) * Fintype.card F) := by rw [gaussSum_mul_inv_eq_sign_card hχ hψ]
            _ = χ (-1) * ih.sign * (Fintype.card F : R) ^ (ih.cardPow + 1) *
                  (ih.jacobiPairs.map fun p => jacobiSum p.1 p.2).prod := by
                rw [pow_succ]; ring }
    else
      have hcons_prod : (χ :: χ' :: tl).prod = χ * (χ' :: tl).prod := List.prod_cons
      { sign := ih.sign
        cardPow := ih.cardPow
        jacobiPairs := (χ, (χ' :: tl).prod) :: ih.jacobiPairs
        sign_sq := ih.sign_sq
        sign_eq_one_of_even_chars := fun hev =>
          ih.sign_eq_one_of_even_chars fun φ hφ => hev φ (List.mem_cons_of_mem _ hφ)
        jacobiPairs_nontrivial := fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hmem
          · exact ⟨hχ, hP, hmul⟩
          · exact ih.jacobiPairs_nontrivial p hmem
        jacobiPairs_pow_eq_one := fun n hn p hp => by
          rcases List.mem_cons.mp hp with rfl | hmem
          · exact ⟨hn χ List.mem_cons_self,
              list_prod_pow_eq_one fun φ hφ => hn φ (List.mem_cons_of_mem _ hφ)⟩
          · exact ih.jacobiPairs_pow_eq_one n (fun φ hφ => hn φ (List.mem_cons_of_mem _ hφ)) p hmem
        conservation := by
          have hc := ih.conservation
          rw [if_neg hP] at hc
          rw [hcons_prod, if_neg hmul]
          simp only [List.length_cons] at hc ⊢
          omega
        pos_cardPow_of_prod_eq_one := fun h1 => absurd (hcons_prod ▸ h1) hmul
        prod_eq := by
          have hp := ih.prod_eq
          rw [if_neg hP] at hp
          rw [hcons_prod, if_neg hmul, List.map_cons, List.prod_cons, hp]
          simp only [List.map_cons, List.prod_cons]
          calc gaussSum χ ψ * (ih.sign * (Fintype.card F : R) ^ ih.cardPow *
                (ih.jacobiPairs.map fun p => jacobiSum p.1 p.2).prod *
                gaussSum (χ' :: tl).prod ψ)
              = ih.sign * (Fintype.card F : R) ^ ih.cardPow *
                  (ih.jacobiPairs.map fun p => jacobiSum p.1 p.2).prod *
                  (gaussSum χ ψ * gaussSum (χ' :: tl).prod ψ) := by ring
            _ = ih.sign * (Fintype.card F : R) ^ ih.cardPow *
                  (ih.jacobiPairs.map fun p => jacobiSum p.1 p.2).prod *
                  (gaussSum (χ * (χ' :: tl).prod) ψ * jacobiSum χ (χ' :: tl).prod) := by
                rw [jacobiSum_mul_nontrivial hmul ψ]
            _ = ih.sign * (Fintype.card F : R) ^ ih.cardPow *
                  (jacobiSum χ (χ' :: tl).prod *
                    (ih.jacobiPairs.map fun p => jacobiSum p.1 p.2).prod) *
                  gaussSum (χ * (χ' :: tl).prod) ψ := by ring }

omit [IsDomain R] in
private theorem exists_list_prod_eq_neg_one_pow_add {α : Type*} (A : Subalgebra ℤ R)
    {π : R} (hπ : π ∈ A) (L : List α) (f : α → R)
    (hf : ∀ a ∈ L, ∃ z ∈ A, f a = -1 + z * π ^ 2) :
    ∃ z ∈ A, (L.map f).prod = (-1) ^ L.length + z * π ^ 2 := by
  induction L with
  | nil => exact ⟨0, A.zero_mem, by simp⟩
  | cons a tl ih =>
    obtain ⟨z₁, hz₁, h₁⟩ := hf a List.mem_cons_self
    obtain ⟨z₂, hz₂, h₂⟩ := ih fun b hb => hf b (List.mem_cons_of_mem _ hb)
    refine ⟨-z₂ + z₁ * (-1) ^ tl.length + z₁ * z₂ * π ^ 2, ?_, ?_⟩
    · exact A.add_mem (A.add_mem (A.neg_mem hz₂)
        (A.mul_mem hz₁ (A.pow_mem (A.neg_mem A.one_mem) _)))
        (A.mul_mem (A.mul_mem hz₁ hz₂) (A.pow_mem hπ 2))
    · simp only [List.map_cons, List.prod_cons, List.length_cons, h₁, h₂]
      ring

/-- **Modulo-`(μ − 1)²` evaluation of a general Gauss monomial.** If `χ^n = 1` (`n > 2`,
`n ∣ #F − 1`) for every `χ ∈ L` and `μ` is a primitive `n`-th root of unity in an integral domain
`R`, the Jacobi-sum product in `fact` evaluates to `(−1)^{r − δ_Π}` modulo `(μ − 1)²` in `ℤ[μ]`,
provided `fact.sign ∈ ℤ[μ]` (for example `fact.sign = ±1`). -/
theorem exists_gaussMonomial_eq_mod_sub_one_sq [DecidableEq (MulChar F R)]
    {n : ℕ} (hn : 2 < n) (hn' : n ∣ Fintype.card F - 1) {μ : R} (hμ : IsPrimitiveRoot μ n)
    {ψ : AddChar F R} {L : List (MulChar F R)} (fact : GaussMonomialFactorization ψ L)
    (hLn : ∀ χ ∈ L, χ ^ n = 1) :
    ∃ z ∈ Algebra.adjoin ℤ ({μ} : Set R),
      (L.map fun χ => gaussSum χ ψ).prod =
        fact.sign * ((-1) ^ (L.length - if L.prod = 1 then 0 else 1) + z * (μ - 1) ^ 2) *
          (Fintype.card F : R) ^ fact.cardPow *
          (if L.prod = 1 then 1 else gaussSum L.prod ψ) := by
  have hπ : μ - 1 ∈ Algebra.adjoin ℤ ({μ} : Set R) :=
    Subalgebra.sub_mem _ (Algebra.self_mem_adjoin_singleton ℤ μ) (Subalgebra.one_mem _)
  obtain ⟨z, hz, hJ⟩ := exists_list_prod_eq_neg_one_pow_add (Algebra.adjoin ℤ ({μ} : Set R)) hπ
    fact.jacobiPairs (fun p => jacobiSum p.1 p.2) fun p hp => by
      obtain ⟨h1, h2⟩ := fact.jacobiPairs_pow_eq_one n hLn p hp
      exact exists_jacobiSum_eq_neg_one_add hn h1 h2 hn' hμ
  have hpow : ((-1 : R) ^ fact.jacobiPairs.length) =
      (-1 : R) ^ (L.length - if L.prod = 1 then 0 else 1) := by
    have hexp : L.length - (if L.prod = 1 then 0 else 1) =
        fact.jacobiPairs.length + 2 * fact.cardPow := by
      have hc := fact.conservation
      omega
    rw [hexp, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  refine ⟨z, hz, ?_⟩
  rw [fact.prod_eq, hJ, hpow]
  ring

omit [IsDomain R] in
/-- Exact parity equivalence: the number of nontrivial Jacobi factors in `fact` is odd if and only
if `(L.prod = 1 ∧ Odd L.length) ∨ (L.prod ≠ 1 ∧ Even L.length)`. -/
theorem odd_jacobiPairs_length_iff [DecidableEq (MulChar F R)]
    {ψ : AddChar F R} {L : List (MulChar F R)} (fact : GaussMonomialFactorization ψ L) :
    Odd fact.jacobiPairs.length ↔
      (L.prod = 1 ∧ Odd L.length) ∨ (L.prod ≠ 1 ∧ Even L.length) := by
  have hc := fact.conservation
  by_cases hP : L.prod = 1
  · simp only [hP, ↓reduceIte, add_zero, true_and, ne_eq, not_true_eq_false, false_and,
      or_false] at hc ⊢
    rw [hc]
    constructor
    · rintro ⟨m, hm⟩; exact ⟨m + fact.cardPow, by omega⟩
    · rintro ⟨m, hm⟩; exact ⟨m - fact.cardPow, by omega⟩
  · simp only [hP, ↓reduceIte, false_and, ne_eq, not_false_eq_true, true_and,
      false_or] at hc ⊢
    rw [hc]
    constructor
    · rintro ⟨m, hm⟩; exact ⟨m + fact.cardPow + 1, by omega⟩
    · rintro ⟨m, hm⟩; exact ⟨m - fact.cardPow - 1, by omega⟩

end GaussMonomialFactorization

/-! ### Cyclotomic non-degeneracy of the Stickelberger congruence sign and Hasse–Davenport -/

section NonDegeneracyAndHasseDavenport

/-- In any characteristic-zero integral domain `R`, if `μ` is a primitive `p^{k+1}`-th root of
unity for an odd prime `p`, then `2` is not a `ℤ[μ]`-multiple of `μ − 1`. -/
theorem not_dvd_two_sub_one_of_odd_prime_pow {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {p k : ℕ} [hp : Fact p.Prime] (hodd : p ≠ 2) {μ : R}
    (hμ : IsPrimitiveRoot μ (p ^ (k + 1))) :
    ¬ ∃ z ∈ Algebra.adjoin ℤ ({μ} : Set R), (2 : R) = z * (μ - 1) := by
  haveI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hinj : Function.Injective (algebraMap R (FractionRing R)) :=
    IsFractionRing.injective R (FractionRing R)
  have hζ : IsPrimitiveRoot (algebraMap R (FractionRing R) μ) (p ^ (k + 1)) :=
    hμ.map_of_injective hinj
  have halg : IsAlgebraic ℚ (algebraMap R (FractionRing R) μ) :=
    ⟨Polynomial.X ^ (p ^ (k + 1)) - 1,
      (Polynomial.monic_X_pow_sub_C (1 : ℚ) (NeZero.ne _)).ne_zero,
      by simp [hζ.pow_eq_one]⟩
  haveI : IsCyclotomicExtension {p ^ (k + 1)} ℚ
      (IntermediateField.adjoin ℚ ({algebraMap R (FractionRing R) μ} : Set (FractionRing R))) := by
    change IsCyclotomicExtension {p ^ (k + 1)} ℚ
      (IntermediateField.adjoin ℚ
        ({algebraMap R (FractionRing R) μ} : Set (FractionRing R))).toSubalgebra
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
    exact hζ.adjoin_isCyclotomicExtension ℚ
  have hμ₀ : IsPrimitiveRoot
      (IntermediateField.AdjoinSimple.gen ℚ (algebraMap R (FractionRing R) μ)) (p ^ (k + 1)) :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ
  have hz_int : ∀ z ∈ Algebra.adjoin ℤ ({μ} : Set R),
      ∃ w : 𝓞 (IntermediateField.adjoin ℚ
          ({algebraMap R (FractionRing R) μ} : Set (FractionRing R))),
        ((w : IntermediateField.adjoin ℚ
          ({algebraMap R (FractionRing R) μ} : Set (FractionRing R))) :
          FractionRing R) = algebraMap R (FractionRing R) z := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨hμ₀.toInteger, rfl⟩
    | algebraMap r =>
      exact ⟨(r : 𝓞 _), by simp⟩
    | add x y _ _ ihx ihy =>
      rcases ihx with ⟨wx, hwx⟩
      rcases ihy with ⟨wy, hwy⟩
      exact ⟨wx + wy, by push_cast; rw [hwx, hwy]⟩
    | mul x y _ _ ihx ihy =>
      rcases ihx with ⟨wx, hwx⟩
      rcases ihy with ⟨wy, hwy⟩
      exact ⟨wx * wy, by push_cast; rw [hwx, hwy]⟩
  rintro ⟨z, hz, h2⟩
  rcases hz_int z hz with ⟨w, hw⟩
  have hdvd : hμ₀.toInteger - 1 ∣ (2 : 𝓞 _) := by
    refine ⟨w, ?_⟩
    ext
    have hmap := congr_arg (algebraMap R (FractionRing R)) h2
    simp only [map_ofNat, map_mul, map_sub, map_one] at hmap
    push_cast
    change (2 : FractionRing R) =
      (algebraMap R (FractionRing R) μ - 1) *
        ((w : IntermediateField.adjoin ℚ
          ({algebraMap R (FractionRing R) μ} : Set (FractionRing R))) :
          FractionRing R)
    rw [hw, hmap, mul_comm]
  exact hμ₀.toInteger_sub_one_not_dvd_two hodd hdvd

/-- **Non-degeneracy of the Stickelberger sign for odd prime powers.** For any odd prime `p`,
`k : ℕ`, and primitive `p^{k+1}`-th root of unity `μ` in a characteristic-zero integral domain `R`,
the residue classes `−1 + z₁ (μ − 1)²` and `+1 + z₂ (μ − 1)²` (`z₁, z₂ ∈ ℤ[μ]`) never coincide. -/
theorem neg_one_ne_one_mod_sub_one_sq_of_odd_prime_pow
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {p k : ℕ} [Fact p.Prime] (hodd : p ≠ 2) {μ : R}
    (hμ : IsPrimitiveRoot μ (p ^ (k + 1)))
    {z₁ z₂ : R} (hz₁ : z₁ ∈ Algebra.adjoin ℤ ({μ} : Set R))
    (hz₂ : z₂ ∈ Algebra.adjoin ℤ ({μ} : Set R)) :
    (-1 : R) + z₁ * (μ - 1) ^ 2 ≠ 1 + z₂ * (μ - 1) ^ 2 := by
  intro heq
  apply not_dvd_two_sub_one_of_odd_prime_pow hodd hμ
  have hπ : μ - 1 ∈ Algebra.adjoin ℤ ({μ} : Set R) :=
    Subalgebra.sub_mem _ (Algebra.self_mem_adjoin_singleton ℤ μ) (Subalgebra.one_mem _)
  refine ⟨(z₁ - z₂) * (μ - 1),
    Subalgebra.mul_mem _ (Subalgebra.sub_mem _ hz₁ hz₂) hπ, ?_⟩
  linear_combination -heq

/-- Quadratic Jacobi identity `J(χ, q) = χ(4) J(χ, χ)` for any nontrivial multiplicative character
`χ` on a finite field `F` of odd characteristic. -/
theorem jacobiSum_quadraticChar_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hchar : ringChar F ≠ 2) {χ : MulChar F ℂ} (hχ : χ ≠ 1) :
    jacobiSum χ ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) =
      χ (4 : F) * jacobiSum χ χ := by
  let q : MulChar F ℂ := (quadraticChar F).ringHomComp (Int.castRingHom ℂ)
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
  let oneSub : F ≃ F :=
    { toFun := fun y => 1 - y, invFun := fun y => 1 - y,
      left_inv := fun y => by ring, right_inv := fun y => by ring }
  let affineDouble : F ≃ F :=
    { toFun := fun x => 2 * x - 1, invFun := fun t => (t + 1) / 2,
      left_inv := fun x => by field_simp; ring,
      right_inv := fun t => by field_simp; ring }
  have hsum0 : (∑ y : F, χ (1 - y)) = 0 :=
    (Equiv.sum_comp oneSub χ).trans (MulChar.sum_eq_zero_of_ne_one hχ)
  have hfiber : (∑ t : F, χ (1 - t ^ 2)) =
      ∑ y : F, ((quadraticChar F y : ℂ) + 1) * χ (1 - y) := by
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun t : F => t ^ 2)
      (f := fun t : F => χ (1 - t ^ 2))]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_congr rfl fun t ht => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht; rw [ht]]
    simp only [Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hcard := quadraticChar_card_sqrts hchar y
    rw [Set.toFinset_setOf] at hcard
    exact_mod_cast hcard
  have hsq : (∑ t : F, χ (1 - t ^ 2)) = jacobiSum χ q := by
    rw [hfiber]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    simp only [one_mul, hsum0, add_zero]
    exact jacobiSum_comm q χ
  have hchange : (∑ t : F, χ (1 - t ^ 2)) = ∑ x : F, χ (4 * x * (1 - x)) := by
    refine (Equiv.sum_comp affineDouble (fun t : F => χ (1 - t ^ 2))).symm.trans ?_
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    change 1 - (2 * x - 1) ^ 2 = 4 * x * (1 - x)
    ring
  calc jacobiSum χ q = ∑ x : F, χ (4 * x * (1 - x)) := hsq.symm.trans hchange
    _ = χ (4 : F) * jacobiSum χ χ := by
      rw [jacobiSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [map_mul]
      ring

/-- **Universal Hasse–Davenport reduction for `(m, 2m)` quadratic-product pairs.** For any
nontrivial odd-order character `χ` (`Odd m`, `χ^m = 1`, `χ ≠ 1`) on a finite field `F` of odd
characteristic and `q` the quadratic character, the Gauss-sum pairing `g(χ) g(χ⁻¹ q)` reduces
directly to the odd-order Jacobi sum `J(χ, χ)`:
`g(χ) g(χ⁻¹ q) = χ(4) J(χ, χ) g(q)`. -/
theorem gaussSum_mul_inv_mul_quadraticChar_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hchar : ringChar F ≠ 2) {m : ℕ} (hm : Odd m) {χ : MulChar F ℂ}
    (hχ1 : χ ≠ 1) (hχm : χ ^ m = 1) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum (χ⁻¹ * (quadraticChar F).ringHomComp (Int.castRingHom ℂ)) ψ =
      χ (4 : F) * jacobiSum χ χ *
        gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) ψ := by
  let q : MulChar F ℂ := (quadraticChar F).ringHomComp (Int.castRingHom ℂ)
  have hq2 : q ^ 2 = 1 := (quadraticChar_isQuadratic F).comp _ |>.sq_eq_one
  have hq1 : q ≠ 1 := by
    have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
    exact (MulChar.ringHomComp_ne_one_iff hinj).mpr (quadraticChar_ne_one hchar)
  have hχinv1 : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ1
  have hχinvm : χ⁻¹ ^ m = 1 := by rw [inv_pow, hχm, inv_one]
  have hχsq1 : χ * χ ≠ 1 := by
    intro hsq
    rw [← pow_two] at hsq
    obtain ⟨u, rfl⟩ := hm
    have hpow : χ ^ (2 * u + 1) = χ := by
      rw [pow_add, pow_mul, hsq, one_pow, one_mul, pow_one]
    exact hχ1 (hpow.symm.trans hχm)
  have hprod_ne : χ⁻¹ * q ≠ 1 := by
    intro h1
    have hqm : q ^ m = 1 := by
      have hpm : (χ⁻¹ * q) ^ m = 1 := by rw [h1, one_pow]
      rwa [mul_pow, hχinvm, one_mul] at hpm
    obtain ⟨u, rfl⟩ := hm
    have hqp : q ^ (2 * u + 1) = q := by
      rw [pow_add, pow_mul, hq2, one_pow, one_mul, pow_one]
    exact hq1 (hqp.symm.trans hqm)
  have hhd : gaussSum (χ⁻¹ * q) ψ * (χ⁻¹ (4 : F) * jacobiSum χ⁻¹ χ⁻¹) =
      gaussSum χ⁻¹ ψ * gaussSum q ψ := by
    rw [← jacobiSum_quadraticChar_eq hchar hχinv1]
    exact jacobiSum_mul_nontrivial hprod_ne ψ
  have hcharC : ringChar ℂ ≠ ringChar F := by
    have hc0 : ringChar ℂ = 0 :=
      Nat.cast_eq_zero.mp (ringChar.Nat.cast_ringChar (R := ℂ))
    rw [hc0]
    exact (CharP.char_is_prime F (ringChar F)).ne_zero.symm
  have hJJ : jacobiSum χ χ * jacobiSum χ⁻¹ χ⁻¹ = Fintype.card F :=
    jacobiSum_mul_jacobiSum_inv hcharC hχ1 hχ1 hχsq1
  have h4unit : IsUnit (4 : F) := by
    rw [show (4 : F) = 2 * 2 by ring]
    exact (Ring.two_ne_zero hchar).isUnit.mul (Ring.two_ne_zero hchar).isUnit
  have h4inv : χ⁻¹ (4 : F) * χ (4 : F) = 1 := by
    rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply h4unit]
  have hcard_ne : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hfactor_ne : χ⁻¹ (4 : F) * jacobiSum χ⁻¹ χ⁻¹ ≠ 0 := by
    intro hz
    have h0 : (χ⁻¹ (4 : F) * jacobiSum χ⁻¹ χ⁻¹) * (χ (4 : F) * jacobiSum χ χ) = 0 := by
      rw [hz, zero_mul]
    have heq : (χ⁻¹ (4 : F) * jacobiSum χ⁻¹ χ⁻¹) * (χ (4 : F) * jacobiSum χ χ) =
        Fintype.card F := by
      calc (χ⁻¹ (4 : F) * jacobiSum χ⁻¹ χ⁻¹) * (χ (4 : F) * jacobiSum χ χ)
          = (χ⁻¹ (4 : F) * χ (4 : F)) * (jacobiSum χ χ * jacobiSum χ⁻¹ χ⁻¹) := by ring
        _ = Fintype.card F := by rw [h4inv, one_mul, hJJ]
    exact hcard_ne (heq.symm.trans h0)
  apply mul_left_cancel₀ hfactor_ne
  have hneg1 : χ (-1) = 1 := MulChar.val_neg_one_eq_one_of_odd_order hm hχm
  calc (χ⁻¹ (4 : F) * jacobiSum χ⁻¹ χ⁻¹) * (gaussSum χ ψ * gaussSum (χ⁻¹ * q) ψ)
      = gaussSum χ ψ * (gaussSum (χ⁻¹ * q) ψ * (χ⁻¹ (4 : F) * jacobiSum χ⁻¹ χ⁻¹)) := by ring
    _ = (gaussSum χ ψ * gaussSum χ⁻¹ ψ) * gaussSum q ψ := by rw [hhd, mul_assoc]
    _ = (Fintype.card F : ℂ) * gaussSum q ψ := by
        rw [gaussSum_mul_inv_eq_sign_card hχ1 hψ, hneg1, one_mul]
    _ = (χ⁻¹ (4 : F) * χ (4 : F)) * (jacobiSum χ χ * jacobiSum χ⁻¹ χ⁻¹) * gaussSum q ψ := by
        rw [h4inv, one_mul, hJJ]
    _ = (χ⁻¹ (4 : F) * jacobiSum χ⁻¹ χ⁻¹) * (χ (4 : F) * jacobiSum χ χ * gaussSum q ψ) := by
        ring

end NonDegeneracyAndHasseDavenport

/-! ### Quadratic stripping and character-order trichotomy -/

section CharacterOrderClassification

/-- Group property that at most one element has order `2` (satisfied by every finite cyclic group
and by `MulChar F R` over any finite field `F` and integral domain `R`). -/
def HasUniqueOrderTwo (G : Type*) [Group G] : Prop :=
  ∀ ⦃x y : G⦄, orderOf x = 2 → orderOf y = 2 → x = y

/-- Over any finite field `F` and integral domain `R`, `MulChar F R` has at most one character of
order `2`. -/
theorem mulChar_hasUniqueOrderTwo (F : Type*) [Field F] [Fintype F]
    (R : Type*) [CommRing R] [IsDomain R] :
    HasUniqueOrderTwo (MulChar F R) := by
  intro χ₁ χ₂ h₁ h₂
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hval : ∀ χ : MulChar F R, orderOf χ = 2 → χ (g : F) = -1 := by
    intro χ hχ
    have hsq : χ (g : F) ^ 2 = 1 := by
      rw [← χ.pow_apply' two_ne_zero, ← hχ, pow_orderOf_eq_one, MulChar.one_apply g.isUnit]
    rcases sq_eq_one_iff.mp hsq with h1 | hm1
    · exfalso
      have htriv : χ = 1 := by
        ext x
        obtain ⟨n, rfl⟩ := hg x
        rw [MulChar.one_apply (g ^ n).isUnit]
        have hg1 : χ.toUnitHom g = 1 := Units.ext h1
        have hgn : χ.toUnitHom (g ^ n) = 1 := by rw [map_zpow, hg1, one_zpow]
        exact congr_arg Units.val hgn
      rw [htriv, orderOf_one] at hχ
      omega
    · exact hm1
  ext x
  obtain ⟨n, rfl⟩ := hg x
  have h₁₂ : χ₁.toUnitHom g = χ₂.toUnitHom g :=
    Units.ext ((hval χ₁ h₁).trans (hval χ₂ h₂).symm)
  have hgn : χ₁.toUnitHom (g ^ n) = χ₂.toUnitHom (g ^ n) := by rw [map_zpow, map_zpow, h₁₂]
  exact congr_arg Units.val hgn

/-- Every nontrivial multiplicative character on a finite field has finite order `≥ 2`. -/
theorem MulChar.two_le_orderOf_iff_ne_one {F : Type*} [Field F] [Fintype F]
    {R : Type*} [CommRing R] {χ : MulChar F R} :
    2 ≤ orderOf χ ↔ χ ≠ 1 := by
  have hpos : 0 < orderOf χ := χ.orderOf_pos
  constructor
  · intro h2 h1
    rw [h1, orderOf_one] at h2
    omega
  · intro hne
    have hne1 : orderOf χ ≠ 1 := mt orderOf_eq_one_iff.mp hne
    omega

/-- Predicate that a tuple `L` of finite-order group elements eliminates higher-order Gauss factors
(`L.prod² = 1`) and carries an odd number of nontrivial Jacobi factors. -/
structure IsMoebiusSignedTuple {G : Type*} [CommGroup G] (L : List G) : Prop where
  nonempty : L ≠ []
  two_le_order : ∀ x ∈ L, 2 ≤ orderOf x
  prod_sq_eq_one : L.prod ^ 2 = 1
  parity : (L.prod = 1 ∧ Odd L.length) ∨ (L.prod ≠ 1 ∧ Even L.length)

/-- Equivalence between `IsMoebiusSignedTuple L` on `MulChar F R` and `L.prod² = 1` with an odd
number of Jacobi factors in `GaussMonomialFactorization`. -/
theorem isMoebiusSignedTuple_iff_gaussFactorization
    {F : Type*} [Field F] [Fintype F] {R : Type*} [CommRing R] [DecidableEq (MulChar F R)]
    {ψ : AddChar F R} {L : List (MulChar F R)} (hL_ne : L ≠ []) (hL : ∀ χ ∈ L, χ ≠ 1)
    (fact : GaussMonomialFactorization ψ L) :
    IsMoebiusSignedTuple L ↔ L.prod ^ 2 = 1 ∧ Odd fact.jacobiPairs.length := by
  rw [odd_jacobiPairs_length_iff fact]
  constructor
  · intro h; exact ⟨h.prod_sq_eq_one, h.parity⟩
  · rintro ⟨hsq, hpar⟩
    exact ⟨hL_ne, fun χ hχ => MulChar.two_le_orderOf_iff_ne_one.mpr (hL χ hχ), hsq, hpar⟩

/-- Sublist of elements of `L` having order at least `3` (stripping quadratic elements). -/
noncomputable def nonQuadraticPart {G : Type*} [Group G] (L : List G) : List G :=
  L.filter fun x => decide (3 ≤ orderOf x)

private theorem orderOf_eq_two_of_sq_eq_one_ne_one {G : Type*} [Group G] {x : G}
    (hsq : x ^ 2 = 1) (hne : x ≠ 1) : orderOf x = 2 :=
  orderOf_eq_prime hsq hne

private theorem odd_add_one_iff_even (m : ℕ) : Odd (m + 1) ↔ Even m :=
  ⟨fun ⟨k, hk⟩ => ⟨k, by omega⟩, fun ⟨k, hk⟩ => ⟨k, by omega⟩⟩

private theorem even_add_one_iff_odd (m : ℕ) : Even (m + 1) ↔ Odd m :=
  ⟨fun ⟨k, hk⟩ => ⟨k - 1, by omega⟩, fun ⟨k, hk⟩ => ⟨k + 1, by omega⟩⟩

private theorem nonQuadraticPart_rel {G : Type*} [CommGroup G] (hG : HasUniqueOrderTwo G)
    {L : List G} (hL : ∀ x ∈ L, 2 ≤ orderOf x) :
    (L.prod = (nonQuadraticPart L).prod ∧
      (Odd L.length ↔ Odd (nonQuadraticPart L).length) ∧
      (Even L.length ↔ Even (nonQuadraticPart L).length)) ∨
    (∃ q : G, orderOf q = 2 ∧ L.prod = q * (nonQuadraticPart L).prod ∧
      (Odd L.length ↔ Even (nonQuadraticPart L).length) ∧
      (Even L.length ↔ Odd (nonQuadraticPart L).length)) := by
  induction L with
  | nil =>
    left
    simp [nonQuadraticPart]
  | cons x tl ih =>
    have hx2 : 2 ≤ orderOf x := hL x List.mem_cons_self
    have htl : ∀ y ∈ tl, 2 ≤ orderOf y := fun y hy => hL y (List.mem_cons_of_mem _ hy)
    by_cases hx3 : 3 ≤ orderOf x
    · have hfilt : nonQuadraticPart (x :: tl) = x :: nonQuadraticPart tl := by
        simp [nonQuadraticPart, hx3]
      rcases ih htl with ⟨hp, ho, he⟩ | ⟨q, hq2, hp, ho, he⟩
      · left
        rw [hfilt, List.prod_cons, List.prod_cons, hp]
        refine ⟨rfl, ?_, ?_⟩
        · rw [List.length_cons, List.length_cons, odd_add_one_iff_even, odd_add_one_iff_even]
          exact he
        · rw [List.length_cons, List.length_cons, even_add_one_iff_odd, even_add_one_iff_odd]
          exact ho
      · right
        refine ⟨q, hq2, ?_, ?_, ?_⟩
        · rw [hfilt, List.prod_cons, List.prod_cons, hp, mul_left_comm]
        · rw [hfilt, List.length_cons, List.length_cons, odd_add_one_iff_even,
            even_add_one_iff_odd]
          exact he
        · rw [hfilt, List.length_cons, List.length_cons, even_add_one_iff_odd,
            odd_add_one_iff_even]
          exact ho
    · have hx_eq2 : orderOf x = 2 := by omega
      have hfilt : nonQuadraticPart (x :: tl) = nonQuadraticPart tl := by
        simp [nonQuadraticPart, hx3]
      rcases ih htl with ⟨hp, ho, he⟩ | ⟨q, hq2, hp, ho, he⟩
      · right
        refine ⟨x, hx_eq2, ?_, ?_, ?_⟩
        · rw [hfilt, List.prod_cons, hp]
        · simp only [hfilt, List.length_cons, odd_add_one_iff_even, he]
        · simp only [hfilt, List.length_cons, even_add_one_iff_odd, ho]
      · left
        have hxq : x = q := hG hx_eq2 hq2
        have hxsq : x ^ 2 = 1 := hx_eq2 ▸ pow_orderOf_eq_one x
        refine ⟨?_, ?_, ?_⟩
        · rw [hfilt, List.prod_cons, hp, ← hxq, ← mul_assoc, ← sq, hxsq, one_mul]
        · simp only [hfilt, List.length_cons, odd_add_one_iff_even, he]
        · simp only [hfilt, List.length_cons, even_add_one_iff_odd, ho]

/-- **Quadratic stripping preserves Möbius parity.** Removing all order-`2` elements from a
Möbius-signed tuple `L` yields `S = nonQuadraticPart L` satisfying `S.prod² = 1` and the identical
Möbius parity disjunction `(S.prod = 1 ∧ Odd S.length) ∨ (S.prod ≠ 1 ∧ Even S.length)`. -/
theorem nonQuadraticPart_moebius_parity {G : Type*} [CommGroup G] (hG : HasUniqueOrderTwo G)
    {L : List G} (hL : IsMoebiusSignedTuple L) :
    (nonQuadraticPart L).prod ^ 2 = 1 ∧
      (((nonQuadraticPart L).prod = 1 ∧ Odd (nonQuadraticPart L).length) ∨
        ((nonQuadraticPart L).prod ≠ 1 ∧ Even (nonQuadraticPart L).length)) := by
  rcases nonQuadraticPart_rel hG hL.two_le_order with ⟨hp, ho, he⟩ | ⟨q, hq2, hp, ho, he⟩
  · refine ⟨hp ▸ hL.prod_sq_eq_one, ?_⟩
    rcases hL.parity with ⟨h1, hodd⟩ | ⟨hne, hev⟩
    · exact Or.inl ⟨hp ▸ h1, ho.mp hodd⟩
    · exact Or.inr ⟨hp ▸ hne, he.mp hev⟩
  · have hqsq : q ^ 2 = 1 := hq2 ▸ pow_orderOf_eq_one q
    have hqne : q ≠ 1 := by
      intro h1; rw [h1, orderOf_one] at hq2; omega
    have hSsq : (nonQuadraticPart L).prod ^ 2 = 1 := by
      have hsq := hL.prod_sq_eq_one
      rwa [hp, mul_pow, hqsq, one_mul] at hsq
    refine ⟨hSsq, ?_⟩
    rcases hL.parity with ⟨h1, hodd⟩ | ⟨hne, hev⟩
    · right
      refine ⟨?_, ho.mp hodd⟩
      intro hS1
      rw [hp, hS1, mul_one] at h1
      exact hqne h1
    · left
      refine ⟨?_, he.mp hev⟩
      by_contra hSne
      have hS2 : orderOf (nonQuadraticPart L).prod = 2 :=
        orderOf_eq_two_of_sq_eq_one_ne_one hSsq hSne
      have hqS : q = (nonQuadraticPart L).prod := hG hq2 hS2
      apply hne
      rw [hp, ← hqS, ← sq, hqsq]

/-- **Every Möbius-signed tuple has at least two elements of order `≥ 3`.** Neither a purely
quadratic tuple (`#S = 0`) nor a tuple with a single higher-order character (`#S = 1`) can satisfy
Möbius parity. -/
theorem two_le_length_nonQuadraticPart {G : Type*} [CommGroup G] (hG : HasUniqueOrderTwo G)
    {L : List G} (hL : IsMoebiusSignedTuple L) :
    2 ≤ (nonQuadraticPart L).length := by
  obtain ⟨hSsq, hSpar⟩ := nonQuadraticPart_moebius_parity hG hL
  match hS_eq : nonQuadraticPart L with
  | [] =>
    rw [hS_eq] at hSpar
    simp at hSpar
  | [x] =>
    have hx_mem : x ∈ nonQuadraticPart L := by rw [hS_eq]; exact List.mem_cons_self
    have hx3 : 3 ≤ orderOf x := by
      simp only [nonQuadraticPart, List.mem_filter, decide_eq_true_eq] at hx_mem
      exact hx_mem.2
    rw [hS_eq, List.prod_singleton] at hSsq
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hSsq
    have hle2 : orderOf x ≤ 2 := Nat.le_of_dvd (by decide) hdvd
    omega
  | _ :: _ :: _ =>
    simp

/-- Every element of `nonQuadraticPart L` has order at least `3`. -/
theorem three_le_orderOf_mem_nonQuadraticPart {G : Type*} [Group G] {L : List G} {x : G}
    (hx : x ∈ nonQuadraticPart L) : 3 ≤ orderOf x := by
  simp only [nonQuadraticPart, List.mem_filter, decide_eq_true_eq] at hx
  exact hx.2

/-- If three elements of order `≥ 3` multiply to `1`, then either all three have order `3`, or at
least two of them have order `≥ 4`. -/
theorem three_orders_of_prod_eq_one {G : Type*} [CommGroup G] {x₁ x₂ x₃ : G}
    (h₁ : 3 ≤ orderOf x₁) (h₂ : 3 ≤ orderOf x₂) (h₃ : 3 ≤ orderOf x₃)
    (hprod : x₁ * x₂ * x₃ = 1) :
    (orderOf x₁ = 3 ∧ orderOf x₂ = 3 ∧ orderOf x₃ = 3) ∨
      (4 ≤ orderOf x₁ ∧ 4 ≤ orderOf x₂) ∨
      (4 ≤ orderOf x₁ ∧ 4 ≤ orderOf x₃) ∨
      (4 ≤ orderOf x₂ ∧ 4 ≤ orderOf x₃) := by
  have helper : ∀ {a b c : G}, a * b * c = 1 → orderOf a = 3 → orderOf b = 3 → 3 ≤ orderOf c →
      orderOf c = 3 := by
    intro a b c habc ha hb hc3
    have ha3 : a ^ 3 = 1 := ha ▸ pow_orderOf_eq_one a
    have hb3 : b ^ 3 = 1 := hb ▸ pow_orderOf_eq_one b
    have hc_pow : c ^ 3 = 1 := by
      have hp : (a * b * c) ^ 3 = 1 := by rw [habc, one_pow]
      rwa [mul_pow, mul_pow, ha3, hb3, one_mul, one_mul] at hp
    have hle : orderOf c ≤ 3 := Nat.le_of_dvd (by decide) (orderOf_dvd_of_pow_eq_one hc_pow)
    omega
  by_cases e₁ : orderOf x₁ = 3 <;> by_cases e₂ : orderOf x₂ = 3 <;> by_cases e₃ : orderOf x₃ = 3
  · exact Or.inl ⟨e₁, e₂, e₃⟩
  · exact absurd (helper hprod e₁ e₂ h₃) e₃
  · have hp' : x₁ * x₃ * x₂ = 1 := by rw [mul_right_comm, hprod]
    exact absurd (helper hp' e₁ e₃ h₂) e₂
  · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
  · have hp' : x₂ * x₃ * x₁ = 1 := by
      calc x₂ * x₃ * x₁ = x₁ * (x₂ * x₃) := mul_comm _ _
        _ = x₁ * x₂ * x₃ := (mul_assoc _ _ _).symm
        _ = 1 := hprod
    exact absurd (helper hp' e₂ e₃ h₁) e₁
  · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
  · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  · exact Or.inr (Or.inl ⟨by omega, by omega⟩)

/-- **Complete character-order trichotomy for quadratic-product pairs.** Let `G` be a commutative
group with at most one element of order `2`, and let `x₁, x₂ : G` satisfy `3 ≤ orderOf x₁` and
`orderOf (x₁ * x₂) = 2`. Then `(orderOf x₁, orderOf x₂)` falls into one of three mutually exclusive
families (and automatically `3 ≤ orderOf x₂`):
1. `Odd m₁`: `m₂ = 2 m₁` and `lcm(m₁, m₂) = 2 m₁`;
2. `m₁ = 2 m₀` with `Odd m₀` (`m₀ ≥ 3`): `m₂ = m₀` and `lcm(m₁, m₂) = 2 m₀`;
3. `4 ∣ m₁`: `m₂ = m₁` and `lcm(m₁, m₂) = m₁`. -/
theorem quadratic_product_order_trichotomy {G : Type*} [CommGroup G] (hG : HasUniqueOrderTwo G)
    {x₁ x₂ : G} (h₁ : 3 ≤ orderOf x₁) (hq : orderOf (x₁ * x₂) = 2) :
    (Odd (orderOf x₁) ∧ orderOf x₂ = 2 * orderOf x₁ ∧
        Nat.lcm (orderOf x₁) (orderOf x₂) = 2 * orderOf x₁) ∨
      (∃ m₀ : ℕ, Odd m₀ ∧ 3 ≤ m₀ ∧ orderOf x₁ = 2 * m₀ ∧ orderOf x₂ = m₀ ∧
        Nat.lcm (orderOf x₁) (orderOf x₂) = 2 * m₀) ∨
      (4 ∣ orderOf x₁ ∧ orderOf x₂ = orderOf x₁ ∧
        Nat.lcm (orderOf x₁) (orderOf x₂) = orderOf x₁) := by
  set m₁ := orderOf x₁
  set m₂ := orderOf x₂
  set q := x₁ * x₂
  have hqsq : q ^ 2 = 1 := hq ▸ pow_orderOf_eq_one q
  have hqne : q ≠ 1 := by intro h1; rw [h1, orderOf_one] at hq; omega
  -- `(x₁ x₂)² = 1` gives `x₂² = (x₁²)⁻¹`, equating `orderOf (x₁²)` and `orderOf (x₂²)`.
  have hsq_inv : x₂ ^ 2 = (x₁ ^ 2)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [mul_comm, ← mul_pow]
    exact hqsq
  have hord_sq : m₁ / m₁.gcd 2 = m₂ / m₂.gcd 2 := by
    have h12 : orderOf (x₁ ^ 2) = orderOf (x₂ ^ 2) := by
      rw [hsq_inv, orderOf_inv]
    rwa [orderOf_pow' x₁ two_ne_zero, orderOf_pow' x₂ two_ne_zero] at h12
  rcases Nat.even_or_odd m₁ with ⟨u, hu⟩ | hodd₁
  · have hg₁ : m₁.gcd 2 = 2 := Nat.gcd_eq_right ⟨u, by omega⟩
    rw [hg₁] at hord_sq
    have hm₁_div : m₁ / 2 = u := by omega
    rw [hm₁_div] at hord_sq
    rcases Nat.even_or_odd u with ⟨v, hv⟩ | hodd_u
    · right; right
      have h4 : 4 ∣ m₁ := ⟨v, by omega⟩
      have hg₂ : m₂.gcd 2 = 2 := by
        rcases Nat.even_or_odd m₂ with ⟨w, hw⟩ | hodd₂
        · exact Nat.gcd_eq_right ⟨w, by omega⟩
        · have hg21 : m₂.gcd 2 = 1 := hodd₂.coprime_two_right.gcd_eq_one
          rw [hg21, Nat.div_one] at hord_sq
          exfalso
          rcases hodd₂ with ⟨w, hw⟩
          omega
      rw [hg₂] at hord_sq
      have hm₂_eq : m₂ = m₁ := by
        have hdvd2 : 2 ∣ m₂ := hg₂ ▸ Nat.gcd_dvd_left m₂ 2
        obtain ⟨w, hw⟩ := hdvd2
        omega
      exact ⟨h4, hm₂_eq, by rw [hm₂_eq, Nat.lcm_self]⟩
    · right; left
      have hu3 : 3 ≤ u := by
        rcases hodd_u with ⟨w, hw⟩
        omega
      have hg₂ : m₂.gcd 2 = 1 := by
        rcases Nat.even_or_odd m₂ with ⟨w, hw⟩ | hodd₂
        · exfalso
          have hg22 : m₂.gcd 2 = 2 := Nat.gcd_eq_right ⟨w, by omega⟩
          rw [hg22] at hord_sq
          have hm₂_eq : m₂ = 2 * u := by omega
          have hord1 : orderOf (x₁ ^ u) = 2 := by
            rw [orderOf_pow' x₁ (by omega), show m₁.gcd u = u from
              Nat.gcd_eq_right ⟨2, by omega⟩]
            change m₁ / u = 2
            rw [show m₁ = 2 * u by omega, Nat.mul_div_cancel 2 (by omega)]
          have hord2 : orderOf (x₂ ^ u) = 2 := by
            rw [orderOf_pow' x₂ (by omega), show m₂.gcd u = u from
              Nat.gcd_eq_right ⟨2, by omega⟩]
            change m₂ / u = 2
            rw [hm₂_eq, Nat.mul_div_cancel 2 (by omega)]
          have hpow_eq : x₁ ^ u = x₂ ^ u := hG hord1 hord2
          have hqu : q ^ u = 1 := by
            change (x₁ * x₂) ^ u = 1
            rw [mul_pow, ← hpow_eq, ← sq, ← pow_mul, show u * 2 = m₁ by omega]
            exact pow_orderOf_eq_one x₁
          rcases hodd_u with ⟨w', hw'⟩
          have hqp : q ^ u = q := by
            rw [hw', pow_add, pow_mul, hqsq, one_pow, one_mul, pow_one]
          exact hqne (hqp.symm.trans hqu)
        · exact hodd₂.coprime_two_right.gcd_eq_one
      rw [hg₂, Nat.div_one] at hord_sq
      have hm₂_eq : m₂ = u := hord_sq.symm
      have hlcm : Nat.lcm m₁ m₂ = 2 * u := by
        rw [show m₁ = 2 * u by omega, hm₂_eq]
        exact Nat.lcm_eq_left ⟨2, by ring⟩
      exact ⟨u, hodd_u, hu3, by omega, hm₂_eq, hlcm⟩
  · left
    have hg₁ : m₁.gcd 2 = 1 := hodd₁.coprime_two_right.gcd_eq_one
    rw [hg₁, Nat.div_one] at hord_sq
    have hg₂ : m₂.gcd 2 = 2 := by
      rcases Nat.even_or_odd m₂ with ⟨w, hw⟩ | hodd₂
      · exact Nat.gcd_eq_right ⟨w, by omega⟩
      · exfalso
        have hg21 : m₂.gcd 2 = 1 := hodd₂.coprime_two_right.gcd_eq_one
        rw [hg21, Nat.div_one] at hord_sq
        have hqm₁ : q ^ m₁ = 1 := by
          change (x₁ * x₂) ^ m₁ = 1
          rw [mul_pow, pow_orderOf_eq_one x₁, one_mul, hord_sq]
          exact pow_orderOf_eq_one x₂
        rcases hodd₁ with ⟨w, hw⟩
        have hqp : q ^ m₁ = q := by
          rw [hw, pow_add, pow_mul, hqsq, one_pow, one_mul, pow_one]
        exact hqne (hqp.symm.trans hqm₁)
    rw [hg₂] at hord_sq
    have hdvd2 : 2 ∣ m₂ := hg₂ ▸ Nat.gcd_dvd_left m₂ 2
    obtain ⟨w, hw⟩ := hdvd2
    have hm₂_eq : m₂ = 2 * m₁ := by omega
    have hlcm : Nat.lcm m₁ m₂ = 2 * m₁ := by
      rw [hm₂_eq]
      exact Nat.lcm_eq_right ⟨2, by ring⟩
    exact ⟨hodd₁, hm₂_eq, hlcm⟩

/-- Corollary of the order trichotomy: whenever `3 ≤ orderOf x₁` and `orderOf (x₁ x₂) = 2`,
`lcm(orderOf x₁, orderOf x₂)` is even and at least `4` (and `3 ≤ orderOf x₂`). -/
theorem even_and_four_le_lcm_of_quadratic_product {G : Type*} [CommGroup G]
    (hG : HasUniqueOrderTwo G) {x₁ x₂ : G} (h₁ : 3 ≤ orderOf x₁)
    (hq : orderOf (x₁ * x₂) = 2) :
    3 ≤ orderOf x₂ ∧ Even (Nat.lcm (orderOf x₁) (orderOf x₂)) ∧
      4 ≤ Nat.lcm (orderOf x₁) (orderOf x₂) := by
  rcases quadratic_product_order_trichotomy hG h₁ hq with
    ⟨_, hm₂, hlcm⟩ | ⟨m₀, _, hm₀, _, hm₂, hlcm⟩ | ⟨⟨u, hu⟩, hm₂, hlcm⟩
  · rw [hlcm]; exact ⟨by omega, ⟨orderOf x₁, by ring⟩, by omega⟩
  · rw [hlcm]; exact ⟨by omega, ⟨m₀, by ring⟩, by omega⟩
  · rw [hlcm, hu]; exact ⟨by omega, ⟨2 * u, by ring⟩, by omega⟩

end CharacterOrderClassification

end GaloisForLFunctions.FamilyContinuationTheory
