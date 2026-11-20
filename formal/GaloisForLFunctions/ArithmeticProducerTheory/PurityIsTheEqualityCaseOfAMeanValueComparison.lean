import Mathlib

/-!
# Purity as the equality case of a mean-value comparison

A comparison of two sizes that survives the product formula, executed on the Fermat family.

* **Reading.** The functional equation pairs the Jacobi sums: `J(χ, φ) · J(χ⁻¹, φ⁻¹) = q`. It is an
  identity in every field of characteristic prime to `q`; it fixes the product of the two sizes
  `‖J(χ, φ)‖` and `‖J(χ⁻¹, φ⁻¹)‖` and nothing else.
* **Price.** Parseval over the characters of `𝔽_qˣ` counts the points `x ≠ 0, 1`:
  `Σ_χ ‖J(χ, φ)‖² = (q − 1)(q − 2)` (`sum_norm_sq_jacobiSum`).
* **Comparison.** For real families with `aᵢ bᵢ = q` the slack of the second moment over the
  product is `Σ (aᵢ − bᵢ)² = Σ aᵢ² + Σ bᵢ² − 2 |s| q` (`sum_sub_sq_eq`); if it is `≤ 0`, every
  `aᵢ² = q` (`sq_eq_of_mul_eq_of_sum_sq_le`).
* **Output.** On the characters with `χ, φ, χφ ≠ 1` the price equals the reading, the slack is
  zero, and `‖J(χ, φ)‖² = q` (`norm_jacobiSum_sq_of_meanValue`).

No positivity of a form and no conjugation identity for the Jacobi sum is used: the archimedean
place enters through a count. For a Dirichlet polynomial of length `N` the same price is the mean
value theorem, whose error term of size `N` per coefficient is the slack of this comparison over
the integers.
-/

noncomputable section

open scoped Classical
open ComplexConjugate

namespace GaloisForLFunctions.ArithmeticProducerTheory

/-! ### The comparison -/

/-- **The slack.** For two real families with `aᵢ bᵢ = q`, the excess of the second moments over
the product is a sum of squares. -/
theorem sum_sub_sq_eq {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (q : ℝ)
    (hab : ∀ i ∈ s, a i * b i = q) :
    ∑ i ∈ s, (a i - b i) ^ 2 = ∑ i ∈ s, a i ^ 2 + ∑ i ∈ s, b i ^ 2 - 2 * s.card * q := by
  have h2 : ∑ i ∈ s, a i * b i = s.card * q := by
    rw [Finset.sum_congr rfl hab, Finset.sum_const, nsmul_eq_mul]
  have h1 : ∑ i ∈ s, (a i - b i) ^ 2 =
      ∑ i ∈ s, a i ^ 2 + ∑ i ∈ s, b i ^ 2 - 2 * ∑ i ∈ s, a i * b i := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, h2]
  ring

/-- **Zero slack is purity.** If `aᵢ bᵢ = q` and the second moments are at most `2 |s| q`, then
`aᵢ² = q` for every `i`. -/
theorem sq_eq_of_mul_eq_of_sum_sq_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (q : ℝ)
    (hab : ∀ i ∈ s, a i * b i = q)
    (hsum : ∑ i ∈ s, a i ^ 2 + ∑ i ∈ s, b i ^ 2 ≤ 2 * s.card * q) :
    ∀ i ∈ s, a i ^ 2 = q := by
  intro i hi
  have hslack : ∑ j ∈ s, (a j - b j) ^ 2 = 0 :=
    le_antisymm (by rw [sum_sub_sq_eq s a b q hab]; linarith)
      (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (a j - b j)).mp hslack i hi
  have hEq : a i = b i := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0)
  rw [sq, ← hab i hi, ← hEq]

/-! ### The price: Parseval over the characters of a finite field -/

variable {K : Type*} [Field K] [Fintype K]

local instance : Fintype (MulChar K ℂ) := Fintype.ofFinite _

theorem card_mulChar_add_one : Fintype.card (MulChar K ℂ) + 1 = Fintype.card K := by
  rw [← Nat.card_eq_fintype_card, MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity K ℂ,
    Nat.card_eq_fintype_card, Fintype.card_units]
  exact Nat.sub_add_cancel Fintype.card_pos

/-- The values of a character at nonzero arguments have modulus one. -/
theorem norm_mulChar_apply (χ : MulChar K ℂ) {x : K} (hx : x ≠ 0) : ‖χ x‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.sub_ne_zero_of_lt Fintype.one_lt_card)).mp
    (by rw [← norm_pow, ← map_pow, FiniteField.pow_card_sub_one_eq_one x hx, map_one, norm_one])

/-- The characters separate the points: `Σ_χ χ(a) = 0` for `a ≠ 1`. -/
theorem sum_mulChar_apply_eq_zero {a : K} (ha : a ≠ 1) : ∑ χ : MulChar K ℂ, χ a = 0 := by
  obtain ⟨χ₀, hχ₀⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity K ℂ ha
  have h : χ₀ a * ∑ χ : MulChar K ℂ, χ a = ∑ χ : MulChar K ℂ, χ a := by
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft χ₀) _ _ fun χ => by
      rw [Equiv.coe_mulLeft, MulChar.mul_apply]
  have h' : (χ₀ a - 1) * ∑ χ : MulChar K ℂ, χ a = 0 := by rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hχ₀)

/-- Orthogonality in the character variable. -/
theorem sum_mulChar_mul_inv (x y : K) :
    ∑ χ : MulChar K ℂ, χ x * χ⁻¹ y =
      if x = y ∧ x ≠ 0 then (Fintype.card K : ℂ) - 1 else 0 := by
  by_cases hx : x = 0
  · have h0 : ∀ χ : MulChar K ℂ, χ x * χ⁻¹ y = 0 := fun χ => by
      rw [hx, MulChar.map_zero, zero_mul]
    rw [Finset.sum_congr rfl fun χ _ => h0 χ, Finset.sum_const_zero, if_neg fun h => h.2 hx]
  by_cases hy : y = 0
  · have h0 : ∀ χ : MulChar K ℂ, χ x * χ⁻¹ y = 0 := fun χ => by
      rw [hy, MulChar.map_zero, mul_zero]
    rw [Finset.sum_congr rfl fun χ _ => h0 χ, Finset.sum_const_zero,
      if_neg fun h => hx (h.1.trans hy)]
  have hterm : ∀ χ : MulChar K ℂ, χ x * χ⁻¹ y = χ (x * y⁻¹) := fun χ => by
    rw [MulChar.inv_apply', map_mul]
  rw [Finset.sum_congr rfl fun χ _ => hterm χ]
  by_cases hxy : x = y
  · rw [if_pos ⟨hxy, hx⟩, hxy, mul_inv_cancel₀ hy]
    simp only [map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [eq_sub_iff_add_eq]
    exact_mod_cast card_mulChar_add_one (K := K)
  · rw [if_neg fun h => hxy h.1]
    exact sum_mulChar_apply_eq_zero fun h => hxy ((mul_inv_eq_one₀ hy).mp h)

/-- **Parseval over the characters.** The second moment of the transform `χ ↦ Σ_x χ(x) f(x)` is
`q − 1` times the second moment of `f` on `x ≠ 0`. -/
theorem sum_norm_sq_mulChar_sum (f : K → ℂ) :
    (∑ χ : MulChar K ℂ, ((‖∑ x, χ x * f x‖ : ℝ) : ℂ) ^ 2) =
      ((Fintype.card K : ℂ) - 1) * ∑ x ∈ Finset.univ.erase (0 : K), ((‖f x‖ : ℝ) : ℂ) ^ 2 := by
  have h1 : ∀ χ : MulChar K ℂ, ((‖∑ x, χ x * f x‖ : ℝ) : ℂ) ^ 2 =
      ∑ x, ∑ y, f x * conj (f y) * (χ x * χ⁻¹ y) := by
    intro χ
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul, ← MulChar.star_apply' χ y]
    simp only [starRingEnd_apply]
    ring
  have h2 : ∀ x : K, ∑ χ : MulChar K ℂ, ∑ y, f x * conj (f y) * (χ x * χ⁻¹ y) =
      if x = 0 then 0 else ((Fintype.card K : ℂ) - 1) * ((‖f x‖ : ℝ) : ℂ) ^ 2 := by
    intro x
    have h3 : ∀ y : K, ∑ χ : MulChar K ℂ, f x * conj (f y) * (χ x * χ⁻¹ y) =
        f x * conj (f y) * (if x = y ∧ x ≠ 0 then (Fintype.card K : ℂ) - 1 else 0) := fun y => by
      rw [← Finset.mul_sum, sum_mulChar_mul_inv]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun y _ => h3 y, Finset.sum_eq_single x]
    · by_cases hx : x = 0
      · rw [if_pos hx, if_neg fun h => h.2 hx, mul_zero]
      · rw [if_neg hx, if_pos ⟨rfl, hx⟩, Complex.mul_conj']
        ring
    · intro y _ hy
      rw [if_neg fun h => hy h.1.symm, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ x) h
  have h4 : ∑ x ∈ Finset.univ.erase (0 : K),
        (if x = 0 then (0 : ℂ) else ((Fintype.card K : ℂ) - 1) * ((‖f x‖ : ℝ) : ℂ) ^ 2) =
      ∑ x : K, (if x = 0 then (0 : ℂ) else ((Fintype.card K : ℂ) - 1) * ((‖f x‖ : ℝ) : ℂ) ^ 2) :=
    Finset.sum_erase _ (if_pos rfl)
  rw [Finset.sum_congr rfl fun χ _ => h1 χ, Finset.sum_comm, Finset.sum_congr rfl fun x _ => h2 x,
    ← h4, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x hx => if_neg (Finset.ne_of_mem_erase hx)

/-- **The price.** The second moment of the Jacobi sums over all `χ` counts the points
`x ≠ 0, 1`: `Σ_χ ‖J(χ, φ)‖² = (q − 1)(q − 2)`. -/
theorem sum_norm_sq_jacobiSum (φ : MulChar K ℂ) :
    ∑ χ : MulChar K ℂ, ‖jacobiSum χ φ‖ ^ 2 =
      ((Fintype.card K : ℝ) - 1) * ((Fintype.card K : ℝ) - 2) := by
  have hC := sum_norm_sq_mulChar_sum (K := K) fun x => φ (1 - x)
  have h1 : ∑ x ∈ (Finset.univ.erase (0 : K)).erase 1, ((‖φ (1 - x)‖ : ℝ) : ℂ) ^ 2 =
      ∑ x ∈ Finset.univ.erase (0 : K), ((‖φ (1 - x)‖ : ℝ) : ℂ) ^ 2 :=
    Finset.sum_erase _ (by
      rw [sub_self, MulChar.map_zero, norm_zero, Complex.ofReal_zero, zero_pow two_ne_zero])
  have h2 : ∀ x ∈ (Finset.univ.erase (0 : K)).erase 1, ((‖φ (1 - x)‖ : ℝ) : ℂ) ^ 2 = 1 :=
    fun x hx => by
      rw [norm_mulChar_apply φ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hx).symm),
        Complex.ofReal_one, one_pow]
  have hc : ((Finset.univ.erase (0 : K)).erase 1).card + 2 = Fintype.card K := by
    have e1 := Finset.card_erase_add_one (Finset.mem_univ (0 : K))
    have e2 := Finset.card_erase_add_one
      (Finset.mem_erase.mpr ⟨one_ne_zero, Finset.mem_univ (1 : K)⟩)
    rw [Finset.card_univ] at e1
    omega
  have hcount : ∑ x ∈ Finset.univ.erase (0 : K), ((‖φ (1 - x)‖ : ℝ) : ℂ) ^ 2 =
      (Fintype.card K : ℂ) - 2 := by
    rw [← h1, Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul, mul_one,
      eq_sub_iff_add_eq]
    exact_mod_cast hc
  rw [hcount] at hC
  have hreal : ((∑ χ : MulChar K ℂ, ‖jacobiSum χ φ‖ ^ 2 : ℝ) : ℂ) =
      ((((Fintype.card K : ℝ) - 1) * ((Fintype.card K : ℝ) - 2) : ℝ) : ℂ) := by
    push_cast
    exact hC
  exact_mod_cast hreal

/-! ### The Fermat family -/

/-- The characters `χ` with `χ ≠ 1` and `χ φ ≠ 1`. -/
def genericChars (φ : MulChar K ℂ) : Finset (MulChar K ℂ) := (Finset.univ.erase 1).erase φ⁻¹

theorem mem_genericChars {χ φ : MulChar K ℂ} : χ ∈ genericChars φ ↔ χ ≠ 1 ∧ χ * φ ≠ 1 := by
  rw [genericChars, Finset.mem_erase, Finset.mem_erase]
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h2, fun h => h1 (mul_eq_one_iff_eq_inv.mp h)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h2 (mul_eq_one_iff_eq_inv.mpr h), h1, Finset.mem_univ _⟩

theorem card_genericChars {φ : MulChar K ℂ} (hφ : φ ≠ 1) :
    ((genericChars φ).card : ℝ) = (Fintype.card K : ℝ) - 3 := by
  have e1 := Finset.card_erase_add_one (Finset.mem_univ (1 : MulChar K ℂ))
  have e2 := Finset.card_erase_add_one
    (Finset.mem_erase.mpr ⟨inv_ne_one.mpr hφ, Finset.mem_univ φ⁻¹⟩)
  have e3 := card_mulChar_add_one (K := K)
  rw [Finset.card_univ] at e1
  have h : (genericChars φ).card + 3 = Fintype.card K := by
    unfold genericChars
    omega
  rw [eq_sub_iff_add_eq]
  exact_mod_cast h

/-- At the two degenerate characters the Jacobi sum has modulus one. -/
theorem norm_jacobiSum_one_sq {φ : MulChar K ℂ} (hφ : φ ≠ 1) : ‖jacobiSum 1 φ‖ ^ 2 = 1 := by
  rw [jacobiSum_one_nontrivial hφ, norm_neg, norm_one, one_pow]

theorem norm_jacobiSum_inv_sq {φ : MulChar K ℂ} (hφ : φ ≠ 1) : ‖jacobiSum φ⁻¹ φ‖ ^ 2 = 1 := by
  rw [jacobiSum_comm, jacobiSum_nontrivial_inv hφ, norm_neg,
    norm_mulChar_apply φ (neg_ne_zero.mpr one_ne_zero), one_pow]

/-- On the generic characters the price is exactly `q` per character. -/
theorem sum_genericChars_norm_sq {φ : MulChar K ℂ} (hφ : φ ≠ 1) :
    ∑ χ ∈ genericChars φ, ‖jacobiSum χ φ‖ ^ 2 = (genericChars φ).card * (Fintype.card K : ℝ) := by
  have h1 : ‖jacobiSum 1 φ‖ ^ 2 + ∑ χ ∈ Finset.univ.erase (1 : MulChar K ℂ), ‖jacobiSum χ φ‖ ^ 2 =
      ∑ χ : MulChar K ℂ, ‖jacobiSum χ φ‖ ^ 2 :=
    Finset.add_sum_erase Finset.univ (fun χ : MulChar K ℂ => ‖jacobiSum χ φ‖ ^ 2)
      (Finset.mem_univ 1)
  have h2 : ‖jacobiSum φ⁻¹ φ‖ ^ 2 + ∑ χ ∈ genericChars φ, ‖jacobiSum χ φ‖ ^ 2 =
      ∑ χ ∈ Finset.univ.erase (1 : MulChar K ℂ), ‖jacobiSum χ φ‖ ^ 2 :=
    Finset.add_sum_erase (Finset.univ.erase (1 : MulChar K ℂ))
      (fun χ : MulChar K ℂ => ‖jacobiSum χ φ‖ ^ 2)
      (Finset.mem_erase.mpr ⟨inv_ne_one.mpr hφ, Finset.mem_univ φ⁻¹⟩)
  rw [norm_jacobiSum_one_sq hφ, sum_norm_sq_jacobiSum] at h1
  rw [norm_jacobiSum_inv_sq hφ] at h2
  have h3 : ∑ χ ∈ genericChars φ, ‖jacobiSum χ φ‖ ^ 2 =
      ((Fintype.card K : ℝ) - 1) * ((Fintype.card K : ℝ) - 2) - 2 := by linarith
  rw [h3, card_genericChars hφ]
  ring

/-- Inversion carries the generic characters of `φ` to those of `φ⁻¹`. -/
theorem sum_genericChars_inv (φ : MulChar K ℂ) :
    ∑ χ ∈ genericChars φ, ‖jacobiSum χ⁻¹ φ⁻¹‖ ^ 2 =
      ∑ χ ∈ genericChars φ⁻¹, ‖jacobiSum χ φ⁻¹‖ ^ 2 := by
  refine Finset.sum_nbij' (fun χ => χ⁻¹) (fun χ => χ⁻¹) ?_ ?_ (fun χ _ => inv_inv χ)
    (fun χ _ => inv_inv χ) (fun χ _ => rfl)
  · intro χ hχ
    rw [mem_genericChars] at hχ ⊢
    exact ⟨inv_ne_one.mpr hχ.1, by rw [← mul_inv]; exact inv_ne_one.mpr hχ.2⟩
  · intro χ hχ
    rw [mem_genericChars] at hχ ⊢
    have e : χ⁻¹ * φ = (χ * φ⁻¹)⁻¹ := by rw [mul_inv, inv_inv]
    exact ⟨inv_ne_one.mpr hχ.1, by rw [e]; exact inv_ne_one.mpr hχ.2⟩

/-- **Purity from the functional equation and the mean value.** For `χ, φ, χφ ≠ 1`,
`‖J(χ, φ)‖² = q`: the functional equation fixes the products `‖J(χ, φ)‖ ‖J(χ⁻¹, φ⁻¹)‖ = q`,
Parseval fixes both second moments at `q` per character, and the comparison has zero slack. -/
theorem norm_jacobiSum_sq_of_meanValue {χ φ : MulChar K ℂ} (hχ : χ ≠ 1) (hφ : φ ≠ 1)
    (hχφ : χ * φ ≠ 1) : ‖jacobiSum χ φ‖ ^ 2 = Fintype.card K := by
  have hchar : ringChar ℂ ≠ ringChar K := by
    rw [ringChar.eq_zero]
    exact (CharP.ringChar_ne_zero_of_finite K).symm
  refine sq_eq_of_mul_eq_of_sum_sq_le (genericChars φ) (fun χ => ‖jacobiSum χ φ‖)
    (fun χ => ‖jacobiSum χ⁻¹ φ⁻¹‖) (Fintype.card K) ?_ ?_ χ (mem_genericChars.mpr ⟨hχ, hχφ⟩)
  · intro ψ hψ
    rw [mem_genericChars] at hψ
    show ‖jacobiSum ψ φ‖ * ‖jacobiSum ψ⁻¹ φ⁻¹‖ = (Fintype.card K : ℝ)
    rw [← norm_mul, jacobiSum_mul_jacobiSum_inv hchar hψ.1 hφ hψ.2, Complex.norm_natCast]
  · show ∑ χ ∈ genericChars φ, ‖jacobiSum χ φ‖ ^ 2 +
        ∑ χ ∈ genericChars φ, ‖jacobiSum χ⁻¹ φ⁻¹‖ ^ 2 ≤
      2 * (genericChars φ).card * (Fintype.card K : ℝ)
    rw [sum_genericChars_norm_sq hφ, sum_genericChars_inv,
      sum_genericChars_norm_sq (inv_ne_one.mpr hφ), card_genericChars hφ,
      card_genericChars (inv_ne_one.mpr hφ)]
    exact le_of_eq (by ring)

end GaloisForLFunctions.ArithmeticProducerTheory
