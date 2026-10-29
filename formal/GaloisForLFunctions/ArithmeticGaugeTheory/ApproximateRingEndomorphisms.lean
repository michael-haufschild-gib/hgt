import GaloisForLFunctions.ArithmeticGaugeTheory.TheAdditivelyInvariantPoint

/-!
# Approximate ring endomorphisms of ℕ and the Frobenius gap

Over `𝔽_p[X]` the Frobenius `f ↦ f^p` is a ring endomorphism that multiplies degrees by `p`
(`natDegree_frobenius`): it is additive and multiplicative at once, and its growth is what gives
Stepanov's auxiliary its multiplicity. This file classifies the maps of `ℕ` that are completely
multiplicative and additive up to a bounded defect `‖φ(a + b) − φ(a) − φ(b)‖ ≤ B`.

* **Classification** (`approxRingEndomorphism_classification`). Such a map is the identity on the
  positive integers, or it is bounded by one. Doubling gives `‖φ(n)‖ ‖φ(2) − 2‖ ≤ B`: either
  `φ(2) = 2`, or `φ` is bounded, hence bounded by one since `‖φ(n)‖^k = ‖φ(n^k)‖`. If `φ(2) = 2`,
  then `φ(2^k) = 2^k`, and adding `n` copies of `2^k` costs `(n − 1)B`, so
  `2^k ‖φ(n) − n‖ ≤ (n − 1)B` for every `k`.
* **Converse** (`additiveDefectBounded_of_norm_le_one`). Every map bounded by one has defect at most
  three. So the approximate ring endomorphisms are exactly the identity and the completely
  multiplicative functions in the closed unit ball.
* **The gauge torus** (`approxRingEndomorphism_unimodular_iff`, `additiveDefectBounded_twist`). Every
  gauge point is an approximate ring endomorphism of defect at most three. An approximate ring
  endomorphism with `f(1) = 1` and `‖f(p)‖ ≥ 1` at every prime is the identity or a gauge point.
* **Exact endomorphisms** (`ringEndomorphism_classification`). With defect zero only the identity
  and zero remain.
* **Integer values** (`int_approxRingEndomorphism_classification`). An integer-valued approximate
  ring endomorphism is the identity or takes values in `{−1, 0, 1}`: the Liouville sign, the real
  characters and their products.

So `ℤ` has no Frobenius substitute among its own self-maps. The only multiplicative maps that
respect addition up to a fixed budget are the identity, which does not grow, and the bounded gauge
points, the parity twin among them. A source of growing multiplicity must live on a larger object.
-/

open Filter

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-- Bounded additive defect on the positive integers. -/
def AdditiveDefectBounded (φ : ℕ → ℂ) (B : ℝ) : Prop :=
  ∀ a b, a ≠ 0 → b ≠ 0 → ‖φ (a + b) - φ a - φ b‖ ≤ B

/-- An approximate ring endomorphism of `ℕ`: completely multiplicative, additive up to a bounded
defect. -/
def IsApproxRingEndomorphism (φ : ℕ → ℂ) : Prop :=
  IsCompletelyMultiplicative φ ∧ ∃ B, AdditiveDefectBounded φ B

/-! ### Elementary consequences of the two laws -/

/-- Powers: `φ(n^k) = φ(n)^k`. -/
theorem map_pow_of_isCompletelyMultiplicative {φ : ℕ → ℂ} (hφ : IsCompletelyMultiplicative φ)
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) (h1 : φ 1 = 1) : φ (n ^ k) = φ n ^ k := by
  induction k with
  | zero => simpa using h1
  | succ k ih => rw [pow_succ, hφ _ _ (pow_ne_zero k hn) hn, ih, pow_succ]

/-- Adding `n` copies of `m` costs at most `(n − 1)B`. -/
theorem norm_map_nsmul_sub_le {φ : ℕ → ℂ} {B : ℝ} (hB : AdditiveDefectBounded φ B) {m : ℕ}
    (hm : m ≠ 0) : ∀ n, 1 ≤ n → ‖φ (n * m) - n * φ m‖ ≤ (n - 1) * B := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hnm : n * m ≠ 0 := Nat.mul_ne_zero (by omega) hm
    have hstep := hB (n * m) m hnm hm
    have hsplit : φ ((n + 1) * m) - ((n + 1 : ℕ) : ℂ) * φ m =
        (φ (n * m + m) - φ (n * m) - φ m) + (φ (n * m) - n * φ m) := by
      rw [Nat.succ_mul]; push_cast; ring
    rw [hsplit]
    calc ‖(φ (n * m + m) - φ (n * m) - φ m) + (φ (n * m) - n * φ m)‖
        ≤ B + (n - 1) * B := (norm_add_le _ _).trans (add_le_add hstep ih)
      _ = ((n + 1 : ℕ) - 1 : ℝ) * B := by push_cast; ring

/-- Doubling: `‖φ(n)‖ ‖φ(2) − 2‖ ≤ B`. -/
theorem norm_mul_norm_sub_two_le {φ : ℕ → ℂ} (hφ : IsCompletelyMultiplicative φ) {B : ℝ}
    (hB : AdditiveDefectBounded φ B) {n : ℕ} (hn : n ≠ 0) : ‖φ n‖ * ‖φ 2 - 2‖ ≤ B := by
  have h := hB n n hn hn
  rw [← two_mul, hφ 2 n two_ne_zero hn] at h
  rw [← norm_mul]
  calc ‖φ n * (φ 2 - 2)‖ = ‖φ 2 * φ n - φ n - φ n‖ := by congr 1; ring
    _ ≤ B := h

/-- A nonnegative quantity whose dyadic multiples stay bounded vanishes. -/
theorem eq_zero_of_mul_two_pow_le {a D : ℝ} (ha : 0 ≤ a) (h : ∀ k : ℕ, a * 2 ^ k ≤ D) : a = 0 := by
  by_contra hne
  have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (D / a) (by norm_num : (1 : ℝ) < 2)
  have := h k
  rw [div_lt_iff₀ hpos] at hk
  linarith [mul_comm a ((2 : ℝ) ^ k)]

/-- **Bounded completely multiplicative functions are bounded by one.** -/
theorem norm_le_one_of_bounded {φ : ℕ → ℂ} (hφ : IsCompletelyMultiplicative φ) (h1 : φ 1 = 1)
    {C : ℝ} (hC : ∀ n, n ≠ 0 → ‖φ n‖ ≤ C) : ∀ n, n ≠ 0 → ‖φ n‖ ≤ 1 := by
  intro n hn
  by_contra hgt
  push_neg at hgt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hgt
  have := hC (n ^ k) (pow_ne_zero k hn)
  rw [map_pow_of_isCompletelyMultiplicative hφ hn k h1, norm_pow] at this
  linarith

/-! ### Classification -/

/-- If `φ(2) = 2`, then `φ` is the identity on the positive integers. -/
theorem eq_id_of_map_two {φ : ℕ → ℂ} (hφ : IsCompletelyMultiplicative φ) {B : ℝ}
    (hB : AdditiveDefectBounded φ B) (h2 : φ 2 = 2) : ∀ n, n ≠ 0 → φ n = n := by
  have h1 : φ 1 = 1 := by
    have h := hφ 1 2 one_ne_zero two_ne_zero
    rw [one_mul, h2] at h
    exact (mul_right_cancel₀ two_ne_zero (h.symm.trans (one_mul 2).symm))
  intro n hn
  have hbound : ∀ k : ℕ, ‖φ n - n‖ * 2 ^ k ≤ (n - 1) * B := by
    intro k
    have hpow : φ (2 ^ k) = 2 ^ k := by
      rw [map_pow_of_isCompletelyMultiplicative hφ two_ne_zero k h1, h2]
    have h := norm_map_nsmul_sub_le hB (pow_ne_zero k two_ne_zero) n (Nat.one_le_iff_ne_zero.mpr hn)
    rw [hφ n _ hn (pow_ne_zero k two_ne_zero), hpow] at h
    calc ‖φ n - n‖ * 2 ^ k = ‖φ n * 2 ^ k - n * 2 ^ k‖ := by
          rw [← sub_mul, norm_mul, norm_pow, Complex.norm_ofNat]
      _ ≤ (n - 1) * B := h
  exact sub_eq_zero.mp (norm_eq_zero.mp (eq_zero_of_mul_two_pow_le (norm_nonneg _) hbound))

/-- **Classification of approximate ring endomorphisms.** A completely multiplicative map with
bounded additive defect is the identity on the positive integers or is bounded by one. -/
theorem approxRingEndomorphism_classification {φ : ℕ → ℂ} (hφ : IsCompletelyMultiplicative φ)
    {B : ℝ} (hB : AdditiveDefectBounded φ B) :
    (∀ n, n ≠ 0 → φ n = n) ∨ ∀ n, n ≠ 0 → ‖φ n‖ ≤ 1 := by
  by_cases h2 : φ 2 = 2
  · exact Or.inl (eq_id_of_map_two hφ hB h2)
  · right
    have hpos : 0 < ‖φ 2 - 2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h2)
    have hbdd : ∀ n, n ≠ 0 → ‖φ n‖ ≤ B / ‖φ 2 - 2‖ := fun n hn =>
      (le_div_iff₀ hpos).mpr (norm_mul_norm_sub_two_le hφ hB hn)
    -- `φ(1)² = φ(1)`, so `φ(1) ∈ {0, 1}`.
    have h11 : φ 1 * φ 1 = φ 1 := by rw [← hφ 1 1 one_ne_zero one_ne_zero, one_mul]
    by_cases h1 : φ 1 = 1
    · exact norm_le_one_of_bounded hφ h1 hbdd
    · have h0 : φ 1 = 0 := by
        rcases mul_self_eq_self.mp h11 with h | h
        · exact h
        · exact absurd h h1
      intro n hn
      have := hφ n 1 hn one_ne_zero
      rw [mul_one, h0, mul_zero] at this
      rw [this, norm_zero]
      exact zero_le_one

/-- **Converse.** A map bounded by one has additive defect at most three. -/
theorem additiveDefectBounded_of_norm_le_one {φ : ℕ → ℂ} (h : ∀ n, n ≠ 0 → ‖φ n‖ ≤ 1) :
    AdditiveDefectBounded φ 3 := by
  intro a b ha hb
  calc ‖φ (a + b) - φ a - φ b‖ ≤ ‖φ (a + b)‖ + ‖φ a‖ + ‖φ b‖ := by
        refine (norm_sub_le _ _).trans ?_
        exact add_le_add_right (norm_sub_le _ _) _
    _ ≤ 1 + 1 + 1 := add_le_add (add_le_add (h _ (by omega)) (h a ha)) (h b hb)
    _ = 3 := by norm_num

/-- The identity is an exact ring endomorphism. -/
theorem additiveDefectBounded_id : AdditiveDefectBounded (fun n => (n : ℂ)) 0 := by
  intro a b _ _
  simp

/-- **Every gauge point is an approximate ring endomorphism**, with defect at most three. -/
theorem additiveDefectBounded_twist (x : GaugeTorus) : AdditiveDefectBounded (twist x) 3 :=
  additiveDefectBounded_of_norm_le_one fun n _ => (norm_twist x n).le

theorem isApproxRingEndomorphism_twist (x : GaugeTorus) : IsApproxRingEndomorphism (twist x) :=
  ⟨isCompletelyMultiplicative_twist x, 3, additiveDefectBounded_twist x⟩

/-- **The gauge torus inside the approximate ring endomorphisms.** An approximate ring
endomorphism with `f(1) = 1` and `‖f(p)‖ ≥ 1` at every prime is the identity on the positive
integers, or it is a gauge point. -/
theorem approxRingEndomorphism_unimodular_iff {f : ℕ → ℂ} (hf : IsApproxRingEndomorphism f)
    (h1 : f 1 = 1) (hp : ∀ p, p.Prime → 1 ≤ ‖f p‖) :
    (∀ n, n ≠ 0 → f n = n) ∨ ∃ x : GaugeTorus, ∀ n, n ≠ 0 → twist x n = f n := by
  obtain ⟨hmul, B, hB⟩ := hf
  rcases approxRingEndomorphism_classification hmul hB with hid | hball
  · exact Or.inl hid
  · right
    exact exists_twist_eq f h1 hmul fun p hpp =>
      le_antisymm (hball p hpp.ne_zero) (hp p hpp)

/-- **Exact ring endomorphisms of ℕ.** With zero additive defect only the identity and zero
remain. -/
theorem ringEndomorphism_classification {φ : ℕ → ℂ} (hφ : IsCompletelyMultiplicative φ)
    (hadd : AdditiveDefectBounded φ 0) :
    (∀ n, n ≠ 0 → φ n = n) ∨ ∀ n, n ≠ 0 → φ n = 0 := by
  rcases approxRingEndomorphism_classification hφ hadd with hid | hball
  · exact Or.inl hid
  · right
    -- Exact additivity gives `φ(n) = n φ(1)`; boundedness forces `φ(1) = 0`.
    have hlin : ∀ n, n ≠ 0 → φ n = n * φ 1 := by
      intro n hn
      have h := norm_map_nsmul_sub_le hadd one_ne_zero n (Nat.one_le_iff_ne_zero.mpr hn)
      rw [mul_zero, mul_one] at h
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
    have h10 : φ 1 = 0 := by
      have h2 := hball 2 two_ne_zero
      rw [hlin 2 two_ne_zero, norm_mul, Complex.norm_ofNat] at h2
      have h1 := hball 1 one_ne_zero
      by_contra hne
      have hpos : 0 < ‖φ 1‖ := norm_pos_iff.mpr hne
      -- `‖φ 1‖ = ‖φ(1)‖²` from `φ(1) = φ(1)²`.
      have h11 : φ 1 = φ 1 * φ 1 := by rw [← hφ 1 1 one_ne_zero one_ne_zero, one_mul]
      have hone : ‖φ 1‖ = 1 := by
        have := congrArg norm h11
        rw [norm_mul] at this
        nlinarith
      linarith
    intro n hn
    rw [hlin n hn, h10, mul_zero]

/-- **Integer-valued approximate ring endomorphisms** are the identity, or take values in
`{−1, 0, 1}`. -/
theorem int_approxRingEndomorphism_classification {φ : ℕ → ℤ}
    (hφ : IsCompletelyMultiplicative fun n => (φ n : ℂ)) {B : ℝ}
    (hB : AdditiveDefectBounded (fun n => (φ n : ℂ)) B) :
    (∀ n, n ≠ 0 → φ n = n) ∨ ∀ n, n ≠ 0 → φ n = -1 ∨ φ n = 0 ∨ φ n = 1 := by
  rcases approxRingEndomorphism_classification hφ hB with hid | hball
  · left
    intro n hn
    exact_mod_cast hid n hn
  · right
    intro n hn
    have h := hball n hn
    rw [Complex.norm_intCast] at h
    have h' : |φ n| ≤ 1 := by exact_mod_cast h
    rcases abs_le.mp h' with ⟨hlo, hhi⟩
    omega

/-! ### The contrast over `𝔽_p[X]` -/

/-- **Frobenius grows.** Over `𝔽_p[X]` the Frobenius ring endomorphism multiplies degrees by `p`. -/
theorem natDegree_frobenius (p : ℕ) [Fact p.Prime] (f : Polynomial (ZMod p)) :
    (frobenius (Polynomial (ZMod p)) p f).natDegree = p * f.natDegree := by
  rw [frobenius_def, Polynomial.natDegree_pow]

end GaloisForLFunctions.ArithmeticGaugeTheory
