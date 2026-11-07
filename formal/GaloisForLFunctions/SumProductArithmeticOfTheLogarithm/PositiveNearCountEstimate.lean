import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCountModel

/-!
# A positive-generator system at quadratic logarithmic count distance

The system with odd-prime labels and extra labels of norms three and four has
leading count coefficient one and error O((log X)^2). Each exponent rectangle
is a disjoint union of odd-integer fibres. Their half-unit rounding errors and
the two geometric tails give the explicit bound.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount

open RHTower.BeurlingDeletion

/-- A finite union of odd-integer fibres, tagged by the two extra-label exponents. -/
private def rectangle (X : ℝ) (A B : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (A + 1) ×ˢ Finset.range (B + 1)).biUnion fun ab =>
    (oddIntegers (X / ((3 : ℝ) ^ ab.1 * 4 ^ ab.2))).image fun u => (u, ab)

/-- The tagged fibres are disjoint, so their cardinalities add. -/
private theorem card_rectangle (X : ℝ) (A B : ℕ) :
    (rectangle X A B).card =
      ∑ a ∈ Finset.range (A + 1), ∑ b ∈ Finset.range (B + 1),
        (oddIntegers (X / ((3 : ℝ) ^ a * 4 ^ b))).card := by
  rw [rectangle, Finset.card_biUnion]
  · rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    exact Finset.card_image_of_injective _ (fun u v huv => congrArg Prod.fst huv)
  · intro ab _ cd _ hne
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hv
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hw
    exact hne (congrArg Prod.snd (hu.trans hw.symm))

/-- Strict power cutoffs include every triple of bounded norm. -/
private theorem rectangle_eq_triples {X : ℝ} (hX : 0 ≤ X) (A B : ℕ)
    (hA : X < (3 : ℝ) ^ (A + 1)) (hB : X < (4 : ℝ) ^ (B + 1)) :
    (rectangle X A B : Set (ℕ × ℕ × ℕ)) = tripleSet X := by
  ext v
  constructor
  · intro hv
    obtain ⟨ab, _, hv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    have hd : 0 < (3 : ℝ) ^ ab.1 * 4 ^ ab.2 := by positivity
    obtain ⟨huo, huX⟩ := (mem_oddIntegers (div_nonneg hX hd.le) u).mp hu
    refine ⟨huo, ?_⟩
    simpa only [mul_assoc] using (le_div_iff₀ hd).mp huX
  · rcases v with ⟨u, a, b⟩
    rintro ⟨hu, huX⟩
    have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast Nat.pos_of_ne_zero hu.1
    have ha1 : (1 : ℝ) ≤ (3 : ℝ) ^ a := one_le_pow₀ (by norm_num)
    have hb1 : (1 : ℝ) ≤ (4 : ℝ) ^ b := one_le_pow₀ (by norm_num)
    have hd : 0 < (3 : ℝ) ^ a * 4 ^ b := by positivity
    have habX : (3 : ℝ) ^ a * 4 ^ b ≤ X := by
      have hh := mul_le_mul_of_nonneg_right hu1 hd.le
      simp only [one_mul] at hh
      exact hh.trans (by simpa only [mul_assoc] using huX)
    have haX : (3 : ℝ) ^ a ≤ X := by
      have hh := mul_le_mul_of_nonneg_left hb1 (by positivity : 0 ≤ (3 : ℝ) ^ a)
      simp only [mul_one] at hh
      exact hh.trans habX
    have hbX : (4 : ℝ) ^ b ≤ X := by
      have hh := mul_le_mul_of_nonneg_right ha1 (by positivity : 0 ≤ (4 : ℝ) ^ b)
      simp only [one_mul] at hh
      exact hh.trans habX
    have haA : a < A + 1 := by
      by_contra hh
      have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (show A + 1 ≤ a by omega)
      exact (not_le_of_gt hA) (hp.trans haX)
    have hbB : b < B + 1 := by
      by_contra hh
      have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (show B + 1 ≤ b by omega)
      exact (not_le_of_gt hB) (hp.trans hbX)
    apply Finset.mem_biUnion.mpr
    refine ⟨(a, b), Finset.mem_product.mpr ⟨Finset.mem_range.mpr haA,
      Finset.mem_range.mpr hbB⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨u, (mem_oddIntegers (div_nonneg hX hd.le) u).mpr ⟨hu, ?_⟩, rfl⟩
    exact (le_div_iff₀ hd).mpr (by simpa only [mul_assoc] using huX)

/-- The actual norm count is a finite double sum of odd-integer counts. -/
theorem countBall_eq_rectangle_sum {X : ℝ} (hX : 0 ≤ X) (A B : ℕ)
    (hA : X < (3 : ℝ) ^ (A + 1)) (hB : X < (4 : ℝ) ^ (B + 1)) :
    system.countBall X = ∑ a ∈ Finset.range (A + 1), ∑ b ∈ Finset.range (B + 1),
      (oddIntegers (X / ((3 : ℝ) ^ a * 4 ^ b))).card := by
  rw [countBall_eq_ncard_triples, ← rectangle_eq_triples hX A B hA hB,
    Set.ncard_coe_finset, card_rectangle]

/-- The two geometric factors make the leading coefficient exactly one. -/
private theorem rectangle_main_term (X : ℝ) (A B : ℕ) :
    (∑ a ∈ Finset.range (A + 1), ∑ b ∈ Finset.range (B + 1),
      X / ((3 : ℝ) ^ a * 4 ^ b) / 2) =
      X * (1 - (1 / 3 : ℝ) ^ (A + 1)) * (1 - (1 / 4 : ℝ) ^ (B + 1)) := by
  have hf : (∑ a ∈ Finset.range (A + 1), ∑ b ∈ Finset.range (B + 1),
      X / ((3 : ℝ) ^ a * 4 ^ b) / 2) =
      X / 2 * (∑ a ∈ Finset.range (A + 1), (1 / 3 : ℝ) ^ a) *
        (∑ b ∈ Finset.range (B + 1), (1 / 4 : ℝ) ^ b) := by
    symm
    conv_lhs => lhs; rw [Finset.mul_sum]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [div_pow, div_pow]
    simp only [one_pow, div_eq_mul_inv, mul_inv, one_mul]
    ring
  rw [hf, geom_sum_eq (by norm_num : (1 / 3 : ℝ) ≠ 1),
    geom_sum_eq (by norm_num : (1 / 4 : ℝ) ≠ 1)]
  norm_num
  ring

/-- Each odd-integer fibre contributes rounding error at most one half. -/
private theorem rectangle_rounding_error {X : ℝ} (hX : 0 ≤ X) (A B : ℕ) :
    |(∑ a ∈ Finset.range (A + 1), ∑ b ∈ Finset.range (B + 1),
        ((oddIntegers (X / ((3 : ℝ) ^ a * 4 ^ b))).card : ℝ)) -
      (∑ a ∈ Finset.range (A + 1), ∑ b ∈ Finset.range (B + 1),
        X / ((3 : ℝ) ^ a * 4 ^ b) / 2)| ≤
      ((A + 1 : ℕ) : ℝ) * ((B + 1 : ℕ) : ℝ) / 2 := by
  let E (a b : ℕ) := ((oddIntegers (X / ((3 : ℝ) ^ a * 4 ^ b))).card : ℝ) -
    X / ((3 : ℝ) ^ a * 4 ^ b) / 2
  have he (a b : ℕ) : |E a b| ≤ 1 / 2 :=
    odd_count_error (div_nonneg hX (by positivity))
  have hlo : (∑ _a ∈ Finset.range (A + 1), ∑ _b ∈ Finset.range (B + 1), (-1 / 2 : ℝ)) ≤
      ∑ a ∈ Finset.range (A + 1), ∑ b ∈ Finset.range (B + 1), E a b := by
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    simpa only [neg_div] using (abs_le.mp (he a b)).1
  have hhi : (∑ a ∈ Finset.range (A + 1), ∑ b ∈ Finset.range (B + 1), E a b) ≤
      ∑ _a ∈ Finset.range (A + 1), ∑ _b ∈ Finset.range (B + 1), (1 / 2 : ℝ) := by
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    exact (abs_le.mp (he a b)).2
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlo hhi
  have hs : (∑ a ∈ Finset.range (A + 1), ∑ b ∈ Finset.range (B + 1),
        ((oddIntegers (X / ((3 : ℝ) ^ a * 4 ^ b))).card : ℝ)) -
      (∑ a ∈ Finset.range (A + 1), ∑ b ∈ Finset.range (B + 1),
        X / ((3 : ℝ) ^ a * 4 ^ b) / 2) =
      ∑ a ∈ Finset.range (A + 1), ∑ b ∈ Finset.range (B + 1), E a b := by
    dsimp only [E]
    simp_rw [Finset.sum_sub_distrib]
  rw [hs]
  exact abs_le.mpr ⟨by linarith only [hlo], by linarith only [hhi]⟩

/-- The omitted geometric main terms total less than two. -/
private theorem geometric_tail {X : ℝ} (hX : 0 ≤ X) (A B : ℕ)
    (hA : X < (3 : ℝ) ^ (A + 1)) (hB : X < (4 : ℝ) ^ (B + 1)) :
    |X * (1 - (1 / 3 : ℝ) ^ (A + 1)) * (1 - (1 / 4 : ℝ) ^ (B + 1)) - X| ≤ 2 := by
  let r₃ := (1 / 3 : ℝ) ^ (A + 1)
  let r₄ := (1 / 4 : ℝ) ^ (B + 1)
  change |X * (1 - r₃) * (1 - r₄) - X| ≤ 2
  have hr₃ : 0 ≤ r₃ := by dsimp only [r₃]; positivity
  have hr₄ : 0 ≤ r₄ := by dsimp only [r₄]; positivity
  have hr₄le : r₄ ≤ 1 := by
    dsimp only [r₄]
    rw [div_pow, one_pow]
    apply (div_le_iff₀ (by positivity : 0 < (4 : ℝ) ^ (B + 1))).mpr
    simpa only [one_mul] using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4) :
      (1 : ℝ) ≤ 4 ^ (B + 1))
  have hx₃ : X * r₃ < 1 := by
    dsimp only [r₃]
    rw [div_pow, one_pow, ← mul_div_assoc, mul_one]
    exact (div_lt_iff₀ (by positivity : 0 < (3 : ℝ) ^ (A + 1))).mpr (by simpa using hA)
  have hx₄ : X * r₄ < 1 := by
    dsimp only [r₄]
    rw [div_pow, one_pow, ← mul_div_assoc, mul_one]
    exact (div_lt_iff₀ (by positivity : 0 < (4 : ℝ) ^ (B + 1))).mpr (by simpa using hB)
  have hcross : 0 ≤ X * r₃ * r₄ := mul_nonneg (mul_nonneg hX hr₃) hr₄
  have hsub : 0 ≤ X * r₃ * (1 - r₄) :=
    mul_nonneg (mul_nonneg hX hr₃) (sub_nonneg.mpr hr₄le)
  have hlast : 0 ≤ X * r₄ := mul_nonneg hX hr₄
  exact abs_le.mpr ⟨by nlinarith only [hx₃, hx₄, hcross],
    by nlinarith only [hsub, hlast]⟩

/-- A logarithmic floor gives a strict power cutoff and bounds its exponent. -/
private theorem log_floor_cutoff {b X : ℝ} (hb : 1 < b) (hX : 1 ≤ X) :
    X < b ^ (⌊Real.log X / Real.log b⌋₊ + 1) ∧
      (⌊Real.log X / Real.log b⌋₊ : ℝ) ≤ Real.log X / Real.log b := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hx0 : 0 < X := zero_lt_one.trans_le hX
  have hl : 0 < Real.log b := Real.log_pos hb
  have hr : 0 ≤ Real.log X / Real.log b := div_nonneg (Real.log_nonneg hX) hl.le
  refine ⟨?_, Nat.floor_le hr⟩
  have hf := Nat.lt_floor_add_one (Real.log X / Real.log b)
  have hg : Real.log X < ((⌊Real.log X / Real.log b⌋₊ + 1 : ℕ) : ℝ) * Real.log b := by
    push_cast
    exact (div_lt_iff₀ hl).mp hf
  calc
    X = Real.exp (Real.log X) := (Real.exp_log hx0).symm
    _ < Real.exp (((⌊Real.log X / Real.log b⌋₊ + 1 : ℕ) : ℝ) * Real.log b) :=
      Real.exp_lt_exp.mpr hg
    _ = b ^ (⌊Real.log X / Real.log b⌋₊ + 1) := by
      rw [← Real.log_pow, Real.exp_log (pow_pos hb0 _)]

/-- The actual count error is bounded by half the exponent rectangle plus two. -/
theorem count_error_rectangle {X : ℝ} (hX : 0 ≤ X) (A B : ℕ)
    (hA : X < (3 : ℝ) ^ (A + 1)) (hB : X < (4 : ℝ) ^ (B + 1)) :
    |(system.countBall X : ℝ) - X| ≤ ((A + 1 : ℕ) : ℝ) * ((B + 1 : ℕ) : ℝ) / 2 + 2 := by
  have hc : (system.countBall X : ℝ) =
      ∑ a ∈ Finset.range (A + 1), ∑ b ∈ Finset.range (B + 1),
        ((oddIntegers (X / ((3 : ℝ) ^ a * 4 ^ b))).card : ℝ) := by
    rw [countBall_eq_rectangle_sum hX A B hA hB]
    simp only [Nat.cast_sum]
  have hr := rectangle_rounding_error hX A B
  rw [rectangle_main_term] at hr
  have ht := geometric_tail hX A B hA hB
  rw [hc]
  apply abs_le.mpr
  constructor
  · linarith only [(abs_le.mp hr).1, (abs_le.mp ht).1]
  · linarith only [(abs_le.mp hr).2, (abs_le.mp ht).2]

/-- An explicit quadratic polynomial in log X bounds the slope-one counting error. -/
theorem count_error_log_bound {X : ℝ} (hX : 1 ≤ X) :
    |(system.countBall X : ℝ) - X| ≤
      (Real.log X / Real.log 3 + 1) * (Real.log X / Real.log 4 + 1) / 2 + 2 := by
  let A := ⌊Real.log X / Real.log 3⌋₊
  let B := ⌊Real.log X / Real.log 4⌋₊
  obtain ⟨hA, ha⟩ := log_floor_cutoff (by norm_num : (1 : ℝ) < 3) hX
  obtain ⟨hB, hb⟩ := log_floor_cutoff (by norm_num : (1 : ℝ) < 4) hX
  change (A : ℝ) ≤ Real.log X / Real.log 3 at ha
  change (B : ℝ) ≤ Real.log X / Real.log 4 at hb
  have hsize : ((A + 1 : ℕ) : ℝ) * ((B + 1 : ℕ) : ℝ) ≤
      (Real.log X / Real.log 3 + 1) * (Real.log X / Real.log 4 + 1) := by
    apply mul_le_mul
    · push_cast; linarith only [ha]
    · push_cast; linarith only [hb]
    · positivity
    · exact add_nonneg (div_nonneg (Real.log_nonneg hX)
        (Real.log_pos (by norm_num : (1 : ℝ) < 3)).le) (by norm_num)
  have hc := count_error_rectangle (zero_le_one.trans hX) A B hA hB
  linarith only [hc, hsize]

/-- Duplicate norm-three labels rule out a norm-preserving equivalence with rational primes. -/
theorem not_prime_equiv :
    ¬ Nonempty {e : system.Label ≃ {p : ℕ // p.Prime} //
      ∀ l, system.labelNorm l = ((e l : ℕ) : ℝ)} := by
  rintro ⟨⟨e, he⟩⟩
  let p : KeptPrime ({2} : Set ℕ) := ⟨3, by norm_num⟩
  have hnorm : system.labelNorm (Sum.inl p) = system.labelNorm (Sum.inr false) := rfl
  have hreal : ((e (Sum.inl p) : ℕ) : ℝ) = ((e (Sum.inr false) : ℕ) : ℝ) :=
    (he _).symm.trans (hnorm.trans (he _))
  have hnat : (e (Sum.inl p) : ℕ) = (e (Sum.inr false) : ℕ) := by exact_mod_cast hreal
  have heq : e (Sum.inl p) = e (Sum.inr false) := Subtype.ext hnat
  cases e.injective heq

/-- This nonclassical positive-generator system has count error O((log X)^2). -/
theorem count_error_log_sq : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, Real.exp 1 ≤ X →
    |(system.countBall X : ℝ) - X| ≤ C * (Real.log X) ^ 2 := by
  let a := 1 / Real.log 3 + 1
  let b := 1 / Real.log 4 + 1
  have hl₃ : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl₄ : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hb : 0 < b := by dsimp only [b]; positivity
  refine ⟨a * b / 2 + 2, by positivity, ?_⟩
  intro X hX
  have he : (1 : ℝ) ≤ Real.exp 1 := by
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 by norm_num))
  have hx1 : 1 ≤ X := he.trans hX
  have hlog : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hlog0 : 0 ≤ Real.log X := zero_le_one.trans hlog
  have h₃ : Real.log X / Real.log 3 + 1 ≤ a * Real.log X := by
    have hf : a * Real.log X = Real.log X / Real.log 3 + Real.log X := by dsimp only [a]; ring
    rw [hf]
    linarith only [hlog]
  have h₄ : Real.log X / Real.log 4 + 1 ≤ b * Real.log X := by
    have hf : b * Real.log X = Real.log X / Real.log 4 + Real.log X := by dsimp only [b]; ring
    rw [hf]
    linarith only [hlog]
  have hp : (Real.log X / Real.log 3 + 1) * (Real.log X / Real.log 4 + 1) ≤
      a * b * (Real.log X) ^ 2 := by
    calc
      _ ≤ (a * Real.log X) * (b * Real.log X) := mul_le_mul h₃ h₄
        (add_nonneg (div_nonneg hlog0 hl₄.le) (by norm_num)) (mul_nonneg ha.le hlog0)
      _ = _ := by ring
  have hq : 1 ≤ (Real.log X) ^ 2 := by nlinarith only [hlog]
  have hc := count_error_log_bound hx1
  calc
    _ ≤ a * b * (Real.log X) ^ 2 / 2 + 2 := by linarith only [hc, hp]
    _ ≤ (a * b / 2 + 2) * (Real.log X) ^ 2 := by nlinarith only [hq]

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount
