import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCountRiesz
import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCountProfile

/-!
# The continuous profile of the actual positive-model count

The norm-coordinate bijection preserves arbitrary weights. Applied to the first
count average, it gives a finite sum of norm-four profiles over powers of three.
The normalized deficit differs from the corresponding periodic-profile sum by
at most five eighths.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount

private def taggedFibres (X : ℝ) (A B : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (A + 1) ×ˢ Finset.range (B + 1)).biUnion fun ab =>
    (oddIntegers (X / ((3 : ℝ) ^ ab.1 * 4 ^ ab.2))).image fun u => (u, ab)

private theorem taggedFibres_disjoint (X : ℝ) (A B : ℕ) :
    ((Finset.range (A + 1) ×ˢ Finset.range (B + 1) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).PairwiseDisjoint
      (fun ab => (oddIntegers (X / ((3 : ℝ) ^ ab.1 * 4 ^ ab.2))).image fun u => (u, ab)) := by
  intro ab _ cd _ hne
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hv
  obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hw
  exact hne (congrArg Prod.snd (hu.trans hw.symm))

private theorem card_taggedFibres (X : ℝ) (A B : ℕ) :
    (taggedFibres X A B).card =
      ∑ a ∈ Finset.range (A + 1), ∑ b ∈ Finset.range (B + 1),
        (oddIntegers (X / ((3 : ℝ) ^ a * 4 ^ b))).card := by
  rw [taggedFibres, Finset.card_biUnion (taggedFibres_disjoint X A B), Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact Finset.card_image_of_injective _ (fun u v huv => congrArg Prod.fst huv)

private theorem taggedFibres_eq {X : ℝ} (hX : 0 ≤ X) (A B : ℕ)
    (hA : X < (3 : ℝ) ^ (A + 1)) (hB : X < (4 : ℝ) ^ (B + 1)) :
    taggedFibres X A B = (tripleSet_finite X).toFinset := by
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨ab, _, hv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    have hd : 0 < (3 : ℝ) ^ ab.1 * 4 ^ ab.2 := by positivity
    obtain ⟨huo, huX⟩ := (mem_oddIntegers (div_nonneg hX hd.le) u).mp hu
    apply (tripleSet_finite X).mem_toFinset.mpr
    refine ⟨huo, ?_⟩
    simpa only [mul_assoc] using (le_div_iff₀ hd).mp huX
  · have hc := countBall_eq_rectangle_sum hX A B hA hB
    rw [countBall_eq_ncard_triples, ← card_taggedFibres] at hc
    rw [Set.ncard_eq_toFinset_card _ (tripleSet_finite X)] at hc
    exact hc.le

/-- The actual coordinate bijection preserves every weight depending on the norm. -/
theorem sum_normBall_eq_rectangle {M : Type*} [AddCommMonoid M]
    (φ : ℝ → M) {X : ℝ} (hX : 0 ≤ X) (A B : ℕ)
    (hA : X < (3 : ℝ) ^ (A + 1)) (hB : X < (4 : ℝ) ^ (B + 1)) :
    (∑ g ∈ (isDiscrete X).toFinset, φ (system.intNorm g)) =
      ∑ a ∈ Finset.range (A + 1), ∑ b ∈ Finset.range (B + 1),
        ∑ u ∈ oddIntegers (X / ((3 : ℝ) ^ a * 4 ^ b)),
          φ ((u : ℝ) * (3 : ℝ) ^ a * 4 ^ b) := by
  have him : (isDiscrete X).toFinset.image coordinates = (tripleSet_finite X).toFinset := by
    ext v
    simp only [Finset.mem_image, Set.Finite.mem_toFinset]
    rw [tripleSet_eq_image]
    rfl
  have hsum : (∑ g ∈ (isDiscrete X).toFinset, φ (system.intNorm g)) =
      ∑ v ∈ (tripleSet_finite X).toFinset,
        φ ((v.1 : ℝ) * 3 ^ v.2.1 * 4 ^ v.2.2) := by
    rw [← him, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro g _
      rw [intNorm_coordinates]
    · intro g _ g' _ he
      exact coordinates_injective he
  rw [hsum, ← taggedFibres_eq hX A B hA hB, taggedFibres,
    Finset.sum_biUnion (taggedFibres_disjoint X A B), Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_image]
  intro u _ v _ he
  exact congrArg Prod.fst he

private theorem first_odds_sum (J : ℕ) :
    (∑ j ∈ Finset.range J, (2 * j + 1 : ℝ)) = (J : ℝ) ^ 2 := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The continuous midpoint formula is the actual weighted odd-integer count. -/
theorem oddArea_eq_sum {Y : ℝ} (hY : 0 ≤ Y) :
    oddArea Y = ∑ u ∈ oddIntegers Y, (Y - (u : ℝ)) := by
  rw [oddArea_eq_floor hY, oddIntegers, Finset.sum_image]
  · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, first_odds_sum]
  · intro a _ b _ he
    change 2 * a + 1 = 2 * b + 1 at he
    omega

private theorem rieszCount_eq_rectangle_area {X : ℝ} (hX : 0 ≤ X) (A B : ℕ)
    (hA : X < (3 : ℝ) ^ (A + 1)) (hB : X < (4 : ℝ) ^ (B + 1)) :
    rieszCount X = ∑ a ∈ Finset.range (A + 1), ∑ b ∈ Finset.range (B + 1),
      ((3 : ℝ) ^ a * 4 ^ b) * oddArea (X / ((3 : ℝ) ^ a * 4 ^ b)) := by
  rw [rieszCount, sum_normBall_eq_rectangle (fun t => X - t) hX A B hA hB]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [oddArea_eq_sum (show 0 ≤ X / ((3 : ℝ) ^ a * 4 ^ b) by positivity), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  field_simp

/-- The actual weighted norm count splits into its norm-three exponent and norm-four profile. -/
theorem rieszCount_eq_three_sum {X : ℝ} (hX : 0 ≤ X) (A : ℕ)
    (hA : X < (3 : ℝ) ^ (A + 1)) :
    rieszCount X = ∑ a ∈ Finset.range (A + 1), (3 : ℝ) ^ a * fourArea (X / (3 : ℝ) ^ a) := by
  obtain ⟨B, hBX⟩ := pow_unbounded_of_one_lt X (by norm_num : (1 : ℝ) < 4)
  have hB : X < (4 : ℝ) ^ (B + 1) := hBX.trans_le
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (Nat.le_succ B))
  rw [rieszCount_eq_rectangle_area hX A B hA hB]
  apply Finset.sum_congr rfl
  intro a _
  have ha : (1 : ℝ) ≤ (3 : ℝ) ^ a := one_le_pow₀ (by norm_num)
  have hY : 0 ≤ X / (3 : ℝ) ^ a := by positivity
  have hYX : X / (3 : ℝ) ^ a ≤ X := by
    apply (div_le_iff₀ (by positivity : 0 < (3 : ℝ) ^ a)).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ha hX
  have hcut : |X / (3 : ℝ) ^ a| ≤ (4 : ℝ) ^ (B + 1) := by
    rw [abs_of_nonneg hY]
    exact (hYX.trans_lt hB).le
  rw [fourArea_eq_sum (B + 1) hcut, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [div_mul_eq_div_div, mul_assoc]


private theorem three_quadratic_main (X : ℝ) (A : ℕ) :
    (∑ a ∈ Finset.range (A + 1), X ^ 2 / (3 * (3 : ℝ) ^ a)) =
      X ^ 2 / 2 - X ^ 2 / (2 * (3 : ℝ) ^ (A + 1)) := by
  have he : (∑ a ∈ Finset.range (A + 1), X ^ 2 / (3 * (3 : ℝ) ^ a)) =
      X ^ 2 / 3 * ∑ a ∈ Finset.range (A + 1), (1 / 3 : ℝ) ^ a := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [div_pow, one_pow]
    ring
  rw [he, geom_sum_eq (by norm_num : (1 / 3 : ℝ) ≠ 1)]
  norm_num
  rw [div_pow, one_pow]
  field_simp
  ring

/-- The actual normalized deficit differs from its finite profile sum by at most five eighths. -/
theorem normalized_deficit_profile_error {X : ℝ} (hX : 1 ≤ X) (A : ℕ)
    (hAlo : (3 : ℝ) ^ A ≤ X) (hAhi : X < (3 : ℝ) ^ (A + 1)) :
    |(X ^ 2 / 2 - rieszCount X) / X -
      ∑ a ∈ Finset.range (A + 1), fourProfile (X / (3 : ℝ) ^ a)| ≤ 5 / 8 := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hterm (a : ℕ) :
      0 ≤ X * fourProfile (X / (3 : ℝ) ^ a) -
        (3 : ℝ) ^ a * fourDeficit (X / (3 : ℝ) ^ a) ∧
      X * fourProfile (X / (3 : ℝ) ^ a) -
        (3 : ℝ) ^ a * fourDeficit (X / (3 : ℝ) ^ a) ≤ (3 : ℝ) ^ a / 12 := by
    have hp : 0 < (3 : ℝ) ^ a := by positivity
    have h := fourProfile_approx (show 0 < X / (3 : ℝ) ^ a by positivity)
    have he : (3 : ℝ) ^ a * ((X / (3 : ℝ) ^ a) * fourProfile (X / (3 : ℝ) ^ a) -
        fourDeficit (X / (3 : ℝ) ^ a)) =
        X * fourProfile (X / (3 : ℝ) ^ a) -
          (3 : ℝ) ^ a * fourDeficit (X / (3 : ℝ) ^ a) := by
      field_simp
    rw [← he]
    constructor
    · exact mul_nonneg hp.le h.1
    · simpa only [mul_one_div] using mul_le_mul_of_nonneg_left h.2 hp.le
  have he0 : 0 ≤ X * (∑ a ∈ Finset.range (A + 1), fourProfile (X / (3 : ℝ) ^ a)) -
      ∑ a ∈ Finset.range (A + 1), (3 : ℝ) ^ a * fourDeficit (X / (3 : ℝ) ^ a) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg (fun a _ => (hterm a).1)
  have he1 : X * (∑ a ∈ Finset.range (A + 1), fourProfile (X / (3 : ℝ) ^ a)) -
      (∑ a ∈ Finset.range (A + 1), (3 : ℝ) ^ a * fourDeficit (X / (3 : ℝ) ^ a)) ≤ X / 8 := by
    calc
      _ = ∑ a ∈ Finset.range (A + 1), (X * fourProfile (X / (3 : ℝ) ^ a) -
          (3 : ℝ) ^ a * fourDeficit (X / (3 : ℝ) ^ a)) := by
        rw [Finset.mul_sum, Finset.sum_sub_distrib]
      _ ≤ ∑ a ∈ Finset.range (A + 1), (3 : ℝ) ^ a / 12 :=
        Finset.sum_le_sum (fun a _ => (hterm a).2)
      _ = ((3 : ℝ) ^ (A + 1) - 1) / 24 := by
        rw [← Finset.sum_div, geom_sum_eq (by norm_num : (3 : ℝ) ≠ 1)]
        norm_num
        ring
      _ ≤ X / 8 := by
        have hp := mul_le_mul_of_nonneg_right hAlo (by norm_num : (0 : ℝ) ≤ 3)
        rw [← pow_succ] at hp
        linarith only [hp]
  have hsum : (∑ a ∈ Finset.range (A + 1), (3 : ℝ) ^ a * fourDeficit (X / (3 : ℝ) ^ a)) =
      X ^ 2 / 2 - X ^ 2 / (2 * (3 : ℝ) ^ (A + 1)) - rieszCount X := by
    rw [← three_quadratic_main, rieszCount_eq_three_sum hX0.le A hAhi,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [fourDeficit]
    field_simp
  rw [hsum] at he0 he1
  have ht0 : 0 ≤ X ^ 2 / (2 * (3 : ℝ) ^ (A + 1)) := by positivity
  have ht1 : X ^ 2 / (2 * (3 : ℝ) ^ (A + 1)) ≤ X / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (3 : ℝ) ^ (A + 1))).mpr
    have h := mul_nonneg hX0.le (sub_nonneg.mpr hAhi.le)
    nlinarith only [h]
  have hnum : |(X ^ 2 / 2 - rieszCount X) -
      X * (∑ a ∈ Finset.range (A + 1), fourProfile (X / (3 : ℝ) ^ a))| ≤ (5 / 8) * X := by
    apply abs_le.mpr
    constructor <;> linarith only [he0, he1, ht0, ht1, hX0]
  have he : (X ^ 2 / 2 - rieszCount X) / X -
      (∑ a ∈ Finset.range (A + 1), fourProfile (X / (3 : ℝ) ^ a)) =
      ((X ^ 2 / 2 - rieszCount X) -
        X * (∑ a ∈ Finset.range (A + 1), fourProfile (X / (3 : ℝ) ^ a))) / X := by
    field_simp
  rw [he, abs_div, abs_of_pos hX0]
  exact (div_le_iff₀ hX0).mpr hnum


end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount
