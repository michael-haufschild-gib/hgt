import GaloisForLFunctions.goldbach.ModularInverseRectangleCompletion
import GaloisForLFunctions.RHTower.Sieve.IntervalMultiples

/-!
# Every gcd fibre of a modular product rectangle

An arbitrary product congruence splits into disjoint unit rectangles at
the quotient moduli. The first-coordinate floor lengths are exact, so
the summed completion estimate includes every nonunit fibre and endpoint.
-/

namespace GaloisForLFunctions.Goldbach

open Finset
open scoped BigOperators

noncomputable section
set_option autoImplicit false

/-- The possible gcd labels of a product equal to `c` modulo `M`. -/
abbrev ModularProductDivisor (M : ℕ+) (c : ℕ) :=
  {g : ℕ // g ∈ (Nat.gcd (M : ℕ) c).divisors}

private theorem product_divisor_pos (M : ℕ+) (c : ℕ) (g : ModularProductDivisor M c) :
    0 < g.val := Nat.pos_of_mem_divisors g.property

private theorem product_divisor_dvd_modulus
    (M : ℕ+) (c : ℕ) (g : ModularProductDivisor M c) : g.val ∣ (M : ℕ) :=
  (Nat.dvd_of_mem_divisors g.property).trans (Nat.gcd_dvd_left (M : ℕ) c)

private theorem product_divisor_dvd_target
    (M : ℕ+) (c : ℕ) (g : ModularProductDivisor M c) : g.val ∣ c :=
  (Nat.dvd_of_mem_divisors g.property).trans (Nat.gcd_dvd_right (M : ℕ) c)

/-- The positive modulus remaining after the actual gcd label is cancelled. -/
def modularProductReducedModulus (M : ℕ+) (c : ℕ) (g : ModularProductDivisor M c) : ℕ+ :=
  ⟨(M : ℕ) / g.val, Nat.div_pos
    (Nat.le_of_dvd M.pos (product_divisor_dvd_modulus M c g))
      (product_divisor_pos M c g)⟩

/-- All pairs in the natural rectangle satisfying the original product congruence. -/
def modularProductRectanglePairs (M : ℕ+) (A H B K c : ℕ) : Finset (ℕ × ℕ) :=
  ((Ioc A (A + H)) ×ˢ (Ioc B (B + K))).filter
    (fun t : ℕ × ℕ => Nat.ModEq (M : ℕ) (t.1 * t.2) c)

/-- The unit rectangle at one gcd label, with both floor endpoints retained. -/
def modularProductUnitPairs (M : ℕ+) (A H B K c : ℕ)
    (g : ModularProductDivisor M c) : Finset (ℕ × ℕ) :=
  modularInverseRectanglePairs (modularProductReducedModulus M c g)
    ((A / g.val + 1 : ℕ) : ℤ) ((A + H) / g.val - A / g.val)
    ((B + 1 : ℕ) : ℤ) K
    ((c / g.val : ℕ) : ZMod (modularProductReducedModulus M c g : ℕ))

/-- Unit-rectangle indices lift to the actual original pair of coordinates. -/
def modularProductPairLift (M : ℕ+) (A B c : ℕ)
    (g : ModularProductDivisor M c) (t : ℕ × ℕ) : ℕ × ℕ :=
  (g.val * (A / g.val + 1 + t.1), B + 1 + t.2)

private theorem scaled_product_modEq (g : ℕ+) (M c u n : ℕ) :
    Nat.ModEq ((g : ℕ) * M) (((g : ℕ) * u) * n) ((g : ℕ) * c) ↔
      Nat.ModEq M (u * n) c := by
  change (((g : ℕ) * u) * n) % ((g : ℕ) * M) =
    ((g : ℕ) * c) % ((g : ℕ) * M) ↔ (u * n) % M = c % M
  rw [Nat.mul_assoc, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
  exact Nat.mul_left_cancel_iff g.pos

private theorem product_unit_reduction (M : ℕ+) (c : ℕ)
    (g : ModularProductDivisor M c) (u n : ℕ) :
    (IsUnit (u : ZMod (modularProductReducedModulus M c g : ℕ)) ∧
      (u : ZMod (modularProductReducedModulus M c g : ℕ)) *
        (n : ZMod (modularProductReducedModulus M c g : ℕ)) =
          (c / g.val : ℕ)) ↔
      Nat.gcd (g.val * u) (M : ℕ) = g.val ∧
        Nat.ModEq (M : ℕ) ((g.val * u) * n) c := by
  have hM : g.val * (modularProductReducedModulus M c g : ℕ) = (M : ℕ) :=
    Nat.mul_div_cancel' (product_divisor_dvd_modulus M c g)
  have hc : g.val * (c / g.val) = c :=
    Nat.mul_div_cancel' (product_divisor_dvd_target M c g)
  have hgcd : Nat.gcd (g.val * u) (M : ℕ) = g.val ↔
      Nat.Coprime u (modularProductReducedModulus M c g : ℕ) := by
    have he : Nat.gcd (g.val * u) (M : ℕ) =
        g.val * Nat.gcd u (modularProductReducedModulus M c g : ℕ) := by
      calc
        _ = Nat.gcd (g.val * u) (g.val * (modularProductReducedModulus M c g : ℕ)) :=
          congrArg (fun k : ℕ => Nat.gcd (g.val * u) k) hM.symm
        _ = _ := Nat.gcd_mul_left _ _ _
    rw [he]
    simpa only [Nat.mul_one] using
      (Nat.mul_left_cancel_iff (product_divisor_pos M c g)
        (m := Nat.gcd u (modularProductReducedModulus M c g : ℕ)) (k := 1))
  have hcong : Nat.ModEq (M : ℕ) ((g.val * u) * n) c ↔
      Nat.ModEq (modularProductReducedModulus M c g : ℕ) (u * n) (c / g.val) := by
    have he := scaled_product_modEq ⟨g.val, product_divisor_pos M c g⟩
      (modularProductReducedModulus M c g : ℕ) (c / g.val) u n
    change Nat.ModEq (g.val * (modularProductReducedModulus M c g : ℕ))
      ((g.val * u) * n) (g.val * (c / g.val)) ↔ _ at he
    rwa [hM, hc] at he
  rw [ZMod.isUnit_iff_coprime, ← Nat.cast_mul,
    ZMod.natCast_eq_natCast_iff, hgcd, hcong]

/-- Membership records the original congruence and its exact gcd label. -/
theorem modularProductUnitPairs_mem_iff (M : ℕ+) (A H B K c : ℕ)
    (g : ModularProductDivisor M c) (t : ℕ × ℕ) :
    t ∈ modularProductUnitPairs M A H B K c g ↔
      t.1 < (A + H) / g.val - A / g.val ∧ t.2 < K ∧
        Nat.gcd (g.val * (A / g.val + 1 + t.1)) (M : ℕ) = g.val ∧
          Nat.ModEq (M : ℕ)
            ((g.val * (A / g.val + 1 + t.1)) * (B + 1 + t.2)) c := by
  simp only [modularProductUnitPairs, modularInverseRectanglePairs, mem_filter,
    mem_product, mem_range, Int.cast_natCast, ← Nat.cast_add]
  rw [product_unit_reduction]
  tauto

/-- The lift preserves distinct indices at every positive gcd label. -/
theorem modularProductPairLift_injective (M : ℕ+) (A B c : ℕ)
    (g : ModularProductDivisor M c) :
    Function.Injective (modularProductPairLift M A B c g) := by
  intro x y he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  dsimp only [modularProductPairLift] at hx hy
  have heq := Nat.mul_left_cancel (product_divisor_pos M c g) hx
  exact Prod.ext (by omega) (by omega)

/-- The unrestricted rectangle is precisely the union of all reduced unit fibres. -/
theorem modularProductRectanglePairs_eq_biUnion (M : ℕ+) (A H B K c : ℕ) :
    modularProductRectanglePairs M A H B K c =
      univ.biUnion (fun g : ModularProductDivisor M c =>
        (modularProductUnitPairs M A H B K c g).image (modularProductPairLift M A B c g)) := by
  classical
  ext x
  rw [mem_biUnion]
  simp only [mem_univ, true_and]
  constructor
  · intro hx
    rcases mem_filter.mp hx with ⟨hbox, hcong⟩
    rcases mem_product.mp hbox with ⟨hm, hn⟩
    rcases mem_Ioc.mp hm with ⟨hmlo, hmhi⟩
    rcases mem_Ioc.mp hn with ⟨hnlo, hnhi⟩
    let d : ℕ := Nat.gcd x.1 (M : ℕ)
    have hd : 0 < d := Nat.gcd_pos_of_pos_right x.1 M.pos
    have hdm : d ∣ x.1 := Nat.gcd_dvd_left x.1 (M : ℕ)
    have hdM : d ∣ (M : ℕ) := Nat.gcd_dvd_right x.1 (M : ℕ)
    have hdc : d ∣ c := (hcong.dvd_iff hdM).mp (dvd_mul_of_dvd_left hdm x.2)
    let g : ModularProductDivisor M c := ⟨d, Nat.mem_divisors.mpr
      ⟨Nat.dvd_gcd hdM hdc, (Nat.gcd_pos_of_pos_left c M.pos).ne'⟩⟩
    have hmfac : g.val * (x.1 / g.val) = x.1 := Nat.mul_div_cancel' hdm
    have hulo : A / g.val < x.1 / g.val := by
      apply (Nat.div_lt_iff_lt_mul hd).mpr
      change A < (x.1 / g.val) * g.val
      rw [Nat.mul_comm, hmfac]
      exact hmlo
    have huhi : x.1 / g.val ≤ (A + H) / g.val := by
      apply (Nat.le_div_iff_mul_le hd).mpr
      change (x.1 / g.val) * g.val ≤ A + H
      rw [Nat.mul_comm, hmfac]
      exact hmhi
    let j : ℕ := x.1 / g.val - (A / g.val + 1)
    let k : ℕ := x.2 - (B + 1)
    have hj : j < (A + H) / g.val - A / g.val := by dsimp [j]; omega
    have hk : k < K := by dsimp [k]; omega
    have hju : A / g.val + 1 + j = x.1 / g.val := by dsimp [j]; omega
    have hkn : B + 1 + k = x.2 := by dsimp [k]; omega
    have hjm : g.val * (A / g.val + 1 + j) = x.1 := by rw [hju, hmfac]
    refine ⟨g, mem_image.mpr ⟨(j, k), ?_, ?_⟩⟩
    · apply (modularProductUnitPairs_mem_iff M A H B K c g (j, k)).mpr
      refine ⟨hj, hk, ?_, ?_⟩
      · change Nat.gcd (g.val * (A / g.val + 1 + j)) (M : ℕ) = g.val
        rw [hjm]
      · change Nat.ModEq (M : ℕ) ((g.val * (A / g.val + 1 + j)) * (B + 1 + k)) c
        rwa [hjm, hkn]
    · exact Prod.ext hjm hkn
  · rintro ⟨g, hx⟩
    rcases mem_image.mp hx with ⟨t, ht, rfl⟩
    obtain ⟨hj, hk, _, hcong⟩ := (modularProductUnitPairs_mem_iff M A H B K c g t).mp ht
    have hg := product_divisor_pos M c g
    have hfloor : A / g.val ≤ (A + H) / g.val := Nat.div_le_div_right (by omega)
    have hulo : A / g.val < A / g.val + 1 + t.1 := by omega
    have huhi : A / g.val + 1 + t.1 ≤ (A + H) / g.val := by omega
    have hmlo : A < g.val * (A / g.val + 1 + t.1) := by
      simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hg).mp hulo
    have hmhi : g.val * (A / g.val + 1 + t.1) ≤ A + H := by
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hg).mp huhi
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_Ioc.mpr ⟨hmlo, hmhi⟩, ?_⟩, hcong⟩
    exact mem_Ioc.mpr ⟨by change B < B + 1 + t.2; omega,
      by change B + 1 + t.2 ≤ B + K; omega⟩

/-- Disjointness follows from the actual first coordinate's unique gcd label. -/
theorem modularProductRectanglePairs_card (M : ℕ+) (A H B K c : ℕ) :
    (modularProductRectanglePairs M A H B K c).card =
      ∑ g : ModularProductDivisor M c, (modularProductUnitPairs M A H B K c g).card := by
  classical
  rw [modularProductRectanglePairs_eq_biUnion, card_biUnion]
  · apply sum_congr rfl
    intro g _
    exact card_image_of_injective _ (modularProductPairLift_injective M A B c g)
  · intro g _ h _ hne
    apply disjoint_left.mpr
    intro x hxg hxh
    rcases mem_image.mp hxg with ⟨u, hu, hux⟩
    rcases mem_image.mp hxh with ⟨v, hv, hvx⟩
    have hgu : Nat.gcd (modularProductPairLift M A B c g u).1 (M : ℕ) = g.val :=
      ((modularProductUnitPairs_mem_iff M A H B K c g u).mp hu).2.2.1
    have hhv : Nat.gcd (modularProductPairLift M A B c h v).1 (M : ℕ) = h.val :=
      ((modularProductUnitPairs_mem_iff M A H B K c h v).mp hv).2.2.1
    rw [hux] at hgu
    rw [hvx] at hhv
    exact hne (Subtype.ext (hgu.symm.trans hhv))

/-- The discrete main term retains the exact first-coordinate floor length in every fibre. -/
def modularProductRectangleMain (M : ℕ+) (A H K c : ℕ) : ℝ :=
  ∑ g : ModularProductDivisor M c,
    (Nat.totient (modularProductReducedModulus M c g : ℕ) : ℝ) *
      (((A + H) / g.val - A / g.val : ℕ) : ℝ) * (K : ℝ) /
        (modularProductReducedModulus M c g : ℝ) ^ 2

/-- The sum of the exact completion budgets of all nonunit fibres. -/
def modularProductRectangleError (M : ℕ+) (A H K c : ℕ) : ℝ :=
  ∑ g : ModularProductDivisor M c,
    let Q : ℕ+ := modularProductReducedModulus M c g
    let L : ℕ := (A + H) / g.val - A / g.val
    let delta : ℕ := Nat.gcd (Q : ℕ) (((c / g.val : ℕ) : ZMod (Q : ℕ)).val)
    24 * ((Q : ℕ).divisors.card : ℝ) * (Q : ℝ) ^ (2 / 3 : ℝ) *
        (delta : ℝ) ^ (1 / 3 : ℝ) * (1 + Real.log (Q : ℝ)) ^ 2 +
      ((Q : ℕ).divisors.card : ℝ) * (1 + Real.log (Q : ℝ)) *
        ((L : ℝ) * (delta : ℝ) + (K : ℝ)) / (Q : ℝ)

/-- Unrestricted product rectangles inherit the sum of all unit-fibre completion bounds. -/
theorem modularProductRectanglePairs_error_le (M : ℕ+) (A H B K c : ℕ) :
    |((modularProductRectanglePairs M A H B K c).card : ℝ) -
        modularProductRectangleMain M A H K c| ≤
      modularProductRectangleError M A H K c := by
  rw [modularProductRectanglePairs_card, Nat.cast_sum,
    modularProductRectangleMain, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro g _
  exact modularInverseRectanglePairs_error_le (modularProductReducedModulus M c g)
    ((A / g.val + 1 : ℕ) : ℤ) ((A + H) / g.val - A / g.val)
    ((B + 1 : ℕ) : ℤ) K
    ((c / g.val : ℕ) : ZMod (modularProductReducedModulus M c g : ℕ))

/-- The full arithmetic density of an unrestricted modular product rectangle. -/
def modularProductRectangleDensity (M : ℕ+) (c : ℕ) : ℝ :=
  ∑ g : ModularProductDivisor M c,
    (Nat.totient (modularProductReducedModulus M c g : ℕ) : ℝ) /
      ((M : ℝ) * (modularProductReducedModulus M c g : ℝ))

/-- The exact cost of replacing first-coordinate floor lengths by real lengths. -/
def modularProductRectangleRounding (M : ℕ+) (K c : ℕ) : ℝ :=
  ∑ g : ModularProductDivisor M c,
    (Nat.totient (modularProductReducedModulus M c g : ℕ) : ℝ) * (K : ℝ) /
      (modularProductReducedModulus M c g : ℝ) ^ 2

/-- Each floor difference costs at most one reduced first-coordinate position. -/
theorem modularProductRectangleMain_area_error_le (M : ℕ+) (A H K c : ℕ) :
    |modularProductRectangleMain M A H K c -
        modularProductRectangleDensity M c * (H : ℝ) * (K : ℝ)| ≤
      modularProductRectangleRounding M K c := by
  rw [modularProductRectangleMain, modularProductRectangleDensity,
    sum_mul, sum_mul, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro g _
  have hg : 0 < g.val := product_divisor_pos M c g
  have hab : A ≤ A + H := by omega
  have hr := RHTower.Sieve.abs_card_filter_dvd_Ioc_sub_lt g.val A (A + H) hg hab
  rw [RHTower.Sieve.card_filter_dvd_Ioc g.val A (A + H) hab] at hr
  have hround : |(((A + H) / g.val - A / g.val : ℕ) : ℝ) - (H : ℝ) / (g.val : ℝ)| ≤ 1 := by
    simpa only [Nat.cast_add, add_sub_cancel_left] using hr.le
  have hgR : (0 : ℝ) < (g.val : ℝ) := by exact_mod_cast hg
  have hQ : (0 : ℝ) < (modularProductReducedModulus M c g : ℝ) := by
    exact_mod_cast (modularProductReducedModulus M c g).pos
  have hM : (g.val : ℝ) * (modularProductReducedModulus M c g : ℝ) = (M : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' (product_divisor_dvd_modulus M c g)
  have he :
      (Nat.totient (modularProductReducedModulus M c g : ℕ) : ℝ) *
          (((A + H) / g.val - A / g.val : ℕ) : ℝ) * (K : ℝ) /
            (modularProductReducedModulus M c g : ℝ) ^ 2 -
        (Nat.totient (modularProductReducedModulus M c g : ℕ) : ℝ) /
          ((M : ℝ) * (modularProductReducedModulus M c g : ℝ)) * (H : ℝ) * (K : ℝ) =
      ((Nat.totient (modularProductReducedModulus M c g : ℕ) : ℝ) * (K : ℝ) /
        (modularProductReducedModulus M c g : ℝ) ^ 2) *
          ((((A + H) / g.val - A / g.val : ℕ) : ℝ) - (H : ℝ) / (g.val : ℝ)) := by
    rw [← hM]
    field_simp [hgR.ne', hQ.ne']
  have hw : 0 ≤ (Nat.totient (modularProductReducedModulus M c g : ℕ) : ℝ) * (K : ℝ) /
      (modularProductReducedModulus M c g : ℝ) ^ 2 := by positivity
  rw [he, abs_mul, abs_of_nonneg hw]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hround hw

/-- The area estimate pays both all nonunit completion errors and all floor roundings. -/
theorem modularProductRectanglePairs_area_error_le (M : ℕ+) (A H B K c : ℕ) :
    |((modularProductRectanglePairs M A H B K c).card : ℝ) -
        modularProductRectangleDensity M c * (H : ℝ) * (K : ℝ)| ≤
      modularProductRectangleError M A H K c + modularProductRectangleRounding M K c := by
  exact (abs_sub_le ((modularProductRectanglePairs M A H B K c).card : ℝ)
    (modularProductRectangleMain M A H K c)
    (modularProductRectangleDensity M c * (H : ℝ) * (K : ℝ))).trans
      (add_le_add (modularProductRectanglePairs_error_le M A H B K c)
        (modularProductRectangleMain_area_error_le M A H K c))

end
end GaloisForLFunctions.Goldbach
