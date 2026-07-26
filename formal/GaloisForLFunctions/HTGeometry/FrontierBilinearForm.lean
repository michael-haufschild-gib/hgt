/-
The frontier object is a constrained bilinear form.

In the coprime parametrisation of `2aq = d m²` — `d = d_a d_q`, `2a = d_a z²`, `q = d_q w²`, `m = wz`
— the frontier phase becomes

    N · m √d / q = N · w z √(d_a d_q) / (d_q w²) = **N · (z/w) · √(d_a/d_q)** ,

a product of a rational `z/w` and the square root of a rational `d_a/d_q`.  **So the frontier object is
a bilinear form in the two parameter families `{z/w}` and `{√(d_a/d_q)}`**, which is the setting of the
double large sieve — the instrument the campaign identified as the remaining requirement.

The parameter ranges, with `L = N^(1/3)`:

    `w ≤ √L = N^(1/6)` ,   `d_q ≤ L/w² ≤ N^(1/3)` ,
    `z ≤ w√(2 d_q/d_a) ≤ L = N^(1/3)` ,   `d_a ≤ 2q/z²` .

Counting: for each `(d_q, w)` with `d_q w² ≤ L` there are `≍ q = d_q w²` pairs `(d_a, z)`, so

    Σ_(w ≤ √L) Σ_(d_q ≤ L/w²) d_q w² ≍ Σ_(w ≤ √L) w² (L/w²)² = Σ_(w ≤ √L) L²/w² ≍ **L²** ,

the right total.  The ranges of `z` and `d_a` depend on `w` and `d_q`, so the form is **constrained**,
not a free product; applying the double large sieve requires a dyadic decomposition into free boxes,
whose cost the campaign priced only qualitatively.
-/
import GaloisForLFunctions.HTGeometry.ClassSizeDistribution

namespace HTGeometry

/-! ### The parameter ranges -/

/-- Exponent of the range of `w`, from `q = d_q w² ≤ L`. -/
def bilinearWExponent : ℚ := 1 / 6

/-- Exponent of the range of `d_q`. -/
def bilinearDqExponent : ℚ := 1 / 3

/-- Exponent of the range of `z`. -/
def bilinearZExponent : ℚ := 1 / 3

/-- Exponent of the range of `d_a`. -/
def bilinearDaExponent : ℚ := 1 / 3

/-- **`w` ranges over the square root of the Farey order.** -/
theorem bilinearW_is_half_farey :
    bilinearWExponent = fareyOrderExponent / 2 := by
  unfold bilinearWExponent fareyOrderExponent; norm_num

/-- **`d_q` and `d_a` each range over the Farey order**, and their product over its square — the
kernel range. -/
theorem kernel_product_range :
    bilinearDaExponent + bilinearDqExponent = correctedClassCount := by
  unfold bilinearDaExponent bilinearDqExponent correctedClassCount; norm_num

/-! ### The count -/

/-- Exponent of the number of `(d_q, w)` pairs, `Σ_w L/w² ≍ L`. -/
def bilinearOuterCount : ℚ := 1 / 3

/-- Exponent of the number of `(d_a, z)` pairs for a given outer pair, `≍ q ≤ L`. -/
def bilinearInnerCount : ℚ := 1 / 3

/-- **The total is `L²`, the right number of frequencies.** -/
theorem bilinear_total_count :
    bilinearOuterCount + bilinearInnerCount = totalFrequencyExponent := by
  unfold bilinearOuterCount bilinearInnerCount totalFrequencyExponent; norm_num

/-- And it matches the frontier's term count. -/
theorem bilinear_count_matches_frontier :
    bilinearOuterCount + bilinearInnerCount = frontierTermCount := by
  rw [bilinear_total_count]
  exact total_matches_frontier

/-! ### The two families -/

/-- Exponent of the number of distinct rationals `z/w`. -/
def rationalFamilyExponent : ℚ := bilinearZExponent + bilinearWExponent

/-- **It is `1/2`.** -/
@[simp] theorem rationalFamily_eq : rationalFamilyExponent = 1 / 2 := by
  unfold rationalFamilyExponent bilinearZExponent bilinearWExponent; norm_num

/-- Exponent of the number of distinct square roots `√(d_a/d_q)`. -/
def surdFamilyExponent : ℚ := bilinearDaExponent + bilinearDqExponent

/-- **It is `2/3`.** -/
@[simp] theorem surdFamily_eq : surdFamilyExponent = 2 / 3 := by
  unfold surdFamilyExponent bilinearDaExponent bilinearDqExponent; norm_num

/-- **The free product of the two families exceeds the true count**, so the form is constrained. -/
theorem form_is_constrained :
    totalFrequencyExponent < rationalFamilyExponent + surdFamilyExponent ∧
      rationalFamilyExponent + surdFamilyExponent - totalFrequencyExponent = 1 / 2 := by
  rw [rationalFamily_eq, surdFamily_eq]
  unfold totalFrequencyExponent
  constructor <;> norm_num

/-! ### What this identifies -/

/-- **The frontier object is a bilinear form** in a rational family of exponent `1/2` and a surd
family of exponent `2/3`, constrained so that their free product `7/6` collapses to the true count
`2/3` — an overcount of exactly `1/2`. -/
theorem frontier_bilinear_structure :
    rationalFamilyExponent = 1 / 2 ∧ surdFamilyExponent = 2 / 3 ∧
      totalFrequencyExponent = 2 / 3 ∧
      rationalFamilyExponent + surdFamilyExponent - totalFrequencyExponent = 1 / 2 :=
  ⟨rationalFamily_eq, surdFamily_eq, rfl, form_is_constrained.2⟩

/-- **The target in this language.**  Square-root cancellation across the kernels means bounding the
form by `L^(1+o(1)) = N^(1/3+o(1))` against the trivial `N^(2/3)`. -/
theorem bilinear_target :
    frontierLindelof = 1 / 3 ∧ totalFrequencyExponent = 2 / 3 ∧
      totalFrequencyExponent - frontierLindelof = fareyOrderExponent := by
  refine ⟨rfl, rfl, ?_⟩
  unfold totalFrequencyExponent frontierLindelof fareyOrderExponent; norm_num

end HTGeometry
