import GaloisForLFunctions.RHTower.MellinTrivialZeros
import GaloisForLFunctions.RHTower.BurnolRectangleResidue
import GaloisForLFunctions.RHTower.ZetaTrivialZeroSimple
import GaloisForLFunctions.HTGeometry.ZetaJetFreeness

/-!
# Orders of the continued Mellin transform

`M(f)(s) = N(s)/(s(1−s))` with `N` entire (Proposition 2.2).  This module records what the
rectangle residue identity needs about `M`:

* `M` is meromorphic everywhere and analytic away from `0` and `1`;
* its order at a trivial zero `−2k` is at least `1` (because `N` vanishes there — the `χ` factor of
  the functional equation does);
* its order at `0` is at least `0` (the singularity is removable, even though the Lean value
  `N(0)/0` is junk);
* its order at `1` is at least `−1`.

Combined with `meromorphicOrderAt riemannZeta` at the same three places (`1`, `0`, `−1`
respectively, the last from `ZetaTrivialZeroSimple`), this shows Burnol's integrand is regular at
each of them, so — exactly as the paper says — *the trivial zeros and `s = 1` contribute no
residue*.

## Main results

* `meromorphicAt_extendedMellinContinuation`, `analyticAt_extendedMellinContinuation_of_ne`
* `laurentCoeff_burnolIntegrand_extendedMellin_trivial_zero`
* `laurentCoeff_burnolIntegrand_extendedMellin_zero`, `..._one`
-/

open Complex Set Topology Filter MeasureTheory
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The denominator `s(1−s)` -/

/-- The quadratic denominator of the continued Mellin transform. -/
def mellinDenominator : ℂ → ℂ := fun s => s * (1 - s)

theorem analyticAt_mellinDenominator (p : ℂ) : AnalyticAt ℂ mellinDenominator p :=
  analyticAt_id.mul (analyticAt_const.sub analyticAt_id)

theorem meromorphicOrderAt_mellinDenominator_zero :
    meromorphicOrderAt mellinDenominator 0 = ((1 : ℤ) : WithTop ℤ) := by
  have hord : analyticOrderAt mellinDenominator 0 = ((1 : ℕ) : ℕ∞) := by
    refine ((analyticAt_mellinDenominator 0).analyticOrderAt_eq_natCast).2
      ⟨fun z : ℂ => 1 - z, analyticAt_const.sub analyticAt_id, by simp, ?_⟩
    filter_upwards with z
    simp [mellinDenominator]
  rw [(analyticAt_mellinDenominator 0).meromorphicOrderAt_eq, hord]
  simp

theorem meromorphicOrderAt_mellinDenominator_one :
    meromorphicOrderAt mellinDenominator 1 = ((1 : ℤ) : WithTop ℤ) := by
  have hord : analyticOrderAt mellinDenominator 1 = ((1 : ℕ) : ℕ∞) := by
    refine ((analyticAt_mellinDenominator 1).analyticOrderAt_eq_natCast).2
      ⟨fun z : ℂ => -z, analyticAt_id.neg, by simp, ?_⟩
    filter_upwards with z
    simp [mellinDenominator]
    ring
  rw [(analyticAt_mellinDenominator 1).meromorphicOrderAt_eq, hord]
  simp

theorem meromorphicOrderAt_mellinDenominator_of_ne {p : ℂ} (h0 : p ≠ 0) (h1 : p ≠ 1) :
    meromorphicOrderAt mellinDenominator p = (0 : WithTop ℤ) := by
  have hne : mellinDenominator p ≠ 0 := by
    rw [mellinDenominator]
    exact mul_ne_zero h0 (sub_ne_zero.2 fun h => h1 h.symm)
  rw [(analyticAt_mellinDenominator p).meromorphicOrderAt_eq,
    (analyticAt_mellinDenominator p).analyticOrderAt_eq_zero.2 hne]
  simp

/-! ## The continued Mellin transform -/

variable {a : ℝ} {f : SoninL2} {c d : ℂ}

theorem extendedMellinContinuation_eq_div (a : ℝ) (c d : ℂ) (f : SoninL2) :
    extendedMellinContinuation a c d f
      = (extendedMellinNumerator a c d f) / mellinDenominator := by
  funext s
  rw [extendedMellinContinuation, Pi.div_apply, mellinDenominator]

theorem analyticAt_extendedMellinNumerator (ha : 0 < a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d) (p : ℂ) :
    AnalyticAt ℂ (extendedMellinNumerator a c d f) p :=
  ((differentiable_extendedMellinNumerator ha hev hc hd).1).analyticAt p

theorem meromorphicAt_extendedMellinContinuation (ha : 0 < a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d) (p : ℂ) :
    MeromorphicAt (extendedMellinContinuation a c d f) p := by
  rw [extendedMellinContinuation_eq_div]
  exact (analyticAt_extendedMellinNumerator ha hev hc hd p).meromorphicAt.div
    (analyticAt_mellinDenominator p).meromorphicAt

theorem analyticAt_extendedMellinContinuation_of_ne (ha : 0 < a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {p : ℂ} (h0 : p ≠ 0) (h1 : p ≠ 1) :
    AnalyticAt ℂ (extendedMellinContinuation a c d f) p := by
  rw [extendedMellinContinuation_eq_div]
  refine (analyticAt_extendedMellinNumerator ha hev hc hd p).div
    (analyticAt_mellinDenominator p) ?_
  rw [mellinDenominator]
  exact mul_ne_zero h0 (sub_ne_zero.2 fun h => h1 h.symm)

theorem meromorphicOrderAt_extendedMellinContinuation (ha : 0 < a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d) (p : ℂ) :
    meromorphicOrderAt (extendedMellinContinuation a c d f) p
      = meromorphicOrderAt (extendedMellinNumerator a c d f) p
        - meromorphicOrderAt mellinDenominator p := by
  rw [extendedMellinContinuation_eq_div,
    meromorphicOrderAt_div (analyticAt_extendedMellinNumerator ha hev hc hd p).meromorphicAt
      (analyticAt_mellinDenominator p).meromorphicAt]

/-! ## The three regular points -/

theorem one_le_meromorphicOrderAt_extendedMellinContinuation_trivial (ha : 0 < a)
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {k : ℕ} (hk : k ≠ 0) :
    ((1 : ℤ) : WithTop ℤ)
      ≤ meromorphicOrderAt (extendedMellinContinuation a c d f) (-(2 * (k : ℂ))) := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
  have hre : (-(2 * (k : ℂ))).re = -(2 * (k : ℝ)) := by simp
  have hrelt : (-(2 * (k : ℂ))).re < 0 := by rw [hre]; linarith
  have h0 : (-(2 * (k : ℂ))) ≠ 0 := by
    intro h; rw [h] at hrelt; simp at hrelt
  have h1 : (-(2 * (k : ℂ))) ≠ 1 := by
    intro h; rw [h] at hrelt; norm_num at hrelt
  have hN : ((1 : ℤ) : WithTop ℤ)
      ≤ meromorphicOrderAt (extendedMellinNumerator a c d f) (-(2 * (k : ℂ))) :=
    one_le_meromorphicOrderAt_of_eq_zero (analyticAt_extendedMellinNumerator ha hev hc hd _)
      (extendedMellinNumerator_neg_two_mul_nat a c d f k)
  rw [meromorphicOrderAt_extendedMellinContinuation ha hev hc hd,
    meromorphicOrderAt_mellinDenominator_of_ne h0 h1, sub_zero]
  exact hN

theorem zero_le_meromorphicOrderAt_extendedMellinContinuation_zero (ha : 0 < a)
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d) :
    ((0 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (extendedMellinContinuation a c d f) 0 := by
  have hN : ((1 : ℤ) : WithTop ℤ)
      ≤ meromorphicOrderAt (extendedMellinNumerator a c d f) 0 :=
    one_le_meromorphicOrderAt_of_eq_zero (analyticAt_extendedMellinNumerator ha hev hc hd _)
      (extendedMellinNumerator_zero a c d f)
  rw [meromorphicOrderAt_extendedMellinContinuation ha hev hc hd,
    meromorphicOrderAt_mellinDenominator_zero]
  induction hx : meromorphicOrderAt (extendedMellinNumerator a c d f) 0 with
  | top => simp
  | coe n =>
      rw [hx] at hN
      have hn : (1 : ℤ) ≤ n := by exact_mod_cast hN
      have h0 : (0 : ℤ) ≤ n - 1 := by omega
      exact_mod_cast h0

theorem neg_one_le_meromorphicOrderAt_extendedMellinContinuation_one (ha : 0 < a)
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (extendedMellinContinuation a c d f) 1 := by
  have hN : ((0 : ℤ) : WithTop ℤ)
      ≤ meromorphicOrderAt (extendedMellinNumerator a c d f) 1 :=
    meromorphicOrderAt_nonneg_of_analyticAt (analyticAt_extendedMellinNumerator ha hev hc hd _)
  rw [meromorphicOrderAt_extendedMellinContinuation ha hev hc hd,
    meromorphicOrderAt_mellinDenominator_one]
  induction hx : meromorphicOrderAt (extendedMellinNumerator a c d f) 1 with
  | top => simp
  | coe n =>
      rw [hx] at hN
      have hn : (0 : ℤ) ≤ n := by exact_mod_cast hN
      have h0 : (-1 : ℤ) ≤ n - 1 := by omega
      exact_mod_cast h0

/-! ## No residue at `0`, at `1`, or at a trivial zero -/

theorem meromorphicOrderAt_riemannZeta_zero_point :
    meromorphicOrderAt riemannZeta 0 = ((0 : ℤ) : WithTop ℤ) := by
  have hana : AnalyticAt ℂ riemannZeta 0 := analyticOn_riemannZeta 0 (by norm_num)
  have hne : riemannZeta 0 ≠ 0 := by
    rw [riemannZeta_zero]
    norm_num
  rw [hana.meromorphicOrderAt_eq, hana.analyticOrderAt_eq_zero.2 hne]
  simp

variable (Z : ℂ)

/-- **The trivial zeros contribute no residue.** -/
theorem laurentCoeff_burnolIntegrand_extendedMellin_trivial (ha : 0 < a)
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {Z : ℂ} (hZ : riemannZeta Z ≠ 0) {k : ℕ} (hk : k ≠ 0) (hZk : (-(2 * (k : ℂ))) ≠ Z) :
    laurentCoeff (burnolIntegrand (extendedMellinContinuation a c d f) Z)
      (-(2 * (k : ℂ))) (-1) = 0 :=
  laurentCoeff_burnolIntegrand_eq_zero_of_order_ge
    (meromorphicAt_extendedMellinContinuation ha hev hc hd _) hZ hZk
    (meromorphicOrderAt_riemannZeta_trivial hk)
    (one_le_meromorphicOrderAt_extendedMellinContinuation_trivial ha hev hc hd hk)

/-- **The origin contributes no residue.** -/
theorem laurentCoeff_burnolIntegrand_extendedMellin_zero (ha : 0 < a)
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {Z : ℂ} (hZ : riemannZeta Z ≠ 0) (hZ0 : (0 : ℂ) ≠ Z) :
    laurentCoeff (burnolIntegrand (extendedMellinContinuation a c d f) Z) 0 (-1) = 0 :=
  laurentCoeff_burnolIntegrand_eq_zero_of_order_ge
    (meromorphicAt_extendedMellinContinuation ha hev hc hd _) hZ hZ0
    meromorphicOrderAt_riemannZeta_zero_point
    (zero_le_meromorphicOrderAt_extendedMellinContinuation_zero ha hev hc hd)

/-- **The pole of `ζ` at `s = 1` contributes no residue**: it cancels the pole of `M(f)`. -/
theorem laurentCoeff_burnolIntegrand_extendedMellin_one (ha : 0 < a)
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {Z : ℂ} (hZ : riemannZeta Z ≠ 0) (hZ1 : (1 : ℂ) ≠ Z) :
    laurentCoeff (burnolIntegrand (extendedMellinContinuation a c d f) Z) 1 (-1) = 0 :=
  laurentCoeff_burnolIntegrand_eq_zero_of_order_ge
    (meromorphicAt_extendedMellinContinuation ha hev hc hd _) hZ hZ1
    GaloisForLFunctions.meromorphicOrderAt_riemannZeta_one
    (neg_one_le_meromorphicOrderAt_extendedMellinContinuation_one ha hev hc hd)

end

end RHTower
