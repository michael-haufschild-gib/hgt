import GaloisForLFunctions.RHTower.BurnolCompletenessUnit
import GaloisForLFunctions.RHTower.SoninCarrierMellinOrder
import GaloisForLFunctions.RHTower.TwoPointShiftFactor

/-!
# Completeness after omitting two top-order evaluators

Burnol's Proposition 6.5: at the critical aperture the Sonine space `K₁` is still spanned by the
evaluators after two of them — the top-order evaluators at two nontrivial zeros, or the two
top-order evaluators at a single zero of multiplicity at least two — have been removed.

Orthogonality to the shortened list says that `ζ` divides `M(f)·(s − ρ₁)(s − ρ₂)` at every
nontrivial zero.  Since a genuine Sonine vector has `M(f)(0) = 0` and no pole at `s = 1`, the
function

`θ(s) = M(f)(s)·(s − ρ₁)(s − ρ₂)/(s(s − 1)ζ(s))`

is entire; it obeys the same three boundary estimates as `M(f)/ζ` up to the bounded rational factor,
hence is a polynomial, and it tends to `0` along the positive real axis because the rational factor
tends to `1`.  So `θ = 0` and `f = 0`.

## Main results

* `soninTwoPointMellin`
* `zero_le_meromorphicOrderAt_burnolQuotient_soninTwoPointMellin`
-/

open Complex Set Topology Filter MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℝ} {f : SoninL2} {ρ₁ ρ₂ : ℂ}

/-- The continued Mellin transform of a Sonine vector, corrected by the rational factor
`(s − ρ₁)(s − ρ₂)/(s(s − 1))`. -/
def soninTwoPointMellin (a : ℝ) (f : SoninL2) (ρ₁ ρ₂ : ℂ) : ℂ → ℂ :=
  fun s => extendedMellinContinuation a 0 0 f s * twoPointShift ρ₁ ρ₂ s

/-! ## Orders of the rational factor -/

theorem neg_one_le_meromorphicOrderAt_twoPointShift_zero (ρ₁ ρ₂ : ℂ) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (twoPointShift ρ₁ ρ₂) 0 := by
  rw [meromorphicOrderAt_twoPointShift, meromorphicOrderAt_twoPointDenom_zero]
  have h := zero_le_meromorphicOrderAt_twoPointNumer ρ₁ ρ₂ 0
  induction hx : meromorphicOrderAt (twoPointNumer ρ₁ ρ₂) 0 with
  | top => simp
  | coe n =>
      rw [hx] at h
      have hn : (0 : ℤ) ≤ n := by exact_mod_cast h
      have : (-1 : ℤ) ≤ n - 1 := by omega
      exact_mod_cast this

theorem neg_one_le_meromorphicOrderAt_twoPointShift_one (ρ₁ ρ₂ : ℂ) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (twoPointShift ρ₁ ρ₂) 1 := by
  rw [meromorphicOrderAt_twoPointShift, meromorphicOrderAt_twoPointDenom_one]
  have h := zero_le_meromorphicOrderAt_twoPointNumer ρ₁ ρ₂ 1
  induction hx : meromorphicOrderAt (twoPointNumer ρ₁ ρ₂) 1 with
  | top => simp
  | coe n =>
      rw [hx] at h
      have hn : (0 : ℤ) ≤ n := by exact_mod_cast h
      have : (-1 : ℤ) ≤ n - 1 := by omega
      exact_mod_cast this

theorem meromorphicOrderAt_twoPointShift_of_ne {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) (ρ₁ ρ₂ : ℂ) :
    meromorphicOrderAt (twoPointShift ρ₁ ρ₂) z = meromorphicOrderAt (twoPointNumer ρ₁ ρ₂) z := by
  rw [meromorphicOrderAt_twoPointShift, meromorphicOrderAt_twoPointDenom_of_ne h0 h1, sub_zero]

theorem zero_le_meromorphicOrderAt_twoPointShift_of_ne {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1)
    (ρ₁ ρ₂ : ℂ) : (0 : WithTop ℤ) ≤ meromorphicOrderAt (twoPointShift ρ₁ ρ₂) z := by
  rw [meromorphicOrderAt_twoPointShift_of_ne h0 h1]
  exact zero_le_meromorphicOrderAt_twoPointNumer ρ₁ ρ₂ z

/-! ## Meromorphy and the order of the corrected transform -/

theorem meromorphicAt_soninTwoPointMellin (ha : 0 < a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = 0)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = 0) (z : ℂ) :
    MeromorphicAt (soninTwoPointMellin a f ρ₁ ρ₂) z :=
  (meromorphicAt_extendedMellinContinuation ha hev hc hd z).mul
    (meromorphicAt_twoPointShift ρ₁ ρ₂ z)

theorem meromorphicOrderAt_soninTwoPointMellin (ha : 0 < a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = 0)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = 0) (z : ℂ) :
    meromorphicOrderAt (soninTwoPointMellin a f ρ₁ ρ₂) z
      = meromorphicOrderAt (extendedMellinContinuation a 0 0 f) z
        + meromorphicOrderAt (twoPointShift ρ₁ ρ₂) z := by
  have h := meromorphicOrderAt_mul (f := extendedMellinContinuation a 0 0 f)
    (g := twoPointShift ρ₁ ρ₂) (x := z)
    (meromorphicAt_extendedMellinContinuation ha hev hc hd z) (meromorphicAt_twoPointShift ρ₁ ρ₂ z)
  rw [← h]
  rfl

/-- **`ζ` divides the corrected transform at every point of the plane.** -/
theorem meromorphicOrderAt_riemannZeta_le_soninTwoPointMellin (ha : 0 < a)
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = 0)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = 0)
    (hdvd : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      meromorphicOrderAt riemannZeta ρ
        ≤ meromorphicOrderAt (extendedMellinContinuation a 0 0 f) ρ
          + meromorphicOrderAt (twoPointNumer ρ₁ ρ₂) ρ)
    (z : ℂ) :
    meromorphicOrderAt riemannZeta z
      ≤ meromorphicOrderAt (soninTwoPointMellin a f ρ₁ ρ₂) z := by
  rw [meromorphicOrderAt_soninTwoPointMellin ha hev hc hd]
  by_cases h1 : z = 1
  · subst h1
    rw [GaloisForLFunctions.meromorphicOrderAt_riemannZeta_one]
    have hM := zero_le_meromorphicOrderAt_extendedMellinContinuation_one ha hev hc hd
    have hS := neg_one_le_meromorphicOrderAt_twoPointShift_one ρ₁ ρ₂
    have := add_le_add hM hS
    refine le_trans (le_of_eq ?_) this
    norm_num
  by_cases h0 : z = 0
  · subst h0
    rw [meromorphicOrderAt_riemannZeta_zero_point]
    have hM := one_le_meromorphicOrderAt_extendedMellinContinuation_zero ha hev hc hd
    have hS := neg_one_le_meromorphicOrderAt_twoPointShift_zero ρ₁ ρ₂
    have := add_le_add hM hS
    refine le_trans (le_of_eq ?_) this
    norm_num
  rw [meromorphicOrderAt_twoPointShift_of_ne h0 h1]
  by_cases hζ : riemannZeta z = 0
  · rcases riemannZeta_zero_trivial_or_mem_strip hζ with ⟨n, hn⟩ | ⟨hlo, hhi⟩
    · have hk : (n + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero n
      have hz : z = -(2 * (((n + 1 : ℕ) : ℂ))) := by rw [hn]; push_cast; ring
      have hM : ((1 : ℤ) : WithTop ℤ)
          ≤ meromorphicOrderAt (extendedMellinContinuation a 0 0 f) z := by
        rw [hz]
        exact one_le_meromorphicOrderAt_extendedMellinContinuation_trivial ha hev hc hd hk
      have hS := zero_le_meromorphicOrderAt_twoPointNumer ρ₁ ρ₂ z
      have hz1 : meromorphicOrderAt riemannZeta z = ((1 : ℤ) : WithTop ℤ) := by
        rw [hz, meromorphicOrderAt_riemannZeta_trivial hk]
      rw [hz1]
      have := add_le_add hM hS
      refine le_trans (le_of_eq ?_) this
      norm_num
    · exact hdvd z hζ hlo hhi
  · have hzord : meromorphicOrderAt riemannZeta z = ((0 : ℤ) : WithTop ℤ) := by
      have hana : AnalyticAt ℂ riemannZeta z := analyticOn_riemannZeta z (by simpa using h1)
      rw [hana.meromorphicOrderAt_eq, hana.analyticOrderAt_eq_zero.2 hζ]
      simp
    rw [hzord]
    have hM : ((0 : ℤ) : WithTop ℤ)
        ≤ meromorphicOrderAt (extendedMellinContinuation a 0 0 f) z := by
      have := meromorphicOrderAt_nonneg_of_analyticAt
        (analyticAt_extendedMellinContinuation_of_ne ha hev hc hd h0 h1)
      simpa using this
    have hS := zero_le_meromorphicOrderAt_twoPointNumer ρ₁ ρ₂ z
    have := add_le_add hM hS
    refine le_trans (le_of_eq ?_) this
    norm_num

/-- **The corrected quotient is regular everywhere.** -/
theorem zero_le_meromorphicOrderAt_burnolQuotient_soninTwoPointMellin (ha : 0 < a)
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = 0)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = 0)
    (hdvd : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      meromorphicOrderAt riemannZeta ρ
        ≤ meromorphicOrderAt (extendedMellinContinuation a 0 0 f) ρ
          + meromorphicOrderAt (twoPointNumer ρ₁ ρ₂) ρ)
    (z : ℂ) :
    0 ≤ meromorphicOrderAt (burnolQuotient (soninTwoPointMellin a f ρ₁ ρ₂)) z := by
  have hmero : MeromorphicAt (soninTwoPointMellin a f ρ₁ ρ₂) z :=
    meromorphicAt_soninTwoPointMellin ha hev hc hd z
  have hle := meromorphicOrderAt_riemannZeta_le_soninTwoPointMellin ha hev hc hd hdvd z
  rw [meromorphicOrderAt_burnolQuotient hmero]
  induction hx : meromorphicOrderAt riemannZeta z with
  | top =>
      rw [hx] at hle
      rw [top_le_iff.1 hle]
      simp
  | coe n =>
      rw [hx] at hle
      exact withTop_sub_nonneg_of_le hle

end

end RHTower
