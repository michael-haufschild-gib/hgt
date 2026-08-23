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

/-! ## The three boundary estimates -/

theorem burnolQuotientNF_soninTwoPointMellin_eq (ha : 0 < a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = 0)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = 0)
    {s : ℂ} (hζ : riemannZeta s ≠ 0) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    burnolQuotientNF (soninTwoPointMellin a f ρ₁ ρ₂) s
      = extendedMellinContinuation a 0 0 f s * twoPointShift ρ₁ ρ₂ s * (riemannZeta s)⁻¹ := by
  have hana : AnalyticAt ℂ (soninTwoPointMellin a f ρ₁ ρ₂) s :=
    AnalyticAt.mul (analyticAt_extendedMellinContinuation_of_ne ha hev hc hd h0 h1)
      (analyticAt_twoPointShift h0 h1)
  have hq : AnalyticAt ℂ (burnolQuotient (soninTwoPointMellin a f ρ₁ ρ₂)) s :=
    analyticAt_burnolQuotient hana hζ h1
  rw [burnolQuotientNF_eq_of_analyticAt
    (fun z => meromorphicAt_soninTwoPointMellin ha hev hc hd z) hq, burnolQuotient,
    soninTwoPointMellin]

theorem one_le_norm_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) : 1 ≤ ‖s‖ ∧ 1 ≤ ‖s - 1‖ := by
  constructor
  · have := Complex.abs_re_le_norm s
    have h : |s.re| = s.re := abs_of_nonneg (by linarith)
    rw [h] at this
    linarith
  · have := Complex.abs_re_le_norm (s - 1)
    have hre : (s - 1).re = s.re - 1 := by simp
    have h : |(s - 1).re| = s.re - 1 := by rw [hre]; exact abs_of_nonneg (by linarith)
    rw [h] at this
    linarith

theorem one_le_norm_of_re_le_neg_one {s : ℂ} (hs : s.re ≤ -1) : 1 ≤ ‖s‖ ∧ 1 ≤ ‖s - 1‖ := by
  constructor
  · have := Complex.abs_re_le_norm s
    have h : |s.re| = -s.re := abs_of_nonpos (by linarith)
    rw [h] at this
    linarith
  · have := Complex.abs_re_le_norm (s - 1)
    have hre : (s - 1).re = s.re - 1 := by simp
    have h : |(s - 1).re| = -(s.re - 1) := by rw [hre]; exact abs_of_nonpos (by linarith)
    rw [h] at this
    linarith

/-- **Boundedness on the right half-plane.** -/
theorem exists_bound_twoPointNF_right (ha : 1 ≤ a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = 0)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = 0)
    (ρ₁ ρ₂ : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 2 ≤ s.re →
      ‖burnolQuotientNF (soninTwoPointMellin a f ρ₁ ρ₂) s‖ ≤ C := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  obtain ⟨CM, hCM0, hMb⟩ := exists_norm_extendedMellin_halfPlane_le ha0 hev hc hd
  obtain ⟨CS, hCS0, hSb⟩ := exists_bound_twoPointShift ρ₁ ρ₂
  refine ⟨4 * CM * CS, by positivity, ?_⟩
  intro s hs
  have hζ : riemannZeta s ≠ 0 := by
    have h := norm_riemannZeta_ge_of_two_le_re hs
    intro hzero
    rw [hzero] at h
    simp at h
    linarith
  have h1 : s ≠ 1 := by
    intro h; rw [h] at hs; norm_num at hs
  have h0 : s ≠ 0 := by
    intro h; rw [h] at hs; norm_num at hs
  rw [burnolQuotientNF_soninTwoPointMellin_eq ha0 hev hc hd hζ h0 h1, norm_mul, norm_mul]
  obtain ⟨hn1, hn2⟩ := one_le_norm_of_two_le_re hs
  have hS := hSb s hn1 hn2
  have hM := hMb s hs
  have hapow : a ^ (-s.re) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos ha ?_
    linarith
  have hMle : ‖extendedMellinContinuation a 0 0 f s‖ ≤ CM := by
    refine le_trans hM ?_
    nlinarith [hCM0]
  have hz := norm_zeta_inv_le_of_two_le_re hs
  have hb1 : ‖extendedMellinContinuation a 0 0 f s‖ * ‖twoPointShift ρ₁ ρ₂ s‖ ≤ CM * CS :=
    mul_le_mul hMle hS (norm_nonneg _) (le_of_lt hCM0)
  have hb2 := mul_le_mul hb1 hz (norm_nonneg _) (by positivity : (0:ℝ) ≤ CM * CS)
  linarith [hb2]

/-- **Boundedness on the left half-plane**, through the functional equation. -/
theorem exists_bound_twoPointNF_left (ha : 1 ≤ a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = 0)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = 0)
    (hdvd : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      meromorphicOrderAt riemannZeta ρ
        ≤ meromorphicOrderAt (extendedMellinContinuation a 0 0 f) ρ
          + meromorphicOrderAt (twoPointNumer ρ₁ ρ₂) ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ≤ -1 →
      ‖burnolQuotientNF (soninTwoPointMellin a f ρ₁ ρ₂) s‖ ≤ C := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hev' : fourierUnitary f ∈ evenSubspace := fourierUnitary_mem_evenSubspace hev
  have hc' := fourierUnitary_band_of_reflect hev hd
  obtain ⟨CM, hCM0, hMb⟩ := exists_norm_extendedMellin_halfPlane_le (b := a)
    (g := fourierUnitary f) (c := 0) (d := 0) ha0 hev' hc' hc
  obtain ⟨CS, hCS0, hSb⟩ := exists_bound_twoPointShift ρ₁ ρ₂
  refine ⟨4 * CM * CS, by positivity, ?_⟩
  have hdiff : Differentiable ℂ (burnolQuotientNF (soninTwoPointMellin a f ρ₁ ρ₂)) :=
    differentiable_burnolQuotientNF (fun z => meromorphicAt_soninTwoPointMellin ha0 hev hc hd z)
      (zero_le_meromorphicOrderAt_burnolQuotient_soninTwoPointMellin ha0 hev hc hd hdvd)
  have hoff : ∀ s : ℂ, s.re ≤ -1 → s.im ≠ 0 →
      ‖burnolQuotientNF (soninTwoPointMellin a f ρ₁ ρ₂) s‖ ≤ 4 * CM * CS := by
    intro s hs him
    have hζ : riemannZeta s ≠ 0 := by
      intro hzero
      rcases riemannZeta_zero_trivial_or_mem_strip hzero with ⟨n, hn⟩ | ⟨h1, -⟩
      · have := congrArg Complex.im hn
        simp at this
        exact him this
      · linarith
    have h1 : s ≠ 1 := by
      intro h; rw [h] at hs; norm_num at hs
    have h0 : s ≠ 0 := by
      intro h; rw [h] at him; simp at him
    rw [burnolQuotientNF_soninTwoPointMellin_eq ha0 hev hc hd hζ h0 h1]
    have hrefl : extendedMellinContinuation a 0 0 f s * (riemannZeta s)⁻¹
        = extendedMellinContinuation a 0 0 (fourierUnitary f) (1 - s)
          * (riemannZeta (1 - s))⁻¹ := by
      have h := burnolQuotient_reflect_of_im_ne a 0 0 f (by linarith) him
      rw [burnolQuotient, burnolQuotient] at h
      exact h
    have hval : extendedMellinContinuation a 0 0 f s * twoPointShift ρ₁ ρ₂ s
        * (riemannZeta s)⁻¹
        = (extendedMellinContinuation a 0 0 (fourierUnitary f) (1 - s)
            * (riemannZeta (1 - s))⁻¹) * twoPointShift ρ₁ ρ₂ s := by
      rw [← hrefl]; ring
    rw [hval, norm_mul, norm_mul]
    have hre : ((1 : ℂ) - s).re = 1 - s.re := by simp
    have h2re : (2:ℝ) ≤ ((1 : ℂ) - s).re := by rw [hre]; linarith
    have hM := hMb ((1 : ℂ) - s) h2re
    have hz := norm_zeta_inv_le_of_two_le_re h2re
    have hapow : a ^ (-((1 : ℂ) - s).re) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos ha ?_
      rw [hre]; linarith
    have hMle : ‖extendedMellinContinuation a 0 0 (fourierUnitary f) ((1 : ℂ) - s)‖ ≤ CM := by
      refine le_trans hM ?_
      nlinarith [hCM0]
    obtain ⟨hn1, hn2⟩ := one_le_norm_of_re_le_neg_one hs
    have hS := hSb s hn1 hn2
    have hb1 : ‖extendedMellinContinuation a 0 0 (fourierUnitary f) ((1 : ℂ) - s)‖
        * ‖(riemannZeta ((1 : ℂ) - s))⁻¹‖ ≤ CM * 4 :=
      mul_le_mul hMle hz (norm_nonneg _) (le_of_lt hCM0)
    have hb2 := mul_le_mul hb1 hS (norm_nonneg _) (by positivity : (0:ℝ) ≤ CM * 4)
    linarith [hb2]
  intro s hs
  rcases eq_or_ne s.im 0 with him | him
  · set u : ℕ → ℂ := fun n => s + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I with hudef
    have hure : ∀ n : ℕ, (u n).re = s.re := by
      intro n; rw [hudef]; simp
    have huim : ∀ n : ℕ, (u n).im ≠ 0 := by
      intro n
      rw [hudef]
      simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_one, mul_zero, add_zero, zero_add, him]
      positivity
    have hutend : Tendsto u atTop (𝓝 s) := by
      have hreal : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 (0:ℝ)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hcx : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) atTop (𝓝 (0:ℂ)) := by
        have hcont : Continuous (fun x : ℝ => ((x : ℝ) : ℂ) * I) := by fun_prop
        have hcomp := (hcont.tendsto (0:ℝ)).comp hreal
        simpa [Function.comp_def] using hcomp
      have := (tendsto_const_nhds (x := s) (f := (atTop : Filter ℕ))).add hcx
      simpa [hudef] using this
    have hlim := (hdiff.continuous.continuousAt (x := s)).tendsto.comp hutend
    have hbd : ∀ n : ℕ,
        ‖burnolQuotientNF (soninTwoPointMellin a f ρ₁ ρ₂) (u n)‖ ≤ 4 * CM * CS := by
      intro n
      exact hoff (u n) (by rw [hure n]; exact hs) (huim n)
    exact le_of_tendsto (hlim.norm) (Filter.Eventually.of_forall hbd)
  · exact hoff s hs him

/-! ## The selected horizontal lines -/

/-- **Polynomial bound on the selected horizontal lines.** -/
theorem exists_bound_twoPointNF_horizontal (ha : 1 ≤ a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = 0)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = 0)
    (ρ₁ ρ₂ : ℂ)
    {T : ℕ → ℝ} (htop : Tendsto T atTop atTop) (hT1 : ∀ k : ℕ, 1 ≤ T k)
    (hTne : ∀ k : ℕ, ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
      riemannZeta ((σ : ℂ) + ((T k : ℝ) : ℂ) * I) ≠ 0)
    (hzeta : ∀ b : ℝ, 2 ≤ b → ∃ (C A : ℝ) (k₀ : ℕ), 0 < C ∧ 0 < A ∧
      ∀ k : ℕ, k₀ ≤ k → ∀ σ : ℝ, -b ≤ σ → σ ≤ b →
        ‖(riemannZeta ((σ : ℂ) + ((T k : ℝ) : ℂ) * I))⁻¹‖ ≤ C * (T k) ^ A) :
    ∃ (C : ℝ) (D k₀ : ℕ), 0 ≤ C ∧ ∀ k : ℕ, k₀ ≤ k → ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 →
      (s.im = T k ∨ s.im = -T k) →
      ‖burnolQuotientNF (soninTwoPointMellin a f ρ₁ ρ₂) s‖ ≤ C * (1 + T k) ^ D := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  obtain ⟨CH, D, k₀, hCH0, hH⟩ :=
    exists_bound_burnolQuotientNF_horizontal ha hev hc hd htop hT1 hTne hzeta
  obtain ⟨CS, hCS0, hSb⟩ := exists_bound_twoPointShift ρ₁ ρ₂
  refine ⟨CH * CS, D, k₀, by positivity, ?_⟩
  intro k hk s hs1 hs2 him
  have hTk1 : (1 : ℝ) ≤ T k := hT1 k
  have hTk0 : (0 : ℝ) < T k := by linarith
  have habs : |s.im| = T k := by
    rcases him with h | h
    · rw [h, abs_of_pos hTk0]
    · rw [h, abs_neg, abs_of_pos hTk0]
  have hsplit : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have hζne : riemannZeta s ≠ 0 := by
    rcases him with h | h
    · rw [hsplit, h]
      exact hTne k s.re hs1 hs2
    · rw [hsplit, h]
      have hbase := hTne k s.re hs1 hs2
      have := riemannZeta_ne_zero_neg_height (σ := s.re) (t := T k) hbase
      simpa using this
  have hs1' : s ≠ 1 := by
    intro h
    rw [h] at habs
    simp at habs
    linarith
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at habs
    simp at habs
    linarith
  have hana : AnalyticAt ℂ (burnolQuotient (extendedMellinContinuation a 0 0 f)) s :=
    analyticAt_burnolQuotient
      (analyticAt_extendedMellinContinuation_of_ne ha0 hev hc hd hs0 hs1') hζne hs1'
  have hMval : burnolQuotientNF (extendedMellinContinuation a 0 0 f) s
      = extendedMellinContinuation a 0 0 f s * (riemannZeta s)⁻¹ := by
    rw [burnolQuotientNF_eq_of_analyticAt (meromorphicAt_extendedMellin_all ha0 hev hc hd) hana,
      burnolQuotient]
  have hval : burnolQuotientNF (soninTwoPointMellin a f ρ₁ ρ₂) s
      = burnolQuotientNF (extendedMellinContinuation a 0 0 f) s * twoPointShift ρ₁ ρ₂ s := by
    rw [burnolQuotientNF_soninTwoPointMellin_eq ha0 hev hc hd hζne hs0 hs1', hMval]
    ring
  have hnorms : 1 ≤ ‖s‖ ∧ 1 ≤ ‖s - 1‖ := by
    constructor
    · have := Complex.abs_im_le_norm s
      rw [habs] at this
      linarith
    · have h := Complex.abs_im_le_norm (s - 1)
      have hre : (s - 1).im = s.im := by simp
      rw [hre, habs] at h
      linarith
  rw [hval, norm_mul]
  have hb1 := hH k hk s hs1 hs2 him
  have hb2 := hSb s hnorms.1 hnorms.2
  have hb3 := mul_le_mul hb1 hb2 (norm_nonneg _) (by positivity)
  calc ‖burnolQuotientNF (extendedMellinContinuation a 0 0 f) s‖ * ‖twoPointShift ρ₁ ρ₂ s‖
      ≤ CH * (1 + T k) ^ D * CS := hb3
    _ = CH * CS * (1 + T k) ^ D := by ring

/-! ## Polynomial growth -/

/-- **Polynomial growth of the corrected quotient.** -/
theorem exists_polyGrowth_twoPointNF (ha : 1 ≤ a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = 0)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = 0)
    (hdvd : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      meromorphicOrderAt riemannZeta ρ
        ≤ meromorphicOrderAt (extendedMellinContinuation a 0 0 f) ρ
          + meromorphicOrderAt (twoPointNumer ρ₁ ρ₂) ρ) :
    ∃ (M : ℝ) (D : ℕ), 0 ≤ M ∧ ∀ z : ℂ,
      ‖burnolQuotientNF (soninTwoPointMellin a f ρ₁ ρ₂) z‖ ≤ M * (‖z‖ + 1) ^ D := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  obtain ⟨T, _hmono, htop, hT1, hspace, hTne, hzeta⟩ := exists_seq_zeta_inv_horizontal
  obtain ⟨CR, hCR0, hR⟩ := exists_bound_twoPointNF_right ha hev hc hd ρ₁ ρ₂
  obtain ⟨CL, hCL0, hLb⟩ := exists_bound_twoPointNF_left ha hev hc hd hdvd
  obtain ⟨CH, D, k₀, hCH0, hH⟩ :=
    exists_bound_twoPointNF_horizontal ha hev hc hd ρ₁ ρ₂ htop hT1 hTne hzeta
  have hdiff : Differentiable ℂ (burnolQuotientNF (soninTwoPointMellin a f ρ₁ ρ₂)) :=
    differentiable_burnolQuotientNF (fun z => meromorphicAt_soninTwoPointMellin ha0 hev hc hd z)
      (zero_le_meromorphicOrderAt_burnolQuotient_soninTwoPointMellin ha0 hev hc hd hdvd)
  have hStop : Tendsto (fun n : ℕ => T (n + k₀)) atTop atTop :=
    htop.comp (tendsto_add_atTop_nat k₀)
  have hSspace : ∀ n : ℕ, T (n + 1 + k₀) ≤ T (n + k₀) + 3 := by
    intro n
    rw [show n + 1 + k₀ = (n + k₀) + 1 from by omega]
    exact hspace (n + k₀)
  have hS0 : (1 : ℝ) ≤ T k₀ := hT1 k₀
  refine ⟨CR + CL + CH * (T k₀ + 4) ^ D, D, by positivity, ?_⟩
  intro z
  have hz1 : (1 : ℝ) ≤ (‖z‖ + 1) ^ D := one_le_pow₀ (by linarith [norm_nonneg z])
  have hbig : (0 : ℝ) ≤ CR + CL + CH * (T k₀ + 4) ^ D := by positivity
  by_cases hzr : 2 ≤ z.re
  · calc ‖burnolQuotientNF (soninTwoPointMellin a f ρ₁ ρ₂) z‖ ≤ CR := hR z hzr
      _ ≤ (CR + CL + CH * (T k₀ + 4) ^ D) * 1 := by
          have : (0:ℝ) ≤ CH * (T k₀ + 4) ^ D := by positivity
          nlinarith
      _ ≤ (CR + CL + CH * (T k₀ + 4) ^ D) * (‖z‖ + 1) ^ D :=
          mul_le_mul_of_nonneg_left hz1 hbig
  by_cases hzl : z.re ≤ -1
  · calc ‖burnolQuotientNF (soninTwoPointMellin a f ρ₁ ρ₂) z‖ ≤ CL := hLb z hzl
      _ ≤ (CR + CL + CH * (T k₀ + 4) ^ D) * 1 := by
          have : (0:ℝ) ≤ CH * (T k₀ + 4) ^ D := by positivity
          nlinarith
      _ ≤ (CR + CL + CH * (T k₀ + 4) ^ D) * (‖z‖ + 1) ^ D :=
          mul_le_mul_of_nonneg_left hz1 hbig
  push Not at hzr hzl
  obtain ⟨n, hn1, hn2⟩ := exists_height_between hStop hSspace |z.im|
  set k : ℕ := n + k₀ with hkdef
  have hkk₀ : k₀ ≤ k := Nat.le_add_left _ _
  have hTk1 : (1 : ℝ) ≤ T k := hT1 k
  have hTk0 : (0 : ℝ) < T k := by linarith
  have hedge : ∀ w : ℂ, (-1 : ℝ) ≤ w.re → w.re ≤ 2 → -(T k) ≤ w.im → w.im ≤ T k →
      (w.re = -1 ∨ w.re = 2 ∨ w.im = -(T k) ∨ w.im = T k) →
      ‖burnolQuotientNF (soninTwoPointMellin a f ρ₁ ρ₂) w‖
        ≤ max CR (max CL (CH * (1 + T k) ^ D)) := by
    intro w hw1 hw2 _ _ hcase
    rcases hcase with h | h | h | h
    · exact le_trans (hLb w (by rw [h])) (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact le_trans (hR w (by rw [h])) (le_max_left _ _)
    · exact le_trans (hH k hkk₀ w hw1 hw2 (Or.inr h))
        (le_trans (le_max_right _ _) (le_max_right _ _))
    · exact le_trans (hH k hkk₀ w hw1 hw2 (Or.inl h))
        (le_trans (le_max_right _ _) (le_max_right _ _))
  have him1 : -(T k) ≤ z.im := (abs_le.1 hn1).1
  have him2 : z.im ≤ T k := (abs_le.1 hn1).2
  have hbound := norm_le_of_mem_rectangle hdiff (by norm_num : (-1:ℝ) < 2) hTk0 hedge
    (le_of_lt hzl) (le_of_lt hzr) him1 him2
  have hzim : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hTkle : 1 + T k ≤ (T k₀ + 4) * (‖z‖ + 1) := by
    have h1 : T k ≤ max (T k₀) (|z.im| + 3) := by
      simpa using hn2
    have h2 : max (T k₀) (|z.im| + 3) ≤ T k₀ + (|z.im| + 3) := by
      refine max_le (by nlinarith [abs_nonneg z.im]) (by linarith)
    have h3 : (T k₀ + 4) * (‖z‖ + 1) = (T k₀ + 4) * ‖z‖ + (T k₀ + 4) := by ring
    have h4 : (1:ℝ) * ‖z‖ ≤ (T k₀ + 4) * ‖z‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg z)
    nlinarith [norm_nonneg z]
  have hpow : (1 + T k) ^ D ≤ (T k₀ + 4) ^ D * (‖z‖ + 1) ^ D := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) hTkle D
  refine le_trans hbound ?_
  refine max_le ?_ (max_le ?_ ?_)
  · nlinarith [hz1, (by positivity : (0:ℝ) ≤ CH * (T k₀ + 4) ^ D)]
  · nlinarith [hz1, (by positivity : (0:ℝ) ≤ CH * (T k₀ + 4) ^ D)]
  · have : CH * (1 + T k) ^ D ≤ CH * ((T k₀ + 4) ^ D * (‖z‖ + 1) ^ D) :=
      mul_le_mul_of_nonneg_left hpow hCH0
    nlinarith [hz1, (by positivity : (0:ℝ) ≤ (‖z‖ + 1) ^ D)]

end

end RHTower
