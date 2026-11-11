import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheShiftedMobiusProfilesConvergeUniformly

/-!
# The first two shift jets of the Möbius profile

Differentiating the finite power shift inserts a normalized logarithm.
The first two jets are finite combinations of the profiles `P`, `xP`,
and `x²P`. Their uniform limits are `−P` and zero.
-/

open ArithmeticFunction Filter Set Topology
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- A normalized shift jet of the finite Möbius profile. -/
def shiftedMobiusProfileJet (P : ℝ → ℝ) (j : ℕ) (L u v : ℝ) : ℝ :=
  L * (∑ n ∈ Finset.Icc 1 ⌊Real.exp (L * u)⌋₊,
    ((moebius n : ℤ) : ℝ) / (n : ℝ) * Real.exp (v * Real.log n / L) *
      (Real.log n / L) ^ j * P (u - Real.log n / L))

@[simp] theorem shiftedMobiusProfileJet_zero (P : ℝ → ℝ) (L u v : ℝ) :
    shiftedMobiusProfileJet P 0 L u v = normalizedShiftedMobiusProfile P L u v := by
  simp only [shiftedMobiusProfileJet, normalizedShiftedMobiusProfile, pow_zero, mul_one]

/-- The finite shift jets are actual successive derivatives in the shift parameter. -/
theorem hasDerivAt_shiftedMobiusProfileJet (P : ℝ → ℝ) (j : ℕ) (L u v : ℝ) :
    HasDerivAt (shiftedMobiusProfileJet P j L u) (shiftedMobiusProfileJet P (j + 1) L u v) v := by
  unfold shiftedMobiusProfileJet
  apply HasDerivAt.const_mul
  apply HasDerivAt.sum
  intro n hn
  have he : HasDerivAt (fun v => Real.exp (v * Real.log n / L))
      (Real.exp (v * Real.log n / L) * (Real.log n / L)) v := by
    convert ((Real.hasDerivAt_exp _).comp v
      (((hasDerivAt_id v).mul_const (Real.log n)).div_const L)) using 1 <;> simp only [id_eq] <;> ring
  apply (((he.const_mul (((moebius n : ℤ) : ℝ) / (n : ℝ))).mul_const
    ((Real.log n / L) ^ j)).mul_const (P (u - Real.log n / L))).congr_deriv
  rw [pow_succ]
  ring

/-- The first shift derivative is the difference of two smooth-profile transforms. -/
theorem shiftedMobiusProfileJet_one (P : ℝ → ℝ) (L u v : ℝ) :
    shiftedMobiusProfileJet P 1 L u v =
      u * normalizedShiftedMobiusProfile P L u v -
        normalizedShiftedMobiusProfile (fun x => x * P x) L u v := by
  simp only [shiftedMobiusProfileJet, normalizedShiftedMobiusProfile, Finset.mul_sum, pow_one]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- The second shift derivative is a three-profile finite difference. -/
theorem shiftedMobiusProfileJet_two (P : ℝ → ℝ) (L u v : ℝ) :
    shiftedMobiusProfileJet P 2 L u v =
      u ^ 2 * normalizedShiftedMobiusProfile P L u v -
        2 * u * normalizedShiftedMobiusProfile (fun x => x * P x) L u v +
          normalizedShiftedMobiusProfile (fun x => x ^ 2 * P x) L u v := by
  simp only [shiftedMobiusProfileJet, normalizedShiftedMobiusProfile, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

private theorem first_profile_error_bound {u a b A B η : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hη : 0 ≤ η) (ha : |a - A| ≤ η) (hb : |b - B| ≤ η) :
    |(u * a - b) - (u * A - B)| ≤ 2 * η := by
  have he : (u * a - b) - (u * A - B) = u * (a - A) - (b - B) := by ring
  rw [he]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hu.1]
  have hm : u * |a - A| ≤ η := (mul_le_mul hu.2 ha (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  linarith only [hm, hb]

private theorem second_profile_error_bound {u a b c A B C η : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hη : 0 ≤ η)
    (ha : |a - A| ≤ η) (hb : |b - B| ≤ η) (hc : |c - C| ≤ η) :
    |(u ^ 2 * a - 2 * u * b + c) - (u ^ 2 * A - 2 * u * B + C)| ≤ 4 * η := by
  have he : (u ^ 2 * a - 2 * u * b + c) - (u ^ 2 * A - 2 * u * B + C) =
      (u ^ 2 * (a - A) - 2 * u * (b - B)) + (c - C) := by ring
  rw [he]
  have h1 : u ^ 2 * |a - A| ≤ η :=
    (mul_le_mul (pow_le_one₀ hu.1 hu.2) ha (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have h2 : 2 * u * |b - B| ≤ 2 * η := by
    have hh : u * |b - B| ≤ η :=
      (mul_le_mul hu.2 hb (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    nlinarith only [hh]
  calc
    _ ≤ |u ^ 2 * (a - A) - 2 * u * (b - B)| + |c - C| := abs_add_le _ _
    _ ≤ (|u ^ 2 * (a - A)| + |2 * u * (b - B)|) + |c - C| :=
      add_le_add (abs_sub _ _) le_rfl
    _ = (u ^ 2 * |a - A| + 2 * u * |b - B|) + |c - C| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg u), abs_mul,
        abs_of_nonneg (mul_nonneg (by norm_num) hu.1)]
    _ ≤ 4 * η := by linarith only [h1, h2, hc]

/-- The first three shift jets have a common bound; the positive-order jets converge to `−P` and zero. -/
theorem shiftedMobiusProfileJets_compact_uniform
    {P P₁ P₂ : ℝ → ℝ} (hP : ∀ x, HasDerivAt P (P₁ x) x)
    (hP₁ : ∀ x, HasDerivAt P₁ (P₂ x) x) (hc₂ : Continuous P₂) (hP0 : P 0 = 0)
    {V : ℝ} (hV : 0 ≤ V) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ L : ℝ, 0 < L → ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (-V) V, ∀ j : ℕ, j ≤ 2 →
      |shiftedMobiusProfileJet P j L u v| ≤ B) ∧
    (∀ δ ε : ℝ, 0 < δ → 0 < ε → ∀ᶠ L : ℝ in atTop, ∀ u ∈ Icc δ 1, ∀ v ∈ Icc (-V) V,
      |shiftedMobiusProfileJet P 1 L u v + P u| < ε ∧
      |shiftedMobiusProfileJet P 2 L u v| < ε) := by
  have hcP : Continuous P := continuous_iff_continuousAt.mpr (fun x => (hP x).continuousAt)
  have hcP₁ : Continuous P₁ := continuous_iff_continuousAt.mpr (fun x => (hP₁ x).continuousAt)
  let Q : ℝ → ℝ := fun x => x * P x
  let Q₁ : ℝ → ℝ := fun x => P x + x * P₁ x
  let Q₂ : ℝ → ℝ := fun x => 2 * P₁ x + x * P₂ x
  let R : ℝ → ℝ := fun x => x ^ 2 * P x
  let R₁ : ℝ → ℝ := fun x => 2 * x * P x + x ^ 2 * P₁ x
  let R₂ : ℝ → ℝ := fun x => 2 * P x + 4 * x * P₁ x + x ^ 2 * P₂ x
  have hQ (x : ℝ) : HasDerivAt Q (Q₁ x) x := by
    apply ((hasDerivAt_id x).mul (hP x)).congr_deriv
    dsimp only [Q₁, id_eq]
    ring
  have hQ₁ (x : ℝ) : HasDerivAt Q₁ (Q₂ x) x := by
    apply ((hP x).add ((hasDerivAt_id x).mul (hP₁ x))).congr_deriv
    dsimp only [Q₂, id_eq]
    ring
  have hR (x : ℝ) : HasDerivAt R (R₁ x) x := by
    apply (((hasDerivAt_id x).pow 2).mul (hP x)).congr_deriv
    dsimp only [R₁, id_eq]
    ring
  have hR₁ (x : ℝ) : HasDerivAt R₁ (R₂ x) x := by
    apply ((((hasDerivAt_id x).const_mul 2).mul (hP x)).add
      (((hasDerivAt_id x).pow 2).mul (hP₁ x))).congr_deriv
    dsimp only [R₂, id_eq]
    ring
  have hcQ₂ : Continuous Q₂ := by dsimp only [Q₂]; fun_prop
  have hcR₂ : Continuous R₂ := by dsimp only [R₂]; fun_prop
  have hQ0 : Q 0 = 0 := by simp [Q]
  have hR0 : R 0 = 0 := by simp [R]
  have hpall := normalizedShiftedMobiusProfile_compact_uniform hP hP₁ hc₂ hP0 hV
  have hqall := normalizedShiftedMobiusProfile_compact_uniform hQ hQ₁ hcQ₂ hQ0 hV
  have hrall := normalizedShiftedMobiusProfile_compact_uniform hR hR₁ hcR₂ hR0 hV
  constructor
  · obtain ⟨B₀, hB₀, hb₀⟩ := hpall.1
    obtain ⟨B₁, hB₁, hb₁⟩ := hqall.1
    obtain ⟨B₂, hB₂, hb₂⟩ := hrall.1
    let S := B₀ + B₁ + B₂
    have hS : 0 ≤ S := by dsimp only [S]; positivity
    refine ⟨4 * S, by positivity, ?_⟩
    intro L hL u hu v hv j hj
    have h₀ : |normalizedShiftedMobiusProfile P L u v - 0| ≤ S := by
      simpa only [sub_zero] using (hb₀ L hL u hu v hv).trans
        (show B₀ ≤ S by dsimp only [S]; linarith only [hB₁, hB₂])
    have h₁ : |normalizedShiftedMobiusProfile Q L u v - 0| ≤ S := by
      simpa only [sub_zero] using (hb₁ L hL u hu v hv).trans
        (show B₁ ≤ S by dsimp only [S]; linarith only [hB₀, hB₂])
    have h₂ : |normalizedShiftedMobiusProfile R L u v - 0| ≤ S := by
      simpa only [sub_zero] using (hb₂ L hL u hu v hv).trans
        (show B₂ ≤ S by dsimp only [S]; linarith only [hB₀, hB₁])
    interval_cases j
    · rw [shiftedMobiusProfileJet_zero]
      simpa only [sub_zero] using h₀.trans (show S ≤ 4 * S by linarith only [hS])
    · rw [shiftedMobiusProfileJet_one]
      have hh := (first_profile_error_bound hu hS h₀ h₁).trans
        (show 2 * S ≤ 4 * S by linarith only [hS])
      simpa only [mul_zero, sub_zero] using hh
    · rw [shiftedMobiusProfileJet_two]
      simpa only [mul_zero, sub_zero, add_zero] using second_profile_error_bound hu hS h₀ h₁ h₂
  · intro δ ε hδ hε
    let η : ℝ := ε / 8
    have hη : 0 < η := by dsimp only [η]; positivity
    have hp := hpall.2 δ η hδ hη
    have hq := hqall.2 δ η hδ hη
    have hr := hrall.2 δ η hδ hη
    filter_upwards [hp, hq, hr] with L hp hq hr
    intro u hu v hv
    have hu0 : u ∈ Icc (0 : ℝ) 1 := ⟨hδ.le.trans hu.1, hu.2⟩
    have hfirst := first_profile_error_bound hu0 hη.le (hp u hu v hv).le (hq u hu v hv).le
    have hsecond := second_profile_error_bound hu0 hη.le (hp u hu v hv).le (hq u hu v hv).le (hr u hu v hv).le
    have hval₁ : u * (P₁ u - v * P u) - (Q₁ u - v * Q u) = -P u := by
      dsimp only [Q₁, Q]
      ring
    have hval₂ : u ^ 2 * (P₁ u - v * P u) - 2 * u * (Q₁ u - v * Q u) +
        (R₁ u - v * R u) = 0 := by
      dsimp only [Q₁, Q, R₁, R]
      ring
    rw [hval₁, sub_neg_eq_add] at hfirst
    rw [hval₂, sub_zero] at hsecond
    constructor
    · rw [shiftedMobiusProfileJet_one]
      exact hfirst.trans_lt (by dsimp only [η]; linarith only [hε])
    · rw [shiftedMobiusProfileJet_two]
      exact hsecond.trans_lt (by dsimp only [η]; linarith only [hε])

end GaloisForLFunctions.MultiscaleMollifiedZetaField
