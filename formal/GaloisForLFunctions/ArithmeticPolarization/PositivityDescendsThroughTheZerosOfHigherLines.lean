import GaloisForLFunctions.ArithmeticPolarization.OneVerticalSectionDecidesPositivity

/-!
# Positivity descends through the zeros of the higher lines

Let a finite polar configuration have all its ordinates in a lattice `ωℤ`, and write
`T_σ(t) = Σ_{Re z = σ} c(z) cos(Im z · t)` for the trigonometric sum of the vertical line
`Re z = σ` (`leadingSum`). Every `T_σ` has period `2π/ω`.

* **The line hierarchy law** (`leadingSum_nonneg_of_higher_eq_zero`): if the scale weight
  `w(t) = Σ_σ e^{σt} T_σ(t)` is nonnegative on `t > 0` (equivalently, one vertical section is
  positive definite, `posDef_section_iff_scaleWeight_nonneg`), then at every `t*` where all the
  lines to the right of `σ` vanish, `T_σ(t*) ≥ 0`. Along `t* + 2πm/ω` the higher lines vanish
  identically and the lower ones are `O(e^{(σ − η)t})`.
* **Leading and second lines** (`leadingSum_nonneg_of_lattice`, `secondLine_nonneg_of_lattice`):
  the leading line is nonnegative everywhere, and the next line is nonnegative on the zero set of
  the leading one.

A positive completion therefore constrains its lines in sequence: each line is free only where the
lines above it are positive, and must be nonnegative where they all vanish. In particular a
quartet at the second depth is constrained by the zero set of the completed first line.
-/

open Complex Finset Filter Topology Real
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open ArithmeticCorrespondencePositivity MultiplicativePositivityGeometry

/-- Lattice ordinates make every line sum `2π/ω`-periodic. -/
theorem leadingSum_add_period {S : Finset ℂ} {c : ℂ → ℝ} {ω : ℝ} (hω : ω ≠ 0)
    (hlat : ∀ z ∈ S, ∃ k : ℤ, z.im = k * ω) (σ t : ℝ) (m : ℕ) :
    leadingSum S c σ (t + m * (2 * π / ω)) = leadingSum S c σ t := by
  rw [leadingSum, leadingSum]
  refine Finset.sum_congr rfl fun z hz => ?_
  obtain ⟨k, hk⟩ := hlat z (Finset.mem_filter.mp hz).1
  have : z.im * (t + m * (2 * π / ω)) = z.im * t + ((k * m : ℤ) : ℝ) * (2 * π) := by
    rw [hk]; push_cast; field_simp
  rw [this, Real.cos_add_int_mul_two_pi]

/-- A finite set of points strictly left of `σ` stays a fixed distance away from `σ`. -/
theorem exists_gap (S : Finset ℂ) (σ : ℝ) : ∃ η > 0, ∀ z ∈ S, z.re < σ → z.re ≤ σ - η := by
  by_cases hne : (S.filter fun z => z.re < σ).Nonempty
  · obtain ⟨z₀, hz₀, hmax⟩ := (S.filter fun z => z.re < σ).exists_max_image (fun z => z.re) hne
    refine ⟨σ - z₀.re, by linarith [(Finset.mem_filter.mp hz₀).2], fun z hz hzσ => ?_⟩
    have := hmax z (Finset.mem_filter.mpr ⟨hz, hzσ⟩)
    linarith
  · refine ⟨1, one_pos, fun z hz hzσ => absurd ⟨z, Finset.mem_filter.mpr ⟨hz, hzσ⟩⟩ hne⟩

/-- The scale weight splits into the lines right of `σ`, the line `σ`, and the rest. -/
theorem polarScaleWeight_split (S : Finset ℂ) (c : ℂ → ℝ) (σ t : ℝ) :
    polarScaleWeight S c t =
      ∑ σ' ∈ (S.filter fun z => σ < z.re).image Complex.re,
          Real.exp (σ' * t) * leadingSum S c σ' t +
        Real.exp (σ * t) * leadingSum S c σ t +
        ∑ z ∈ S.filter (fun z => z.re < σ), c z * Real.exp (z.re * t) * Real.cos (z.im * t) := by
  classical
  have hsplit : polarScaleWeight S c t =
      ∑ z ∈ S.filter (fun z => σ < z.re), c z * Real.exp (z.re * t) * Real.cos (z.im * t) +
        ∑ z ∈ S.filter (fun z => z.re = σ), c z * Real.exp (z.re * t) * Real.cos (z.im * t) +
        ∑ z ∈ S.filter (fun z => z.re < σ), c z * Real.exp (z.re * t) * Real.cos (z.im * t) := by
    rw [polarScaleWeight, ← Finset.sum_filter_add_sum_filter_not S (fun z => σ < z.re)]
    rw [add_assoc]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not (S.filter fun z => ¬σ < z.re) (fun z => z.re = σ),
      Finset.filter_filter, Finset.filter_filter]
    congr 1
    · refine Finset.sum_congr (Finset.filter_congr fun z _ => ?_) fun _ _ => rfl
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨by rw [h]; exact lt_irrefl σ, h⟩
    · refine Finset.sum_congr (Finset.filter_congr fun z _ => ?_) fun _ _ => rfl
      constructor
      · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne (not_lt.mp h1) h2
      · intro h; exact ⟨not_lt.mpr h.le, h.ne⟩
  have hhigh : ∑ z ∈ S.filter (fun z => σ < z.re), c z * Real.exp (z.re * t) * Real.cos (z.im * t) =
      ∑ σ' ∈ (S.filter fun z => σ < z.re).image Complex.re,
        Real.exp (σ' * t) * leadingSum S c σ' t := by
    refine (Finset.sum_image' (fun z => c z * Real.exp (z.re * t) * Real.cos (z.im * t))
      fun z hz => ?_).symm
    rw [leadingSum, Finset.mul_sum, Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun y _ => ?_) fun y hy => ?_
    · constructor
      · intro h; exact ⟨by rw [h]; exact (Finset.mem_filter.mp hz).2, h⟩
      · rintro ⟨_, h⟩; exact h
    · rw [(Finset.mem_filter.mp hy).2.2]; ring
  have hmid : ∑ z ∈ S.filter (fun z => z.re = σ), c z * Real.exp (z.re * t) * Real.cos (z.im * t) =
      Real.exp (σ * t) * leadingSum S c σ t := by
    rw [leadingSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [(Finset.mem_filter.mp hz).2]; ring
  rw [hsplit, hhigh, hmid]

/-- **The line hierarchy law.** On a lattice configuration with nonnegative scale weight, each
line sum is nonnegative wherever all the lines to its right vanish. -/
theorem leadingSum_nonneg_of_higher_eq_zero {S : Finset ℂ} {c : ℂ → ℝ} {ω : ℝ} (hω : ω ≠ 0)
    (hlat : ∀ z ∈ S, ∃ k : ℤ, z.im = k * ω)
    (hw : ∀ t : ℝ, 0 < t → 0 ≤ polarScaleWeight S c t) {σ t₀ : ℝ}
    (hzero : ∀ σ' : ℝ, σ < σ' → leadingSum S c σ' t₀ = 0) : 0 ≤ leadingSum S c σ t₀ := by
  by_contra hneg
  rw [not_le] at hneg
  set T := leadingSum S c σ t₀ with hT
  obtain ⟨η, hη, hgap⟩ := exists_gap S σ
  set C := ∑ z ∈ S, |c z| with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun z _ => abs_nonneg _
  set P := 2 * π / |ω| with hP
  have hP0 : 0 < P := by positivity
  -- along `t₀ + mP` the higher lines vanish and the rest is `O(e^{(σ − η)t})`
  have hperiod : ∀ (σ' : ℝ) (m : ℕ), leadingSum S c σ' (t₀ + m * P) = leadingSum S c σ' t₀ := by
    intro σ' m
    rcases lt_or_gt_of_ne hω with hneg' | hpos
    · -- `P = 2π/|ω|` is an integer multiple of `2π/ω` up to sign
      have hlat' : ∀ z ∈ S, ∃ k : ℤ, z.im = k * (-ω) := fun z hz => by
        obtain ⟨k, hk⟩ := hlat z hz; exact ⟨-k, by rw [hk]; push_cast; ring⟩
      have := leadingSum_add_period (c := c) (neg_ne_zero.mpr hω) hlat' σ' t₀ m
      rwa [show 2 * π / -ω = P by rw [hP, abs_of_neg hneg']] at this
    · have := leadingSum_add_period (c := c) hω hlat σ' t₀ m
      rwa [show 2 * π / ω = P by rw [hP, abs_of_pos hpos]] at this
  -- choose `m` so that `t = t₀ + mP` is positive and `C e^{−ηt} < −T`
  have hT0 : 0 < -T := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt ((|t₀| + C / (-T) / η + 1) / P)
  set t := t₀ + m * P with htdef
  have hmP : |t₀| + C / (-T) / η + 1 < m * P := by
    rwa [div_lt_iff₀ hP0] at hm
  have hCT : 0 ≤ C / (-T) / η := div_nonneg (div_nonneg hC0 hT0.le) hη.le
  have ht : 0 < t := by
    have := neg_abs_le t₀
    linarith
  have hηt : C / (-T) < η * t := by
    have h1 : C / (-T) / η < t := by have := neg_abs_le t₀; linarith
    rwa [div_lt_iff₀ hη, mul_comm] at h1
  -- the decomposition at `t`
  have hsplit := polarScaleWeight_split S c σ t
  have hhigh : ∑ σ' ∈ (S.filter fun z => σ < z.re).image Complex.re,
      Real.exp (σ' * t) * leadingSum S c σ' t = 0 := by
    refine Finset.sum_eq_zero fun σ' hσ' => ?_
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hσ'
    rw [htdef, hperiod, hzero _ (Finset.mem_filter.mp hz).2, mul_zero]
  have hrest : |∑ z ∈ S.filter (fun z => z.re < σ), c z * Real.exp (z.re * t) * Real.cos (z.im * t)|
      ≤ C * Real.exp ((σ - η) * t) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ z ∈ S.filter (fun z => z.re < σ), |c z * Real.exp (z.re * t) * Real.cos (z.im * t)|
        ≤ ∑ z ∈ S.filter (fun z => z.re < σ), |c z| * Real.exp ((σ - η) * t) := by
          refine Finset.sum_le_sum fun z hz => ?_
          rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
          have hcos := Real.abs_cos_le_one (z.im * t)
          have hexp : Real.exp (z.re * t) ≤ Real.exp ((σ - η) * t) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
              (hgap z (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz).2) ht.le)
          calc |c z| * Real.exp (z.re * t) * |Real.cos (z.im * t)|
              ≤ |c z| * Real.exp (z.re * t) * 1 :=
                mul_le_mul_of_nonneg_left hcos (by positivity)
            _ ≤ |c z| * Real.exp ((σ - η) * t) := by
                rw [mul_one]; exact mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
      _ = (∑ z ∈ S.filter (fun z => z.re < σ), |c z|) * Real.exp ((σ - η) * t) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ C * Real.exp ((σ - η) * t) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun z _ _ => abs_nonneg _
  have hline : leadingSum S c σ t = T := by rw [htdef, hperiod]
  have h0 := hw t ht
  rw [hsplit, hhigh, zero_add, hline] at h0
  -- `0 ≤ e^{σt} T + R` with `T < 0` and `|R| ≤ C e^{(σ − η)t}`
  have hR := (abs_le.mp hrest).2
  have hkey : Real.exp (σ * t) * (-T) ≤ C * Real.exp ((σ - η) * t) := by linarith
  have hsplitexp : Real.exp ((σ - η) * t) = Real.exp (σ * t) * Real.exp (-(η * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplitexp, ← mul_assoc, mul_comm C, mul_assoc] at hkey
  have hkey' : -T ≤ C * Real.exp (-(η * t)) :=
    le_of_mul_le_mul_left hkey (Real.exp_pos _)
  -- but `C e^{−ηt} < −T`
  have hexp : C * Real.exp (-(η * t)) < -T := by
    have h1 : 1 + η * t ≤ Real.exp (η * t) := by
      have := Real.add_one_le_exp (η * t); linarith
    have h2 : C < -T * (η * t) := by have := (div_lt_iff₀ hT0).mp hηt; linarith
    have h3 : C < -T * Real.exp (η * t) := by
      have := mul_le_mul_of_nonneg_left h1 hT0.le
      linarith
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)]
    exact h3
  linarith

/-- **The leading line of a positive lattice configuration is nonnegative.** -/
theorem leadingSum_nonneg_of_lattice {S : Finset ℂ} {c : ℂ → ℝ} {ω σmax : ℝ} (hω : ω ≠ 0)
    (hlat : ∀ z ∈ S, ∃ k : ℤ, z.im = k * ω)
    (hw : ∀ t : ℝ, 0 < t → 0 ≤ polarScaleWeight S c t)
    (hmax : ∀ z ∈ S, c z ≠ 0 → z.re ≤ σmax) (t : ℝ) : 0 ≤ leadingSum S c σmax t := by
  refine leadingSum_nonneg_of_higher_eq_zero hω hlat hw fun σ' hσ' => ?_
  refine Finset.sum_eq_zero fun z hz => ?_
  by_cases hc : c z = 0
  · rw [hc, zero_mul]
  · have := hmax z (Finset.mem_filter.mp hz).1 hc
    rw [(Finset.mem_filter.mp hz).2] at this
    linarith

/-- **The second-line law.** The next line is nonnegative wherever the leading line vanishes. -/
theorem secondLine_nonneg_of_lattice {S : Finset ℂ} {c : ℂ → ℝ} {ω σ₁ σ₂ : ℝ} (hω : ω ≠ 0)
    (hlat : ∀ z ∈ S, ∃ k : ℤ, z.im = k * ω)
    (hw : ∀ t : ℝ, 0 < t → 0 ≤ polarScaleWeight S c t)
    (hlines : ∀ z ∈ S, c z ≠ 0 → σ₂ < z.re → z.re = σ₁) {t : ℝ}
    (hT₁ : leadingSum S c σ₁ t = 0) : 0 ≤ leadingSum S c σ₂ t := by
  refine leadingSum_nonneg_of_higher_eq_zero hω hlat hw fun σ' hσ' => ?_
  by_cases h : σ' = σ₁
  · rw [h, hT₁]
  · refine Finset.sum_eq_zero fun z hz => ?_
    by_cases hc : c z = 0
    · rw [hc, zero_mul]
    · have hre := (Finset.mem_filter.mp hz).2
      have := hlines z (Finset.mem_filter.mp hz).1 hc (by rw [hre]; exact hσ')
      exact absurd (hre.symm.trans this) h

end GaloisForLFunctions.ArithmeticPolarization
