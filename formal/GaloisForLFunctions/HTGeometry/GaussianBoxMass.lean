import GaloisForLFunctions.HTGeometry.BoundedSumConcentration

/-!
# A Gaussian coefficient vector lies in an explicit box with probability at least one half

A standard Gaussian has moment generating function `exp(t²/2)`, so it is subgaussian with proxy one
and its two-sided tail at level `B` is at most `2exp(-B²/2)`.  Choosing `B² ≥ 2 log(8m)` makes each
tail at most `1/(4m)`, and the union bound over the `m` coefficients leaves at least three quarters
of the mass inside the box `[-B,B]^m`.

The box is explicit: `B = ⌈√(2 log(8m))⌉ + 1` works, and no independence between coefficients is
used -- only subadditivity.
-/

open MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section GaussianBox

variable {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]

/-- **A standard Gaussian is subgaussian with proxy one.** -/
theorem hasSubgaussianMGF_of_standardGaussian {X : Ω → ℝ} (hmeas : AEMeasurable X p)
    (hX : p.map X = gaussianReal 0 1) : HasSubgaussianMGF X 1 p := by
  constructor
  · intro t
    have hiff := integrable_map_measure (μ := p) (f := X) (g := fun x : ℝ => Real.exp (t * x))
      (by fun_prop) hmeas
    rw [hX] at hiff
    exact hiff.mp (integrable_exp_mul_gaussianReal t)
  · intro t
    rw [mgf_gaussianReal hX t]
    simp

/-- **The two-sided Gaussian tail.** -/
theorem measureReal_abs_ge_le_of_standardGaussian {X : Ω → ℝ} (hmeas : AEMeasurable X p)
    (hX : p.map X = gaussianReal 0 1) {t : ℝ} (ht : 0 ≤ t) :
    p.real {ω | t ≤ |X ω|} ≤ 2 * Real.exp (-t ^ 2 / 2) := by
  classical
  have hsub : HasSubgaussianMGF X 1 p := hasSubgaussianMGF_of_standardGaussian hmeas hX
  have hneg : HasSubgaussianMGF (fun ω => -X ω) 1 p := hsub.neg
  have h1 := hsub.measure_ge_le ht
  have h2 := hneg.measure_ge_le ht
  have hunion : {ω | t ≤ |X ω|} ⊆ {ω | t ≤ X ω} ∪ {ω | t ≤ -X ω} := by
    intro ω hω
    rcases abs_cases (X ω) with ⟨heq, -⟩ | ⟨heq, -⟩
    · left
      rw [Set.mem_setOf_eq] at hω ⊢
      rw [heq] at hω
      exact hω
    · right
      rw [Set.mem_setOf_eq] at hω ⊢
      rw [heq] at hω
      exact hω
  have hmono : p.real {ω | t ≤ |X ω|}
      ≤ p.real {ω | t ≤ X ω} + p.real {ω | t ≤ -X ω} := by
    calc p.real {ω | t ≤ |X ω|} ≤ p.real ({ω | t ≤ X ω} ∪ {ω | t ≤ -X ω}) :=
          measureReal_mono hunion (measure_ne_top _ _)
      _ ≤ p.real {ω | t ≤ X ω} + p.real {ω | t ≤ -X ω} := measureReal_union_le _ _
  have h1' : p.real {ω | t ≤ X ω} ≤ Real.exp (-t ^ 2 / 2) := by
    refine le_trans h1 (le_of_eq ?_)
    norm_num
  have h2' : p.real {ω | t ≤ -X ω} ≤ Real.exp (-t ^ 2 / 2) := by
    refine le_trans h2 (le_of_eq ?_)
    norm_num
  linarith

/-- **The explicit Gaussian box.**  With `B² ≥ 2 log(8m)` the coefficient vector stays in
`[-B,B]^m` with probability at least one half. -/
theorem half_le_measureReal_box {m : ℕ} (hm : 0 < m) (J : Fin m → Ω → ℝ)
    (hmeas : ∀ a, Measurable (J a)) (hJ : ∀ a, p.map (J a) = gaussianReal 0 1)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : 2 * Real.log (8 * m) ≤ B ^ 2) :
    1 / 2 ≤ p.real {ω | ∀ a, |J a ω| ≤ B} := by
  classical
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hexp : Real.exp (-B ^ 2 / 2) ≤ 1 / (8 * (m : ℝ)) := by
    have hlog : Real.log (8 * (m : ℝ)) ≤ B ^ 2 / 2 := by linarith
    have hpos : (0 : ℝ) < 8 * (m : ℝ) := by positivity
    calc Real.exp (-B ^ 2 / 2) = (Real.exp (B ^ 2 / 2))⁻¹ := by
          rw [← Real.exp_neg]
          congr 1
          ring
      _ ≤ (Real.exp (Real.log (8 * (m : ℝ))))⁻¹ := by
          rw [inv_le_inv₀ (Real.exp_pos _) (Real.exp_pos _)]
          exact Real.exp_le_exp.mpr hlog
      _ = 1 / (8 * (m : ℝ)) := by
          rw [Real.exp_log hpos, one_div]
  have hcompl : {ω | ∀ a, |J a ω| ≤ B}ᶜ ⊆ ⋃ a : Fin m, {ω | B ≤ |J a ω|} := by
    intro ω hω
    rw [Set.mem_compl_iff, Set.mem_setOf_eq] at hω
    push Not at hω
    obtain ⟨a, ha⟩ := hω
    exact Set.mem_iUnion.mpr ⟨a, le_of_lt ha⟩
  have hbound : p.real ({ω | ∀ a, |J a ω| ≤ B}ᶜ) ≤ 1 / 4 := by
    calc p.real ({ω | ∀ a, |J a ω| ≤ B}ᶜ)
        ≤ p.real (⋃ a : Fin m, {ω | B ≤ |J a ω|}) :=
          measureReal_mono hcompl (measure_ne_top _ _)
      _ ≤ ∑ a : Fin m, p.real {ω | B ≤ |J a ω|} := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _a : Fin m, 2 * Real.exp (-B ^ 2 / 2) :=
          Finset.sum_le_sum fun a _ =>
            measureReal_abs_ge_le_of_standardGaussian (hmeas a).aemeasurable (hJ a) hB0
      _ = (m : ℝ) * (2 * Real.exp (-B ^ 2 / 2)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ (m : ℝ) * (2 * (1 / (8 * (m : ℝ)))) := by
          have : 2 * Real.exp (-B ^ 2 / 2) ≤ 2 * (1 / (8 * (m : ℝ))) := by linarith
          exact mul_le_mul_of_nonneg_left this (le_of_lt hmR)
      _ = 1 / 4 := by
          field_simp
          ring
  have htotal : p.real {ω | ∀ a, |J a ω| ≤ B} + p.real ({ω | ∀ a, |J a ω| ≤ B}ᶜ) = 1 := by
    have hmeasSet : MeasurableSet {ω | ∀ a, |J a ω| ≤ B} := by
      have : {ω | ∀ a, |J a ω| ≤ B} = ⋂ a : Fin m, {ω | |J a ω| ≤ B} := by
        ext ω
        simp
      rw [this]
      exact MeasurableSet.iInter fun a => measurableSet_le ((hmeas a).abs) measurable_const
    exact probReal_add_probReal_compl hmeasSet
  linarith

end GaussianBox

end GaloisForLFunctions.HTGeometry
