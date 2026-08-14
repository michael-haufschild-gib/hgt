import GaloisForLFunctions.HTGeometry.EulerShiftOperatorAlgebra

/-!
# The weighted leading vertex of a Newton polygon at an irrational level

Reading an operator `L = ∑_μ t^μ Φ_μ(θ)` at a Gevrey level `r` weights the monomial `t^μ θ^j` by

```text
λ_r(μ, j) = j − r μ .
```

Two facts about this weight carry the whole irrational case.

* **The maximum is attained.**  The degrees are bounded by the order of the operator, so
  `λ_r(μ, deg Φ_μ) → −∞` and only finitely many shifts can compete.
* **The maximizing shift is unique.**  Equality `deg Φ_μ − r μ = deg Φ_ν − r ν` with `μ ≠ ν`
  exhibits `r` as a quotient of integers.  For irrational `r` the weight is therefore injective, so
  the leading vertex of the polygon is a single monomial and there is a positive gap to the next
  one.

The gap is the quantity that separates the dominant term of the coefficient recursion from all the
others.  It exists only because the level is irrational; at a rational level several vertices may
share the leading weight, which is exactly the degeneracy the classical theory has to resolve by a
factorization.
-/

open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-- The weight of the shift `μ` at Gevrey level `r`. -/
noncomputable def weightedLevel (r : ℝ) (Φ : ℕ → Polynomial ℂ) (μ : ℕ) : ℝ :=
  (((Φ μ).natDegree : ℕ) : ℝ) - r * μ

theorem weightedLevel_zero (r : ℝ) (Φ : ℕ → Polynomial ℂ) :
    weightedLevel r Φ 0 = (((Φ 0).natDegree : ℕ) : ℝ) := by
  rw [weightedLevel]
  simp

/-- **At an irrational level distinct shifts have distinct weights.** -/
theorem weightedLevel_injective_of_irrational {r : ℝ} (hr : Irrational r)
    (Φ : ℕ → Polynomial ℂ) : Function.Injective (weightedLevel r Φ) := by
  intro μ ν h
  by_contra hne
  refine hr ⟨((((Φ ν).natDegree : ℤ) - ((Φ μ).natDegree : ℤ)) : ℚ)
      / (((ν : ℤ) - (μ : ℤ)) : ℚ), ?_⟩
  have hden : ((ν : ℝ) - (μ : ℝ)) ≠ 0 := by
    intro hc
    apply hne
    have : (μ : ℝ) = (ν : ℝ) := by linarith
    exact_mod_cast this
  rw [weightedLevel, weightedLevel] at h
  have hr' : r * ((ν : ℝ) - (μ : ℝ)) = (((Φ ν).natDegree : ℕ) : ℝ) - (((Φ μ).natDegree : ℕ) : ℝ) := by
    linarith
  push_cast
  field_simp
  linarith [hr']

/-- **The weight attains a maximum on the shifts that occur.** -/
theorem exists_max_weightedLevel {r : ℝ} (hr : 0 < r) {Φ : ℕ → Polynomial ℂ} {m : ℕ}
    (hdeg : ∀ μ, (Φ μ).natDegree ≤ m) {μ₀ : ℕ} (hμ₀ : Φ μ₀ ≠ 0) :
    ∃ ν, Φ ν ≠ 0 ∧ ∀ μ, Φ μ ≠ 0 → weightedLevel r Φ μ ≤ weightedLevel r Φ ν := by
  classical
  set L₀ : ℝ := weightedLevel r Φ μ₀ with hL₀
  set M : ℕ := ⌈((m : ℝ) - L₀) / r⌉₊ with hM
  have hmemM : ∀ μ : ℕ, L₀ ≤ weightedLevel r Φ μ → μ ≤ M := by
    intro μ hμ
    have hd : (((Φ μ).natDegree : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hdeg μ
    have hrmu : r * (μ : ℝ) ≤ (m : ℝ) - L₀ := by
      rw [weightedLevel] at hμ
      linarith
    have hle : (μ : ℝ) ≤ ((m : ℝ) - L₀) / r := by
      rw [le_div_iff₀ hr]
      linarith
    have := Nat.le_ceil (((m : ℝ) - L₀) / r)
    exact_mod_cast le_trans hle this
  have hμ₀M : μ₀ ∈ (Finset.range (M + 1)).filter (fun μ => Φ μ ≠ 0) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hμ₀⟩
    have := hmemM μ₀ le_rfl
    omega
  obtain ⟨ν, hν, hνmax⟩ :=
    Finset.exists_max_image ((Finset.range (M + 1)).filter (fun μ => Φ μ ≠ 0))
      (weightedLevel r Φ) ⟨μ₀, hμ₀M⟩
  refine ⟨ν, (Finset.mem_filter.mp hν).2, fun μ hμ => ?_⟩
  by_cases hcase : L₀ ≤ weightedLevel r Φ μ
  · exact hνmax μ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have := hmemM μ hcase
      omega), hμ⟩)
  · push Not at hcase
    exact le_trans (le_of_lt hcase) (hνmax μ₀ hμ₀M)

/-- **The gap below the leading vertex.**  At an irrational level the maximizing shift is strictly
ahead of every other shift that occurs, and on any finite window the advantage is uniform. -/
theorem exists_gap_weightedLevel {r : ℝ} (hr : Irrational r) {Φ : ℕ → Polynomial ℂ} {ν : ℕ}
    (hmax : ∀ μ, Φ μ ≠ 0 → weightedLevel r Φ μ ≤ weightedLevel r Φ ν) (M : ℕ) :
    ∃ η : ℝ, 0 < η ∧ ∀ μ ≤ M, μ ≠ ν → Φ μ ≠ 0 →
      weightedLevel r Φ μ + η ≤ weightedLevel r Φ ν := by
  classical
  set s : Finset ℕ := (Finset.range (M + 1)).filter (fun μ => μ ≠ ν ∧ Φ μ ≠ 0) with hs
  by_cases hempty : s = ∅
  · refine ⟨1, one_pos, fun μ hμ hμν hΦ => ?_⟩
    exfalso
    have : μ ∈ s := by
      rw [hs]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hμν, hΦ⟩
    rw [hempty] at this
    exact absurd this (Finset.notMem_empty μ)
  · obtain ⟨μ₁, hμ₁, hμ₁max⟩ :=
      Finset.exists_max_image s (weightedLevel r Φ) (Finset.nonempty_of_ne_empty hempty)
    rw [hs, Finset.mem_filter] at hμ₁
    obtain ⟨-, hμ₁ν, hμ₁Φ⟩ := hμ₁
    refine ⟨weightedLevel r Φ ν - weightedLevel r Φ μ₁, ?_, fun μ hμ hμν hΦ => ?_⟩
    · have hle := hmax μ₁ hμ₁Φ
      have hne : weightedLevel r Φ μ₁ ≠ weightedLevel r Φ ν := fun hc =>
        hμ₁ν (weightedLevel_injective_of_irrational hr Φ hc)
      cases lt_or_eq_of_le hle with
      | inl h => linarith
      | inr h => exact absurd h hne
    · have hmem : μ ∈ s := by
        rw [hs]
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hμν, hΦ⟩
      have := hμ₁max μ hmem
      linarith

end GaloisForLFunctions.HTGeometry
