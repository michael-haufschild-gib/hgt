import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.SeparatedLevelsCoupleThroughTheChebyshevError
import GaloisForLFunctions.ArithmeticIndexDescent.TouchingCellsPayTheFullMixedSource
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheLambdaRingOfTheScalingSurface

/-!
# Touching levels couple uniformly

Two copies of tests supported in `[0, ℓ]`, placed at `s` and `s + ℓ`, touch at one point. Their
Weil coupling has no gap to decay with, but it is bounded by a constant that depends on `ℓ` only.

* **Translation invariance** (`realWeilForm_shiftTest_shiftTest`): the pairing of copies at `s`
  and `t` depends on `t − s` only.
* **Endpoints** (`eq_zero_of_forall_lt`, `eq_zero_of_forall_gt`): a continuous function vanishing
  outside `[0, ℓ]` vanishes at both ends, so the copies are ordered across the touching point.
* **Uniform touching coupling** (`exists_abs_weilPair_touching_le`): for every `ℓ > 0` one constant
  `C` gives `|W(φ(· − s), ψ(· − s − ℓ))| ≤ C(‖φ‖² + ‖ψ‖²)` for all such `φ, ψ` and every `s`. This
  is ArithmeticIndexDescent's window bound for touching cells, carried to every level by
  translation.

At dyadic levels (`ℓ = log 2`, `s = j log 2`) adjacent levels couple through one constant for all
`j`, and levels at distance `d ≥ 2` couple through the Chebyshev error with Gamma cost `4^{−(d−1)}`
(`SeparatedLevelsCoupleThroughTheChebyshevError`). So every coupling cost of a generator orbit is
bounded, and only the Chebyshev part at distances `d ≥ 2` can fail to be summable.
-/

noncomputable section

open Set Filter Topology

namespace GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open ArithmeticCastelnuovoSeveri ArithmeticIndexDescent

/-- **Translation invariance**: copies at `s` and `t` pair like copies at `s − t` and `0`. -/
theorem realWeilForm_shiftTest_shiftTest (s t : ℝ) (φ ψ : realTests) :
    realWeilForm (shiftTest s φ) (shiftTest t ψ) = realWeilForm (shiftTest (s - t) φ) ψ := by
  show weilPair (scaleShift s φ.1) (scaleShift t ψ.1) = weilPair (scaleShift (s - t) φ.1) ψ.1
  exact weilPair_scaleShift s t φ.1 ψ.1

/-- A continuous function vanishing right of `a` vanishes at `a`. -/
theorem eq_zero_of_forall_gt {φ : ℝ → ℝ} (hφ : Continuous φ) {a : ℝ} (h : ∀ u, a < u → φ u = 0) :
    φ a = 0 := by
  have h1 : Tendsto φ (𝓝[>] a) (𝓝 (φ a)) := (hφ.tendsto a).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto φ (𝓝[>] a) (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun u hu => (h u hu).symm)
  exact tendsto_nhds_unique h1 h2

/-- A continuous function vanishing left of `a` vanishes at `a`. -/
theorem eq_zero_of_forall_lt {φ : ℝ → ℝ} (hφ : Continuous φ) {a : ℝ} (h : ∀ u, u < a → φ u = 0) :
    φ a = 0 := by
  have h1 : Tendsto φ (𝓝[<] a) (𝓝 (φ a)) := (hφ.tendsto a).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto φ (𝓝[<] a) (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun u hu => (h u hu).symm)
  exact tendsto_nhds_unique h1 h2

/-- **Touching levels couple uniformly.** For every `ℓ > 0` there is `C ≥ 0` such that copies at
`s` and `s + ℓ` of real tests vanishing outside `[0, ℓ]` satisfy
`|W(φ(· − s), ψ(· − s − ℓ))| ≤ C(‖φ‖² + ‖ψ‖²)`, for every `s`. -/
theorem exists_abs_weilPair_touching_le {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ) (φ ψ : realTests),
      (∀ u, u ∉ Icc 0 ℓ → φ.1 u = 0) → (∀ u, u ∉ Icc 0 ℓ → ψ.1 u = 0) →
      |realWeilForm (shiftTest s φ) (shiftTest (s + ℓ) ψ)| ≤
        C * (sectionMass φ.1 + sectionMass ψ.1) := by
  obtain ⟨C, hC, hbound⟩ := exists_orderedWeil_window_mass_bound hℓ
  refine ⟨C, hC, fun s φ ψ hφ hψ => ?_⟩
  -- the right end of `φ` and the left end of `ψ` vanish
  have hφℓ : φ.1 ℓ = 0 :=
    eq_zero_of_forall_gt φ.2.1.continuous fun u hu => hφ u fun hm => by linarith [(mem_Icc.mp hm).2]
  have hψ0 : ψ.1 0 = 0 :=
    eq_zero_of_forall_lt ψ.2.1.continuous fun u hu => hψ u fun hm => by linarith [(mem_Icc.mp hm).1]
  rw [realWeilForm_shiftTest_shiftTest, show s - (s + ℓ) = -ℓ by ring]
  have h := hbound 0 (shiftTest (-ℓ) φ) ψ
    (fun u hu => by
      show φ.1 (u - -ℓ) = 0
      refine hφ _ fun hm => ?_
      have := (mem_Icc.mp hm)
      rcases lt_or_ge u 0 with h0 | h0
      · rw [abs_of_neg h0] at hu; linarith
      · rw [abs_of_nonneg h0] at hu; linarith)
    (fun u hu => hψ u fun hm => by
      rw [abs_of_nonneg (mem_Icc.mp hm).1] at hu; linarith [(mem_Icc.mp hm).2])
    (fun u hu => by
      show φ.1 (u - -ℓ) = 0
      rcases hu.lt_or_eq with h0 | h0
      · exact hφ _ fun hm => by linarith [(mem_Icc.mp hm).2]
      · rw [← h0, zero_sub, neg_neg]; exact hφℓ)
    (fun u hu => by
      rcases hu.lt_or_eq with h0 | h0
      · exact hψ u fun hm => by linarith [(mem_Icc.mp hm).1]
      · rw [h0]; exact hψ0)
  rwa [shiftTest, sectionMass_shift] at h

/-- At dyadic levels: adjacent levels `j, j + 1` of copies of tests on `[0, log 2]` couple through
one constant, for every `j`. -/
theorem exists_abs_weilPair_adjacent_dyadic_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (φ ψ : realTests),
      (∀ u, u ∉ Icc 0 (Real.log 2) → φ.1 u = 0) → (∀ u, u ∉ Icc 0 (Real.log 2) → ψ.1 u = 0) →
      |realWeilForm (shiftTest (j * Real.log 2) φ) (shiftTest ((j + 1 : ℕ) * Real.log 2) ψ)| ≤
        C * (sectionMass φ.1 + sectionMass ψ.1) := by
  obtain ⟨C, hC, h⟩ := exists_abs_weilPair_touching_le (Real.log_pos one_lt_two)
  refine ⟨C, hC, fun j φ ψ hφ hψ => ?_⟩
  have e : ((j + 1 : ℕ) : ℝ) * Real.log 2 = j * Real.log 2 + Real.log 2 := by push_cast; ring
  rw [e]
  exact h _ φ ψ hφ hψ

end GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
