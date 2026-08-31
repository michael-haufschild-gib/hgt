import GaloisForLFunctions.HTGeometry.DominantConstantTermWild
import GaloisForLFunctions.HTGeometry.EulerWildProximity

/-!
# The dominant-constant-term case of the Euler relation

When the coefficient of `(z f′)^0` carries strictly more total degree than every other coefficient,
the tame alternative of the exponent dichotomy is impossible wherever `‖f‖` is large, so the wild
bound holds at every such point.  Integrating it over the circle bounds the characteristic by a
logarithmic-derivative proximity:

```text
T(r,f) ≤ m·m(r, f′/f) + m·log r + E.
```

This is the Newton case that Gol'dberg's theorem, as formalized, does not reach, and the inequality
above is the substitute: it is again of the form `T ≤ S`, the collapse behind Picard's theorem.
-/

namespace GaloisForLFunctions.HTGeometry

open ValueDistribution Polynomial

/-- **The wild bound holds everywhere when the constant term dominates.** -/
theorem exists_wild_of_dominant_constant_term {m : ℕ} (hm : 1 ≤ m) {C : ℕ → Polynomial ℂ}
    (hCm : C m ≠ 0) (hC0 : C 0 ≠ 0)
    (hdom : ∀ k, 1 ≤ k → k ≤ m → (C k).natDegree + k + 1 ≤ (C 0).natDegree)
    {Y W : ℂ → ℂ}
    (hrel : ∀ z : ℂ, ∑ k ∈ Finset.range (m + 1), (C k).eval (Y z) * (W z) ^ k = 0) :
    ∃ c R₂ : ℝ, 0 < c ∧ 1 ≤ R₂ ∧
      ∀ z : ℂ, R₂ ≤ ‖Y z‖ → c * ‖Y z‖ ^ (m + 1) ≤ ‖W z‖ ^ m := by
  obtain ⟨K, c, R₀, hK1, hc0, hc1, hR₀1, hdich⟩ := exists_dichotomy_of_relation hm hCm hrel
  obtain ⟨R₂, hR₂1, hnottame⟩ :=
    exists_not_tame_of_dominant_constant_term hm hC0 hdom hrel (K := K) (by linarith)
  refine ⟨c, max R₀ R₂, hc0, le_trans hR₀1 (le_max_left _ _), ?_⟩
  intro z hz
  rcases hdich z (le_trans (le_max_left _ _) hz) with htame | hwild
  · exact absurd htame (hnottame z (le_trans (le_max_right _ _) hz))
  · exact hwild

/-- **The characteristic is bounded by a logarithmic-derivative proximity** whenever the constant
term of the Euler relation dominates. -/
theorem exists_characteristic_le_logDeriv_of_dominant_constant_term {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (horder : ∀ z : ℂ, meromorphicOrderAt f z ≠ ⊤)
    {m : ℕ} (hm : 1 ≤ m) {C : ℕ → Polynomial ℂ} (hCm : C m ≠ 0) (hC0 : C 0 ≠ 0)
    (hdom : ∀ k, 1 ≤ k → k ≤ m → (C k).natDegree + k + 1 ≤ (C 0).natDegree)
    (hrel : ∀ z : ℂ, ∑ k ∈ Finset.range (m + 1),
      (C k).eval (f z) * (z * deriv f z) ^ k = 0) :
    ∃ E : ℝ, ∀ r : ℝ, 1 ≤ r → characteristic f ⊤ r
      ≤ (m : ℝ) * proximity (fun z => deriv f z / f z) ⊤ r + (m : ℝ) * Real.log r + E := by
  obtain ⟨c, R₂, hc0, hR₂1, hwild⟩ :=
    exists_wild_of_dominant_constant_term hm hCm hC0 hdom (Y := f)
      (W := fun z => z * deriv f z) hrel
  refine ⟨|Real.log c| + ((m : ℝ) + 1) * Real.log R₂, fun r hr => ?_⟩
  exact characteristic_le_logDeriv_of_wild hf horder hm hc0 hR₂1 hwild hr

end GaloisForLFunctions.HTGeometry
