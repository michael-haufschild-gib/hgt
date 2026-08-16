import GaloisForLFunctions.HTGeometry.SiegelCoeffMap
import GaloisForLFunctions.HTGeometry.PolydiscCoeffVanishing

/-!
# The Siegel gain

Combining the counting step with the multi-index Schwarz estimate: once there are more coefficients
than Taylor conditions, some nonzero polynomial in the given functions is smaller on the small
polydiscs than its bound on the large ones, by the fixed factor

`(N+1)^n · (r/R)^N · ∑ (j+1)^n (r/R)^j`.

The bound on the large polydiscs is left universally quantified, so the statement can be applied
after the comparison constant of a cover has been fixed — that is how a periodicity argument turns
the gain into vanishing.
-/

namespace GaloisForLFunctions.HTGeometry

variable {n m : ℕ} {ι : Type*} [Fintype ι]

/-- The multi-indices of total degree below `N`. -/
noncomputable def lowDegreeIndices (n N : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.range N).filter fun β => ∑ i, β i < N

theorem mem_lowDegreeIndices {n N : ℕ} {β : Fin n → ℕ} :
    β ∈ lowDegreeIndices n N ↔ ∑ i, β i < N := by
  classical
  rw [lowDegreeIndices, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    exact lt_of_le_of_lt (Finset.single_le_sum (f := β) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ i)) h

/-- **The Siegel gain.**  A nonzero polynomial in the given functions whose value on every small
polydisc is smaller than its bound on the large ones by the Schwarz factor. -/
theorem exists_ne_zero_siegel_gain {N : ℕ}
    (f : Fin (n + 1) → (Fin n → ℂ) → ℂ) (hf : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (f k))
    (c : ι → (Fin n → ℂ)) {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hcount : Fintype.card ι * N ^ n < (m + 1) ^ (n + 1)) :
    ∃ a : (Fin (n + 1) → Fin (m + 1)) → ℂ, a ≠ 0 ∧
      ∀ M : ℝ, (∀ i : ι, ∀ θ : Fin n → ℝ,
          ‖siegelCombination f a (torusMap (c i) (fun _ => R) θ)‖ ≤ M) →
        ∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r →
          ‖siegelCombination f a (c i + y)‖
            ≤ M * (((N + 1) ^ n : ℕ) : ℝ) * (r / R) ^ N *
              ∑' j : ℕ, (((j + 1) ^ n : ℕ) : ℝ) * (r / R) ^ j := by
  classical
  have hcont : ∀ k, Continuous (f k) := fun k => (hf k).continuous
  obtain ⟨a, ha, hvan⟩ :=
    exists_ne_zero_poly_polydiscCoeff_eq_zero (m := m) (N := N) f hcont c hR
      (lowDegreeIndices n N) (fun β hβ => mem_lowDegreeIndices.mp hβ) hcount
  refine ⟨a, ha, ?_⟩
  intro M hM i y hy
  refine norm_le_of_polydiscCoeff_vanish (differentiable_siegelCombination hf a) (c i) hR hr hrR
    (hM i) ?_ hy
  intro β hβ
  exact hvan i β (mem_lowDegreeIndices.mpr hβ)

end GaloisForLFunctions.HTGeometry
