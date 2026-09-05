import Mathlib

/-!
# Scale-convention algebra from arXiv:2608.29060

Exact positive homogeneity makes all positive discovery scales and scales at least one produce the
same quotient set.  An additive cost contributes at most an arbitrary `epsilon` once scale exceeds
`B / epsilon`.  These are the paper's convention-independent algebraic steps; its cited bounded
cell repetition theorem is intentionally not restated here.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.HTGeometry

/-- Quotients observed at all positive scales. -/
def bellmanShorelineAllScaleQuotients
    {U : Type*} (T : U → ℝ → ℝ) : Set ℝ :=
  {q | ∃ u d, 0 < d ∧ q = T u d / d}

/-- Quotients observed only at scales at least one. -/
def bellmanShorelineLargeScaleQuotients
    {U : Type*} (T : U → ℝ → ℝ) : Set ℝ :=
  {q | ∃ u d, 1 ≤ d ∧ q = T u d / d}

/-- Exact homogeneity identifies every positive-scale quotient with its unit-scale quotient. -/
theorem bellmanShoreline_quotient_eq_unit_of_homogeneous
    {U : Type*} {T : U → ℝ → ℝ}
    (hhomogeneous : ∀ u a d, 0 < a → T u (a * d) = a * T u d)
    (u : U) {d : ℝ} (hd : 0 < d) :
    T u d / d = T u 1 := by
  have hscale := hhomogeneous u d 1 hd
  rw [mul_one] at hscale
  rw [hscale]
  field_simp [hd.ne']

/-- For an exactly homogeneous search law, imposing `d ≥ 1` loses no quotient values. -/
theorem bellmanShoreline_allScaleQuotients_eq_largeScaleQuotients
    {U : Type*} {T : U → ℝ → ℝ}
    (hhomogeneous : ∀ u a d, 0 < a → T u (a * d) = a * T u d) :
    bellmanShorelineAllScaleQuotients T = bellmanShorelineLargeScaleQuotients T := by
  ext q
  constructor
  · rintro ⟨u, d, hd, rfl⟩
    refine ⟨u, 1, le_rfl, ?_⟩
    simp [bellmanShoreline_quotient_eq_unit_of_homogeneous hhomogeneous u hd]
  · rintro ⟨u, d, hd, rfl⟩
    exact ⟨u, d, lt_of_lt_of_le zero_lt_one hd, rfl⟩

/-- Additive cost `B` changes the quotient by at most `epsilon` beyond scale `B / epsilon`. -/
theorem bellmanShoreline_additiveCost_absorbed_at_largeScale
    {cost C B epsilon d : ℝ}
    (hd : 0 < d) (hepsilon : 0 < epsilon)
    (hcost : cost ≤ C * d + B) (hlarge : B / epsilon ≤ d) :
    cost / d ≤ C + epsilon := by
  have hBd : B ≤ epsilon * d := by
    simpa [mul_comm] using (div_le_iff₀ hepsilon).mp hlarge
  apply (div_le_iff₀ hd).mpr
  nlinarith

end GaloisForLFunctions.HTGeometry

end
