import GaloisForLFunctions.HTGeometry.AbeLeadingDeterminant
import GaloisForLFunctions.HTGeometry.AbeNormalizedDampingTannery

/-!
# Determinant transfer for normalized damping expansions

This composes the two valid ingredients of the graded-damping route.  If the
finite packet matrix has an *actual normalized entrywise expansion* with an
invertible leading matrix and summable polynomial-exponential complement
coefficients, its determinant is eventually nonzero.  The phases need only be
positive term by term; no uniform gap is present in the theorem.

The expansion remains an output to be proved from Abe's explicit multiplier,
not an interface substituted for the target theorem.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Graded normalized determinant transfer.** Let `V` be the nonzero leading
matrix of a finite packet evaluation matrix `M`.  Suppose each entry of
`B⁻ᴰ • M B` is exactly `V` plus a summable family of normalized
polynomial-exponential terms.  Strict positivity of each individual phase
then suffices for `det (M B) ≠ 0` eventually. -/
theorem eventually_det_ne_zero_of_normalized_damping_matrix_expansion
    {Q ι : Type*} [Fintype Q] [DecidableEq Q]
    (D : ℕ) (V : Matrix Q Q ℂ) (M : ℝ → Matrix Q Q ℂ)
    (c : ι → Q → Q → ℂ) (e : ι → Q → Q → ℕ) (a : ι → Q → Q → ℝ)
    (ha : ∀ z i j, 0 < a z i j)
    (hsum : ∀ i j, Summable (fun z ↦ ‖c z i j‖))
    (hM : ∀ B i j, ((((B⁻¹) ^ D : ℝ) : ℂ) • M B) i j =
      V i j + tsum (fun z ↦ normalizedDampingTerm D (fun z ↦ c z i j)
        (fun z ↦ e z i j) (fun z ↦ a z i j) B z))
    (hV : V.det ≠ 0) :
    ∀ᶠ B in atTop, (M B).det ≠ 0 := by
  apply eventually_det_ne_zero_of_tendsto_smul_matrix
    (fun B ↦ (((B⁻¹) ^ D : ℝ) : ℂ)) M V
  · apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have htail := tendsto_tsum_normalizedDampingTerm_zero D (fun z ↦ c z i j)
      (fun z ↦ e z i j) (fun z ↦ a z i j) (fun z ↦ ha z i j) (hsum i j)
    have hconst : Tendsto (fun _ : ℝ ↦ V i j) atTop (nhds (V i j)) :=
      tendsto_const_nhds
    have hlimit : Tendsto (fun B : ℝ ↦ V i j + tsum (fun z ↦
        normalizedDampingTerm D (fun z ↦ c z i j) (fun z ↦ e z i j)
          (fun z ↦ a z i j) B z)) atTop (nhds (V i j)) := by
      simpa using hconst.add htail
    refine hlimit.congr' (Filter.Eventually.of_forall ?_)
    intro B
    exact (hM B i j).symm
  · exact hV

/-- **Row-graded normalized determinant transfer.**  This is the form used by
the distinct-speed construction: `S B` may normalize every jet row by its own
power of `B`, while the normalized entries have summable damping expansions. -/
theorem eventually_det_ne_zero_of_left_normalized_damping_matrix_expansion
    {Q ι : Type*} [Fintype Q] [DecidableEq Q]
    (D : ℕ) (S M : ℝ → Matrix Q Q ℂ) (V : Matrix Q Q ℂ)
    (c : ι → Q → Q → ℂ) (e : ι → Q → Q → ℕ) (a : ι → Q → Q → ℝ)
    (ha : ∀ z i j, 0 < a z i j)
    (hsum : ∀ i j, Summable (fun z ↦ ‖c z i j‖))
    (hM : ∀ B i j, (S B * M B) i j =
      V i j + tsum (fun z ↦ normalizedDampingTerm D (fun z ↦ c z i j)
        (fun z ↦ e z i j) (fun z ↦ a z i j) B z))
    (hV : V.det ≠ 0) :
    ∀ᶠ B in atTop, (M B).det ≠ 0 := by
  apply eventually_det_ne_zero_of_tendsto_left_mul_matrix S M V
  · apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have htail := tendsto_tsum_normalizedDampingTerm_zero D (fun z ↦ c z i j)
      (fun z ↦ e z i j) (fun z ↦ a z i j) (fun z ↦ ha z i j) (hsum i j)
    have hconst : Tendsto (fun _ : ℝ ↦ V i j) atTop (nhds (V i j)) :=
      tendsto_const_nhds
    have hlimit : Tendsto (fun B : ℝ ↦ V i j + tsum (fun z ↦
        normalizedDampingTerm D (fun z ↦ c z i j) (fun z ↦ e z i j)
          (fun z ↦ a z i j) B z)) atTop (nhds (V i j)) := by
      simpa using hconst.add htail
    refine hlimit.congr' (Filter.Eventually.of_forall ?_)
    intro B
    exact (hM B i j).symm
  · exact hV

end

end GaloisForLFunctions.HTGeometry
