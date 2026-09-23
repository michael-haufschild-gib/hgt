import GaloisForLFunctions.HTGeometry.InterfinityGeometry.MultiTimeRegions

/-!
# The multi-time source cochain

The cubical source cochain of `d` independent future times is the product

`b_V(s) = ∏_j (e^{-V_j s_j} − 1)`,

and the weighted norm on the cube factorizes coordinatewise.  Each factor is finite exactly because
`β_j > −2`, so the cochain lies in the weighted space for every finite time tuple, and its squared
norm is the product of the one-time squared norms.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- The cubical source cochain. -/
def multiLaplaceCochain (V s : Fin d → ℝ) : ℝ := ∏ j, laplaceCochain (V j) (s j)

/-- The cubical weight. -/
def multiWeight (β s : Fin d → ℝ) : ℝ := ∏ j, s j ^ (β j - 1)

/-- The weighted square of the cubical cochain factorizes coordinatewise. -/
theorem multiLaplace_sq_weight_factor (β V s : Fin d → ℝ) :
    (multiLaplaceCochain V s) ^ (2 : ℕ) * multiWeight β s =
      ∏ j, (laplaceCochain (V j) (s j)) ^ (2 : ℕ) * s j ^ (β j - 1) := by
  rw [multiLaplaceCochain, multiWeight, ← Finset.prod_pow, ← Finset.prod_mul_distrib]

/-- The cubical measure: Lebesgue measure on each open unit factor. -/
abbrev cubeMeasure (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1)

/-- **The cubical source cochain lies in the weighted space exactly because every weight exponent
exceeds `−2`.** -/
theorem integrable_multiLaplaceCochain_sq {β : Fin d → ℝ} (hβ : ∀ j, -2 < β j) {V : Fin d → ℝ}
    (hV : ∀ j, 0 ≤ V j) :
    Integrable (fun s : Fin d → ℝ => (multiLaplaceCochain V s) ^ (2 : ℕ) * multiWeight β s)
      (cubeMeasure d) := by
  have hfac : (fun s : Fin d → ℝ => (multiLaplaceCochain V s) ^ (2 : ℕ) * multiWeight β s) =
      fun s : Fin d → ℝ => ∏ j, (fun u : ℝ => (laplaceCochain (V j) u) ^ (2 : ℕ) * u ^ (β j - 1)) (s j) :=
    funext fun s => multiLaplace_sq_weight_factor β V s
  rw [hfac]
  exact Integrable.fintype_prod fun j => integrableOn_laplaceCochain_sq (hβ j) (hV j)

/-- **The weighted square norm factorizes.** -/
theorem integral_multiLaplaceCochain_sq (β V : Fin d → ℝ) :
    (∫ s, (multiLaplaceCochain V s) ^ (2 : ℕ) * multiWeight β s ∂(cubeMeasure d)) =
      ∏ j, ∫ u in Ioo (0 : ℝ) 1, (laplaceCochain (V j) u) ^ (2 : ℕ) * u ^ (β j - 1) := by
  have hfac : (fun s : Fin d → ℝ => (multiLaplaceCochain V s) ^ (2 : ℕ) * multiWeight β s) =
      fun s : Fin d → ℝ => ∏ j, (fun u : ℝ => (laplaceCochain (V j) u) ^ (2 : ℕ) * u ^ (β j - 1)) (s j) :=
    funext fun s => multiLaplace_sq_weight_factor β V s
  rw [hfac]
  exact integral_fintype_prod_eq_prod (𝕜 := ℝ)
    (μ := fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1))
    (fun j u => (laplaceCochain (V j) u) ^ (2 : ℕ) * u ^ (β j - 1))

/-! ## The cubical cocycle law -/

/-- In every coordinate the cubical cochain obeys the one-time cocycle law. -/
theorem multiLaplaceCochain_add (V W s : Fin d → ℝ) (j : Fin d) :
    multiLaplaceCochain (Function.update V j (V j + W j)) s =
      multiLaplaceCochain V s +
        Real.exp (-(V j * s j)) * multiLaplaceCochain (Function.update V j (W j)) s := by
  classical
  have hsplit : laplaceCochain (V j + W j) (s j) =
      laplaceCochain (V j) (s j) + Real.exp (-(V j * s j)) * laplaceCochain (W j) (s j) :=
    laplaceCochain_add (V j) (W j) (s j)
  simp only [multiLaplaceCochain]
  rw [Finset.prod_eq_prod_sdiff_singleton_mul (Finset.mem_univ j),
    Finset.prod_eq_prod_sdiff_singleton_mul (Finset.mem_univ j) (fun i =>
      laplaceCochain (V i) (s i)),
    Finset.prod_eq_prod_sdiff_singleton_mul (Finset.mem_univ j) (fun i =>
      laplaceCochain (Function.update V j (W j) i) (s i))]
  have hdiff : ∀ i ∈ Finset.univ \ {j},
      laplaceCochain (Function.update V j (V j + W j) i) (s i) = laplaceCochain (V i) (s i) := by
    intro i hi
    have hij : i ≠ j := by
      simpa using (Finset.mem_sdiff.1 hi).2
    rw [Function.update_of_ne hij]
  have hdiff' : ∀ i ∈ Finset.univ \ {j},
      laplaceCochain (Function.update V j (W j) i) (s i) = laplaceCochain (V i) (s i) := by
    intro i hi
    have hij : i ≠ j := by
      simpa using (Finset.mem_sdiff.1 hi).2
    rw [Function.update_of_ne hij]
  rw [Finset.prod_congr rfl hdiff, Finset.prod_congr rfl hdiff']
  simp only [Function.update_self]
  rw [hsplit]
  ring

end

end GaloisForLFunctions.HTGeometry.Interfinity
