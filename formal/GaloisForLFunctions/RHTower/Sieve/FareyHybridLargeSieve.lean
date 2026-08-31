import GaloisForLFunctions.RHTower.Sieve.FiniteAdditiveHybridLargeSieve
import GaloisForLFunctions.RHTower.Sieve.LogPolyProductScale

/-!
# Hybrid large sieve for reduced additive frequencies

Rescaling the Gallagher frequency to the ordinary Dirichlet height gives the physical
`(N + qT)` hybrid estimate.  Restricting the full additive Fourier family to units gives the
reduced-residue version used for Farey points and Kloosterman quadratic forms.
-/

open Complex MeasureTheory Set Finset

noncomputable section

namespace RHTower.Sieve

/-- Additively twisted Dirichlet polynomial in the physical height variable. -/
def additiveHybridDirichletPoly (q N : ℕ) (a : ℕ → ℂ)
    (d : ZMod (q + 1)) (t : ℝ) : ℂ :=
  additiveHybridLogPoly q N a d (t / (2 * Real.pi))

/-- Exact conversion from Gallagher frequency to physical Dirichlet height. -/
theorem integral_additiveHybridDirichletPoly_eq
    (q N : ℕ) (a : ℕ → ℂ) (d : ZMod (q + 1))
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in Set.Icc (-T) T, ‖additiveHybridDirichletPoly q N a d t‖ ^ 2) =
      2 * Real.pi *
        ∫ w in Set.Icc (-(T / (2 * Real.pi))) (T / (2 * Real.pi)),
          ‖additiveHybridLogPoly q N a d w‖ ^ 2 := by
  let g : ℝ → ℝ := fun t => ‖additiveHybridDirichletPoly q N a d t‖ ^ 2
  have hW : 0 ≤ T / (2 * Real.pi) := by positivity
  have hscale := integral_Icc_comp_scale g hW
  have hleft :
      (∫ w in Set.Icc (-(T / (2 * Real.pi))) (T / (2 * Real.pi)),
          ‖additiveHybridLogPoly q N a d w‖ ^ 2) =
        ∫ w in Set.Icc (-(T / (2 * Real.pi))) (T / (2 * Real.pi)),
          g (2 * Real.pi * w) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro w _
    dsimp only [g, additiveHybridDirichletPoly]
    congr 2
    field_simp
  have hright :
      (∫ t in Set.Icc (-(2 * Real.pi * (T / (2 * Real.pi))))
          (2 * Real.pi * (T / (2 * Real.pi))), g t) =
        ∫ t in Set.Icc (-T) T, ‖additiveHybridDirichletPoly q N a d t‖ ^ 2 := by
    congr 3 <;> field_simp
  rw [← hleft, hright] at hscale
  calc
    _ = 2 * Real.pi * ((2 * Real.pi)⁻¹ *
        ∫ t in Set.Icc (-T) T, ‖additiveHybridDirichletPoly q N a d t‖ ^ 2) := by
      field_simp
    _ = _ := by rw [← hscale]

/-- Physical-height hybrid large sieve over all additive frequencies. -/
theorem sum_integral_additiveHybridDirichletPoly_le_length
    (q N : ℕ) (a : ℕ → ℂ) {T : ℝ} (hT : 1 ≤ T) :
    ∑ d : ZMod (q + 1),
        (∫ t in Set.Icc (-T) T, ‖additiveHybridDirichletPoly q N a d t‖ ^ 2)
      ≤ (5 * Real.pi * Real.exp 1 * (N : ℝ) +
          5 * Real.pi * ((q + 1 : ℕ) : ℝ) * T) *
        ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  simp_rw [integral_additiveHybridDirichletPoly_eq q N a _ (zero_le_one.trans hT)]
  rw [← Finset.mul_sum]
  have hbase := sum_integral_normSq_additiveHybridLogPoly_le_length q N a hT
  have hscaled := mul_le_mul_of_nonneg_left hbase
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  calc
    _ ≤ 2 * Real.pi *
        (((5 * Real.exp 1 / 2) * (N : ℝ) +
            (5 / 2) * ((q + 1 : ℕ) : ℝ) * T) *
          ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) := hscaled
    _ = _ := by ring

/-- Deshouillers--Iwaniec hybrid Farey estimate over reduced residue frequencies. -/
theorem sum_units_integral_additiveHybridDirichletPoly_le_length
    (q N : ℕ) (a : ℕ → ℂ) {T : ℝ} (hT : 1 ≤ T) :
    ∑ d : (ZMod (q + 1))ˣ,
        (∫ t in Set.Icc (-T) T,
          ‖additiveHybridDirichletPoly q N a (d : ZMod (q + 1)) t‖ ^ 2)
      ≤ (5 * Real.pi * Real.exp 1 * (N : ℝ) +
          5 * Real.pi * ((q + 1 : ℕ) : ℝ) * T) *
        ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  classical
  let F : ZMod (q + 1) → ℝ := fun d =>
    ∫ t in Set.Icc (-T) T, ‖additiveHybridDirichletPoly q N a d t‖ ^ 2
  let s : Finset (ZMod (q + 1)) :=
    Finset.univ.image fun d : (ZMod (q + 1))ˣ => (d : ZMod (q + 1))
  have hinj : Set.InjOn (fun d : (ZMod (q + 1))ˣ => (d : ZMod (q + 1)))
      ((Finset.univ : Finset (ZMod (q + 1))ˣ) : Set (ZMod (q + 1))ˣ) := by
    intro d _ e _ h
    exact Units.ext h
  have heq :
      (∑ d : (ZMod (q + 1))ˣ, F (d : ZMod (q + 1))) = ∑ d ∈ s, F d := by
    dsimp only [s]
    rw [Finset.sum_image hinj]
  have hsub : (∑ d ∈ s, F d) ≤ ∑ d : ZMod (q + 1), F d :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun d _ _ => by dsimp only [F]; exact integral_nonneg fun _ => sq_nonneg _)
  have hfull := sum_integral_additiveHybridDirichletPoly_le_length q N a hT
  dsimp only [F] at heq hsub
  rw [heq]
  exact hsub.trans hfull

end RHTower.Sieve
