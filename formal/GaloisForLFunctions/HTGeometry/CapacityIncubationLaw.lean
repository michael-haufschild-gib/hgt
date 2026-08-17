import GaloisForLFunctions.HTGeometry.SphericalPatchTube

/-!
# The capacity-compatible incubation law

A carrier patch with a uniform synthesis certificate makes its whole spherical tube easy through the
prescribed window: the Lipschitz coefficient map turns the tube radius into an operator-norm
distance, and Duhamel turns that into a slack the window length can pay.

Selecting one seed from a finite family whose good set has pointwise density `1-beta` keeps at least
that fraction of the tube.  Since the tube has surface measure at least a patch constant times the
`d`-th power of its radius, and the admissible radius is inversely proportional to the window, the
selected seed's good part of the tube is at least a constant times `L^{-d}`.
-/

open MeasureTheory Metric Set WithLp
open scoped Pointwise ENNReal

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry

noncomputable section

section Incubation

variable {f d : ℕ} {dd : Type*} [Fintype dd] [DecidableEq dd] {Γ : Type*}

open scoped Matrix.Norms.L2Operator

/-- **The tube is easy through the whole window.**  Every coefficient direction within `r` of the
carrier patch inherits the patch certificate at slack `epsMinus`, uniformly for `0 ≤ t ≤ L`. -/
theorem approxComplexity_le_of_mem_patchThickening
    (act : Γ → EuclideanSpace ℂ dd → EuclideanSpace ℂ dd) (chi : EuclideanSpace ℂ dd)
    {ψ : EuclideanSpace ℂ dd} (hψ : ‖ψ‖ = 1)
    (Hmap : PatchSpace f d →ₗ[ℝ] Matrix dd dd ℂ)
    (hherm : ∀ p, IsSelfAdjoint (Hmap p))
    {LH : ℝ} (hLH : 0 ≤ LH)
    (hlip : ∀ a b, ‖Hmap a - Hmap b‖ ≤ LH * ‖a - b‖)
    {PU : Set (EuclideanSpace ℝ (Fin f))} (hcompact : IsCompact (embedPatch (d := d) PU))
    (hnonempty : (embedPatch (d := d) PU).Nonempty)
    {eta epsMinus r L : ℝ} {B : ℕ}
    (hcert : ∀ y ∈ embedPatch (d := d) PU, ∀ s : ℝ, ∃ w : List Γ, w.length ≤ B ∧
      dist (orbitState (Hmap y) ψ s) (wordAct act w chi) ≤ eta)
    (hL : 0 ≤ L) (hgap : L * (LH * r) ≤ epsMinus - eta)
    {ω : sphere (0 : PatchSpace f d) 1} (hω : ω ∈ patchThickening (d := d) PU r)
    {t : ℝ} (ht0 : 0 ≤ t) (htL : t ≤ L) :
    approxComplexity act chi epsMinus (orbitState (Hmap (ω : PatchSpace f d)) ψ t) ≤ B := by
  obtain ⟨y, hy, hdist⟩ :=
    hcompact.exists_infDist_eq_dist hnonempty (ω : PatchSpace f d)
  have hle : dist (ω : PatchSpace f d) y ≤ r := by
    rw [← hdist]
    exact hω
  have hHdist : ‖Hmap (ω : PatchSpace f d) - Hmap y‖ ≤ LH * r := by
    refine le_trans (hlip _ _) ?_
    have hnorm : ‖(ω : PatchSpace f d) - y‖ ≤ r := by
      rw [← dist_eq_norm]
      exact hle
    exact mul_le_mul_of_nonneg_left hnorm hLH
  refine approxComplexity_orbitState_le_of_window act chi (hherm _) (hherm y) hψ
    (hcert y hy) ?_ ht0 htL
  refine le_trans (mul_le_mul_of_nonneg_left hHdist hL) hgap

end Incubation

/-! ## Seed selection on the tube -/

section Seed

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Type*} [Fintype Q] [Nonempty Q]

/-- **Fubini seed selection on a subset.**  A finite seed family whose good sets have pointwise
density `1-beta` has one seed whose good set carries that fraction of any measurable subset. -/
theorem exists_seed_measureReal_ge (μ : Measure Ω) [IsFiniteMeasure μ] (N : Set Ω)
    (G : Q → Set Ω) (hGmeas : ∀ q, MeasurableSet (G q)) {β : ℝ}
    (hdensity : ∀ x, (Fintype.card Q : ℝ) * (1 - β) ≤
      ∑ q, Set.indicator (G q) (1 : Ω → ℝ) x) :
    ∃ q, (1 - β) * μ.real N ≤ (μ.restrict N).real (G q) := by
  haveI : IsFiniteMeasure (μ.restrict N) := by
    constructor
    exact lt_of_le_of_lt (Measure.restrict_le_self Set.univ) (measure_lt_top μ Set.univ)
  obtain ⟨q, hq⟩ := exists_measureReal_ge_of_pointwise (μ := μ.restrict N) G hGmeas hdensity
  refine ⟨q, ?_⟩
  have huniv : (μ.restrict N).real Set.univ = μ.real N := by
    rw [Measure.real, Measure.restrict_apply_univ, Measure.real]
  rwa [huniv] at hq

/-- **Removing the exceptional set costs nothing.**  Intersecting with a conull generic-completion
set leaves every measure unchanged, so the generic spectral conclusions may be added to the good
seed set for free. -/
theorem measureReal_inter_conull (μ : Measure Ω) (A G : Set Ω) (hG : μ Gᶜ = 0) :
    μ.real (A ∩ G) = μ.real A := by
  rw [Measure.real, Measure.real, measure_inter_conull hG]

end Seed

/-! ## The incubation tail -/

section Tail

/-- **`(10)`: the incubation tail has the codimension exponent.**  A tube whose measure is at least
`aP * r^d` at the admissible radius `r = c/L` gives the selected seed a good set of measure at least
`(1-beta) * aP * c^d * L^{-d}`. -/
theorem incubation_tail_lower {aP c beta L m : ℝ} {d : ℕ} (hbeta : beta ≤ 1)
    (htube : aP * (c / L) ^ d ≤ m) :
    (1 - beta) * (aP * c ^ d / L ^ d) ≤ (1 - beta) * m := by
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  refine le_trans (le_of_eq ?_) htube
  rw [div_pow]
  ring

end Tail

end

end GaloisForLFunctions.HTGeometry
