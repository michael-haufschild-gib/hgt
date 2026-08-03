import GaloisForLFunctions.HTGeometry.ClockSlabExistence
import GaloisForLFunctions.HTGeometry.ClockLocalTwoSpecies
import GaloisForLFunctions.HTGeometry.ClockProbeChartRiccati

/-!
# The two-species scale law on a null slab, in every dimension

A conformal factor depending only on the two null coordinates `x⁰ ± x¹` produces an effective
potential of the same slab form: the d'Alembertian and the gradient square of a slab function are
slab functions, computed from the bivariate derivatives by

`□ σ = -2(∂η∂ξ σ + ∂ξ∂η σ)`,  `Γ(σ, σ) = -4 ∂ξσ ∂ησ`.

So the probe families demanded by the two-species reconstruction exist for such a conformal factor,
in every dimension, and the conformal scale is recovered with no hypothesis on the probe families
at all. In dimension two every conformal factor is of this form, so this contains the
two-dimensional theorem.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped ContDiff

variable {n : ℕ}

/-! ## Sums over a slab -/

theorem sum_of_transverse_zero {f : Fin (n + 2) → ℝ}
    (hf : ∀ i, i ≠ 0 → i ≠ 1 → f i = 0) : ∑ i, f i = f 0 + f 1 := by
  rw [← Finset.sum_subset (Finset.subset_univ ({0, 1} : Finset (Fin (n + 2))))]
  · rw [Finset.sum_pair (slab_zero_ne_one n)]
  · intro i _ hi
    exact hf i (fun hc => hi (by simp [hc])) (fun hc => hi (by simp [hc]))

/-! ## The gradient square of a slab lift -/

variable {u A B : ℝ → ℝ → ℝ} {Ω : Set (ℝ × ℝ)}

/-- **The gradient square of a slab lift.** The null directions pair only with each other. -/
theorem gradPair_slabLift (h : IsC1On u A B Ω) {x : Fin (n + 2) → ℝ}
    (hx : slabCLM n x ∈ Ω) :
    (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.gradPair
        (slabLift u n) (slabLift u n) x
      = -4 * (A (x 0 + x 1) (x 0 - x 1) * B (x 0 + x 1) (x 0 - x 1)) := by
  have hz : ∀ i : Fin (n + 2), i ≠ 0 → i ≠ 1 →
      (slabEps n i)⁻¹ * coordPartial i (slabLift u n) x
        * coordPartial i (slabLift u n) x = 0 := by
    intro i h0 h1
    rw [coordPartial_slabLift_transverse h hx h0 h1]
    ring
  rw [ofSignature_gradPair, sum_of_transverse_zero hz,
    coordPartial_slabLift_zero h hx, coordPartial_slabLift_one h hx,
    slabEps_zero, slabEps_of_ne n (Ne.symm (slab_zero_ne_one n))]
  ring

/-! ## Smooth bivariate data -/

/-- A continuously differentiable function of two variables carries its partial derivatives on the
whole plane. -/
theorem isC1On_univ_of_contDiff {S : ℝ × ℝ → ℝ} (hS : ContDiff ℝ 1 S) :
    IsC1On (fun a b => S (a, b)) (planarFst S) (planarSnd S) univ where
  isOpen := isOpen_univ
  hasDerivFst := fun p _ => hasDerivAt_planarFst hS p.1 p.2
  hasDerivSnd := fun p _ => hasDerivAt_planarSnd hS p.1 p.2
  contFst := continuous_planarFst hS
  contSnd := continuous_planarSnd hS

/-- The first partial derivative of a smooth function of two variables, uncurried. -/
noncomputable def planarFstU (S : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => planarFst S p.1 p.2

/-- The second partial derivative of a smooth function of two variables, uncurried. -/
noncomputable def planarSndU (S : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => planarSnd S p.1 p.2

theorem contDiff_fderiv_of_contDiff_infty {S : ℝ × ℝ → ℝ} (hS : ContDiff ℝ ∞ S) :
    ContDiff ℝ ∞ (fderiv ℝ S) :=
  hS.fderiv_right (by exact_mod_cast le_top)

theorem contDiff_planarFstU {S : ℝ × ℝ → ℝ} (hS : ContDiff ℝ ∞ S) :
    ContDiff ℝ ∞ (planarFstU S) :=
  (contDiff_fderiv_of_contDiff_infty hS).clm_apply contDiff_const

theorem contDiff_planarSndU {S : ℝ × ℝ → ℝ} (hS : ContDiff ℝ ∞ S) :
    ContDiff ℝ ∞ (planarSndU S) :=
  (contDiff_fderiv_of_contDiff_infty hS).clm_apply contDiff_const

/-! ## The effective potential of a slab conformal factor -/

/-- **The effective potential of a slab conformal factor is a slab potential**, and it is
continuously differentiable. -/
theorem exists_slab_conformalPotential (n : ℕ) (a massSq : ℝ) {S : ℝ × ℝ → ℝ}
    (hS : ContDiff ℝ ∞ S) :
    ∃ vv : ℝ → ℝ → ℝ, ContDiff ℝ 1 (fun p : ℝ × ℝ => vv p.1 p.2) ∧
      (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.conformalPotential
          a massSq (slabLift (fun s t => S (s, t)) n)
        = slabLift vv n := by
  have hS1 : ContDiff ℝ 1 S := hS.of_le (by exact_mod_cast le_top)
  have hFst : ContDiff ℝ ∞ (planarFstU S) := contDiff_planarFstU hS
  have hSnd : ContDiff ℝ ∞ (planarSndU S) := contDiff_planarSndU hS
  have hC1 : IsC1On (fun a b => S (a, b)) (planarFst S) (planarSnd S) univ :=
    isC1On_univ_of_contDiff hS1
  have hC1A : IsC1On (planarFst S) (planarFst (planarFstU S)) (planarSnd (planarFstU S)) univ :=
    isC1On_univ_of_contDiff (hFst.of_le (by exact_mod_cast le_top))
  have hC1B : IsC1On (planarSnd S) (planarFst (planarSndU S)) (planarSnd (planarSndU S)) univ :=
    isC1On_univ_of_contDiff (hSnd.of_le (by exact_mod_cast le_top))
  refine ⟨fun ξ η => massSq * Real.exp (2 * S (ξ, η))
      + 2 * a * (planarSnd (planarFstU S) ξ η + planarFst (planarSndU S) ξ η)
      + 4 * a ^ 2 * (planarFst S ξ η * planarSnd S ξ η), ?_, ?_⟩
  · have h1 : ContDiff ℝ 1 fun p : ℝ × ℝ => massSq * Real.exp (2 * S p) :=
      contDiff_const.mul (Real.contDiff_exp.comp (contDiff_const.mul hS1))
    have hle : ((1 + 1 : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (1 + 1 : ℕ∞) ≤ ⊤)
    have h2 : ContDiff ℝ 1 fun p : ℝ × ℝ => planarSnd (planarFstU S) p.1 p.2 :=
      (hFst.fderiv_right hle).clm_apply contDiff_const
    have h3 : ContDiff ℝ 1 fun p : ℝ × ℝ => planarFst (planarSndU S) p.1 p.2 :=
      (hSnd.fderiv_right hle).clm_apply contDiff_const
    have h4 : ContDiff ℝ 1 fun p : ℝ × ℝ => planarFst S p.1 p.2 :=
      hFst.of_le (by exact_mod_cast le_top)
    have h5 : ContDiff ℝ 1 fun p : ℝ × ℝ => planarSnd S p.1 p.2 :=
      hSnd.of_le (by exact_mod_cast le_top)
    exact (h1.add (contDiff_const.mul (h2.add h3))).add (contDiff_const.mul (h4.mul h5))
  · funext x
    rw [SmoothMetricChart.conformalPotential, SmoothMetricChart.conformalDefect,
      dalembert_slabLift hC1 hC1A hC1B (mem_univ _),
      gradPair_slabLift hC1 (mem_univ _)]
    show massSq * Real.exp (2 * S (x 0 + x 1, x 0 - x 1))
        - (a * (-2 * (planarSnd (planarFstU S) (x 0 + x 1) (x 0 - x 1)
              + planarFst (planarSndU S) (x 0 + x 1) (x 0 - x 1)))
          + a ^ 2 * (-4 * (planarFst S (x 0 + x 1) (x 0 - x 1)
              * planarSnd S (x 0 + x 1) (x 0 - x 1))))
      = massSq * Real.exp (2 * S (x 0 + x 1, x 0 - x 1))
        + 2 * a * (planarSnd (planarFstU S) (x 0 + x 1) (x 0 - x 1)
            + planarFst (planarSndU S) (x 0 + x 1) (x 0 - x 1))
        + 4 * a ^ 2 * (planarFst S (x 0 + x 1) (x 0 - x 1)
            * planarSnd S (x 0 + x 1) (x 0 - x 1))
    ring

/-! ## The reconstruction -/

/-- **A slab clock species has probes on open regions at every event, in every dimension.** -/
theorem openProbes_conformalPotential_slab (n : ℕ) (a massSq : ℝ) {S : ℝ × ℝ → ℝ}
    (hS : ContDiff ℝ ∞ S) :
    OpenProbes (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
      ((SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.conformalPotential
        a massSq (slabLift (fun s t => S (s, t)) n)) := by
  obtain ⟨vv, hvv, heq⟩ := exists_slab_conformalPotential n a massSq hS
  rw [heq]
  intro x
  obtain ⟨W, hWopen, hxW, U, hUon, hUne, _⟩ := exists_clockProbe_on_slab hvv n x
  exact ⟨W, hWopen, hxW, U, hUon, hUne⟩

theorem contDiff_slabLift_of_contDiff {S : ℝ × ℝ → ℝ} (hS : ContDiff ℝ ∞ S) (n : ℕ) :
    ContDiff ℝ ∞ (slabLift (fun s t => S (s, t)) n) :=
  hS.comp (slabCLM n).contDiff

/-- **The two-species conformal clock scale law on a null slab, unconditionally, in every
dimension.**

For a conformal factor depending only on the two null coordinates, the conformal scale of the
spacetime is reconstructed from the effective potentials of one massive and one massless species,
with no hypothesis on the probe families: the required probes are proved to exist. -/
theorem twoSpecies_scale_reconstruction_slab (n : ℕ) (a : ℝ) {massSq : ℝ} (hmass : massSq ≠ 0)
    {S : ℝ × ℝ → ℝ} (hS : ContDiff ℝ ∞ S)
    {other₁ other₂ : (Fin (n + 2) → ℝ) → ℝ}
    (h₁ : ∀ (U : (Fin (n + 2) → ℝ) → ℝ) (W : Set (Fin (n + 2) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
          ((SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.conformalPotential
            a massSq (slabLift (fun s t => S (s, t)) n)) U W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
          other₁ U W)
    (h₂ : ∀ (U : (Fin (n + 2) → ℝ) → ℝ) (W : Set (Fin (n + 2) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
          ((SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.conformalPotential
            a 0 (slabLift (fun s t => S (s, t)) n)) U W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
          other₂ U W)
    (x : Fin (n + 2) → ℝ) :
    (other₁ x - other₂ x) / massSq
      = Real.exp (2 * slabLift (fun s t => S (s, t)) n x) :=
  scale_reconstruction_of_openProbes
    (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart a
    (contDiff_slabLift_of_contDiff hS n) hmass
    (openProbes_conformalPotential_slab n a massSq hS) h₁ h₂ x

end GaloisForLFunctions.HTGeometry
