import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheRestrictedWeilFormIsCompactlyNegative
import GaloisForLFunctions.HTGeometry.WeakSequentialCompactness

/-!
# Unit nonpositive limits do not vanish

For identity plus a compactly read form, exact unit normalization prevents
weak escape even at zero limiting energy. The compact term must retain a
negative contribution of at least one.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Unit vectors with vanishing upper energy bounds have a nonzero
nonpositive weak limit. -/
theorem compactPerturbation_unit_weakLimit_of_energy_upper_bound {J : E →L[ℂ] F}
    (hJ : IsCompactOperator J) (R : F →L[ℂ] F) {u : ℕ → E} {u₀ : E}
    (h : WeakConvC u u₀) (hu : ∀ n, ‖u n‖ = 1)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hQ : ∀ n, compactPerturbedEnergy J R (u n) ≤ ε n) :
    u₀ ≠ 0 ∧ compactPerturbedEnergy J R u₀ ≤ 0 := by
  have hB : ∀ n, ‖u n‖ ≤ 1 := fun n => (hu n).le
  have hr : Continuous fun x : F => (inner ℂ (R x) x).re :=
    Complex.continuous_re.comp (continuous_inner.comp (R.continuous.prodMk continuous_id))
  have hterm := (hr.tendsto (J u₀)).comp (tendsto_of_weakConvC hJ h hB)
  have hlim : Tendsto (fun n => compactPerturbedEnergy J R (u n)) atTop
      (𝓝 (1 + (inner ℂ (R (J u₀)) (J u₀)).re)) := by
    simpa only [compactPerturbedEnergy, hu, one_pow, Function.comp_apply] using
      (tendsto_const_nhds.add hterm)
  have hle : 1 + (inner ℂ (R (J u₀)) (J u₀)).re ≤ 0 :=
    le_of_tendsto_of_tendsto' hlim hε hQ
  refine ⟨?_, (compactPerturbation_le_of_weakConvC hJ R h hB hlim).trans hle⟩
  rintro rfl
  have hfalse : (1 : ℝ) ≤ 0 := by
    simpa only [map_zero, inner_zero_left, Complex.zero_re, add_zero] using hle
  exact (not_le_of_gt zero_lt_one) hfalse

/-- Exact unit mass closes the zero-energy endpoint of weak nonvanishing. -/
theorem compactPerturbation_unit_nonpositive_weakLimit {J : E →L[ℂ] F}
    (hJ : IsCompactOperator J) (R : F →L[ℂ] F) {u : ℕ → E} {u₀ : E}
    (h : WeakConvC u u₀) (hu : ∀ n, ‖u n‖ = 1)
    (hQ : ∀ n, compactPerturbedEnergy J R (u n) ≤ 0) :
    u₀ ≠ 0 ∧ compactPerturbedEnergy J R u₀ ≤ 0 :=
  compactPerturbation_unit_weakLimit_of_energy_upper_bound hJ R h hu
    tendsto_const_nhds hQ

/-- Bounded Hilbert sequences have subsequences converging against every
continuous linear functional. -/
theorem exists_weakConvC_subseq_of_bounded [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] (u : ℕ → E) {B : ℝ} (hB : ∀ n, ‖u n‖ ≤ B) :
    ∃ u₀ : E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ‖u₀‖ ≤ B ∧ WeakConvC (u ∘ φ) u₀ := by
  obtain ⟨u₀, φ, hφ, hnorm, hw⟩ := HTGeometry.exists_weaklyConvergent_subseq_of_bounded u B hB
  refine ⟨u₀, φ, hφ, hnorm, fun L => ?_⟩
  let y := (InnerProductSpace.toDual ℂ E).symm L
  have hy (x : E) : inner ℂ y x = L x := InnerProductSpace.toDual_symm_apply
  have ht := (continuous_star.tendsto _).comp (hw y)
  simpa only [Function.comp_def, RCLike.star_def, inner_conj_symm, hy] using ht

/-- Every unit nonpositive sequence has a nonzero nonpositive weak limit
after passage to a subsequence. -/
theorem exists_unit_nonpositive_weakLimit [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] {J : E →L[ℂ] F}
    (hJ : IsCompactOperator J) (R : F →L[ℂ] F) (u : ℕ → E)
    (hu : ∀ n, ‖u n‖ = 1) (hQ : ∀ n, compactPerturbedEnergy J R (u n) ≤ 0) :
    ∃ u₀ : E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ‖u₀‖ ≤ 1 ∧
      WeakConvC (u ∘ φ) u₀ ∧ u₀ ≠ 0 ∧ compactPerturbedEnergy J R u₀ ≤ 0 := by
  obtain ⟨u₀, φ, hφ, hnorm, hweak⟩ := exists_weakConvC_subseq_of_bounded u (fun n => (hu n).le)
  exact ⟨u₀, φ, hφ, hnorm, hweak,
    compactPerturbation_unit_nonpositive_weakLimit hJ R hweak
      (fun n => hu (φ n)) (fun n => hQ (φ n))⟩

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
