import GaloisForLFunctions.RHTower.FokasLenellsCutoffWeakBounds

/-!
# Exact strong and weak cutoff limits

Weak convergence of every fixed matrix coefficient already forces zeroth
order and real time. In that surviving case the existing strong convergence
identifies the unique actual raw limit, before and after Cauchy compression.
-/

open MeasureTheory Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

private theorem negative_nat_tendsto : Tendsto (fun k : ℕ => -(k : ℝ)) atTop atBot :=
  tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop

private theorem complex_strong_good (n : ℕ) (τ : ℂ) (hn : n = 0) (hi : τ.im = 0) (u : SoninL2) :
    Tendsto (fun a => cutoffComplexOperator a n τ u) atBot
      (𝓝 (evolution τ.re u)) := by
  subst n
  have he : τ = (τ.re : ℂ) := by apply Complex.ext <;> simp [hi]
  have h (a : ℝ) : cutoffComplexOperator a 0 τ = cutoffEvolution a τ.re := by
    rw [he,cutoffComplexOperator_zero_ofReal,Complex.ofReal_re]
  simpa only [h] using cutoffEvolution_tendsto_atBot τ.re u

private theorem cauchy_strong_good (n : ℕ) (τ : ℂ) (hn : n = 0) (hi : τ.im = 0) (u : SoninL2) :
    Tendsto (fun a => cutoffComplexCauchyOperator a n τ u) atBot
      (𝓝 (cauchyEvolution τ.re u)) := by
  subst n
  have he : τ = (τ.re : ℂ) := by apply Complex.ext <;> simp [hi]
  have h (a : ℝ) : cutoffComplexCauchyOperator a 0 τ = cutoffCauchyEvolution a τ.re := by
    rw [he,cutoffComplexCauchyOperator_ofReal,cutoffCauchyDerivative_zero,Complex.ofReal_re]
  simpa only [h] using cutoffCauchyEvolution_tendsto_atBot τ.re u

private theorem all_coefficients_converge_iff
    (T : ℝ → SoninL2 →L[ℂ] SoninL2) (R : SoninL2 →L[ℂ] SoninL2) (n : ℕ) (τ : ℂ)
    (hb : (∀ u v : SoninL2, BddAbove (Set.range fun k : ℕ => ‖inner ℂ (T (-(k:ℝ)) u) v‖)) ↔
      n = 0 ∧ τ.im = 0)
    (hg : n = 0 → τ.im = 0 → ∀ u, Tendsto (fun a => T a u) atBot (𝓝 (R u))) :
    (∀ u v : SoninL2, ∃ c : ℂ, Tendsto (fun a => inner ℂ (T a u) v) atBot (𝓝 c)) ↔
      n = 0 ∧ τ.im = 0 := by
  constructor
  · intro h
    apply hb.1
    intro u v
    obtain ⟨c,hc⟩ := h u v
    exact (Metric.isBounded_range_of_tendsto _ (hc.comp negative_nat_tendsto).norm).bddAbove
  · rintro ⟨hn,hi⟩ u v
    exact ⟨inner ℂ (R u) v,(hg hn hi u).inner tendsto_const_nhds⟩

private theorem weak_limit_iff
    (T : ℝ → SoninL2 →L[ℂ] SoninL2) (R A : SoninL2 →L[ℂ] SoninL2) (n : ℕ) (τ : ℂ)
    (hb : (∀ u v : SoninL2, BddAbove (Set.range fun k : ℕ => ‖inner ℂ (T (-(k:ℝ)) u) v‖)) ↔
      n = 0 ∧ τ.im = 0)
    (hg : n = 0 → τ.im = 0 → ∀ u, Tendsto (fun a => T a u) atBot (𝓝 (R u))) :
    (∀ u v : SoninL2, Tendsto (fun a => inner ℂ (T a u) v) atBot (𝓝 (inner ℂ (A u) v))) ↔
      n = 0 ∧ τ.im = 0 ∧ A = R := by
  constructor
  · intro h
    obtain ⟨hn,hi⟩ := (all_coefficients_converge_iff T R n τ hb hg).1
      (fun u v => ⟨inner ℂ (A u) v,h u v⟩)
    refine ⟨hn,hi,?_⟩
    apply ContinuousLinearMap.ext
    intro u
    apply ext_inner_right ℂ
    intro v
    exact tendsto_nhds_unique (h u v) ((hg hn hi u).inner tendsto_const_nhds)
  · rintro ⟨hn,hi,rfl⟩ u v
    exact (hg hn hi u).inner tendsto_const_nhds

private theorem strong_limit_iff
    (T : ℝ → SoninL2 →L[ℂ] SoninL2) (R A : SoninL2 →L[ℂ] SoninL2) (n : ℕ) (τ : ℂ)
    (hb : (∀ u v : SoninL2, BddAbove (Set.range fun k : ℕ => ‖inner ℂ (T (-(k:ℝ)) u) v‖)) ↔
      n = 0 ∧ τ.im = 0)
    (hg : n = 0 → τ.im = 0 → ∀ u, Tendsto (fun a => T a u) atBot (𝓝 (R u))) :
    (∀ u : SoninL2, Tendsto (fun a => T a u) atBot (𝓝 (A u))) ↔
      n = 0 ∧ τ.im = 0 ∧ A = R := by
  constructor
  · intro h
    exact (weak_limit_iff T R A n τ hb hg).1 (fun u v => (h u).inner tendsto_const_nhds)
  · rintro ⟨hn,hi,rfl⟩
    exact hg hn hi

/-- All fixed matrix coefficients converge exactly at zeroth order and real time. -/
theorem cutoffComplexOperator_all_matrixCoefficients_converge_iff (n : ℕ) (τ : ℂ) :
    (∀ u v : SoninL2, ∃ c : ℂ,
      Tendsto (fun a => inner ℂ (cutoffComplexOperator a n τ u) v) atBot (𝓝 c)) ↔
      n = 0 ∧ τ.im = 0 :=
  all_coefficients_converge_iff _ (evolution τ.re).toContinuousLinearEquiv.toContinuousLinearMap n τ
    (cutoffComplexOperator_weak_sequence_bound_iff n τ) (complex_strong_good n τ)

/-- Cauchy compression has exactly the same scalar weak-convergence gate. -/
theorem cutoffComplexCauchyOperator_all_matrixCoefficients_converge_iff (n : ℕ) (τ : ℂ) :
    (∀ u v : SoninL2, ∃ c : ℂ,
      Tendsto (fun a => inner ℂ (cutoffComplexCauchyOperator a n τ u) v) atBot (𝓝 c)) ↔
      n = 0 ∧ τ.im = 0 :=
  all_coefficients_converge_iff _ (cauchyEvolution τ.re) n τ
    (cutoffComplexCauchyOperator_weak_sequence_bound_iff n τ) (cauchy_strong_good n τ)

/-- Exact weak operator-limit classification, including the unique actual raw limit. -/
theorem cutoffComplexOperator_weak_limit_iff (n : ℕ) (τ : ℂ) (A : SoninL2 →L[ℂ] SoninL2) :
    (∀ u v : SoninL2, Tendsto (fun a => inner ℂ (cutoffComplexOperator a n τ u) v) atBot
      (𝓝 (inner ℂ (A u) v))) ↔
      n = 0 ∧ τ.im = 0 ∧ A = (evolution τ.re).toContinuousLinearEquiv.toContinuousLinearMap :=
  weak_limit_iff _ _ A n τ (cutoffComplexOperator_weak_sequence_bound_iff n τ) (complex_strong_good n τ)

/-- Exact weak Cauchy-limit classification, with its actual raw Cauchy operator. -/
theorem cutoffComplexCauchyOperator_weak_limit_iff (n : ℕ) (τ : ℂ) (A : SoninL2 →L[ℂ] SoninL2) :
    (∀ u v : SoninL2, Tendsto (fun a => inner ℂ (cutoffComplexCauchyOperator a n τ u) v) atBot
      (𝓝 (inner ℂ (A u) v))) ↔
      n = 0 ∧ τ.im = 0 ∧ A = cauchyEvolution τ.re :=
  weak_limit_iff _ _ A n τ (cutoffComplexCauchyOperator_weak_sequence_bound_iff n τ) (cauchy_strong_good n τ)

/-- Strong cutoff limits have exactly the same gate and the same uniquely determined raw operator. -/
theorem cutoffComplexOperator_strong_limit_iff (n : ℕ) (τ : ℂ) (A : SoninL2 →L[ℂ] SoninL2) :
    (∀ u : SoninL2, Tendsto (fun a => cutoffComplexOperator a n τ u) atBot (𝓝 (A u))) ↔
      n = 0 ∧ τ.im = 0 ∧ A = (evolution τ.re).toContinuousLinearEquiv.toContinuousLinearMap :=
  strong_limit_iff _ _ A n τ (cutoffComplexOperator_weak_sequence_bound_iff n τ) (complex_strong_good n τ)

/-- Exact strong-limit classification survives actual Cauchy compression. -/
theorem cutoffComplexCauchyOperator_strong_limit_iff (n : ℕ) (τ : ℂ) (A : SoninL2 →L[ℂ] SoninL2) :
    (∀ u : SoninL2, Tendsto (fun a => cutoffComplexCauchyOperator a n τ u) atBot (𝓝 (A u))) ↔
      n = 0 ∧ τ.im = 0 ∧ A = cauchyEvolution τ.re :=
  strong_limit_iff _ _ A n τ (cutoffComplexCauchyOperator_weak_sequence_bound_iff n τ) (cauchy_strong_good n τ)

end
end RHTower.FokasLenells
