import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.IsolatedDilations
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.WindowEvent

/-! # From isolation on typical paths to vanishing prefix probabilities -/
open Set MeasureTheory ProbabilityTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ShortWindows
noncomputable section

abbrev prefixPoint (k : ℕ) (ω : PathPauliDisorder) : PrefixIndex (k+1) → ℝ :=
  fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)

/-- Eventual avoidance on typical paths forces the prefix probabilities to vanish. -/
theorem probability_vanishes {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : ℕ → Set Ω) (hm : ∀ k, MeasurableSet (A k))
    (h : ∀ᵐ x ∂μ, ∀ᶠ k : ℕ in atTop, x ∉ A k) : Tendsto (fun k => μ.real (A k)) atTop (𝓝 0) := by
  let f (k : ℕ) := (A k).indicator (1 : Ω → ℝ)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun k => f k x) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [h] with x hx
    exact tendsto_const_nhds.congr' (hx.mono fun k hk => (indicator_of_notMem hk _).symm)
  have hbound (k : ℕ) : ∀ᵐ x ∂μ, ‖f k x‖ ≤ 1 := by
    filter_upwards with x
    by_cases hx : x∈A k <;> simp [f,hx]
  have hc := tendsto_integral_of_dominated_convergence (μ:=μ) (F:=f) (fun _ => (1:ℝ))
    (fun k => (measurable_const.indicator (hm k)).aestronglyMeasurable) (integrable_const _) hbound hlim
  have he (k : ℕ) : (∫ x, f k x ∂μ)=μ.real (A k) := integral_indicator_one (hm k)
  simpa only [he,integral_zero] using hc

/-- Arbitrarily many nearly unit dilations suffice. Isolation only needs
to hold eventually along almost every infinite disorder realization. -/
theorem prefix_probability_of_isolation (E : (k : ℕ) → Set (PrefixIndex (k+1) → ℝ))
    (hE : ∀ k, MeasurableSet (E k)) (a : (m k : ℕ) → Fin m → ℝ)
    (hprice : ∀ m, ∀ᶠ k : ℕ in atTop, ∀ i, 1 ≤ a m k i ∧
      (Fintype.card (PrefixIndex (k+1)):ℝ)*(a m k i-1) ≤ 1)
    (hiso : ∀ m, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      prefixPoint k ω∈E k → prefixPoint k ω∈isolated (a m k) (E k)) :
    Tendsto (fun k => pathPauliDisorderLaw.real (prefixPoint k ⁻¹' E k)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨m,hm⟩ := exists_nat_gt (Real.exp 1/(ε/2))
  let μ := pathPauliDisorderLaw
  letI : IsProbabilityMeasure μ := by dsimp [μ,pathPauliDisorderLaw]; infer_instance
  let B (k : ℕ) := isolated (a m k) (E k)
  let A (k : ℕ) := prefixPoint k ⁻¹' (E k \ B k)
  have hB (k : ℕ) : MeasurableSet (B k) := measurable_isolated _ (hE k)
  have hA (k : ℕ) : MeasurableSet (A k) := ((hE k).diff (hB k)).preimage
    (gaussian_pauli_prefix_coordinates_law (k+1)).measurable
  have hmiss : ∀ᵐ ω ∂μ, ∀ᶠ k : ℕ in atTop, ω ∉ A k := by
    filter_upwards [hiso m] with ω hω
    exact hω.mono fun k hk h => h.2 (hk h.1)
  have hlim := probability_vanishes μ A hA hmiss
  have hhalf := half_pos hε
  have hcost := (div_lt_iff₀ hhalf).mp hm
  have hmpos := (div_pos (Real.exp_pos 1) hhalf).trans hm
  filter_upwards [hprice m,hlim.eventually_lt_const hhalf] with k hk hsmall
  have hmp := gaussian_pauli_prefix_coordinates_law (k+1)
  have hh := gaussian_isolated_mass (hE k) (fun i => (hk i).1) (fun i => (hk i).2)
  have he := hmp.measureReal_preimage (hB k).nullMeasurableSet
  change μ.real (prefixPoint k ⁻¹' B k)=_ at he
  change (m:ℝ)*(centredProductGaussian (PrefixIndex (k+1)) 1).real (B k) ≤ Real.exp 1 at hh
  rw [←he] at hh
  have hb : μ.real (prefixPoint k ⁻¹' B k) < ε/2 := by
    apply (mul_lt_mul_iff_right₀ hmpos).mp
    exact hh.trans_lt hcost
  have hsub : prefixPoint k ⁻¹' E k ⊆ (prefixPoint k ⁻¹' B k) ∪ A k := fun x hx =>
    (em (prefixPoint k x∈B k)).elim Or.inl (fun h => Or.inr ⟨hx,h⟩)
  have hu := (measureReal_mono (μ:=μ) hsub).trans (measureReal_union_le _ _)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg measureReal_nonneg]
  change μ.real (prefixPoint k ⁻¹' E k) < ε
  linarith only [hu,hsmall,hb]

#print axioms prefix_probability_of_isolation
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ShortWindows
