import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Stationary Hilbert curves extend from dense parameters

A Hilbert curve with inner product `K(t-s)` is uniformly continuous whenever
`K` is continuous at zero. On a dense parameter set it therefore extends to
the full real line. Continuity and product density preserve the entire
inner-product kernel, including when the original parameter map is not injective.
-/

open Complex Set Filter Topology
open scoped InnerProductSpace

noncomputable section
namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Stationary inner products make a Hilbert curve uniformly continuous as soon as its
scalar correlation is continuous at zero. -/
theorem uniformContinuous_of_stationary_inner {S : Set ℝ} (f : S → E) (K : ℝ → ℂ)
    (hK : ContinuousAt K 0)
    (hinner : ∀ x y : S, ⟪f x, f y⟫_ℂ = K ((y : ℝ) - x)) : UniformContinuous f := by
  have hn (x : S) : ‖f x‖ ^ 2 = (K 0).re := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), RCLike.re_to_complex, hinner, sub_self]
  have hd (x y : S) : ‖f x - f y‖ ^ 2 =
      2 * (K 0).re - 2 * (K ((y : ℝ) - x)).re := by
    rw [norm_sub_sq (𝕜 := ℂ), hn, hn, RCLike.re_to_complex, hinner]
    ring
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  have hk := Complex.continuous_re.continuousAt.comp hK
  obtain ⟨δ, hδ, hcontrol⟩ := Metric.continuousAt_iff.mp hk (ε ^ 2 / 2) (by positivity)
  refine ⟨δ, hδ, fun {x y} hxy => ?_⟩
  have hdxy : dist ((y : ℝ) - x) 0 < δ := by
    change dist (x : ℝ) (y : ℝ) < δ at hxy
    simpa only [dist_zero_right, Real.norm_eq_abs, Real.dist_eq, abs_sub_comm] using hxy
  have hbound : |(K ((y : ℝ) - x)).re - (K 0).re| < ε ^ 2 / 2 := by
    simpa only [Real.dist_eq, Function.comp_apply] using hcontrol hdxy
  have hs : ‖f x - f y‖ ^ 2 < ε ^ 2 := by
    rw [hd]
    linarith only [(abs_lt.mp hbound).1]
  rw [dist_eq_norm]
  nlinarith only [hs, hε, norm_nonneg (f x - f y)]

/-- A stationary Hilbert curve on a dense subset extends with the same correlation. -/
theorem exists_stationary_hilbert_extension [CompleteSpace E] {S : Set ℝ}
    (hS : Dense S) (f : S → E) (K : ℝ → ℂ) (hK : Continuous K)
    (hinner : ∀ x y : S, ⟪f x, f y⟫_ℂ = K ((y : ℝ) - x)) :
    ∃ F : ℝ → E, UniformContinuous F ∧ (∀ x : S, F x = f x) ∧
      ∀ x y : ℝ, ⟪F x, F y⟫_ℂ = K (y - x) := by
  have hf := uniformContinuous_of_stationary_inner f K hK.continuousAt hinner
  let F := hS.extend f
  have hF : UniformContinuous F := hS.uniformContinuous_extend hf
  have hres (x : S) : F x = f x := hS.extend_of_ind hf x
  refine ⟨F, hF, hres, ?_⟩
  have hclosed : IsClosed {p : ℝ × ℝ | ⟪F p.1, F p.2⟫_ℂ = K (p.2 - p.1)} :=
    isClosed_eq ((hF.continuous.comp continuous_fst).inner
      (hF.continuous.comp continuous_snd)) (hK.comp (continuous_snd.sub continuous_fst))
  have hsub : S ×ˢ S ⊆ {p : ℝ × ℝ | ⟪F p.1, F p.2⟫_ℂ = K (p.2 - p.1)} := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    change ⟪F x, F y⟫_ℂ = K (y - x)
    rw [hres ⟨x, hx⟩, hres ⟨y, hy⟩]
    exact hinner ⟨x, hx⟩ ⟨y, hy⟩
  intro x y
  exact hclosed.closure_subset_iff.mpr hsub ((hS.prod hS) (x, y))

/-- The dense parameter map need not be injective: equal parameters have zero Hilbert distance. -/
theorem exists_stationary_hilbert_extension_indexed [CompleteSpace E] {ι : Type*}
    (t : ι → ℝ) (ht : DenseRange t) (v : ι → E) (K : ℝ → ℂ) (hK : Continuous K)
    (hinner : ∀ i j, ⟪v i, v j⟫_ℂ = K (t j - t i)) :
    ∃ F : ℝ → E, UniformContinuous F ∧ (∀ i, F (t i) = v i) ∧
      ∀ x y : ℝ, ⟪F x, F y⟫_ℂ = K (y - x) := by
  let f : Set.range t → E := fun x => v x.property.choose
  have hc (x : Set.range t) : t x.property.choose = (x : ℝ) := x.property.choose_spec
  have hfinner (x y : Set.range t) : ⟪f x, f y⟫_ℂ = K ((y : ℝ) - x) := by
    change ⟪v x.property.choose, v y.property.choose⟫_ℂ = _
    rw [hinner, hc x, hc y]
  obtain ⟨F, hF, hres, hkernel⟩ := exists_stationary_hilbert_extension ht f K hK hfinner
  refine ⟨F, hF, ?_, hkernel⟩
  intro i
  rw [hres ⟨t i, Set.mem_range_self i⟩]
  let j := (⟨t i, Set.mem_range_self i⟩ : Set.range t).property.choose
  have hji : t j = t i := hc ⟨t i, Set.mem_range_self i⟩
  change v j = v i
  have hn (k : ι) : ‖v k‖ ^ 2 = (K 0).re := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), RCLike.re_to_complex, hinner, sub_self]
  have hz : ‖v j - v i‖ ^ 2 = 0 := by
    rw [norm_sub_sq (𝕜 := ℂ), hn, hn, RCLike.re_to_complex, hinner, hji, sub_self]
    ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

#print axioms exists_stationary_hilbert_extension_indexed
#print axioms exists_stationary_hilbert_extension
end GaloisForLFunctions.HTGeometry
