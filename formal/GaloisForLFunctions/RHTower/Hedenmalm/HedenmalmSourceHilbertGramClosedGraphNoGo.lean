import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaNullTemperedDenseRadicalUniversalityLaw
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Hedenmalm source Hilbert-Gram closed-graph no-go

A Hilbert Gram pullback of the Hedenmalm source form has algebraic radical exactly the kernel of
its realization map.  Theta nullity and momentum symmetry make that radical dense in ordinary
`L²`, so it cannot be only the one-dimensional theta-source line.  More strongly, every partial
ordinary-`L²` operator realizing a nonzero such Gram map on the full Schwartz source core is
nonclosable.

The result does not address a form defined only on Hedenmalm's finite zero-eigenfunction span.  It
closes the full-source, positive Hilbert-Gram, ordinary-`L²` graph category without assuming RH or
simplicity.
-/

open Complex Function Filter Set
open scoped Topology SchwartzMap

noncomputable section

namespace LinearPMap

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A closable partial linear operator has no nonzero limit above a sequence of domain points
converging to zero.  This is the sequential zero-fibre consequence of graph closability. -/
theorem IsClosable.eq_zero_of_tendsto_graph
    {T : E →ₗ.[ℂ] F} (hT : T.IsClosable)
    (x : ℕ → T.domain) {y : F}
    (hx : Tendsto (fun n => (x n : E)) atTop (𝓝 0))
    (hy : Tendsto (fun n => T (x n)) atTop (𝓝 y)) :
    y = 0 := by
  obtain ⟨T', hclosure⟩ := hT
  have hmem : (0, y) ∈ T.graph.topologicalClosure := by
    apply mem_closure_iff_seq_limit.mpr
    refine ⟨fun n => ((x n : E), T (x n)), ?_, ?_⟩
    · intro n
      exact T.mem_graph (x n)
    · exact hx.prodMk_nhds hy
  have hgraph : (0, y) ∈ T'.graph := by
    rw [← hclosure]
    exact hmem
  exact T'.graph_fst_eq_zero_snd hgraph rfl

end LinearPMap

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A linear map into a complex inner-product space realizes a continuous Schwartz form as its
Hilbert Gram pullback.  The order matches the convention that the form is linear on the left. -/
def HilbertGramRealizes
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (J : SchwartzMap ℝ ℂ →ₗ[ℂ] H) : Prop :=
  ∀ u v, Q u v = inner ℂ (J v) (J u)

/-- The left radical of a Hilbert Gram pullback is exactly the kernel of its realization map. -/
theorem hilbertGram_leftRadical_eq_ker
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (J : SchwartzMap ℝ ℂ →ₗ[ℂ] H)
    (hgram : HilbertGramRealizes Q J) :
    Q.leftRadical = LinearMap.ker J := by
  ext u
  rw [Q.mem_leftRadical_iff, LinearMap.mem_ker]
  constructor
  · intro hu
    have huu := hu u
    rw [hgram] at huu
    exact inner_self_eq_zero.mp huu
  · intro hu v
    rw [hgram, hu]
    simp

/-- Every Hilbert Gram pullback is a nonnegative Schwartz form. -/
theorem hilbertGram_isNonnegative
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (J : SchwartzMap ℝ ℂ →ₗ[ℂ] H)
    (hgram : HilbertGramRealizes Q J) :
    Q.IsNonnegative := by
  intro u
  rw [hgram]
  constructor
  · exact inner_self_nonneg (𝕜 := ℂ) (x := J u)
  · rw [← inner_self_ofReal_re (𝕜 := ℂ) (J u)]
    simp

/-- A nonzero realization map supplies a nonzero diagonal of its Gram form. -/
theorem exists_hilbertGram_diagonal_ne_zero
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (J : SchwartzMap ℝ ℂ →ₗ[ℂ] H)
    (hgram : HilbertGramRealizes Q J) (hJ : J ≠ 0) :
    ∃ u : SchwartzMap ℝ ℂ, Q u u ≠ 0 := by
  have hwitness : ∃ u : SchwartzMap ℝ ℂ, J u ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hJ
    ext u
    exact hnone u
  obtain ⟨u, hu⟩ := hwitness
  refine ⟨u, ?_⟩
  rw [hgram]
  exact inner_self_ne_zero.mpr hu

/-- If the realization map kills the completed theta source, that source belongs to the complete
left radical of the Gram form. -/
theorem hilbertGram_theta_leftRadical_of_sourceNull
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (J : SchwartzMap ℝ ℂ →ₗ[ℂ] H)
    (hgram : HilbertGramRealizes Q J)
    (hsource : J xiThetaSchwartzSource = 0) :
    ∀ v : SchwartzMap ℝ ℂ, Q xiThetaSchwartzSource v = 0 := by
  intro v
  rw [hgram, hsource]
  simp

/-- **Faithful source-quotient no-go.** A nonzero Hilbert Gram realization of a momentum-symmetric
Hedenmalm source form cannot have exactly the one-dimensional theta-source line as its kernel. -/
theorem hilbertGram_kernel_ne_thetaSourceLine
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (J : SchwartzMap ℝ ℂ →ₗ[ℂ] H)
    (hgram : HilbertGramRealizes Q J)
    (hMomentum : Q.MomentumSymmetric)
    (hsource : J xiThetaSchwartzSource = 0)
    (hJ : J ≠ 0) :
    LinearMap.ker J ≠ xiThetaSchwartzSourceLine := by
  intro hker
  apply not_exists_nonzero_universalPositiveForm_thetaNull_exactSourceLineRadical
  refine ⟨Q, hMomentum, hilbertGram_isNonnegative Q J hgram, ?_, ?_, ?_⟩
  · rw [hgram, hsource]
    simp
  · exact (hilbertGram_leftRadical_eq_ker Q J hgram).trans hker
  · obtain ⟨u, hu⟩ := exists_hilbertGram_diagonal_ne_zero Q J hgram hJ
    exact ⟨u, u, hu⟩

/-- **Closed-graph no-go.** No partial ordinary-`L²` operator realizing a nonzero theta-null
Hilbert Gram map on the full Schwartz source core is closable. -/
theorem hilbertGram_l2PartialOperator_not_closable
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (J : SchwartzMap ℝ ℂ →ₗ[ℂ] H)
    (hgram : HilbertGramRealizes Q J)
    (hMomentum : Q.MomentumSymmetric)
    (hsource : J xiThetaSchwartzSource = 0)
    (hJ : J ≠ 0)
    (T : XiThetaL2 →ₗ.[ℂ] H)
    (hdom : ∀ u : SchwartzMap ℝ ℂ, xiThetaSchwartzToL2 u ∈ T.domain)
    (hrealize : ∀ u : SchwartzMap ℝ ℂ,
      T ⟨xiThetaSchwartzToL2 u, hdom u⟩ = J u) :
    ¬ T.IsClosable := by
  intro hT
  obtain ⟨u, hu⟩ := exists_hilbertGram_diagonal_ne_zero Q J hgram hJ
  obtain ⟨z, hz0, hzdiff, hzenergy⟩ :=
    exists_xiThetaL2Null_constantEnergy_sequence
      Q (hilbertGram_isNonnegative Q J hgram) hMomentum
      (hilbertGram_theta_leftRadical_of_sourceNull Q J hgram hsource) u
  let x : ℕ → T.domain := fun n => ⟨xiThetaSchwartzToL2 (z n), hdom (z n)⟩
  have hx : Tendsto (fun n => (x n : XiThetaL2)) atTop (𝓝 0) := by
    simpa only [x] using hz0
  have hJconst (n : ℕ) : J (z n) = J (z 0) := by
    have hzero := hzdiff n 0
    rw [hgram] at hzero
    have hjzero : J (z n - z 0) = 0 := inner_self_eq_zero.mp hzero
    rw [map_sub] at hjzero
    exact sub_eq_zero.mp hjzero
  have hTx (n : ℕ) : T (x n) = J (z n) := by
    simpa only [x] using hrealize (z n)
  have hy : Tendsto (fun n => T (x n)) atTop (𝓝 (J (z 0))) := by
    have heq : (fun n => T (x n)) = fun _n : ℕ => J (z 0) := by
      funext n
      rw [hTx, hJconst]
    rw [heq]
    exact tendsto_const_nhds
  have hJz0 : J (z 0) ≠ 0 := by
    intro hjzero
    have henergy := hzenergy 0
    rw [hgram, hjzero] at henergy
    simp at henergy
    exact hu henergy.symm
  exact hJz0 (hT.eq_zero_of_tendsto_graph x hx hy)

/-- Complete nonzero Hilbert-Gram survivor law: the representing divisor measure is nonzero,
the ordinary-`L²` radical image is dense proper nonclosed, a curried distribution remains
nonzero, and the form is not sequentially closable through ordinary `L²`. -/
theorem hilbertGram_nonzero_thetaNull_temperedDenseRadicalLaw
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (J : SchwartzMap ℝ ℂ →ₗ[ℂ] H)
    (hgram : HilbertGramRealizes Q J)
    (hMomentum : Q.MomentumSymmetric)
    (hsource : J xiThetaSchwartzSource = 0)
    (hJ : J ≠ 0) :
    Q.compactSpectralRieszMeasure hMomentum
        (hilbertGram_isNonnegative Q J hgram) ≠ 0 ∧
      Dense (xiThetaL2RadicalImage Q : Set XiThetaL2) ∧
      ¬ IsClosed (xiThetaL2RadicalImage Q : Set XiThetaL2) ∧
      (∃ v : SchwartzMap ℝ ℂ, Q.leftTemperedDistribution v ≠ 0) ∧
      ¬ Q.IsSequentiallyClosableThrough xiThetaSchwartzToL2 := by
  apply universalPositiveForm_nonzero_thetaNull_temperedDenseRadicalLaw
    Q hMomentum (hilbertGram_isNonnegative Q J hgram)
  · rw [hgram, hsource]
    simp
  · obtain ⟨u, hu⟩ := exists_hilbertGram_diagonal_ne_zero Q J hgram hJ
    exact ⟨u, u, hu⟩

end RHTower
