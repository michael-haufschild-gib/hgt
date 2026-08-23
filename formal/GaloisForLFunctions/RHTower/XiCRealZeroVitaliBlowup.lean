import GaloisForLFunctions.HTGeometry.VitaliConvergence
import GaloisForLFunctions.RHTower.LocallyUniformZeroTransfer

/-!
# Vitali blow-up obstruction for real-zero approximations of centered Xi

Compact-open convergence is stronger than a spectral-determinant route needs to prove directly.
Vitali's theorem reduces it to local boundedness plus pointwise convergence on any set accumulating
inside the plane.  Combined with real-zero transfer, those two weaker inputs already imply RH.

The contrapositive is quantitative in topology: if RH is false, then every entire real-zero family
which converges pointwise to `XiC` on a uniqueness set has a point where its norms are unbounded on
every neighborhood.  Thus a failed determinant route cannot remain a normal family and merely
select the wrong analytic continuation; it must develop local amplitude blow-up.
-/

open Complex Metric Set Filter Topology

namespace RHTower

/-- Local boundedness of a sequence of entire-function candidates, written in the form required
by Vitali on the whole complex plane. -/
def LocallyBoundedEntireSequence (F : ℕ → ℂ → ℂ) : Prop :=
  ∀ z : ℂ, ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ,
    ∀ n : ℕ, ∀ w ∈ ball z R, ‖F n w‖ ≤ C

/-- **[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED] Vitali--real-zero RH criterion.**
An entire locally bounded family with real zero loci need only converge to `XiC` pointwise on one
uniqueness set.  Vitali supplies the missing compact-open convergence, after which zero transfer
proves RH. -/
theorem riemannHypothesis_of_XiC_vitali_realZero_approximants
    {F : ℕ → ℂ → ℂ} {Y : Set ℂ} {z₀ : ℂ}
    (hF : ∀ n, Differentiable ℂ (F n))
    (hbounded : LocallyBoundedEntireSequence F)
    (hacc : ∃ᶠ z in 𝓝[≠] z₀, z ∈ Y)
    (hpointwise : ∀ z ∈ Y, Tendsto (fun n => F n z) atTop (𝓝 (XiC z)))
    (hreal : ∀ n z, F n z = 0 → z.im = 0) :
    RiemannHypothesis := by
  have hlocalOn : TendstoLocallyUniformlyOn F XiC atTop Set.univ :=
    GaloisForLFunctions.HTGeometry.tendstoLocallyUniformlyOn_of_pointwise_on_uniquenessSet
      isOpen_univ isPreconnected_univ
      (fun n => (hF n).differentiableOn)
      (fun z _ => by
        obtain ⟨R, hR, C, hC⟩ := hbounded z
        exact ⟨R, hR, Set.subset_univ _, C, hC⟩)
      XiC_differentiable.differentiableOn
      (Set.subset_univ Y) (Set.mem_univ z₀) hacc hpointwise
  exact riemannHypothesis_of_XiC_locally_uniform_real_zero_approximants
    (tendstoLocallyUniformlyOn_univ.mp hlocalOn)
    (Filter.Eventually.of_forall hF)
    (Filter.Eventually.of_forall hreal)

/-- **[LEAN-PROVED] [OBSTRUCTION] [NOVELTY UNVERIFIED] Normal-family dichotomy.**
For every entire real-zero family which matches `XiC` pointwise on a uniqueness set, either RH is
true or the family is not locally bounded.  This is a closed alternative: it assumes no candidate
compact-open limit. -/
theorem riemannHypothesis_or_not_locallyBoundedEntireSequence_of_XiC_pointwise_realZero
    {F : ℕ → ℂ → ℂ} {Y : Set ℂ} {z₀ : ℂ}
    (hF : ∀ n, Differentiable ℂ (F n))
    (hacc : ∃ᶠ z in 𝓝[≠] z₀, z ∈ Y)
    (hpointwise : ∀ z ∈ Y, Tendsto (fun n => F n z) atTop (𝓝 (XiC z)))
    (hreal : ∀ n z, F n z = 0 → z.im = 0) :
    RiemannHypothesis ∨ ¬ LocallyBoundedEntireSequence F := by
  by_cases hbounded : LocallyBoundedEntireSequence F
  · exact Or.inl
      (riemannHypothesis_of_XiC_vitali_realZero_approximants
        hF hbounded hacc hpointwise hreal)
  · exact Or.inr hbounded

/-- **[LEAN-PROVED] [OBSTRUCTION] [NOVELTY UNVERIFIED] Local amplitude blow-up.**
If RH is false, an entire real-zero family converging pointwise to `XiC` on a uniqueness set has
one point `z` such that on every ball around `z`, its norms exceed every prescribed level. -/
theorem exists_local_norm_blowup_of_not_riemannHypothesis_of_XiC_pointwise_realZero
    {F : ℕ → ℂ → ℂ} {Y : Set ℂ} {z₀ : ℂ}
    (hnot : ¬ RiemannHypothesis)
    (hF : ∀ n, Differentiable ℂ (F n))
    (hacc : ∃ᶠ z in 𝓝[≠] z₀, z ∈ Y)
    (hpointwise : ∀ z ∈ Y, Tendsto (fun n => F n z) atTop (𝓝 (XiC z)))
    (hreal : ∀ n z, F n z = 0 → z.im = 0) :
    ∃ z : ℂ, ∀ R : ℝ, 0 < R → ∀ C : ℝ,
      ∃ n : ℕ, ∃ w ∈ ball z R, C < ‖F n w‖ := by
  have hnotBounded : ¬ LocallyBoundedEntireSequence F := by
    intro hbounded
    exact hnot (riemannHypothesis_of_XiC_vitali_realZero_approximants
      hF hbounded hacc hpointwise hreal)
  unfold LocallyBoundedEntireSequence at hnotBounded
  push Not at hnotBounded
  obtain ⟨z, hz⟩ := hnotBounded
  refine ⟨z, fun R hR C => ?_⟩
  obtain ⟨n, w, hw, hnorm⟩ := hz R hR C
  exact ⟨n, w, hw, hnorm⟩

end RHTower
