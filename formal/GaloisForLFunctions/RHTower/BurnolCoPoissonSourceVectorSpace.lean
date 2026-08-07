import GaloisForLFunctions.RHTower.BurnolCoPoissonGeneralSeedMellin
import GaloisForLFunctions.RHTower.BurnolCoPoissonSubWindowIndependence

/-!
# The closed span of the co-Poisson source vectors

Every co-Poisson source vector has completed Mellin evaluation `Gamma_R(w) zeta(w) M(g)(w)`, so at
a zero of zeta the Riesz evaluator annihilates the whole closed span of the source vectors, and off
the zero set the symmetric window `[b, 1/b]` already witnesses non-orthogonality.  The evaluator is
therefore orthogonal to that span exactly at the zeros of zeta.
-/

open Complex Real MeasureTheory Set Filter Topology Finset
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- The co-Poisson source vectors at aperture `b`, without their cosine transforms. -/
def burnolCoPoissonVectorGenerators (b : ℝ) : Set (soninExtendedSpace b) :=
  {f | ∃ src : BurnolCoPoissonSource b, f = src.vector}

/-- The closed span of the co-Poisson source vectors at aperture `b`. -/
def burnolCoPoissonVectorSpace (b : ℝ) : Submodule ℂ (soninExtendedSpace b) :=
  (Submodule.span ℂ (burnolCoPoissonVectorGenerators b)).topologicalClosure

/-- **At a zeta zero the Riesz evaluator annihilates the whole closed span of the co-Poisson
source vectors.**  This is the transfer of the two-sided law to the full source side: no
co-Poisson vector, and no limit of their combinations, can witness nonvanishing at a zero. -/
theorem inner_eq_zero_of_mem_burnolCoPoissonVectorSpace {b : ℝ} (hb : 0 < b)
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hz : riemannZeta w = 0)
    (u : soninExtendedSpace b) (hu : u ∈ burnolCoPoissonVectorSpace b) :
    ⟪burnolExtendedSoninEvaluationVector w b hlo hhi hb, u⟫_ℂ = 0 := by
  letI : Fact (0 < b) := ⟨hb⟩
  set k := burnolExtendedSoninEvaluationVector w b hlo hhi hb with hk
  set K : Submodule ℂ (soninExtendedSpace b) :=
    LinearMap.ker ((innerSL ℂ k).toLinearMap) with hK
  have hclosed : IsClosed (K : Set (soninExtendedSpace b)) :=
    (innerSL ℂ k).isClosed_ker
  have hgen : burnolCoPoissonVectorGenerators b ⊆ (K : Set (soninExtendedSpace b)) := by
    rintro f ⟨src, rfl⟩
    rw [SetLike.mem_coe, hK, LinearMap.mem_ker]
    show ⟪k, src.vector⟫_ℂ = 0
    exact inner_burnolExtendedSoninEvaluationVector_source_eq_zero hb src hlo hhi hz
  have hle : burnolCoPoissonVectorSpace b ≤ K :=
    (Submodule.span ℂ (burnolCoPoissonVectorGenerators b)).topologicalClosure_minimal
      (Submodule.span_le.mpr hgen) hclosed
  have hmem := hle hu
  rw [hK, LinearMap.mem_ker] at hmem
  exact hmem

theorem burnolSubWindowGenerators_subset {A : ℝ} (hA : 0 < A) :
    burnolSubWindowGenerators A ⊆ burnolCoPoissonVectorGenerators A := by
  rintro f ⟨c, d, hc, hcd, hAle, rfl⟩
  exact ⟨coPoissonSubWindowSourceAt hA hc hcd hAle, rfl⟩

theorem burnolSubWindowSpace_le_burnolCoPoissonVectorSpace {A : ℝ} (hA : 0 < A) :
    burnolSubWindowSpace A ≤ burnolCoPoissonVectorSpace A :=
  Submodule.topologicalClosure_mono
    (Submodule.span_mono (burnolSubWindowGenerators_subset hA))

/-- **The closed span of the co-Poisson vectors is infinite dimensional.** -/
theorem not_finiteDimensional_burnolCoPoissonVectorSpace {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1) :
    ¬ FiniteDimensional ℂ (burnolCoPoissonVectorSpace A) := by
  intro hfin
  obtain ⟨v, hvmem, hvind⟩ :=
    exists_linearIndependent_mem_burnolSubWindowSpace hA0 hA1
      (Module.finrank ℂ (burnolCoPoissonVectorSpace A) + 1)
  have hmem : ∀ i, v i ∈ burnolCoPoissonVectorSpace A := fun i =>
    burnolSubWindowSpace_le_burnolCoPoissonVectorSpace hA0 (hvmem i)
  have hv'ind : LinearIndependent ℂ (fun i => (⟨v i, hmem i⟩ : burnolCoPoissonVectorSpace A)) :=
    LinearIndependent.of_comp (burnolCoPoissonVectorSpace A).subtype hvind
  have hcard := hv'ind.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  omega


/-- Off the zero set of zeta the closed span of the co-Poisson vectors already detects the
evaluator: the symmetric window `[b, 1/b]` is a witness at aperture `b` itself. -/
theorem exists_mem_burnolCoPoissonVectorSpace_inner_ne_zero {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hz : riemannZeta w ≠ 0) :
    ∃ u : soninExtendedSpace b, u ∈ burnolCoPoissonVectorSpace b ∧
      ⟪burnolExtendedSoninEvaluationVector w b hlo hhi hb, u⟫_ℂ ≠ 0 := by
  have hbinv : b < b⁻¹ := by
    have h1 : (1 : ℝ) < b⁻¹ := (one_lt_inv₀ hb).mpr hb1
    linarith
  have hap : subWindowAperture b b⁻¹ = b :=
    subWindowAperture_left_eq hb hbinv.le (le_of_eq rfl)
  have hAle : b ≤ subWindowAperture b b⁻¹ := le_of_eq hap.symm
  refine ⟨coPoissonSubWindowSoninAt hb hbinv.le hAle, ?_, ?_⟩
  · refine (Submodule.span ℂ (burnolCoPoissonVectorGenerators b)).le_topologicalClosure ?_
    exact Submodule.subset_span ⟨coPoissonSubWindowSourceAt hb hb hbinv.le hAle, rfl⟩
  · exact inner_burnolExtendedSoninEvaluationVector_subWindowAt_ne_zero hlo hhi hz hb hb hbinv hAle

/-- **The evaluator is orthogonal to the co-Poisson span exactly at the zeros of zeta.** -/
theorem inner_eq_zero_on_burnolCoPoissonVectorSpace_iff {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) :
    (∀ u : soninExtendedSpace b, u ∈ burnolCoPoissonVectorSpace b →
        ⟪burnolExtendedSoninEvaluationVector w b hlo hhi hb, u⟫_ℂ = 0) ↔
      riemannZeta w = 0 := by
  constructor
  · intro hall
    by_contra hz
    obtain ⟨u, hu, hne⟩ := exists_mem_burnolCoPoissonVectorSpace_inner_ne_zero hb hb1 hlo hhi hz
    exact hne (hall u hu)
  · intro hz u hu
    exact inner_eq_zero_of_mem_burnolCoPoissonVectorSpace hb hlo hhi hz u hu

/-- **The Riemann hypothesis as non-orthogonality of the Riesz evaluator to the co-Poisson span.**
On the right half of the critical strip, orthogonality of the evaluator to the whole span is exactly
a zero of `ζ`; outside the strip `ζ` is nonvanishing for free.  So RH holds precisely when, at every
`w` with `1/2 < re w < 1`, some co-Poisson vector is detected by the evaluator at `w`.  The aperture
`b` is arbitrary in `(0, 1)`: the criterion is equivalent to RH for each of them separately. -/
theorem riemannHypothesis_iff_exists_burnolCoPoisson_inner_ne_zero {b : ℝ} (hb : 0 < b)
    (hb1 : b < 1) :
    RiemannHypothesis ↔
      ∀ (w : ℂ) (hlo : 1 / 2 < w.re) (hhi : w.re < 1),
        ∃ u : soninExtendedSpace b, u ∈ burnolCoPoissonVectorSpace b ∧
          ⟪burnolExtendedSoninEvaluationVector w b hlo hhi hb, u⟫_ℂ ≠ 0 := by
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  constructor
  · intro h w hlo hhi
    exact exists_mem_burnolCoPoissonVectorSpace_inner_ne_zero hb hb1 hlo hhi (h w hlo hhi)
  · intro h w hlo hhi hz
    obtain ⟨u, hu, hne⟩ := h w hlo hhi
    exact hne (inner_eq_zero_of_mem_burnolCoPoissonVectorSpace hb hlo hhi hz u hu)

end RHTower
