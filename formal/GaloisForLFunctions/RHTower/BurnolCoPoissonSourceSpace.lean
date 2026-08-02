import GaloisForLFunctions.RHTower.BurnolSoninReflectedEvaluation

/-!
# Burnol's source-defined co-Poisson subspace

For a seed `g` supported away from zero, Burnol's positive co-Poisson sum is

`t ↦ ∑_{n≥1} g(|t|/n)/n - ∫₀^∞ g(1/y)/y dy`.

The source objects below retain that literal sum, seed integrability, compact multiplicative
support, and equality almost everywhere with an actual vector of the extended Sonine space.  The
co-Poisson source space is the closed span of these vectors and their cosine transforms.  Including
both branches records the Duffin--Weinberger--Burnol intertwining pair and makes Fourier invariance
part of the source construction, without mentioning zeta zeros.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace BigOperators

noncomputable section

namespace RHTower

/-- Literal even positive co-Poisson sum attached to a seed on the positive ray. -/
def burnolCoPoissonRightSum (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
      g (|t| / ((n + 1 : ℕ) : ℝ))) -
    ∫ y in Ioi (0 : ℝ), (((y : ℂ)⁻¹) * g (y⁻¹))

theorem burnolCoPoissonRightSum_even (g : ℝ → ℂ) (t : ℝ) :
    burnolCoPoissonRightSum g (-t) = burnolCoPoissonRightSum g t := by
  simp only [burnolCoPoissonRightSum, abs_neg]

/-- A literal co-Poisson source landing in Burnol's extended Sonine space at aperture `b`.

The landing field says exactly that the explicit co-Poisson sum is square-integrable and belongs
to the carrier: the vector itself is an `L_b` element and its representative agrees almost
everywhere with the source sum. -/
structure BurnolCoPoissonSource (b : ℝ) where
  seed : ℝ → ℂ
  seed_integrable : Integrable seed
  seed_support : Function.support seed ⊆ Icc b b⁻¹
  vector : soninExtendedSpace b
  vector_eq_sum :
    (((vector : soninExtendedSpace b) : evenSubspace) : SoninL2) =ᵐ[volume]
      burnolCoPoissonRightSum seed

/-- Source generators consist of both members of every co-Poisson cosine pair. -/
def burnolCoPoissonGeneratorSet (b : ℝ) : Set evenSubspace :=
  {f | ∃ g : BurnolCoPoissonSource b,
    f = (g.vector : evenSubspace) ∨
      f = soninCosineUnitary (g.vector : evenSubspace)}

theorem burnolCoPoissonGeneratorSet_cosine
    {b : ℝ} {f : evenSubspace}
    (hf : f ∈ burnolCoPoissonGeneratorSet b) :
    soninCosineUnitary f ∈ burnolCoPoissonGeneratorSet b := by
  obtain ⟨g, rfl | rfl⟩ := hf
  · exact ⟨g, Or.inr rfl⟩
  · exact ⟨g, Or.inl (soninCosineUnitary_involutive (g.vector : evenSubspace))⟩

/-- Algebraic span of the literal co-Poisson cosine pairs. -/
def burnolCoPoissonAlgebraicSourceSpace (b : ℝ) :
    Submodule ℂ evenSubspace :=
  Submodule.span ℂ (burnolCoPoissonGeneratorSet b)

theorem soninCosineUnitary_mem_coPoissonAlgebraicSourceSpace
    {b : ℝ} {f : evenSubspace}
    (hf : f ∈ burnolCoPoissonAlgebraicSourceSpace b) :
    soninCosineUnitary f ∈ burnolCoPoissonAlgebraicSourceSpace b := by
  refine Submodule.span_induction (p := fun f _ =>
    soninCosineUnitary f ∈ burnolCoPoissonAlgebraicSourceSpace b)
    ?_ ?_ ?_ ?_ hf
  · intro x hx
    exact Submodule.subset_span (burnolCoPoissonGeneratorSet_cosine hx)
  · have hz : soninCosineUnitary (0 : evenSubspace) = 0 :=
      soninCosineUnitary.toLinearEquiv.map_zero
    rw [hz]
    exact (burnolCoPoissonAlgebraicSourceSpace b).zero_mem
  · intro x y _ _ hx hy
    rw [map_add]
    exact (burnolCoPoissonAlgebraicSourceSpace b).add_mem hx hy
  · intro c x _ hx
    rw [map_smul]
    exact (burnolCoPoissonAlgebraicSourceSpace b).smul_mem c hx

/-- Burnol's closed, source-defined co-Poisson subspace. -/
def burnolCoPoissonSourceSpace (b : ℝ) :
    Submodule ℂ evenSubspace :=
  (burnolCoPoissonAlgebraicSourceSpace b).topologicalClosure

theorem isClosed_burnolCoPoissonSourceSpace (b : ℝ) :
    IsClosed (burnolCoPoissonSourceSpace b : Set evenSubspace) :=
  (burnolCoPoissonAlgebraicSourceSpace b).isClosed_topologicalClosure

theorem burnolCoPoissonAlgebraicSourceSpace_le_soninExtendedSpace (b : ℝ) :
    burnolCoPoissonAlgebraicSourceSpace b ≤ soninExtendedSpace b := by
  rw [burnolCoPoissonAlgebraicSourceSpace, Submodule.span_le]
  intro f hf
  obtain ⟨g, rfl | rfl⟩ := hf
  · exact g.vector.property
  · exact soninCosineUnitary_mem_soninExtendedSpace g.vector.property

theorem burnolCoPoissonSourceSpace_le_soninExtendedSpace
    {b : ℝ} (hb : 0 < b) :
    burnolCoPoissonSourceSpace b ≤ soninExtendedSpace b := by
  exact (burnolCoPoissonAlgebraicSourceSpace b).topologicalClosure_minimal
    (burnolCoPoissonAlgebraicSourceSpace_le_soninExtendedSpace b)
    (isClosed_soninExtendedSpace hb)

theorem soninCosineUnitary_mem_coPoissonSourceSpace
    {b : ℝ} {f : evenSubspace}
    (hf : f ∈ burnolCoPoissonSourceSpace b) :
    soninCosineUnitary f ∈ burnolCoPoissonSourceSpace b := by
  let U := soninCosineUnitary
  let C₀ := burnolCoPoissonAlgebraicSourceSpace b
  let C := burnolCoPoissonSourceSpace b
  have hclosed : IsClosed ((C.comap U.toLinearEquiv.toLinearMap :
      Submodule ℂ evenSubspace) : Set evenSubspace) := by
    exact (isClosed_burnolCoPoissonSourceSpace b).preimage U.continuous
  have hle : C₀ ≤ C.comap U.toLinearEquiv.toLinearMap := by
    intro x hx
    exact (burnolCoPoissonAlgebraicSourceSpace b).le_topologicalClosure
      (soninCosineUnitary_mem_coPoissonAlgebraicSourceSpace hx)
  have hf' := (C₀.topologicalClosure_minimal hle hclosed) hf
  exact hf'

/-- Burnol's quotient realization inside `L_b`: extended Sonine vectors orthogonal to every
co-Poisson source. -/
def burnolCoPoissonQuotientSpace (b : ℝ) :
    Submodule ℂ evenSubspace :=
  soninExtendedSpace b ⊓ (burnolCoPoissonSourceSpace b)ᗮ

theorem isClosed_burnolCoPoissonQuotientSpace {b : ℝ} (hb : 0 < b) :
    IsClosed (burnolCoPoissonQuotientSpace b : Set evenSubspace) :=
  (isClosed_soninExtendedSpace hb).inter
    (Submodule.isClosed_orthogonal (burnolCoPoissonSourceSpace b))

theorem soninCosineUnitary_mem_coPoissonQuotientSpace
    {b : ℝ} {f : evenSubspace}
    (hf : f ∈ burnolCoPoissonQuotientSpace b) :
    soninCosineUnitary f ∈ burnolCoPoissonQuotientSpace b := by
  rw [burnolCoPoissonQuotientSpace] at hf ⊢
  constructor
  · exact soninCosineUnitary_mem_soninExtendedSpace hf.1
  · intro c hc
    have hFc : soninCosineUnitary c ∈ burnolCoPoissonSourceSpace b :=
      soninCosineUnitary_mem_coPoissonSourceSpace hc
    change ⟪c, soninCosineUnitary f⟫_ℂ = 0
    rw [← soninCosineUnitary.inner_map_map]
    rw [soninCosineUnitary_involutive]
    exact hf.2 (soninCosineUnitary c) hFc

end RHTower
