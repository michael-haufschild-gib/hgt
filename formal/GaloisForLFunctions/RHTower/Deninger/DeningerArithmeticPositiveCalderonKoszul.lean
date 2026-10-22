import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticUnitaryBRSTHodge
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Prod

/-!
# Positive Calderón--conormal and Koszul contractions

Finite arithmetic Hodge packets use a positive Dirichlet-to-Neumann
operator `A` and a linearized Milnor-incidence subspace `L`.  The
Calderón graph of `A` has trivial intersection with the conormal
`L × Lᗮ`: a vector in the intersection has zero positive energy.

The second theorem is the algebraic contraction kernel used by the
positive Hodge--Koszul argument.  If `d h + h d` is a nonzero scalar
multiple of the identity, every `d`-cycle is a `d`-boundary.

Both statements are unconditional and contain no zeta-zero or RH
premise.
-/

namespace RHTower

noncomputable section

section CalderonConormal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Linear conormal of an incidence subspace in the real cotangent
model `E × E`. -/
def deningerLinearConormal (L : Submodule ℝ E) :
    Submodule ℝ (E × E) :=
  Submodule.prod L Lᗮ

/-- The graph of a linear operator is linearly equivalent to its
domain. -/
def deningerCalderonGraphEquiv (A : E →ₗ[ℝ] E) :
    E ≃ₗ[ℝ] A.graph where
  toFun x := ⟨(x, A x), by simp⟩
  invFun z := z.1.1
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (A.mem_graph_iff z.1).mp z.2 |>.symm
  map_add' x y := by
    apply Subtype.ext
    ext <;> simp
  map_smul' c x := by
    apply Subtype.ext
    ext <;> simp

/-- The linear conormal is linearly equivalent to the product of the
incidence subspace and its orthogonal. -/
def deningerLinearConormalEquiv (L : Submodule ℝ E) :
    (L × Lᗮ) ≃ₗ[ℝ] deningerLinearConormal L where
  toFun z := ⟨((z.1 : E), (z.2 : E)), z.1.2, z.2.2⟩
  invFun z := (⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The Calderón graph has the dimension of the boundary-position
space. -/
theorem finrank_deningerCalderonGraph (A : E →ₗ[ℝ] E) :
    Module.finrank ℝ A.graph = Module.finrank ℝ E :=
  LinearEquiv.finrank_eq (deningerCalderonGraphEquiv A).symm

/-- In finite dimension, the incidence conormal has half the
dimension of the position--momentum phase space. -/
theorem finrank_deningerLinearConormal
    [FiniteDimensional ℝ E]
    (L : Submodule ℝ E) :
    Module.finrank ℝ (deningerLinearConormal L) =
      Module.finrank ℝ E := by
  rw [LinearEquiv.finrank_eq
      (deningerLinearConormalEquiv L).symm,
    Module.finrank_prod]
  exact L.finrank_add_finrank_orthogonal

/--
`DAC_POSITIVE_GRAPH_CONORMAL_TRANSVERSALITY`, intersection part.

The graph of a strictly positive linear operator intersects the
conormal of any linear incidence subspace only at zero.  No
finite-dimensional hypothesis is needed for this kernel statement.
-/
theorem deningerPositiveCalderonGraph_inf_conormal_eq_bot
    (A : E →ₗ[ℝ] E)
    (L : Submodule ℝ E)
    (hpositive : ∀ x : E, x ≠ 0 → 0 < inner ℝ (A x) x) :
    A.graph ⊓ deningerLinearConormal L = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  rcases hz with ⟨hgraph, hconormal⟩
  have hzgraph : z.2 = A z.1 :=
    (A.mem_graph_iff z).mp hgraph
  have hzprod :
      z.1 ∈ L ∧ z.2 ∈ Lᗮ :=
    Submodule.mem_prod.mp hconormal
  have hinner : inner ℝ (A z.1) z.1 = 0 := by
    rw [← hzgraph]
    exact
      Submodule.inner_left_of_mem_orthogonal
        hzprod.1 hzprod.2
  have hzfst : z.1 = 0 := by
    by_contra hne
    have hstrict := hpositive z.1 hne
    rw [hinner] at hstrict
    exact lt_irrefl 0 hstrict
  apply Prod.ext
  · exact hzfst
  · change z.2 = 0
    rw [hzgraph, hzfst, map_zero]

/--
Constrained Green stationarity: the boundary position satisfies the
incidence relation and the Dirichlet-to-Neumann value annihilates
every allowed incidence variation.
-/
def deningerConstrainedGreenStationary
    (A : E →ₗ[ℝ] E)
    (L : Submodule ℝ E)
    (x : E) : Prop :=
  x ∈ L ∧ ∀ y : E, y ∈ L → inner ℝ y (A x) = 0

/--
`DAC_GREEN_EULER_LAGRANGE_GRAPH_CONORMAL`.

The constrained Euler--Lagrange equation for a quadratic Green energy
is exactly membership of its Calderón graph in the incidence
conormal.
-/
theorem deningerCalderonGraph_conormal_iff_stationary
    (A : E →ₗ[ℝ] E)
    (L : Submodule ℝ E)
    (x : E) :
    (x, A x) ∈ A.graph ⊓ deningerLinearConormal L ↔
      deningerConstrainedGreenStationary A L x := by
  simp only [Submodule.mem_inf, A.mem_graph_iff,
    deningerLinearConormal, Submodule.mem_prod,
    deningerConstrainedGreenStationary]
  constructor
  · rintro ⟨_, hxL, hAx⟩
    exact ⟨hxL, (L.mem_orthogonal (A x)).1 hAx⟩
  · rintro ⟨hxL, hstationary⟩
    exact
      ⟨True.intro, hxL,
        (L.mem_orthogonal (A x)).2 hstationary⟩

/--
A stationary point of a strictly positive constrained Green energy is
zero.
-/
theorem deningerConstrainedGreenStationary_eq_zero_of_positive
    (A : E →ₗ[ℝ] E)
    (L : Submodule ℝ E)
    (hpositive : ∀ x : E, x ≠ 0 → 0 < inner ℝ (A x) x)
    {x : E}
    (hstationary : deningerConstrainedGreenStationary A L x) :
    x = 0 := by
  have hmem :
      (x, A x) ∈ A.graph ⊓ deningerLinearConormal L :=
    (deningerCalderonGraph_conormal_iff_stationary A L x).2
      hstationary
  have hintersection :=
    deningerPositiveCalderonGraph_inf_conormal_eq_bot
      A L hpositive
  rw [hintersection] at hmem
  exact congrArg Prod.fst hmem

/--
`DAC_FINITE_CALDERON_CONORMAL_DIRECT_SUM`.

On a finite Hodge packet, strict positivity makes the Calderón graph
and incidence conormal complementary Lagrangians.  Hence the linear
derived-intersection fibre is acyclic, not merely kernel-free.
-/
theorem deningerPositiveCalderonGraph_sup_conormal_eq_top
    [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] E)
    (L : Submodule ℝ E)
    (hpositive : ∀ x : E, x ≠ 0 → 0 < inner ℝ (A x) x) :
    A.graph ⊔ deningerLinearConormal L = ⊤ := by
  apply Submodule.eq_top_of_disjoint
  · rw [Module.finrank_prod, finrank_deningerCalderonGraph,
      finrank_deningerLinearConormal]
  · rw [disjoint_iff_inf_le,
      deningerPositiveCalderonGraph_inf_conormal_eq_bot
        A L hpositive]

/-! ## Global energy and chirality-kernel reduction -/

/--
`DAC_GLOBAL_GREEN_ENERGY_STRICT_POSITIVITY`.

A nonnegative Green energy that detects zero makes its
Dirichlet-to-Neumann operator strictly positive.  No uniform spectral
gap is required.
-/
theorem deningerStrictPositive_of_greenEnergy_detects_zero
    (A : E →ₗ[ℝ] E)
    (energy : E → ℝ)
    (henergy : ∀ x : E, inner ℝ (A x) x = energy x)
    (hnonnegative : ∀ x : E, 0 ≤ energy x)
    (hdetects : ∀ x : E, energy x = 0 → x = 0) :
    ∀ x : E, x ≠ 0 → 0 < inner ℝ (A x) x := by
  intro x hx
  rw [henergy]
  exact
    lt_of_le_of_ne
      (hnonnegative x)
      (Ne.symm fun hzero => hx (hdetects x hzero))

/--
`DAC_GLOBAL_CALDERON_CHIRALITY_KERNEL_REDUCTION`.

Suppose a zero of a global chirality operator has Cauchy data in the
intersection of the positive Calderón graph and the incidence
conormal.  If vanishing Cauchy data determines the relative harmonic
class, then the chirality kernel is trivial.
-/
theorem deningerGlobalChirality_kernel_eq_bot
    {H : Type*}
    [AddCommGroup H] [Module ℝ H]
    (S : H →ₗ[ℝ] H)
    (trace : H →ₗ[ℝ] E)
    (A : E →ₗ[ℝ] E)
    (L : Submodule ℝ E)
    (hpositive : ∀ x : E, x ≠ 0 → 0 < inner ℝ (A x) x)
    (hkernel_boundary :
      ∀ x : H,
        S x = 0 →
          (trace x, A (trace x)) ∈
            A.graph ⊓ deningerLinearConormal L)
    (hrelative_unique :
      ∀ x : H, S x = 0 → trace x = 0 → x = 0) :
    LinearMap.ker S = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hintersection :
      A.graph ⊓ deningerLinearConormal L = ⊥ :=
    deningerPositiveCalderonGraph_inf_conormal_eq_bot
      A L hpositive
  have hpair_mem :
      (trace x, A (trace x)) ∈
        A.graph ⊓ deningerLinearConormal L :=
    hkernel_boundary x hx
  have hpair_zero : (trace x, A (trace x)) = 0 := by
    rw [hintersection] at hpair_mem
    exact hpair_mem
  have htrace : trace x = 0 :=
    congrArg Prod.fst hpair_zero
  exact hrelative_unique x hx htrace

/--
Energy form of
`deningerGlobalChirality_kernel_eq_bot`.  This is the exact abstract
kernel theorem used by the global arithmetic Calderón construction.
-/
theorem deningerGlobalChirality_kernel_eq_bot_of_greenEnergy
    {H : Type*}
    [AddCommGroup H] [Module ℝ H]
    (S : H →ₗ[ℝ] H)
    (trace : H →ₗ[ℝ] E)
    (A : E →ₗ[ℝ] E)
    (L : Submodule ℝ E)
    (energy : E → ℝ)
    (henergy : ∀ x : E, inner ℝ (A x) x = energy x)
    (hnonnegative : ∀ x : E, 0 ≤ energy x)
    (hdetects : ∀ x : E, energy x = 0 → x = 0)
    (hkernel_boundary :
      ∀ x : H,
        S x = 0 →
          (trace x, A (trace x)) ∈
            A.graph ⊓ deningerLinearConormal L)
    (hrelative_unique :
      ∀ x : H, S x = 0 → trace x = 0 → x = 0) :
    LinearMap.ker S = ⊥ := by
  exact
    deningerGlobalChirality_kernel_eq_bot
      S trace A L
      (deningerStrictPositive_of_greenEnergy_detects_zero
        A energy henergy hnonnegative hdetects)
      hkernel_boundary hrelative_unique

omit [InnerProductSpace ℝ E] in
/--
`DAC_RESTRICTED_SUM_GREEN_ENERGY_DETECTION`.

A summable family of nonnegative local Green energies is globally
nonnegative.  If the local energies jointly detect zero, then their
sum detects zero.  No uniform positive lower bound is used.
-/
theorem deningerTsumEnergy_nonnegative_and_detects_zero
    {ι : Type*}
    (localEnergy : ι → E → ℝ)
    (hsummable :
      ∀ x : E, Summable (fun i : ι => localEnergy i x))
    (hnonnegative :
      ∀ (i : ι) (x : E), 0 ≤ localEnergy i x)
    (hjointly_detects :
      ∀ x : E, (∀ i : ι, localEnergy i x = 0) → x = 0) :
    (∀ x : E, 0 ≤ ∑' i : ι, localEnergy i x) ∧
      (∀ x : E,
        (∑' i : ι, localEnergy i x) = 0 →
          x = 0) := by
  constructor
  · intro x
    exact tsum_nonneg fun i => hnonnegative i x
  · intro x hsum
    apply hjointly_detects x
    intro i
    have hi :
        localEnergy i x ≤
          ∑' j : ι, localEnergy j x :=
      (hsummable x).le_tsum i fun j _ => hnonnegative j x
    rw [hsum] at hi
    exact le_antisymm hi (hnonnegative i x)

/--
`DAC_GLOBAL_GREEN_ENERGY_RADICAL_PASSAGE`.

If local nonnegative energies vanish on boundaries and jointly
classify boundaries, then the summed energy has radical exactly the
boundary submodule.
-/
theorem deningerTsumEnergy_eq_zero_iff_mem_boundaries
    {ι : Type*}
    (boundaries : Submodule ℝ E)
    (localEnergy : ι → E → ℝ)
    (hsummable :
      ∀ x : E, Summable (fun i : ι => localEnergy i x))
    (hnonnegative :
      ∀ (i : ι) (x : E), 0 ≤ localEnergy i x)
    (hboundaries :
      ∀ x : E, x ∈ boundaries →
        ∀ i : ι, localEnergy i x = 0)
    (hlocal_zero_is_boundary :
      ∀ x : E,
        (∀ i : ι, localEnergy i x = 0) →
          x ∈ boundaries)
    (x : E) :
    (∑' i : ι, localEnergy i x) = 0 ↔
      x ∈ boundaries := by
  constructor
  · intro hsum
    apply hlocal_zero_is_boundary x
    intro i
    have hi :
        localEnergy i x ≤
          ∑' j : ι, localEnergy j x :=
      (hsummable x).le_tsum i fun j _ => hnonnegative j x
    rw [hsum] at hi
    exact le_antisymm hi (hnonnegative i x)
  · intro hx
    have hzero :
        (fun i : ι => localEnergy i x) = 0 := by
      funext i
      exact hboundaries x hx i
    rw [hzero]
    exact tsum_zero

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/--
`DAC_LOCAL_GREEN_ENERGY_SUMMABLE_MAJORANT`.

A summable packet majorant proves pointwise summability of every
nonnegative local-energy family it dominates.  This is the abstract
bounded-set estimate required in each seminorm of the restricted
arithmetic source topology.
-/
theorem deningerLocalEnergy_summable_of_summable_majorant
    {ι X : Type*}
    (localEnergy : ι → X → ℝ)
    (majorant : ι → ℝ)
    (size : X → ℝ)
    (hmajorant : Summable majorant)
    (hnonnegative : ∀ i x, 0 ≤ localEnergy i x)
    (hbound : ∀ i x, localEnergy i x ≤ majorant i * size x)
    (x : X) :
    Summable (fun i => localEnergy i x) :=
  Summable.of_nonneg_of_le
    (fun i => hnonnegative i x)
    (fun i => hbound i x)
    (hmajorant.mul_right (size x))

/-- Sum of local continuous Green bilinear forms. -/
def deningerSummedGreenForm
    {ι : Type*}
    (localForm : ι → E →L[ℝ] E →L[ℝ] ℝ) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ∑' i, localForm i

/--
Summability in the continuous-bilinear-map space commutes with
evaluation in both variables.
-/
theorem deningerSummedGreenForm_hasSum_apply_apply
    {ι : Type*}
    (localForm : ι → E →L[ℝ] E →L[ℝ] ℝ)
    (hforms : Summable localForm)
    (x y : E) :
    HasSum (fun i => localForm i x y)
      (deningerSummedGreenForm localForm x y) := by
  have houter :
      HasSum (fun i => localForm i x)
        ((∑' i, localForm i) x) := by
    simpa using
      hforms.hasSum.mapL
        ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ)) x)
  simpa [deningerSummedGreenForm] using
    houter.mapL ((ContinuousLinearMap.apply ℝ ℝ) y)

/-- The summed Green form evaluates to the sum of local pairings. -/
theorem deningerSummedGreenForm_apply_apply
    {ι : Type*}
    (localForm : ι → E →L[ℝ] E →L[ℝ] ℝ)
    (hforms : Summable localForm)
    (x y : E) :
    deningerSummedGreenForm localForm x y =
      ∑' i, localForm i x y :=
  (deningerSummedGreenForm_hasSum_apply_apply
    localForm hforms x y).tsum_eq.symm

/--
The diagonal energy of the summed continuous Green form is
continuous.  Thus form-level packet summability supplies the exact
continuity needed for passage to closed boundaries.
-/
theorem deningerSummedGreenEnergy_continuous
    {ι : Type*}
    (localForm : ι → E →L[ℝ] E →L[ℝ] ℝ) :
    Continuous
      (fun x : E => deningerSummedGreenForm localForm x x) :=
  (deningerSummedGreenForm localForm).continuous.clm_apply
    continuous_id

/-- Nonnegative local Green forms give nonnegative summed energy. -/
theorem deningerSummedGreenEnergy_nonnegative
    {ι : Type*}
    (localForm : ι → E →L[ℝ] E →L[ℝ] ℝ)
    (hforms : Summable localForm)
    (hnonnegative : ∀ i x, 0 ≤ localForm i x x)
    (x : E) :
    0 ≤ deningerSummedGreenForm localForm x x := by
  rw [deningerSummedGreenForm_apply_apply localForm hforms x x]
  exact tsum_nonneg fun i => hnonnegative i x

/--
`DAC_GREEN_ENERGY_CLOSED_BOUNDARY_PASSAGE`.

A continuous energy that vanishes on algebraic boundaries also
vanishes on their topological closure.
-/
theorem deningerContinuousEnergy_zero_on_boundaryClosure
    (boundaries : Submodule ℝ E)
    (energy : E → ℝ)
    (hcontinuous : Continuous energy)
    (hzero : ∀ x : E, x ∈ boundaries → energy x = 0)
    {x : E}
    (hx : x ∈ boundaries.topologicalClosure) :
    energy x = 0 := by
  have hsubset :
      (boundaries : Set E) ⊆ {y : E | energy y = 0} := by
    intro y hy
    exact hzero y hy
  have hclosed :
      IsClosed {y : E | energy y = 0} :=
    isClosed_eq hcontinuous continuous_const
  have hxclosure : x ∈ closure (boundaries : Set E) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hx
  exact (closure_minimal hsubset hclosed) hxclosure

/--
Countable/restricted-sum form of the global chirality-kernel
reduction.  Summability and joint zero detection of local energies
are the complete extra inputs.
-/
theorem deningerGlobalChirality_kernel_eq_bot_of_tsumEnergy
    {H ι : Type*}
    [AddCommGroup H] [Module ℝ H]
    (S : H →ₗ[ℝ] H)
    (trace : H →ₗ[ℝ] E)
    (A : E →ₗ[ℝ] E)
    (L : Submodule ℝ E)
    (localEnergy : ι → E → ℝ)
    (henergy :
      ∀ x : E,
        inner ℝ (A x) x =
          ∑' i : ι, localEnergy i x)
    (hsummable :
      ∀ x : E, Summable (fun i : ι => localEnergy i x))
    (hnonnegative :
      ∀ (i : ι) (x : E), 0 ≤ localEnergy i x)
    (hjointly_detects :
      ∀ x : E, (∀ i : ι, localEnergy i x = 0) → x = 0)
    (hkernel_boundary :
      ∀ x : H,
        S x = 0 →
          (trace x, A (trace x)) ∈
            A.graph ⊓ deningerLinearConormal L)
    (hrelative_unique :
      ∀ x : H, S x = 0 → trace x = 0 → x = 0) :
    LinearMap.ker S = ⊥ := by
  obtain ⟨hnonnegative_global, hdetects_global⟩ :=
    deningerTsumEnergy_nonnegative_and_detects_zero
      localEnergy hsummable hnonnegative hjointly_detects
  exact
    deningerGlobalChirality_kernel_eq_bot_of_greenEnergy
      S trace A L
      (fun x => ∑' i : ι, localEnergy i x)
      henergy hnonnegative_global hdetects_global
      hkernel_boundary hrelative_unique

/--
`DAC_RELATIVE_CAUCHY_UNIQUENESS_DESCENT`.

Relative Cauchy uniqueness descends from a jointly separating chart
cover: zero global Cauchy data give zero local Cauchy data; local
unique continuation kills every chart restriction; joint separation
kills the global class.
-/
theorem deningerRelativeCauchyUnique_of_localRestrictions
    {ι H B U : Type*}
    [AddCommGroup H] [Module ℝ H]
    [AddCommGroup B] [Module ℝ B]
    [AddCommGroup U] [Module ℝ U]
    (S : H →ₗ[ℝ] H)
    (trace : H →ₗ[ℝ] B)
    (restriction : ι → H →ₗ[ℝ] U)
    (localCauchy : ι → H →ₗ[ℝ] B)
    (hglobal_to_local :
      ∀ (x : H) (i : ι),
        trace x = 0 → localCauchy i x = 0)
    (hlocal_unique :
      ∀ (x : H) (i : ι),
        S x = 0 →
          localCauchy i x = 0 →
            restriction i x = 0)
    (hrestrictions_separate :
      ∀ x : H, (∀ i : ι, restriction i x = 0) → x = 0) :
    ∀ x : H, S x = 0 → trace x = 0 → x = 0 := by
  intro x hS htrace
  apply hrestrictions_separate x
  intro i
  exact
    hlocal_unique x i hS
      (hglobal_to_local x i htrace)

end CalderonConormal

section ScaledChainContraction

variable {𝕜 C : Type*} [Field 𝕜] [AddCommGroup C] [Module 𝕜 C]

/--
`DAC_POSITIVE_HODGE_KOSZUL_CONTRACTION`, abstract contraction kernel.

If `d h + h d = a · id` with `a ≠ 0`, then every `d`-cycle is a
`d`-boundary.  The Euler homotopy on a positive-total-degree Koszul
summand is the specialization with `a` equal to that total degree.
-/
theorem deninger_exact_of_scaled_chainContraction
    (d h : C →ₗ[𝕜] C)
    (a : 𝕜)
    (ha : a ≠ 0)
    (hcontract : ∀ x : C, d (h x) + h (d x) = a • x)
    {x : C}
    (hx : d x = 0) :
    ∃ y : C, d y = x := by
  refine ⟨a⁻¹ • h x, ?_⟩
  have hdh : d (h x) = a • x := by
    simpa [hx] using hcontract x
  rw [map_smul, hdh, ← mul_smul, inv_mul_cancel₀ ha, one_smul]

/-- Unit-scaled form of
`deninger_exact_of_scaled_chainContraction`. -/
theorem deninger_exact_of_chainContraction
    (d h : C →ₗ[𝕜] C)
    (hcontract : ∀ x : C, d (h x) + h (d x) = x)
    {x : C}
    (hx : d x = 0) :
    ∃ y : C, d y = x := by
  apply
    deninger_exact_of_scaled_chainContraction
      d h 1 one_ne_zero
  · simpa using hcontract
  · exact hx

end ScaledChainContraction

end

end RHTower
