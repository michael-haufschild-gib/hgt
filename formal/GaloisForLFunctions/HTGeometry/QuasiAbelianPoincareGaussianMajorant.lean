import GaloisForLFunctions.HTGeometry.FinitePiProductSummability
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Polynomial-Gaussian majorants for quasi-Abelian Poincare series

Abe's positive-factor estimates reduce every fixed derivative order on a compact set to a finite
integer-lattice majorant: a coordinatewise polynomial times a strictly decaying Gaussian. This
file turns that exact bound into local normal convergence. It is independent of the later subgroup
induction and can therefore be reused for the seed series and every differentiated complement.
-/

open Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Reindexing a locally normally summable family by an injective map preserves local normal
summability on an open set.  In particular, an equivalence may transfer a lattice majorant to its
bundled subgroup index. -/
theorem SummableLocallyUniformlyOn.comp_injective_open
    {alpha beta iota kappa : Type*} [AddCommGroup alpha] [UniformSpace alpha]
    [IsUniformAddGroup alpha] [CompleteSpace alpha]
    [TopologicalSpace beta] [LocallyCompactSpace beta]
    {f : iota → beta → alpha} {U : Set beta}
    (hU : IsOpen U) (h : SummableLocallyUniformlyOn f U)
    {e : kappa → iota} (he : Function.Injective e) :
    SummableLocallyUniformlyOn (fun k ↦ f (e k)) U := by
  apply summableLocallyUniformlyOn_of_of_forall_exists_nhds
  intro x hx
  obtain ⟨K, ⟨hKnhds, hKcompact⟩, hKU⟩ :=
    (compact_basis_nhds x).mem_iff.mp (hU.mem_nhds hx)
  refine ⟨K, nhdsWithin_le_nhds hKnhds, ?_⟩
  have hcanon := h.hasSumLocallyUniformlyOn
  have hloc : TendstoUniformlyOn
      (fun t : Finset iota ↦ fun y ↦ ∑ i ∈ t, f i y)
      (fun y ↦ ∑' i, f i y) Filter.atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hcanon
      K hKU hKcompact
  have huni : HasSumUniformlyOn f (fun y ↦ ∑' i, f i y) K :=
    hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr hloc
  change Summable (UniformOnFun.ofFun {K} ∘ fun k ↦ f (e k))
  exact huni.summableUniformlyOn.comp_injective he

/-- Coordinatewise polynomial-Gaussian weight on a finite integer lattice. -/
def polynomialGaussianLatticeWeight
    (ι : Type) [Fintype ι] (A : ι → ℕ) (sigma : ι → ℝ)
    (z : ι → ℤ) : ℝ :=
  ∏ i, (1 + ((z i).natAbs : ℝ)) ^ A i *
    Real.exp (-sigma i * (z i : ℝ) ^ (2 : ℕ))

/-- Every such weight is summable when every coordinate has strictly positive Gaussian decay. -/
theorem summable_polynomialGaussianLatticeWeight
    (ι : Type) [Fintype ι] (A : ι → ℕ) (sigma : ι → ℝ)
    (hsigma : ∀ i, 0 < sigma i) :
    Summable (polynomialGaussianLatticeWeight ι A sigma) := by
  change Summable (fun z : ι → ℤ =>
    ∏ i, (1 + ((z i).natAbs : ℝ)) ^ A i *
      Real.exp (-sigma i * (z i : ℝ) ^ (2 : ℕ)))
  exact GaloisForLFunctions.summable_fintype_pi_polynomialGaussian
    ι A sigma hsigma

/-- **Abe local-normal-convergence bridge.** A compact-uniform polynomial-Gaussian lattice bound
implies local normal convergence of the corresponding function series. -/
theorem summableLocallyUniformlyOn_of_polynomialGaussianLattice_bound
    {ι : Type} {X : Type*} [Fintype ι]
    [TopologicalSpace X] [LocallyCompactSpace X]
    (f : (ι → ℤ) → X → ℂ) (s : Set X) (hs : IsOpen s)
    (A : ι → ℕ) (sigma : ι → ℝ) (hsigma : ∀ i, 0 < sigma i)
    (hbound : ∀ K : Set X, K ⊆ s → IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ K →
        ‖f z x‖ ≤ C * polynomialGaussianLatticeWeight ι A sigma z) :
    SummableLocallyUniformlyOn f s := by
  apply SummableLocallyUniformlyOn_of_locally_bounded hs
  intro K hKs hK
  obtain ⟨C, hC, hboundC⟩ := hbound K hKs hK
  refine ⟨fun z => C * polynomialGaussianLatticeWeight ι A sigma z,
    (summable_polynomialGaussianLatticeWeight ι A sigma hsigma).mul_left C,
    ?_⟩
  exact hboundC

/-- The norm of a convergent Poincare series is bounded by the summed polynomial-Gaussian
majorant.  Unlike a finite partial-sum estimate, this controls the actual `tsum`. -/
theorem norm_tsum_le_polynomialGaussianLatticeWeight
    {ι : Type} [Fintype ι]
    (f : (ι → ℤ) → ℂ) (A : ι → ℕ) (sigma : ι → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (C : ℝ)
    (hbound : ∀ z, ‖f z‖ ≤ C * polynomialGaussianLatticeWeight ι A sigma z) :
    ‖∑' z, f z‖ ≤ C * ∑' z, polynomialGaussianLatticeWeight ι A sigma z := by
  have hmajor : Summable
      (fun z => C * polynomialGaussianLatticeWeight ι A sigma z) :=
    (summable_polynomialGaussianLatticeWeight ι A sigma hsigma).mul_left C
  have hnorm : Summable (fun z => ‖f z‖) :=
    Summable.of_nonneg_of_le (fun z => norm_nonneg (f z)) hbound hmajor
  calc
    ‖∑' z, f z‖ ≤ ∑' z, ‖f z‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' z, C * polynomialGaussianLatticeWeight ι A sigma z :=
      hnorm.tsum_le_tsum hbound hmajor
    _ = C * ∑' z, polynomialGaussianLatticeWeight ι A sigma z :=
      tsum_mul_left

/-- A compact-uniform scalar bound tending to zero forces local uniform convergence to zero.
This is the final topological step in Abe's damping argument: after summing the Gaussian lattice
majorant, every compact receives one scalar error bound. -/
theorem tendstoLocallyUniformly_zero_of_compact_norm_bound
    {T X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    {l : Filter T} {F : T → X → ℂ}
    (hbound : ∀ K : Set X, IsCompact K →
      ∃ b : T → ℝ, Filter.Tendsto b l (nhds 0) ∧
        ∀ᶠ t in l, ∀ x : X, x ∈ K → ‖F t x‖ ≤ b t) :
    TendstoLocallyUniformly F (fun _ ↦ 0) l := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨b, hb, hFb⟩ := hbound K hK
  filter_upwards [hb.eventually_lt_const hε, hFb] with t hbt ht x hx
  rw [dist_zero_left]
  exact (ht x hx).trans_lt hbt

/-- **Abe damping limit for a full Poincare series.** If every lattice term has a compact-uniform
polynomial-Gaussian majorant multiplied by `B^r * exp (-δ B)`, with `δ > 0`, then the actual
Poincare `tsum` tends locally uniformly to zero as `B → +∞`.  Thus polynomial losses from any
fixed jet order cannot obstruct subgroup-complement peeling. -/
theorem tendstoLocallyUniformly_tsum_zero_of_polynomialGaussian_damping_bound
    {ι : Type} {X : Type*} [Fintype ι]
    [TopologicalSpace X] [LocallyCompactSpace X]
    (f : ℝ → (ι → ℤ) → X → ℂ)
    (A : ι → ℕ) (sigma : ι → ℝ) (hsigma : ∀ i, 0 < sigma i)
    (r : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hbound : ∀ K : Set X, IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, 0 ≤ B → ∀ z x, x ∈ K →
        ‖f B z x‖ ≤
          (C * (B ^ r * Real.exp (-(δ * B)))) *
            polynomialGaussianLatticeWeight ι A sigma z) :
    TendstoLocallyUniformly
      (fun B x => ∑' z, f B z x) (fun _ ↦ 0) Filter.atTop := by
  apply tendstoLocallyUniformly_zero_of_compact_norm_bound
  intro K hK
  obtain ⟨C, hC, hboundC⟩ := hbound K hK
  let S : ℝ := ∑' z, polynomialGaussianLatticeWeight ι A sigma z
  have hdecay : Filter.Tendsto
      (fun B : ℝ => B ^ r * Real.exp (-(δ * B))) Filter.atTop (nhds 0) := by
    have hbase := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero r
    have hscale : Filter.Tendsto (fun B : ℝ => δ * B) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hδ Filter.tendsto_id
    have hcomp := hbase.comp hscale
    have hconst := hcomp.const_mul ((δ ^ r)⁻¹)
    simp only [mul_zero] at hconst
    refine hconst.congr ?_
    intro B
    have hpow : (δ * B) ^ r = δ ^ r * B ^ r := by rw [mul_pow]
    rw [Function.comp_apply, hpow]
    field_simp [ne_of_gt hδ]
  refine ⟨fun B => (C * (B ^ r * Real.exp (-(δ * B)))) * S, ?_, ?_⟩
  · have hscaled := hdecay.const_mul (C * S)
    simpa only [mul_zero] using hscaled.congr'
      (Filter.Eventually.of_forall fun B => by ring)
  · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with B hB x hx
    exact norm_tsum_le_polynomialGaussianLatticeWeight
      (fun z => f B z x) A sigma hsigma
      (C * (B ^ r * Real.exp (-(δ * B))))
      (fun z => hboundC B hB z x hx)

end

end GaloisForLFunctions.HTGeometry
