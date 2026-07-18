import GaloisForLFunctions.RHTower.ScaleCovariantBernsteinAbelTomography

/-!
# Intrinsic aggregate source for Bernstein--Abel tomography

An indexed atomic source is observable only through the sum of its weights on each equal-node
fibre.  This file constructs the nonzero aggregate support, proves exact fibrewise descent of all
power moments, transfers the cofinite support and geometric hypotheses, and applies the tomography
theorem without injectivity or pointwise nonvanishing assumptions on the raw indexing.
-/

open Complex Filter Topology
open scoped BigOperators Real

namespace RHTower

noncomputable section

/-- Total weight carried by one geometric node of an arbitrarily indexed atomic source. -/
def atomicAggregateWeight {I : Type*} (c z : I → ℂ) (u : ℂ) : ℂ :=
  ∑' i : z ⁻¹' {u}, c i.1

/-- The intrinsic occupied support consists exactly of the nonzero aggregate fibres. -/
def AtomicAggregateSupport {I : Type*} (c z : I → ℂ) : Type :=
  {u : ℂ // atomicAggregateWeight c z u ≠ 0}

/-- Geometric node of the intrinsic aggregate source. -/
def atomicAggregateNode {I : Type*} (c z : I → ℂ) :
    AtomicAggregateSupport c z → ℂ :=
  fun u => u.1

/-- Coefficient of the intrinsic aggregate source. -/
def atomicAggregateCoefficient {I : Type*} (c z : I → ℂ) :
    AtomicAggregateSupport c z → ℂ :=
  fun u => atomicAggregateWeight c z u.1

/-- Fibrewise regrouping preserves absolute summability of the aggregate weights. -/
theorem summable_atomicAggregateWeight
    {I : Type*} {c z : I → ℂ} (hc : Summable c) :
    Summable (atomicAggregateWeight c z) := by
  simpa only [atomicAggregateWeight] using
    (hc.hasSum.tsum_fiberwise z).summable

/-- The nonzero aggregate coefficients form an absolutely summable intrinsic source. -/
theorem summable_atomicAggregateCoefficient
    {I : Type*} {c z : I → ℂ} (hc : Summable c) :
    Summable (atomicAggregateCoefficient c z) := by
  simpa only [AtomicAggregateSupport, atomicAggregateCoefficient] using
    (summable_atomicAggregateWeight hc).subtype
      (fun u => atomicAggregateWeight c z u ≠ 0)

/-- A nonzero aggregate fibre contains at least one raw source index. -/
theorem exists_eq_of_atomicAggregateWeight_ne_zero
    {I : Type*} {c z : I → ℂ} {u : ℂ}
    (hu : atomicAggregateWeight c z u ≠ 0) :
    ∃ i : I, z i = u := by
  by_contra h
  push_neg at h
  have hempty : z ⁻¹' ({u} : Set ℂ) = ∅ := by
    ext i
    simp [h i]
  apply hu
  rw [atomicAggregateWeight, hempty]
  simp

/-- A chosen raw representative of each occupied aggregate fibre. -/
def atomicAggregateRepresentative {I : Type*} (c z : I → ℂ)
    (u : AtomicAggregateSupport c z) : I :=
  Classical.choose (exists_eq_of_atomicAggregateWeight_ne_zero u.property)

@[simp] theorem atomicAggregateRepresentative_spec
    {I : Type*} (c z : I → ℂ) (u : AtomicAggregateSupport c z) :
    z (atomicAggregateRepresentative c z u) = atomicAggregateNode c z u :=
  Classical.choose_spec (exists_eq_of_atomicAggregateWeight_ne_zero u.property)

/-- Distinct aggregate nodes have distinct chosen raw representatives. -/
theorem atomicAggregateRepresentative_injective
    {I : Type*} (c z : I → ℂ) :
    Function.Injective (atomicAggregateRepresentative c z) := by
  intro u v huv
  apply Subtype.ext
  change atomicAggregateNode c z u = atomicAggregateNode c z v
  rw [← atomicAggregateRepresentative_spec c z u,
    ← atomicAggregateRepresentative_spec c z v, huv]

/-- The aggregate node map is tautologically injective. -/
theorem atomicAggregateNode_injective
    {I : Type*} (c z : I → ℂ) :
    Function.Injective (atomicAggregateNode c z) :=
  Subtype.coe_injective

/-- Every aggregate coefficient is nonzero by construction. -/
theorem atomicAggregateCoefficient_ne_zero
    {I : Type*} (c z : I → ℂ) :
    ∀ u, atomicAggregateCoefficient c z u ≠ 0 :=
  fun u => u.property

/-- Cofinite convergence of the raw nodes descends to the intrinsic aggregate support. -/
theorem tendsto_atomicAggregateNode_cofinite_zero
    {I : Type*} {c z : I → ℂ}
    (hz0 : Tendsto z cofinite (nhds 0)) :
    Tendsto (atomicAggregateNode c z) cofinite (nhds 0) := by
  have hrep : Tendsto (atomicAggregateRepresentative c z) cofinite cofinite :=
    (atomicAggregateRepresentative_injective c z).tendsto_cofinite
  have hcomp := hz0.comp hrep
  simpa only [Function.comp_def, atomicAggregateRepresentative_spec] using hcomp

/-- Cofinal vanishing of the transverse defect descends to the intrinsic aggregate support. -/
theorem tendsto_atomicAggregateNode_transverseDefect_cofinite_zero
    {I : Type*} {c z : I → ℂ}
    (htrans : Tendsto (fun i => HTGeometry.transverseDefect (z i))
      cofinite (nhds 0)) :
    Tendsto
      (fun u : AtomicAggregateSupport c z =>
        HTGeometry.transverseDefect (atomicAggregateNode c z u))
      cofinite (nhds 0) := by
  have hrep : Tendsto (atomicAggregateRepresentative c z) cofinite cofinite :=
    (atomicAggregateRepresentative_injective c z).tendsto_cofinite
  have hcomp := htrans.comp hrep
  simpa only [Function.comp_def, atomicAggregateRepresentative_spec] using hcomp

/-- A uniform norm bound descends to aggregate nodes. -/
theorem norm_atomicAggregateNode_le
    {I : Type*} {c z : I → ℂ} {M : ℝ}
    (hbound : ∀ i, ‖z i‖ ≤ M) :
    ∀ u, ‖atomicAggregateNode c z u‖ ≤ M := by
  intro u
  rw [← atomicAggregateRepresentative_spec c z u]
  exact hbound _

/-- Nonnegative-real orientation descends to aggregate nodes. -/
theorem atomicAggregateNode_re_nonneg_of_im_eq_zero
    {I : Type*} {c z : I → ℂ}
    (hreal : ∀ i, (z i).im = 0 → 0 ≤ (z i).re) :
    ∀ u, (atomicAggregateNode c z u).im = 0 →
      0 ≤ (atomicAggregateNode c z u).re := by
  intro u hu
  rw [← atomicAggregateRepresentative_spec c z u] at hu ⊢
  exact hreal _ hu

/-- Exact fibrewise regrouping of every bounded atomic power moment. -/
theorem atomicPowerMoment_eq_atomicAggregatePowerMoment
    {I : Type*} {c z : I → ℂ} (hc : Summable c)
    {M : ℝ} (hbound : ∀ i, ‖z i‖ ≤ M) (n : ℕ) :
    atomicPowerMoment c z n =
      atomicPowerMoment
        (atomicAggregateCoefficient c z) (atomicAggregateNode c z) n := by
  let F : I → ℂ := fun i => c i * z i ^ n
  have hF : Summable F := summable_atomicPowerMoment_term hc hbound n
  have hfiber := hF.hasSum.tsum_fiberwise z
  have hinner (u : ℂ) :
      (∑' i : z ⁻¹' {u}, F i.1) = atomicAggregateWeight c z u * u ^ n := by
    rw [atomicAggregateWeight]
    calc
      (∑' i : z ⁻¹' {u}, F i.1) =
          ∑' i : z ⁻¹' {u}, c i.1 * u ^ n := by
        apply tsum_congr
        intro i
        have hi : z i.1 = u := by simpa using i.property
        dsimp only [F]
        rw [hi]
      _ = (∑' i : z ⁻¹' {u}, c i.1) * u ^ n := tsum_mul_right
  have hsupp : Function.support (fun u : ℂ =>
      atomicAggregateWeight c z u * u ^ n) ⊆
      {u : ℂ | atomicAggregateWeight c z u ≠ 0} := by
    intro u hu
    intro hzero
    apply hu
    simp only [Function.mem_support]
    rw [hzero, zero_mul]
  rw [atomicPowerMoment, atomicPowerMoment, ← hfiber.tsum_eq]
  calc
    (∑' u : ℂ, ∑' i : z ⁻¹' {u}, F i.1) =
        ∑' u : ℂ, atomicAggregateWeight c z u * u ^ n :=
      tsum_congr hinner
    _ = ∑' u : {u : ℂ | atomicAggregateWeight c z u ≠ 0},
        atomicAggregateWeight c z u.1 * u.1 ^ n :=
      (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' u : AtomicAggregateSupport c z,
        atomicAggregateCoefficient c z u * atomicAggregateNode c z u ^ n := by
      rfl

/-- Positive zeroth moment forces the intrinsic aggregate support to be nonempty. -/
theorem nonempty_atomicAggregateSupport_of_positive_real_moment
    {I : Type*} {c z : I → ℂ} {m : ℕ → ℝ}
    (hc : Summable c) {M : ℝ} (hbound : ∀ i, ‖z i‖ ≤ M)
    (hmoment : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    (hm0 : 0 < m 0) :
    Nonempty (AtomicAggregateSupport c z) := by
  by_contra hne
  haveI : IsEmpty (AtomicAggregateSupport c z) := not_nonempty_iff.mp hne
  have hzero : atomicPowerMoment
      (atomicAggregateCoefficient c z) (atomicAggregateNode c z) 0 = 0 := by
    simp [atomicPowerMoment]
  have hcast : (m 0 : ℂ) = 0 := by
    rw [hmoment 0, atomicPowerMoment_eq_atomicAggregatePowerMoment hc hbound 0,
      hzero]
  exact (Complex.ofReal_ne_zero.mpr hm0.ne') hcast

/-- **Aggregate-source tomography.**  Arbitrary repeated and zero raw fibres are quotiented out
before selection.  The resulting nonzero aggregate source satisfies the complete tomography law,
so injectivity and pointwise nonvanishing are intrinsic conclusions rather than raw hypotheses. -/
theorem scaleCovariantBernsteinAbel_tomography_of_aggregate
    {I : Type*} (c z : I → ℂ) (m : ℕ → ℝ)
    (hc : Summable c)
    (hz0 : Tendsto z cofinite (nhds 0))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ i, ‖z i‖ ≤ M)
    (hreal : ∀ i, (z i).im = 0 → 0 ≤ (z i).re)
    (hmoment : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    (hm0 : 0 < m 0) :
    ScaleCovariantBernsteinAbelTomographyLaw
      (atomicAggregateCoefficient c z) (atomicAggregateNode c z) m M := by
  classical
  letI : Nonempty (AtomicAggregateSupport c z) :=
    nonempty_atomicAggregateSupport_of_positive_real_moment
      hc hbound hmoment hm0
  apply scaleCovariantBernsteinAbel_tomography
  · exact summable_atomicAggregateCoefficient hc
  · exact tendsto_atomicAggregateNode_cofinite_zero hz0
  · exact atomicAggregateNode_injective c z
  · exact atomicAggregateCoefficient_ne_zero c z
  · exact hM
  · exact norm_atomicAggregateNode_le hbound
  · exact atomicAggregateNode_re_nonneg_of_im_eq_zero hreal
  · intro n
    exact (hmoment n).trans
      (atomicPowerMoment_eq_atomicAggregatePowerMoment hc hbound n)
  · exact hm0

end

end RHTower
