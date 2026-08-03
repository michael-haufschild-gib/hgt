import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Lagrange
import GaloisForLFunctions.RHTower.InvariantSubalgebraCrossedProduct

/-!
# Endpoint-holomorphic Real-corona smoothness

This file isolates the analytic condition needed for an upper/lower CRT idempotent to lie in an
endpoint-holomorphic subalgebra.  A representative must be holomorphic on one connected
neighborhood containing the compactifying endpoints and take the constant values `1` and `0` on
the two divisor sectors.

The classification is exact.  Finite separated sectors admit an explicit Lagrange-polynomial
representative.  If either infinite sector accumulates at an endpoint inside the holomorphic
domain, the identity theorem makes the requested two values incompatible.  Thus, under the
two endpoint-accumulation hypotheses, endpoint-holomorphic representability is equivalent to
finiteness of both sectors.
-/

open Set

namespace GaloisForLFunctions.RHTower

/-- An upper/lower corona separator represented by a function holomorphic through the chosen
endpoint neighborhood. -/
def HasEndpointHolomorphicCoronaRepresentative
    (U upper lower : Set ℂ) : Prop :=
  ∃ h : ℂ → ℂ,
    AnalyticOnNhd ℂ h U ∧
    (∀ z ∈ upper, h z = 1) ∧
    (∀ z ∈ lower, h z = 0)

/-- Natural endpoint-holomorphic coefficient algebra on a divisor `Z`: functions on `Z` which
are restrictions of holomorphic functions on `U`. -/
def endpointHolomorphicSubalgebra (U Z : Set ℂ) : Subalgebra ℂ (Z → ℂ) where
  carrier := {f | ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h U ∧
    ∀ z : Z, h (z : ℂ) = f z}
  zero_mem' := ⟨fun _ => 0, analyticOnNhd_const, by simp⟩
  add_mem' := by
    rintro f g ⟨hf, hfA, hfeq⟩ ⟨hg, hgA, hgeq⟩
    refine ⟨fun z => hf z + hg z, hfA.add hgA, ?_⟩
    intro z
    simp [hfeq z, hgeq z]
  one_mem' := ⟨fun _ => 1, analyticOnNhd_const, by simp⟩
  mul_mem' := by
    rintro f g ⟨hf, hfA, hfeq⟩ ⟨hg, hgA, hgeq⟩
    refine ⟨fun z => hf z * hg z, hfA.mul hgA, ?_⟩
    intro z
    simp [hfeq z, hgeq z]
  algebraMap_mem' := by
    intro c
    refine ⟨fun _ => c, analyticOnNhd_const, ?_⟩
    intro z
    rfl

/-- The endpoint-holomorphic coefficient algebra is dense in the full divisor function algebra for
pointwise convergence.  The proof is stronger than approximation: every basic finite-coordinate
condition is met exactly by a Lagrange polynomial. -/
theorem endpointHolomorphicSubalgebra_dense (U Z : Set ℂ) :
    Dense (endpointHolomorphicSubalgebra U Z : Set (Z → ℂ)) := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro f
  rw [mem_closure_iff]
  intro o ho hfo
  classical
  have hnhds : o ∈ nhds f := ho.mem_nhds hfo
  rw [nhds_pi, Filter.mem_pi'] at hnhds
  rcases hnhds with ⟨I, t, ht, hto⟩
  let p : Polynomial ℂ := Lagrange.interpolate I (fun z : Z => (z : ℂ)) f
  let g : Z → ℂ := fun z => p.eval (z : ℂ)
  have hinj : Set.InjOn (fun z : Z => (z : ℂ)) (I : Set Z) := by
    intro a _ b _ hab
    exact Subtype.ext hab
  have hmatch : ∀ z ∈ I, g z = f z := by
    intro z hz
    simpa [g, p] using Lagrange.eval_interpolate_at_node f hinj hz
  have hgmem : g ∈ endpointHolomorphicSubalgebra U Z := by
    refine ⟨fun z => p.eval z,
      (AnalyticOnNhd.eval_polynomial p).mono (Set.subset_univ U), ?_⟩
    intro z
    rfl
  refine ⟨g, hto ?_, hgmem⟩
  intro z hz
  rw [hmatch z hz]
  exact mem_of_mem_nhds (ht z)

/-- Upper-sector characteristic function on the complete two-sector divisor. -/
noncomputable def endpointRealCoronaIdempotent
    (upper lower : Set ℂ) : (upper ∪ lower : Set ℂ) → ℂ :=
  fun z => @ite ℂ ((z : ℂ) ∈ upper) (Classical.propDecidable _) 1 0

/-- The upper-sector characteristic function is an idempotent in the full divisor function
algebra, without any finiteness or regularity hypothesis. -/
theorem endpointRealCoronaIdempotent_isIdempotent (upper lower : Set ℂ) :
    IsIdempotentElem (endpointRealCoronaIdempotent upper lower) := by
  classical
  funext z
  simp only [endpointRealCoronaIdempotent, Pi.mul_apply]
  split_ifs <;> norm_num

/-- Membership of the Real-corona idempotent in the natural endpoint-holomorphic coefficient
algebra is exactly endpoint-holomorphic representability of its upper/lower values. -/
theorem endpointRealCoronaIdempotent_mem_iff
    {U upper lower : Set ℂ} (hdisj : Disjoint upper lower) :
    endpointRealCoronaIdempotent upper lower ∈
        endpointHolomorphicSubalgebra U (upper ∪ lower) ↔
      HasEndpointHolomorphicCoronaRepresentative U upper lower := by
  classical
  constructor
  · rintro ⟨h, hA, heq⟩
    refine ⟨h, hA, ?_, ?_⟩
    · intro z hz
      have hzcarrier : z ∈ upper ∪ lower := Or.inl hz
      have heval := heq ⟨z, hzcarrier⟩
      simpa [endpointRealCoronaIdempotent, hz] using heval
    · intro z hz
      have hzcarrier : z ∈ upper ∪ lower := Or.inr hz
      have hnot : z ∉ upper := fun hzu => Set.disjoint_left.1 hdisj hzu hz
      have heval := heq ⟨z, hzcarrier⟩
      simpa [endpointRealCoronaIdempotent, hnot] using heval
  · rintro ⟨h, hA, hUpper, hLower⟩
    refine ⟨h, hA, ?_⟩
    intro z
    rcases z.property with hz | hz
    · simp [endpointRealCoronaIdempotent, hz, hUpper (z : ℂ) hz]
    · have hnot : (z : ℂ) ∉ upper :=
        fun hzu => Set.disjoint_left.1 hdisj hzu hz
      simp [endpointRealCoronaIdempotent, hnot, hLower (z : ℂ) hz]

/-- Accumulation of the `1` sector at an interior holomorphic endpoint forces the representative
to be identically `1`, contradicting any point of the `0` sector. -/
theorem no_endpoint_holomorphic_rep_of_upper_accumulates
    {U upper lower : Set ℂ} {z0 y : ℂ}
    (hU : IsPreconnected U) (hz0 : z0 ∈ U)
    (hacc : z0 ∈ closure (upper \ {z0}))
    (hyU : y ∈ U) (hylower : y ∈ lower) :
    ¬HasEndpointHolomorphicCoronaRepresentative U upper lower := by
  rintro ⟨h, hhan, hu, hl⟩
  have hacc' : z0 ∈ closure ({z | h z = (1 : ℂ)} \ {z0}) := by
    apply closure_mono ?_ hacc
    intro z hz
    exact ⟨hu z hz.1, hz.2⟩
  have heq := hhan.eqOn_of_preconnected_of_mem_closure
    analyticOnNhd_const hU hz0 hacc'
  have hone : h y = 1 := heq hyU
  have hzero : h y = 0 := hl y hylower
  norm_num [hzero] at hone

/-- Accumulation of the `0` sector at an interior holomorphic endpoint forces the representative
to be identically `0`, contradicting any point of the `1` sector. -/
theorem no_endpoint_holomorphic_rep_of_lower_accumulates
    {U upper lower : Set ℂ} {z0 y : ℂ}
    (hU : IsPreconnected U) (hz0 : z0 ∈ U)
    (hacc : z0 ∈ closure (lower \ {z0}))
    (hyU : y ∈ U) (hyupper : y ∈ upper) :
    ¬HasEndpointHolomorphicCoronaRepresentative U upper lower := by
  rintro ⟨h, hhan, hu, hl⟩
  have hacc' : z0 ∈ closure ({z | h z = (0 : ℂ)} \ {z0}) := by
    apply closure_mono ?_ hacc
    intro z hz
    exact ⟨hl z hz.1, hz.2⟩
  have heq := hhan.eqOn_of_preconnected_of_mem_closure
    analyticOnNhd_const hU hz0 hacc'
  have hzero : h y = 0 := heq hyU
  have hone : h y = 1 := hu y hyupper
  norm_num [hone] at hzero

/-- Two finite disjoint sectors admit an entire separator, explicitly supplied by Lagrange
interpolation. -/
theorem exists_entire_corona_rep_of_finite
    {upper lower : Set ℂ} (hu : upper.Finite) (hl : lower.Finite)
    (hdisj : Disjoint upper lower) :
    HasEndpointHolomorphicCoronaRepresentative Set.univ upper lower := by
  classical
  let s : Finset ℂ := hu.toFinset ∪ hl.toFinset
  let r : ℂ → ℂ := fun z => if z ∈ upper then 1 else 0
  let p : Polynomial ℂ := Lagrange.interpolate s id r
  refine ⟨fun z => p.eval z, ?_, ?_, ?_⟩
  · exact AnalyticOnNhd.eval_polynomial p
  · intro z hz
    have hzs : z ∈ s := by simp [s, Set.Finite.mem_toFinset, hz]
    have hinj : Set.InjOn id (s : Set ℂ) := Set.injOn_id _
    simpa [p, r, hz] using Lagrange.eval_interpolate_at_node r hinj hzs
  · intro z hz
    have hzs : z ∈ s := by simp [s, Set.Finite.mem_toFinset, hz]
    have hnot : z ∉ upper := by
      intro hzu
      exact Set.disjoint_left.1 hdisj hzu hz
    have hinj : Set.InjOn id (s : Set ℂ) := Set.injOn_id _
    simpa [p, r, hnot] using Lagrange.eval_interpolate_at_node r hinj hzs

/-- The entire finite-sector separator restricts to every endpoint neighborhood. -/
theorem exists_endpoint_holomorphic_corona_rep_of_finite
    {U upper lower : Set ℂ} (hu : upper.Finite) (hl : lower.Finite)
    (hdisj : Disjoint upper lower) :
    HasEndpointHolomorphicCoronaRepresentative U upper lower := by
  rcases exists_entire_corona_rep_of_finite hu hl hdisj with ⟨h, hhan, hhU, hhL⟩
  exact ⟨h, hhan.mono (Set.subset_univ U), hhU, hhL⟩

/-- Exact endpoint-holomorphic smoothness classification for a two-sector divisor.

The hypotheses say that every infinite sector accumulates at its compactifying endpoint inside
the connected holomorphic domain.  Under these intrinsic endpoint hypotheses, a corona separator
extends holomorphically through the endpoints exactly when both sectors are finite. -/
theorem endpoint_holomorphic_corona_iff_finite
    {U upper lower : Set ℂ} {zUpper zLower : ℂ}
    (hU : IsPreconnected U)
    (hupperU : upper ⊆ U) (hlowerU : lower ⊆ U)
    (hupper_nonempty : upper.Nonempty) (hlower_nonempty : lower.Nonempty)
    (hzUpper : zUpper ∈ U) (hzLower : zLower ∈ U)
    (hupper_acc : upper.Infinite → zUpper ∈ closure (upper \ {zUpper}))
    (hlower_acc : lower.Infinite → zLower ∈ closure (lower \ {zLower}))
    (hdisj : Disjoint upper lower) :
    HasEndpointHolomorphicCoronaRepresentative U upper lower ↔
      upper.Finite ∧ lower.Finite := by
  constructor
  · intro hrep
    constructor
    · by_contra hu
      rcases hlower_nonempty with ⟨y, hy⟩
      exact (no_endpoint_holomorphic_rep_of_upper_accumulates hU hzUpper (hupper_acc hu)
        (hlowerU hy) hy) hrep
    · by_contra hl
      rcases hupper_nonempty with ⟨y, hy⟩
      exact (no_endpoint_holomorphic_rep_of_lower_accumulates hU hzLower (hlower_acc hl)
        (hupperU hy) hy) hrep
  · rintro ⟨hu, hl⟩
    exact exists_endpoint_holomorphic_corona_rep_of_finite hu hl hdisj

/-- P3 classification in coefficient-algebra form: under the standard two-ended divisor
accumulation hypotheses, the Real-corona idempotent belongs to the natural endpoint-holomorphic
subalgebra exactly for finite completed divisors. -/
theorem endpointRealCoronaIdempotent_mem_iff_finite
    {U upper lower : Set ℂ} {zUpper zLower : ℂ}
    (hU : IsPreconnected U)
    (hupperU : upper ⊆ U) (hlowerU : lower ⊆ U)
    (hupper_nonempty : upper.Nonempty) (hlower_nonempty : lower.Nonempty)
    (hzUpper : zUpper ∈ U) (hzLower : zLower ∈ U)
    (hupper_acc : upper.Infinite → zUpper ∈ closure (upper \ {zUpper}))
    (hlower_acc : lower.Infinite → zLower ∈ closure (lower \ {zLower}))
    (hdisj : Disjoint upper lower) :
    endpointRealCoronaIdempotent upper lower ∈
        endpointHolomorphicSubalgebra U (upper ∪ lower) ↔
      upper.Finite ∧ lower.Finite := by
  rw [endpointRealCoronaIdempotent_mem_iff hdisj]
  exact endpoint_holomorphic_corona_iff_finite hU hupperU hlowerU
    hupper_nonempty hlower_nonempty hzUpper hzLower hupper_acc hlower_acc hdisj

section CrossedProduct

variable {G : Type*} [Monoid G] {U Z : Set ℂ}
  [MulSemiringAction G (Z → ℂ)] [SMulCommClass G ℂ (Z → ℂ)]

/-- The endpoint-holomorphic algebra, bundled as invariant coefficient data for a crossed product.
The sole input is the exact invariance condition required by the skew action. -/
def endpointHolomorphicInvariantSubalgebra
    (hInvariant : ∀ (g : G) {f : Z → ℂ},
      f ∈ endpointHolomorphicSubalgebra U Z →
        g • f ∈ endpointHolomorphicSubalgebra U Z) :
    InvariantSubalgebra G (Z → ℂ) where
  S := endpointHolomorphicSubalgebra U Z
  smul_mem := hInvariant

/-- Full crossed-product version of P3.  Once the endpoint-holomorphic coefficient algebra is
invariant under the chosen action, the degree-zero Real-corona idempotent lies in the image of the
smooth skew crossed product exactly for finite upper and lower divisor sectors. -/
theorem endpointRealCoronaDegreeZero_mem_crossedProductRange_iff_finite
    {U upper lower : Set ℂ} {zUpper zLower : ℂ}
    [MulSemiringAction G (((upper ∪ lower : Set ℂ) → ℂ))]
    [SMulCommClass G ℂ (((upper ∪ lower : Set ℂ) → ℂ))]
    (hInvariant : ∀ (g : G) {f : (upper ∪ lower : Set ℂ) → ℂ},
      f ∈ endpointHolomorphicSubalgebra U (upper ∪ lower) →
        g • f ∈ endpointHolomorphicSubalgebra U (upper ∪ lower))
    (hU : IsPreconnected U)
    (hupperU : upper ⊆ U) (hlowerU : lower ⊆ U)
    (hupper_nonempty : upper.Nonempty) (hlower_nonempty : lower.Nonempty)
    (hzUpper : zUpper ∈ U) (hzLower : zLower ∈ U)
    (hupper_acc : upper.Infinite → zUpper ∈ closure (upper \ {zUpper}))
    (hlower_acc : lower.Infinite → zLower ∈ closure (lower \ {zLower}))
    (hdisj : Disjoint upper lower) :
    SkewMonoidAlgebra.single (1 : G) (endpointRealCoronaIdempotent upper lower) ∈
        Set.range
          (endpointHolomorphicInvariantSubalgebra hInvariant).crossedProductInclusion ↔
      upper.Finite ∧ lower.Finite := by
  rw [InvariantSubalgebra.degreeZero_mem_crossedProductRange_iff
    (endpointHolomorphicInvariantSubalgebra hInvariant)
    (endpointRealCoronaIdempotent upper lower)]
  exact endpointRealCoronaIdempotent_mem_iff_finite hU hupperU hlowerU
    hupper_nonempty hlower_nonempty hzUpper hzLower hupper_acc hlower_acc hdisj

end CrossedProduct

end GaloisForLFunctions.RHTower
