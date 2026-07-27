import GaloisForLFunctions.HTGeometry.MatrixFacetCodimension
import GaloisForLFunctions.HTGeometry.AnalyticJetFieldBridge

/-!
# A differentially algebraic gauge cannot enlarge a facet complement

A finite-state facet datum whose internal transport is not constant but only *`DA`-gauge-flat* —
each omitted translation reproduces the carrier up to `B(z + ω) C B(z)⁻¹` with a constant `C` and a
differentially algebraic entire gauge `B` — still obeys the facet-codimension law.  Conjugating by
the gauge turns the transport into the constant `C`, and the gauge is invisible to differential
algebraicity because the differentially algebraic entire functions form a ring
(`differentiallyAlgebraic_mul`, `differentiallyAlgebraic_add`): a hypertranscendental component
cannot be manufactured by a differentially algebraic change of internal coordinates.

Contrapositive: a one-variable finite-state system with a nonpure Stanley--Reisner geometry has an
internal translation cocycle that is **not** `DA`-gauge-equivalent to a constant representation.

* `differentiallyAlgebraic_finsetSum` — the ring closure in finite-sum form;
* **`no_daGaugeFlatFacetRealization_of_two_omitted`**;
* **`daGaugeFlat_facetComplementRankOne`**.
-/

open Finset Set

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [DecidableEq α]

/-- Entirety and differential algebraicity are preserved by finite sums. -/
theorem differentiallyAlgebraic_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hd : ∀ i ∈ s, Differentiable ℂ (f i))
    (hDA : ∀ i ∈ s, DifferentiallyAlgebraic (f i)) :
    DifferentiallyAlgebraic (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using differentiallyAlgebraic_const 0
  | insert a s ha ih =>
      have hda : Differentiable ℂ (f a) := hd a (Finset.mem_insert_self a s)
      have hsum : Differentiable ℂ (fun z => ∑ i ∈ s, f i z) := by
        have hs : Differentiable ℂ (∑ i ∈ s, f i) :=
          Differentiable.sum fun i hi => hd i (Finset.mem_insert_of_mem hi)
        have heq : (∑ i ∈ s, f i) = fun z => ∑ i ∈ s, f i z := by
          funext z
          simp [Finset.sum_apply]
        rwa [heq] at hs
      have hrest : DifferentiallyAlgebraic (fun z => ∑ i ∈ s, f i z) :=
        ih (fun i hi => hd i (Finset.mem_insert_of_mem hi))
          (fun i hi => hDA i (Finset.mem_insert_of_mem hi))
      have hfun : (fun z => ∑ i ∈ insert a s, f i z) =
          fun z => f a z + ∑ i ∈ s, f i z := by
        funext z
        rw [Finset.sum_insert ha]
      rw [hfun]
      exact differentiallyAlgebraic_add (hda.differentiableOn.analyticOnNhd isOpen_univ)
        (hsum.differentiableOn.analyticOnNhd isOpen_univ)
        (hDA a (Finset.mem_insert_self a s)) hrest

/-- A matrix-vector product of entire differentially algebraic data is differentially algebraic. -/
theorem differentiallyAlgebraic_mulVec {m : ℕ} {M : ℂ → Matrix (Fin m) (Fin m) ℂ}
    {v : ℂ → (Fin m → ℂ)}
    (hMd : ∀ i j, Differentiable ℂ (fun z => M z i j))
    (hvd : ∀ j, Differentiable ℂ (fun z => v z j))
    (hM : ∀ i j, DifferentiallyAlgebraic (fun z => M z i j))
    (hv : ∀ j, DifferentiallyAlgebraic (fun z => v z j)) (i : Fin m) :
    DifferentiallyAlgebraic (fun z => (M z).mulVec (v z) i) := by
  have hfun : (fun z => (M z).mulVec (v z) i) = fun z => ∑ j, M z i j * v z j := by
    funext z
    simp [Matrix.mulVec, dotProduct]
  rw [hfun]
  refine differentiallyAlgebraic_finsetSum _ _ (fun j _ => (hMd i j).mul (hvd j))
    (fun j _ => ?_)
  exact differentiallyAlgebraic_mul ((hMd i j).differentiableOn.analyticOnNhd isOpen_univ)
    ((hvd j).differentiableOn.analyticOnNhd isOpen_univ) (hM i j) (hv j)

/-- **A `DA`-gauge-flat facet datum.**  `ℚ`-independent translation steps together with, for every
facet, an entire `ℂ^m`-valued carrier which each omitted translation reproduces up to the
conjugated constant transport `B(z + ω) C B(z)⁻¹`, where `B` is an entire differentially algebraic
invertible gauge, and some component of which is hypertranscendental. -/
structure DAGaugeFlatFacetRealization (m : ℕ) (V : Finset α) (facets : Set (Finset α)) where
  /-- The translation steps attached to the vertices. -/
  ω : α → ℂ
  /-- The steps are `ℚ`-linearly independent. -/
  indep : LinearIndependent ℚ ω
  /-- The facet carriers. -/
  carrier : Finset α → (ℂ → (Fin m → ℂ))
  /-- Every component of every carrier is entire. -/
  carrier_entire : ∀ F ∈ facets, ∀ i, Differentiable ℂ (fun z => carrier F z i)
  /-- The internal gauge. -/
  gauge : Finset α → (ℂ → Matrix (Fin m) (Fin m) ℂ)
  /-- The inverse gauge. -/
  gaugeInv : Finset α → (ℂ → Matrix (Fin m) (Fin m) ℂ)
  /-- The gauge is entire. -/
  gauge_entire : ∀ F ∈ facets, ∀ i j, Differentiable ℂ (fun z => gauge F z i j)
  /-- The inverse gauge is entire. -/
  gaugeInv_entire : ∀ F ∈ facets, ∀ i j, Differentiable ℂ (fun z => gaugeInv F z i j)
  /-- The gauge is differentially algebraic. -/
  gauge_differentiallyAlgebraic : ∀ F ∈ facets, ∀ i j,
    DifferentiallyAlgebraic (fun z => gauge F z i j)
  /-- The inverse gauge inverts the gauge on the left. -/
  gaugeInv_mul_gauge : ∀ F ∈ facets, ∀ z, gaugeInv F z * gauge F z = 1
  /-- The inverse gauge inverts the gauge on the right. -/
  gauge_mul_gaugeInv : ∀ F ∈ facets, ∀ z, gauge F z * gaugeInv F z = 1
  /-- Each omitted translation reproduces the carrier up to the gauged constant transport. -/
  carrier_monodromy : ∀ F ∈ facets, ∀ v ∈ V \ F,
    ∃ C : Matrix (Fin m) (Fin m) ℂ, ∀ z,
      carrier F (z + ω v) = (gauge F (z + ω v) * C * gaugeInv F z).mulVec (carrier F z)
  /-- Some component of each carrier is hypertranscendental. -/
  carrier_hypertranscendental : ∀ F ∈ facets, ∃ i, Hypertranscendental (fun z => carrier F z i)

namespace DAGaugeFlatFacetRealization

variable {m : ℕ} {V : Finset α} {facets : Set (Finset α)}

/-- The gauge-transformed carrier. -/
noncomputable def gaugedCarrier (R : DAGaugeFlatFacetRealization m V facets) (F : Finset α) :
    ℂ → (Fin m → ℂ) :=
  fun z => (R.gaugeInv F z).mulVec (R.carrier F z)

theorem gaugedCarrier_entire (R : DAGaugeFlatFacetRealization m V facets) {F : Finset α}
    (hF : F ∈ facets) (i : Fin m) : Differentiable ℂ (fun z => R.gaugedCarrier F z i) := by
  have hfun : (fun z => R.gaugedCarrier F z i) =
      fun z => ∑ j, R.gaugeInv F z i j * R.carrier F z j := by
    funext z
    simp [gaugedCarrier, Matrix.mulVec, dotProduct]
  rw [hfun]
  have hs : Differentiable ℂ
      (∑ j : Fin m, (fun z => R.gaugeInv F z i j * R.carrier F z j)) :=
    Differentiable.sum fun j _ => (R.gaugeInv_entire F hF i j).mul (R.carrier_entire F hF j)
  have heq : (∑ j : Fin m, (fun z => R.gaugeInv F z i j * R.carrier F z j)) =
      fun z => ∑ j, R.gaugeInv F z i j * R.carrier F z j := by
    funext z
    simp [Finset.sum_apply]
  rwa [heq] at hs

/-- The gauge turns the transport into its constant part. -/
theorem gaugedCarrier_monodromy (R : DAGaugeFlatFacetRealization m V facets) {F : Finset α}
    (hF : F ∈ facets) {v : α} (hv : v ∈ V \ F) :
    ∃ C : Matrix (Fin m) (Fin m) ℂ, ∀ z,
      R.gaugedCarrier F (z + R.ω v) = C.mulVec (R.gaugedCarrier F z) := by
  obtain ⟨C, hC⟩ := R.carrier_monodromy F hF v hv
  refine ⟨C, fun z => ?_⟩
  have hstep : R.gaugedCarrier F (z + R.ω v) =
      (R.gaugeInv F (z + R.ω v) * (R.gauge F (z + R.ω v) * C * R.gaugeInv F z)).mulVec
        (R.carrier F z) := by
    rw [gaugedCarrier, hC z, Matrix.mulVec_mulVec]
  rw [hstep]
  have hassoc : R.gaugeInv F (z + R.ω v) * (R.gauge F (z + R.ω v) * C * R.gaugeInv F z) =
      C * R.gaugeInv F z := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, R.gaugeInv_mul_gauge F hF, Matrix.one_mul]
  rw [hassoc, ← Matrix.mulVec_mulVec]
  rfl

/-- **The gauge cannot manufacture hypertranscendence.**  Some component of the gauged carrier is
hypertranscendental, because the original carrier is recovered from the gauged one by a
differentially algebraic matrix. -/
theorem gaugedCarrier_hypertranscendental (R : DAGaugeFlatFacetRealization m V facets)
    {F : Finset α} (hF : F ∈ facets) :
    ∃ i, Hypertranscendental (fun z => R.gaugedCarrier F z i) := by
  classical
  by_contra hcon
  push Not at hcon
  have hgDA : ∀ i, DifferentiallyAlgebraic (fun z => R.gaugedCarrier F z i) := by
    intro i
    exact not_not.mp (hcon i)
  obtain ⟨i, hi⟩ := R.carrier_hypertranscendental F hF
  apply hi
  have hfun : (fun z => R.carrier F z i) =
      fun z => (R.gauge F z).mulVec (R.gaugedCarrier F z) i := by
    funext z
    rw [gaugedCarrier, Matrix.mulVec_mulVec, R.gauge_mul_gaugeInv F hF, Matrix.one_mulVec]
  rw [hfun]
  exact differentiallyAlgebraic_mulVec (R.gauge_entire F hF)
    (R.gaugedCarrier_entire hF) (R.gauge_differentiallyAlgebraic F hF) hgDA i

/-- The gauged datum is an ordinary constant-transport finite-state datum. -/
noncomputable def toMatrixFacetRealization (R : DAGaugeFlatFacetRealization m V facets) :
    MatrixFacetRealization m V facets where
  ω := R.ω
  indep := R.indep
  carrier := R.gaugedCarrier
  carrier_entire := fun _ hF i => R.gaugedCarrier_entire hF i
  carrier_monodromy := fun _ hF _ hv => R.gaugedCarrier_monodromy hF hv
  carrier_hypertranscendental := fun _ hF => R.gaugedCarrier_hypertranscendental hF

end DAGaugeFlatFacetRealization

/-- **Two omitted vertices are impossible for a `DA`-gauge-flat datum.** -/
theorem no_daGaugeFlatFacetRealization_of_two_omitted {m : ℕ} {V : Finset α}
    {facets : Set (Finset α)} (R : DAGaugeFlatFacetRealization m V facets) {F : Finset α}
    (hF : F ∈ facets) {u v : α} (hu : u ∈ V \ F) (hv : v ∈ V \ F) (huv : u ≠ v) : False :=
  no_matrixFacetRealization_of_two_omitted R.toMatrixFacetRealization hF hu hv huv

/-- **The `DA`-gauge curvature law.**  A finite-state facet datum with a differentially algebraic
gauge obeys the facet-codimension law: every facet omits at most one ambient vertex.  Equivalently,
a nonpure geometry forces an internal cocycle that is not `DA`-gauge-equivalent to a constant
representation. -/
theorem daGaugeFlat_facetComplementRankOne {m : ℕ} {V : Finset α} {facets : Set (Finset α)}
    (R : DAGaugeFlatFacetRealization m V facets) (hsub : ∀ F ∈ facets, F ⊆ V) :
    FacetComplementRankOne V facets :=
  matrix_facetComplementRankOne R.toMatrixFacetRealization hsub

end GaloisForLFunctions.HTGeometry
