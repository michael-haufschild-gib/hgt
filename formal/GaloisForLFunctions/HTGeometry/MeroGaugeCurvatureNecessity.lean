import GaloisForLFunctions.HTGeometry.MeroFieldShiftStableSpace
import GaloisForLFunctions.HTGeometry.MatrixFacetCodimension

/-!
# The gauge curvature law for meromorphic gauges

The finite-state facet-codimension law survives an internal transport that is only gauge-flat with
a **meromorphic** differentially algebraic gauge — in particular a rational one, which is what the
shift case of the Schaefke--Singer reduction produces.  Everything happens inside the global
meromorphic differential field, where differential algebraicity is closed under the field
operations, so no entirety and no nonvanishing hypothesis is needed anywhere.

* `differentialAlgebraicOver_finset_sum`, `differentialAlgebraicOver_mulVec` — the field-level ring
  closure in the shapes the gauge computation needs;
* **`differentialAlgebraicOver_of_gauged_constant_monodromy`** — conjugating a gauged constant
  transport by its gauge produces a constant transport, whose components are differentially
  algebraic by the vector two-shift law; multiplying back by the gauge keeps them so;
* **`meroGauge_facetComplementRankOne`** — hence the facet-codimension law for a meromorphic
  gauge-flat finite-state datum: no facet omits two ambient vertices.
-/

open Finset Set

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

/-! ## Field-level closure in matrix shape -/

/-- Differential algebraicity is closed under finite sums. -/
theorem differentialAlgebraicOver_finset_sum {F E ι : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {s : Finset ι} {f : ι → E} (hf : ∀ i ∈ s, DifferentialAlgebraicOver F (f i)) :
    DifferentialAlgebraicOver F (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using differentialAlgebraicOver_algebraMap (F := F) (E := E) 0
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact differentialAlgebraicOver_add (hf i (by simp))
        (ih fun j hj => hf j (by simp [hj]))

/-- A matrix-vector product of differentially algebraic entries is differentially algebraic. -/
theorem differentialAlgebraicOver_mulVec {m : ℕ}
    {M : Matrix (Fin m) (Fin m) (meroField (Set.univ : Set ℂ))}
    {v : Fin m → meroField (Set.univ : Set ℂ)}
    (hM : ∀ i j, DifferentialAlgebraicOver (RatFunc ℂ) (M i j))
    (hv : ∀ j, DifferentialAlgebraicOver (RatFunc ℂ) (v j)) (i : Fin m) :
    DifferentialAlgebraicOver (RatFunc ℂ) (M.mulVec v i) := by
  have hfun : M.mulVec v i = ∑ j, M i j * v j := by
    simp [Matrix.mulVec, dotProduct]
  rw [hfun]
  exact differentialAlgebraicOver_finset_sum fun j _ =>
    differentialAlgebraicOver_mul (hM i j) (hv j)

/-! ## Conjugating away a differentially algebraic gauge -/

set_option synthInstance.maxHeartbeats 400000 in
/-- **A gauged constant transport has differentially algebraic components.**  If two
`ℚ`-independent translations reproduce a vector of meromorphic germs up to
`B(z + ω) C B(z)⁻¹` with constant `C` and a differentially algebraic invertible gauge `B`, then
every component is differentially algebraic over the rational coordinate field. -/
theorem differentialAlgebraicOver_of_gauged_constant_monodromy {α β : ℂ} {m : ℕ}
    (hindep : LinearIndependent ℚ ![α, β])
    (v : Fin m → meroField (Set.univ : Set ℂ))
    (B Binv : Matrix (Fin m) (Fin m) (meroField (Set.univ : Set ℂ)))
    (hBDA : ∀ i j, DifferentialAlgebraicOver (RatFunc ℂ) (B i j))
    (hinv : Binv * B = 1) (hinv' : B * Binv = 1)
    (Cα Cβ : Matrix (Fin m) (Fin m) ℂ)
    (hα : ∀ i, addTranslationMeroEquiv α (v i) =
      ((B.map (addTranslationMeroEquiv α) *
        Cα.map (algebraMap ℂ (meroField (Set.univ : Set ℂ))) * Binv).mulVec v) i)
    (hβ : ∀ i, addTranslationMeroEquiv β (v i) =
      ((B.map (addTranslationMeroEquiv β) *
        Cβ.map (algebraMap ℂ (meroField (Set.univ : Set ℂ))) * Binv).mulVec v) i)
    (i : Fin m) : DifferentialAlgebraicOver (RatFunc ℂ) (v i) := by
  classical
  set g : Fin m → meroField (Set.univ : Set ℂ) := Binv.mulVec v with hg
  have hconj : ∀ (q : ℂ) (C : Matrix (Fin m) (Fin m) ℂ),
      (∀ k, addTranslationMeroEquiv q (v k) =
        ((B.map (addTranslationMeroEquiv q) *
          C.map (algebraMap ℂ (meroField (Set.univ : Set ℂ))) * Binv).mulVec v) k) →
      ∀ k, addTranslationMeroEquiv q (g k) =
        ∑ j, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (C k j) * g j := by
    intro q C hC k
    have hstep : addTranslationMeroEquiv q (g k) =
        ((Binv.map (addTranslationMeroEquiv q)).mulVec
          (fun j => addTranslationMeroEquiv q (v j))) k := by
      rw [hg]
      simpa [Function.comp_def] using
        RingHom.map_mulVec ((addTranslationMeroEquiv q).toRingHom) Binv v k
    have hvfun : (fun j => addTranslationMeroEquiv q (v j)) =
        (B.map (addTranslationMeroEquiv q) *
          C.map (algebraMap ℂ (meroField (Set.univ : Set ℂ))) * Binv).mulVec v := by
      funext j
      exact hC j
    rw [hstep, hvfun, Matrix.mulVec_mulVec]
    have hmat : Binv.map (addTranslationMeroEquiv q) *
        (B.map (addTranslationMeroEquiv q) *
          C.map (algebraMap ℂ (meroField (Set.univ : Set ℂ))) * Binv) =
        C.map (algebraMap ℂ (meroField (Set.univ : Set ℂ))) * Binv := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, hinv]
      rw [Matrix.map_one _ (map_zero (addTranslationMeroEquiv q))
        (map_one (addTranslationMeroEquiv q)), Matrix.one_mul]
    rw [hmat, ← Matrix.mulVec_mulVec]
    show (C.map (algebraMap ℂ (meroField (Set.univ : Set ℂ)))).mulVec g k = _
    simp [Matrix.mulVec, dotProduct]
  have hgDA : ∀ k, DifferentialAlgebraicOver (RatFunc ℂ) (g k) :=
    differentialAlgebraicOver_of_constant_matrix_monodromy hindep g Cα Cβ
      (hconj α Cα hα) (hconj β Cβ hβ)
  have hrecover : B.mulVec g = v := by
    rw [hg, Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
  have : v i = (B.mulVec g) i := by rw [hrecover]
  rw [this]
  exact differentialAlgebraicOver_mulVec hBDA hgDA i

/-! ## The facet datum -/

variable {α : Type*} [DecidableEq α]

/-- **A meromorphic gauge-flat facet datum.**  `ℚ`-independent translation steps together with, for
every facet, a vector of meromorphic germs which each omitted translation reproduces up to the
conjugated constant transport `B(z + ω) C B(z)⁻¹` with a differentially algebraic invertible gauge
`B`, some component of which is hypertranscendental over the rational coordinate field. -/
structure MeroGaugeFacetRealization (m : ℕ) (V : Finset α) (facets : Set (Finset α)) where
  /-- The translation steps attached to the vertices. -/
  ω : α → ℂ
  /-- The steps are `ℚ`-linearly independent. -/
  indep : LinearIndependent ℚ ω
  /-- The facet carriers, as vectors of meromorphic germs. -/
  carrier : Finset α → (Fin m → meroField (Set.univ : Set ℂ))
  /-- The internal gauge. -/
  gauge : Finset α → Matrix (Fin m) (Fin m) (meroField (Set.univ : Set ℂ))
  /-- The inverse gauge. -/
  gaugeInv : Finset α → Matrix (Fin m) (Fin m) (meroField (Set.univ : Set ℂ))
  /-- The gauge is differentially algebraic. -/
  gauge_differentialAlgebraic : ∀ F ∈ facets, ∀ i j,
    DifferentialAlgebraicOver (RatFunc ℂ) (gauge F i j)
  /-- The inverse gauge inverts the gauge on the left. -/
  gaugeInv_mul_gauge : ∀ F ∈ facets, gaugeInv F * gauge F = 1
  /-- The inverse gauge inverts the gauge on the right. -/
  gauge_mul_gaugeInv : ∀ F ∈ facets, gauge F * gaugeInv F = 1
  /-- Each omitted translation reproduces the carrier up to the gauged constant transport. -/
  carrier_monodromy : ∀ F ∈ facets, ∀ v ∈ V \ F,
    ∃ C : Matrix (Fin m) (Fin m) ℂ, ∀ i,
      addTranslationMeroEquiv (ω v) (carrier F i) =
        ((gauge F).map (addTranslationMeroEquiv (ω v)) *
          C.map (algebraMap ℂ (meroField (Set.univ : Set ℂ))) * gaugeInv F).mulVec
          (carrier F) i
  /-- Some component of each carrier is hypertranscendental. -/
  carrier_hypertranscendental : ∀ F ∈ facets, ∃ i,
    HypertranscendentalOver (RatFunc ℂ) (carrier F i)

/-- **Two omitted vertices are impossible for a meromorphic gauge-flat datum.** -/
theorem no_meroGaugeFacetRealization_of_two_omitted {m : ℕ} {V : Finset α}
    {facets : Set (Finset α)} (R : MeroGaugeFacetRealization m V facets) {F : Finset α}
    (hF : F ∈ facets) {u v : α} (hu : u ∈ V \ F) (hv : v ∈ V \ F) (huv : u ≠ v) : False := by
  obtain ⟨Cu, hCu⟩ := R.carrier_monodromy F hF u hu
  obtain ⟨Cv, hCv⟩ := R.carrier_monodromy F hF v hv
  obtain ⟨i, hi⟩ := R.carrier_hypertranscendental F hF
  have hindep : LinearIndependent ℚ ![R.ω u, R.ω v] := by
    rw [← comp_cons_two]
    exact R.indep.comp _ (injective_cons_two huv)
  exact hi (differentialAlgebraicOver_of_gauged_constant_monodromy hindep (R.carrier F)
    (R.gauge F) (R.gaugeInv F) (R.gauge_differentialAlgebraic F hF)
    (R.gaugeInv_mul_gauge F hF) (R.gauge_mul_gaugeInv F hF) Cu Cv hCu hCv i)

/-- **The meromorphic gauge curvature law.**  Every facet of a meromorphic gauge-flat finite-state
datum omits at most one ambient vertex.  Contrapositive: a nonpure geometry forces an internal
cocycle that is not gauge-equivalent to a constant representation by *any* differentially algebraic
meromorphic gauge — in particular not by a rational one. -/
theorem meroGauge_facetComplementRankOne {m : ℕ} {V : Finset α} {facets : Set (Finset α)}
    (R : MeroGaugeFacetRealization m V facets) (hsub : ∀ F ∈ facets, F ⊆ V) :
    FacetComplementRankOne V facets := by
  intro F hF
  refine ⟨hsub F hF, ?_⟩
  by_contra hlt
  have h2 : 2 ≤ (V \ F).card := by omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h2
  exact no_meroGaugeFacetRealization_of_two_omitted R hF hu hv huv

end

end GaloisForLFunctions.HTGeometry
