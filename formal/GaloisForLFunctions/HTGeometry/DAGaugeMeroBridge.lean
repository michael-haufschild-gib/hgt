/-
The entire gauge-flat facet datum is a meromorphic one.

`DAGaugeFlatFacetRealization` carries entire carriers and an entire differentially algebraic matrix
gauge; `MeroGaugeFacetRealization` carries the same data inside the global meromorphic differential
field, with differential algebraicity taken over the rational coordinate field.  Both layers prove
the facet-codimension law, independently.

They are not independent.  The jet bridge realizes an entire function as an element of
`meroField univ`, matches the two differential-algebraicity notions in both directions, and
intertwines translation of the argument with `addTranslationMeroEquiv`.  Realizing a matrix of
entire functions entrywise therefore turns an entire gauge-flat datum into a meromorphic one, and
the entire curvature law becomes the meromorphic law read on the image.

* `meroMatrixOfEntire`, `meroVecOfEntire` — entrywise realization, with the product, unit,
  constant, matrix-vector and translation laws;
* `DAGaugeFlatFacetRealization.toMeroGaugeFacetRealization` — the transport;
* `no_daGaugeFlatFacetRealization_of_two_omitted_of_mero`,
  `daGaugeFlat_facetComplementRankOne_of_mero` — the entire curvature law, obtained from the
  meromorphic one rather than through the gauged carrier.
-/
import GaloisForLFunctions.HTGeometry.MeroGaugeCurvatureNecessity
import GaloisForLFunctions.HTGeometry.DAGaugeCurvatureNecessity
import GaloisForLFunctions.HTGeometry.BesselOrderMeromorphic
import GaloisForLFunctions.HTGeometry.AnalyticMeroPolynomialEval

open Finset Set

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- An entire function is analytic on a neighbourhood of every point of the plane. -/
theorem analyticOnNhd_univ_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
  hf.differentiableOn.analyticOnNhd isOpen_univ

/-- Entrywise realization of an entire matrix field. -/
def meroMatrixOfEntire {m : ℕ} (M : ℂ → Matrix (Fin m) (Fin m) ℂ)
    (hM : ∀ i j, Differentiable ℂ (fun z => M z i j)) :
    Matrix (Fin m) (Fin m) (meroField (Set.univ : Set ℂ)) :=
  fun i j =>
    analyticMeroElement (fun z => M z i j) (analyticOnNhd_univ_of_differentiable (hM i j))

/-- Entrywise realization of an entire vector field. -/
def meroVecOfEntire {m : ℕ} (v : ℂ → (Fin m → ℂ))
    (hv : ∀ i, Differentiable ℂ (fun z => v z i)) :
    Fin m → meroField (Set.univ : Set ℂ) :=
  fun i => analyticMeroElement (fun z => v z i) (analyticOnNhd_univ_of_differentiable (hv i))

theorem meroMatrixOfEntire_congr {m : ℕ} {M N : ℂ → Matrix (Fin m) (Fin m) ℂ}
    (hM : ∀ i j, Differentiable ℂ (fun z => M z i j))
    (hN : ∀ i j, Differentiable ℂ (fun z => N z i j)) (h : M = N) :
    meroMatrixOfEntire M hM = meroMatrixOfEntire N hN := by
  subst h; rfl

theorem meroVecOfEntire_congr {m : ℕ} {v w : ℂ → (Fin m → ℂ)}
    (hv : ∀ i, Differentiable ℂ (fun z => v z i))
    (hw : ∀ i, Differentiable ℂ (fun z => w z i)) (h : v = w) :
    meroVecOfEntire v hv = meroVecOfEntire w hw := by
  subst h; rfl

theorem differentiable_matrix_mul_apply {m : ℕ} {M N : ℂ → Matrix (Fin m) (Fin m) ℂ}
    (hM : ∀ i j, Differentiable ℂ (fun z => M z i j))
    (hN : ∀ i j, Differentiable ℂ (fun z => N z i j)) (i j : Fin m) :
    Differentiable ℂ (fun z => (M z * N z) i j) := by
  have hfun : (fun z => (M z * N z) i j) = fun z => ∑ k, M z i k * N z k j := by
    funext z
    simp [Matrix.mul_apply]
  rw [hfun]
  exact fun z => DifferentiableAt.fun_sum fun k _ => ((hM i k) z).mul ((hN k j) z)

theorem differentiable_mulVec_apply {m : ℕ} {M : ℂ → Matrix (Fin m) (Fin m) ℂ}
    {v : ℂ → (Fin m → ℂ)}
    (hM : ∀ i j, Differentiable ℂ (fun z => M z i j))
    (hv : ∀ i, Differentiable ℂ (fun z => v z i)) (i : Fin m) :
    Differentiable ℂ (fun z => (M z).mulVec (v z) i) := by
  have hfun : (fun z => (M z).mulVec (v z) i) = fun z => ∑ k, M z i k * v z k := by
    funext z
    simp [Matrix.mulVec, dotProduct]
  rw [hfun]
  exact fun z => DifferentiableAt.fun_sum fun k _ => ((hM i k) z).mul ((hv k) z)

theorem meroMatrixOfEntire_mul {m : ℕ} (M N : ℂ → Matrix (Fin m) (Fin m) ℂ)
    (hM : ∀ i j, Differentiable ℂ (fun z => M z i j))
    (hN : ∀ i j, Differentiable ℂ (fun z => N z i j)) :
    meroMatrixOfEntire (fun z => M z * N z) (differentiable_matrix_mul_apply hM hN)
      = meroMatrixOfEntire M hM * meroMatrixOfEntire N hN := by
  funext i j
  have hfun : (fun z => (M z * N z) i j) = fun z => ∑ k, M z i k * N z k j := by
    funext z
    simp [Matrix.mul_apply]
  have hsum : AnalyticOnNhd ℂ (fun z => ∑ k, M z i k * N z k j) (Set.univ : Set ℂ) :=
    analyticOnNhd_univ_of_differentiable
      (fun z => DifferentiableAt.fun_sum fun k _ => ((hM i k) z).mul ((hN k j) z))
  show analyticMeroElement (fun z => (M z * N z) i j) _ = _
  calc analyticMeroElement (fun z => (M z * N z) i j)
        (analyticOnNhd_univ_of_differentiable (differentiable_matrix_mul_apply hM hN i j))
      = analyticMeroElement (fun z => ∑ k, M z i k * N z k j) hsum :=
        analyticMeroElement_congr _ _ hfun
    _ = ∑ k, analyticMeroElement (fun z => M z i k * N z k j)
          (analyticOnNhd_univ_of_differentiable ((hM i k).mul (hN k j))) :=
        analyticMeroElement_finsetSum Finset.univ _ _ hsum
    _ = ∑ k, analyticMeroElement (fun z => M z i k)
            (analyticOnNhd_univ_of_differentiable (hM i k)) *
          analyticMeroElement (fun z => N z k j)
            (analyticOnNhd_univ_of_differentiable (hN k j)) :=
        Finset.sum_congr rfl fun k _ => analyticMeroElement_mul _ _
    _ = (meroMatrixOfEntire M hM * meroMatrixOfEntire N hN) i j := by
        simp [Matrix.mul_apply, meroMatrixOfEntire]

theorem meroVecOfEntire_mulVec {m : ℕ} (M : ℂ → Matrix (Fin m) (Fin m) ℂ)
    (v : ℂ → (Fin m → ℂ))
    (hM : ∀ i j, Differentiable ℂ (fun z => M z i j))
    (hv : ∀ i, Differentiable ℂ (fun z => v z i)) :
    meroVecOfEntire (fun z => (M z).mulVec (v z)) (differentiable_mulVec_apply hM hv)
      = (meroMatrixOfEntire M hM).mulVec (meroVecOfEntire v hv) := by
  funext i
  have hfun : (fun z => (M z).mulVec (v z) i) = fun z => ∑ k, M z i k * v z k := by
    funext z
    simp [Matrix.mulVec, dotProduct]
  have hsum : AnalyticOnNhd ℂ (fun z => ∑ k, M z i k * v z k) (Set.univ : Set ℂ) :=
    analyticOnNhd_univ_of_differentiable
      (fun z => DifferentiableAt.fun_sum fun k _ => ((hM i k) z).mul ((hv k) z))
  show analyticMeroElement (fun z => (M z).mulVec (v z) i) _ = _
  calc analyticMeroElement (fun z => (M z).mulVec (v z) i)
        (analyticOnNhd_univ_of_differentiable (differentiable_mulVec_apply hM hv i))
      = analyticMeroElement (fun z => ∑ k, M z i k * v z k) hsum :=
        analyticMeroElement_congr _ _ hfun
    _ = ∑ k, analyticMeroElement (fun z => M z i k * v z k)
          (analyticOnNhd_univ_of_differentiable ((hM i k).mul (hv k))) :=
        analyticMeroElement_finsetSum Finset.univ _ _ hsum
    _ = ∑ k, analyticMeroElement (fun z => M z i k)
            (analyticOnNhd_univ_of_differentiable (hM i k)) *
          analyticMeroElement (fun z => v z k)
            (analyticOnNhd_univ_of_differentiable (hv k)) :=
        Finset.sum_congr rfl fun k _ => analyticMeroElement_mul _ _
    _ = (meroMatrixOfEntire M hM).mulVec (meroVecOfEntire v hv) i := by
        simp [Matrix.mulVec, meroMatrixOfEntire, meroVecOfEntire, dotProduct]

theorem meroMatrixOfEntire_one {m : ℕ}
    (h1 : ∀ i j, Differentiable ℂ (fun _ : ℂ => (1 : Matrix (Fin m) (Fin m) ℂ) i j)) :
    meroMatrixOfEntire (fun _ : ℂ => (1 : Matrix (Fin m) (Fin m) ℂ)) h1 = 1 := by
  funext i j
  show analyticMeroElement (fun _ : ℂ => (1 : Matrix (Fin m) (Fin m) ℂ) i j) _ = _
  by_cases hij : i = j
  · subst hij
    have hval : (fun _ : ℂ => (1 : Matrix (Fin m) (Fin m) ℂ) i i) = fun _ : ℂ => (1 : ℂ) := by
      funext _
      simp
    rw [analyticMeroElement_congr _ analyticOnNhd_const hval, analyticMeroElement_const, map_one]
    simp
  · have hval : (fun _ : ℂ => (1 : Matrix (Fin m) (Fin m) ℂ) i j) = fun _ : ℂ => (0 : ℂ) := by
      funext _
      simp [hij]
    rw [analyticMeroElement_congr _ analyticOnNhd_const hval, analyticMeroElement_zero]
    simp [hij]

theorem meroMatrixOfEntire_const {m : ℕ} (C : Matrix (Fin m) (Fin m) ℂ)
    (hC : ∀ i j, Differentiable ℂ (fun _ : ℂ => C i j)) :
    meroMatrixOfEntire (fun _ : ℂ => C) hC
      = C.map (algebraMap ℂ (meroField (Set.univ : Set ℂ))) := by
  funext i j
  show analyticMeroElement (fun _ : ℂ => C i j) _ = _
  rw [analyticMeroElement_congr _ analyticOnNhd_const rfl, analyticMeroElement_const]
  rfl

theorem addTranslationMeroEquiv_meroVecOfEntire {m : ℕ} (q : ℂ) (v : ℂ → (Fin m → ℂ))
    (hv : ∀ i, Differentiable ℂ (fun z => v z i)) (i : Fin m) :
    addTranslationMeroEquiv q (meroVecOfEntire v hv i) =
      meroVecOfEntire (fun z => v (z + q))
        (fun i => (hv i).comp (differentiable_id.add_const q)) i :=
  addTranslationMeroEquiv_analyticMeroElement q _

theorem map_addTranslationMeroEquiv_meroMatrixOfEntire {m : ℕ} (q : ℂ)
    (M : ℂ → Matrix (Fin m) (Fin m) ℂ) (hM : ∀ i j, Differentiable ℂ (fun z => M z i j)) :
    (meroMatrixOfEntire M hM).map (addTranslationMeroEquiv q) =
      meroMatrixOfEntire (fun z => M (z + q))
        (fun i j => (hM i j).comp (differentiable_id.add_const q)) := by
  funext i j
  show addTranslationMeroEquiv q (analyticMeroElement (fun z => M z i j) _) = _
  exact addTranslationMeroEquiv_analyticMeroElement q _

variable {α : Type*} [DecidableEq α]

open scoped Classical in
/-- **An entire gauge-flat facet datum is a meromorphic one.** -/
def DAGaugeFlatFacetRealization.toMeroGaugeFacetRealization {m : ℕ} {V : Finset α}
    {facets : Set (Finset α)} (R : DAGaugeFlatFacetRealization m V facets) :
    MeroGaugeFacetRealization m V facets where
  ω := R.ω
  indep := R.indep
  carrier := fun F =>
    if h : F ∈ facets then meroVecOfEntire (R.carrier F) (R.carrier_entire F h) else 0
  gauge := fun F =>
    if h : F ∈ facets then meroMatrixOfEntire (R.gauge F) (R.gauge_entire F h) else 0
  gaugeInv := fun F =>
    if h : F ∈ facets then meroMatrixOfEntire (R.gaugeInv F) (R.gaugeInv_entire F h) else 0
  gauge_differentialAlgebraic := by
    intro F hF i j
    simp only [dif_pos hF]
    exact differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic _
      (R.gauge_differentiallyAlgebraic F hF i j)
  gaugeInv_mul_gauge := by
    intro F hF
    simp only [dif_pos hF]
    rw [← meroMatrixOfEntire_mul (R.gaugeInv F) (R.gauge F)
      (R.gaugeInv_entire F hF) (R.gauge_entire F hF)]
    have hfun : (fun z => R.gaugeInv F z * R.gauge F z)
        = fun _ : ℂ => (1 : Matrix (Fin m) (Fin m) ℂ) := funext (R.gaugeInv_mul_gauge F hF)
    rw [meroMatrixOfEntire_congr (N := fun _ : ℂ => (1 : Matrix (Fin m) (Fin m) ℂ)) _
      (fun _ _ => differentiable_const _) hfun, meroMatrixOfEntire_one]
  gauge_mul_gaugeInv := by
    intro F hF
    simp only [dif_pos hF]
    rw [← meroMatrixOfEntire_mul (R.gauge F) (R.gaugeInv F)
      (R.gauge_entire F hF) (R.gaugeInv_entire F hF)]
    have hfun : (fun z => R.gauge F z * R.gaugeInv F z)
        = fun _ : ℂ => (1 : Matrix (Fin m) (Fin m) ℂ) := funext (R.gauge_mul_gaugeInv F hF)
    rw [meroMatrixOfEntire_congr (N := fun _ : ℂ => (1 : Matrix (Fin m) (Fin m) ℂ)) _
      (fun _ _ => differentiable_const _) hfun, meroMatrixOfEntire_one]
  carrier_monodromy := by
    intro F hF v hv
    obtain ⟨C, hC⟩ := R.carrier_monodromy F hF v hv
    refine ⟨C, fun i => ?_⟩
    simp only [dif_pos hF]
    have hgshift : ∀ i j, Differentiable ℂ (fun z => R.gauge F (z + R.ω v) i j) :=
      fun i j => (R.gauge_entire F hF i j).comp (differentiable_id.add_const (R.ω v))
    have hCd : ∀ i j : Fin m, Differentiable ℂ (fun _ : ℂ => C i j) :=
      fun _ _ => differentiable_const _
    have hprod1 : ∀ i j, Differentiable ℂ (fun z => (R.gauge F (z + R.ω v) * C) i j) :=
      differentiable_matrix_mul_apply hgshift hCd
    have hprod2 : ∀ i j,
        Differentiable ℂ (fun z => (R.gauge F (z + R.ω v) * C * R.gaugeInv F z) i j) :=
      differentiable_matrix_mul_apply hprod1 (R.gaugeInv_entire F hF)
    have hfun : (fun z => R.carrier F (z + R.ω v))
        = fun z => (R.gauge F (z + R.ω v) * C * R.gaugeInv F z).mulVec (R.carrier F z) :=
      funext hC
    have hmat : meroMatrixOfEntire (fun z => R.gauge F (z + R.ω v) * C * R.gaugeInv F z) hprod2
        = (meroMatrixOfEntire (R.gauge F) (R.gauge_entire F hF)).map
              (addTranslationMeroEquiv (R.ω v))
            * C.map (algebraMap ℂ (meroField (Set.univ : Set ℂ)))
            * meroMatrixOfEntire (R.gaugeInv F) (R.gaugeInv_entire F hF) := by
      rw [map_addTranslationMeroEquiv_meroMatrixOfEntire, ← meroMatrixOfEntire_const C hCd,
        ← meroMatrixOfEntire_mul _ _ hgshift hCd,
        ← meroMatrixOfEntire_mul _ _ hprod1 (R.gaugeInv_entire F hF)]
    rw [addTranslationMeroEquiv_meroVecOfEntire,
      meroVecOfEntire_congr _
        (differentiable_mulVec_apply hprod2 (R.carrier_entire F hF)) hfun,
      meroVecOfEntire_mulVec _ _ hprod2 (R.carrier_entire F hF), hmat]
  carrier_hypertranscendental := by
    intro F hF
    obtain ⟨i, hi⟩ := R.carrier_hypertranscendental F hF
    refine ⟨i, ?_⟩
    simp only [dif_pos hF]
    intro hDA
    exact hi (differentiallyAlgebraic_of_differentialAlgebraicOver_analyticMeroElement _ hDA)

/-- **Two omitted vertices are impossible for an entire gauge-flat datum**, obtained from the
meromorphic law through the realization instead of through the gauged carrier. -/
theorem no_daGaugeFlatFacetRealization_of_two_omitted_of_mero {m : ℕ} {V : Finset α}
    {facets : Set (Finset α)} (R : DAGaugeFlatFacetRealization m V facets) {F : Finset α}
    (hF : F ∈ facets) {u v : α} (hu : u ∈ V \ F) (hv : v ∈ V \ F) (huv : u ≠ v) : False :=
  no_meroGaugeFacetRealization_of_two_omitted R.toMeroGaugeFacetRealization hF hu hv huv

/-- **The entire gauge curvature law is the meromorphic one read on the realization.** -/
theorem daGaugeFlat_facetComplementRankOne_of_mero {m : ℕ} {V : Finset α}
    {facets : Set (Finset α)} (R : DAGaugeFlatFacetRealization m V facets)
    (hsub : ∀ F ∈ facets, F ⊆ V) : FacetComplementRankOne V facets :=
  meroGauge_facetComplementRankOne R.toMeroGaugeFacetRealization hsub

end

end GaloisForLFunctions.HTGeometry
