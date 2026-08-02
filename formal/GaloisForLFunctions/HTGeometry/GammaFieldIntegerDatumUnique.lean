import GaloisForLFunctions.HTGeometry.GammaFieldIntegerDatum

/-!
# Uniqueness of the integer datum of equation (3)

Equation (3) asserts that the integers `k, a, b` and the constant `c` of the projective boundary are
*unique*.  Uniqueness is a consequence of the dominance order alone: two shapes with different data
are comparable, the subordinate one vanishes against the dominant one, and a nonzero residue against
both is impossible.  With the data equal the shapes coincide, so the residues do.

The same then holds for the element itself: two line representatives of one carrier element agree
eventually — their germs are equal, and a germ identity at the upper end holds along every vertical
line — so the datum is an invariant of the element.
-/

open Filter Set Topology Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance gammaUniqDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance gammaUniqIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance gammaUniqDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance gammaUniqComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance gammaUniqRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

/-- Two integer data are equal or one is strictly subordinate to the other. -/
theorem shapeZ_trichotomy (k a b k' a' b' : ℤ) :
    (k = k' ∧ a = a' ∧ b = b')
      ∨ (k' < k ∨ (k = k' ∧ a < a') ∨ (k = k' ∧ a = a' ∧ b < b'))
      ∨ (k < k' ∨ (k' = k ∧ a' < a) ∨ (k' = k ∧ a' = a ∧ b' < b)) := by
  omega

/-- A line representative with a nonzero residue is eventually nonzero, and so is its denominator. -/
theorem eventually_ne_zero_of_datum {σ : ℝ} {φ : ℝ → ℂ} {k a b : ℤ} {c : ℂ} (hc : c ≠ 0)
    (h : Tendsto (fun t : ℝ => φ t / gammaShapeZ σ k a b t) atTop (nhds c)) :
    ∀ᶠ t : ℝ in atTop, φ t ≠ 0 := by
  filter_upwards [h.eventually (eventually_ne_nhds hc)] with t ht
  intro h0
  exact ht (by rw [h0, zero_div])

/-- **The datum of a line function is unique.**  A function cannot have nonzero residues against two
different shapes, and against one shape it has only one residue. -/
theorem gammaShapeZ_datum_unique {σ : ℝ} (hσ : 0 < σ) {φ : ℝ → ℂ} {k a b k' a' b' : ℤ} {c c' : ℂ}
    (hc : c ≠ 0) (hc' : c' ≠ 0)
    (h : Tendsto (fun t : ℝ => φ t / gammaShapeZ σ k a b t) atTop (nhds c))
    (h' : Tendsto (fun t : ℝ => φ t / gammaShapeZ σ k' a' b' t) atTop (nhds c')) :
    k = k' ∧ a = a' ∧ b = b' ∧ c = c' := by
  classical
  -- the shape ratio is the ratio of the two normalized limits
  have hratio : ∀ {p q r p' q' r' : ℤ} {u v : ℂ}, v ≠ 0 →
      Tendsto (fun t : ℝ => φ t / gammaShapeZ σ p q r t) atTop (nhds u) →
      Tendsto (fun t : ℝ => φ t / gammaShapeZ σ p' q' r' t) atTop (nhds v) →
      Tendsto (fun t : ℝ => gammaShapeZ σ p' q' r' t / gammaShapeZ σ p q r t) atTop
        (nhds (u / v)) := by
    intro p q r p' q' r' u v hv hu hvlim
    refine (hu.div hvlim hv).congr' ?_
    filter_upwards [eventually_gammaShapeZ_ne_zero (σ := σ) hσ p q r,
      eventually_gammaShapeZ_ne_zero (σ := σ) hσ p' q' r',
      eventually_ne_zero_of_datum hv hvlim] with t hS hS' hφ
    simp only [Pi.div_apply]
    field_simp
  have hfwd := hratio hc' h h'
  have hbwd := hratio hc h' h
  -- a strictly subordinate shape would force one of the two ratios to vanish
  have hdata : k = k' ∧ a = a' ∧ b = b' := by
    rcases shapeZ_trichotomy k a b k' a' b' with heq | hsub | hsub'
    · exact heq
    · have hzero := tendsto_gammaShapeZ_ratio_zero (σ := σ) hσ hsub
      have := tendsto_nhds_unique hzero hbwd
      exact absurd this.symm (div_ne_zero hc' hc)
    · have hzero := tendsto_gammaShapeZ_ratio_zero (σ := σ) hσ hsub'
      have := tendsto_nhds_unique hzero hfwd
      exact absurd this.symm (div_ne_zero hc hc')
  obtain ⟨hk, ha, hb⟩ := hdata
  refine ⟨hk, ha, hb, ?_⟩
  subst hk; subst ha; subst hb
  exact tendsto_nhds_unique h h'

/-- **Two line representatives of one carrier element agree eventually.**  Their germs are equal at
the upper end, and a germ identity there holds along every vertical line. -/
theorem representsOnLine_eventuallyEq {σ : ℝ} {x : upperEndMeroField} {φ φ' : ℝ → ℂ}
    (hφ : RepresentsOnLine σ x φ) (hφ' : RepresentsOnLine σ x φ')
    (hne : ∀ᶠ t : ℝ in atTop, φ t ≠ 0) (hne' : ∀ᶠ t : ℝ in atTop, φ' t ≠ 0) :
    ∀ᶠ t : ℝ in atTop, φ t = φ' t := by
  classical
  obtain ⟨U, V, G, H, hUg, hVg, hV0, hx, hφeq⟩ := hφ
  obtain ⟨U', V', G', H', hUg', hVg', hV0', hx', hφeq'⟩ := hφ'
  -- the two presentations give the same element, so the cross products agree as germs
  have hcross : algebraMap upperEndAnalyticSubring upperEndMeroField (U * V')
      = algebraMap upperEndAnalyticSubring upperEndMeroField (U' * V) := by
    rw [map_mul, map_mul]
    have := hx.symm.trans hx'
    field_simp at this
    linear_combination this
  have hprod : U * V' = U' * V :=
    IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField hcross
  have hgerm : Germ.coeRingHom upperEndFilter (fun z : ℂ => G z * H' z)
      = Germ.coeRingHom upperEndFilter (fun z : ℂ => G' z * H z) := by
    have h1 : upperEndAnalyticSubring.subtype (U * V')
        = Germ.coeRingHom upperEndFilter (fun z : ℂ => G z * H' z) := by
      rw [map_mul, hUg, hVg', ← map_mul]
      rfl
    have h2 : upperEndAnalyticSubring.subtype (U' * V)
        = Germ.coeRingHom upperEndFilter (fun z : ℂ => G' z * H z) := by
      rw [map_mul, hUg', hVg, ← map_mul]
      rfl
    rw [← h1, ← h2, hprod]
  have hev : ∀ᶠ z : ℂ in upperEndFilter, G z * H' z = G' z * H z := by
    have := Filter.Germ.coe_eq.mp hgerm
    exact this
  have hline := eventually_line_of_upperEnd hev σ
  filter_upwards [hline, hne, hne'] with t ht htne htne'
  -- the denominators cannot vanish where the quotients do not
  have hH : H ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    exact htne (by rw [hφeq t, h0, div_zero])
  have hH' : H' ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    exact htne' (by rw [hφeq' t, h0, div_zero])
  rw [hφeq t, hφeq' t, div_eq_div_iff hH hH']
  linear_combination ht

/-- **Equation (3) is unique.**  The integers `k, a, b` and the constant `c` of the projective
boundary depend only on the carrier element, not on the presentation used to compute them. -/
theorem gammaField_intDatum_unique {σ : ℝ} (hσ : 0 < σ) {x : upperEndMeroField}
    {φ φ' : ℝ → ℂ} {k a b k' a' b' : ℤ} {c c' : ℂ} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (hφ : RepresentsOnLine σ x φ) (hφ' : RepresentsOnLine σ x φ')
    (h : Tendsto (fun t : ℝ => φ t / gammaShapeZ σ k a b t) atTop (nhds c))
    (h' : Tendsto (fun t : ℝ => φ' t / gammaShapeZ σ k' a' b' t) atTop (nhds c')) :
    k = k' ∧ a = a' ∧ b = b' ∧ c = c' := by
  have heq := representsOnLine_eventuallyEq hφ hφ' (eventually_ne_zero_of_datum hc h)
    (eventually_ne_zero_of_datum hc' h')
  refine gammaShapeZ_datum_unique hσ hc hc' h (h'.congr' ?_)
  filter_upwards [heq] with t ht
  rw [ht]

end

end GaloisForLFunctions.HTGeometry
