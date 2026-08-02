import GaloisForLFunctions.HTGeometry.GammaMonomialValuation

/-!
# The boundary datum as a valuation

Equation (3) attaches to every nonzero element of `ℂ(s)⟨Γ⟩` a triple of integers and a nonzero
constant; equation (26) orders the triples.  Packaged as a predicate, the datum exists, is unique,
and is *additive*: the datum of a product is the sum of the triples with the product of the
residues, and inversion negates it.  On `Γ` the triple is `(1, 0, 0)` and on the digamma field its
first component vanishes, so the `Γ`-exponent is the monomial valuation of the card's §1.
-/

open Filter Set Topology Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance gammaDatDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance gammaDatIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance gammaDatDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance gammaDatComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance gammaDatRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance gammaDatRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance gammaDatRatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

/-- `x` has boundary datum `(k, a, b)` with residue `c` on the line through `σ`: some line
representative of `x` is asymptotic to `c·Γ^k·s^a·(log s)^b`. -/
def HasGammaDatum (σ : ℝ) (x : upperEndMeroField) (k a b : ℤ) (c : ℂ) : Prop :=
  c ≠ 0 ∧ ∃ φ : ℝ → ℂ, RepresentsOnLine σ x φ
    ∧ Tendsto (fun t : ℝ => φ t / gammaShapeZ σ k a b t) atTop (nhds c)

/-- **Existence of the datum**: eq. (3) for every nonzero element of the Gamma field. -/
theorem exists_hasGammaDatum {σ : ℝ} (hσ : 0 < σ) {x : upperEndMeroField}
    (hx : x ∈ differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
    (hx0 : x ≠ 0) : ∃ (k a b : ℤ) (c : ℂ), HasGammaDatum σ x k a b c := by
  obtain ⟨k, a, b, φ, c, hc, hrep, hlim⟩ := exists_gammaField_intDatum hσ hx hx0
  exact ⟨k, a, b, c, hc, φ, hrep, hlim⟩

/-- **Uniqueness of the datum**: eq. (3)'s uniqueness clause. -/
theorem hasGammaDatum_unique {σ : ℝ} (hσ : 0 < σ) {x : upperEndMeroField} {k a b k' a' b' : ℤ}
    {c c' : ℂ} (h : HasGammaDatum σ x k a b c) (h' : HasGammaDatum σ x k' a' b' c') :
    k = k' ∧ a = a' ∧ b = b' ∧ c = c' := by
  obtain ⟨hc, φ, hrep, hlim⟩ := h
  obtain ⟨hc', φ', hrep', hlim'⟩ := h'
  exact gammaField_intDatum_unique hσ hc hc' hrep hrep' hlim hlim'

/-- **The datum is additive on products.** -/
theorem HasGammaDatum.mul {σ : ℝ} (hσ : 0 < σ) {x y : upperEndMeroField} {k a b k' a' b' : ℤ}
    {c c' : ℂ} (h : HasGammaDatum σ x k a b c) (h' : HasGammaDatum σ y k' a' b' c') :
    HasGammaDatum σ (x * y) (k + k') (a + a') (b + b') (c * c') := by
  obtain ⟨hc, φ, hrep, hlim⟩ := h
  obtain ⟨hc', φ', hrep', hlim'⟩ := h'
  exact ⟨mul_ne_zero hc hc', fun t => φ t * φ' t, hrep.mul hrep',
    tendsto_datum_mul hσ hlim hlim'⟩

/-- Inversion negates the datum and inverts the residue. -/
theorem HasGammaDatum.inv {σ : ℝ} (hσ : 0 < σ) {x : upperEndMeroField} {k a b : ℤ} {c : ℂ}
    (h : HasGammaDatum σ x k a b c) : HasGammaDatum σ x⁻¹ (-k) (-a) (-b) c⁻¹ := by
  obtain ⟨hc, φ, hrep, hlim⟩ := h
  obtain ⟨U, V, G, H, hUg, hVg, hV0, hxeq, hφ⟩ := hrep
  have hU0 : algebraMap upperEndAnalyticSubring upperEndMeroField U ≠ 0 := by
    intro h0
    have hx0 : x = 0 := by rw [hxeq, h0, zero_div]
    have hne : ∀ᶠ t : ℝ in atTop, φ t ≠ 0 := eventually_ne_zero_of_datum hc hlim
    obtain ⟨t, ht⟩ := hne.exists
    exact ht (by
      have : RepresentsOnLine σ (0 : upperEndMeroField) φ := by
        rw [← hx0]
        exact ⟨U, V, G, H, hUg, hVg, hV0, hxeq, hφ⟩
      obtain ⟨t', ht'⟩ := ((representsOnLine_zero_eventually this).and hne).exists
      exact absurd ht'.1 ht'.2)
  refine ⟨inv_ne_zero hc, fun t => (φ t)⁻¹, ⟨V, U, H, G, hVg, hUg, hU0, ?_, ?_⟩, ?_⟩
  · rw [hxeq, inv_div]
  · intro t
    dsimp only
    rw [hφ t, inv_div]
  · have hinv := hlim.inv₀ hc
    refine hinv.congr' ?_
    filter_upwards [eventually_gammaShapeZ_ne_zero (σ := σ) hσ k a b,
      eventually_gammaShapeZ_ne_zero (σ := σ) hσ (-k) (-a) (-b),
      gammaShapeZ_mul hσ k a b (-k) (-a) (-b)] with t hS hS' hmul
    have hone : gammaShapeZ σ k a b t * gammaShapeZ σ (-k) (-a) (-b) t = 1 := by
      rw [hmul]
      simp [gammaShapeZ]
    have hSinv : gammaShapeZ σ (-k) (-a) (-b) t = (gammaShapeZ σ k a b t)⁻¹ :=
      eq_inv_of_mul_eq_one_right hone
    rw [hSinv, inv_div_inv, inv_div]

/-- The datum of `Γ` is `(1, 0, 0)` with residue `1`. -/
theorem hasGammaDatum_gammaUpperMero {σ : ℝ} (hσ : 0 < σ) :
    HasGammaDatum σ gammaUpperMero 1 0 0 1 :=
  ⟨one_ne_zero, fun t => gammaLine σ t, representsOnLine_gammaUpperMero,
    tendsto_gammaLine_div_gammaShapeZ hσ⟩

/-- An element of the digamma field has datum with `Γ`-exponent zero. -/
theorem exists_hasGammaDatum_digammaField {σ : ℝ} (hσ : 0 < σ) {x : upperEndMeroField}
    (hx : x ∈ differentialAdjoin (RatFunc ℂ) ({digammaMero} : Set upperEndMeroField))
    (hx0 : x ≠ 0) : ∃ (a b : ℤ) (c : ℂ), HasGammaDatum σ x 0 a b c := by
  obtain ⟨a, b, φ, c, hc, hrep, hlim⟩ := exists_digammaField_intDatum hσ hx hx0
  exact ⟨a, b, c, hc, φ, hrep, hlim⟩

/-- **The `Γ`-exponent is a valuation.**  On a product it adds; in particular it is `k` on `Γ^k` and
`0` on every nonzero element of the digamma field. -/
theorem gammaExponent_mul {σ : ℝ} (hσ : 0 < σ) {x y : upperEndMeroField} {k a b k' a' b' : ℤ}
    {c c' : ℂ} (h : HasGammaDatum σ x k a b c) (h' : HasGammaDatum σ y k' a' b' c')
    {K A B : ℤ} {C : ℂ} (hxy : HasGammaDatum σ (x * y) K A B C) :
    K = k + k' ∧ A = a + a' ∧ B = b + b' ∧ C = c * c' :=
  hasGammaDatum_unique hσ hxy (h.mul hσ h')

/-- **The digamma field does not contain `Γ`.**  Its elements have `Γ`-exponent `0`, and `Γ` has
exponent `1`. -/
theorem gammaUpperMero_not_mem_digammaAdjoin :
    gammaUpperMero ∉ differentialAdjoin (RatFunc ℂ) ({digammaMero} : Set upperEndMeroField) := by
  intro hmem
  obtain ⟨a, b, c, hdat⟩ := exists_hasGammaDatum_digammaField (σ := 1) one_pos hmem
    gammaUpperMero_ne_zero
  obtain ⟨hk, -, -, -⟩ := hasGammaDatum_unique (σ := 1) one_pos
    (hasGammaDatum_gammaUpperMero (σ := 1) one_pos) hdat
  exact absurd hk one_ne_zero

/-- **Equation (3) in its displayed form.**  With the datum in hand the element is asymptotic to
`c·Γ^k·s^a·(log s)^b`: the quotient tends to `1`. -/
theorem tendsto_div_gammaShapeZ_mul_residue {σ : ℝ} {x : upperEndMeroField} {k a b : ℤ} {c : ℂ}
    (h : HasGammaDatum σ x k a b c) :
    ∃ φ : ℝ → ℂ, RepresentsOnLine σ x φ
      ∧ Tendsto (fun t : ℝ => φ t / (c * gammaShapeZ σ k a b t)) atTop (nhds 1) := by
  obtain ⟨hc, φ, hrep, hlim⟩ := h
  refine ⟨φ, hrep, ?_⟩
  have hdiv := hlim.div_const c
  rw [div_self hc] at hdiv
  refine hdiv.congr fun t => ?_
  rw [div_div]
  ring_nf

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance gammaDat2Domain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance gammaDat2IntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance gammaDat2Differential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance gammaDat2ComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance gammaDat2RatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance gammaDat2RatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance gammaDat2RatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

/-- **Equation (3), existence and uniqueness together.**  Every nonzero element of `ℂ(s)⟨Γ⟩` has
exactly one boundary datum on a vertical line: unique integers `k, a, b` and a unique nonzero
constant `c`. -/
theorem existsUnique_gammaField_datum {σ : ℝ} (hσ : 0 < σ) {x : upperEndMeroField}
    (hx : x ∈ differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
    (hx0 : x ≠ 0) :
    ∃ d : (ℤ × ℤ × ℤ) × ℂ, HasGammaDatum σ x d.1.1 d.1.2.1 d.1.2.2 d.2
      ∧ ∀ d' : (ℤ × ℤ × ℤ) × ℂ, HasGammaDatum σ x d'.1.1 d'.1.2.1 d'.1.2.2 d'.2 → d' = d := by
  obtain ⟨k, a, b, c, hdat⟩ := exists_hasGammaDatum hσ hx hx0
  refine ⟨((k, a, b), c), hdat, fun d' hd' => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hasGammaDatum_unique hσ hd' hdat
  obtain ⟨⟨k', a', b'⟩, c'⟩ := d'
  simp only at h1 h2 h3 h4
  rw [h1, h2, h3, h4]

/-- **Equation (19), existence and uniqueness in the digamma field.**  Every nonzero element of
`ℂ(s)⟨ψ⟩` has exactly one datum, and its `Γ`-exponent is zero: the algebraic-logarithmic residue
`c·s^a·(log s)^b` of §3. -/
theorem existsUnique_digammaField_datum {σ : ℝ} (hσ : 0 < σ) {x : upperEndMeroField}
    (hx : x ∈ differentialAdjoin (RatFunc ℂ) ({digammaMero} : Set upperEndMeroField))
    (hx0 : x ≠ 0) :
    ∃ d : (ℤ × ℤ) × ℂ, HasGammaDatum σ x 0 d.1.1 d.1.2 d.2
      ∧ ∀ d' : (ℤ × ℤ) × ℂ, HasGammaDatum σ x 0 d'.1.1 d'.1.2 d'.2 → d' = d := by
  obtain ⟨a, b, c, hdat⟩ := exists_hasGammaDatum_digammaField hσ hx hx0
  refine ⟨((a, b), c), hdat, fun d' hd' => ?_⟩
  obtain ⟨-, h2, h3, h4⟩ := hasGammaDatum_unique hσ hd' hdat
  obtain ⟨⟨a', b'⟩, c'⟩ := d'
  simp only at h2 h3 h4
  rw [h2, h3, h4]

end

end GaloisForLFunctions.HTGeometry
