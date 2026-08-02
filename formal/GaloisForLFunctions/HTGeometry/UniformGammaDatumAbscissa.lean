import GaloisForLFunctions.HTGeometry.UniformGammaFieldIntDatum
import GaloisForLFunctions.HTGeometry.GammaDatumValuation

/-!
# The boundary datum does not depend on the vertical line

A tube datum restricts to the datum of every line it covers, and the datum of a line is unique.  Since
every abscissa lies in some tube, the `Γ`-exponent, the argument exponent, the logarithm exponent and
the residue of an element of the Gamma field are the same on every vertical line of the right half
plane: they are invariants of the element, not of the line on which they are read.
-/

open Filter Set Topology Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance uniformAbscissaDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance uniformAbscissaIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance uniformAbscissaDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance uniformAbscissaComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance uniformAbscissaRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

/-- A tube limit is a limit along every vertical line the tube covers. -/
theorem TubeLimit.tendsto_line {M : ℝ} {f : ℝ → ℝ → ℂ} {c : ℂ} (h : TubeLimit M f c) {σ : ℝ}
    (hσ : 0 < σ) (hσM : σ ≤ M) : Tendsto (fun t : ℝ => f σ t) atTop (nhds c) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := h (ε / 2) (by positivity)
  refine ⟨T, fun t ht => ?_⟩
  have hbound := hT σ t hσ hσM ht
  rw [dist_eq_norm]
  linarith

/-- The datum of an element of the Gamma field, read uniformly on the tube `0 < σ ≤ M`. -/
def HasGammaTubeDatum (M : ℝ) (x : upperEndMeroField) (k a b : ℤ) (c : ℂ) : Prop :=
  c ≠ 0 ∧ ∃ φ : ℝ → ℝ → ℂ, RepresentsOnTube x φ
    ∧ TubeLimit M (fun σ t => φ σ t / gammaShapeZ σ k a b t) c

/-- A tube datum is the datum of every line the tube covers. -/
theorem HasGammaTubeDatum.hasGammaDatum {M : ℝ} {x : upperEndMeroField} {k a b : ℤ} {c : ℂ}
    (h : HasGammaTubeDatum M x k a b c) {σ : ℝ} (hσ : 0 < σ) (hσM : σ ≤ M) :
    HasGammaDatum σ x k a b c := by
  obtain ⟨hc, φ, hrep, hlim⟩ := h
  exact ⟨hc, φ σ, representsOnLine_of_representsOnTube hrep σ, hlim.tendsto_line hσ hσM⟩

/-- **Existence of the tube datum**: eq. (3) uniformly on `0 < σ ≤ M`. -/
theorem exists_hasGammaTubeDatum {M : ℝ} (hM : 0 < M) {x : upperEndMeroField}
    (hx : x ∈ differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
    (hx0 : x ≠ 0) : ∃ (k a b : ℤ) (c : ℂ), HasGammaTubeDatum M x k a b c := by
  obtain ⟨k, a, b, φ, c, hc, hrep, hlim⟩ := exists_tubeLimit_gammaField_intDatum hM hx hx0
  exact ⟨k, a, b, c, hc, φ, hrep, hlim⟩

/-- **Uniqueness of the tube datum.** -/
theorem hasGammaTubeDatum_unique {M : ℝ} (hM : 0 < M) {x : upperEndMeroField} {k a b k' a' b' : ℤ}
    {c c' : ℂ} (h : HasGammaTubeDatum M x k a b c) (h' : HasGammaTubeDatum M x k' a' b' c') :
    k = k' ∧ a = a' ∧ b = b' ∧ c = c' :=
  hasGammaDatum_unique hM (h.hasGammaDatum hM le_rfl) (h'.hasGammaDatum hM le_rfl)

/-- **Equation (3) on a tube, existence and uniqueness.**  Every nonzero element of the Gamma field
has exactly one datum valid uniformly for `0 < σ ≤ M`. -/
theorem existsUnique_gammaTube_datum {M : ℝ} (hM : 0 < M) {x : upperEndMeroField}
    (hx : x ∈ differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
    (hx0 : x ≠ 0) :
    ∃ d : (ℤ × ℤ × ℤ) × ℂ, HasGammaTubeDatum M x d.1.1 d.1.2.1 d.1.2.2 d.2
      ∧ ∀ d' : (ℤ × ℤ × ℤ) × ℂ, HasGammaTubeDatum M x d'.1.1 d'.1.2.1 d'.1.2.2 d'.2 → d' = d := by
  obtain ⟨k, a, b, c, hdat⟩ := exists_hasGammaTubeDatum hM hx hx0
  refine ⟨((k, a, b), c), hdat, fun d' hd' => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hasGammaTubeDatum_unique hM hd' hdat
  obtain ⟨⟨k', a', b'⟩, c'⟩ := d'
  simp only at h1 h2 h3 h4
  rw [h1, h2, h3, h4]

/-- **The datum is an invariant of the element, not of the line.**  Two vertical lines of the right
half plane give the same `Γ`-exponent, argument exponent, logarithm exponent and residue. -/
theorem hasGammaDatum_abscissa_independent {x : upperEndMeroField}
    (hx : x ∈ differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
    (hx0 : x ≠ 0) {σ σ' : ℝ} (hσ : 0 < σ) (hσ' : 0 < σ') {k a b k' a' b' : ℤ} {c c' : ℂ}
    (h : HasGammaDatum σ x k a b c) (h' : HasGammaDatum σ' x k' a' b' c') :
    k = k' ∧ a = a' ∧ b = b' ∧ c = c' := by
  have hM : 0 < max σ σ' := lt_of_lt_of_le hσ (le_max_left _ _)
  obtain ⟨k₀, a₀, b₀, c₀, hdat⟩ := exists_hasGammaTubeDatum hM hx hx0
  obtain ⟨h1, h2, h3, h4⟩ :=
    hasGammaDatum_unique hσ h (hdat.hasGammaDatum hσ (le_max_left _ _))
  obtain ⟨h1', h2', h3', h4'⟩ :=
    hasGammaDatum_unique hσ' h' (hdat.hasGammaDatum hσ' (le_max_right _ _))
  exact ⟨h1.trans h1'.symm, h2.trans h2'.symm, h3.trans h3'.symm, h4.trans h4'.symm⟩

end

end GaloisForLFunctions.HTGeometry
