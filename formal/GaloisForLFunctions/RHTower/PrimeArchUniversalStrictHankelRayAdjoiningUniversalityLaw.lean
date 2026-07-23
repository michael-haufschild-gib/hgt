import GaloisForLFunctions.RHTower.PrimeArchBlackHoleReciprocalSpectralConeUniversalityLaw
import GaloisForLFunctions.HTGeometry.GeometricKallenLehmannResponse

/-!
# Universal adjoining law for the prime--archimedean strict Hankel cone

Any unconditional strict Hankel moment ray may be adjoined to the existing black-hole,
reciprocal-continuum, and prime--archimedean cone without changing its exact RH classifier.  This
single closure law subsumes arbitrary further positive spectral rays, rather than adding them one
at a time.
-/

namespace RHTower

noncomputable section

/-- Adjoin an arbitrary fourth moment ray to the three-source physical cone. -/
def primeArchAdjoinedStrictHankelMixedClock
    (q : ℕ → ℝ) (scaleLog : ℂ) (alpha beta gamma delta : ℝ) (n : ℕ) : ℝ :=
  primeArchBlackHoleReciprocalMixedClock scaleLog alpha beta gamma n + delta * q n

/-- Hankel formation commutes with adjoining the fourth ray. -/
theorem momentHankelMatrix_primeArchAdjoinedStrictHankelMixedClock
    (q : ℕ → ℝ) (scaleLog : ℂ) (alpha beta gamma delta : ℝ) (n : ℕ) :
    HTGeometry.momentHankelMatrix
        (primeArchAdjoinedStrictHankelMixedClock
          q scaleLog alpha beta gamma delta) n =
      HTGeometry.momentHankelMatrix
          (primeArchBlackHoleReciprocalMixedClock scaleLog alpha beta gamma) n +
        delta • HTGeometry.momentHankelMatrix q n := by
  ext i j
  simp [HTGeometry.momentHankelMatrix, primeArchAdjoinedStrictHankelMixedClock]

/-- Under RH, adjoining any universally strict Hankel ray preserves strictness of every nonzero
nonnegative mixture. -/
theorem primeArchAdjoinedStrictHankelMixedClock_posDef_of_riemannHypothesis
    (hRH : RiemannHypothesis) (q : ℕ → ℝ)
    (hq : ∀ n : ℕ, (HTGeometry.momentHankelMatrix q n).PosDef)
    (scaleLog : ℂ) {alpha beta gamma delta : ℝ}
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hdelta : 0 ≤ delta) (hnonzero : 0 < alpha + beta + gamma + delta)
    (n : ℕ) :
    (HTGeometry.momentHankelMatrix
      (primeArchAdjoinedStrictHankelMixedClock
        q scaleLog alpha beta gamma delta) n).PosDef := by
  rw [momentHankelMatrix_primeArchAdjoinedStrictHankelMixedClock]
  have hbaseNonneg : 0 ≤ alpha + beta + gamma := by linarith
  by_cases hbasePos : 0 < alpha + beta + gamma
  · exact
      (primeArchBlackHoleReciprocalMixedClock_hankel_posDef_of_riemannHypothesis
        hRH scaleLog halpha hbeta hgamma hbasePos n).add_posSemidef
          ((hq n).posSemidef.smul hdelta)
  · have hbaseZero : alpha + beta + gamma = 0 :=
      le_antisymm (le_of_not_gt hbasePos) hbaseNonneg
    have halphaZero : alpha = 0 := by linarith
    have hbetaZero : beta = 0 := by linarith
    have hgammaZero : gamma = 0 := by linarith
    have hdeltaPos : 0 < delta := by linarith
    simpa [momentHankelMatrix_primeArchBlackHoleReciprocalMixedClock,
      halphaZero, hbetaZero, hgammaZero] using (hq n).smul hdeltaPos

/-- **Universal strict-Hankel-ray adjoining law.**  For every moment ray already strict at all
finite depths, RH is equivalent to strict positivity of every nonzero nonnegative mixture after
adjoining that ray to the black-hole/reciprocal/prime--archimedean cone. -/
theorem riemannHypothesis_iff_primeArch_adjoin_any_strictHankelRay
    (q : ℕ → ℝ) (hq : ∀ n : ℕ, (HTGeometry.momentHankelMatrix q n).PosDef) :
    RiemannHypothesis ↔
      ∀ (scaleLog : ℂ) (alpha beta gamma delta : ℝ),
        0 ≤ alpha → 0 ≤ beta → 0 ≤ gamma → 0 ≤ delta →
          0 < alpha + beta + gamma + delta →
            ∀ n : ℕ,
              (HTGeometry.momentHankelMatrix
                (primeArchAdjoinedStrictHankelMixedClock
                  q scaleLog alpha beta gamma delta) n).PosDef := by
  constructor
  · intro hRH scaleLog alpha beta gamma delta halpha hbeta hgamma hdelta hnonzero n
    exact primeArchAdjoinedStrictHankelMixedClock_posDef_of_riemannHypothesis
      hRH q hq scaleLog halpha hbeta hgamma hdelta hnonzero n
  · intro hcone
    apply riemannHypothesis_iff_primeArchBlackHoleReciprocal_spectralCone_posDef.mpr
    intro scaleLog alpha beta gamma halpha hbeta hgamma hnonzero n
    have h := hcone scaleLog alpha beta gamma 0
      halpha hbeta hgamma (by norm_num) (by simpa) n
    simpa [momentHankelMatrix_primeArchAdjoinedStrictHankelMixedClock] using h

/-- Geometric Källén--Lehmann moments supply a concrete self-similar ray satisfying the universal
strictness premise. -/
theorem momentHankelMatrix_geometricKallenLehmannMoment_posDef
    {a b : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (hb₀ : 0 < b) (hb₁ : b < 1) (n : ℕ) :
    (HTGeometry.momentHankelMatrix
      (HTGeometry.geometricKallenLehmannMoment a b) n).PosDef := by
  have hraw := HTGeometry.discreteMomentHankel_posDef
    (HTGeometry.geometricKallenLehmannWeight a)
    (HTGeometry.geometricKallenLehmannNode b)
    (fun k => HTGeometry.geometricKallenLehmannWeight_nonneg ha₀.le ha₁.le k)
    (fun k => HTGeometry.summable_geometricKallenLehmannWeight_mul_node_abs_pow
      ha₀.le ha₁ hb₀.le hb₁.le k)
    (HTGeometry.geometricKallenLehmann_infiniteSupport ha₀ ha₁ hb₀ hb₁)
    n
  simpa only [← HTGeometry.geometricKallenLehmannMoment_eq_tsum
    ha₀.le ha₁ hb₀.le hb₁.le] using hraw

/-- Concrete self-similar Källén--Lehmann specialization of the universal adjoining law. -/
theorem riemannHypothesis_iff_primeArch_adjoin_geometricKallenLehmannRay
    {a b : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (hb₀ : 0 < b) (hb₁ : b < 1) :
    RiemannHypothesis ↔
      ∀ (scaleLog : ℂ) (alpha beta gamma delta : ℝ),
        0 ≤ alpha → 0 ≤ beta → 0 ≤ gamma → 0 ≤ delta →
          0 < alpha + beta + gamma + delta →
            ∀ n : ℕ,
              (HTGeometry.momentHankelMatrix
                (primeArchAdjoinedStrictHankelMixedClock
                  (HTGeometry.geometricKallenLehmannMoment a b)
                  scaleLog alpha beta gamma delta) n).PosDef :=
  riemannHypothesis_iff_primeArch_adjoin_any_strictHankelRay
    (HTGeometry.geometricKallenLehmannMoment a b)
    (momentHankelMatrix_geometricKallenLehmannMoment_posDef ha₀ ha₁ hb₀ hb₁)

end

end RHTower
