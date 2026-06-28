/-
# Content denominator for composed relations

This file removes the bounded-denominator witness as an hRigid input.  If a minimal relation `P`
admits any clearing identity `(C e) * Q = P * S`, Gauss descent over `FractionRing (ℂ[X])` shows that
`P.primPart` divides `Q`; multiplying back by `P.content` gives a clearing identity with the fixed
denominator `P.content`.  Its degree is independent of the period.
-/
import GaloisForLFunctions.Bottcher.ConnectedRepellingNoParabolic
import Mathlib.RingTheory.Polynomial.GaussLemma

open Polynomial Finset Filter Topology

namespace Bottcher

/-- Any nonzero-denominator clearing identity forces divisibility by the primitive part of `P`. -/
theorem primitivePart_dvd_of_denominator_identity
    {P Q : Polynomial (Polynomial ℂ)}
    (hden : ∃ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 ∧
      (Polynomial.C e) * Q = P * S) :
    P.primPart ∣ Q := by
  classical
  obtain ⟨e, S, he0, hPS⟩ := hden
  let φ : Polynomial ℂ →+* FractionRing (Polynomial ℂ) :=
    algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ))
  let PpK : Polynomial (FractionRing (Polynomial ℂ)) := P.primPart.map φ
  let QK : Polynomial (FractionRing (Polynomial ℂ)) := Q.map φ
  let SK : Polynomial (FractionRing (Polynomial ℂ)) := S.map φ
  have heK : φ e ≠ 0 :=
    (map_ne_zero_iff φ
      (IsFractionRing.injective (Polynomial ℂ) (FractionRing (Polynomial ℂ)))).mpr he0
  have hmap : Polynomial.C (φ e) * QK = P.map φ * SK := by
    simpa [QK, SK, φ, Polynomial.map_mul, Polynomial.map_C] using
      congrArg (Polynomial.map φ) hPS
  have hPmap : P.map φ = Polynomial.C (φ P.content) * PpK := by
    simpa [PpK, φ, Polynomial.map_mul, Polynomial.map_C] using
      congrArg (Polynomial.map φ) P.eq_C_content_mul_primPart
  have hfrac : PpK ∣ QK := by
    refine ⟨Polynomial.C ((φ e)⁻¹ * φ P.content) * SK, ?_⟩
    rw [hPmap] at hmap
    calc
      QK = Polynomial.C ((φ e)⁻¹) * (Polynomial.C (φ e) * QK) := by
        rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ heK, Polynomial.C_1, one_mul]
      _ = Polynomial.C ((φ e)⁻¹) * ((Polynomial.C (φ P.content) * PpK) * SK) := by
        rw [hmap]
      _ = PpK * (Polynomial.C ((φ e)⁻¹ * φ P.content) * SK) := by
        rw [Polynomial.C_mul]
        ring_nf
  obtain ⟨g, hg⟩ := hfrac
  have hglift : g ∈ Polynomial.lifts φ := by
    apply P.isPrimitive_primPart.map_mul_mem_lifts_iff.mp
    rw [← hg]
    exact ⟨Q, rfl⟩
  obtain ⟨g0, hg0⟩ := (Polynomial.mem_lifts g).1 hglift
  refine ⟨g0, ?_⟩
  apply Polynomial.map_injective φ
    (IsFractionRing.injective (Polynomial ℂ) (FractionRing (Polynomial ℂ)))
  simpa [PpK, QK, Polynomial.map_mul, hg0] using hg

/-- If the primitive part of `P` divides `Q`, then `P.content` clears the quotient. -/
theorem content_denominator_identity_of_primitivePart_dvd
    (P Q : Polynomial (Polynomial ℂ)) (hdiv : P.primPart ∣ Q) :
    ∃ S : Polynomial (Polynomial ℂ), (Polynomial.C P.content) * Q = P * S := by
  obtain ⟨T, hT⟩ := hdiv
  refine ⟨T, ?_⟩
  rw [hT]
  conv_rhs => rw [P.eq_C_content_mul_primPart]
  ring

/-- Any clearing denominator can be replaced by the fixed denominator `P.content`. -/
theorem content_denominator_identity_of_denominator_identity
    {P Q : Polynomial (Polynomial ℂ)}
    (hden : ∃ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 ∧
      (Polynomial.C e) * Q = P * S) :
    ∃ S : Polynomial (Polynomial ℂ), (Polynomial.C P.content) * Q = P * S :=
  content_denominator_identity_of_primitivePart_dvd P Q
    (primitivePart_dvd_of_denominator_identity hden)

/-- Minimality produces a period-`p` clearing identity with denominator exactly `P.content`. -/
theorem content_compRelPoly_denominator_of_minimal {U : Set ℂ}
    (hUo : IsOpen U) (hUne : U.Nonempty) (c : ℂ) (hU : U ⊆ escapeOpen c)
    (P : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0)
    (hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
      (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    (hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
      (∀ z ∈ U, ∑ i ∈ R.support,
        (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
      P.natDegree ≤ R.natDegree)
    (p : ℕ) :
    ∃ S : Polynomial (Polynomial ℂ),
      (Polynomial.C P.content) * (compRelPoly c p P) = P * S :=
  content_denominator_identity_of_denominator_identity
    (exists_compRelPoly_denominator_of_minimal hUo hUne c hU P hP0 hPrel hPmin p)

/-- The fixed denominator `P.content` gives an eventual bounded witness for every sufficiently large
period, in fact for every period. -/
theorem eventually_content_compRelPoly_denominatorWitness_of_minimal {U : Set ℂ}
    (hUo : IsOpen U) (hUne : U.Nonempty) (c : ℂ) (hU : U ⊆ escapeOpen c)
    (P : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0)
    (hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
      (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    (hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
      (∀ z ∈ U, ∑ i ∈ R.support,
        (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
      P.natDegree ≤ R.natDegree) :
    ∀ᶠ p : ℕ in atTop,
      ∃ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)),
        e ≠ 0 ∧ (Polynomial.C e) * (compRelPoly c p P) = P * S ∧
          e.natDegree ≤ P.content.natDegree := by
  have hcontent0 : P.content ≠ 0 := by
    intro hcontent
    exact hP0 (Polynomial.content_eq_zero_iff.mp hcontent)
  exact Filter.Eventually.of_forall fun p => by
    obtain ⟨S, hS⟩ :=
      content_compRelPoly_denominator_of_minimal hUo hUne c hU P hP0 hPrel hPmin p
    exact ⟨P.content, S, hcontent0, hS, le_rfl⟩

/-- **Content-denominator hRigid input for absolute connected `φ_c` transcendence.**

For each minimal relation the caller now supplies only a finite eventual exceptional set for
non-strong roots and frequently many no-multiplier-one periods.  The bounded denominator witness is
created internally from `P.content`, so it is no longer a terminal hypothesis. -/
theorem phiMero_transcendental_of_repelling_frequently_multiplier_ne_one_contentDenominator_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ (P : Polynomial (Polynomial ℂ)) (_hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (_hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
        (_hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support,
            (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ E : Finset ℂ,
          (∃ᶠ p : ℕ in atTop, 1 ≤ p ∧
            ∀ z : ℂ, (fixedPointPoly c p).IsRoot z →
              (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) ≠ (1 : ℂ)) ∧
          (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply
    phiMero_transcendental_of_repelling_frequently_multiplier_ne_one_denominatorWitnessBound_noExtra_input
      hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨E, hmul, hE⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  exact ⟨E, P.content.natDegree, hmul, hE,
    eventually_content_compRelPoly_denominatorWitness_of_minimal
      hUo hUne c hU P hP0 hPrel hPmin⟩

end Bottcher
