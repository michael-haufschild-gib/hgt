import GaloisForLFunctions.RHTower.DeningerDivisorDefectTrace
import GaloisForLFunctions.RHTower.DeningerLefschetzTrace

/-!
# Prime-side reduction of the twisted resolvent trace

The defect trace splits every anti-holomorphic spectral sum into a holomorphic half and a defect
half.  This file computes the holomorphic half from the prime side, with no differentiation of
the trace: for three pairwise distinct base points off the divisor, partial fractions turn the
`μ`-twisted triple resolvent into a finite combination of the corpus's relative resolvent terms,
so its trace is a finite combination of `logDeriv XiC` values — and, through the arithmetic
Lefschetz formula, of continued prime–Gamma source traces.  Concretely

`Σ' q, μ_q · Π (μ_q - zᵢ)⁻¹ = -(Σᵢ cᵢ · logDeriv XiC zᵢ)`,  `cᵢ = zᵢ / Πⱼ≠ᵢ (zᵢ - zⱼ)`,

where the three partial-fraction coefficients sum to zero — which is exactly why the divergent
single resolvents recombine into the absolutely convergent *relative* terms.

Consequences:

* the **mixed trace** `Σ' conj(μ_q) · Π (μ_q - zᵢ)⁻¹` — the non-holomorphic object no
  holomorphic trace computes — equals the prime expression minus the three-point defect trace,
  unconditionally;
* under RH the mixed trace **is** the prime expression: the anti-holomorphic spectral data of
  the divisor flow becomes von-Mangoldt-computable, and the obstruction to this, off RH, is
  exactly the defect trace of the displacement Ward identity.

Everything is unconditional except where `RiemannHypothesis` is an explicit hypothesis.
-/

noncomputable section

open Complex

namespace RHTower

/-- Partial-fraction identity for the `x`-twisted triple resolvent.  The coefficient sum
vanishes, so the expansion lands in differences `x⁻¹ - (x - zᵢ)⁻¹` — the relative resolvent
terms — rather than in divergent single resolvents. -/
theorem twisted_triple_partial_fraction {x z₁ z₂ z₃ : ℂ} (hx : x ≠ 0)
    (h1 : x ≠ z₁) (h2 : x ≠ z₂) (h3 : x ≠ z₃)
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) :
    x * (x - z₁)⁻¹ * (x - z₂)⁻¹ * (x - z₃)⁻¹ =
      -((z₁ / ((z₁ - z₂) * (z₁ - z₃))) * (x⁻¹ - (x - z₁)⁻¹) +
        (z₂ / ((z₂ - z₁) * (z₂ - z₃))) * (x⁻¹ - (x - z₂)⁻¹) +
        (z₃ / ((z₃ - z₁) * (z₃ - z₂))) * (x⁻¹ - (x - z₃)⁻¹)) := by
  have hx1 : x - z₁ ≠ 0 := sub_ne_zero.mpr h1
  have hx2 : x - z₂ ≠ 0 := sub_ne_zero.mpr h2
  have hx3 : x - z₃ ≠ 0 := sub_ne_zero.mpr h3
  have h12' : z₁ - z₂ ≠ 0 := sub_ne_zero.mpr h12
  have h13' : z₁ - z₃ ≠ 0 := sub_ne_zero.mpr h13
  have h23' : z₂ - z₃ ≠ 0 := sub_ne_zero.mpr h23
  have h21' : z₂ - z₁ ≠ 0 := sub_ne_zero.mpr h12.symm
  have h31' : z₃ - z₁ ≠ 0 := sub_ne_zero.mpr h13.symm
  have h32' : z₃ - z₂ ≠ 0 := sub_ne_zero.mpr h23.symm
  field_simp
  ring

/-- A base point off the divisor is distinct from every spectral point. -/
theorem xiSpectralPoint_ne_of_XiC_ne_zero {z : ℂ} (hz : XiC z ≠ 0)
    (q : XiZeroCopy) : xiSpectralPoint q ≠ z :=
  fun h => hz (h ▸ XiC_xiSpectralPoint_eq_zero q)

/-- The `μ`-twisted triple resolvent term of the divisor flow. -/
def deningerDivisorTwistedResolventTerm (z₁ z₂ z₃ : ℂ) (q : XiZeroCopy) : ℂ :=
  xiSpectralPoint q * (xiSpectralPoint q - z₁)⁻¹ *
    (xiSpectralPoint q - z₂)⁻¹ * (xiSpectralPoint q - z₃)⁻¹

/-- Termwise partial-fraction reduction to relative resolvent terms. -/
theorem deningerDivisorTwistedResolventTerm_eq
    {z₁ z₂ z₃ : ℂ} (hz₁ : XiC z₁ ≠ 0) (hz₂ : XiC z₂ ≠ 0) (hz₃ : XiC z₃ ≠ 0)
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) (q : XiZeroCopy) :
    deningerDivisorTwistedResolventTerm z₁ z₂ z₃ q =
      -((z₁ / ((z₁ - z₂) * (z₁ - z₃))) * xiRelativeResolventTerm z₁ q +
        (z₂ / ((z₂ - z₁) * (z₂ - z₃))) * xiRelativeResolventTerm z₂ q +
        (z₃ / ((z₃ - z₁) * (z₃ - z₂))) * xiRelativeResolventTerm z₃ q) := by
  have hterm : ∀ z : ℂ, xiRelativeResolventTerm z q =
      (xiSpectralPoint q)⁻¹ - (xiSpectralPoint q - z)⁻¹ := by
    intro z
    rw [← deningerDivisorRelativeResolventTerm_eq]
    rfl
  rw [hterm, hterm, hterm, deningerDivisorTwistedResolventTerm]
  exact twisted_triple_partial_fraction (xiSpectralPoint_ne_zero q)
    (xiSpectralPoint_ne_of_XiC_ne_zero hz₁ q)
    (xiSpectralPoint_ne_of_XiC_ne_zero hz₂ q)
    (xiSpectralPoint_ne_of_XiC_ne_zero hz₃ q) h12 h13 h23

/-- The twisted terms are absolutely summable: they are a finite combination of relative
resolvent families. -/
theorem summable_deningerDivisorTwistedResolventTerm
    {z₁ z₂ z₃ : ℂ} (hz₁ : XiC z₁ ≠ 0) (hz₂ : XiC z₂ ≠ 0) (hz₃ : XiC z₃ ≠ 0)
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) :
    Summable (deningerDivisorTwistedResolventTerm z₁ z₂ z₃) := by
  apply Summable.congr _ (fun q =>
    (deningerDivisorTwistedResolventTerm_eq hz₁ hz₂ hz₃ h12 h13 h23 q).symm)
  exact ((((summable_xiRelativeResolventTerm hz₁).mul_left _).add
    ((summable_xiRelativeResolventTerm hz₂).mul_left _)).add
    ((summable_xiRelativeResolventTerm hz₃).mul_left _)).neg

/-- **Prime-side reduction of the twisted trace.**  The `μ`-twisted triple resolvent trace is a
finite combination of Xi logarithmic-derivative values — no differentiation of the trace, no
zero data. -/
theorem deningerDivisorTwistedResolventTrace_eq_logDeriv
    {z₁ z₂ z₃ : ℂ} (hz₁ : XiC z₁ ≠ 0) (hz₂ : XiC z₂ ≠ 0) (hz₃ : XiC z₃ ≠ 0)
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) :
    (∑' q : XiZeroCopy, deningerDivisorTwistedResolventTerm z₁ z₂ z₃ q) =
      -((z₁ / ((z₁ - z₂) * (z₁ - z₃))) * logDeriv XiC z₁ +
        (z₂ / ((z₂ - z₁) * (z₂ - z₃))) * logDeriv XiC z₂ +
        (z₃ / ((z₃ - z₁) * (z₃ - z₂))) * logDeriv XiC z₃) := by
  have hs₁ := (summable_xiRelativeResolventTerm hz₁).mul_left
    (z₁ / ((z₁ - z₂) * (z₁ - z₃)))
  have hs₂ := (summable_xiRelativeResolventTerm hz₂).mul_left
    (z₂ / ((z₂ - z₁) * (z₂ - z₃)))
  have hs₃ := (summable_xiRelativeResolventTerm hz₃).mul_left
    (z₃ / ((z₃ - z₁) * (z₃ - z₂)))
  calc (∑' q : XiZeroCopy, deningerDivisorTwistedResolventTerm z₁ z₂ z₃ q)
      = ∑' q : XiZeroCopy,
          -((z₁ / ((z₁ - z₂) * (z₁ - z₃))) * xiRelativeResolventTerm z₁ q +
            (z₂ / ((z₂ - z₁) * (z₂ - z₃))) * xiRelativeResolventTerm z₂ q +
            (z₃ / ((z₃ - z₁) * (z₃ - z₂))) * xiRelativeResolventTerm z₃ q) :=
        tsum_congr (deningerDivisorTwistedResolventTerm_eq hz₁ hz₂ hz₃
          h12 h13 h23)
    _ = -((z₁ / ((z₁ - z₂) * (z₁ - z₃))) * xiRelativeResolventTrace z₁ +
          (z₂ / ((z₂ - z₁) * (z₂ - z₃))) * xiRelativeResolventTrace z₂ +
          (z₃ / ((z₃ - z₁) * (z₃ - z₂))) * xiRelativeResolventTrace z₃) := by
        rw [tsum_neg, (hs₁.add hs₂).tsum_add hs₃, hs₁.tsum_add hs₂,
          tsum_mul_left, tsum_mul_left, tsum_mul_left]
        rfl
    _ = -((z₁ / ((z₁ - z₂) * (z₁ - z₃))) * logDeriv XiC z₁ +
          (z₂ / ((z₂ - z₁) * (z₂ - z₃))) * logDeriv XiC z₂ +
          (z₃ / ((z₃ - z₁) * (z₃ - z₂))) * logDeriv XiC z₃) := by
        rw [logDeriv_XiC_eq_relativeResolventTrace hz₁,
          logDeriv_XiC_eq_relativeResolventTrace hz₂,
          logDeriv_XiC_eq_relativeResolventTrace hz₃]

/-- **The twisted trace is prime data.**  On admissible base points the logarithmic-derivative
values are the continued prime–Gamma source traces of the arithmetic Lefschetz formula, so the
`μ`-twisted spectral sum is computed by the primes. -/
theorem deningerDivisorTwistedResolventTrace_eq_primeArchSource
    {z₁ z₂ z₃ : ℂ}
    (ha₁ : XiExplicitAdmissible z₁) (ha₂ : XiExplicitAdmissible z₂)
    (ha₃ : XiExplicitAdmissible z₃)
    (hz₁ : XiC z₁ ≠ 0) (hz₂ : XiC z₂ ≠ 0) (hz₃ : XiC z₃ ≠ 0)
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) :
    (∑' q : XiZeroCopy, deningerDivisorTwistedResolventTerm z₁ z₂ z₃ q) =
      -((z₁ / ((z₁ - z₂) * (z₁ - z₃))) *
          continuedPrimeArchSourceRelativeTrace z₁ +
        (z₂ / ((z₂ - z₁) * (z₂ - z₃))) *
          continuedPrimeArchSourceRelativeTrace z₂ +
        (z₃ / ((z₃ - z₁) * (z₃ - z₂))) *
          continuedPrimeArchSourceRelativeTrace z₃) := by
  have hsource : ∀ {z : ℂ}, XiExplicitAdmissible z → XiC z ≠ 0 →
      logDeriv XiC z = continuedPrimeArchSourceRelativeTrace z := by
    intro z ha hz
    rw [logDeriv_XiC_eq_relativeResolventTrace hz,
      ← deningerDivisorRelativeResolventTrace_eq]
    exact deningerResolventLefschetzTrace ha
  rw [deningerDivisorTwistedResolventTrace_eq_logDeriv hz₁ hz₂ hz₃ h12 h13 h23,
    hsource ha₁ hz₁, hsource ha₂ hz₂, hsource ha₃ hz₃]

/-- The mixed (conjugate-twisted) triple resolvent term: the non-holomorphic spectral object. -/
def deningerDivisorMixedResolventTerm (z₁ z₂ z₃ : ℂ) (q : XiZeroCopy) : ℂ :=
  (starRingEnd ℂ) (xiSpectralPoint q) * (xiSpectralPoint q - z₁)⁻¹ *
    (xiSpectralPoint q - z₂)⁻¹ * (xiSpectralPoint q - z₃)⁻¹

/-- The three-point defect term: the Ward twist against three distinct resolvents. -/
def deningerDivisorThreePointDefectTerm (z₁ z₂ z₃ : ℂ) (q : XiZeroCopy) : ℂ :=
  (xiSpectralPoint q - (starRingEnd ℂ) (xiSpectralPoint q)) *
    ((xiSpectralPoint q - z₁)⁻¹ * ((xiSpectralPoint q - z₂)⁻¹ *
      (xiSpectralPoint q - z₃)⁻¹))

/-- Exact termwise decomposition: twisted = mixed + three-point defect. -/
theorem deningerDivisorTwistedResolventTerm_sub_mixed (z₁ z₂ z₃ : ℂ)
    (q : XiZeroCopy) :
    deningerDivisorTwistedResolventTerm z₁ z₂ z₃ q -
        deningerDivisorMixedResolventTerm z₁ z₂ z₃ q =
      deningerDivisorThreePointDefectTerm z₁ z₂ z₃ q := by
  rw [deningerDivisorTwistedResolventTerm, deningerDivisorMixedResolventTerm,
    deningerDivisorThreePointDefectTerm]
  ring

/-- Under RH the mixed term equals the twisted term: real spectral points are conjugation
fixed. -/
theorem deningerDivisorMixedResolventTerm_eq_of_riemannHypothesis
    (hRH : RiemannHypothesis) (z₁ z₂ z₃ : ℂ) (q : XiZeroCopy) :
    deningerDivisorMixedResolventTerm z₁ z₂ z₃ q =
      deningerDivisorTwistedResolventTerm z₁ z₂ z₃ q := by
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
  rw [deningerDivisorMixedResolventTerm, deningerDivisorTwistedResolventTerm,
    ht, Complex.conj_ofReal]

/-- **Under RH the non-holomorphic spectral trace is prime data.**  The mixed trace — which no
holomorphic identity computes — becomes the continued prime–Gamma source combination.
Unconditionally, the gap between the mixed trace and this prime expression is exactly the
three-point defect trace of the displacement Ward identity. -/
theorem deningerDivisorMixedResolventTrace_eq_primeArchSource_of_riemannHypothesis
    (hRH : RiemannHypothesis) {z₁ z₂ z₃ : ℂ}
    (ha₁ : XiExplicitAdmissible z₁) (ha₂ : XiExplicitAdmissible z₂)
    (ha₃ : XiExplicitAdmissible z₃)
    (hz₁ : XiC z₁ ≠ 0) (hz₂ : XiC z₂ ≠ 0) (hz₃ : XiC z₃ ≠ 0)
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) :
    (∑' q : XiZeroCopy, deningerDivisorMixedResolventTerm z₁ z₂ z₃ q) =
      -((z₁ / ((z₁ - z₂) * (z₁ - z₃))) *
          continuedPrimeArchSourceRelativeTrace z₁ +
        (z₂ / ((z₂ - z₁) * (z₂ - z₃))) *
          continuedPrimeArchSourceRelativeTrace z₂ +
        (z₃ / ((z₃ - z₁) * (z₃ - z₂))) *
          continuedPrimeArchSourceRelativeTrace z₃) := by
  rw [tsum_congr (deningerDivisorMixedResolventTerm_eq_of_riemannHypothesis
    hRH z₁ z₂ z₃)]
  exact deningerDivisorTwistedResolventTrace_eq_primeArchSource
    ha₁ ha₂ ha₃ hz₁ hz₂ hz₃ h12 h13 h23

end RHTower
