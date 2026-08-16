import GaloisForLFunctions.RHTower.XiShiftedHardEdgeOddRootSuzukiAdmission
import GaloisForLFunctions.RHTower.SoninEvenCarrier
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral
import GaloisForLFunctions.RHTower.XiShiftedHardEdgePaleyWiener

/-!
# Literal compact source for the Route-U hard-edge limit

An abstract `L²` bandlimit is enough to select a literal compact integrable Fourier source.  For a
continuous representative, Fourier squaring and continuity upgrade its almost-everywhere inversion
law to a pointwise identity.  Applied to the actual hard-edge strong limit, this transports every
continuous squared-variable root factorization to a pointwise compact source at the exact Route-U
`2π` normalization, without losing multiplicity.
-/

open Complex MeasureTheory Set
open scoped ENNReal FourierTransform
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Literal open-interval representative of the Fourier transform of an L² state. -/
def routeUBandlimitedCompactSource
    (a : ℝ) (F : SoninL2) : ℝ → ℂ :=
  (Ioo (-a) a).indicator fun x => (fourierUnitary F : ℝ → ℂ) x

/-- Almost-everywhere support outside a closed band can be sharpened to the open-band hypothesis
needed by the literal representative: the two endpoints are null. -/
theorem routeUOpenBandSupport_of_ae_abs_support
    {a : ℝ} (ha : 0 ≤ a) {F : SoninL2}
    (hhigh : ∀ᵐ x ∂(volume : Measure ℝ),
      a < |x| → (fourierUnitary F : ℝ → ℂ) x = 0) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      x ∉ Ioo (-a) a → (fourierUnitary F : ℝ → ℂ) x = 0 := by
  filter_upwards [hhigh, volume.ae_ne (-a), volume.ae_ne a] with x hx hleft hright
  intro hout
  apply hx
  have hout' : x ≤ -a ∨ a ≤ x := by
    simpa only [mem_Ioo, not_and_or, not_lt] using hout
  rcases hout' with hxneg | hxpos
  · rw [abs_of_nonpos (hxneg.trans (neg_nonpos.mpr ha))]
    apply lt_of_le_of_ne (by linarith)
    intro heq
    apply hleft
    linarith
  · rw [abs_of_nonneg (ha.trans hxpos)]
    exact lt_of_le_of_ne hxpos (Ne.symm hright)

/-- The actual Route-U hard-edge strong limit satisfies the open-band support condition at
aperture `C/π`; endpoint values are discarded only on their null set. -/
theorem routeUHardEdge_limit_open_band_support {C : ℝ} (hC : 0 < C)
    {a : ℕ → ℝ} {p : ℕ → Polynomial ℝ} {N : ℕ → ℕ} {b : ℕ → ℕ → ℝ}
    (ha : ∀ k : ℕ, 0 < a k)
    (haT : Filter.Tendsto a Filter.atTop Filter.atTop)
    (hb : ∀ k : ℕ, routeUHardEdgeAngularPoly (a k) (p k)
      = ∑ j ∈ Finset.range (N k + 1),
        Polynomial.C (b k j) * Polynomial.Chebyshev.T ℝ (j : ℤ))
    (hNC : ∀ k : ℕ, ((N k : ℕ) : ℝ) ≤ C * a k)
    (hnorm : ∀ k : ℕ,
      (∫ x : ℝ, routeUHardEdgeRationalTest (a k) (p k) x ^ 2) = 1)
    {L : Lp ℝ 2 (volume : Measure ℝ)}
    (hL : Filter.Tendsto (fun k : ℕ =>
      (memLp_routeUHardEdgeRationalTest (ha k) (p k)).toLp
        (routeUHardEdgeRationalTest (a k) (p k))) Filter.atTop (nhds L)) :
    ∀ᵐ ξ ∂(volume : Measure ℝ),
      ξ ∉ Ioo (-(C / Real.pi)) (C / Real.pi) →
        (fourierUnitary (ofRealLp L) : ℝ → ℂ) ξ = 0 := by
  apply routeUOpenBandSupport_of_ae_abs_support (le_of_lt (div_pos hC Real.pi_pos))
  filter_upwards [routeUHardEdge_limit_fourier_ae_eq_zero
    hC ha haT hb hNC hnorm hL] with ξ hξ
  intro habs
  apply hξ
  have hmul : C < Real.pi * |ξ| := by
    simpa [mul_comm] using (div_lt_iff₀ Real.pi_pos).mp habs
  nlinarith [Real.pi_pos]

theorem routeUBandlimitedCompactSource_ae
    {a : ℝ} {F : SoninL2}
    (hband : ∀ᵐ x ∂(volume : Measure ℝ),
      x ∉ Ioo (-a) a → (fourierUnitary F : ℝ → ℂ) x = 0) :
    (fourierUnitary F : ℝ → ℂ) =ᵐ[volume]
      routeUBandlimitedCompactSource a F := by
  filter_upwards [hband] with x hx
  by_cases hxi : x ∈ Ioo (-a) a
  · simp [routeUBandlimitedCompactSource, hxi]
  · simp [routeUBandlimitedCompactSource, hxi, hx hxi]

theorem integrable_routeUBandlimitedCompactSource
    (a : ℝ) (F : SoninL2) :
    Integrable (routeUBandlimitedCompactSource a F) := by
  exact (integrableOn_Lp_of_measure_ne_top (fourierUnitary F)
    fact_one_le_two_ennreal.elim measure_Ioo_lt_top.ne).integrable_indicator measurableSet_Ioo

theorem memLp_routeUBandlimitedCompactSource
    {a : ℝ} {F : SoninL2}
    (hband : ∀ᵐ x ∂(volume : Measure ℝ),
      x ∉ Ioo (-a) a → (fourierUnitary F : ℝ → ℂ) x = 0) :
    MemLp (routeUBandlimitedCompactSource a F) 2 volume :=
  (memLp_congr_ae (routeUBandlimitedCompactSource_ae hband)).mp
    (Lp.memLp (fourierUnitary F))

theorem fourier_routeUBandlimitedCompactSource_eq_reflection
    {a : ℝ} {f : ℝ → ℂ} (hfcont : Continuous f)
    (hf2 : MemLp f 2 volume)
    (hband : ∀ᵐ x ∂(volume : Measure ℝ),
      x ∉ Ioo (-a) a →
        (fourierUnitary (hf2.toLp f) : ℝ → ℂ) x = 0)
    (ξ : ℝ) :
    𝓕 (routeUBandlimitedCompactSource a (hf2.toLp f)) ξ = f (-ξ) := by
  let F : SoninL2 := hf2.toLp f
  let q : ℝ → ℂ := routeUBandlimitedCompactSource a F
  have hqae : (fourierUnitary F : ℝ → ℂ) =ᵐ[volume] q := by
    exact routeUBandlimitedCompactSource_ae hband
  have hq1 : Integrable q := integrable_routeUBandlimitedCompactSource a F
  have hq2 : MemLp q 2 volume :=
    (memLp_congr_ae hqae).mp (Lp.memLp (fourierUnitary F))
  have hqLp : hq2.toLp q = fourierUnitary F := by
    apply Lp.ext
    exact hq2.coeFn_toLp.trans hqae.symm
  have hdouble : 𝓕 (hq2.toLp q) = l2Reflection F := by
    rw [hqLp]
    exact l2_fourier_fourier F
  have hclassical :
      ((l2Reflection F : SoninL2) : ℝ → ℂ) =ᵐ[volume] 𝓕 q := by
    have h := GaloisForLFunctions.RHTower.coeFn_fourier_toLp hq1 hq2
    rw [hdouble] at h
    exact h
  have hFneg : (fun x : ℝ => (F : ℝ → ℂ) (-x)) =ᵐ[volume]
      fun x : ℝ => f (-x) := by
    exact hf2.coeFn_toLp.comp_tendsto
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  have hae : 𝓕 q =ᵐ[volume] fun x : ℝ => f (-x) :=
    hclassical.symm.trans ((l2Reflection_ae F).trans hFneg)
  have heq : 𝓕 q = fun x : ℝ => f (-x) :=
    ((GaloisForLFunctions.RHTower.continuous_fourier_of_integrable hq1).ae_eq_iff_eq
      (volume : Measure ℝ) (hfcont.comp continuous_neg)).mp hae
  exact congrFun heq ξ

theorem routeURealFourier_routeUBandlimitedCompactSource
    {a : ℝ} {f : ℝ → ℂ} (hfcont : Continuous f)
    (hf2 : MemLp f 2 volume)
    (hband : ∀ᵐ x ∂(volume : Measure ℝ),
      x ∉ Ioo (-a) a →
        (fourierUnitary (hf2.toLp f) : ℝ → ℂ) x = 0)
    (w : ℝ) :
    routeURealFourier (routeUBandlimitedCompactSource a (hf2.toLp f)) w =
      f (w / (2 * Real.pi)) := by
  have hscale := routeURealFourier_neg_two_pi_eq_fourier
    (routeUBandlimitedCompactSource a (hf2.toLp f)) (-w / (2 * Real.pi))
  have hfourier := fourier_routeUBandlimitedCompactSource_eq_reflection
    hfcont hf2 hband (-w / (2 * Real.pi))
  rw [hfourier] at hscale
  convert hscale using 1 <;> field_simp [Real.pi_ne_zero]

theorem routeUBandlimitedCompactSource_eq_zero_of_outside
    (a : ℝ) (F : SoninL2) {x : ℝ}
    (hx : x ≤ -a ∨ a ≤ x) :
    routeUBandlimitedCompactSource a F x = 0 := by
  have hnot : x ∉ Ioo (-a) a := by
    rintro ⟨hleft, hright⟩
    rcases hx with hx | hx <;> linarith
  simp [routeUBandlimitedCompactSource, hnot]

/-- Squared-variable profile transported through Route U's `2π` Fourier normalization. -/
def routeUScaledSquaredProfile (m : ℕ) (K : ℝ → ℂ) (u : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ) ^ (2 * m))⁻¹ * K (u / (2 * Real.pi) ^ 2)

theorem continuous_routeUScaledSquaredProfile
    {m : ℕ} {K : ℝ → ℂ} (hK : Continuous K) :
    Continuous (routeUScaledSquaredProfile m K) := by
  exact continuous_const.mul (hK.comp (continuous_id.div_const ((2 * Real.pi) ^ 2)))

theorem routeURealFourier_routeUBandlimitedCompactSource_factor_pow
    {a r : ℝ} {m : ℕ} {f : ℝ → ℂ} {K : ℝ → ℂ}
    (hfcont : Continuous f) (hf2 : MemLp f 2 volume)
    (hband : ∀ᵐ x ∂(volume : Measure ℝ),
      x ∉ Ioo (-a) a →
        (fourierUnitary (hf2.toLp f) : ℝ → ℂ) x = 0)
    (hfactor : ∀ x : ℝ,
      f x = (((x ^ 2 - r ^ 2 : ℝ) : ℂ) ^ m) * K (x ^ 2))
    (w : ℝ) :
    routeURealFourier (routeUBandlimitedCompactSource a (hf2.toLp f)) w =
      (((w ^ 2 - (2 * Real.pi * r) ^ 2 : ℝ) : ℂ) ^ m) *
        routeUScaledSquaredProfile m K (w ^ 2) := by
  rw [routeURealFourier_routeUBandlimitedCompactSource hfcont hf2 hband, hfactor]
  have hbase :
      (w / (2 * Real.pi)) ^ 2 - r ^ 2 =
        (w ^ 2 - (2 * Real.pi * r) ^ 2) / (2 * Real.pi) ^ 2 := by
    field_simp [Real.pi_ne_zero]
  have harg : (w / (2 * Real.pi)) ^ 2 = w ^ 2 / (2 * Real.pi) ^ 2 := by
    rw [div_pow]
  rw [hbase, harg, routeUScaledSquaredProfile]
  push_cast
  rw [div_pow, pow_mul]
  ring

/-- A continuous representative of the actual Route-U hard-edge limit has a literal compact
source, not merely an abstract Paley--Wiener `L²` class. -/
theorem routeUHardEdge_limit_has_literal_compact_source {C : ℝ} (hC : 0 < C)
    {a : ℕ → ℝ} {p : ℕ → Polynomial ℝ} {N : ℕ → ℕ} {b : ℕ → ℕ → ℝ}
    (ha : ∀ k : ℕ, 0 < a k)
    (haT : Filter.Tendsto a Filter.atTop Filter.atTop)
    (hb : ∀ k : ℕ, routeUHardEdgeAngularPoly (a k) (p k)
      = ∑ j ∈ Finset.range (N k + 1),
        Polynomial.C (b k j) * Polynomial.Chebyshev.T ℝ (j : ℤ))
    (hNC : ∀ k : ℕ, ((N k : ℕ) : ℝ) ≤ C * a k)
    (hnorm : ∀ k : ℕ,
      (∫ x : ℝ, routeUHardEdgeRationalTest (a k) (p k) x ^ 2) = 1)
    {L : Lp ℝ 2 (volume : Measure ℝ)}
    (hL : Filter.Tendsto (fun k : ℕ =>
      (memLp_routeUHardEdgeRationalTest (ha k) (p k)).toLp
        (routeUHardEdgeRationalTest (a k) (p k))) Filter.atTop (nhds L))
    {f : ℝ → ℂ} (hfcont : Continuous f) (hf2 : MemLp f 2 volume)
    (hrep : hf2.toLp f = ofRealLp L) :
    ∃ q : ℝ → ℂ,
      Integrable q ∧ MemLp q 2 volume ∧
      (∀ x : ℝ, x ≤ -(C / Real.pi) ∨ C / Real.pi ≤ x → q x = 0) ∧
      (∀ w : ℝ, routeURealFourier q w = f (w / (2 * Real.pi))) := by
  have hbandL := routeUHardEdge_limit_open_band_support
    hC ha haT hb hNC hnorm hL
  have hband : ∀ᵐ ξ ∂(volume : Measure ℝ),
      ξ ∉ Ioo (-(C / Real.pi)) (C / Real.pi) →
        (fourierUnitary (hf2.toLp f) : ℝ → ℂ) ξ = 0 := by
    rw [hrep]
    exact hbandL
  let q := routeUBandlimitedCompactSource (C / Real.pi) (hf2.toLp f)
  refine ⟨q, integrable_routeUBandlimitedCompactSource _ _,
    memLp_routeUBandlimitedCompactSource hband, ?_, ?_⟩
  · intro x hx
    exact routeUBandlimitedCompactSource_eq_zero_of_outside _ _ hx
  · intro w
    exact routeURealFourier_routeUBandlimitedCompactSource hfcont hf2 hband w

/-- Exact symmetric-root factorization survives actual hard-edge source selection.  The new
profile is continuous and root multiplicity is unchanged under Route U's normalization. -/
theorem routeUHardEdge_limit_has_literal_compact_factorization
    {C : ℝ} (hC : 0 < C)
    {a : ℕ → ℝ} {p : ℕ → Polynomial ℝ} {N : ℕ → ℕ} {b : ℕ → ℕ → ℝ}
    (ha : ∀ k : ℕ, 0 < a k)
    (haT : Filter.Tendsto a Filter.atTop Filter.atTop)
    (hb : ∀ k : ℕ, routeUHardEdgeAngularPoly (a k) (p k)
      = ∑ j ∈ Finset.range (N k + 1),
        Polynomial.C (b k j) * Polynomial.Chebyshev.T ℝ (j : ℤ))
    (hNC : ∀ k : ℕ, ((N k : ℕ) : ℝ) ≤ C * a k)
    (hnorm : ∀ k : ℕ,
      (∫ x : ℝ, routeUHardEdgeRationalTest (a k) (p k) x ^ 2) = 1)
    {L : Lp ℝ 2 (volume : Measure ℝ)}
    (hL : Filter.Tendsto (fun k : ℕ =>
      (memLp_routeUHardEdgeRationalTest (ha k) (p k)).toLp
        (routeUHardEdgeRationalTest (a k) (p k))) Filter.atTop (nhds L))
    {f : ℝ → ℂ} (hfcont : Continuous f) (hf2 : MemLp f 2 volume)
    (hrep : hf2.toLp f = ofRealLp L)
    {r : ℝ} {m : ℕ} {K : ℝ → ℂ} (hK : Continuous K)
    (hfactor : ∀ x : ℝ,
      f x = (((x ^ 2 - r ^ 2 : ℝ) : ℂ) ^ m) * K (x ^ 2)) :
    ∃ q : ℝ → ℂ, ∃ G : ℝ → ℂ,
      Integrable q ∧ MemLp q 2 volume ∧ Continuous G ∧
      (∀ x : ℝ, x ≤ -(C / Real.pi) ∨ C / Real.pi ≤ x → q x = 0) ∧
      (∀ w : ℝ, routeURealFourier q w =
        (((w ^ 2 - (2 * Real.pi * r) ^ 2 : ℝ) : ℂ) ^ m) * G (w ^ 2)) := by
  have hbandL := routeUHardEdge_limit_open_band_support
    hC ha haT hb hNC hnorm hL
  have hband : ∀ᵐ ξ ∂(volume : Measure ℝ),
      ξ ∉ Ioo (-(C / Real.pi)) (C / Real.pi) →
        (fourierUnitary (hf2.toLp f) : ℝ → ℂ) ξ = 0 := by
    rw [hrep]
    exact hbandL
  let q := routeUBandlimitedCompactSource (C / Real.pi) (hf2.toLp f)
  let G := routeUScaledSquaredProfile m K
  refine ⟨q, G, integrable_routeUBandlimitedCompactSource _ _,
    memLp_routeUBandlimitedCompactSource hband,
    continuous_routeUScaledSquaredProfile hK, ?_, ?_⟩
  · intro x hx
    exact routeUBandlimitedCompactSource_eq_zero_of_outside _ _ hx
  · intro w
    exact routeURealFourier_routeUBandlimitedCompactSource_factor_pow
      hfcont hf2 hband hfactor w

end RHTower
