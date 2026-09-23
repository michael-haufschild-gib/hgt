import GaloisForLFunctions.RHTower.ProlateIndexedTotalMass
import GaloisForLFunctions.RHTower.ProlateProfileIntegralLimit
import GaloisForLFunctions.RHTower.ProlateTailIntegralBound
import GaloisForLFunctions.RHTower.HermiteLineIntegral

/-!
# The profile integral of the canonical indexed prolate mode

The first moment of the `n`-th canonical even prolate profile over its natural window converges to
the whole-line integral of the `2n`-th Hermite function:

```text
φ_{2n}(0) · ∫_{−√c}^{√c} Ψ_n  →  ∫_ℝ φ_{2n} .
```

Every input of the growing-window transfer is available at the indexed family: the window
comparison gives convergence on each fixed window, a Hermite function is a polynomial times a
Gaussian and so its symmetric windows exhaust its mass, the aperture virial bounds the second moment
by the separation constant — which converges — and the second-moment tail bound turns that into
tails uniformly below any target.  Evenness of the profile copies the right tail bound to the left.

Dividing by the total mass gives the shape ratio, the amplitude-free quantity the constrained
prolate coordinate is built from; the amplitude cancels because the ratio is quadratic over
quadratic.
-/

noncomputable section

open MeasureTheory Set Filter Topology GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-! ## The amplitude is nonzero -/

theorem indexedRungAmplitude_ne_zero (n : ℕ) : indexedRungAmplitude n ≠ 0 := by
  intro h
  have hlim := tendsto_indexedRung_totalMass n
  have hfun : (fun a : ProlatePositiveAperture =>
      indexedRungAmplitude n ^ (2 : ℕ) * indexedOscillatorTotalMass n a) = fun _ => (0 : ℝ) := by
    funext a
    rw [h]
    ring
  rw [hfun] at hlim
  have heq : (0 : ℝ) = ∫ x, hermiteFun (2 * n) x ^ (2 : ℕ) :=
    tendsto_nhds_unique tendsto_const_nhds hlim
  exact absurd heq.symm (integral_hermiteFun_sq_pos_line (2 * n)).ne'

/-! ## The window integral -/

/-- **The window integral converges to the Hermite window integral.** -/
theorem tendsto_indexedRung_windowIntegral (n : ℕ) {K : ℝ} (hK : 0 < K) :
    Tendsto (fun a : ProlatePositiveAperture =>
        ∫ x in (-K)..K, indexedRungAmplitude n * indexedOscillatorProfile n a x)
      atTop (𝓝 (∫ x in (-K)..K, hermiteFun (2 * n) x)) := by
  set κ : ℝ := indexedRungAmplitude n with hκ
  have hbnd : ∀ᶠ a in (atTop : Filter ProlatePositiveAperture),
      ‖(∫ x in (-K)..K, κ * indexedOscillatorProfile n a x)
        - ∫ x in (-K)..K, hermiteFun (2 * n) x‖
        ≤ indexedRungEnvelope n K a * (2 * K) := by
    filter_upwards [eventually_indexedRung_windowDist n hK] with a hdist
    have hsub : (∫ x in (-K)..K, κ * indexedOscillatorProfile n a x)
        - (∫ x in (-K)..K, hermiteFun (2 * n) x)
        = ∫ x in (-K)..K, (κ * indexedOscillatorProfile n a x - hermiteFun (2 * n) x) := by
      rw [← intervalIntegral.integral_sub]
      · exact (continuous_const.mul
          (continuous_indexedOscillatorProfile n a)).intervalIntegrable _ _
      · exact (continuous_hermiteFun (2 * n)).intervalIntegrable _ _
    rw [hsub]
    have hptwise : ∀ x ∈ uIoc (-K) K,
        ‖κ * indexedOscillatorProfile n a x - hermiteFun (2 * n) x‖
          ≤ indexedRungEnvelope n K a := by
      intro x hx
      have hxIcc : x ∈ Icc (-K) K := by
        rw [uIoc_of_le (by linarith : (-K : ℝ) ≤ K)] at hx
        exact ⟨le_of_lt hx.1, hx.2⟩
      rw [Real.norm_eq_abs]
      exact hdist x hxIcc
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const hptwise
    have habs : |K - -K| = 2 * K := by
      rw [show K - -K = 2 * K from by ring, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * K)]
    rwa [habs] at hle
  have henv : Tendsto (fun a : ProlatePositiveAperture =>
      indexedRungEnvelope n K a * (2 * K)) atTop (𝓝 0) := by
    simpa using (tendsto_indexedRungEnvelope n K).mul_const (2 * K)
  have hzero := squeeze_zero_norm' hbnd henv
  have hadd := hzero.add_const (∫ x in (-K)..K, hermiteFun (2 * n) x)
  simpa using hadd

/-! ## The profile integral over the natural window -/

/-- **The profile integral of the canonical indexed mode.** -/
theorem tendsto_indexedRung_profileIntegral (n : ℕ) :
    Tendsto (fun a : ProlatePositiveAperture =>
        ∫ x in (-Real.sqrt (indexedOscillatorBandwidth a))..
            (Real.sqrt (indexedOscillatorBandwidth a)),
          indexedRungAmplitude n * indexedOscillatorProfile n a x)
      atTop (𝓝 (∫ x, hermiteFun (2 * n) x)) := by
  set κ : ℝ := indexedRungAmplitude n with hκ
  have hκne : κ ≠ 0 := indexedRungAmplitude_ne_zero n
  set M : ℝ := 4 * (n : ℝ) + 2 with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  have hsqrt : ∀ K : ℝ, 0 < K →
      ∀ᶠ a in (atTop : Filter ProlatePositiveAperture),
        K ≤ Real.sqrt (indexedOscillatorBandwidth a) := by
    intro K hK
    filter_upwards [tendsto_indexedOscillatorBandwidth_atTop.eventually_ge_atTop (K ^ (2 : ℕ))] with a ha
    calc K = Real.sqrt (K ^ (2 : ℕ)) := (Real.sqrt_sq hK.le).symm
      _ ≤ Real.sqrt (indexedOscillatorBandwidth a) := Real.sqrt_le_sqrt ha
  have hmuM : ∀ᶠ a in (atTop : Filter ProlatePositiveAperture),
      indexedOscillatorSeparation n a ≤ M := by
    filter_upwards [(tendsto_indexedOscillatorSeparation_atTop n).eventually
      (eventually_lt_nhds (by rw [hM]; linarith : 4 * (n : ℝ) + 1 < M))] with a ha
    exact ha.le
  -- a second moment bounded uniformly in the aperture
  set Mphi : ℝ := ∫ x, hermiteFun (2 * n) x ^ (2 : ℕ) with hMphi
  set N₀ : ℝ := M * ((Mphi + 1) / κ ^ (2 : ℕ)) + 1 with hN₀
  have hMphi0 : 0 < Mphi := integral_hermiteFun_sq_pos_line (2 * n)
  have hκsq : 0 < κ ^ (2 : ℕ) := by positivity
  have hN₀pos : 0 < N₀ := by
    have : 0 ≤ M * ((Mphi + 1) / κ ^ (2 : ℕ)) := by positivity
    rw [hN₀]; linarith
  have hmom : ∀ᶠ a in (atTop : Filter ProlatePositiveAperture),
      indexedOscillatorSecondMoment n a ≤ N₀ := by
    filter_upwards [hmuM, (tendsto_indexedRung_totalMass n).eventually
      (eventually_lt_nhds (by linarith : Mphi < Mphi + 1))] with a hmu htm
    have hTM0 := indexedOscillatorTotalMass_nonneg n a
    have hTMle : indexedOscillatorTotalMass n a ≤ (Mphi + 1) / κ ^ (2 : ℕ) := by
      rw [le_div_iff₀ hκsq]
      nlinarith [htm]
    have h1 := indexedOscillatorSecondMoment_le n a
    have h2 : indexedOscillatorSeparation n a * indexedOscillatorTotalMass n a
        ≤ M * ((Mphi + 1) / κ ^ (2 : ℕ)) := by
      have hnn : 0 ≤ M := hMpos.le
      nlinarith [hmu, hTM0, hTMle]
    rw [hN₀]
    linarith
  -- the four inputs of the growing-window transfer
  refine tendsto_intervalIntegral_growing_window'
    (F := fun a x => κ * indexedOscillatorProfile n a x)
    (R := fun a => Real.sqrt (indexedOscillatorBandwidth a))
    (g := fun K => ∫ x in (-K)..K, hermiteFun (2 * n) x) ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun a u v =>
      (continuous_const.mul (continuous_indexedOscillatorProfile n a)).intervalIntegrable u v
  · intro K hK
    exact tendsto_indexedRung_windowIntegral n hK
  · exact tendsto_intervalIntegral_hermiteFun (2 * n)
  · exact hsqrt
  · intro δ hδ
    refine ⟨N₀ / (δ / (|κ| + 1)) ^ (2 : ℕ) + 1, by positivity, ?_⟩
    intro K hK0
    have hδ' : 0 < δ / (|κ| + 1) := by positivity
    have hKpos : 0 < K := lt_of_lt_of_le (by positivity) hK0
    have hcut : N₀ / (δ / (|κ| + 1)) ^ (2 : ℕ) < K := lt_of_lt_of_le (by linarith) hK0
    filter_upwards [hsqrt K hKpos, hmom] with a hKa hmoma
    have hD := signedModeRadialData_isExact_of_pos a.property n
    have hcpos : 0 < indexedOscillatorBandwidth a := indexedOscillatorBandwidth_pos a
    have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (signedModeRadialData (a : ℝ) n).R :=
      hD.2.2.2.2.2.1
    have hmomrw : (∫ ξ in (-Real.sqrt (indexedOscillatorBandwidth a))..
        (Real.sqrt (indexedOscillatorBandwidth a)),
        ξ ^ (2 : ℕ) * (normalizedProlateProfile (indexedOscillatorBandwidth a)
          (signedModeRadialData (a : ℝ) n).R ξ) ^ (2 : ℕ)) ≤ N₀ := by
      rw [show (fun ξ : ℝ => ξ ^ (2 : ℕ) * (normalizedProlateProfile (indexedOscillatorBandwidth a)
        (signedModeRadialData (a : ℝ) n).R ξ) ^ (2 : ℕ))
          = fun ξ : ℝ => ξ ^ (2 : ℕ) * (indexedOscillatorProfile n a ξ) ^ (2 : ℕ) from rfl]
      exact hmoma
    have htail := normalizedProlate_tail_lt hcpos hKpos hKa hN₀pos hδ' hcut hsm hmomrw
    have htailP : |∫ ξ in K..(Real.sqrt (indexedOscillatorBandwidth a)),
        indexedOscillatorProfile n a ξ| < δ / (|κ| + 1) := htail
    have heven : Function.Even (indexedOscillatorProfile n a) :=
      indexedOscillatorProfile_even n a
    have hscale : ∀ u v : ℝ, (∫ x in u..v, κ * indexedOscillatorProfile n a x)
        = κ * ∫ x in u..v, indexedOscillatorProfile n a x := fun u v =>
      intervalIntegral.integral_const_mul _ _
    have hbound : ∀ t : ℝ, |t| < δ / (|κ| + 1) → |κ * t| ≤ δ := by
      intro t ht
      rw [abs_mul]
      have h1 : |κ| ≤ |κ| + 1 := by linarith
      have h2 : (0 : ℝ) ≤ |t| := abs_nonneg t
      have h3 : |κ| * |t| ≤ (|κ| + 1) * (δ / (|κ| + 1)) := by
        refine mul_le_mul h1 ht.le h2 (by positivity)
      have h4 : (|κ| + 1) * (δ / (|κ| + 1)) = δ := by
        field_simp
      linarith [h3, h4]
    refine ⟨?_, ?_⟩
    · rw [hscale]
      exact hbound _ htailP
    · rw [hscale, intervalIntegral_neg_of_even heven K
        (Real.sqrt (indexedOscillatorBandwidth a))]
      exact hbound _ htailP

/-! ## The shape ratio -/

/-- **The shape ratio of the canonical indexed profile.**  The amplitude cancels, so the limit is
the Hermite shape ratio at the `2n`-th rung. -/
theorem tendsto_indexedRung_shapeRatio (n : ℕ) :
    Tendsto (fun a : ProlatePositiveAperture =>
        (∫ x in (-Real.sqrt (indexedOscillatorBandwidth a))..
            (Real.sqrt (indexedOscillatorBandwidth a)), indexedOscillatorProfile n a x) ^ (2 : ℕ)
          / ∫ x in (-Real.sqrt (indexedOscillatorBandwidth a))..
              (Real.sqrt (indexedOscillatorBandwidth a)),
            (indexedOscillatorProfile n a x) ^ (2 : ℕ))
      atTop (𝓝 ((∫ x, hermiteFun (2 * n) x) ^ (2 : ℕ) / ∫ x, hermiteFun (2 * n) x ^ (2 : ℕ))) := by
  have hκne : indexedRungAmplitude n ≠ 0 := indexedRungAmplitude_ne_zero n
  have hMphi0 : 0 < ∫ x, hermiteFun (2 * n) x ^ (2 : ℕ) := integral_hermiteFun_sq_pos_line (2 * n)
  have hnum := (tendsto_indexedRung_profileIntegral n).pow 2
  have hden := tendsto_indexedRung_totalMass n
  have hdiv := hnum.div hden hMphi0.ne'
  refine hdiv.congr fun a => ?_
  simp only [Pi.div_apply]
  have hscale : (∫ x in (-Real.sqrt (indexedOscillatorBandwidth a))..
      (Real.sqrt (indexedOscillatorBandwidth a)),
        indexedRungAmplitude n * indexedOscillatorProfile n a x)
      = indexedRungAmplitude n * ∫ x in (-Real.sqrt (indexedOscillatorBandwidth a))..
          (Real.sqrt (indexedOscillatorBandwidth a)), indexedOscillatorProfile n a x :=
    intervalIntegral.integral_const_mul _ _
  rw [hscale, indexedOscillatorTotalMass, mul_pow,
    mul_div_mul_left _ _ (pow_ne_zero 2 hκne)]

end GaloisForLFunctions.RHTower

end
