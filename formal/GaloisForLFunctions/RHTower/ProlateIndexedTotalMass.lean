import GaloisForLFunctions.RHTower.ProlateIndexedProfileRungLimit
import GaloisForLFunctions.RHTower.ProlateGroundTotalMass
import GaloisForLFunctions.HTGeometry.WindowTotalSqueeze

/-!
# The total mass of the canonical indexed prolate profile

The window mass of the `n`-th canonical even prolate mode converges to the window mass of the
`2n`-th Hermite function, and the tails are controlled by the second moment, which the aperture
virial bounds by the separation constant.  The window–total squeeze then identifies the total mass
over the natural window `[−√c, √c]` with the whole-line mass of the Hermite rung:

```text
φ_{2n}(0)² · ∫_{−√c}^{√c} Ψ_{n}²  →  ∫_ℝ φ_{2n}² .
```

This is the excited-rung counterpart of the ground total mass, and it is the analytic input the
constrained-prolate coordinate limit consumes at every index: the normalization step is already
discharged for all modes at once, so only the profile mass of the mode itself is needed.

The window comparison is quantitative rather than dominated: the Grönwall envelope bounds the
distance to the Hermite rung uniformly on the window, and a difference of squares is that distance
times a uniform amplitude.  No countable generation of the aperture filter is used.
-/

noncomputable section

open MeasureTheory Set Filter Topology GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- A difference of squares of bounded quantities is the distance times twice the bound. -/
theorem abs_sq_sub_sq_le {u v B : ℝ} (hu : |u| ≤ B) (hv : |v| ≤ B) :
    |u ^ 2 - v ^ 2| ≤ 2 * B * |u - v| := by
  have hfac : u ^ 2 - v ^ 2 = (u - v) * (u + v) := by ring
  have hsum : |u + v| ≤ 2 * B := le_trans (abs_add u v) (by linarith)
  rw [hfac, abs_mul]
  have hnn : (0 : ℝ) ≤ |u - v| := abs_nonneg _
  nlinarith [hnn, abs_nonneg (u + v)]

theorem continuous_indexedOscillatorProfile (n : ℕ) (a : ProlatePositiveAperture) :
    Continuous (indexedOscillatorProfile n a) :=
  fun_prop_continuous
where
  fun_prop_continuous : Continuous (indexedOscillatorProfile n a) := by
    have hd : Differentiable ℝ (indexedOscillatorProfile n a) := fun x =>
      (indexedOscillatorProfile_hasDerivAt n a x).differentiableAt
    exact hd.continuous

/-- The amplitude scaling used to match the Hermite initial phase vector. -/
def indexedRungAmplitude (n : ℕ) : ℝ := hermiteFun (2 * n) 0

/-- The uniform window bound of the rescaled canonical profile. -/
def indexedRungWindowBound (n : ℕ) (K : ℝ) : ℝ :=
  |indexedRungAmplitude n| * indexedOscillatorWindowBound (4 * (n : ℝ) + 2) K

theorem indexedRungWindowBound_nonneg (n : ℕ) (K : ℝ) : 0 ≤ indexedRungWindowBound n K :=
  mul_nonneg (abs_nonneg _) (indexedOscillatorWindowBound_nonneg _ _)

/-- The Grönwall envelope of the window comparison at the `2n`-th rung. -/
def indexedRungEnvelope (n : ℕ) (K : ℝ) (a : ProlatePositiveAperture) : ℝ :=
  ((prolateWindowEpsP (indexedOscillatorBandwidth a) (indexedOscillatorSeparation n a) K (2 * n)
      + prolateWindowEpsQ (indexedOscillatorBandwidth a) K) * indexedRungWindowBound n K
    / max 1 (hermiteWindowBound K (2 * n)))
    * (Real.exp (max 1 (hermiteWindowBound K (2 * n)) * (K - 0)) - 1)

theorem tendsto_indexedRungEnvelope (n : ℕ) (K : ℝ) :
    Tendsto (indexedRungEnvelope n K) atTop (𝓝 0) := by
  have hmu' : Tendsto (indexedOscillatorSeparation n) atTop (𝓝 (2 * ((2 * n : ℕ) : ℝ) + 1)) := by
    have hval : 2 * ((2 * n : ℕ) : ℝ) + 1 = 4 * (n : ℝ) + 1 := by push_cast; ring
    rw [hval]
    exact tendsto_indexedOscillatorSeparation_atTop n
  exact tendsto_prolateWindow_envelope (mu := indexedOscillatorSeparation n)
    (c := indexedOscillatorBandwidth) (K := K) (B := indexedRungWindowBound n K) (n := 2 * n)
    hmu' tendsto_indexedOscillatorBandwidth_atTop

/-- **The window distance to the Hermite rung, eventually.**  On the whole symmetric window the
rescaled canonical profile stays within the Grönwall envelope of the `2n`-th Hermite function; the
negative half is the reflection of the positive half, both functions being even. -/
theorem eventually_indexedRung_windowDist (n : ℕ) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ a in (atTop : Filter ProlatePositiveAperture), ∀ x ∈ Icc (-K) K,
      |indexedRungAmplitude n * indexedOscillatorProfile n a x - hermiteFun (2 * n) x|
        ≤ indexedRungEnvelope n K a := by
  set κ : ℝ := indexedRungAmplitude n with hκ
  have heven : Even (2 * n) := ⟨n, by ring⟩
  have hgood := eventually_indexedOscillatorProfile_windowBound
    (M := 4 * (n : ℝ) + 2) (m := 4 * (n : ℝ) + 1) (by positivity) n
    (tendsto_indexedOscillatorSeparation_atTop n) (by linarith)
    tendsto_indexedOscillatorBandwidth_atTop hK
  filter_upwards [hgood] with a ha
  have hpos : ∀ x ∈ Icc (0 : ℝ) K,
      |κ * indexedOscillatorProfile n a x - hermiteFun (2 * n) x|
        ≤ indexedRungEnvelope n K a := by
    have hB : ∀ x ∈ Icc (0 : ℝ) K,
        max |κ * indexedOscillatorProfile n a x| |κ * indexedOscillatorProfileDeriv n a x|
          ≤ indexedRungWindowBound n K := by
      intro x hx
      have hb := ha.2.2.2.1 x hx
      have hP : |indexedOscillatorProfile n a x|
          ≤ indexedOscillatorWindowBound (4 * (n : ℝ) + 2) K := le_trans (le_max_left _ _) hb
      have hP' : |indexedOscillatorProfileDeriv n a x|
          ≤ indexedOscillatorWindowBound (4 * (n : ℝ) + 2) K := le_trans (le_max_right _ _) hb
      refine max_le ?_ ?_
      · rw [abs_mul, indexedRungWindowBound]
        exact mul_le_mul_of_nonneg_left hP (abs_nonneg κ)
      · rw [abs_mul, indexedRungWindowBound]
        exact mul_le_mul_of_nonneg_left hP' (abs_nonneg κ)
    have hdist := prolateProfile_window_hermiteRung_dist_le (n := 2 * n)
      (u := fun x => κ * indexedOscillatorProfile n a x)
      (u' := fun x => κ * indexedOscillatorProfileDeriv n a x)
      (u'' := fun x => κ * indexedOscillatorProfileDeriv2 n a x)
      (B := indexedRungWindowBound n K) hK ha.2.1
      (fun x => (indexedOscillatorProfile_hasDerivAt n a x).const_mul κ)
      (fun x => (indexedOscillatorProfileDeriv_hasDerivAt n a x).const_mul κ)
      (fun x hx => by rw [ha.2.2.1 x hx]; ring) hB
      (by rw [ha.2.2.2.2.1, hκ, indexedRungAmplitude]; ring)
      (by rw [ha.2.2.2.2.2, deriv_hermiteFun_zero_of_even heven]; ring)
    intro x hx
    exact le_trans (le_max_left _ _) (hdist x hx)
  intro x hx
  rcases le_or_gt 0 x with hx0 | hx0
  · exact hpos x ⟨hx0, hx.2⟩
  · have hneg : -x ∈ Icc (0 : ℝ) K := ⟨by linarith, by linarith [hx.1]⟩
    have hP := indexedOscillatorProfile_even n a x
    have hH := even_hermiteFun heven x
    have h := hpos (-x) hneg
    rwa [hP, hH] at h

/-- **The window mass converges to the Hermite window mass.** -/
theorem tendsto_indexedRung_windowMass (n : ℕ) {K : ℝ} (hK : 0 < K) :
    Tendsto (fun a : ProlatePositiveAperture =>
        ∫ x in (-K)..K, (indexedRungAmplitude n * indexedOscillatorProfile n a x) ^ 2)
      atTop (𝓝 (∫ x in (-K)..K, hermiteFun (2 * n) x ^ 2)) := by
  set κ : ℝ := indexedRungAmplitude n with hκ
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ Icc (-K) K, |hermiteFun (2 * n) x| ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := -K) (b := K)).exists_bound_of_continuousOn
      (continuous_hermiteFun (2 * n)).continuousOn
    exact ⟨C, fun x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩
  set Bmax : ℝ := max (indexedRungWindowBound n K) C with hBmax
  have hBmax0 : 0 ≤ Bmax := le_trans (indexedRungWindowBound_nonneg n K) (le_max_left _ _)
  have hgood := eventually_indexedOscillatorProfile_windowBound
    (M := 4 * (n : ℝ) + 2) (m := 4 * (n : ℝ) + 1) (by positivity) n
    (tendsto_indexedOscillatorSeparation_atTop n) (by linarith)
    tendsto_indexedOscillatorBandwidth_atTop hK
  have heven : Even (2 * n) := ⟨n, by ring⟩
  have hbnd : ∀ᶠ a in (atTop : Filter ProlatePositiveAperture),
      ‖(∫ x in (-K)..K, (κ * indexedOscillatorProfile n a x) ^ 2)
        - ∫ x in (-K)..K, hermiteFun (2 * n) x ^ 2‖
        ≤ (2 * Bmax * indexedRungEnvelope n K a) * (2 * K) := by
    filter_upwards [hgood, eventually_indexedRung_windowDist n hK] with a ha hdist
    have hAmp : ∀ x ∈ Icc (-K) K, |κ * indexedOscillatorProfile n a x| ≤ Bmax := by
      have hpos : ∀ x ∈ Icc (0 : ℝ) K, |κ * indexedOscillatorProfile n a x| ≤ Bmax := by
        intro x hx
        have hb := ha.2.2.2.1 x hx
        have hP : |indexedOscillatorProfile n a x|
            ≤ indexedOscillatorWindowBound (4 * (n : ℝ) + 2) K := le_trans (le_max_left _ _) hb
        rw [abs_mul]
        refine le_trans ?_ (le_max_left _ _)
        rw [indexedRungWindowBound]
        exact mul_le_mul_of_nonneg_left hP (abs_nonneg κ)
      intro x hx
      rcases le_or_gt 0 x with hx0 | hx0
      · exact hpos x ⟨hx0, hx.2⟩
      · have hneg : -x ∈ Icc (0 : ℝ) K := ⟨by linarith, by linarith [hx.1]⟩
        have hP := indexedOscillatorProfile_even n a x
        have h := hpos (-x) hneg
        rwa [hP] at h
    have hsub : (∫ x in (-K)..K, (κ * indexedOscillatorProfile n a x) ^ 2)
        - (∫ x in (-K)..K, hermiteFun (2 * n) x ^ 2)
        = ∫ x in (-K)..K, ((κ * indexedOscillatorProfile n a x) ^ 2
            - hermiteFun (2 * n) x ^ 2) := by
      rw [← intervalIntegral.integral_sub]
      · exact ((continuous_const.mul (continuous_indexedOscillatorProfile n a)).pow
          2).intervalIntegrable _ _
      · exact ((continuous_hermiteFun (2 * n)).pow 2).intervalIntegrable _ _
    rw [hsub]
    have hptwise : ∀ x ∈ uIoc (-K) K,
        ‖(κ * indexedOscillatorProfile n a x) ^ 2 - hermiteFun (2 * n) x ^ 2‖
          ≤ 2 * Bmax * indexedRungEnvelope n K a := by
      intro x hx
      have hxIcc : x ∈ Icc (-K) K := by
        rw [uIoc_of_le (by linarith : (-K : ℝ) ≤ K)] at hx
        exact ⟨le_of_lt hx.1, hx.2⟩
      have h1 : |κ * indexedOscillatorProfile n a x| ≤ Bmax := hAmp x hxIcc
      have h2 : |hermiteFun (2 * n) x| ≤ Bmax := le_trans (hC x hxIcc) (le_max_right _ _)
      have h3 := abs_sq_sub_sq_le h1 h2
      have h4 := hdist x hxIcc
      rw [Real.norm_eq_abs]
      refine le_trans h3 ?_
      exact mul_le_mul_of_nonneg_left h4 (by linarith)
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const hptwise
    have habs : |K - -K| = 2 * K := by
      rw [show K - -K = 2 * K from by ring, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * K)]
    rwa [habs] at hle
  have henv : Tendsto (fun a : ProlatePositiveAperture =>
      (2 * Bmax * indexedRungEnvelope n K a) * (2 * K)) atTop (𝓝 0) := by
    have h := ((tendsto_indexedRungEnvelope n K).const_mul (2 * Bmax)).mul_const (2 * K)
    simpa using h
  have hzero := squeeze_zero_norm' hbnd henv
  have hadd := hzero.add_const (∫ x in (-K)..K, hermiteFun (2 * n) x ^ 2)
  simpa using hadd

/-- **The total mass of the canonical indexed profile.**  The window–total squeeze identifies the
mass over the natural window with the whole-line mass of the Hermite rung. -/
theorem tendsto_indexedRung_totalMass (n : ℕ) :
    Tendsto (fun a : ProlatePositiveAperture =>
        indexedRungAmplitude n ^ 2 * indexedOscillatorTotalMass n a)
      atTop (𝓝 (∫ x, hermiteFun (2 * n) x ^ 2)) := by
  set κ : ℝ := indexedRungAmplitude n with hκ
  set M : ℝ := 4 * (n : ℝ) + 2 with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  have hsqrt : ∀ K : ℝ, 0 < K →
      ∀ᶠ a in (atTop : Filter ProlatePositiveAperture),
        K ≤ Real.sqrt (indexedOscillatorBandwidth a) := by
    intro K hK
    filter_upwards [tendsto_indexedOscillatorBandwidth_atTop.eventually_ge_atTop (K ^ 2)] with a ha
    calc K = Real.sqrt (K ^ 2) := (Real.sqrt_sq hK.le).symm
      _ ≤ Real.sqrt (indexedOscillatorBandwidth a) := Real.sqrt_le_sqrt ha
  have hmuM : ∀ᶠ a in (atTop : Filter ProlatePositiveAperture),
      indexedOscillatorSeparation n a ≤ M := by
    filter_upwards [(tendsto_indexedOscillatorSeparation_atTop n).eventually
      (eventually_lt_nhds (by rw [hM]; linarith : 4 * (n : ℝ) + 1 < M))] with a ha
    exact ha.le
  refine tendsto_total_of_window (M := M)
    (N := fun a => κ ^ 2 * indexedOscillatorTotalMass n a)
    (W := fun K a => ∫ x in (-K)..K, (κ * indexedOscillatorProfile n a x) ^ 2)
    (G := fun K => ∫ x in (-K)..K, hermiteFun (2 * n) x ^ 2)
    hMpos ?_ ?_ ?_ ?_
  · intro K hK _
    filter_upwards [hsqrt K hK] with a hKa
    have hbase := window_le_total (f := indexedOscillatorProfile n a) hKa
      (continuous_indexedOscillatorProfile n a)
    have hrw : ∀ R : ℝ, (∫ x in (-R)..R, (κ * indexedOscillatorProfile n a x) ^ 2)
        = κ ^ 2 * ∫ x in (-R)..R, (indexedOscillatorProfile n a x) ^ 2 := by
      intro R
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun x _ => by ring
    rw [hrw K, indexedOscillatorTotalMass]
    exact mul_le_mul_of_nonneg_left hbase (sq_nonneg κ)
  · intro K hK hKM
    filter_upwards [hsqrt K hK, hmuM] with a hKa hmu
    have htail := window_tail_le_of_secondMoment (f := indexedOscillatorProfile n a)
      (K := K) (R := Real.sqrt (indexedOscillatorBandwidth a)) hK hKa
      (continuous_indexedOscillatorProfile n a)
    have hmom := indexedOscillatorSecondMoment_le n a
    have hTM := indexedOscillatorTotalMass_nonneg n a
    have hK2 : (0 : ℝ) < K ^ 2 := by positivity
    have hbase : indexedOscillatorTotalMass n a * (1 - M / K ^ 2)
        ≤ ∫ x in (-K)..K, (indexedOscillatorProfile n a x) ^ 2 := by
      have h1 : indexedOscillatorTotalMass n a
          - (∫ x in (-K)..K, (indexedOscillatorProfile n a x) ^ 2)
          ≤ (1 / K ^ 2) * indexedOscillatorSecondMoment n a := by
        rw [indexedOscillatorTotalMass, indexedOscillatorSecondMoment]
        exact htail
      have h2 : indexedOscillatorSecondMoment n a ≤ M * indexedOscillatorTotalMass n a :=
        le_trans hmom (mul_le_mul_of_nonneg_right hmu hTM)
      have h3 : (1 / K ^ 2) * indexedOscillatorSecondMoment n a
          ≤ (1 / K ^ 2) * (M * indexedOscillatorTotalMass n a) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have hdiv : (1 / K ^ 2) * (M * indexedOscillatorTotalMass n a)
          = (M / K ^ 2) * indexedOscillatorTotalMass n a := by field_simp
      rw [hdiv] at h3
      nlinarith [h1, h3]
    have hrw : (∫ x in (-K)..K, (κ * indexedOscillatorProfile n a x) ^ 2)
        = κ ^ 2 * ∫ x in (-K)..K, (indexedOscillatorProfile n a x) ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun x _ => by ring
    rw [hrw]
    have := mul_le_mul_of_nonneg_left hbase (sq_nonneg κ)
    nlinarith [this, sq_nonneg κ]
  · intro K hK _
    exact tendsto_indexedRung_windowMass n hK
  · exact intervalIntegral_tendsto_integral (integrable_hermiteFun_sq (2 * n))
      tendsto_neg_atTop_atBot tendsto_id

end GaloisForLFunctions.RHTower

end
