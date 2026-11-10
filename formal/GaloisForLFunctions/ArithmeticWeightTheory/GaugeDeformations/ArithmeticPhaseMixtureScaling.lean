import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.ArithmeticPhaseMixtureDivisor

/-!
# Rational scaling limit of the arithmetic mixture

The nonprincipal Taylor mass and the ramified correction vanish at the
endpoint. Uniform control of higher prime powers leaves the unit `ζ(2)`.
The exact moving divisor then yields the locally uniform rational profile
`ζ(2)(w+2)^4/(w+4)^2`, on the complement of its pole for the continuation
and on the right half-plane for the actual Euler product.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.ArithmeticGaugeTheory
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

private theorem continuousAt_mixtureFiniteCorrection {q : ℝ × ℂ} (ht : 0 ≤ q.1) :
    ContinuousAt (fun q : ℝ × ℂ => mixtureFiniteCorrection q.1 q.2) q := by
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  have ha := analyticAt_analyticSmoothingPrimePhase (R := (6 / 5 : NNReal))
    (by norm_num) analyticOnNhd_mixtureSkew p (z := (q.1 : ℂ))
    (by simpa only [Complex.ofReal_re] using ht)
  have hmap : ContinuousAt (fun v : ℝ × ℂ => (v.1 : ℂ)) q := by fun_prop
  have hS : ContinuousAt (fun v : ℝ × ℂ =>
      mixtureSkew (Complex.exp (-(v.1 : ℂ) * (Real.log 2 : ℂ)))) q := by
    simpa only [analyticSmoothingPrimePhase, p, Subtype.coe_mk, Nat.cast_ofNat] using
      ha.continuousAt.comp (g := analyticSmoothingPrimePhase mixtureSkew p)
        (f := fun v : ℝ × ℂ => (v.1 : ℂ)) hmap
  have hp : ContinuousAt (fun v : ℝ × ℂ => (2 : ℂ) ^ (-v.2)) q := by
    simpa only [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0), Pi.neg_apply] using
      ((continuousAt_snd.neg).const_mul (Complex.log 2)).cexp
  exact (hS.const_mul Complex.I).mul hp

private theorem mixture_closed_shift_mem {r R t : ℝ} (hr : 0 < r) (hrR : r ≤ R / 8)
    (ht : 0 ≤ t) (htr : t ≤ r) {s : ℂ} (hs : s ∈ closedBall (1 : ℂ) r)
    (n : ℕ) (hn : n ≤ 4) : s + (n : ℂ) * (t : ℂ) ∈ ball (1 : ℂ) R := by
  have hsr : ‖s - 1‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hs
  have hnt : (n : ℝ) * t ≤ 4 * t := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) ht
  rw [mem_ball, dist_eq_norm,
    show s + (n : ℂ) * (t : ℂ) - 1 = (s - 1) + (n : ℂ) * (t : ℂ) by ring]
  apply (norm_add_le _ _).trans_lt
  rw [norm_mul, Complex.norm_natCast, norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  linarith only [hr, hrR, htr, hsr, hnt]

/-- Joint continuity of the unit persists through the endpoint on a fixed
parameter-spectral rectangle. -/
theorem exists_continuousOn_mixtureDivisorUnit :
    ∃ r : ℝ, 0 < r ∧ ContinuousOn (fun q : ℝ × ℂ => mixtureDivisorUnit q.1 q.2)
      (Icc 0 r ×ˢ closedBall (1 : ℂ) r) := by
  obtain ⟨R, hR, hE, _⟩ := exists_primeLogRegularPart_germ
  let r := min (mixtureCharacterWidth / 4) (min (R / 8) (1 / 8))
  have hr : 0 < r := lt_min (div_pos mixtureCharacterWidth_pos (by norm_num))
    (lt_min (div_pos hR (by norm_num)) (by norm_num))
  have hrE : r ≤ R / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hr8 : r ≤ 1 / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hre : r < mixtureCharacterWidth := lt_of_le_of_lt (min_le_left _ _)
    (by linarith only [mixtureCharacterWidth_pos])
  let D : Set (ℝ × ℂ) := Icc 0 r ×ˢ closedBall (1 : ℂ) r
  have hhalf {q : ℝ × ℂ} (hq : q ∈ D) : 3 / 4 < q.2.re := by
    have hn : ‖q.2 - 1‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hq.2
    have hh := Complex.re_le_norm (1 - q.2)
    rw [norm_sub_rev] at hh
    simp only [Complex.sub_re, Complex.one_re] at hh
    linarith only [hh, hn, hr8]
  have htube {q : ℝ × ℂ} (hq : q ∈ D) :
      1 - mixtureCharacterWidth < q.2.re ∧ |q.2.im| < mixtureCharacterWidth := by
    have hb : q.2 ∈ ball (1 : ℂ) mixtureCharacterWidth :=
      (closedBall_subset_ball hre) hq.2
    exact mixture_ball_in_tube le_rfl hb
  have h2 : ContinuousOn (fun q : ℝ × ℂ => primeLogRegularPart (q.2 + 2 * (q.1 : ℂ))) D := by
    intro q hq
    have hmap : ContinuousAt (fun q : ℝ × ℂ => q.2 + 2 * (q.1 : ℂ)) q := by fun_prop
    have hs2 := mixture_closed_shift_mem hr hrE hq.1.1 hq.1.2 hq.2 2 (by norm_num)
    simp only [Nat.cast_ofNat] at hs2
    exact ((hE _ hs2).continuousAt.comp
      (g := primeLogRegularPart) (f := fun q : ℝ × ℂ => q.2 + 2 * (q.1 : ℂ)) hmap).continuousWithinAt
  have h4 : ContinuousOn (fun q : ℝ × ℂ => primeLogRegularPart (q.2 + 4 * (q.1 : ℂ))) D := by
    intro q hq
    have hmap : ContinuousAt (fun q : ℝ × ℂ => q.2 + 4 * (q.1 : ℂ)) q := by fun_prop
    have hs4 := mixture_closed_shift_mem hr hrE hq.1.1 hq.1.2 hq.2 4 (by norm_num)
    simp only [Nat.cast_ofNat] at hs4
    exact ((hE _ hs4).continuousAt.comp
      (g := primeLogRegularPart) (f := fun q : ℝ × ℂ => q.2 + 4 * (q.1 : ℂ)) hmap).continuousWithinAt
  obtain ⟨C, hC, hF, hb, _⟩ := mixtureCharacterLog_properties
  have hχ : ContinuousOn (fun q : ℝ × ℂ =>
      characterShiftSeries mixtureSkewCoefficient mixtureCharacterLog q.1 q.2) D :=
    (continuousOn_characterShiftSeries hF hb summable_norm_mixtureSkewCoefficient).mono
      (fun q hq => ⟨hq.1.1, htube hq⟩)
  have hH : ContinuousOn (fun q : ℝ × ℂ => mixtureHigherPrimeLog q.1 q.2) D :=
    (continuousOn_mixtureHigherPrimeLog (b := 3 / 4) (by norm_num)).mono
      (fun q hq => ⟨hq.1.1, hhalf hq⟩)
  have hH0 : ContinuousOn (fun q : ℝ × ℂ => hullRem q.2 (twist 0)) D := by
    intro q hq
    have hs : 1 / 2 < q.2.re := by linarith only [hhalf hq]
    exact ((analyticOnNhd_hullRem (norm_twist_prime 0) q.2 hs).continuousAt.comp
      (g := fun s : ℂ => hullRem s (twist 0)) (f := Prod.snd) continuousAt_snd).continuousWithinAt
  have hfinite : ContinuousOn (fun q : ℝ × ℂ => mixtureFiniteCorrection q.1 q.2) D :=
    fun q hq => (continuousAt_mixtureFiniteCorrection hq.1.1).continuousWithinAt
  have hZ : ContinuousOn (fun q : ℝ × ℂ => zetaResidueFactor q.2) D :=
    (differentiable_zetaResidueFactor.continuous.comp continuous_snd).continuousOn
  exact ⟨r, hr, hZ.mul ((((((h2.const_mul (-4)).add (h4.const_mul 2)).add
    (hχ.const_mul Complex.I)).add hfinite).add hH).sub hH0).cexp⟩

/-- Continuous extension of the rescaled continuation through parameter zero. -/
def normalizedMixtureProfile (t : ℝ) (w : ℂ) : ℂ :=
  mixtureDivisorUnit t (1 + (t : ℂ) * w) * (w + 2) ^ 4 / (w + 4) ^ 2

theorem normalizedMixtureProfile_zero (w : ℂ) :
    normalizedMixtureProfile 0 w = mixtureScalingProfile w := by
  simp only [normalizedMixtureProfile, Complex.ofReal_zero, zero_mul, add_zero,
    mixtureDivisorUnit_endpoint, mixtureScalingProfile]

theorem mixtureContinuation_scaled {t : ℝ} (ht : t ≠ 0) {w : ℂ} (hw : w + 4 ≠ 0) :
    mixtureContinuation t (1 + (t : ℂ) * w) / (t : ℂ) ^ 2 = normalizedMixtureProfile t w := by
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  rw [mixtureContinuation, normalizedMixtureProfile,
    show 1 + (t : ℂ) * w - (1 - 2 * (t : ℂ)) = (t : ℂ) * (w + 2) by ring,
    show 1 + (t : ℂ) * w - (1 - 4 * (t : ℂ)) = (t : ℂ) * (w + 4) by ring,
    mul_pow, mul_pow]
  field_simp [htC, hw]

/-- Uniform continuity on compact parameter-spectral sets gives the complete
rational scaling limit away from its single pole. -/
theorem tendstoUniformlyOn_normalizedMixtureProfile {K : Set ℂ} (hK : IsCompact K)
    (havoid : K ⊆ {w : ℂ | w ≠ -4}) :
    TendstoUniformlyOn normalizedMixtureProfile mixtureScalingProfile (𝓝[>] (0 : ℝ)) K := by
  obtain ⟨r, hr, hc⟩ := exists_continuousOn_mixtureDivisorUnit
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (continuous_id.continuousOn : ContinuousOn (fun w : ℂ => w) K)
  let M := max B 1
  have hM : 1 ≤ M := le_max_right _ _
  have hMw (w : ℂ) (hw : w ∈ K) : ‖w‖ ≤ M := (hB w hw).trans (le_max_left _ _)
  have hMp : 0 < M + 1 := by linarith only [hM]
  let a := min r (r / (M + 1))
  have ha : 0 < a := lt_min hr (div_pos hr hMp)
  have har : a ≤ r := min_le_left _ _
  have ham : a * (M + 1) ≤ r := (le_div_iff₀ hMp).mp (min_le_right _ _)
  let D : Set (ℝ × ℂ) := Icc 0 a ×ˢ K
  have hmap : Continuous (fun q : ℝ × ℂ => (q.1, 1 + (q.1 : ℂ) * q.2)) := by fun_prop
  have hmaps : MapsTo (fun q : ℝ × ℂ => (q.1, 1 + (q.1 : ℂ) * q.2)) D
      (Icc 0 r ×ˢ closedBall (1 : ℂ) r) := by
    intro q hq
    refine ⟨⟨hq.1.1, hq.1.2.trans har⟩, ?_⟩
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_real,
      Real.norm_eq_abs, abs_of_nonneg hq.1.1]
    have hm := mul_le_mul hq.1.2 (hMw q.2 hq.2) (norm_nonneg q.2) ha.le
    linarith only [hm, ham, ha]
  have hAc := hc.comp hmap.continuousOn hmaps
  have hcont : ContinuousOn (fun q : ℝ × ℂ => normalizedMixtureProfile q.1 q.2) D := by
    intro q hq
    have hden : q.2 + 4 ≠ 0 := by
      intro he
      apply havoid hq.2
      linear_combination he
    exact ((hAc q hq).mul ((continuousAt_snd.add continuousAt_const).pow 4).continuousWithinAt).div
      ((continuousAt_snd.add continuousAt_const).pow 2).continuousWithinAt (pow_ne_zero 2 hden)
  have hu : TendstoUniformlyOn normalizedMixtureProfile (normalizedMixtureProfile 0)
      (𝓝[Icc (0 : ℝ) a] 0) K :=
    ((isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hcont).tendstoUniformlyOn
      ⟨le_rfl, ha.le⟩
  have hu' : TendstoUniformlyOn normalizedMixtureProfile (normalizedMixtureProfile 0)
      (𝓝[>] (0 : ℝ)) K := fun V hV =>
    Filter.Eventually.filter_mono (nhdsGT_zero_le_Icc ha) (hu V hV)
  rwa [show normalizedMixtureProfile 0 = mixtureScalingProfile from funext normalizedMixtureProfile_zero] at hu'

/-- The full meromorphic continuation has a rational nearby profile on the
complement of the limiting pole. -/
theorem tendstoLocallyUniformlyOn_mixtureContinuation :
    TendstoLocallyUniformlyOn
      (fun t : ℝ => fun w : ℂ => mixtureContinuation t (1 + (t : ℂ) * w) / (t : ℂ) ^ 2)
      mixtureScalingProfile (𝓝[>] (0 : ℝ)) {w : ℂ | w ≠ -4} := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_compl_singleton : IsOpen ({(-4 : ℂ)}ᶜ))).mpr
  intro K havoid hK
  have hu := tendstoUniformlyOn_normalizedMixtureProfile hK havoid
  intro V hV
  filter_upwards [hu V hV, self_mem_nhdsWithin] with t htlim ht
  change 0 < t at ht
  intro w hw
  have hden : w + 4 ≠ 0 := by
    intro he
    apply havoid hw
    linear_combination he
  rw [mixtureContinuation_scaled ht.ne' hden]
  exact htlim w hw

/-- On the right half-plane the rational scaling limit belongs to the actual
arithmetic Euler product, not merely its meromorphic continuation. -/
theorem tendstoLocallyUniformlyOn_mixtureEuler :
    TendstoLocallyUniformlyOn
      (fun t : ℝ => fun w : ℂ =>
        ((1 + (t : ℂ) * w - 1) * gaugeFibre (mixturePhaseGauge t) (1 + (t : ℂ) * w)) /
          (t : ℂ) ^ 2)
      mixtureScalingProfile (𝓝[>] (0 : ℝ)) {w : ℂ | 0 < w.re} := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_lt continuous_const Complex.continuous_re)).mpr
  intro K hright hK
  have havoid : K ⊆ {w : ℂ | w ≠ -4} := by
    intro w hw he
    have hh : 0 < w.re := hright hw
    rw [he] at hh
    norm_num at hh
  have hu := tendstoUniformlyOn_normalizedMixtureProfile hK havoid
  obtain ⟨R, hR, he⟩ := mixtureEuler_factorization
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (continuous_id.continuousOn : ContinuousOn (fun w : ℂ => w) K)
  let M := max B 1
  have hM : 1 ≤ M := le_max_right _ _
  have hMw (w : ℂ) (hw : w ∈ K) : ‖w‖ ≤ M := (hB w hw).trans (le_max_left _ _)
  have hMp : 0 < M + 5 := by linarith only [hM]
  let a := R / (M + 5)
  have ha : 0 < a := div_pos hR hMp
  intro V hV
  filter_upwards [hu V hV, self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds ha)] with t hlim ht hta
  change 0 < t at ht
  intro w hw
  have htr : t * (M + 5) < R := (lt_div_iff₀ hMp).mp hta
  have hshift (n : ℕ) (hn : n ≤ 4) :
      1 + (t : ℂ) * w + (n : ℂ) * (t : ℂ) ∈ ball (1 : ℂ) R := by
    rw [mem_ball, dist_eq_norm,
      show 1 + (t : ℂ) * w + (n : ℂ) * (t : ℂ) - 1 = (t : ℂ) * (w + (n : ℂ)) by ring,
      norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos ht]
    have hnorm : ‖w + (n : ℂ)‖ ≤ M + 5 := by
      apply (norm_add_le _ _).trans
      rw [Complex.norm_natCast]
      have hnR : (n : ℝ) ≤ 4 := by exact_mod_cast hn
      linarith only [hMw w hw, hnR]
    exact (mul_le_mul_of_nonneg_left hnorm ht.le).trans_lt htr
  have hRe : 1 < (1 + (t : ℂ) * w).re := by
    have hwRe : 0 < w.re := hright hw
    have hm := mul_pos ht hwRe
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    linarith only [hm]
  have hs2 := hshift 2 (by norm_num)
  have hs4 := hshift 4 (by norm_num)
  simp only [Nat.cast_ofNat] at hs2 hs4
  have hEuler := he t ht.le (1 + (t : ℂ) * w) hs2 hs4 hRe
  have hden : w + 4 ≠ 0 := by
    intro hz
    apply havoid hw
    linear_combination hz
  rw [hEuler, mixtureContinuation_scaled ht.ne' hden]
  exact hlim w hw

#print axioms exists_continuousOn_mixtureDivisorUnit
#print axioms tendstoLocallyUniformlyOn_mixtureContinuation
#print axioms tendstoLocallyUniformlyOn_mixtureEuler
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
