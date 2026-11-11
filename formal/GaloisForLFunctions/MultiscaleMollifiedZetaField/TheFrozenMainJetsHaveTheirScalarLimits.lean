import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheFrozenMainJetsObeyTheProductRule
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheThreeProfileScalarIsTheLevinsonConstant
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheDetectorMainUsesThreeFixedProfiles

/-!
# Scalar limits of the actual frozen main terms

Arithmetic and pole jets converge independently of the taper. Its mass
need only be bounded relative to the block scale. Multiplication by that
bounded mass preserves every vanishing coefficient error.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open RHTower.ZetaGateProductAFE GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

private theorem tendsto_zero_mul_bounded {ι : Type*} {l : Filter ι}
    {f g : ι → ℝ} (hf : Tendsto f l (𝓝 0)) {B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ᶠ i in l, |g i| ≤ B) : Tendsto (fun i => f i * g i) l (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  let δ := ε / (B + 1)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδB : δ * B < ε := by
    have he : δ * (B + 1) = ε := by
      dsimp only [δ]
      field_simp [show B + 1 ≠ 0 by positivity]
    nlinarith only [he, hδ]
  filter_upwards [hf.eventually (Metric.ball_mem_nhds 0 hδ), hg] with i hi hgi
  have hfi : |f i| < δ := by simpa only [mem_ball, Real.dist_eq, sub_zero] using hi
  rw [Real.dist_eq, sub_zero, abs_mul]
  exact (mul_le_mul hfi.le hgi (abs_nonneg _) (by positivity)).trans_lt hδB

private theorem tendsto_triple_scaled_error {ι : Type*} {l : Filter ι}
    {a b c W M : ι → ℝ} {A B C K : ℝ}
    (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
    (hc : Tendsto (fun i => (c i - W i * C) / M i) l (𝓝 0))
    (hK : 0 ≤ K) (hW : ∀ᶠ i in l, |W i / M i| ≤ K) :
    Tendsto (fun i => (a i * b i * c i - W i * (A * B * C)) / M i) l (𝓝 0) := by
  have hab : Tendsto (fun i => a i * b i - A * B) l (𝓝 0) := by
    simpa only [sub_self] using (ha.mul hb).sub_const (A * B)
  have h0 := (ha.mul hb).mul hc
  have h1 := (tendsto_zero_mul_bounded hab hK hW).mul_const C
  have hh := h0.add h1
  simp only [mul_zero, zero_mul, zero_add] at hh
  convert hh using 1
  funext i
  ring

/-- Real reflected-integral errors inherit the complex conductor-jet limit. -/
theorem tendsto_realNormalizedChiTaperJet_error
    {ι : Type*} {l : Filter ι} {L p q η u M : ι → ℝ}
    (hL : Tendsto L l atTop) (hp : Tendsto (fun i => p i - η i) l atTop)
    {τ u₀ B : ℝ} (hu : Tendsto u l (𝓝 u₀)) (hu₀ : 0 < u₀) (hB : 0 ≤ B)
    (hτa : Tendsto (fun i => Real.log ((p i - η i) / (2 * Real.pi)) / L i) l (𝓝 τ))
    (hτb : Tendsto (fun i => Real.log ((q i + η i) / (2 * Real.pi)) / L i) l (𝓝 τ))
    (hgeom : ∀ᶠ i in l, 0 < η i ∧ p i ≤ q i ∧ 0 < M i ∧
      (q i - p i + 2 * η i) / M i ≤ B) (j : ℕ) :
    Tendsto (fun i => (realNormalizedChiTaperJet (L i) (p i) (q i) (η i) j (u i) -
      (∫ t, blockWindow (p i) (q i) (η i) t) * ((2 * τ) ^ j * Real.exp (2 * τ * u₀))) / M i)
      l (𝓝 0) := by
  have hh := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_normalizedChiTaperJet_error hL hp hu hu₀ hB hτa hτb hgeom j)
  have he : (2 * (τ : ℂ)) ^ j * Complex.exp (2 * (τ : ℂ) * (u₀ : ℂ)) =
      (((2 * τ) ^ j * Real.exp (2 * τ * u₀) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp, Complex.ofReal_ofNat]
  simpa only [Function.comp_def, he, Complex.div_ofReal_re, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re,
    realNormalizedChiTaperJet] using hh

private theorem eventually_taper_mass_bound {ι : Type*} {l : Filter ι}
    {p q η M : ι → ℝ} {B : ℝ}
    (hgeom : ∀ᶠ i in l, 0 < η i ∧ p i ≤ q i ∧ 0 < M i ∧
      (q i - p i + 2 * η i) / M i ≤ B) :
    ∀ᶠ i in l, |(∫ t, blockWindow (p i) (q i) (η i) t) / M i| ≤ B := by
  filter_upwards [hgeom] with i hi
  rw [abs_of_nonneg (div_nonneg (integral_blockWindow_nonneg _ _ _) hi.2.2.1.le)]
  exact (div_le_div_of_nonneg_right (integral_blockWindow_le hi.1 hi.2.1) hi.2.2.1.le).trans hi.2.2.2

/-- The actual frozen main value approaches its scalar times the actual taper mass. -/
theorem tendsto_normalizedFrozenMainJet_zero_error (P : ℝ[X]) (hP : P.eval 0 = 0)
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} (hn : Tendsto n l atTop)
    {p q η u M : ι → ℝ} (hp : Tendsto (fun i => p i - η i) l atTop)
    {τ u₀ B : ℝ} (hu : Tendsto u l (𝓝 u₀)) (hu₀ : 0 < u₀) (hB : 0 ≤ B)
    (hτa : Tendsto (fun i => Real.log ((p i - η i) / (2 * Real.pi)) / Real.log (n i)) l (𝓝 τ))
    (hτb : Tendsto (fun i => Real.log ((q i + η i) / (2 * Real.pi)) / Real.log (n i)) l (𝓝 τ))
    (hgeom : ∀ᶠ i in l, 0 < η i ∧ p i ≤ q i ∧ 0 < M i ∧
      (q i - p i + 2 * η i) / M i ≤ B) :
    Tendsto (fun i => (normalizedFrozenMainJet P.eval (n i) (u i) (p i) (q i) (η i) 0 0 -
      (∫ t, blockWindow (p i) (q i) (η i) t) * frozenMainScalarValue P u₀ τ) / M i) l (𝓝 0) := by
  have hL : Tendsto (fun i => Real.log (n i : ℝ)) l atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)
  have hd : Tendsto (fun i => frozenDirectGcd P.eval (n i) (u i) 0) l
      (𝓝 (polynomialProfilePairIntegral P P u₀ 0)) := by
    simpa only [polynomialProfilePairIntegral, pow_zero, one_mul, pow_two] using
      (tendsto_frozenDirectGcd_first_three P hP hn hu).1
  have hr : Tendsto (fun i => frozenReflectedGcd P.eval (n i) (u i) 0) l
      (𝓝 (polynomialProfilePairIntegral P P (-u₀) 0)) := by
    simpa only [polynomialProfilePairIntegral, pow_zero, one_mul, pow_two] using
      (tendsto_frozenReflectedGcd_first_three P hP hn hu).1
  have hpd := tendsto_scaledZetaPoleValue (by norm_num : (-2 : ℝ) ≠ 0) hL hu hu₀.ne'
  have hpr := tendsto_scaledZetaPoleValue (by norm_num : (2 : ℝ) ≠ 0) hL hu hu₀.ne'
  have hW := eventually_taper_mass_bound hgeom
  have hc := tendsto_realNormalizedChiTaperJet_error hL hp hu hu₀ hB hτa hτb hgeom 0
  simp only [pow_zero, one_mul] at hc
  have hmass : Tendsto (fun i => ((∫ t, blockWindow (p i) (q i) (η i) t) -
      (∫ t, blockWindow (p i) (q i) (η i) t) * 1) / M i) l (𝓝 0) := by
    simpa only [mul_one, sub_self, zero_div] using (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ)) l (𝓝 0))
  have hsum := (tendsto_triple_scaled_error hd hpd hmass hB hW).add
    (tendsto_triple_scaled_error hr hpr hc hB hW)
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [hn.eventually_ge_atTop 2, hgeom] with i hi hgi
  rw [normalizedFrozenMainJet_zero_eq (by omega : 1 < n i), add_zero,
    ← realNormalizedChiTaperJet_zero]
  unfold frozenMainScalarValue
  field_simp [hu₀.ne', hgi.2.2.1.ne']
  ring

/-- The explicit first and second scaled pole jets converge along every diverging scale. -/
theorem tendsto_pole_explicit_jets {κ : ℝ} (hκ : κ ≠ 0)
    {ι : Type*} {l : Filter ι} {L u : ι → ℝ} {u₀ : ℝ}
    (hL : Tendsto L l atTop) (hu : Tendsto u l (𝓝 u₀)) (hu₀ : u₀ ≠ 0) :
    Tendsto (fun i => scaledZetaPoleFirstJet (L i) κ (u i)) l (𝓝 (-1 / (κ * u₀ ^ 2))) ∧
    Tendsto (fun i => scaledZetaPoleSecondJet (L i) κ (u i)) l (𝓝 (2 / (κ * u₀ ^ 3))) := by
  obtain ⟨h1, h2⟩ := tendsto_scaledZetaPoleValue_derivatives hκ hL hu hu₀
  constructor
  · apply h1.congr'
    filter_upwards [hL.eventually_gt_atTop 0, hu.eventually_ne hu₀] with i hLi hui
    exact (hasDerivAt_scaledZetaPoleValue hLi.ne' hκ hui).deriv
  · apply h2.congr'
    filter_upwards [hL.eventually_gt_atTop 0, hu.eventually_ne hu₀] with i hLi hui
    exact (scaledZetaPoleValue_derivatives hLi.ne' hκ hui).2

/-- Both actual normalized displacement derivatives have their scalar limits at bounded relative mass. -/
theorem tendsto_normalizedFrozenMainJet_derivative_errors (P : ℝ[X]) (hP : P.eval 0 = 0)
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} (hn : Tendsto n l atTop)
    {p q η u M : ι → ℝ} (hp : Tendsto (fun i => p i - η i) l atTop)
    {τ u₀ B : ℝ} (hu : Tendsto u l (𝓝 u₀)) (hu₀ : 0 < u₀) (hB : 0 ≤ B)
    (hτa : Tendsto (fun i => Real.log ((p i - η i) / (2 * Real.pi)) / Real.log (n i)) l (𝓝 τ))
    (hτb : Tendsto (fun i => Real.log ((q i + η i) / (2 * Real.pi)) / Real.log (n i)) l (𝓝 τ))
    (hgeom : ∀ᶠ i in l, 0 < η i ∧ p i ≤ q i ∧ 0 < M i ∧
      (q i - p i + 2 * η i) / M i ≤ B) :
    Tendsto (fun i => (normalizedFrozenMainJet P.eval (n i) (u i) (p i) (q i) (η i) 1 0 -
      (∫ t, blockWindow (p i) (q i) (η i) t) * frozenMainScalarFirst P u₀ τ) / M i) l (𝓝 0) ∧
    Tendsto (fun i => (normalizedFrozenMainJet P.eval (n i) (u i) (p i) (q i) (η i) 2 0 -
      (∫ t, blockWindow (p i) (q i) (η i) t) * frozenMainScalarSecond P u₀ τ) / M i) l (𝓝 0) := by
  have hL : Tendsto (fun i => Real.log (n i : ℝ)) l atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)
  have hd0 : Tendsto (fun i => frozenDirectGcd P.eval (n i) (u i) 0) l
      (𝓝 (polynomialProfilePairIntegral P P u₀ 0)) := by
    simpa only [polynomialProfilePairIntegral, pow_zero, one_mul, pow_two] using
      (tendsto_frozenDirectGcd_first_three P hP hn hu).1
  have hr0 : Tendsto (fun i => frozenReflectedGcd P.eval (n i) (u i) 0) l
      (𝓝 (polynomialProfilePairIntegral P P (-u₀) 0)) := by
    simpa only [polynomialProfilePairIntegral, pow_zero, one_mul, pow_two] using
      (tendsto_frozenReflectedGcd_first_three P hP hn hu).1
  have hd1 : Tendsto (fun i => frozenDirectGcdFirst P.eval (n i) (u i) 0) l
      (𝓝 (polynomialProfileFirstLimit P P u₀ (-2) 2 0)) := by
    simpa only [frozenDirectGcdFirst, mul_zero, add_zero] using
      tendsto_correctedProfileFirstJet_reindexed P P hP hP hn hu (-2) 2 0
  have hr1 : Tendsto (fun i => frozenReflectedGcdFirst P.eval (n i) (u i) 0) l
      (𝓝 (polynomialProfileFirstLimit P P (-u₀) 2 0 0)) := by
    simpa only [frozenReflectedGcdFirst, mul_zero, add_zero] using
      tendsto_correctedProfileFirstJet_reindexed P P hP hP hn hu.neg 2 0 0
  have hd2 : Tendsto (fun i => frozenDirectGcdSecond P.eval (n i) (u i) 0) l
      (𝓝 (polynomialProfileSecondLimit P P u₀ (-2) 2 0)) := by
    simpa only [frozenDirectGcdSecond, mul_zero, add_zero] using
      tendsto_correctedProfileSecondJet_reindexed P P hP hP hn hu (-2) 2 0
  have hr2 : Tendsto (fun i => frozenReflectedGcdSecond P.eval (n i) (u i) 0) l
      (𝓝 (polynomialProfileSecondLimit P P (-u₀) 2 0 0)) := by
    simpa only [frozenReflectedGcdSecond, mul_zero, add_zero] using
      tendsto_correctedProfileSecondJet_reindexed P P hP hP hn hu.neg 2 0 0
  have hpd0 := tendsto_scaledZetaPoleValue (by norm_num : (-2 : ℝ) ≠ 0) hL hu hu₀.ne'
  have hpr0 := tendsto_scaledZetaPoleValue (by norm_num : (2 : ℝ) ≠ 0) hL hu hu₀.ne'
  obtain ⟨hpd1, hpd2⟩ := tendsto_pole_explicit_jets (by norm_num : (-2 : ℝ) ≠ 0) hL hu hu₀.ne'
  obtain ⟨hpr1, hpr2⟩ := tendsto_pole_explicit_jets (by norm_num : (2 : ℝ) ≠ 0) hL hu hu₀.ne'
  have hW := eventually_taper_mass_bound hgeom
  have hc0 := tendsto_realNormalizedChiTaperJet_error hL hp hu hu₀ hB hτa hτb hgeom 0
  have hc1 := tendsto_realNormalizedChiTaperJet_error hL hp hu hu₀ hB hτa hτb hgeom 1
  have hc2 := tendsto_realNormalizedChiTaperJet_error hL hp hu hu₀ hB hτa hτb hgeom 2
  have hmass : Tendsto (fun i => ((∫ t, blockWindow (p i) (q i) (η i) t) -
      (∫ t, blockWindow (p i) (q i) (η i) t) * 1) / M i) l (𝓝 0) := by
    simpa only [mul_one, sub_self, zero_div] using (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ)) l (𝓝 0))
  have hsmall : ∀ᶠ i in l, u i / Real.log (n i) < 1 / 20 :=
    (hu.div_atTop hL).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 20))
  have hvalid : ∀ᶠ i in l, 1 < n i ∧ 0 < η i ∧ 4 ≤ p i - η i ∧
      0 < (u i + 0) / Real.log (n i) ∧ (u i + 0) / Real.log (n i) < 1 / 20 := by
    filter_upwards [hn.eventually_ge_atTop 2, hgeom, hp.eventually_ge_atTop 4,
      hu.eventually (Ioi_mem_nhds hu₀), hL.eventually_gt_atTop 0, hsmall] with i hni hgi hpi hui hLi hsi
    refine ⟨by omega, hgi.1, hpi, ?_, ?_⟩
    · simpa only [add_zero] using div_pos hui hLi
    · simpa only [add_zero] using hsi
  constructor
  · have hsum := ((((tendsto_triple_scaled_error hd1 hpd0 hmass hB hW).add
        (tendsto_triple_scaled_error hd0 hpd1 hmass hB hW)).add
        (tendsto_triple_scaled_error hr1 hpr0 hc0 hB hW)).add
        (tendsto_triple_scaled_error hr0 hpr1 hc0 hB hW)).add
        (tendsto_triple_scaled_error hr0 hpr0 hc1 hB hW)
    simp only [zero_add] at hsum
    apply hsum.congr'
    filter_upwards [hvalid, hgeom] with i hi hgi
    rw [normalizedFrozenMainJet_one_eq hi.1 P.eval (u i) hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.le]
    dsimp only [frozenMainProductFirst, scalarTripleFirstJet, frozenMainScalarFirst]
    simp only [add_zero, mul_zero, pow_zero, pow_one, one_mul]
    field_simp [hu₀.ne', hgi.2.2.1.ne']
    ring
  · have d20 := tendsto_triple_scaled_error hd2 hpd0 hmass hB hW
    have d02 := tendsto_triple_scaled_error hd0 hpd2 hmass hB hW
    have d11 := (tendsto_triple_scaled_error hd1 hpd1 hmass hB hW).const_mul 2
    have r200 := tendsto_triple_scaled_error hr2 hpr0 hc0 hB hW
    have r020 := tendsto_triple_scaled_error hr0 hpr2 hc0 hB hW
    have r002 := tendsto_triple_scaled_error hr0 hpr0 hc2 hB hW
    have r110 := (tendsto_triple_scaled_error hr1 hpr1 hc0 hB hW).const_mul 2
    have r101 := (tendsto_triple_scaled_error hr1 hpr0 hc1 hB hW).const_mul 2
    have r011 := (tendsto_triple_scaled_error hr0 hpr1 hc1 hB hW).const_mul 2
    have hsum := (((((((d20.add d02).add d11).add r200).add r020).add r002).add r110).add r101).add r011
    simp only [mul_zero, zero_add] at hsum
    apply hsum.congr'
    filter_upwards [hvalid, hgeom] with i hi hgi
    rw [normalizedFrozenMainJet_two_eq hi.1 P.eval (u i) hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2]
    dsimp only [frozenMainProductSecond, scalarTripleSecondJet, frozenMainScalarSecond]
    simp only [add_zero, mul_zero, pow_zero, pow_one, one_mul]
    field_simp [hu₀.ne', hgi.2.2.1.ne']
    ring

private theorem tendsto_weighted_scaled_error {ι : Type*} {l : Filter ι}
    {a c W M : ι → ℝ} {A C K : ℝ}
    (ha : Tendsto a l (𝓝 A))
    (hc : Tendsto (fun i => (c i - W i * C) / M i) l (𝓝 0))
    (hK : 0 ≤ K) (hW : ∀ᶠ i in l, |W i / M i| ≤ K) :
    Tendsto (fun i => (a i * c i - W i * (A * C)) / M i) l (𝓝 0) := by
  simpa only [mul_one] using tendsto_triple_scaled_error ha
    (tendsto_const_nhds : Tendsto (fun _ : ι => (1 : ℝ)) l (𝓝 1)) hc hK hW

/-- The exact three-profile main combination has the linear-detector scalar limit. -/
theorem tendsto_normalizedThreeProfileMain_error
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} (hn : Tendsto n l atTop)
    {p q η u M α : ι → ℝ} (hp : Tendsto (fun i => p i - η i) l atTop)
    {θ R B : ℝ} (hθ : 0 < θ) (hR : 0 < R)
    (hu : Tendsto u l (𝓝 (R * θ))) (hα : Tendsto α l (𝓝 θ)) (hB : 0 ≤ B)
    (hτa : Tendsto (fun i => Real.log ((p i - η i) / (2 * Real.pi)) / Real.log (n i)) l (𝓝 (1 / θ)))
    (hτb : Tendsto (fun i => Real.log ((q i + η i) / (2 * Real.pi)) / Real.log (n i)) l (𝓝 (1 / θ)))
    (hgeom : ∀ᶠ i in l, 0 < η i ∧ p i ≤ q i ∧ 0 < M i ∧
      (q i - p i + 2 * η i) / M i ≤ B) :
    Tendsto (fun i => (normalizedThreeProfileMain (n i) (u i) (p i) (q i) (η i) (α i) -
      (∫ t, blockWindow (p i) (q i) (η i) t) * threeProfileDetectorScalar θ R) / M i) l (𝓝 0) := by
  have hX : (X : ℝ[X]).eval 0 = 0 := by simp only [Polynomial.eval_X]
  have hS := complementPolynomial_eval_zero X hX
  have hH : (X + complementPolynomial X : ℝ[X]).eval 0 = 0 := by
    rw [Polynomial.eval_add, hX, hS, zero_add]
  have hf0 := tendsto_normalizedFrozenMainJet_zero_error X hX hn hp hu (mul_pos hR hθ) hB hτa hτb hgeom
  have hs0 := tendsto_normalizedFrozenMainJet_zero_error (complementPolynomial X) hS hn hp hu
    (mul_pos hR hθ) hB hτa hτb hgeom
  have hh0 := tendsto_normalizedFrozenMainJet_zero_error (X + complementPolynomial X) hH hn hp hu
    (mul_pos hR hθ) hB hτa hτb hgeom
  obtain ⟨hf1, hf2⟩ := tendsto_normalizedFrozenMainJet_derivative_errors X hX hn hp hu
    (mul_pos hR hθ) hB hτa hτb hgeom
  obtain ⟨hs1, _⟩ := tendsto_normalizedFrozenMainJet_derivative_errors (complementPolynomial X) hS hn hp hu
    (mul_pos hR hθ) hB hτa hτb hgeom
  obtain ⟨hh1, _⟩ := tendsto_normalizedFrozenMainJet_derivative_errors (X + complementPolynomial X) hH hn hp hu
    (mul_pos hR hθ) hB hτa hτb hgeom
  have hW := eventually_taper_mass_bound hgeom
  have hcoef0 : Tendsto (fun i => 1 - α i) l (𝓝 (1 - θ)) := tendsto_const_nhds.sub hα
  have hcoef1 : Tendsto (fun i => α i ^ 2 - α i) l (𝓝 (θ ^ 2 - θ)) := (hα.pow 2).sub hα
  have hcoef3 : Tendsto (fun i => -(α i / 2 * (2 - α i))) l (𝓝 (-(θ / 2 * (2 - θ)))) :=
    ((hα.div_const 2).mul (tendsto_const_nhds.sub hα)).neg
  have hcoef4 : Tendsto (fun i => α i ^ 2 / 2) l (𝓝 (θ ^ 2 / 2)) := (hα.pow 2).div_const 2
  have hcoef6 : Tendsto (fun i => α i ^ 2 / 4) l (𝓝 (θ ^ 2 / 4)) := (hα.pow 2).div_const 4
  have e0 := tendsto_weighted_scaled_error hcoef0 hf0 hB hW
  have e1 := tendsto_weighted_scaled_error hcoef1 hs0 hB hW
  have e2 := tendsto_weighted_scaled_error hα hh0 hB hW
  have e3 := tendsto_weighted_scaled_error hcoef3 hf1 hB hW
  have e4 := tendsto_weighted_scaled_error hcoef4 hs1 hB hW
  have e5 := tendsto_weighted_scaled_error hcoef4.neg hh1 hB hW
  have e6 := tendsto_weighted_scaled_error hcoef6 hf2 hB hW
  have hsum := (((((e0.add e1).add e2).add e3).add e4).add e5).add e6
  simp only [zero_add] at hsum
  convert hsum using 1
  funext i
  dsimp only [normalizedThreeProfileMain, threeProfileDetectorScalar]
  ring

/-- The actual matched linear detector main term has the selected three-profile scalar limit. -/
theorem tendsto_detectorThreeMomentMain_error
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} (hn : Tendsto n l atTop)
    {p q η d lam M : ι → ℝ} (hp : Tendsto (fun i => p i - η i) l atTop)
    {θ R B : ℝ} (hθ : 0 < θ) (hR : 0 < R)
    (hu : Tendsto (fun i => d i * Real.log (n i)) l (𝓝 (R * θ)))
    (hlam : Tendsto (fun i => lam i * Real.log (n i)) l (𝓝 θ)) (hB : 0 ≤ B)
    (hτa : Tendsto (fun i => Real.log ((p i - η i) / (2 * Real.pi)) / Real.log (n i)) l (𝓝 (1 / θ)))
    (hτb : Tendsto (fun i => Real.log ((q i + η i) / (2 * Real.pi)) / Real.log (n i)) l (𝓝 (1 / θ)))
    (hgeom : ∀ᶠ i in l, 0 < η i ∧ p i ≤ q i ∧ 0 < M i ∧
      (q i - p i + 2 * η i) / M i ≤ B) :
    Tendsto (fun i => (detectorThreeMomentMain (p i) (q i) (η i) (n i)
      (linearDetectorWeights (n i) (d i)) (d i) (lam i) -
      (∫ t, blockWindow (p i) (q i) (η i) t) * threeProfileDetectorScalar θ R) / M i) l (𝓝 0) := by
  have hL : Tendsto (fun i => Real.log (n i : ℝ)) l atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)
  have hd : Tendsto d l (𝓝 0) := by
    apply (hu.div_atTop hL).congr'
    filter_upwards [hL.eventually_gt_atTop 0] with i hi
    exact mul_div_cancel_right₀ (d i) hi.ne'
  apply (tendsto_normalizedThreeProfileMain_error hn hp hθ hR hu hlam hB hτa hτb hgeom).congr'
  filter_upwards [hn.eventually_ge_atTop 2, hgeom, hp.eventually_ge_atTop 4,
    hu.eventually (Ioi_mem_nhds (mul_pos hR hθ)), hL.eventually_gt_atTop 0,
    hd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 20))] with i hni hgi hpi hui hLi hdi
  have hdp : 0 < d i := (mul_pos_iff_of_pos_right hLi).mp hui
  rw [detectorThreeMomentMain_eq_normalizedProfiles hgi.1 hpi (by omega : 1 < n i) hdp hdi.le]

end GaloisForLFunctions.MultiscaleMollifiedZetaField
