import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheFrozenMainJetsObeyTheProductRule
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheThreeProfileScalarIsTheLevinsonConstant

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
    have he : δ * (B + 1) = ε := by dsimp only [δ]; field_simp
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
  filter_upwards [hn.eventually_ge_atTop 2] with i hi
  rw [normalizedFrozenMainJet_zero_eq (by omega : 1 < n i), add_zero,
    ← realNormalizedChiTaperJet_zero]
  unfold frozenMainScalarValue
  field_simp [hu₀.ne']
  ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField
