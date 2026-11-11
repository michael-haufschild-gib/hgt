import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheChiJetsAreUniformAcrossDyadicBlocks

/-!
# Conductor jets after integration against the actual taper

The displacement derivatives pass through the taper integral. Uniform
conductor limits on its support then bound the integral error by its
support length times the uniform error. This remains valid for moving
blocks whose length, divided by the chosen block scale, stays bounded.
-/

open Complex Filter MeasureTheory Metric Set Topology
open RHTower GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The literal jet of the normalized reflected taper integral. -/
def normalizedChiTaperJet (L p q η u : ℝ) (j : ℕ) : ℂ :=
  iteratedDeriv j (fun z => ∫ t, blockWindowC p q η t * holomorphicChiPair (z / (L : ℂ)) t)
    (u : ℂ)

private theorem iteratedDeriv_dilation (f : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun w => f (c * w)) = fun w => c ^ n * iteratedDeriv n f (c * w) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ n ih =>
      funext z
      rw [iteratedDeriv_succ, ih, deriv_const_mul_field']
      beta_reduce
      rw [deriv_comp_mul_left (f := iteratedDeriv n f), iteratedDeriv_succ, smul_eq_mul, pow_succ]
      ring

/-- The normalized integral jet is the integral of the normalized chi jet. -/
theorem normalizedChiTaperJet_eq_integral {L p q η u : ℝ}
    (hL : 0 < L) (hu : 0 < u) (hη : 0 < η) (hp : 4 ≤ p - η)
    (hu20 : u / L ≤ 1 / 20) (j : ℕ) :
    normalizedChiTaperJet L p q η u j =
      ∫ t, blockWindowC p q η t *
        iteratedDeriv j (fun z => holomorphicChiPair (z / (L : ℂ)) t) (u : ℂ) := by
  have hs (f : ℂ → ℂ) :
      iteratedDeriv j (fun z => f (z / (L : ℂ))) (u : ℂ) =
        ((L : ℂ)⁻¹) ^ j * iteratedDeriv j f ((u : ℂ) / (L : ℂ)) := by
    simpa only [div_eq_mul_inv, mul_comm] using
      congrFun (iteratedDeriv_dilation f ((L : ℂ)⁻¹) j) (u : ℂ)
  have hc : (u : ℂ) / (L : ℂ) ∈ ball ((u / L : ℝ) : ℂ) (u / L) := by
    rw [← Complex.ofReal_div]
    exact mem_ball_self (div_pos hu hL)
  unfold normalizedChiTaperJet
  rw [hs (fun z => ∫ t, blockWindowC p q η t * holomorphicChiPair z t),
    iteratedDeriv_integral_holomorphicChiPair hη hp (div_pos hu hL) hu20 j hc,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [hs (fun z => holomorphicChiPair z t)]
  ring

private theorem norm_tapered_integral_sub_mass_mul_le {p q η ε : ℝ}
    (hη : 0 < η) (hpq : p ≤ q) (hε : 0 ≤ ε) {F : ℝ → ℂ} {c : ℂ}
    (hF : AEStronglyMeasurable F volume)
    (hclose : ∀ t ∈ Icc (p - η) (q + η), ‖F t - c‖ ≤ ε) :
    ‖(∫ t, blockWindowC p q η t * F t) - ((∫ t, blockWindow p q η t : ℝ) : ℂ) * c‖ ≤
      (q - p + 2 * η) * ε := by
  have hW : Integrable (blockWindow p q η) volume :=
    (contDiff_blockWindow p q η).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_blockWindow hη)
  have hWC := integrable_blockWindowC (p := p) (q := q) hη
  have hb (t : ℝ) : ‖blockWindowC p q η t * (F t - c)‖ ≤ blockWindow p q η t * ε := by
    by_cases ht : t ∈ Icc (p - η) (q + η)
    · rw [norm_mul, norm_blockWindowC_eq]
      exact mul_le_mul_of_nonneg_left (hclose t ht) (blockWindow_nonneg p q η t)
    · rw [blockWindowC_eq_zero hη ht, zero_mul, norm_zero]
      exact mul_nonneg (blockWindow_nonneg p q η t) hε
  have hDI : Integrable (fun t => blockWindowC p q η t * (F t - c)) volume :=
    (hW.mul_const ε).mono' (hWC.aestronglyMeasurable.mul (hF.sub aestronglyMeasurable_const))
      (Eventually.of_forall hb)
  have hFI : Integrable (fun t => blockWindowC p q η t * F t) volume := by
    convert hDI.add (hWC.mul_const c) using 1
    funext t
    ring
  have he : (∫ t, blockWindowC p q η t * (F t - c)) =
      (∫ t, blockWindowC p q η t * F t) - ((∫ t, blockWindow p q η t : ℝ) : ℂ) * c := by
    simp_rw [mul_sub]
    rw [integral_sub hFI (hWC.mul_const c), integral_mul_const]
    rw [show (∫ t, blockWindowC p q η t) = ((∫ t, blockWindow p q η t : ℝ) : ℂ) from integral_ofReal]
  calc
    _ = ‖∫ t, blockWindowC p q η t * (F t - c)‖ := by rw [he]
    _ ≤ ∫ t, blockWindow p q η t * ε :=
      norm_integral_le_of_norm_le (hW.mul_const ε) (Eventually.of_forall hb)
    _ = (∫ t, blockWindow p q η t) * ε := integral_mul_const ε _
    _ ≤ _ := mul_le_mul_of_nonneg_right (integral_blockWindow_le hη hpq) hε

/-- Every reflected integral jet has its conductor limit, uniformly at bounded relative block length. -/
theorem tendsto_normalizedChiTaperJet_error
    {ι : Type*} {l : Filter ι} {L p q η u M : ι → ℝ}
    (hL : Tendsto L l atTop) (hp : Tendsto (fun i => p i - η i) l atTop)
    {τ u₀ B : ℝ} (hu : Tendsto u l (𝓝 u₀)) (hu₀ : 0 < u₀) (hB : 0 ≤ B)
    (hτa : Tendsto (fun i => Real.log ((p i - η i) / (2 * Real.pi)) / L i) l (𝓝 τ))
    (hτb : Tendsto (fun i => Real.log ((q i + η i) / (2 * Real.pi)) / L i) l (𝓝 τ))
    (hgeom : ∀ᶠ i in l, 0 < η i ∧ p i ≤ q i ∧ 0 < M i ∧
      (q i - p i + 2 * η i) / M i ≤ B) (j : ℕ) :
    Tendsto (fun i => (normalizedChiTaperJet (L i) (p i) (q i) (η i) (u i) j -
      ((∫ t, blockWindow (p i) (q i) (η i) t : ℝ) : ℂ) *
        ((2 * (τ : ℂ)) ^ j * Complex.exp (2 * (τ : ℂ) * (u₀ : ℂ)))) / (M i : ℂ)) l (𝓝 0) := by
  have hab : ∀ᶠ i in l, p i - η i ≤ q i + η i := by
    filter_upwards [hgeom] with i hi
    linarith only [hi.1, hi.2.1]
  have hC : Tendsto (fun i => (u i : ℂ)) l (𝓝 (u₀ : ℂ)) := by
    simpa only [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp hu
  have hsmall : ∀ᶠ i in l, u i / L i ≤ 1 / 20 :=
    ((hu.div_atTop hL).eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 20)).mono (fun _ hi => hi.le)
  apply Metric.tendsto_nhds.2
  intro ε hε
  let δ : ℝ := ε / (B + 1)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδB : B * δ < ε := by
    have he : (B + 1) * δ = ε := by
      dsimp only [δ]
      field_simp [show B + 1 ≠ 0 by positivity]
    nlinarith only [he, hδ]
  have hclose := eventually_uniform_scaled_holomorphicChiPair_jet hL hp hab hτa hτb hC j hδ
  filter_upwards [hgeom, hL.eventually_gt_atTop 0, hu.eventually_gt_const hu₀,
    hp.eventually_ge_atTop 4, hsmall, hclose] with i hi hLi hui hpi hsi hci
  have herr : ‖normalizedChiTaperJet (L i) (p i) (q i) (η i) (u i) j -
      ((∫ t, blockWindow (p i) (q i) (η i) t : ℝ) : ℂ) *
        ((2 * (τ : ℂ)) ^ j * Complex.exp (2 * (τ : ℂ) * (u₀ : ℂ)))‖ ≤
      (q i - p i + 2 * η i) * δ := by
    rw [normalizedChiTaperJet_eq_integral hLi hui hi.1 hpi hsi j]
    exact norm_tapered_integral_sub_mass_mul_le hi.1 hi.2.1 hδ.le
      (aestronglyMeasurable_scaled_holomorphicChiPair_jet hLi j (by exact hui))
      (fun t ht => (hci t ht).le)
  rw [dist_zero_right, norm_div, Complex.norm_real, Real.norm_of_nonneg hi.2.2.1.le]
  calc
    _ ≤ ((q i - p i + 2 * η i) * δ) / M i :=
      div_le_div_of_nonneg_right herr hi.2.2.1.le
    _ = ((q i - p i + 2 * η i) / M i) * δ := by ring
    _ ≤ B * δ := mul_le_mul_of_nonneg_right hi.2.2.2 hδ.le
    _ < ε := hδB

end GaloisForLFunctions.MultiscaleMollifiedZetaField
