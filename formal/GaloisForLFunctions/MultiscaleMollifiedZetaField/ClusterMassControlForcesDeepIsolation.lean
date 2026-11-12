import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheTuranCameraSeesBoundedClusters

/-!
# Exterior mass control forces deep isolation

The original cluster condition is imposed at every centre in the target's
full sector window. Moving to the opposite endpoint puts any companion at
a different ordinate outside the sector. Its singleton mass then forces
an explicit separation law for equally deep or deeper zeros.
-/

noncomputable section

open Complex Set MeasureTheory
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

private theorem integral_le_profileMass {v : ℝ → ℝ} (hv0 : ∀ u, 0 ≤ v u) :
    (∫ u, v u) ≤ profileMass v := by
  have he : (fun u => ‖cplx v u‖) = v := by
    funext u
    simp only [cplx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hv0 u)]
  rw [profileMass, he]
  exact le_add_of_nonneg_right (integral_nonneg fun _ => norm_nonneg _)

/-- A single exterior zero at least as deep as the target spends the
inverse Lorentzian denominator of its entire permitted signal. -/
theorem clusterAt_exterior_deep_separation
    {v : ℝ → ℝ} (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u)
    {δ h : ℝ} (hδ : 0 < δ) (hh : 0 ≤ h) {M N : ℕ} (hN : 1 ≤ N)
    {ρ q : zetaZeroConfig.carrier}
    (hρ : 1 / 2 ≤ (ρ : ℂ).re) (hq : (ρ : ℂ).re ≤ (q : ℂ).re)
    (hcluster : ClusterAt v δ h M N ρ) {t : ℝ}
    (ht : |t - (ρ : ℂ).im| ≤ 1 / (10 * δ))
    (hout : 1 / 10 < |(q : ℂ).im - t| * δ) :
    4 ≤ turanConstant N M * (1 + δ ^ 2 * ((q : ℂ).im - t) ^ 2) := by
  classical
  obtain ⟨s, _, _, hsec, htail⟩ := hcluster t ht
  have hqs : q ∉ s := fun hmem => (not_lt_of_ge (hsec q hmem)) hout
  have hdis : Disjoint ({q} : Finset zetaZeroConfig.carrier) s := by
    simpa only [Finset.disjoint_singleton_left] using hqs
  have htailq := htail (M + 1) le_rfl (by omega) {q} hdis
  simp only [Finset.sum_singleton, Nat.cast_add, Nat.cast_one] at htailq
  let E := Real.exp (((ρ : ℂ).re - 1 / 2) * (((M : ℝ) + 1) * h - δ))
  let D := 1 + δ ^ 2 * ((q : ℂ).im - t) ^ 2
  have hE : 0 < E := Real.exp_pos _
  have hD : 0 < D := by dsimp only [D]; positivity
  have hexp : E ≤ Real.exp (((q : ℂ).re - 1 / 2) * (((M : ℝ) + 1) * h) +
      |(q : ℂ).re - 1 / 2| * δ) := by
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg (by linarith only [hρ, hq])]
    have hy : 0 ≤ ((M : ℝ) + 1) * h := by positivity
    have hb := mul_le_mul_of_nonneg_right (sub_le_sub_right hq (1 / 2)) hy
    have hp := mul_nonneg (show 0 ≤ (ρ : ℂ).re - 1 / 2 by linarith only [hρ]) hδ.le
    have hqp := mul_nonneg (show 0 ≤ (q : ℂ).re - 1 / 2 by linarith only [hρ, hq]) hδ.le
    nlinarith only [hb, hp, hqp]
  have hw : E / D ≤ companionWeight δ (((M : ℝ) + 1) * h) t q := by
    exact div_le_div_of_nonneg_right hexp hD.le
  have hw0 : 0 ≤ companionWeight δ (((M : ℝ) + 1) * h) t q :=
    (div_pos hE hD).le.trans hw
  have hm : (1 : ℝ) ≤ zetaZeroConfig.mult q := by
    exact_mod_cast zetaZeroConfig.one_le_mult q q.2
  have hlow : (∫ u, v u) * (E / D) ≤ profileMass v *
      ((zetaZeroConfig.mult q : ℝ) * companionWeight δ (((M : ℝ) + 1) * h) t q) := by
    apply mul_le_mul (integral_le_profileMass hv0)
      (hw.trans (le_mul_of_one_le_left hw0 hm)) (div_pos hE hD).le
      (profileMass_nonneg v)
  have hbound : (∫ u, v u) * (E / D) ≤
      1 / 4 * (∫ u, v u) * turanConstant N M * E := hlow.trans htailq
  have hmul : (∫ u, v u) * E ≤
      (1 / 4 * (∫ u, v u) * turanConstant N M * E) * D := by
    apply (div_le_iff₀ hD).mp
    simpa only [mul_div_assoc] using hbound
  have hfactor : (∫ u, v u) * E * 4 ≤
      ((∫ u, v u) * E) * (turanConstant N M * D) := by
    nlinarith only [hmul]
  exact (mul_le_mul_iff_right₀ (mul_pos hI hE)).mp hfactor

private theorem opposite_window_endpoint {x z δ : ℝ} (hδ : 0 < δ) (hne : z ≠ x) :
    ∃ t : ℝ, |t - x| ≤ 1 / (10 * δ) ∧
      1 / 10 < |z - t| * δ ∧
      |z - t| * δ = |z - x| * δ + 1 / 10 := by
  have hr : 0 < 1 / (10 * δ) := by positivity
  have he : (1 / (10 * δ)) * δ = 1 / 10 := by field_simp
  rcases lt_or_gt_of_ne hne with hz | hz
  · refine ⟨x + 1 / (10 * δ), ?_, ?_, ?_⟩
    · rw [add_sub_cancel_left, abs_of_pos hr]
    · rw [abs_of_neg (by linarith only [hz, hr])]
      nlinarith only [mul_neg_of_neg_of_pos (sub_neg.mpr hz) hδ, he]
    · rw [abs_of_neg (by linarith only [hz, hr]), abs_of_neg (sub_neg.mpr hz)]
      nlinarith only [he]
  · refine ⟨x - 1 / (10 * δ), ?_, ?_, ?_⟩
    · rw [sub_sub_cancel_left, abs_neg, abs_of_pos hr]
    · rw [abs_of_pos (by linarith only [hz, hr])]
      nlinarith only [mul_pos (sub_pos.mpr hz) hδ, he]
    · rw [abs_of_pos (by linarith only [hz, hr]), abs_of_pos (sub_pos.mpr hz)]
      nlinarith only [he]

/-- Requiring the exterior estimate throughout the whole window forces
a gap to every equally deep or deeper zero at a different ordinate. -/
theorem clusterAt_forces_deep_ordinate_gap
    {v : ℝ → ℝ} (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u)
    {δ h : ℝ} (hδ : 0 < δ) (hh : 0 ≤ h) {M N : ℕ} (hN : 1 ≤ N)
    {ρ q : zetaZeroConfig.carrier}
    (hρ : 1 / 2 ≤ (ρ : ℂ).re) (hq : (ρ : ℂ).re ≤ (q : ℂ).re)
    (hne : (q : ℂ).im ≠ (ρ : ℂ).im) (hcluster : ClusterAt v δ h M N ρ) :
    4 ≤ turanConstant N M * (1 + (|(q : ℂ).im - (ρ : ℂ).im| * δ + 1 / 10) ^ 2) := by
  obtain ⟨t, ht, hout, he⟩ := opposite_window_endpoint hδ hne
  have hb := clusterAt_exterior_deep_separation hv0 hI hδ hh hN hρ hq hcluster ht hout
  have hsq : δ ^ 2 * ((q : ℂ).im - t) ^ 2 =
      (|(q : ℂ).im - (ρ : ℂ).im| * δ + 1 / 10) ^ 2 := by
    rw [← he, mul_pow, sq_abs]
    ring
  simpa only [hsq] using hb

/-- Nearby equally deep zeros with different ordinates violate the
original exterior-mass condition, regardless of its core cardinality. -/
theorem not_clusterAt_of_nearby_deep_zero
    {v : ℝ → ℝ} (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u)
    {δ h : ℝ} (hδ : 0 < δ) (hh : 0 ≤ h) {M N : ℕ} (hN : 1 ≤ N)
    {ρ q : zetaZeroConfig.carrier}
    (hρ : 1 / 2 ≤ (ρ : ℂ).re) (hq : (ρ : ℂ).re ≤ (q : ℂ).re)
    (hne : (q : ℂ).im ≠ (ρ : ℂ).im)
    (hnear : |(q : ℂ).im - (ρ : ℂ).im| * δ ≤ 1) :
    ¬ ClusterAt v δ h M N ρ := by
  intro hcluster
  have hb := clusterAt_forces_deep_ordinate_gap hv0 hI hδ hh hN hρ hq hne hcluster
  have hκ : turanConstant N M ≤ 1 := by
    apply (turanConstant_le (n := 1) le_rfl hN M).trans
    unfold turanConstant
    simp only [Nat.cast_one, pow_one]
    apply (div_le_one (by positivity)).mpr
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hM : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
    nlinarith only [he, hM, mul_nonneg (sub_nonneg.mpr he) hM]
  have hx : 0 ≤ |(q : ℂ).im - (ρ : ℂ).im| * δ := mul_nonneg (abs_nonneg _) hδ.le
  have hk := mul_le_mul_of_nonneg_right hκ
    (show 0 ≤ 1 + (|(q : ℂ).im - (ρ : ℂ).im| * δ + 1 / 10) ^ 2 by positivity)
  nlinarith only [hb, hk, hnear, hx,
    mul_nonneg (sub_nonneg.mpr hnear) (by linarith only [hx] :
      0 ≤ 1 + |(q : ℂ).im - (ρ : ℂ).im| * δ)]

/-- Distinct ordinates of clustered right-half-strip zeros are
automatically separated, even when their real parts differ. -/
theorem clusterAt_distinct_ordinates_separated
    {v : ℝ → ℝ} (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u)
    {δ h : ℝ} (hδ : 0 < δ) (hh : 0 ≤ h) {M N : ℕ} (hN : 1 ≤ N)
    {ρ q : zetaZeroConfig.carrier}
    (hρ : 1 / 2 ≤ (ρ : ℂ).re) (hq : 1 / 2 ≤ (q : ℂ).re)
    (hcρ : ClusterAt v δ h M N ρ) (hcq : ClusterAt v δ h M N q)
    (hne : (q : ℂ).im ≠ (ρ : ℂ).im) :
    1 < |(q : ℂ).im - (ρ : ℂ).im| * δ := by
  by_contra h
  have hnear := le_of_not_gt h
  rcases le_total (ρ : ℂ).re (q : ℂ).re with hle | hle
  · exact not_clusterAt_of_nearby_deep_zero hv0 hI hδ hh hN hρ hle hne hnear hcρ
  · have hnear' : |(ρ : ℂ).im - (q : ℂ).im| * δ ≤ 1 := by
      rwa [abs_sub_comm]
    exact not_clusterAt_of_nearby_deep_zero hv0 hI hδ hh hN hq hle hne.symm hnear' hcq

end GaloisForLFunctions.MultiscaleMollifiedZetaField
