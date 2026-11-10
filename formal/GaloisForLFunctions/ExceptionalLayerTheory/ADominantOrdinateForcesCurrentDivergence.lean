import GaloisForLFunctions.ExceptionalLayerTheory.TheSharpRecurrentLayerEnvelope

/-!
# A dominant ordinate forces current divergence

Copies at the same ordinate have identical phase. If their total Gamma
weight exceeds the weight of every other ordinate combined, reverse
triangle inequality gives a positive uniform floor. The actual corrected
current then grows at every sufficiently large height.
-/

open Complex Filter Topology RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The grouped Gamma mass of one ordinate, less the mass of its complement. -/
def ordinateDominanceMargin (G : Finset XiZeroCopy) (γ : ℝ) : ℝ := by
  classical
  exact exceptionalLayerMass (G.filter fun q => (xiZero q).im = γ) -
    exceptionalLayerMass (G.filter fun q => (xiZero q).im ≠ γ)

/-- A dominant ordinate gives a height-independent lower bound for the layer wave. -/
theorem ordinateDominanceMargin_le_norm_wave (G : Finset XiZeroCopy) (γ a t : ℝ) :
    ordinateDominanceMargin G γ ≤ ‖∑ q ∈ G, exceptionalOrdinateWave (xiZero q).im a t‖ := by
  classical
  let A := G.filter fun q => (xiZero q).im = γ
  let B := G.filter fun q => (xiZero q).im ≠ γ
  let f := fun q => exceptionalOrdinateWave (xiZero q).im a t
  have hsplit : (∑ q ∈ A, f q) + (∑ q ∈ B, f q) = ∑ q ∈ G, f q :=
    Finset.sum_filter_add_sum_filter_not G (fun q => (xiZero q).im = γ) f
  have hA : ‖∑ q ∈ A, f q‖ = exceptionalLayerMass A := by
    have heq : (∑ q ∈ A, f q) = (A.card : ℂ) * exceptionalOrdinateWave γ a t := by
      calc (∑ q ∈ A, f q) = ∑ _q ∈ A, exceptionalOrdinateWave γ a t :=
          Finset.sum_congr rfl fun q hq => by
            dsimp only [f]; rw [(Finset.mem_filter.mp hq).2]
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [heq, norm_mul, Complex.norm_natCast, norm_exceptionalOrdinateWave, exceptionalLayerMass]
    calc (A.card : ℝ) * Real.exp (Real.pi * γ / 4) =
        ∑ _q ∈ A, Real.exp (Real.pi * γ / 4) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = _ := Finset.sum_congr rfl fun q hq => by rw [(Finset.mem_filter.mp hq).2]
  have hB : ‖∑ q ∈ B, f q‖ ≤ exceptionalLayerMass B := by
    refine (norm_sum_le _ _).trans_eq ?_
    exact Finset.sum_congr rfl fun q _ => norm_exceptionalOrdinateWave _ _ _
  have htriangle := norm_sub_le (∑ q ∈ G, f q) (∑ q ∈ B, f q)
  rw [← hsplit, add_sub_cancel_right, hA] at htriangle
  change exceptionalLayerMass A - exceptionalLayerMass B ≤ _
  linarith only [htriangle, hB]

/-- A positive wave floor transfers to divergence of the corrected current. -/
theorem corrected_current_diverges_of_positive_wave_floor
    {G : Finset XiZeroCopy} {σ β a c : ℝ} (hc : 0 < c)
    (hsuper : Real.pi / 2 < a * (β - σ))
    (hprofile : Tendsto (fun t : ℝ => normalizedExceptionalCurrent σ β a t +
      ∑ q ∈ G, exceptionalOrdinateWave (xiZero q).im a t) atTop (𝓝 0))
    (hfloor : ∀ t : ℝ, c ≤ ‖∑ q ∈ G, exceptionalOrdinateWave (xiZero q).im a t‖) :
    Tendsto (fun t : ℝ => ‖correctedExceptionalCurrent σ a t‖) atTop atTop := by
  have hen := hprofile.norm
  simp only [norm_zero] at hen
  have hJ : ∀ᶠ t : ℝ in atTop, c / 2 ≤ ‖normalizedExceptionalCurrent σ β a t‖ := by
    filter_upwards [hen.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < c / 2))]
      with t ht
    have hn := norm_sub_le
      (normalizedExceptionalCurrent σ β a t + ∑ q ∈ G, exceptionalOrdinateWave (xiZero q).im a t)
      (normalizedExceptionalCurrent σ β a t)
    rw [add_sub_cancel_left] at hn
    linarith only [hfloor t, hn, ht]
  have hr : 0 < gaussianObservationRate (β : ℂ) σ a := by
    simp only [gaussianObservationRate, Complex.ofReal_re]
    linarith only [hsuper]
  let P : ℝ → ℂ := fun t =>
    gaussianMBKernel (Real.exp (-a * t)) ((β : ℂ) - ((σ : ℂ) + t * I))
  have hP : Tendsto (fun t => ‖P t‖) atTop atTop :=
    tendsto_norm_gaussianMode_atTop_of_positive_rate (β : ℂ) σ a hr
  refine tendsto_atTop.2 fun B => ?_
  filter_upwards [hJ, hP.eventually (eventually_ge_atTop (2 * (|B| + 1) / c))]
    with t hj hpole
  have hp0 : 0 < ‖P t‖ := (by positivity : 0 < 2 * (|B| + 1) / c).trans_le hpole
  have hpne : P t ≠ 0 := norm_pos_iff.mp hp0
  have hb := mul_le_mul_of_nonneg_left hpole (div_pos hc (by norm_num : (0 : ℝ) < 2)).le
  have hscale : c / 2 * (2 * (|B| + 1) / c) = |B| + 1 := by field_simp [ne_of_gt hc]
  rw [hscale] at hb
  have hbig := mul_le_mul_of_nonneg_right hj hp0.le
  have heq : ‖normalizedExceptionalCurrent σ β a t‖ * ‖P t‖ =
      ‖correctedExceptionalCurrent σ a t‖ := by
    rw [← norm_mul]
    exact congrArg norm (div_mul_cancel₀ _ hpne)
  rw [heq] at hbig
  linarith only [hb, hbig, le_abs_self B]

/-- Every actual finite top layer with a dominant ordinate has pointwise
divergence of the corrected current at all supercritical speeds. -/
theorem not_asymptoticAbscissaLaw_has_dominant_ordinate_divergence :
    ¬ AsymptoticAbscissaLaw → ∃ (G : Finset XiZeroCopy) (σ β : ℝ),
      1 / 2 < σ ∧ σ < β ∧ β < 1 ∧ G.Nonempty ∧
      (∀ q : XiZeroCopy, q ∈ G ↔ (xiZero q).re = β) ∧
      (∀ q : XiZeroCopy, (xiZero q).re ≤ β) ∧
      ∀ γ : ℝ, 0 < ordinateDominanceMargin G γ →
        ∀ a : ℝ, 0 < a → Real.pi / 2 < a * (β - σ) →
          Tendsto (fun t : ℝ => ‖correctedExceptionalCurrent σ a t‖) atTop atTop := by
  classical
  intro hnot
  obtain ⟨F, θ, σ, β, hθ, hgap, hσβ, hβ1, ⟨q₀, hq₀F, hq₀β⟩,
    hmax, hrest, hprofile⟩ := not_asymptoticAbscissaLaw_has_escaping_layer_profile hnot
  let G : Finset XiZeroCopy := F.filter (fun q => (xiZero q).re = β)
  have htop : ∀ q : XiZeroCopy, q ∈ G ↔ (xiZero q).re = β := by
    intro q
    refine ⟨fun hq => (Finset.mem_filter.mp hq).2, fun hq => ?_⟩
    have hqF : q ∈ F := by
      by_contra hn
      have hr := hrest q hn
      rw [hq] at hr
      linarith only [hr, hgap, hσβ]
    exact Finset.mem_filter.mpr ⟨hqF, hq⟩
  have hall : ∀ q : XiZeroCopy, (xiZero q).re ≤ β := by
    intro q
    by_cases hq : q ∈ F
    · exact hmax q hq
    · exact (hrest q hq).trans (hgap.trans hσβ).le
  refine ⟨G, σ, β, by linarith only [hθ, hgap], hσβ, hβ1,
    ⟨q₀, Finset.mem_filter.mpr ⟨hq₀F, hq₀β⟩⟩, htop, hall, ?_⟩
  intro γ hγ a ha hsuper
  exact corrected_current_diverges_of_positive_wave_floor hγ hsuper
    (hprofile a ha hsuper) (ordinateDominanceMargin_le_norm_wave G γ a)

#print axioms ordinateDominanceMargin_le_norm_wave
#print axioms not_asymptoticAbscissaLaw_has_dominant_ordinate_divergence

end GaloisForLFunctions.ExceptionalLayerTheory
