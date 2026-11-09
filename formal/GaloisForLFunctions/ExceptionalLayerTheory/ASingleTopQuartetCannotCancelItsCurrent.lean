import GaloisForLFunctions.ExceptionalLayerTheory.TheSharpRecurrentLayerEnvelope
import GaloisForLFunctions.RHTower.Deninger.DeningerDivisorSchwarzMonodromy
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing

/-!
# A single top quartet cannot cancel its high current

A conjugate top pair has equal multiplicities and unequal vertical Gamma
weights. Its normalized current therefore stays away from zero at every
large height. In the actual finite-layer world, either the top has two
distinct positive ordinates or the corrected current grows pointwise at
all supercritical exponential speeds.
-/

open Complex Filter Set Topology RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem xiZero_conj_copy (q : XiZeroCopy) :
    xiZero (xiZeroCopyConjEquiv q) = (starRingEnd ℂ) (xiZero q) := rfl

private theorem xiZero_im_ne_zero (q : XiZeroCopy) : (xiZero q).im ≠ 0 := by
  intro him
  have hq : xiZero q = ((xiZero q).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hz : xi (xiZero q) = 0 := xi_xiZeroCopy_eq_zero q
  rw [hq] at hz
  exact xi_ne_zero_of_real _ hz

private theorem topPair_sum_eq {G : Finset XiZeroCopy} {γ : ℝ}
    (hclosed : ∀ q ∈ G, xiZeroCopyConjEquiv q ∈ G)
    (hpair : ∀ q ∈ G, (xiZero q).im = γ ∨ (xiZero q).im = -γ) (a t : ℝ) :
    (∑ q ∈ G, exceptionalOrdinateWave (xiZero q).im a t) =
      (((G.card : ℝ) / 2 : ℝ) : ℂ) *
        (exceptionalOrdinateWave γ a t + exceptionalOrdinateWave (-γ) a t) := by
  classical
  have hsum : (∑ q ∈ G, exceptionalOrdinateWave (xiZero (xiZeroCopyConjEquiv q)).im a t) =
      ∑ q ∈ G, exceptionalOrdinateWave (xiZero q).im a t := by
    apply Finset.sum_bij (fun q _ => xiZeroCopyConjEquiv q)
    · exact hclosed
    · intro q _ r _ hqr
      exact xiZeroCopyConjEquiv.injective hqr
    · intro q hq
      exact ⟨xiZeroCopyConjEquiv q, hclosed q hq, xiZeroCopyConjEquiv_apply_apply q⟩
    · intro q _
      rfl
  have heq : (∑ q ∈ G, (exceptionalOrdinateWave (xiZero q).im a t +
      exceptionalOrdinateWave (xiZero (xiZeroCopyConjEquiv q)).im a t)) =
      (G.card : ℂ) * (exceptionalOrdinateWave γ a t + exceptionalOrdinateWave (-γ) a t) := by
    calc
      _ = ∑ _q ∈ G, (exceptionalOrdinateWave γ a t + exceptionalOrdinateWave (-γ) a t) := by
        refine Finset.sum_congr rfl fun q hq => ?_
        rw [xiZero_conj_copy, Complex.conj_im]
        rcases hpair q hq with hqγ | hqγ
        · rw [hqγ]
        · rw [hqγ, neg_neg]
          exact add_comm _ _
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_add_distrib, hsum] at heq
  calc
    _ = ((∑ q ∈ G, exceptionalOrdinateWave (xiZero q).im a t) +
        (∑ q ∈ G, exceptionalOrdinateWave (xiZero q).im a t)) / 2 := by ring
    _ = _ := by rw [heq]; push_cast; ring

private theorem topPair_amplitude_pos {G : Finset XiZeroCopy} {γ : ℝ}
    (hG : G.Nonempty) (hγ : 0 < γ) :
    0 < (G.card : ℝ) / 2 *
      (Real.exp (Real.pi * γ / 4) - Real.exp (Real.pi * (-γ) / 4)) := by
  have hc : 0 < (G.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hG
  have he : Real.exp (Real.pi * (-γ) / 4) < Real.exp (Real.pi * γ / 4) :=
    Real.exp_lt_exp.mpr (by linarith only [mul_pos Real.pi_pos hγ])
  exact mul_pos (div_pos hc (by norm_num)) (sub_pos.mpr he)

private theorem norm_topPair_sum_ge {G : Finset XiZeroCopy} {γ : ℝ}
    (hclosed : ∀ q ∈ G, xiZeroCopyConjEquiv q ∈ G)
    (hpair : ∀ q ∈ G, (xiZero q).im = γ ∨ (xiZero q).im = -γ) (a t : ℝ) :
    (G.card : ℝ) / 2 *
      (Real.exp (Real.pi * γ / 4) - Real.exp (Real.pi * (-γ) / 4)) ≤
      ‖∑ q ∈ G, exceptionalOrdinateWave (xiZero q).im a t‖ := by
  rw [topPair_sum_eq hclosed hpair, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (G.card : ℝ) / 2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ (G.card : ℝ) / 2)
  have hn := norm_sub_le
    (exceptionalOrdinateWave γ a t + exceptionalOrdinateWave (-γ) a t)
    (exceptionalOrdinateWave (-γ) a t)
  rw [add_sub_cancel_right, norm_exceptionalOrdinateWave, norm_exceptionalOrdinateWave] at hn
  linarith only [hn]

/-- In the actual finite-layer world, a top with only one positive ordinate
forces pointwise growth of the corrected current at every supercritical speed.
Thus phase cancellation can occur only when the top has distinct positive ordinates. -/
theorem not_asymptoticAbscissaLaw_has_top_ordinate_dichotomy :
    ¬ AsymptoticAbscissaLaw →
      ∃ σ β : ℝ, 1 / 2 < σ ∧ σ < β ∧ β < 1 ∧
        (∀ q : XiZeroCopy, (xiZero q).re ≤ β) ∧
        (∃ q : XiZeroCopy, (xiZero q).re = β) ∧
        ((∃ q r : XiZeroCopy, (xiZero q).re = β ∧ (xiZero r).re = β ∧
            0 < (xiZero q).im ∧ 0 < (xiZero r).im ∧ (xiZero q).im ≠ (xiZero r).im) ∨
          ∀ a : ℝ, 0 < a → Real.pi / 2 < a * (β - σ) →
            Tendsto (fun t : ℝ => ‖correctedExceptionalCurrent σ a t‖) atTop atTop) := by
  classical
  intro hnot
  obtain ⟨F, θ, σ, β, hθ, hgap, hσβ, hβ1, ⟨q₀, hq₀F, hq₀β⟩,
    hmax, hrest, hprofile⟩ := not_asymptoticAbscissaLaw_has_escaping_layer_profile hnot
  let G : Finset XiZeroCopy := F.filter (fun q => (xiZero q).re = β)
  have hG : G.Nonempty := ⟨q₀, Finset.mem_filter.mpr ⟨hq₀F, hq₀β⟩⟩
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
  have hclosed : ∀ q ∈ G, xiZeroCopyConjEquiv q ∈ G := by
    intro q hq
    apply (htop _).mpr
    rw [xiZero_conj_copy, Complex.conj_re]
    exact (htop q).mp hq
  refine ⟨σ, β, by linarith only [hθ, hgap], hσβ, hβ1, hall, ⟨q₀, hq₀β⟩, ?_⟩
  by_cases htwo : ∃ q r : XiZeroCopy, (xiZero q).re = β ∧ (xiZero r).re = β ∧
      0 < (xiZero q).im ∧ 0 < (xiZero r).im ∧ (xiZero q).im ≠ (xiZero r).im
  · exact Or.inl htwo
  right
  have hpositive : ∃ q ∈ G, 0 < (xiZero q).im := by
    obtain ⟨q, hq⟩ := hG
    rcases lt_or_gt_of_ne (xiZero_im_ne_zero q) with hneg | hpos
    · refine ⟨xiZeroCopyConjEquiv q, hclosed q hq, ?_⟩
      rw [xiZero_conj_copy, Complex.conj_im]
      linarith only [hneg]
    · exact ⟨q, hq, hpos⟩
  obtain ⟨p, hpG, hp⟩ := hpositive
  let γ : ℝ := (xiZero p).im
  have hγ : 0 < γ := hp
  have hpos_unique : ∀ q ∈ G, 0 < (xiZero q).im → (xiZero q).im = γ := by
    intro q hq hqpos
    by_contra hne
    exact htwo ⟨q, p, (htop q).mp hq, (htop p).mp hpG, hqpos, hp, hne⟩
  have hpair : ∀ q ∈ G, (xiZero q).im = γ ∨ (xiZero q).im = -γ := by
    intro q hq
    by_cases hpos : 0 < (xiZero q).im
    · exact Or.inl (hpos_unique q hq hpos)
    · right
      have hneg : (xiZero q).im < 0 :=
        lt_of_le_of_ne (le_of_not_gt hpos) (xiZero_im_ne_zero q)
      have hconjpos : 0 < (xiZero (xiZeroCopyConjEquiv q)).im := by
        rw [xiZero_conj_copy, Complex.conj_im]
        linarith only [hneg]
      have heq := hpos_unique (xiZeroCopyConjEquiv q) (hclosed q hq) hconjpos
      rw [xiZero_conj_copy, Complex.conj_im] at heq
      linarith only [heq]
  let c : ℝ := (G.card : ℝ) / 2 *
    (Real.exp (Real.pi * γ / 4) - Real.exp (Real.pi * (-γ) / 4))
  have hc : 0 < c := topPair_amplitude_pos hG hγ
  intro a ha hsuper
  have hprof : Tendsto (fun t : ℝ => normalizedExceptionalCurrent σ β a t +
      ∑ q ∈ G, exceptionalOrdinateWave (xiZero q).im a t) atTop (𝓝 0) :=
    hprofile a ha hsuper
  have hen := hprof.norm
  simp only [norm_zero] at hen
  have hJ : ∀ᶠ t : ℝ in atTop, c / 2 ≤ ‖normalizedExceptionalCurrent σ β a t‖ := by
    filter_upwards [hen.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < c / 2))]
      with t ht
    have hs : c ≤ ‖∑ q ∈ G, exceptionalOrdinateWave (xiZero q).im a t‖ :=
      norm_topPair_sum_ge hclosed hpair a t
    have hn := norm_sub_le
      (normalizedExceptionalCurrent σ β a t + ∑ q ∈ G, exceptionalOrdinateWave (xiZero q).im a t)
      (normalizedExceptionalCurrent σ β a t)
    rw [add_sub_cancel_left] at hn
    linarith only [hs, hn, ht]
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
  have hscale : c / 2 * (2 * (|B| + 1) / c) = |B| + 1 := by
    field_simp [ne_of_gt hc]
  rw [hscale] at hb
  have hbig := mul_le_mul_of_nonneg_right hj hp0.le
  have heq : ‖normalizedExceptionalCurrent σ β a t‖ * ‖P t‖ =
      ‖correctedExceptionalCurrent σ a t‖ := by
    rw [← norm_mul]
    exact congrArg norm (div_mul_cancel₀ _ hpne)
  rw [heq] at hbig
  linarith only [hb, hbig, le_abs_self B]

#print axioms not_asymptoticAbscissaLaw_has_top_ordinate_dichotomy

end GaloisForLFunctions.ExceptionalLayerTheory
