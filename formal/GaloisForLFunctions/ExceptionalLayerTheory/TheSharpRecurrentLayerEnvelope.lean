import GaloisForLFunctions.ExceptionalLayerTheory.TheExceptionalLayerAtEscapingHeights
import GaloisForLFunctions.HTGeometry.BohrFiniteRecurrence

/-!
# The sharp recurrent envelope of the exceptional layer

The high-height Gaussian profile has positive ordinate weights. Its exact
upper envelope is their total mass, and finite Bohr recurrence reaches that
mass at arbitrarily late physical heights. The result concerns the complete
infinite prime current, after its explicit pole and continuation corrections.
-/

open Complex Filter Set Topology RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The observation phase after including the vertical Gamma correction. -/
def exceptionalObservationPhase (a t : ℝ) : ℝ :=
  (a * t + Real.log (t / 2)) / 2

/-- Total Gamma-tilted multiplicity of a finite layer. -/
def exceptionalLayerMass (F : Finset XiZeroCopy) : ℝ :=
  ∑ q ∈ F, Real.exp (Real.pi * (xiZero q).im / 4)

/-- The literal infinite prime current with its pole and continuation terms removed. -/
def correctedExceptionalCurrent (σ a t : ℝ) : ℂ :=
  gaussianDampedPrimeSum ((σ : ℂ) + t * I) (Real.exp (-a * t)) +
    (Real.exp (-(Real.exp (-a * t))) : ℂ) * logDeriv riemannZeta ((σ : ℂ) + t * I) -
    gaussianMBKernel (Real.exp (-a * t)) (1 - ((σ : ℂ) + t * I))

/-- Current measured in units of the real top-layer Gaussian mode. -/
def normalizedExceptionalCurrent (σ β a t : ℝ) : ℂ :=
  correctedExceptionalCurrent σ a t /
    gaussianMBKernel (Real.exp (-a * t)) ((β : ℂ) - ((σ : ℂ) + t * I))

private theorem exceptionalOrdinateWave_eq_character (γ a t : ℝ) :
    exceptionalOrdinateWave γ a t = (Real.exp (Real.pi * γ / 4) : ℂ) *
      Complex.exp (I * ((exceptionalObservationPhase a t : ℂ) * (γ : ℂ))) := by
  rw [exceptionalOrdinateWave, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp [exceptionalObservationPhase] <;> ring

private theorem tendsto_exceptionalObservationPhase {a : ℝ} (ha : 0 < a) :
    Tendsto (exceptionalObservationPhase a) atTop atTop := by
  have hlin : Tendsto (fun t : ℝ => a * t / 2) atTop atTop := by
    have h := Filter.Tendsto.const_mul_atTop (div_pos ha (by norm_num : (0 : ℝ) < 2))
      (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)
    exact h.congr fun t => by simp only [id_eq]; ring
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ), hlin.eventually_ge_atTop b] with t ht hb
  have hlog : 0 ≤ Real.log (t / 2) := Real.log_nonneg (by linarith only [ht])
  dsimp only [exceptionalObservationPhase]
  linarith only [hlog, hb]

private theorem exists_observationPhase_preimage {a T ξ : ℝ}
    (ha : 0 < a) (hT : 0 < T) (hξ : exceptionalObservationPhase a T ≤ ξ) :
    ∃ t : ℝ, T ≤ t ∧ exceptionalObservationPhase a t = ξ := by
  have hc : ContinuousOn (exceptionalObservationPhase a) (Ici T) := by
    intro t ht
    have hp : 0 < t / 2 := div_pos (hT.trans_le ht) (by norm_num)
    have hdiv : ContinuousAt (fun x : ℝ => x / 2) t := continuousAt_id.div_const (2 : ℝ)
    have hlog : ContinuousAt (fun x : ℝ => Real.log (x / 2)) t :=
      ContinuousAt.comp (g := Real.log) (f := fun x : ℝ => x / 2) (x := t)
        (Real.continuousAt_log (ne_of_gt hp)) hdiv
    have hlin : ContinuousAt (fun x : ℝ => a * x) t :=
      continuousAt_const.mul continuousAt_id
    exact ((hlin.add hlog).div_const (2 : ℝ)).continuousWithinAt
  exact intermediate_value_Ici hc (tendsto_exceptionalObservationPhase ha) hξ

private theorem exceptionalLayerMass_nonneg (F : Finset XiZeroCopy) :
    0 ≤ exceptionalLayerMass F :=
  Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le

private theorem exceptionalLayerMass_pos {F : Finset XiZeroCopy} (hF : F.Nonempty) :
    0 < exceptionalLayerMass F := by
  obtain ⟨q, hq⟩ := hF
  exact (Real.exp_pos (Real.pi * (xiZero q).im / 4)).trans_le
    (Finset.single_le_sum (fun p _ => (Real.exp_pos (Real.pi * (xiZero p).im / 4)).le) hq)

private theorem norm_ordinateWave_sum_le (F : Finset XiZeroCopy) (a t : ℝ) :
    ‖∑ q ∈ F, exceptionalOrdinateWave (xiZero q).im a t‖ ≤ exceptionalLayerMass F := by
  refine (norm_sum_le _ _).trans_eq ?_
  exact Finset.sum_congr rfl fun q _ => norm_exceptionalOrdinateWave _ _ _

private theorem exists_bounded_gap_ordinateWave_revival (F : Finset XiZeroCopy)
    {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ ∀ R : ℝ, 2 ≤ R →
      ∃ t : ℝ, R ≤ t ∧ t ≤ R + L ∧
        ‖(∑ q ∈ F, exceptionalOrdinateWave (xiZero q).im a t) -
          (exceptionalLayerMass F : ℂ)‖ ≤ ε := by
  classical
  let S := exceptionalLayerMass F
  have hS : 0 ≤ S := exceptionalLayerMass_nonneg F
  let δ := ε / (S + 1)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  let u : Fin F.card → ℝ := fun j => (xiZero (F.equivFin.symm j)).im
  obtain ⟨L, hL, hdense⟩ := isBohrAlmostPeriodic_bohrCharVector F.card
    (fun j => -(u j)) δ hδ
  refine ⟨2 * L / a, by positivity, fun R hR => ?_⟩
  have hR0 : 0 < R := (by norm_num : (0 : ℝ) < 2).trans_le hR
  obtain ⟨ξ, hξ, hperiod⟩ := hdense (exceptionalObservationPhase a R)
  obtain ⟨t, ht, hphase⟩ := exists_observationPhase_preimage ha hR0 hξ.1
  have hchar : ∀ j, ‖Complex.exp (I * ((ξ : ℂ) * ((u j : ℝ) : ℂ))) - 1‖ ≤ δ := by
    have hh := hperiod 0
    rw [pi_norm_le_iff_of_nonneg hδ.le] at hh
    intro j
    have hj := hh j
    simp only [Pi.sub_apply, zero_add, bohrCharVector_zero] at hj
    have heq : bohrCharVector (fun j => -(u j)) ξ j =
        Complex.exp (I * ((ξ : ℂ) * ((u j : ℝ) : ℂ))) := by
      rw [bohrCharVector, bohrChar]
      push_cast
      ring_nf
    rwa [heq] at hj
  have hspan : t ≤ R + 2 * L / a := by
    have hlog : Real.log (R / 2) ≤ Real.log (t / 2) :=
      Real.log_le_log (div_pos hR0 (by norm_num))
        (div_le_div_of_nonneg_right ht (by norm_num))
    have hp : exceptionalObservationPhase a t ≤ exceptionalObservationPhase a R + L := by
      rw [hphase]
      exact hξ.2
    dsimp only [exceptionalObservationPhase] at hp
    have hmul : (t - R) * a ≤ 2 * L := by nlinarith only [hp, hlog]
    have hh := (le_div_iff₀ ha).mpr hmul
    linarith only [hh]
  have hreturn : ∀ q ∈ F,
      ‖Complex.exp (I * ((exceptionalObservationPhase a t : ℂ) * ((xiZero q).im : ℂ))) - 1‖ ≤ δ := by
    intro q hq
    have hh := hchar (F.equivFin ⟨q, hq⟩)
    simpa only [u, Equiv.symm_apply_apply, hphase] using hh
  refine ⟨t, ht, hspan, ?_⟩
  have heq : (∑ q ∈ F, exceptionalOrdinateWave (xiZero q).im a t) -
      (exceptionalLayerMass F : ℂ) =
      ∑ q ∈ F, (Real.exp (Real.pi * (xiZero q).im / 4) : ℂ) *
        (Complex.exp (I * ((exceptionalObservationPhase a t : ℂ) * ((xiZero q).im : ℂ))) - 1) := by
    dsimp only [exceptionalLayerMass]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [exceptionalOrdinateWave_eq_character]
    push_cast
    ring
  rw [heq]
  calc
    _ ≤ ∑ q ∈ F, ‖(Real.exp (Real.pi * (xiZero q).im / 4) : ℂ) *
        (Complex.exp (I * ((exceptionalObservationPhase a t : ℂ) * ((xiZero q).im : ℂ))) - 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ F, Real.exp (Real.pi * (xiZero q).im / 4) * δ := by
      refine Finset.sum_le_sum fun q hq => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hreturn q hq) (Real.exp_pos _).le
    _ = S * δ := by rw [← Finset.sum_mul]; rfl
    _ ≤ (S + 1) * δ := by gcongr; linarith
    _ = ε := by
      dsimp only [δ]
      field_simp [ne_of_gt (by linarith only [hS] : 0 < S + 1)]

/-- The actual top-layer mass is the sharp recurrent envelope of the full
normalized prime current. Readings recur near the negative real mass itself
with bounded gaps in height. -/
theorem not_asymptoticAbscissaLaw_has_sharp_recurrent_envelope :
    ¬ AsymptoticAbscissaLaw →
      ∃ (G : Finset XiZeroCopy) (σ β : ℝ),
        1 / 2 < σ ∧ σ < β ∧ β < 1 ∧ G.Nonempty ∧
        (∀ q : XiZeroCopy, q ∈ G ↔ (xiZero q).re = β) ∧
        (∀ q : XiZeroCopy, (xiZero q).re ≤ β) ∧
        0 < exceptionalLayerMass G ∧
        ∀ a : ℝ, 0 < a → Real.pi / 2 < a * (β - σ) →
          ∀ ε : ℝ, 0 < ε →
            (∀ᶠ t : ℝ in atTop,
              ‖normalizedExceptionalCurrent σ β a t‖ ≤ exceptionalLayerMass G + ε) ∧
            ∃ L : ℝ, 0 < L ∧ ∀ᶠ R : ℝ in atTop,
              ∃ t : ℝ, R ≤ t ∧ t ≤ R + L ∧
                ‖normalizedExceptionalCurrent σ β a t + (exceptionalLayerMass G : ℂ)‖ < ε := by
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
  refine ⟨G, σ, β, by linarith only [hθ, hgap], hσβ, hβ1, hG, htop, hall,
    exceptionalLayerMass_pos hG, ?_⟩
  intro a ha hsuper ε hε
  have hp : Tendsto (fun t : ℝ => normalizedExceptionalCurrent σ β a t +
      ∑ q ∈ G, exceptionalOrdinateWave (xiZero q).im a t) atTop (𝓝 0) :=
    hprofile a ha hsuper
  have hpn := hp.norm
  simp only [norm_zero] at hpn
  have herr := hpn.eventually (eventually_lt_nhds hε)
  constructor
  · filter_upwards [herr] with t ht
    have hn := norm_sub_le
      (normalizedExceptionalCurrent σ β a t + ∑ q ∈ G, exceptionalOrdinateWave (xiZero q).im a t)
      (∑ q ∈ G, exceptionalOrdinateWave (xiZero q).im a t)
    rw [add_sub_cancel_right] at hn
    have hb := norm_ordinateWave_sum_le G a t
    linarith only [hn, ht, hb]
  · have hhalf := hpn.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < ε / 2))
    obtain ⟨T, hT⟩ := eventually_atTop.1 hhalf
    obtain ⟨L, hL, hreturn⟩ := exists_bounded_gap_ordinateWave_revival G ha
      (by positivity : 0 < ε / 2)
    refine ⟨L, hL, ?_⟩
    filter_upwards [eventually_ge_atTop (max T 2)] with R hR
    obtain ⟨t, ht, hspan, hmass⟩ := hreturn R ((le_max_right _ _).trans hR)
    refine ⟨t, ht, hspan, ?_⟩
    have he := hT t (((le_max_left _ _).trans hR).trans ht)
    have hn := norm_sub_le
      (normalizedExceptionalCurrent σ β a t + ∑ q ∈ G, exceptionalOrdinateWave (xiZero q).im a t)
      ((∑ q ∈ G, exceptionalOrdinateWave (xiZero q).im a t) - (exceptionalLayerMass G : ℂ))
    have hid : normalizedExceptionalCurrent σ β a t +
        (∑ q ∈ G, exceptionalOrdinateWave (xiZero q).im a t) -
        ((∑ q ∈ G, exceptionalOrdinateWave (xiZero q).im a t) - (exceptionalLayerMass G : ℂ)) =
        normalizedExceptionalCurrent σ β a t + (exceptionalLayerMass G : ℂ) := by ring
    rw [hid] at hn
    linarith only [hn, he, hmass]

/-- A finite exceptional layer forces arbitrarily large excursions of the
corrected infinite prime current above every height. -/
theorem not_asymptoticAbscissaLaw_has_unbounded_corrected_current :
    ¬ AsymptoticAbscissaLaw →
      ∃ σ a : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ 0 < a ∧
        ∀ B R : ℝ, ∃ t : ℝ, R ≤ t ∧ B ≤ ‖correctedExceptionalCurrent σ a t‖ := by
  intro hnot
  obtain ⟨G, σ, β, hσ, hσβ, hβ1, _, _, _, hS, henvelope⟩ :=
    not_asymptoticAbscissaLaw_has_sharp_recurrent_envelope hnot
  let S := exceptionalLayerMass G
  let a := Real.pi / (β - σ)
  have ha : 0 < a := div_pos Real.pi_pos (sub_pos.mpr hσβ)
  have hsuper : Real.pi / 2 < a * (β - σ) := by
    dsimp only [a]
    rw [div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hσβ))]
    linarith only [Real.pi_pos]
  have hr : 0 < gaussianObservationRate (β : ℂ) σ a := by
    simp only [gaussianObservationRate, Complex.ofReal_re]
    linarith only [hsuper]
  let P : ℝ → ℂ := fun t =>
    gaussianMBKernel (Real.exp (-a * t)) ((β : ℂ) - ((σ : ℂ) + t * I))
  have hP : Tendsto (fun t => ‖P t‖) atTop atTop :=
    tendsto_norm_gaussianMode_atTop_of_positive_rate (β : ℂ) σ a hr
  obtain ⟨L, _, hrec⟩ := (henvelope a ha hsuper (S / 2)
    (by change 0 < exceptionalLayerMass G / 2; positivity)).2
  obtain ⟨U, hU⟩ := eventually_atTop.1 hrec
  refine ⟨σ, a, hσ, hσβ.trans hβ1, ha, fun B R => ?_⟩
  obtain ⟨T, hT⟩ := eventually_atTop.1
    (hP.eventually (eventually_ge_atTop (2 * (|B| + 1) / S)))
  obtain ⟨t, ht, _, hnear⟩ := hU (max (max R T) U) (le_max_right _ _)
  have hRT : max R T ≤ t := (le_max_left _ _).trans ht
  have hp := hT t ((le_max_right _ _).trans hRT)
  have hS0 : 0 < S := hS
  have hp0 : 0 < ‖P t‖ := (by positivity : 0 < 2 * (|B| + 1) / S).trans_le hp
  have hpne : P t ≠ 0 := norm_pos_iff.mp hp0
  have hn := norm_sub_le (normalizedExceptionalCurrent σ β a t + (S : ℂ))
    (normalizedExceptionalCurrent σ β a t)
  rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS0] at hn
  have hj : S / 2 < ‖normalizedExceptionalCurrent σ β a t‖ := by
    linarith only [hn, hnear]
  have hb := mul_le_mul_of_nonneg_left hp (div_pos hS0 (by norm_num : (0 : ℝ) < 2)).le
  have hscale : S / 2 * (2 * (|B| + 1) / S) = |B| + 1 := by
    field_simp [ne_of_gt hS0]
  rw [hscale] at hb
  have hbig := mul_lt_mul_of_pos_right hj hp0
  have heq : ‖normalizedExceptionalCurrent σ β a t‖ * ‖P t‖ =
      ‖correctedExceptionalCurrent σ a t‖ := by
    rw [← norm_mul]
    exact congrArg norm (div_mul_cancel₀ _ hpne)
  rw [heq] at hbig
  exact ⟨t, (le_max_left _ _).trans hRT, by linarith only [hb, hbig, le_abs_self B]⟩

#print axioms not_asymptoticAbscissaLaw_has_sharp_recurrent_envelope
#print axioms not_asymptoticAbscissaLaw_has_unbounded_corrected_current

end GaloisForLFunctions.ExceptionalLayerTheory
