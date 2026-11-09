import GaloisForLFunctions.ExceptionalLayerTheory.TheSharpRecurrentLayerEnvelope

/-!
# Local filters recover the top divisor

Fixed height shifts become characters of the top ordinates after Gaussian
normalization. A polynomial filter annihilates every unwanted ordinate and
recovers the target's multiplicity. The sample spacing can be arbitrarily
small, so cancellation cannot hide a finite top throughout a fixed window.
-/

open Complex Filter Set Topology RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Character acquired by a top ordinate under a fixed height shift. -/
def ordinateShiftNode (γ a h : ℝ) : ℂ :=
  Complex.exp (((γ * a * h / 2 : ℝ) : ℂ) * I)

private theorem tendsto_log_shift_difference (h : ℝ) :
    Tendsto (fun t : ℝ => Real.log ((t + h) / 2) - Real.log (t / 2))
      atTop (𝓝 0) := by
  have hr : Tendsto (fun t : ℝ => 1 + h / t) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop))
  have hl := (Real.continuousAt_log one_ne_zero).tendsto.comp hr
  simp only [Real.log_one, Function.comp_def] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (|h| + 1)] with t ht
  have ht0 : 0 < t := by linarith only [ht, abs_nonneg h]
  have hth : 0 < t + h := by linarith only [ht, neg_abs_le h]
  rw [← Real.log_div (ne_of_gt (div_pos hth (by norm_num)))
    (ne_of_gt (div_pos ht0 (by norm_num)))]
  congr 1
  field_simp

/-- Gamma's logarithmic phase has vanishing increment error under a fixed shift. -/
theorem tendsto_ordinateWave_shift_ratio (γ a h : ℝ) :
    Tendsto (fun t : ℝ => exceptionalOrdinateWave γ a (t + h) /
      exceptionalOrdinateWave γ a t) atTop (𝓝 (ordinateShiftNode γ a h)) := by
  have hl := (Complex.continuous_ofReal.tendsto 0).comp (tendsto_log_shift_difference h)
  have hx := (hl.const_mul (((γ / 2 : ℝ) : ℂ) * I)).const_add
    (((γ * a * h / 2 : ℝ) : ℂ) * I)
  simp only [Complex.ofReal_zero, mul_zero, add_zero, Function.comp_def] at hx
  have he := (Complex.continuous_exp.tendsto _).comp hx
  simp only [Function.comp_def] at he
  apply he.congr
  intro t
  rw [exceptionalOrdinateWave, exceptionalOrdinateWave, ← Complex.exp_sub]
  congr 1
  push_cast
  ring

private theorem tendsto_ordinateWave_shift_error (γ a h : ℝ) :
    Tendsto (fun t : ℝ => exceptionalOrdinateWave γ a (t + h) -
      ordinateShiftNode γ a h * exceptionalOrdinateWave γ a t) atTop (𝓝 0) := by
  have hh := ((tendsto_ordinateWave_shift_ratio γ a h).sub_const
    (ordinateShiftNode γ a h)).norm.const_mul (Real.exp (Real.pi * γ / 4))
  simp only [sub_self, norm_zero, mul_zero] at hh
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply hh.congr
  intro t
  have hn : exceptionalOrdinateWave γ a t ≠ 0 := Complex.exp_ne_zero _
  rw [show exceptionalOrdinateWave γ a (t + h) -
    ordinateShiftNode γ a h * exceptionalOrdinateWave γ a t =
      exceptionalOrdinateWave γ a t *
        (exceptionalOrdinateWave γ a (t + h) / exceptionalOrdinateWave γ a t -
          ordinateShiftNode γ a h) by field_simp,
    norm_mul, norm_exceptionalOrdinateWave]

private theorem ordinateShiftNode_nat_mul (γ a h : ℝ) (j : ℕ) :
    ordinateShiftNode γ a (j * h) = ordinateShiftNode γ a h ^ j := by
  rw [ordinateShiftNode, ordinateShiftNode, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- A polynomial acting by height shifts acts by evaluation on each top mode. -/
theorem tendsto_polynomial_filtered_ordinateWave (P : Polynomial ℂ) (γ a h : ℝ) :
    Tendsto (fun t : ℝ =>
      (∑ j ∈ Finset.range (P.natDegree + 1),
        P.coeff j * exceptionalOrdinateWave γ a (t + j * h)) -
      P.eval (ordinateShiftNode γ a h) * exceptionalOrdinateWave γ a t)
      atTop (𝓝 0) := by
  have hh := tendsto_finsetSum (Finset.range (P.natDegree + 1))
    (fun j _ => (tendsto_ordinateWave_shift_error γ a (j * h)).const_mul (P.coeff j))
  simp only [mul_zero, Finset.sum_const_zero] at hh
  apply hh.congr
  intro t
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [ordinateShiftNode_nat_mul]
  ring

/-- Finite polynomial combination of normalized readings at equally spaced heights. -/
def filteredExceptionalCurrent (P : Polynomial ℂ) (σ β a h t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (P.natDegree + 1),
    P.coeff j * normalizedExceptionalCurrent σ β a (t + j * h)

private theorem tendsto_filtered_current_profile
    (G : Finset XiZeroCopy) (σ β a h : ℝ) (P : Polynomial ℂ)
    (hprofile : Tendsto (fun t : ℝ => normalizedExceptionalCurrent σ β a t +
      ∑ q ∈ G, exceptionalOrdinateWave (xiZero q).im a t) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => filteredExceptionalCurrent P σ β a h t +
      ∑ q ∈ G, P.eval (ordinateShiftNode (xiZero q).im a h) *
        exceptionalOrdinateWave (xiZero q).im a t) atTop (𝓝 0) := by
  have hs := tendsto_finsetSum (Finset.range (P.natDegree + 1))
    (fun j _ => (hprofile.comp (Filter.tendsto_atTop_add_const_right atTop (j * h)
      (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop))).const_mul (P.coeff j))
  have hw := tendsto_finsetSum G
    (fun q _ => tendsto_polynomial_filtered_ordinateWave P (xiZero q).im a h)
  have hh := hs.sub hw
  simp only [mul_zero, Finset.sum_const_zero, sub_zero] at hh
  apply hh.congr
  intro t
  simp only [Function.comp_def, id_eq, filteredExceptionalCurrent, mul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.range (P.natDegree + 1)) (t := G)]
  ring

private theorem tendsto_div_ordinateWave_zero {f : ℝ → ℂ}
    (hf : Tendsto f atTop (𝓝 0)) (γ a : ℝ) :
    Tendsto (fun t => f t / exceptionalOrdinateWave γ a t) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hh := hf.norm.div_const (Real.exp (Real.pi * γ / 4))
  simpa only [norm_div, norm_exceptionalOrdinateWave, norm_zero, zero_div] using hh

private theorem filtered_current_extracts_ordinate
    (G : Finset XiZeroCopy) (σ β a h γ : ℝ) (P : Polynomial ℂ)
    (hprofile : Tendsto (fun t : ℝ => normalizedExceptionalCurrent σ β a t +
      ∑ q ∈ G, exceptionalOrdinateWave (xiZero q).im a t) atTop (𝓝 0))
    (hkill : ∀ q ∈ G, (xiZero q).im ≠ γ →
      P.eval (ordinateShiftNode (xiZero q).im a h) = 0) :
    Tendsto (fun t : ℝ => filteredExceptionalCurrent P σ β a h t /
      exceptionalOrdinateWave γ a t) atTop
      (𝓝 (-((G.filter (fun q => (xiZero q).im = γ)).card : ℂ) *
        P.eval (ordinateShiftNode γ a h))) := by
  classical
  let c : ℂ := ((G.filter (fun q => (xiZero q).im = γ)).card : ℂ) *
    P.eval (ordinateShiftNode γ a h)
  have heq (t : ℝ) :
      (∑ q ∈ G, P.eval (ordinateShiftNode (xiZero q).im a h) *
        exceptionalOrdinateWave (xiZero q).im a t) = c * exceptionalOrdinateWave γ a t := by
    rw [← Finset.sum_filter_of_ne (p := fun q => (xiZero q).im = γ)]
    · calc
        _ = ∑ _q ∈ G.filter (fun q => (xiZero q).im = γ),
            P.eval (ordinateShiftNode γ a h) * exceptionalOrdinateWave γ a t := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [(Finset.mem_filter.mp hq).2]
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; dsimp only [c]; ring
    · intro q hq hn
      by_contra hne
      exact hn (by rw [hkill q hq hne, zero_mul])
  have hh := tendsto_div_ordinateWave_zero
    (tendsto_filtered_current_profile G σ β a h P hprofile) γ a
  have hh' := hh.sub_const c
  simp only [zero_sub] at hh'
  have hfinal : Tendsto (fun t : ℝ => filteredExceptionalCurrent P σ β a h t /
      exceptionalOrdinateWave γ a t) atTop (𝓝 (-c)) := hh'.congr fun t => by
    have hne : exceptionalOrdinateWave γ a t ≠ 0 := Complex.exp_ne_zero _
    rw [heq, add_div, mul_div_cancel_right₀ _ hne]
    ring
  simpa only [c, neg_mul] using hfinal

private theorem exists_small_ordinateShift_injective (S : Finset ℝ)
    {a B : ℝ} (ha : 0 < a) (hB : 0 < B) :
    ∃ h : ℝ, 0 < h ∧ h < B ∧
      Set.InjOn (fun γ => ordinateShiftNode γ a h) (S : Set ℝ) := by
  classical
  let M : ℝ := ∑ γ ∈ S, |γ|
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hden : 0 < a * (M + 1) := mul_pos ha (by linarith only [hM])
  obtain ⟨h, hh0, hh⟩ := exists_between
    (lt_min hB (div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) hden))
  have hhB : h < B := hh.trans_le (min_le_left _ _)
  have hhm : h * (a * (M + 1)) < 2 * Real.pi :=
    (lt_div_iff₀ hden).mp (hh.trans_le (min_le_right _ _))
  have hphase : ∀ γ ∈ S, |γ * a * h / 2| < Real.pi := by
    intro γ hγ
    have hb : |γ| ≤ M := Finset.single_le_sum (fun δ _ => abs_nonneg δ) hγ
    have hm := mul_le_mul_of_nonneg_right hb (mul_pos ha hh0).le
    rw [abs_div, abs_mul, abs_mul, abs_of_pos ha, abs_of_pos hh0,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith only [hm, hhm, mul_pos ha hh0]
  refine ⟨h, hh0, hhB, ?_⟩
  intro γ hγ δ hδ he
  have hg := abs_lt.mp (hphase γ hγ)
  have hd := abs_lt.mp (hphase δ hδ)
  have hex := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (by simpa using hg.1) (by simpa using hg.2.le)
    (by simpa using hd.1) (by simpa using hd.2.le) he
  have heq : γ * a * h / 2 = δ * a * h / 2 := by
    simpa using congrArg Complex.im hex
  apply mul_right_cancel₀ (mul_ne_zero ha.ne' hh0.ne')
  linarith only [heq]

/-- The finite top filter vanishes at every other ordinate, with multiplicities retained. -/
def topOrdinateFilter (G : Finset XiZeroCopy) (γ a h : ℝ) : Polynomial ℂ :=
  ∏ q ∈ G.filter (fun q => (xiZero q).im ≠ γ),
    (Polynomial.X - Polynomial.C (ordinateShiftNode (xiZero q).im a h))

private theorem topOrdinateFilter_kills (G : Finset XiZeroCopy) (γ a h : ℝ)
    {q : XiZeroCopy} (hq : q ∈ G) (hne : (xiZero q).im ≠ γ) :
    (topOrdinateFilter G γ a h).eval (ordinateShiftNode (xiZero q).im a h) = 0 := by
  classical
  simp only [topOrdinateFilter, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  exact Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨hq, hne⟩) (sub_self _)

private theorem topOrdinateFilter_survives (G : Finset XiZeroCopy) (γ a h : ℝ)
    (hγ : γ ∈ G.image (fun q => (xiZero q).im))
    (hinj : Set.InjOn (fun δ => ordinateShiftNode δ a h)
      (G.image (fun q => (xiZero q).im) : Set ℝ)) :
    (topOrdinateFilter G γ a h).eval (ordinateShiftNode γ a h) ≠ 0 := by
  classical
  simp only [topOrdinateFilter, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro q hq
  obtain ⟨hqG, hqγ⟩ := Finset.mem_filter.mp hq
  exact sub_ne_zero.mpr fun he => hqγ
    (hinj (Finset.mem_image_of_mem _ hqG) hγ he.symm)

private theorem topOrdinateFilter_degree_le (G : Finset XiZeroCopy) (γ a h : ℝ) :
    (topOrdinateFilter G γ a h).natDegree ≤ G.card := by
  classical
  unfold topOrdinateFilter
  calc
    _ ≤ ∑ q ∈ G.filter (fun q => (xiZero q).im ≠ γ),
        (Polynomial.X - Polynomial.C (ordinateShiftNode (xiZero q).im a h)).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ = (G.filter (fun q => (xiZero q).im ≠ γ)).card := by simp
    _ ≤ G.card := Finset.card_filter_le _ _

/-- Every actual top ordinate is recovered from finitely many readings inside
any prescribed positive height window. No condition on ordinate relations or
multiplicities is needed. -/
theorem not_asymptoticAbscissaLaw_has_local_divisor_filters :
    ¬ AsymptoticAbscissaLaw →
      ∃ (G : Finset XiZeroCopy) (σ β : ℝ),
        1 / 2 < σ ∧ σ < β ∧ β < 1 ∧ G.Nonempty ∧
        (∀ q : XiZeroCopy, q ∈ G ↔ (xiZero q).re = β) ∧
        (∀ q : XiZeroCopy, (xiZero q).re ≤ β) ∧
        ∀ a : ℝ, 0 < a → Real.pi / 2 < a * (β - σ) →
          ∀ L : ℝ, 0 < L → ∃ h : ℝ, 0 < h ∧
            (∀ j : ℕ, j ≤ G.card → (j : ℝ) * h < L) ∧
            ∀ q ∈ G,
              (topOrdinateFilter G (xiZero q).im a h).natDegree ≤ G.card ∧
              (topOrdinateFilter G (xiZero q).im a h).eval
                (ordinateShiftNode (xiZero q).im a h) ≠ 0 ∧
              Tendsto (fun t : ℝ =>
                filteredExceptionalCurrent (topOrdinateFilter G (xiZero q).im a h) σ β a h t /
                  exceptionalOrdinateWave (xiZero q).im a t) atTop
                (𝓝 (-((G.filter (fun p => (xiZero p).im = (xiZero q).im)).card : ℂ) *
                  (topOrdinateFilter G (xiZero q).im a h).eval
                    (ordinateShiftNode (xiZero q).im a h))) := by
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
  refine ⟨G, σ, β, by linarith only [hθ, hgap], hσβ, hβ1, hG, htop, hall, ?_⟩
  intro a ha hsuper L hL
  obtain ⟨h, hh0, hhB, hinj⟩ := exists_small_ordinateShift_injective
    (G.image (fun q => (xiZero q).im)) ha
    (div_pos hL (by positivity : (0 : ℝ) < (G.card : ℝ) + 1))
  refine ⟨h, hh0, ?_, fun q hq => ?_⟩
  · intro j hj
    have hjR : (j : ℝ) ≤ G.card := by exact_mod_cast hj
    have hb := (lt_div_iff₀ (by positivity : (0 : ℝ) < (G.card : ℝ) + 1)).mp hhB
    have hc := mul_le_mul_of_nonneg_right hjR hh0.le
    nlinarith only [hb, hc, hh0]
  · exact ⟨topOrdinateFilter_degree_le G _ a h,
      topOrdinateFilter_survives G _ a h (Finset.mem_image_of_mem _ hq) hinj,
      filtered_current_extracts_ordinate G σ β a h _ _ (hprofile a ha hsuper)
        (fun p hp hne => topOrdinateFilter_kills G _ a h hp hne)⟩

private theorem exists_positive_local_reading (P : Polynomial ℂ) (σ β a h γ : ℝ)
    {c : ℂ} (hc : c ≠ 0)
    (hlim : Tendsto (fun t : ℝ => filteredExceptionalCurrent P σ β a h t /
      exceptionalOrdinateWave γ a t) atTop (𝓝 c)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ t : ℝ in atTop,
      ∃ j ∈ Finset.range (P.natDegree + 1),
        ε ≤ ‖normalizedExceptionalCurrent σ β a (t + j * h)‖ := by
  let K : ℝ := ∑ j ∈ Finset.range (P.natDegree + 1), ‖P.coeff j‖
  have hK : 0 ≤ K := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hc
  let E : ℝ := Real.exp (Real.pi * γ / 4)
  have hE : 0 < E := Real.exp_pos _
  let ε : ℝ := ‖c‖ * E / (2 * (K + 1))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hlim.norm.eventually
    (eventually_gt_nhds (show ‖c‖ / 2 < ‖c‖ by linarith only [hc0]))]
    with t ht
  rw [norm_div, norm_exceptionalOrdinateWave] at ht
  have hlarge : ‖c‖ / 2 * E < ‖filteredExceptionalCurrent P σ β a h t‖ :=
    (lt_div_iff₀ hE).mp ht
  by_contra hn
  push Not at hn
  have hsmall : ‖filteredExceptionalCurrent P σ β a h t‖ ≤ K * ε := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ j ∈ Finset.range (P.natDegree + 1), ‖P.coeff j‖ * ε := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hn j hj).le (norm_nonneg _)
      _ = K * ε := (Finset.sum_mul _ _ _).symm
  have hpay : K * ε < ‖c‖ / 2 * E := by
    dsimp only [ε]
    rw [mul_div_assoc', div_lt_iff₀ (by positivity : 0 < 2 * (K + 1))]
    nlinarith only [mul_pos hc0 hE]
  exact (not_lt_of_ge hsmall) (hpay.trans hlarge)

/-- Every sufficiently late window of any prescribed positive length contains
an arbitrarily large corrected-current reading. This holds for every finite
top layer, including those with cancelling ordinate phases. -/
theorem not_asymptoticAbscissaLaw_has_short_window_growth :
    ¬ AsymptoticAbscissaLaw →
      ∃ σ β : ℝ, 1 / 2 < σ ∧ σ < β ∧ β < 1 ∧
        ∀ a : ℝ, 0 < a → Real.pi / 2 < a * (β - σ) →
          ∀ L : ℝ, 0 < L → ∀ B : ℝ, ∀ᶠ t : ℝ in atTop,
            ∃ u ∈ Set.Icc t (t + L), B ≤ ‖correctedExceptionalCurrent σ a u‖ := by
  classical
  intro hnot
  obtain ⟨G, σ, β, hσ, hσβ, hβ, hG, _, _, hfilters⟩ :=
    not_asymptoticAbscissaLaw_has_local_divisor_filters hnot
  obtain ⟨q, hq⟩ := hG
  refine ⟨σ, β, hσ, hσβ, hβ, ?_⟩
  intro a ha hsuper L hL B
  obtain ⟨h, hh0, hwindow, hfilter⟩ := hfilters a ha hsuper L hL
  obtain ⟨hdegree, heval, hlim⟩ := hfilter q hq
  let P := topOrdinateFilter G (xiZero q).im a h
  have hm : 0 < (G.filter (fun p => (xiZero p).im = (xiZero q).im)).card :=
    Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, rfl⟩⟩
  have hc : -((G.filter (fun p => (xiZero p).im = (xiZero q).im)).card : ℂ) *
      P.eval (ordinateShiftNode (xiZero q).im a h) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm))) heval
  obtain ⟨ε, hε, hreading⟩ := exists_positive_local_reading P σ β a h (xiZero q).im hc hlim
  have hr : 0 < gaussianObservationRate (β : ℂ) σ a := by
    simp only [gaussianObservationRate, Complex.ofReal_re]
    linarith only [hsuper]
  have hmode := tendsto_norm_gaussianMode_atTop_of_positive_rate (β : ℂ) σ a hr
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hmode.eventually_ge_atTop ((|B| + 1) / ε))
  filter_upwards [hreading, eventually_ge_atTop T] with t hread ht
  obtain ⟨j, hj, hJ⟩ := hread
  have hjd : j ≤ P.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hspan := hwindow j (hjd.trans hdegree)
  have hjh : 0 ≤ (j : ℝ) * h := mul_nonneg (Nat.cast_nonneg j) hh0.le
  let u : ℝ := t + j * h
  have htu : t ≤ u := by dsimp only [u]; linarith only [hjh]
  have hp := hT u (ht.trans htu)
  have hp0 : 0 < ‖gaussianMBKernel (Real.exp (-a * u))
      ((β : ℂ) - ((σ : ℂ) + u * I))‖ :=
    (by positivity : 0 < (|B| + 1) / ε).trans_le hp
  have hraw := mul_le_mul_of_nonneg_right hJ hp0.le
  have heq : ‖normalizedExceptionalCurrent σ β a u‖ *
      ‖gaussianMBKernel (Real.exp (-a * u)) ((β : ℂ) - ((σ : ℂ) + u * I))‖ =
        ‖correctedExceptionalCurrent σ a u‖ := by
    rw [normalizedExceptionalCurrent, norm_div, div_mul_cancel₀ _ hp0.ne']
  change ε * ‖gaussianMBKernel (Real.exp (-a * u))
    ((β : ℂ) - ((σ : ℂ) + u * I))‖ ≤
      ‖normalizedExceptionalCurrent σ β a u‖ *
        ‖gaussianMBKernel (Real.exp (-a * u)) ((β : ℂ) - ((σ : ℂ) + u * I))‖ at hraw
  rw [heq] at hraw
  have hb := mul_le_mul_of_nonneg_left hp hε.le
  rw [mul_div_cancel₀ _ hε.ne'] at hb
  refine ⟨u, ⟨htu, ?_⟩, ?_⟩
  · dsimp only [u]
    linarith only [hspan]
  · linarith only [hb, hraw, le_abs_self B]

#print axioms tendsto_ordinateWave_shift_ratio
#print axioms tendsto_polynomial_filtered_ordinateWave
#print axioms not_asymptoticAbscissaLaw_has_local_divisor_filters
#print axioms not_asymptoticAbscissaLaw_has_short_window_growth

end GaloisForLFunctions.ExceptionalLayerTheory
