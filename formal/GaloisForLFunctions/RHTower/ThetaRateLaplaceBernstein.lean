import GaloisForLFunctions.RHTower.ThetaTranslationMeasureGauge
import GaloisForLFunctions.HTGeometry.RateMobiusInversion

/-!
# Laplace transforms of positive rate measures and prime-deleted theta fluxes

For a positive measure `ν` on `[0, ∞)` let `L_ν(t) = ∫ e^{-tλ} dν(λ)`.

* Laplace uniqueness and order: two measures with finite equal Laplace transforms on `(0, ∞)`
  coincide, and complete monotonicity of `L_{ν₁} - L_{ν₂}` forces `ν₂ ≤ ν₁` (exponential tilts reduce
  both to the finite case).
* Bernstein–Widder without a finiteness assumption at `t = 0`: every completely monotone function on
  `(0, ∞)` is the Laplace transform of a positive measure on `[0, ∞)`.
* Prime dilations: `L_{A_n ν}(t) = n² L_ν(n² t)`, and the two parity parts of a finite deletion
  `D_S ν` are finite word sums of such transforms.
* Deleted fluxes: `b_{D_S f}(t) = Σ_{T ⊆ S} (-1)^{|T|} (∏T)² b_f((∏T)² t)` for every flux source `f`.
  Consequently, if `b_f = L_ν` and `b_{D_S f}` is completely monotone, the rate deletion `D_S ν` is a
  positive measure.
* No residual at rate zero: the Bernstein measure of the flux of a flux source has no mass on
  `(-∞, 0]`, since `b_f(t) → 0` as `t → ∞`.
-/
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## Laplace transforms of rate measures -/

/-- The Laplace transform `∫ e^{-tλ} dν(λ)` of a positive rate measure. -/
def rateLaplace (ν : Measure ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ l, ENNReal.ofReal (Real.exp (-(t * l))) ∂ν

/-- The exponential tilt `e^{-t₀λ} ν`. -/
def rateTilt (t₀ : ℝ) (ν : Measure ℝ) : Measure ℝ :=
  ν.withDensity fun l => ENNReal.ofReal (Real.exp (-(t₀ * l)))

theorem measurable_rateExpKernel (t : ℝ) :
    Measurable fun l : ℝ => ENNReal.ofReal (Real.exp (-(t * l))) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id).neg)

theorem rateTilt_univ (t₀ : ℝ) (ν : Measure ℝ) : rateTilt t₀ ν univ = rateLaplace ν t₀ := by
  rw [rateTilt, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, rateLaplace]

theorem isFiniteMeasure_rateTilt {t₀ : ℝ} {ν : Measure ℝ} (h : rateLaplace ν t₀ ≠ ∞) :
    IsFiniteMeasure (rateTilt t₀ ν) :=
  ⟨by rw [rateTilt_univ]; exact h.lt_top⟩

theorem rateTilt_compl_Ici {t₀ : ℝ} {ν : Measure ℝ} (hν : ν (Ici 0)ᶜ = 0) :
    rateTilt t₀ ν (Ici 0)ᶜ = 0 := by
  rw [rateTilt, withDensity_apply _ measurableSet_Ici.compl]
  exact setLIntegral_measure_zero _ _ hν

theorem rateExpKernel_mul (a b l : ℝ) :
    ENNReal.ofReal (Real.exp (-(a * l))) * ENNReal.ofReal (Real.exp (-(b * l))) =
      ENNReal.ofReal (Real.exp (-((a + b) * l))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

theorem rateLaplace_rateTilt (t₀ t : ℝ) (ν : Measure ℝ) :
    rateLaplace (rateTilt t₀ ν) t = rateLaplace ν (t₀ + t) := by
  rw [rateLaplace, rateTilt, lintegral_withDensity_eq_lintegral_mul _ (measurable_rateExpKernel t₀)
    (measurable_rateExpKernel t), rateLaplace]
  exact lintegral_congr fun l => by simp only [Pi.mul_apply]; rw [rateExpKernel_mul]

/-- The real Laplace integral of the tilt is the tilted transform. -/
theorem integral_exp_rateTilt (t₀ : ℝ) (ν : Measure ℝ) (u : ℝ) :
    ∫ r, Real.exp (-u * r) ∂(rateTilt t₀ ν) = (rateLaplace ν (t₀ + u)).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun r => (Real.exp_pos _).le)
    (by fun_prop), ← rateLaplace_rateTilt]
  congr 1
  exact lintegral_congr fun r => by ring_nf

/-- Tilting back: `e^{t₀λ} (e^{-t₀λ} ν) = ν`. -/
theorem rateTilt_neg_rateTilt (t₀ : ℝ) (ν : Measure ℝ) : rateTilt (-t₀) (rateTilt t₀ ν) = ν := by
  rw [rateTilt, rateTilt, ← withDensity_mul _ (measurable_rateExpKernel t₀) (measurable_rateExpKernel (-t₀))]
  conv_rhs => rw [← withDensity_one (μ := ν)]
  congr 1
  funext l
  rw [Pi.mul_apply, rateExpKernel_mul, show (t₀ + -t₀) * l = 0 by ring, neg_zero, Real.exp_zero,
    ENNReal.ofReal_one, Pi.one_apply]

theorem rateTilt_rateTilt (a b : ℝ) (ν : Measure ℝ) : rateTilt a (rateTilt b ν) = rateTilt (b + a) ν := by
  rw [rateTilt, rateTilt, ← withDensity_mul _ (measurable_rateExpKernel b) (measurable_rateExpKernel a),
    rateTilt]
  congr 1
  funext l
  rw [Pi.mul_apply, rateExpKernel_mul]

theorem rateTilt_mono (t₀ : ℝ) {μ ν : Measure ℝ} (h : μ ≤ ν) : rateTilt t₀ μ ≤ rateTilt t₀ ν :=
  Measure.le_iff.2 fun E hE => by
    rw [rateTilt, rateTilt, withDensity_apply _ hE, withDensity_apply _ hE]
    exact lintegral_mono' (Measure.restrict_mono subset_rfl h) le_rfl

theorem toReal_rateLaplace_eq_integral {τ : Measure ℝ} (t : ℝ) :
    (rateLaplace τ t).toReal = ∫ r, Real.exp (-t * r) ∂τ := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun r => (Real.exp_pos _).le)
    (by fun_prop), rateLaplace]
  congr 1
  exact lintegral_congr fun r => by ring_nf

/-- **Laplace uniqueness** for rate measures carried by `[0, ∞)` with finite Laplace transform. -/
theorem eq_of_rateLaplace_eq {ν ν' : Measure ℝ} (hν : ν (Ici 0)ᶜ = 0) (hν' : ν' (Ici 0)ᶜ = 0)
    (hfin : rateLaplace ν 1 ≠ ∞) (hfin' : rateLaplace ν' 1 ≠ ∞)
    (h : ∀ t, 0 < t → rateLaplace ν t = rateLaplace ν' t) : ν = ν' := by
  haveI := isFiniteMeasure_rateTilt hfin
  haveI := isFiniteMeasure_rateTilt hfin'
  have heq : rateTilt 1 ν = rateTilt 1 ν' :=
    measure_eq_of_laplace_eq (rateTilt_compl_Ici hν) (rateTilt_compl_Ici hν') fun u hu => by
      rw [integral_exp_rateTilt, integral_exp_rateTilt, h _ (by linarith)]
  rw [← rateTilt_neg_rateTilt 1 ν, heq, rateTilt_neg_rateTilt]

/-- **Completely monotone differences.** If `t ↦ L_{ν₁}(t) - L_{ν₂}(t)` is completely monotone on
`(0, ∞)`, then `ν₂ ≤ ν₁`. -/
theorem le_of_completelyMonotoneOn_rateLaplace_sub {ν₁ ν₂ : Measure ℝ} (h₁ : ν₁ (Ici 0)ᶜ = 0)
    (h₂ : ν₂ (Ici 0)ᶜ = 0) (hf₁ : rateLaplace ν₁ 1 ≠ ∞) (hf₂ : rateLaplace ν₂ 1 ≠ ∞)
    (hCM : CompletelyMonotoneOn fun t => (rateLaplace ν₁ t).toReal - (rateLaplace ν₂ t).toReal) :
    ν₂ ≤ ν₁ := by
  haveI := isFiniteMeasure_rateTilt hf₁
  haveI := isFiniteMeasure_rateTilt hf₂
  have hle : rateTilt 1 ν₂ ≤ rateTilt 1 ν₁ := by
    refine le_of_completelyMonotoneOn_laplace_sub (rateTilt_compl_Ici h₁) (rateTilt_compl_Ici h₂) ?_
    refine (completelyMonotoneOn_comp_add_left hCM zero_le_one).congr_Ioi fun u _ => ?_
    simp only
    rw [integral_exp_rateTilt, integral_exp_rateTilt]
  rw [← rateTilt_neg_rateTilt 1 ν₁, ← rateTilt_neg_rateTilt 1 ν₂]
  exact rateTilt_mono _ hle

/-- **Bernstein--Widder on `(0, ∞)`.** Every completely monotone profile on the open half-line is
the Laplace transform of a positive measure carried by `[0, ∞)` with finite Laplace transform at
every positive time; no boundedness at `0` is required. -/
theorem exists_rateMeasure_of_completelyMonotoneOn {H : ℝ → ℝ} (hH : CompletelyMonotoneOn H) :
    ∃ ν : Measure ℝ, ν (Ici 0)ᶜ = 0 ∧ (∀ t, 0 < t → rateLaplace ν t ≠ ∞) ∧
      ∀ t, 0 < t → H t = (rateLaplace ν t).toReal := by
  have hshift : ∀ s : ℝ, 0 < s → ∃ τ : Measure ℝ, IsFiniteMeasure τ ∧ τ (Ici 0)ᶜ = 0 ∧
      ∀ t, 0 < t → H (s + t) = ∫ r, Real.exp (-t * r) ∂τ := by
    intro s hs
    have hcm := completelyMonotoneOn_comp_add_left hH hs.le
    have hc : ContinuousAt H s := hH.2.continuousAt (Ioi_mem_nhds hs)
    have hlim : Tendsto (fun t => H (s + t)) (𝓝[>] (0 : ℝ)) (𝓝 (H s)) := by
      have h1 : Tendsto (fun t : ℝ => s + t) (𝓝[>] (0 : ℝ)) (𝓝 s) := by
        have := (tendsto_const_nhds (x := s)).add (tendsto_id (x := 𝓝 (0 : ℝ)))
        rw [add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      exact hc.tendsto.comp h1
    exact exists_finiteLaplaceMeasure_of_completelyMonotoneOn hcm hlim
  choose τ hτfin hτ hτH using hshift
  have hLτ : ∀ s (hs : 0 < s), ∀ v, 0 < v → rateLaplace (τ s hs) v = ENNReal.ofReal (H (s + v)) := by
    intro s hs v hv
    haveI := hτfin s hs
    have hfinv : rateLaplace (τ s hs) v ≠ ∞ := by
      refine ne_top_of_le_ne_top (measure_ne_top (τ s hs) univ) ?_
      rw [rateLaplace, ← lintegral_one]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_iff.2 (hτ s hs)] with r hr
      rw [ENNReal.ofReal_le_one, Real.exp_le_one_iff]
      have : 0 ≤ r := hr
      nlinarith
    rw [hτH s hs v hv, ← toReal_rateLaplace_eq_integral, ENNReal.ofReal_toReal hfinv]
  have hHnn : ∀ t, 0 < t → 0 ≤ H t := by
    intro t ht
    have h := hτH (t / 2) (half_pos ht) (t / 2) (half_pos ht)
    rw [show t / 2 + t / 2 = t by ring] at h
    rw [h]
    exact integral_nonneg fun r => (Real.exp_pos _).le
  -- all shifts produce the same tilted measure
  have hcons : ∀ s (hs : 0 < s), s < 1 → τ 1 one_pos = rateTilt (1 - s) (τ s hs) := by
    intro s hs hs1
    haveI := hτfin s hs
    haveI := hτfin 1 one_pos
    have hfin : rateLaplace (τ s hs) (1 - s) ≠ ∞ := by
      rw [hLτ s hs _ (by linarith)]; exact ENNReal.ofReal_ne_top
    haveI := isFiniteMeasure_rateTilt hfin
    refine measure_eq_of_laplace_eq (hτ 1 one_pos) (rateTilt_compl_Ici (hτ s hs)) fun u hu => ?_
    have h1 : s + (1 - s + u) = 1 + u := by ring
    rw [integral_exp_rateTilt, hLτ s hs _ (by linarith), h1, ← hτH 1 one_pos u hu,
      ENNReal.toReal_ofReal (hHnn _ (by linarith))]
  have hν : ∀ t (ht : 0 < t), rateTilt (-1) (τ 1 one_pos) =
      rateTilt (-(min (t / 2) (1 / 2))) (τ (min (t / 2) (1 / 2)) (by positivity)) := by
    intro t ht
    have hs : 0 < min (t / 2) (1 / 2) := by positivity
    have hs1 : min (t / 2) (1 / 2) < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    rw [hcons (min (t / 2) (1 / 2)) hs hs1, rateTilt_rateTilt]
    congr 1
    ring
  refine ⟨rateTilt (-1) (τ 1 one_pos), rateTilt_compl_Ici (hτ 1 one_pos), fun t ht => ?_,
    fun t ht => ?_⟩
  all_goals
    have hs : 0 < min (t / 2) (1 / 2) := by positivity
    have hst : min (t / 2) (1 / 2) < t := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    rw [hν t ht, rateLaplace_rateTilt, hLτ _ hs _ (by linarith),
      show min (t / 2) (1 / 2) + (-min (t / 2) (1 / 2) + t) = t by ring]
  · exact ENNReal.ofReal_ne_top
  · rw [ENNReal.toReal_ofReal (hHnn t ht)]

/-! ## Laplace transforms of dilations and deletions -/

theorem rateLaplace_rateDilate (n : ℕ) (ν : Measure ℝ) (t : ℝ) :
    rateLaplace (rateDilate n ν) t = (n : ℝ≥0∞) ^ 2 * rateLaplace ν ((n : ℝ) ^ 2 * t) := by
  rw [rateLaplace, rateDilate, lintegral_smul_measure, lintegral_map (measurable_rateExpKernel t)
    (measurable_rateScale n), smul_eq_mul, rateLaplace]
  congr 1
  exact lintegral_congr fun l => by simp only [rateScale]; ring_nf

/-- The Laplace transform of a finite deletion part is the finite word sum
`Σ_{T ⊆ S} (∏T)² L_ν((∏T)² t)` over words of the given parity. -/
theorem rateLaplace_rateDeletionPart (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (e : Bool)
    (ν : Measure ℝ) (t : ℝ) :
    rateLaplace (rateDeletionPart (· ∈ S) e ν) t =
      ∑ T ∈ S.powerset.filter (fun T => (Even T.card ↔ e = true)),
        ((∏ p ∈ T, p : ℕ) : ℝ≥0∞) ^ 2 * rateLaplace ν (((∏ p ∈ T, p : ℕ) : ℝ) ^ 2 * t) := by
  classical
  rw [rateLaplace, rateDeletionPart, lintegral_sum_measure]
  rw [tsum_eq_sum (s := S.powerset.filter (fun T => (Even T.card ↔ e = true))) fun T hT => ?_]
  · refine Finset.sum_congr rfl fun T hT => ?_
    have hw : IsRateWord (· ∈ S) e T := by
      rw [Finset.mem_filter, Finset.mem_powerset] at hT
      exact ⟨fun p hp => ⟨hS p (hT.1 hp), hT.1 hp⟩, hT.2⟩
    rw [if_pos hw, ← rateLaplace, rateLaplace_rateDilate]
  · have hw : ¬ IsRateWord (· ∈ S) e T := by
      rintro ⟨h1, h2⟩
      exact hT (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 fun p hp => (h1 p hp).2, h2⟩)
    rw [if_neg hw, lintegral_zero_measure]

/-! ## Fluxes of finite deletions -/

theorem ThetaFluxSource.finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, ThetaFluxSource (f i)) : ThetaFluxSource fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (thetaFluxSource_thetaCuspFullSource.const_mul 0)
  | insert a s ha ih =>
      have h := (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
      simpa only [Finset.sum_insert ha] using h

theorem thetaNormalizedFlux_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, ThetaFluxSource (f i)) (t : ℝ) :
    thetaNormalizedFlux (fun x => ∑ i ∈ s, f i x) t = ∑ i ∈ s, thetaNormalizedFlux (f i) t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (thetaNormalizedFlux_const_mul thetaCuspFullSource 0 t)
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [thetaNormalizedFlux_add (hf a (Finset.mem_insert_self a s))
        (ThetaFluxSource.finset_sum s fun i hi => hf i (Finset.mem_insert_of_mem hi)),
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- **Flux of a finite deletion.** `b_{D_S f}(t) = Σ_{T ⊆ S} (-1)^{|T|} (∏T)² b_f((∏T)² t)`. -/
theorem thetaNormalizedFlux_thetaPrimeDeletion_general {f : ℝ → ℝ} (hf : ThetaFluxSource f)
    (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p) {t : ℝ} (ht : 0 < t) :
    thetaNormalizedFlux (thetaPrimeDeletion S f) t = ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card *
      (((∏ p ∈ T, p : ℕ) : ℝ) ^ 2 * thetaNormalizedFlux f (((∏ p ∈ T, p : ℕ) : ℝ) ^ 2 * t)) := by
  have hpos : ∀ T ∈ S.powerset, (0 : ℝ) < ((∏ p ∈ T, p : ℕ) : ℝ) := fun T hT => by
    exact_mod_cast Finset.prod_pos fun p hp => hS p (Finset.mem_powerset.1 hT hp)
  have hsrc : ∀ T ∈ S.powerset, ThetaFluxSource fun x => (-1 : ℝ) ^ T.card *
      ((((∏ p ∈ T, p : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)) * f (x + Real.log ((∏ p ∈ T, p : ℕ) : ℝ))) :=
    fun T _ => ((hf.comp_add _).const_mul _).const_mul _
  change thetaNormalizedFlux (fun x => ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card *
    ((((∏ p ∈ T, p : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)) * f (x + Real.log ((∏ p ∈ T, p : ℕ) : ℝ)))) t = _
  rw [thetaNormalizedFlux_finset_sum _ hsrc]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hP := hpos T hT
  rw [thetaNormalizedFlux_const_mul, thetaNormalizedFlux_const_mul,
    thetaNormalizedFlux_comp_add f _ ht]
  generalize ((∏ p ∈ T, p : ℕ) : ℝ) = P at hP ⊢
  have h1 : Real.exp (2 * Real.log P) = P ^ 2 := by
    rw [mul_comm, Real.exp_mul, Real.exp_log hP, Real.rpow_two]
  have h2 : Real.exp (5 * Real.log P / 2) = P ^ (5 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos hP]; ring_nf
  rw [h1, h2, ← mul_assoc (P ^ _), ← Real.rpow_add hP]
  norm_num

/-! ## Complete monotonicity of deleted fluxes gives positive rate deletions -/

theorem rateDilate_compl_Ici {ν : Measure ℝ} (hν : ν (Ici 0)ᶜ = 0) (n : ℕ) :
    rateDilate n ν (Ici 0)ᶜ = 0 := by
  rw [rateDilate_apply _ _ measurableSet_Ici.compl]
  refine mul_eq_zero_of_right _ (measure_mono_null (fun l hl => ?_) hν)
  simp only [mem_preimage, mem_compl_iff, mem_Ici, not_le, rateScale] at hl ⊢
  exact lt_of_not_ge fun h => hl.not_ge (mul_nonneg (sq_nonneg _) h)

theorem rateDeletionPart_compl_Ici {ν : Measure ℝ} (hν : ν (Ici 0)ᶜ = 0) (P : ℕ → Prop) (e : Bool) :
    rateDeletionPart P e ν (Ici 0)ᶜ = 0 := by
  classical
  rw [rateDeletionPart, Measure.sum_apply _ measurableSet_Ici.compl]
  refine ENNReal.tsum_eq_zero.2 fun T => ?_
  split_ifs
  · exact rateDilate_compl_Ici hν _
  · rfl

theorem rateLaplace_rateDeletionPart_ne_top {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (e : Bool)
    {ν : Measure ℝ} (hfin : ∀ t, 0 < t → rateLaplace ν t ≠ ∞) {t : ℝ} (ht : 0 < t) :
    rateLaplace (rateDeletionPart (· ∈ S) e ν) t ≠ ∞ := by
  rw [rateLaplace_rateDeletionPart S hS]
  refine ENNReal.sum_ne_top.2 fun T hT =>
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)) (hfin _ ?_)
  have : (0 : ℝ) < ((∏ p ∈ T, p : ℕ) : ℝ) := by
    exact_mod_cast prod_pos_of_primes fun p hp =>
      hS p (Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1 hp)
  positivity

/-- The signed deleted flux is the difference of the Laplace transforms of the two deletion parts. -/
theorem thetaNormalizedFlux_thetaPrimeDeletion_eq_rateLaplace_sub {f : ℝ → ℝ}
    (hf : ThetaFluxSource f) {ν : Measure ℝ} (hfin : ∀ t, 0 < t → rateLaplace ν t ≠ ∞)
    (hrep : ∀ t, 0 < t → thetaNormalizedFlux f t = (rateLaplace ν t).toReal) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) {t : ℝ} (ht : 0 < t) :
    thetaNormalizedFlux (thetaPrimeDeletion S f) t =
      (rateLaplace (rateDeletionPart (· ∈ S) true ν) t).toReal -
        (rateLaplace (rateDeletionPart (· ∈ S) false ν) t).toReal := by
  classical
  have hpos : ∀ T ∈ S.powerset, (0 : ℝ) < ((∏ p ∈ T, p : ℕ) : ℝ) := fun T hT => by
    exact_mod_cast prod_pos_of_primes fun p hp => hS p (Finset.mem_powerset.1 hT hp)
  have hterm : ∀ T ∈ S.powerset, (((∏ p ∈ T, p : ℕ) : ℝ≥0∞) ^ 2 *
      rateLaplace ν (((∏ p ∈ T, p : ℕ) : ℝ) ^ 2 * t)).toReal =
      ((∏ p ∈ T, p : ℕ) : ℝ) ^ 2 *
        thetaNormalizedFlux f (((∏ p ∈ T, p : ℕ) : ℝ) ^ 2 * t) := fun T hT => by
    rw [ENNReal.toReal_mul, hrep _ (by have := hpos T hT; positivity)]
    simp
  have hne : ∀ T ∈ S.powerset, ((∏ p ∈ T, p : ℕ) : ℝ≥0∞) ^ 2 *
      rateLaplace ν (((∏ p ∈ T, p : ℕ) : ℝ) ^ 2 * t) ≠ ∞ := fun T hT =>
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
      (hfin _ (by have := hpos T hT; positivity))
  have hE : ∀ e : Bool, (rateLaplace (rateDeletionPart (· ∈ S) e ν) t).toReal =
      ∑ T ∈ S.powerset.filter (fun T => (Even T.card ↔ e = true)),
        ((∏ p ∈ T, p : ℕ) : ℝ) ^ 2 * thetaNormalizedFlux f (((∏ p ∈ T, p : ℕ) : ℝ) ^ 2 * t) := by
    intro e
    rw [rateLaplace_rateDeletionPart S hS,
      ENNReal.toReal_sum fun T hT => hne T (Finset.mem_filter.1 hT).1]
    exact Finset.sum_congr rfl fun T hT => hterm T (Finset.mem_filter.1 hT).1
  rw [hE, hE, thetaNormalizedFlux_thetaPrimeDeletion_general hf S (fun p hp => (hS p hp).pos) ht,
    ← Finset.sum_filter_add_sum_filter_not S.powerset (fun T => Even T.card)]
  simp only [Bool.false_eq_true, iff_false, iff_true]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1 <;> refine Finset.sum_congr rfl fun T hT => ?_
  · rw [(Finset.mem_filter.1 hT).2.neg_one_pow, one_mul]
  · rw [(Nat.not_even_iff_odd.1 (Finset.mem_filter.1 hT).2).neg_one_pow, neg_one_mul]

/-- **Complete monotonicity of a deleted flux gives a positive rate deletion.**  If `b_f` is the
Laplace transform of `ν` and `b_{D_S f}` is completely monotone, then `D_S ν ≥ 0`. -/
theorem rateDeletionPart_le_of_completelyMonotoneOn {f : ℝ → ℝ} (hf : ThetaFluxSource f)
    {ν : Measure ℝ} (hν : ν (Ici 0)ᶜ = 0) (hfin : ∀ t, 0 < t → rateLaplace ν t ≠ ∞)
    (hrep : ∀ t, 0 < t → thetaNormalizedFlux f t = (rateLaplace ν t).toReal) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hCM : CompletelyMonotoneOn (thetaNormalizedFlux (thetaPrimeDeletion S f))) :
    rateDeletionPart (· ∈ S) false ν ≤ rateDeletionPart (· ∈ S) true ν :=
  le_of_completelyMonotoneOn_rateLaplace_sub (rateDeletionPart_compl_Ici hν _ _)
    (rateDeletionPart_compl_Ici hν _ _) (rateLaplace_rateDeletionPart_ne_top hS _ hfin one_pos)
    (rateLaplace_rateDeletionPart_ne_top hS _ hfin one_pos)
    (hCM.congr_Ioi fun _ ht =>
      thetaNormalizedFlux_thetaPrimeDeletion_eq_rateLaplace_sub hf hfin hrep hS ht)

/-! ## The Bernstein measure of a flux has no atom at rate zero -/

theorem tendsto_thetaNormalizedFlux_atTop {f : ℝ → ℝ} (hf : ThetaFluxSource f) :
    Tendsto (thetaNormalizedFlux f) atTop (𝓝 0) := by
  set C : ℝ := ∫ x in Ioi (-1 : ℝ), |Real.exp (x / 2) * f x|
  have hbound : ∀ t, 1 ≤ t → |thetaNormalizedFlux f t| ≤ t ^ (-(3 / 2 : ℝ)) * C := by
    intro t ht
    have hsub : Ici (Real.log t / 2) ⊆ Ioi (-1 : ℝ) := fun x hx => by
      have := Real.log_nonneg ht
      simp only [mem_Ici, mem_Ioi] at hx ⊢
      linarith
    unfold thetaNormalizedFlux
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
    gcongr
    calc |∫ x in Ici (Real.log t / 2), Real.exp (x / 2) * f x|
        ≤ ∫ x in Ici (Real.log t / 2), |Real.exp (x / 2) * f x| := abs_integral_le_integral_abs
      _ ≤ C := setIntegral_mono_set (hf.2 (-1)).abs (ae_of_all _ fun x => abs_nonneg _)
          (Eventually.of_forall hsub)
  have hlim : Tendsto (fun t : ℝ => t ^ (-(3 / 2 : ℝ)) * C) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).mul_const C
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [Real.norm_eq_abs]
  exact hbound t ht

theorem measure_singleton_zero_le_rateLaplace (ν : Measure ℝ) (t : ℝ) :
    ν {0} ≤ rateLaplace ν t := by
  calc ν {0} = ∫⁻ l in {0}, ENNReal.ofReal (Real.exp (-(t * l))) ∂ν := by
        rw [lintegral_singleton]; simp
    _ ≤ rateLaplace ν t := setLIntegral_le_lintegral _ _

/-- **No residual at rate zero.**  The Bernstein measure of the flux of a flux source has no mass
on `(-∞, 0]`. -/
theorem rateMeasure_Iic_zero_of_flux {f : ℝ → ℝ} (hf : ThetaFluxSource f) {ν : Measure ℝ}
    (hν : ν (Ici 0)ᶜ = 0) (hfin : ∀ t, 0 < t → rateLaplace ν t ≠ ∞)
    (hrep : ∀ t, 0 < t → thetaNormalizedFlux f t = (rateLaplace ν t).toReal) : ν (Iic 0) = 0 := by
  have h0 : ν {0} = 0 := by
    have hlim : Tendsto (fun t => ENNReal.ofReal (thetaNormalizedFlux f t)) atTop (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto 0).comp (tendsto_thetaNormalizedFlux_atTop hf)
      rwa [ENNReal.ofReal_zero] at this
    refine le_antisymm (ge_of_tendsto hlim ?_) zero_le
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [hrep t ht, ENNReal.ofReal_toReal (hfin t ht)]
    exact measure_singleton_zero_le_rateLaplace ν t
  have hIic : Iic (0 : ℝ) = (Ici 0)ᶜ ∪ {0} := by
    ext l
    simp only [mem_Iic, mem_union, mem_compl_iff, mem_Ici, not_le, mem_singleton_iff]
    constructor
    · intro h; rcases h.lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h) <;> linarith [h.le]
  rw [hIic]
  exact measure_union_null hν h0

end

end RHTower
