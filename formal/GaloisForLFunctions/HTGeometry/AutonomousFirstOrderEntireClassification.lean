import GaloisForLFunctions.HTGeometry.AutonomousFirstOrderEntirePeriod
import Mathlib.Analysis.Complex.Periodic

/-!
# Briot–Bouquet for entire functions

A transcendental entire solution `f` of an autonomous first-order algebraic differential equation
`P(f, f') = 0`, `P ≠ 0`, is a Laurent polynomial in an exponential:

`f(z) = p(e^{az}) · e^{-m a z}`,  `a ≠ 0`,  `p ∈ ℂ[X]`,  `m ∈ ℕ`.

`f` has a period `ω` (`exists_period_of_autonomous_firstOrder`), so `f(ω z) = g(e^{2πiz})` for a
function `g` holomorphic on `ℂ \ {0}`.  The relation descends to `Q(g(t), D(t)) = 0` with
`D(t) = (2πi/ω) t g'(t)`.  If `g` had an essential singularity at `∞` (or at `0`), Casorati–Weierstrass
and the repeated-regular-value lemma would give two good points of different moduli with equal `g`
and equal `D`; lifting them, local uniqueness gives `f` a second period `ω (z₂ - z₁)` with
`Im(z₂ - z₁) ≠ 0`, and a doubly periodic entire function is constant.  So `g` has polynomial growth
at `∞` and at `0`, and `t^m g(t)` is an entire function of polynomial growth — a polynomial.
-/

open Filter Topology Metric Set Polynomial Complex Function.Periodic

namespace GaloisForLFunctions.HTGeometry

theorem isPreconnected_compl_zero : IsPreconnected ({0}ᶜ : Set ℂ) :=
  (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
    0).isPreconnected

theorem compl_zero_eq_norm_pos : ({0}ᶜ : Set ℂ) = {t : ℂ | 0 < ‖t‖} := by
  ext t; simp [norm_pos_iff]

theorem hasDerivAt_qParam_one (z : ℂ) :
    HasDerivAt (qParam 1) (2 * Real.pi * I * qParam 1 z) z := by
  have hq : qParam 1 = fun w => Complex.exp (2 * (Real.pi : ℂ) * I * w) := by
    funext w; simp [qParam]
  rw [hq]
  have h1 : HasDerivAt (fun w : ℂ => 2 * (Real.pi : ℂ) * I * w) (2 * (Real.pi : ℂ) * I) z := by
    simpa using (hasDerivAt_id z).const_mul (2 * (Real.pi : ℂ) * I)
  refine h1.cexp.congr_deriv ?_
  beta_reduce
  ring

theorem qParam_one_invQParam {t : ℂ} (ht : t ≠ 0) : qParam 1 (invQParam 1 t) = t :=
  qParam_right_inv one_ne_zero ht

variable {f : ℂ → ℂ}

/-- The data of the descent of a periodic solution to the punctured plane. -/
structure PeriodicDescent (f : ℂ → ℂ) (ω : ℂ) where
  ne_zero : ω ≠ 0
  periodic : ∀ z, f (z + ω) = f z

namespace PeriodicDescent

variable {ω : ℂ} (hd : PeriodicDescent f ω)
include hd

/-- The rescaled function of period `1`. -/
def unitPeriodic (f : ℂ → ℂ) (ω : ℂ) : ℂ → ℂ := fun z => f (ω * z)

theorem periodic_unitPeriodic : Function.Periodic (unitPeriodic f ω) ((1 : ℝ) : ℂ) := by
  intro z
  simp only [unitPeriodic, ofReal_one, mul_add, mul_one]
  exact hd.periodic _

/-- The descended function on the punctured plane. -/
noncomputable def cusp (f : ℂ → ℂ) (ω : ℂ) : ℂ → ℂ := cuspFunction 1 (unitPeriodic f ω)

theorem cusp_qParam (z : ℂ) : cusp f ω (qParam 1 z) = f (ω * z) :=
  eq_cuspFunction one_ne_zero hd.periodic_unitPeriodic z

theorem differentiableAt_cusp (hfd : Differentiable ℂ f) {t : ℂ} (ht : t ≠ 0) :
    DifferentiableAt ℂ (cusp f ω) t := by
  have h := differentiableAt_cuspFunction one_ne_zero hd.periodic_unitPeriodic
    (z := invQParam 1 t) ((hfd.comp (differentiable_id.const_mul ω)) _)
  rwa [qParam_one_invQParam ht] at h

/-- The derivative observable on the punctured plane. -/
noncomputable def cuspObs (f : ℂ → ℂ) (ω : ℂ) (t : ℂ) : ℂ :=
  (2 * Real.pi * I / ω) * t * deriv (cusp f ω) t

theorem cuspObs_qParam (hfd : Differentiable ℂ f) (z : ℂ) :
    cuspObs f ω (qParam 1 z) = deriv f (ω * z) := by
  have ht : qParam 1 z ≠ 0 := qParam_ne_zero z
  have hg : HasDerivAt (cusp f ω) (deriv (cusp f ω) (qParam 1 z)) (qParam 1 z) :=
    (hd.differentiableAt_cusp hfd ht).hasDerivAt
  have hcomp := hg.comp z (hasDerivAt_qParam_one z)
  have hF : HasDerivAt (fun z => f (ω * z)) (deriv f (ω * z) * ω) z := by
    have h1 : HasDerivAt (fun z => ω * z) ω z := by simpa using (hasDerivAt_id z).const_mul ω
    exact (hfd (ω * z)).hasDerivAt.comp z h1
  have heq : (cusp f ω ∘ qParam 1) = fun z => f (ω * z) := funext hd.cusp_qParam
  rw [heq] at hcomp
  have h := hcomp.unique hF
  have hω := hd.ne_zero
  have hpi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  simp only [cuspObs]
  field_simp
  linear_combination h

theorem relEval_cusp (hfd : Differentiable ℂ f) {Q : Polynomial (Polynomial ℂ)}
    (hrel : ∀ z, relEval Q (f z) (deriv f z) = 0) {t : ℂ} (ht : t ≠ 0) :
    relEval Q (cusp f ω t) (cuspObs f ω t) = 0 := by
  rw [← qParam_one_invQParam ht, hd.cusp_qParam, hd.cuspObs_qParam hfd]
  exact hrel _

/-- **Equal good jets of different moduli are impossible**: they would give `f` a second period
`ω (z₂ - z₁)` with `Im (z₂ - z₁) ≠ 0`. -/
theorem false_of_equal_cusp_jets (hf : TranscendentalEntire f) {Q : Polynomial (Polynomial ℂ)}
    (hrel : ∀ z, relEval Q (f z) (deriv f z) = 0) {s₁ s₂ : ℂ} (hs₁ : s₁ ≠ 0) (hs₂ : s₂ ≠ 0)
    (hnorm : ‖s₁‖ ≠ ‖s₂‖) (hval : cusp f ω s₁ = cusp f ω s₂)
    (hobs : cuspObs f ω s₁ = cuspObs f ω s₂)
    (hQ : relEval (derivative Q) (cusp f ω s₁) (cuspObs f ω s₁) ≠ 0) : False := by
  set z₁ := invQParam 1 s₁
  set z₂ := invQParam 1 s₂
  have e₁ : qParam 1 z₁ = s₁ := qParam_one_invQParam hs₁
  have e₂ : qParam 1 z₂ = s₂ := qParam_one_invQParam hs₂
  have hv : f (ω * z₁) = f (ω * z₂) := by
    rw [← hd.cusp_qParam, ← hd.cusp_qParam, e₁, e₂, hval]
  have hder : deriv f (ω * z₁) = deriv f (ω * z₂) := by
    rw [← hd.cuspObs_qParam hf.1, ← hd.cuspObs_qParam hf.1, e₁, e₂, hobs]
  have hQ' : relEval (derivative Q) (f (ω * z₁)) (deriv f (ω * z₁)) ≠ 0 := by
    rw [← hd.cusp_qParam, ← hd.cuspObs_qParam hf.1, e₁]; exact hQ
  have hper2 := periodic_of_equal_jets hf.1 hrel hv hder hQ'
  have hratio : (ω * z₂ - ω * z₁) / ω = z₂ - z₁ := by
    field_simp [hd.ne_zero]
  have hne : (z₂ - z₁).im ≠ 0 := by
    intro h
    apply hnorm
    have him : z₂.im = z₁.im := by simp only [sub_im] at h; linarith
    rw [← e₁, ← e₂, norm_qParam, norm_qParam, him]
  have hconst := eq_const_of_two_periods hf.1 hd.ne_zero (ω₂ := ω * z₂ - ω * z₁)
    (by rw [hratio]; exact hne) hd.periodic hper2
  obtain ⟨w₁, w₂, hw⟩ := hf.exists_ne
  exact hw (hconst w₁ w₂)

theorem differentiableOn_cusp (hfd : Differentiable ℂ f) :
    DifferentiableOn ℂ (cusp f ω) {t : ℂ | 0 < ‖t‖} := fun _ ht =>
  (hd.differentiableAt_cusp hfd (norm_pos_iff.mp ht)).differentiableWithinAt

theorem analyticAt_cusp (hfd : Differentiable ℂ f) {t : ℂ} (ht : t ≠ 0) :
    AnalyticAt ℂ (cusp f ω) t := by
  have hopen : IsOpen ({0}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hdiff : DifferentiableOn ℂ (cusp f ω) {0}ᶜ := fun s hs =>
    (hd.differentiableAt_cusp hfd hs).differentiableWithinAt
  exact hdiff.analyticAt (hopen.mem_nhds ht)

/-- The badness function of the descended data: `D · ∂_Y Q (g, D)`. -/
noncomputable def cuspBad (f : ℂ → ℂ) (ω : ℂ) (Q : Polynomial (Polynomial ℂ)) (t : ℂ) : ℂ :=
  cuspObs f ω t * relEval (derivative Q) (cusp f ω t) (cuspObs f ω t)

theorem analyticAt_cuspBad (hfd : Differentiable ℂ f) (Q : Polynomial (Polynomial ℂ)) {t : ℂ}
    (ht : t ≠ 0) : AnalyticAt ℂ (cuspBad f ω Q) t := by
  have hg := hd.analyticAt_cusp hfd ht
  have hobs : AnalyticAt ℂ (cuspObs f ω) t :=
    (analyticAt_const.mul analyticAt_id).mul hg.deriv
  exact hobs.mul (analyticAt_relEval _ hg hobs)

theorem cuspBad_qParam (hfd : Differentiable ℂ f) (Q : Polynomial (Polynomial ℂ)) (z : ℂ) :
    cuspBad f ω Q (qParam 1 z) =
      deriv f (ω * z) * relEval (derivative Q) (f (ω * z)) (deriv f (ω * z)) := by
  rw [cuspBad, hd.cuspObs_qParam hfd, hd.cusp_qParam]

omit hd in
theorem relGood_cusp_of_cuspBad_ne_zero {Q : Polynomial (Polynomial ℂ)} {t : ℂ}
    (h : cuspBad f ω Q t ≠ 0) : RelGood (cusp f ω) (cuspObs f ω) Q t := by
  refine ⟨fun h0 => ?_, right_ne_zero_of_mul h⟩
  apply left_ne_zero_of_mul h
  simp [cuspObs, h0]

/-- The badness function does not vanish identically on the punctured plane. -/
theorem not_eqOn_cuspBad_zero (hf : TranscendentalEntire f) {Q : Polynomial (Polynomial ℂ)}
    (hQ : ∃ z, relEval (derivative Q) (f z) (deriv f z) ≠ 0) :
    ¬ EqOn (cuspBad f ω Q) 0 {0}ᶜ := by
  intro h0
  obtain ⟨z, hz⟩ := exists_badness_ne_zero hf hQ
  have := h0 (show qParam 1 (z / ω) ∈ ({0}ᶜ : Set ℂ) from qParam_ne_zero _)
  rw [hd.cuspBad_qParam hf.1, mul_div_cancel₀ _ hd.ne_zero] at this
  exact hz this

theorem eventually_relGood_cusp (hf : TranscendentalEntire f) {Q : Polynomial (Polynomial ℂ)}
    (hQ : ∃ z, relEval (derivative Q) (f z) (deriv f z) ≠ 0) {t₀ : ℂ} (ht₀ : t₀ ≠ 0) :
    ∀ᶠ t in 𝓝[≠] t₀, RelGood (cusp f ω) (cuspObs f ω) Q t := by
  have hana : AnalyticOnNhd ℂ (cuspBad f ω Q) {0}ᶜ := fun t ht => hd.analyticAt_cuspBad hf.1 Q ht
  rcases (hana t₀ ht₀).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · exact absurd (hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_compl_zero
      ht₀ h0) (hd.not_eqOn_cuspBad_zero hf hQ)
  · filter_upwards [hne] with t ht using relGood_cusp_of_cuspBad_ne_zero ht

/-- The descended function reflected through the unit circle. -/
noncomputable def cuspInv (f : ℂ → ℂ) (ω : ℂ) (t : ℂ) : ℂ := cusp f ω t⁻¹

theorem eventually_relGood_cuspInv (hf : TranscendentalEntire f) {Q : Polynomial (Polynomial ℂ)}
    (hQ : ∃ z, relEval (derivative Q) (f z) (deriv f z) ≠ 0) {t₀ : ℂ} (ht₀ : t₀ ≠ 0) :
    ∀ᶠ t in 𝓝[≠] t₀, RelGood (cuspInv f ω) (fun t => cuspObs f ω t⁻¹) Q t := by
  have hana : AnalyticOnNhd ℂ (fun t => cuspBad f ω Q t⁻¹) {0}ᶜ := fun t ht =>
    (hd.analyticAt_cuspBad hf.1 Q (inv_ne_zero ht)).comp (analyticAt_inv ht)
  rcases (hana t₀ ht₀).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · exfalso
    have hall := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_compl_zero
      ht₀ h0
    exact hd.not_eqOn_cuspBad_zero hf hQ fun s hs => by
      have := hall (show s⁻¹ ∈ ({0}ᶜ : Set ℂ) from inv_ne_zero hs)
      simpa using this
  · filter_upwards [hne, (isOpen_compl_singleton (x := (0 : ℂ))).mem_nhds ht₀ |>
      mem_nhdsWithin_of_mem_nhds] with t ht htne
    have hgood := relGood_cusp_of_cuspBad_ne_zero ht
    refine ⟨fun h0 => hgood.1 ?_, hgood.2⟩
    have htne' : t ≠ 0 := htne
    have hd1 : HasDerivAt (cuspInv f ω) (deriv (cusp f ω) t⁻¹ * (-(t ^ 2)⁻¹)) t :=
      (hd.differentiableAt_cusp hf.1 (inv_ne_zero htne')).hasDerivAt.comp t (hasDerivAt_inv htne')
    rw [hd1.deriv] at h0
    have ht2 : (-(t ^ 2)⁻¹ : ℂ) ≠ 0 := by simp [htne']
    exact (mul_eq_zero.mp h0).resolve_right ht2

theorem differentiableOn_cuspInv (hfd : Differentiable ℂ f) :
    DifferentiableOn ℂ (cuspInv f ω) {t : ℂ | 0 < ‖t‖} := fun t ht => by
  have ht0 : t ≠ 0 := norm_pos_iff.mp ht
  exact ((hd.differentiableAt_cusp hfd (inv_ne_zero ht0)).comp t
    (differentiableAt_inv ht0)).differentiableWithinAt

/-- **No essential singularity at infinity.** -/
theorem polyBound_cusp (hf : TranscendentalEntire f) {Q : Polynomial (Polynomial ℂ)}
    (hQ0 : Q ≠ 0) (hrel : ∀ z, relEval Q (f z) (deriv f z) = 0)
    (hQ : ∃ z, relEval (derivative Q) (f z) (deriv f z) ≠ 0) :
    ∃ (C : ℝ) (n : ℕ) (R : ℝ), ∀ t : ℂ, R < ‖t‖ → ‖cusp f ω t‖ ≤ C * ‖t‖ ^ n := by
  rcases polyBound_or_dense_image (hd.differentiableOn_cusp hf.1) with hb | hdense
  · exact hb
  exfalso
  obtain ⟨t₁, t₂, -, hsep, ht₁, hval, hobs, hgood⟩ :=
    exists_repeated_relGood_value (R₀ := 0) (hd.differentiableOn_cusp hf.1) hQ0
      (fun t ht => hd.relEval_cusp hf.1 hrel (norm_pos_iff.mp ht))
      (fun t ht => hd.eventually_relGood_cusp hf hQ (norm_pos_iff.mp ht)) hdense 0
  have ht₂ : 0 < ‖t₂‖ := by linarith
  exact hd.false_of_equal_cusp_jets hf hrel (norm_pos_iff.mp ht₁) (norm_pos_iff.mp ht₂)
    (by linarith) hval hobs hgood.2

/-- **No essential singularity at the origin.** -/
theorem polyBound_cuspInv (hf : TranscendentalEntire f) {Q : Polynomial (Polynomial ℂ)}
    (hQ0 : Q ≠ 0) (hrel : ∀ z, relEval Q (f z) (deriv f z) = 0)
    (hQ : ∃ z, relEval (derivative Q) (f z) (deriv f z) ≠ 0) :
    ∃ (C : ℝ) (n : ℕ) (R : ℝ), ∀ t : ℂ, R < ‖t‖ → ‖cusp f ω t⁻¹‖ ≤ C * ‖t‖ ^ n := by
  rcases polyBound_or_dense_image (hd.differentiableOn_cuspInv hf.1) with hb | hdense
  · exact hb
  exfalso
  obtain ⟨t₁, t₂, -, hsep, ht₁, hval, hobs, hgood⟩ :=
    exists_repeated_relGood_value (R₀ := 0) (D := fun t => cuspObs f ω t⁻¹)
      (hd.differentiableOn_cuspInv hf.1) hQ0
      (fun t ht => hd.relEval_cusp hf.1 hrel (inv_ne_zero (norm_pos_iff.mp ht)))
      (fun t ht => hd.eventually_relGood_cuspInv hf hQ (norm_pos_iff.mp ht)) hdense 0
  have ht₂ : 0 < ‖t₂‖ := by linarith
  have ht₁0 := norm_pos_iff.mp ht₁
  have ht₂0 := norm_pos_iff.mp ht₂
  refine hd.false_of_equal_cusp_jets hf hrel (inv_ne_zero ht₁0) (inv_ne_zero ht₂0) ?_ hval hobs
    hgood.2
  rw [norm_inv, norm_inv]
  intro h
  have := inv_injective h
  linarith

end PeriodicDescent

/-! ## Polynomial growth at both ends gives a Laurent polynomial -/

/-- A function holomorphic on the punctured plane with polynomial growth at `∞` and at `0` is a
Laurent polynomial. -/
theorem exists_laurent_of_polyBounds {g : ℂ → ℂ} (hg : ∀ t, t ≠ 0 → DifferentiableAt ℂ g t)
    (hinf : ∃ (C : ℝ) (n : ℕ) (R : ℝ), ∀ t : ℂ, R < ‖t‖ → ‖g t‖ ≤ C * ‖t‖ ^ n)
    (h0 : ∃ (C : ℝ) (m : ℕ) (R : ℝ), ∀ t : ℂ, R < ‖t‖ → ‖g t⁻¹‖ ≤ C * ‖t‖ ^ m) :
    ∃ (p : Polynomial ℂ) (m : ℕ), ∀ t, t ≠ 0 → g t = p.eval t / t ^ m := by
  obtain ⟨C, n, R, hR⟩ := hinf
  obtain ⟨C', m, R', hR'⟩ := h0
  set K : ℂ → ℂ := fun t => t ^ m * g t with hK
  set R₁ := max R' 1 with hR₁
  have hR₁pos : 0 < R₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  set ρ := 1 / R₁ with hρ
  have hρpos : 0 < ρ := by positivity
  have hKd : ∀ t, t ≠ 0 → DifferentiableAt ℂ K t := fun t ht =>
    (differentiableAt_id.pow m).mul (hg t ht)
  have hsmall : ∀ t : ℂ, t ∈ ball (0 : ℂ) ρ \ {0} → ‖K t‖ ≤ C' := by
    intro t ht
    have ht0 : t ≠ 0 := ht.2
    have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    have htρ : ‖t‖ < ρ := by simpa using ht.1
    have hinv : R' < ‖t⁻¹‖ := by
      rw [norm_inv]
      have : R₁ < ‖t‖⁻¹ := by
        rw [hρ] at htρ
        rw [lt_inv_comm₀ hR₁pos htpos]; simpa using htρ
      exact lt_of_le_of_lt (le_max_left _ _) this
    have hb := hR' t⁻¹ hinv
    rw [inv_inv, norm_inv, inv_pow] at hb
    rw [hK, norm_mul, norm_pow]
    have htm : 0 < ‖t‖ ^ m := pow_pos htpos m
    calc ‖t‖ ^ m * ‖g t‖ ≤ ‖t‖ ^ m * (C' * (‖t‖ ^ m)⁻¹) := mul_le_mul_of_nonneg_left hb htm.le
      _ = C' := by field_simp
  set K₀ := Function.update K 0 ((𝓝[≠] (0 : ℂ)).limUnder K) with hK₀
  have hK₀ball : DifferentiableOn ℂ K₀ (ball (0 : ℂ) ρ) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds 0 hρpos)
      (fun t ht => (hKd t ht.2).differentiableWithinAt)
      ⟨C', by rintro _ ⟨t, ht, rfl⟩; exact hsmall t ht⟩
  have hK₀eq : ∀ t, t ≠ 0 → K₀ t = K t := fun t ht => by rw [hK₀, Function.update_of_ne ht]
  have hK₀d : Differentiable ℂ K₀ := by
    intro t
    by_cases ht : t = 0
    · subst ht
      exact hK₀ball.differentiableAt (ball_mem_nhds 0 hρpos)
    · have hev : K₀ =ᶠ[𝓝 t] K := by
        filter_upwards [isOpen_compl_singleton.mem_nhds ht] with s hs using hK₀eq s hs
      exact (hKd t ht).congr_of_eventuallyEq hev
  -- polynomial growth of `K₀`
  set R₂ := max R 1 with hR₂
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R₂).exists_bound_of_continuousOn
    hK₀d.continuous.continuousOn
  obtain ⟨p, hp⟩ := Bottcher.exists_polynomial_of_entire_polyGrowth (C := max C 0 + max B 0)
    (n := n + m) hK₀d fun t => by
      have hmax1 : 1 ≤ max 1 ‖t‖ := le_max_left _ _
      have hpow1 : 1 ≤ (max 1 ‖t‖) ^ (n + m) := one_le_pow₀ hmax1
      have hC0 : 0 ≤ max C 0 := le_max_right _ _
      have hB0 : 0 ≤ max B 0 := le_max_right _ _
      by_cases ht : ‖t‖ ≤ R₂
      · have h1 := hB t (by rw [mem_closedBall, dist_zero_right]; exact ht)
        calc ‖K₀ t‖ ≤ max B 0 := h1.trans (le_max_left _ _)
          _ ≤ (max C 0 + max B 0) * 1 := by linarith
          _ ≤ (max C 0 + max B 0) * (max 1 ‖t‖) ^ (n + m) :=
            mul_le_mul_of_nonneg_left hpow1 (by linarith)
      · push Not at ht
        have ht1 : 1 < ‖t‖ := lt_of_le_of_lt (le_max_right _ _) ht
        have htR : R < ‖t‖ := lt_of_le_of_lt (le_max_left _ _) ht
        have ht0 : t ≠ 0 := norm_pos_iff.mp (by linarith)
        rw [hK₀eq t ht0, max_eq_right ht1.le, hK, norm_mul, norm_pow]
        have hzn : 0 ≤ ‖t‖ ^ m := by positivity
        have h1 := hR t htR
        calc ‖t‖ ^ m * ‖g t‖ ≤ ‖t‖ ^ m * (C * ‖t‖ ^ n) := mul_le_mul_of_nonneg_left h1 hzn
          _ ≤ ‖t‖ ^ m * (max C 0 * ‖t‖ ^ n) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_left _ _)
              (by positivity)) hzn
          _ = max C 0 * ‖t‖ ^ (n + m) := by ring
          _ ≤ (max C 0 + max B 0) * ‖t‖ ^ (n + m) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  refine ⟨p, m, fun t ht => ?_⟩
  have h1 := hp t
  rw [hK₀eq t ht, hK] at h1
  have htm : t ^ m ≠ 0 := pow_ne_zero m ht
  field_simp
  linear_combination h1

/-! ## The classification -/

/-- **Briot–Bouquet for entire functions.**  A transcendental entire solution of a nonzero
autonomous first-order algebraic differential equation is a Laurent polynomial in an exponential:
`f(z) = p(e^{az}) / e^{maz}` with `a ≠ 0`. -/
theorem exists_laurentExp_of_autonomous_firstOrder {f : ℂ → ℂ} (hf : TranscendentalEntire f)
    {P : Polynomial (Polynomial ℂ)} (hP : P ≠ 0) (hrel : ∀ z, relEval P (f z) (deriv f z) = 0) :
    ∃ (a : ℂ) (p : Polynomial ℂ) (m : ℕ), a ≠ 0 ∧
      ∀ z, f z = p.eval (Complex.exp (a * z)) / Complex.exp (a * z) ^ m := by
  obtain ⟨ω, hω, hper⟩ := exists_period_of_autonomous_firstOrder hf hP hrel
  have hd : PeriodicDescent f ω := ⟨hω, hper⟩
  obtain ⟨Q, hQ0, hQrel, hQ⟩ := exists_entire_relation_derivative_ne_zero hf hP hrel
  obtain ⟨p, m, hpm⟩ := exists_laurent_of_polyBounds
    (fun t ht => hd.differentiableAt_cusp hf.1 ht) (hd.polyBound_cusp hf hQ0 hQrel hQ)
    (hd.polyBound_cuspInv hf hQ0 hQrel hQ)
  have hpi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  refine ⟨2 * Real.pi * I / ω, p, m, div_ne_zero hpi hω, fun z => ?_⟩
  have hq : qParam 1 (z / ω) = Complex.exp (2 * Real.pi * I / ω * z) := by
    simp only [qParam, ofReal_one, div_one]
    congr 1
    field_simp
  have h1 := hd.cusp_qParam (z / ω)
  rw [mul_div_cancel₀ _ hω] at h1
  rw [← h1, hpm _ (qParam_ne_zero _), hq]

end GaloisForLFunctions.HTGeometry
