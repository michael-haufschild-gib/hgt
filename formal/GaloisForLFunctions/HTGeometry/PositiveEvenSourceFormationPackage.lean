import GaloisForLFunctions.HTGeometry.PositiveEvenSchwartzZeroDensity
import GaloisForLFunctions.HTGeometry.ReflectedExponentialFisher
import GaloisForLFunctions.HTGeometry.CommonMarkovRecoveryNeutrality
import GaloisForLFunctions.HTGeometry.ModularFormationDoubleMeasures

/-!
# The formation package of a positive even Schwartz source

A strictly positive even Schwartz source `F` with entire bilateral Laplace transform, normalized to
the probability law `P₀ = F / ∫F`, generates the exponential family
`dP_t = e^{tx - A(t)} dP₀` with `A(t) = log ∫ e^{tx} dP₀`.  For every parameter-independent Markov
recovery kernel `K`:

* `A` is even and the reflection `x ↦ -x` exchanges the tilts, `R_* P_t = P_{-t}`;
* the split packets `P_t ⊗ K` have exactly the relative entropies of the `P_t`;
* `A'' > 0`, and the reflected Jeffreys work is `J(t) = 4 t A'(t) > 0` for `t ≠ 0`;
* the recovery retains `J(t)`.

Since the positive even sources vanishing at a prescribed off-axis point exist (explicitly, and
densely), these six properties cannot force the zeros of the bilateral Laplace transform onto the
reflection-fixed axis `Re z = 0`.
-/

open MeasureTheory ProbabilityTheory InformationTheory Filter Complex
open scoped SchwartzMap ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

namespace ReflectedExponentialFamily

variable {X : Type*} [MeasurableSpace X] (F : ReflectedExponentialFamily X)

/-- `(EA.26)`  The reflection exchanges the tilts: `R_* P_t = P_{-t}`. -/
theorem map_reflection_tilt (t : ℝ) : (F.tilt t).map F.reflection = F.tilt (-t) := by
  rw [F.tilt_eq_withDensity, F.tilt_eq_withDensity,
    map_withDensity_of_involution F.measurable_reflection F.reflection_involutive F.map_base
      (F.measurable_tiltDensity t), F.mgf_neg]
  congr 1
  funext x
  rw [F.stat_odd, show t * -F.stat x = -t * F.stat x by ring]

end ReflectedExponentialFamily

/-- The six-property formation package of a reflected exponential family on `ℝ` with a common
Markov recovery kernel `K`: even cumulant, reflection exchanging the tilts, recovery-neutral
relative entropy, strict convexity of the cumulant, the Jeffreys work law `J(t) = 4tA'(t)`, strict
reflected properness, and retention of the reflected work under recovery. -/
def FormationPackage (P : ReflectedExponentialFamily ℝ) {H : Type*} [MeasurableSpace H]
    (K : Kernel ℝ H) : Prop :=
  (∀ t, P.cumulant (-t) = P.cumulant t) ∧
    (∀ t, (P.tilt t).map P.reflection = P.tilt (-t)) ∧
    (∀ t s, klDiv (splitPacketLaw (P.tilt t) K) (splitPacketLaw (P.tilt s) K) =
      klDiv (P.tilt t) (P.tilt s)) ∧
    (∀ t, 0 < iteratedDeriv 2 P.cumulant t) ∧
    (∀ t, formationJeffreys (P.tilt t) (P.tilt (-t)) =
      ENNReal.ofReal (4 * t * deriv P.cumulant t)) ∧
    (∀ t, t ≠ 0 → 0 < formationJeffreys (P.tilt t) (P.tilt (-t))) ∧
    (∀ t, formationJeffreys (splitPacketLaw (P.tilt t) K) (splitPacketLaw (P.tilt (-t)) K) =
      formationJeffreys (P.tilt t) (P.tilt (-t)))

namespace PositiveEvenLaplaceEscape

/-- A probability law without atoms gives positive mass to any integrand positive off one point. -/
theorem integral_pos_of_pos_off_point {P : Measure ℝ} [IsProbabilityMeasure P] {c : ℝ}
    (hP : P {c} = 0) {g : ℝ → ℝ} (hg : Integrable g P) (hnn : ∀ x, 0 ≤ g x)
    (hpos : ∀ x, x ≠ c → 0 < g x) : 0 < ∫ x, g x ∂P := by
  rw [integral_pos_iff_support_of_nonneg (fun x => hnn x) hg]
  have hsub : ({c}ᶜ : Set ℝ) ⊆ Function.support g := fun x hx => (hpos x hx).ne'
  have hc : P ({c}ᶜ) = 1 := by
    rw [prob_compl_eq_one_sub (measurableSet_singleton c), hP, tsub_zero]
  calc (0 : ℝ≥0∞) < 1 := zero_lt_one
    _ = P {c}ᶜ := hc.symm
    _ ≤ P (Function.support g) := measure_mono hsub

theorem mul_sinh_pos {x : ℝ} (hx : x ≠ 0) : 0 < x * Real.sinh x := by
  rcases lt_or_gt_of_ne hx with h | h
  · exact mul_pos_of_neg_of_neg h (Real.sinh_neg_iff.mpr h)
  · exact mul_pos h (Real.sinh_pos_iff.mpr h)

theorem mul_sinh_nonneg (x : ℝ) : 0 ≤ x * Real.sinh x := by
  rcases eq_or_ne x 0 with h | h
  · simp [h]
  · exact (mul_sinh_pos h).le

theorem integral_pos_of_pos {F : 𝓢(ℝ, ℝ)} (hpos : ∀ x, 0 < F x) : 0 < ∫ x, F x := by
  rw [integral_pos_iff_support_of_nonneg (fun x => (hpos x).le) F.integrable,
    show Function.support F = Set.univ from Set.eq_univ_of_forall fun x => (hpos x).ne']
  simp

/-- `(EA.25)`  The normalized source law `P₀ = F / ∫F`. -/
def sourceLaw (F : 𝓢(ℝ, ℝ)) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (F x / ∫ y, F y))

theorem measurable_sourceDensity (F : 𝓢(ℝ, ℝ)) :
    Measurable (fun x => ENNReal.ofReal (F x / ∫ y, F y)) :=
  ENNReal.measurable_ofReal.comp (F.continuous.measurable.div_const _)

theorem isProbabilityMeasure_sourceLaw {F : 𝓢(ℝ, ℝ)} (hpos : ∀ x, 0 < F x) :
    IsProbabilityMeasure (sourceLaw F) := by
  constructor
  have hM := integral_pos_of_pos hpos
  rw [sourceLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (F.integrable.div_const _)
      (Eventually.of_forall fun x => div_nonneg (hpos x).le hM.le),
    integral_div, div_self hM.ne', ENNReal.ofReal_one]

theorem map_neg_sourceLaw {F : 𝓢(ℝ, ℝ)} (heven : ∀ x, F (-x) = F x) :
    (sourceLaw F).map (fun x => -x) = sourceLaw F := by
  rw [sourceLaw, map_withDensity_of_involution measurable_neg (fun x => neg_neg x)
    (Measure.measurePreserving_neg (volume : Measure ℝ)).map_eq (measurable_sourceDensity F)]
  congr 1
  funext x
  rw [heven]

theorem sourceLaw_singleton (F : 𝓢(ℝ, ℝ)) (c : ℝ) : sourceLaw F {c} = 0 :=
  withDensity_absolutelyContinuous _ _ Real.volume_singleton

/-- The reflected exponential family of a positive even source, with the identity statistic and
the sign reflection. -/
def sourceFamily (F : 𝓢(ℝ, ℝ)) (hpos : ∀ x, 0 < F x) (heven : ∀ x, F (-x) = F x) :
    ReflectedExponentialFamily ℝ where
  base := sourceLaw F
  isProb := isProbabilityMeasure_sourceLaw hpos
  reflection := fun x => -x
  measurable_reflection := measurable_neg
  reflection_involutive := neg_neg
  map_base := map_neg_sourceLaw heven
  stat := id
  measurable_stat := measurable_id
  stat_odd := fun _ => rfl

/-- Every exponential moment of the normalized source law is finite. -/
theorem integrable_exp_mul_sourceLaw {F : 𝓢(ℝ, ℝ)} (hpos : ∀ x, 0 < F x)
    (hent : HasEntireLaplace F) (t : ℝ) :
    Integrable (fun x => Real.exp (t * x)) (sourceLaw F) := by
  have hM := integral_pos_of_pos hpos
  rw [sourceLaw, integrable_withDensity_iff (measurable_sourceDensity F)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine ((hent (t : ℂ)).norm.div_const (∫ y, F y)).congr (Eventually.of_forall fun x => ?_)
  change ‖cexp ((t : ℂ) * x) * (F x : ℂ)‖ / (∫ y, F y) =
    Real.exp (t * x) * (ENNReal.ofReal (F x / ∫ y, F y)).toReal
  rw [ENNReal.toReal_ofReal (div_nonneg (hpos x).le hM.le), norm_mul, ← Complex.ofReal_mul,
    Complex.norm_exp_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos x)]
  ring

theorem mem_interior_integrableExpSet {F : 𝓢(ℝ, ℝ)} (hpos : ∀ x, 0 < F x)
    (heven : ∀ x, F (-x) = F x) (hent : HasEntireLaplace F) (t : ℝ) :
    t ∈ interior (integrableExpSet (sourceFamily F hpos heven).stat
      (sourceFamily F hpos heven).base) := by
  have h : integrableExpSet (sourceFamily F hpos heven).stat (sourceFamily F hpos heven).base =
      Set.univ :=
    Set.eq_univ_of_forall fun s => integrable_exp_mul_sourceLaw hpos hent s
  rw [h, interior_univ]
  trivial

/-- `(EA.28)`  `A''(t) = Var_{P_t}(X) > 0`: the cumulant is strictly convex. -/
theorem iteratedDeriv_two_cumulant_pos {F : 𝓢(ℝ, ℝ)} (hpos : ∀ x, 0 < F x)
    (heven : ∀ x, F (-x) = F x) (hent : HasEntireLaplace F) (t : ℝ) :
    0 < iteratedDeriv 2 (sourceFamily F hpos heven).cumulant t := by
  set P := sourceFamily F hpos heven with hP
  have ht := mem_interior_integrableExpSet hpos heven hent t
  haveI : IsProbabilityMeasure P.base := P.isProb
  haveI : IsProbabilityMeasure (sourceLaw F) := isProbabilityMeasure_sourceLaw hpos
  change 0 < iteratedDeriv 2 (cgf P.stat P.base) t
  rw [iteratedDeriv_two_cgf_eq_integral ht]
  set c := deriv (cgf P.stat P.base) t
  refine div_pos ?_ (mgf_pos (interior_subset (s := integrableExpSet P.stat P.base) ht))
  have h0 := integrable_pow_mul_exp_of_mem_interior_integrableExpSet ht 0
  have h1 := integrable_pow_mul_exp_of_mem_interior_integrableExpSet ht 1
  have h2 := integrable_pow_mul_exp_of_mem_interior_integrableExpSet ht 2
  have hint : Integrable (fun ω => (P.stat ω - c) ^ 2 * Real.exp (t * P.stat ω)) P.base := by
    refine ((h2.sub (h1.const_mul (2 * c))).add (h0.const_mul (c ^ 2))).congr
      (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  refine integral_pos_of_pos_off_point (c := c) (sourceLaw_singleton F c) hint
    (fun ω => by positivity) fun ω hω => ?_
  have hne : P.stat ω - c ≠ 0 := sub_ne_zero.mpr hω
  positivity

/-- `(EA.29)`  Strict reflected properness: `4 t A'(t) > 0` for `t ≠ 0`. -/
theorem four_mul_deriv_cumulant_pos {F : 𝓢(ℝ, ℝ)} (hpos : ∀ x, 0 < F x)
    (heven : ∀ x, F (-x) = F x) (hent : HasEntireLaplace F) {t : ℝ} (ht0 : t ≠ 0) :
    0 < 4 * t * deriv (sourceFamily F hpos heven).cumulant t := by
  set P := sourceFamily F hpos heven with hP
  have ht := mem_interior_integrableExpSet hpos heven hent t
  haveI : IsProbabilityMeasure P.base := P.isProb
  haveI : IsProbabilityMeasure (sourceLaw F) := isProbabilityMeasure_sourceLaw hpos
  have hint1 := P.integrable_stat_mul_exp t ht
  have hint2 := P.integrable_stat_mul_exp_neg t hint1
  have hsinh := P.integral_stat_mul_sinh t hint1 hint2
  change 0 < 4 * t * deriv (cgf P.stat P.base) t
  rw [deriv_cgf ht]
  have hmgf := mgf_pos (interior_subset (s := integrableExpSet P.stat P.base) ht)
  have hkey : 0 < ∫ x, t * P.stat x * Real.sinh (t * P.stat x) ∂P.base := by
    have hint : Integrable (fun x => t * P.stat x * Real.sinh (t * P.stat x)) P.base := by
      refine ((hint1.sub hint2).const_mul (t / 2)).congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply]
      rw [Real.sinh_eq, show -(t * P.stat x) = -t * P.stat x by ring]
      ring
    refine integral_pos_of_pos_off_point (c := 0) (sourceLaw_singleton F 0) hint
      (fun x => mul_sinh_nonneg _) fun x hx => mul_sinh_pos (mul_ne_zero ht0 hx)
  have hrel : ∫ x, t * P.stat x * Real.sinh (t * P.stat x) ∂P.base =
      t * ∫ x, P.stat x * Real.exp (t * P.stat x) ∂P.base := by
    rw [← hsinh, ← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hrel] at hkey
  have : 4 * t * ((∫ x, P.stat x * Real.exp (t * P.stat x) ∂P.base) / mgf P.stat P.base t) =
      4 * (t * ∫ x, P.stat x * Real.exp (t * P.stat x) ∂P.base) / mgf P.stat P.base t := by ring
  rw [this]
  positivity

/-- **The formation package.**  Every strictly positive even Schwartz source with entire Laplace
transform, with any common Markov recovery kernel, satisfies all six formation properties
`(EA.25)–(EA.29)`. -/
theorem sourceFamily_formationPackage {F : 𝓢(ℝ, ℝ)} (hpos : ∀ x, 0 < F x)
    (heven : ∀ x, F (-x) = F x) (hent : HasEntireLaplace F) {H : Type*} [MeasurableSpace H]
    (K : Kernel ℝ H) [IsMarkovKernel K] :
    FormationPackage (sourceFamily F hpos heven) K := by
  set P := sourceFamily F hpos heven with hP
  have hint : ∀ t, Integrable (fun x => Real.exp (t * P.stat x)) P.base :=
    fun t => integrable_exp_mul_sourceLaw hpos hent t
  have hJ : ∀ t, formationJeffreys (P.tilt t) (P.tilt (-t)) =
      ENNReal.ofReal (4 * t * deriv P.cumulant t) := fun t =>
    P.formationJeffreys_tilt t (mem_interior_integrableExpSet hpos heven hent t)
  refine ⟨P.cumulant_neg, P.map_reflection_tilt, fun t s => ?_,
    iteratedDeriv_two_cumulant_pos hpos heven hent, hJ, fun t ht => ?_, fun t => ?_⟩
  · haveI := P.isProbabilityMeasure_tilt t (hint t)
    haveI := P.isProbabilityMeasure_tilt s (hint s)
    exact klDiv_splitPacketLaw _ _ K
  · rw [hJ t]
    exact ENNReal.ofReal_pos.mpr (four_mul_deriv_cumulant_pos hpos heven hent ht)
  · haveI := P.isProbabilityMeasure_tilt t (hint t)
    haveI := P.isProbabilityMeasure_tilt (-t) (hint (-t))
    simp only [formationJeffreys, klDiv_splitPacketLaw]

/-! ## Countertheorem -/

/-- **Countertheorem 6.1, explicit form.**  For every `a ≠ 0` and `τ ≠ 0` there is a strictly
positive even Schwartz source with entire bilateral Laplace transform vanishing on the quartet
`±(a ± iτ)`, whose normalized exponential family satisfies the full formation package for every
common Markov recovery kernel. -/
theorem exists_offAxis_formation_countermodel (a : ℝ) {τ : ℝ} (hτ : τ ≠ 0) :
    ∃ F : 𝓢(ℝ, ℝ), ∃ hpos : ∀ x, 0 < F x, ∃ heven : ∀ x, F (-x) = F x,
      HasEntireLaplace F ∧ Differentiable ℂ (bilateralLaplace F) ∧
      bilateralLaplace F ((a : ℂ) + (τ : ℂ) * I) = 0 ∧
      bilateralLaplace F (-((a : ℂ) + (τ : ℂ) * I)) = 0 ∧
      bilateralLaplace F (starRingEnd ℂ ((a : ℂ) + (τ : ℂ) * I)) = 0 ∧
      bilateralLaplace F (-starRingEnd ℂ ((a : ℂ) + (τ : ℂ) * I)) = 0 ∧
      ∀ (H : Type) [MeasurableSpace H] (K : Kernel ℝ H) [IsMarkovKernel K],
        FormationPackage (sourceFamily F hpos heven) K := by
  have hent := hasEntireLaplace_twoShellSource a τ
  obtain ⟨h1, h2, h3, h4⟩ := twoShellSource_quartet a hτ
  exact ⟨twoShellSource a τ, twoShellSource_pos a τ, twoShellSource_neg a τ, hent,
    hent.differentiable, h1, h2, h3, h4, fun H _ K _ =>
      sourceFamily_formationPackage (twoShellSource_pos a τ) (twoShellSource_neg a τ) hent K⟩

/-- **Countertheorem 6.1.**  Positivity, Schwartz regularity, the functional equation, common
recovery, information conservation and strict reflected properness do not force the zeros of the
bilateral Laplace transform onto the reflection-fixed axis `Re z = 0`. -/
theorem no_generic_packet_selection :
    ¬ ∀ F : 𝓢(ℝ, ℝ), ∀ (hpos : ∀ x, 0 < F x) (heven : ∀ x, F (-x) = F x),
      HasEntireLaplace F →
      (∀ (H : Type) [MeasurableSpace H] (K : Kernel ℝ H) [IsMarkovKernel K],
        FormationPackage (sourceFamily F hpos heven) K) →
      ∀ z : ℂ, bilateralLaplace F z = 0 → z.re = 0 := by
  intro hsel
  obtain ⟨F, hpos, heven, hent, -, h0, -, -, -, hpack⟩ :=
    exists_offAxis_formation_countermodel 1 (τ := 1) one_ne_zero
  have := hsel F hpos heven hent hpack _ h0
  simp at this

end PositiveEvenLaplaceEscape

end GaloisForLFunctions.HTGeometry
