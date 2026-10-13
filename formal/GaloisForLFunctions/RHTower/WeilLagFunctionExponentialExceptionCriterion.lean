import GaloisForLFunctions.RHTower.WeilLagFunctionPositivePart

/-!
# RH survives exponentially rare exceptions to the one-sided lag bound

**Theorem** (`riemannHypothesis_of_weilLagFunctionReal_le_except`). If the real lag function
satisfies `Φ(L) ≤ M` for every `L ≥ 0` outside a measurable set `E` with `∫_E e^{κL} dL < ∞` for
some `κ > 0`, then RH holds.

**Theorem** (`riemannHypothesis_iff_integrableOn_exp_lagExcursion`). RH holds iff for some `M` and
`κ > 0` the excursion set `{L ≥ 0 : Φ(L) > M}` satisfies `∫ e^{κL} dL < ∞`.

Equivalently, `ψ(x) ≥ x − M√x` (in the smoothed form `Φ(log x) ≤ M`) may fail on a set of
`x ∈ [X, eX]` of logarithmic measure `O(X^{−κ})` without losing RH.

**Proof.** If every zero copy has real part `≤ ½ + a`, then `|Φ(L)| ≤ W e^{aL}` for `L ≥ 0`
(`abs_weilLagFunctionReal_le_of_strip`). The positive part `Φ₊` is at most `max(M, 0)` off `E` and
at most `W e^{max(a−κ,0)T} e^{κL}` on `E ∩ [0,T]`, so
`∫_0^T Φ₊ ≤ max(M,0)T + W e^{max(a−κ,0)T} ∫_E e^{κL}`. The strip form of the integrated
positive-part criterion then gives real parts `≤ ½ + max(a − κ, 0)`. Start from `a = ½` and
iterate: after `⌈1/(2κ)⌉` rounds the primitive is sub-exponential, and the positive-part criterion
gives RH.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- Under a zero-free strip `Re ρ ≤ ½ + a` the lag function grows at most like `W e^{aL}`. -/
theorem abs_weilLagFunctionReal_le_of_strip {a : ℝ}
    (ha : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + a) {L : ℝ} (hL : 0 ≤ L) :
    |weilLagFunctionReal L| ≤ Real.exp (a * L) * lagWeightTotal := by
  have h1 : |weilLagFunctionReal L| = ‖weilLagFunction L‖ := by
    rw [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs]
  rw [h1]
  unfold weilLagFunction lagWeightTotal
  have hterm : ∀ q : XiZeroCopy,
      ‖Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤
        Real.exp (a * L) * ‖lagWeight q‖ := by
    intro q
    rw [div_eq_mul_one_div, norm_mul, Complex.norm_exp, lagWeight]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have hre : ((L : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = L * ((q.1 : ℂ).re - 1 / 2) := by
      simp [Complex.mul_re]
    rw [hre]
    have := ha q
    nlinarith
  have hs : Summable fun q : XiZeroCopy =>
      ‖Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (summable_norm_lagWeight.mul_left _)
  calc ‖∑' q : XiZeroCopy, Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖
      ≤ ∑' q : XiZeroCopy,
          ‖Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
        norm_tsum_le_tsum_norm hs
    _ ≤ ∑' q : XiZeroCopy, Real.exp (a * L) * ‖lagWeight q‖ :=
        hs.tsum_le_tsum hterm (summable_norm_lagWeight.mul_left _)
    _ = Real.exp (a * L) * ∑' q : XiZeroCopy, ‖lagWeight q‖ := tsum_mul_left

/-- **The positive part off an exponentially thin set.** -/
theorem integral_lagPositivePart_le_except {M κ a : ℝ} {E : Set ℝ} (hE : MeasurableSet E)
    (hEint : IntegrableOn (fun u => Real.exp (κ * u)) E)
    (hM : ∀ u, 0 ≤ u → u ∉ E → weilLagFunctionReal u ≤ M)
    (hgrowth : ∀ u, 0 ≤ u → |weilLagFunctionReal u| ≤ Real.exp (a * u) * lagWeightTotal)
    {T : ℝ} (hT : 0 ≤ T) :
    ∫ u in Icc (0:ℝ) T, lagPositivePart u ≤
      max M 0 * T + lagWeightTotal * Real.exp (max (a - κ) 0 * T) *
        ∫ u in E, Real.exp (κ * u) := by
  set m := max (a - κ) 0 with hm
  set ind : ℝ → ℝ := E.indicator (fun u => Real.exp (κ * u)) with hind
  have hindI : Integrable ind := (integrable_indicator_iff hE).mpr hEint
  have hW := lagWeightTotal_nonneg
  have hbound : ∀ u ∈ Icc (0:ℝ) T,
      lagPositivePart u ≤ max M 0 + lagWeightTotal * Real.exp (m * T) * ind u := by
    intro u hu
    rw [lagPositivePart_eq_max]
    by_cases huE : u ∈ E
    · have h1 := hgrowth u hu.1
      have hind1 : ind u = Real.exp (κ * u) := Set.indicator_of_mem huE _
      rw [hind1]
      have h2 : Real.exp (a * u) ≤ Real.exp (m * T) * Real.exp (κ * u) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have : (a - κ) * u ≤ m * T :=
          calc (a - κ) * u ≤ m * u := mul_le_mul_of_nonneg_right (le_max_left _ _) hu.1
            _ ≤ m * T := mul_le_mul_of_nonneg_left hu.2 (le_max_right _ _)
        linarith
      have h3 : max (weilLagFunctionReal u) 0 ≤ Real.exp (a * u) * lagWeightTotal :=
        max_le ((le_abs_self _).trans h1) (mul_nonneg (Real.exp_pos _).le hW)
      have h4 : Real.exp (a * u) * lagWeightTotal ≤
          lagWeightTotal * Real.exp (m * T) * Real.exp (κ * u) :=
        calc Real.exp (a * u) * lagWeightTotal
            ≤ (Real.exp (m * T) * Real.exp (κ * u)) * lagWeightTotal :=
              mul_le_mul_of_nonneg_right h2 hW
          _ = _ := by ring
      have h5 : 0 ≤ max M 0 := le_max_right _ _
      linarith
    · have hind0 : ind u = 0 := Set.indicator_of_notMem huE _
      rw [hind0, mul_zero, add_zero]
      exact max_le_max (hM u hu.1 huE) le_rfl
  have hint1 : IntegrableOn lagPositivePart (Icc 0 T) :=
    integrableOn_oneSidedDensity_zero_Icc (-1) T
  have hint2 : IntegrableOn (fun u => max M 0 + lagWeightTotal * Real.exp (m * T) * ind u)
      (Icc 0 T) :=
    (integrableOn_const (by simp)).add (hindI.integrableOn.const_mul _)
  have hle : ∫ u in Icc (0:ℝ) T, ind u ≤ ∫ u in E, Real.exp (κ * u) := by
    rw [← integral_indicator hE]
    exact setIntegral_le_integral hindI (Filter.Eventually.of_forall fun u =>
      Set.indicator_nonneg (fun u _ => (Real.exp_pos _).le) u)
  have hc : 0 ≤ lagWeightTotal * Real.exp (m * T) := mul_nonneg hW (Real.exp_pos _).le
  calc ∫ u in Icc (0:ℝ) T, lagPositivePart u
      ≤ ∫ u in Icc (0:ℝ) T, (max M 0 + lagWeightTotal * Real.exp (m * T) * ind u) :=
        setIntegral_mono_on hint1 hint2 measurableSet_Icc hbound
    _ = max M 0 * T + lagWeightTotal * Real.exp (m * T) * ∫ u in Icc (0:ℝ) T, ind u := by
        have hconst : IntegrableOn (fun _ : ℝ => max M 0) (Icc (0:ℝ) T) :=
          integrableOn_const (by simp)
        rw [integral_add hconst (hindI.integrableOn.const_mul _),
          integral_const_mul, setIntegral_const, Measure.real_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith)]
        simp [smul_eq_mul, mul_comm]
    _ ≤ max M 0 * T + lagWeightTotal * Real.exp (m * T) * ∫ u in E, Real.exp (κ * u) := by
        nlinarith [mul_le_mul_of_nonneg_left hle hc]

/-- The primitive of `Φ₊` grows at most like `e^{ηT}` for every `η > max(a − κ, 0)`. -/
theorem exists_integral_lagPositivePart_le_exp_except {M κ a : ℝ} {E : Set ℝ}
    (hE : MeasurableSet E) (hEint : IntegrableOn (fun u => Real.exp (κ * u)) E)
    (hM : ∀ u, 0 ≤ u → u ∉ E → weilLagFunctionReal u ≤ M)
    (hgrowth : ∀ u, 0 ≤ u → |weilLagFunctionReal u| ≤ Real.exp (a * u) * lagWeightTotal)
    {η : ℝ} (hη : max (a - κ) 0 < η) :
    ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T → ∫ u in Icc (0:ℝ) T, lagPositivePart u ≤ C * Real.exp (η * T) := by
  have hη0 : 0 < η := lt_of_le_of_lt (le_max_right _ _) hη
  refine ⟨max M 0 / η + lagWeightTotal * ∫ u in E, Real.exp (κ * u), fun T hT => ?_⟩
  have h1 := integral_lagPositivePart_le_except hE hEint hM hgrowth hT (κ := κ) (a := a)
  have hI0 : 0 ≤ ∫ u in E, Real.exp (κ * u) :=
    setIntegral_nonneg hE fun u _ => (Real.exp_pos _).le
  have hW := lagWeightTotal_nonneg
  have h2 : max M 0 * T ≤ max M 0 / η * Real.exp (η * T) := by
    have := Real.add_one_le_exp (η * T)
    rw [div_mul_eq_mul_div, le_div_iff₀ hη0]
    nlinarith [le_max_right M 0]
  have h3 : Real.exp (max (a - κ) 0 * T) ≤ Real.exp (η * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hη.le hT)
  have h4 : lagWeightTotal * Real.exp (max (a - κ) 0 * T) * ∫ u in E, Real.exp (κ * u) ≤
      lagWeightTotal * (∫ u in E, Real.exp (κ * u)) * Real.exp (η * T) :=
    calc lagWeightTotal * Real.exp (max (a - κ) 0 * T) * ∫ u in E, Real.exp (κ * u)
        = lagWeightTotal * (∫ u in E, Real.exp (κ * u)) * Real.exp (max (a - κ) 0 * T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (mul_nonneg hW hI0)
  calc ∫ u in Icc (0:ℝ) T, lagPositivePart u
      ≤ max M 0 * T + lagWeightTotal * Real.exp (max (a - κ) 0 * T) *
          ∫ u in E, Real.exp (κ * u) := h1
    _ ≤ max M 0 / η * Real.exp (η * T) +
          lagWeightTotal * (∫ u in E, Real.exp (κ * u)) * Real.exp (η * T) := by linarith
    _ = (max M 0 / η + lagWeightTotal * ∫ u in E, Real.exp (κ * u)) * Real.exp (η * T) := by
        ring

/-- **One round.** Growth `W e^{aL}` and a one-sided bound off an exponentially thin set give the
strip `Re ρ ≤ ½ + max(a − κ, 0)`. -/
theorem re_le_half_add_of_weilLagFunctionReal_le_except {M κ a : ℝ} {E : Set ℝ}
    (hE : MeasurableSet E) (hEint : IntegrableOn (fun u => Real.exp (κ * u)) E)
    (hM : ∀ u, 0 ≤ u → u ∉ E → weilLagFunctionReal u ≤ M)
    (hgrowth : ∀ u, 0 ≤ u → |weilLagFunctionReal u| ≤ Real.exp (a * u) * lagWeightTotal)
    (q : XiZeroCopy) : (q.1 : ℂ).re ≤ 1 / 2 + max (a - κ) 0 :=
  re_le_half_add_of_lagPositivePart_integral (le_max_right _ _)
    (fun _ hη => exists_integral_lagPositivePart_le_exp_except hE hEint hM hgrowth hη) q

/-- **RH survives exponentially rare exceptions.** If `Φ(L) ≤ M` for all `L ≥ 0` outside a
measurable set `E` with `∫_E e^{κL} dL < ∞`, `κ > 0`, then RH holds. -/
theorem riemannHypothesis_of_weilLagFunctionReal_le_except {M κ : ℝ} (hκ : 0 < κ) {E : Set ℝ}
    (hE : MeasurableSet E) (hEint : IntegrableOn (fun u => Real.exp (κ * u)) E)
    (hM : ∀ u, 0 ≤ u → u ∉ E → weilLagFunctionReal u ≤ M) : RiemannHypothesis := by
  have hstep : ∀ n : ℕ, ∀ q : XiZeroCopy,
      (q.1 : ℂ).re ≤ 1 / 2 + max (1 / 2 - ((n : ℝ) + 1) * κ) 0 := by
    intro n
    induction n with
    | zero =>
      intro q
      have h := re_le_half_add_of_weilLagFunctionReal_le_except hE hEint hM (a := 1 / 2)
        (fun u hu => by
          have h := abs_weilLagFunctionReal_le u
          rw [abs_of_nonneg hu] at h
          convert h using 3; ring) q
      simpa using h
    | succ n ih =>
      intro q
      have h := re_le_half_add_of_weilLagFunctionReal_le_except hE hEint hM
        (a := max (1 / 2 - ((n : ℝ) + 1) * κ) 0)
        (fun u hu => abs_weilLagFunctionReal_le_of_strip ih hu) q
      refine h.trans (le_of_eq ?_)
      push_cast
      rcases le_total (1 / 2 - ((n : ℝ) + 1) * κ) 0 with h1 | h1
      · rw [max_eq_right h1, zero_sub, max_eq_right (by linarith), max_eq_right (by linarith)]
      · rw [max_eq_left h1]; ring_nf
  set n := ⌈1 / (2 * κ)⌉₊ with hn
  have hn' : 1 / 2 ≤ (n : ℝ) * κ := by
    have h1 : 1 / (2 * κ) ≤ (n : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  have hstrip : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + 0 := by
    intro q
    have h := hstep n q
    rwa [max_eq_right (by nlinarith)] at h
  refine riemannHypothesis_of_lagPositivePart_integral_subexponential fun η hη => ?_
  exact exists_integral_lagPositivePart_le_exp_except hE hEint hM (a := 0)
    (fun u hu => abs_weilLagFunctionReal_le_of_strip hstrip hu)
    (by rw [max_eq_right (by linarith)]; exact hη)

/-- **Equivalence.** RH holds iff `Φ ≤ M` off an exponentially thin set of nonnegative lags. -/
theorem riemannHypothesis_iff_exists_weilLagFunctionReal_le_except :
    RiemannHypothesis ↔ ∃ (M κ : ℝ) (E : Set ℝ), 0 < κ ∧ MeasurableSet E ∧
      IntegrableOn (fun u => Real.exp (κ * u)) E ∧
        ∀ u, 0 ≤ u → u ∉ E → weilLagFunctionReal u ≤ M := by
  constructor
  · intro h
    refine ⟨poleSharpConstant, 1, ∅, one_pos, MeasurableSet.empty, integrableOn_empty,
      fun u _ _ => ?_⟩
    have := norm_weilLagFunction_le_of_riemannHypothesis h u
    rw [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  · rintro ⟨M, κ, E, hκ, hE, hEint, hM⟩
    exact riemannHypothesis_of_weilLagFunctionReal_le_except hκ hE hEint hM

/-- **Equivalence (excursion form).** RH holds iff for some `M` and `κ > 0`,
`∫_{\{L ≥ 0 : Φ(L) > M\}} e^{κL} dL < ∞`. -/
theorem riemannHypothesis_iff_integrableOn_exp_lagExcursion :
    RiemannHypothesis ↔ ∃ M κ : ℝ, 0 < κ ∧
      IntegrableOn (fun u => Real.exp (κ * u)) {u : ℝ | 0 ≤ u ∧ M < weilLagFunctionReal u} := by
  constructor
  · intro h
    refine ⟨poleSharpConstant, 1, one_pos, ?_⟩
    have hempty : {u : ℝ | 0 ≤ u ∧ poleSharpConstant < weilLagFunctionReal u} = ∅ := by
      ext u
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
      intro _
      have := norm_weilLagFunction_le_of_riemannHypothesis h u
      rw [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] at this
      exact (le_abs_self _).trans this
    rw [hempty]
    exact integrableOn_empty
  · rintro ⟨M, κ, hκ, hint⟩
    exact riemannHypothesis_of_weilLagFunctionReal_le_except hκ
      (measurableSet_Ici.inter (measurableSet_lt measurable_const measurable_weilLagFunctionReal))
      hint (fun u hu huE => not_lt.mp fun h => huE ⟨hu, h⟩)

end

end RHTower
