import GaloisForLFunctions.RHTower.JointAncestryExceptionalScales
import GaloisForLFunctions.RHTower.JointAncestryRandomPhaseParseval

/-!
# One-sided prime-window means and random-phase variance at arbitrary `θ < 1` off exceptional scales

This module strengthens `WeilLagPrimeWindowMeanReceiver`, `JointAncestryExceptionalScales`, and
`JointAncestryRandomPhaseParseval` in three directions simultaneously:

1. **The negative-part mirror of the exceptional growth criterion**
   (`re_le_half_add_of_neg_exp_le_weilLagFunctionReal_except`,
   `riemannHypothesis_iff_integrableOn_exp_lagNegativeExcursion`).
   If `Φ(u) ≥ −M e^{au}` for `u ≥ 0` outside a measurable set `S` with `∫_S e^{κu} du < ∞` and
   `|Φ(u)| ≤ W e^{αu}`, then `Re ρ ≤ ½ + max(a, α − κ, 0)`. In particular, RH holds iff for some
   `M` and `κ > 0` the negative excursion set `{u ≥ 0 : Φ(u) < −M}` satisfies `∫ e^{κu} du < ∞`.

2. **Arbitrary-exponent `θ ∈ [0, 1)` one-sided prime-window means off exceptional scales**
   (`abs_re_sub_half_le_of_primeWindowMean_upper_except`,
   `abs_re_sub_half_le_of_primeWindowMean_lower_except`).
   Pointwise log-coherence on `jasIntervalPrimes (e^u) (e^{θu})` requires *no* prime-gap input:
   every prime in `(e^u, e^u + e^{θu}]` automatically has `log p ∈ [u, u + e^{−(1−θ)u}]`
   (`log_bounds_of_mem_jasIntervalPrimes_exp`). Consequently, for *any* `θ ∈ [0, 1)`, if outside
   an exponentially thin set `S` of log-scales (`∫_S e^{κu} du < ∞`, `κ > 0`) the window
   `P_u = jasIntervalPrimes (e^u) (e^{θu})` is nonempty and satisfies the *one-sided* bound
   `Σ_{p ∈ P_u} Φ(log p) ≤ C e^{cu} |P_u|` (or `≥ −C e^{cu} |P_u|`), then every zero satisfies
   `|Re ρ − ½| ≤ max(0, c)`.
   Because almost-all short intervals `(x, x + x^θ]` contain primes down to much smaller `θ` than
   the worst-case Huxley barrier `7/12` (with an exponentially thin set of exceptional log-scales),
   this decouples the window-mean receiver from worst-case prime gaps.

3. **Huxley specialization (`7/12 < θ < 1`) and random-phase variance off exceptional scales**
   (`riemannHypothesis_iff_forall_huxleyWindowMean_upper_except`,
   `riemannHypothesis_iff_forall_huxleyWindowMean_lower_except`,
   `abs_re_sub_half_le_of_phaseVariance_except`,
   `riemannHypothesis_iff_forall_huxleyPhaseVariance_except`).
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## The negative-part mirror of the integrated and exceptional growth criteria -/

/-- **The negative-part criterion (strip form).** If `∫_0^∞ Φ₋(u) e^{−σu} du < ∞` for every
`σ > a`, `a ≥ 0`, then every zero of `ξ` has real part `≤ ½ + a`. -/
theorem re_le_half_add_of_lagNegativePart_laplace {a : ℝ} (ha0 : 0 ≤ a)
    (h : ∀ σ : ℝ, a < σ → laplaceMass (oneSidedMeasure 1 0) σ ≠ ⊤) (q : XiZeroCopy) :
    (q.1 : ℂ).re ≤ 1 / 2 + a :=
  re_le_half_add_of_oneSidedMeasure_laplace (Or.inl rfl) ha0 h q

/-- **The integrated negative-part criterion (strip form).** If for every rate `η > a` the primitive
of the negative part satisfies `∫_0^T Φ₋ ≤ C_η e^{ηT}`, `a ≥ 0`, then every zero has real part
`≤ ½ + a`. -/
theorem re_le_half_add_of_lagNegativePart_integral {a : ℝ} (ha0 : 0 ≤ a)
    (hI : ∀ η : ℝ, a < η → ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T →
      ∫ u in Icc (0:ℝ) T, lagNegativePart u ≤ C * Real.exp (η * T)) (q : XiZeroCopy) :
    (q.1 : ℂ).re ≤ 1 / 2 + a := by
  refine re_le_half_add_of_lagNegativePart_laplace ha0 (fun σ hσ => ?_) q
  obtain ⟨C, hC⟩ := hI ((a + σ) / 2) (by linarith)
  exact laplaceMass_oneSidedMeasure_ne_top_of_integral_le (by linarith) (by linarith) hC

theorem integral_lagNegativePart_le_exp_except {M κ a α : ℝ} (ha0 : 0 ≤ a) {S : Set ℝ}
    (hS : MeasurableSet S) (hSint : IntegrableOn (fun u => Real.exp (κ * u)) S)
    (hM : ∀ u, 0 ≤ u → u ∉ S → -(M * Real.exp (a * u)) ≤ weilLagFunctionReal u)
    (hgrowth : ∀ u, 0 ≤ u → |weilLagFunctionReal u| ≤ Real.exp (α * u) * lagWeightTotal)
    {T : ℝ} (hT : 0 ≤ T) :
    ∫ u in Icc (0:ℝ) T, lagNegativePart u ≤
      max M 0 * Real.exp (a * T) * T + lagWeightTotal * Real.exp (max (α - κ) 0 * T) *
        ∫ u in S, Real.exp (κ * u) := by
  set m := max (α - κ) 0 with hm
  set ind : ℝ → ℝ := S.indicator (fun u => Real.exp (κ * u)) with hind
  have hindI : Integrable ind := (integrable_indicator_iff hS).mpr hSint
  have hW := lagWeightTotal_nonneg
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hbound : ∀ u ∈ Icc (0:ℝ) T,
      lagNegativePart u ≤ max M 0 * Real.exp (a * T) + lagWeightTotal * Real.exp (m * T) * ind u := by
    intro u hu
    rw [lagNegativePart_eq_max]
    have hea : Real.exp (a * u) ≤ Real.exp (a * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 ha0)
    by_cases huS : u ∈ S
    · have h1 := hgrowth u hu.1
      have hind1 : ind u = Real.exp (κ * u) := Set.indicator_of_mem huS _
      rw [hind1]
      have h2 : Real.exp (α * u) ≤ Real.exp (m * T) * Real.exp (κ * u) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have : (α - κ) * u ≤ m * T :=
          calc (α - κ) * u ≤ m * u := mul_le_mul_of_nonneg_right (le_max_left _ _) hu.1
            _ ≤ m * T := mul_le_mul_of_nonneg_left hu.2 (le_max_right _ _)
        linarith
      have h3 : max (-weilLagFunctionReal u) 0 ≤ Real.exp (α * u) * lagWeightTotal :=
        max_le ((neg_le_abs _).trans h1) (mul_nonneg (Real.exp_pos _).le hW)
      have h4 : Real.exp (α * u) * lagWeightTotal ≤
          lagWeightTotal * Real.exp (m * T) * Real.exp (κ * u) :=
        calc Real.exp (α * u) * lagWeightTotal
            ≤ (Real.exp (m * T) * Real.exp (κ * u)) * lagWeightTotal :=
              mul_le_mul_of_nonneg_right h2 hW
          _ = _ := by ring
      have h5 : 0 ≤ max M 0 * Real.exp (a * T) := mul_nonneg hM0 (Real.exp_pos _).le
      linarith
    · have hind0 : ind u = 0 := Set.indicator_of_notMem huS _
      rw [hind0, mul_zero, add_zero]
      refine max_le ?_ (mul_nonneg hM0 (Real.exp_pos _).le)
      have hMu : -weilLagFunctionReal u ≤ M * Real.exp (a * u) := by linarith [hM u hu.1 huS]
      calc -weilLagFunctionReal u ≤ M * Real.exp (a * u) := hMu
        _ ≤ max M 0 * Real.exp (a * u) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
        _ ≤ max M 0 * Real.exp (a * T) := mul_le_mul_of_nonneg_left hea hM0
  have hint1 : IntegrableOn lagNegativePart (Icc 0 T) :=
    integrableOn_oneSidedDensity_zero_Icc 1 T
  have hconst : IntegrableOn (fun _ : ℝ => max M 0 * Real.exp (a * T)) (Icc (0:ℝ) T) :=
    integrableOn_const (by simp)
  have hint2 : IntegrableOn
      (fun u => max M 0 * Real.exp (a * T) + lagWeightTotal * Real.exp (m * T) * ind u)
      (Icc 0 T) :=
    hconst.add (hindI.integrableOn.const_mul _)
  have hle : ∫ u in Icc (0:ℝ) T, ind u ≤ ∫ u in S, Real.exp (κ * u) := by
    rw [← integral_indicator hS]
    exact setIntegral_le_integral hindI (Filter.Eventually.of_forall fun u =>
      Set.indicator_nonneg (fun u _ => (Real.exp_pos _).le) u)
  have hc : 0 ≤ lagWeightTotal * Real.exp (m * T) := mul_nonneg hW (Real.exp_pos _).le
  calc ∫ u in Icc (0:ℝ) T, lagNegativePart u
      ≤ ∫ u in Icc (0:ℝ) T,
          (max M 0 * Real.exp (a * T) + lagWeightTotal * Real.exp (m * T) * ind u) :=
        setIntegral_mono_on hint1 hint2 measurableSet_Icc hbound
    _ = max M 0 * Real.exp (a * T) * T +
          lagWeightTotal * Real.exp (m * T) * ∫ u in Icc (0:ℝ) T, ind u := by
        rw [integral_add hconst (hindI.integrableOn.const_mul _),
          show ∫ u in Icc (0:ℝ) T, lagWeightTotal * Real.exp (m * T) * ind u =
            lagWeightTotal * Real.exp (m * T) * ∫ u in Icc (0:ℝ) T, ind u from
            integral_const_mul _ _,
          setIntegral_const, Measure.real_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith)]
        simp [smul_eq_mul, mul_comm]
    _ ≤ max M 0 * Real.exp (a * T) * T +
          lagWeightTotal * Real.exp (m * T) * ∫ u in S, Real.exp (κ * u) := by
        nlinarith [mul_le_mul_of_nonneg_left hle hc]

theorem exists_integral_lagNegativePart_le_exp_except_majorant {M κ a α : ℝ} (ha0 : 0 ≤ a)
    {S : Set ℝ} (hS : MeasurableSet S) (hSint : IntegrableOn (fun u => Real.exp (κ * u)) S)
    (hM : ∀ u, 0 ≤ u → u ∉ S → -(M * Real.exp (a * u)) ≤ weilLagFunctionReal u)
    (hgrowth : ∀ u, 0 ≤ u → |weilLagFunctionReal u| ≤ Real.exp (α * u) * lagWeightTotal)
    {η : ℝ} (hη : max (max a (α - κ)) 0 < η) :
    ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T → ∫ u in Icc (0:ℝ) T, lagNegativePart u ≤ C * Real.exp (η * T) := by
  have hηa : a < η := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hη
  have hηm : max (α - κ) 0 < η := by
    refine max_lt (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hη)
      (lt_of_le_of_lt (le_max_right _ _) hη)
  have hd : 0 < η - a := by linarith
  refine ⟨max M 0 / (η - a) + lagWeightTotal * ∫ u in S, Real.exp (κ * u), fun T hT => ?_⟩
  have h1 := integral_lagNegativePart_le_exp_except ha0 hS hSint hM hgrowth hT (κ := κ)
  have hI0 : 0 ≤ ∫ u in S, Real.exp (κ * u) :=
    setIntegral_nonneg hS fun u _ => (Real.exp_pos _).le
  have hW := lagWeightTotal_nonneg
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have h2 : max M 0 * Real.exp (a * T) * T ≤ max M 0 / (η - a) * Real.exp (η * T) := by
    have hT' : T ≤ Real.exp ((η - a) * T) / (η - a) := by
      rw [le_div_iff₀ hd]
      have := Real.add_one_le_exp ((η - a) * T)
      nlinarith
    have hsplit : Real.exp (η * T) = Real.exp (a * T) * Real.exp ((η - a) * T) := by
      rw [← Real.exp_add]; congr 1; ring
    calc max M 0 * Real.exp (a * T) * T
        ≤ max M 0 * Real.exp (a * T) * (Real.exp ((η - a) * T) / (η - a)) :=
          mul_le_mul_of_nonneg_left hT' (mul_nonneg hM0 (Real.exp_pos _).le)
      _ = max M 0 / (η - a) * Real.exp (η * T) := by rw [hsplit]; field_simp
  have h3 : Real.exp (max (α - κ) 0 * T) ≤ Real.exp (η * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hηm.le hT)
  have h4 : lagWeightTotal * Real.exp (max (α - κ) 0 * T) * ∫ u in S, Real.exp (κ * u) ≤
      lagWeightTotal * (∫ u in S, Real.exp (κ * u)) * Real.exp (η * T) :=
    calc lagWeightTotal * Real.exp (max (α - κ) 0 * T) * ∫ u in S, Real.exp (κ * u)
        = lagWeightTotal * (∫ u in S, Real.exp (κ * u)) * Real.exp (max (α - κ) 0 * T) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (mul_nonneg hW hI0)
  calc ∫ u in Icc (0:ℝ) T, lagNegativePart u
      ≤ max M 0 * Real.exp (a * T) * T + lagWeightTotal * Real.exp (max (α - κ) 0 * T) *
          ∫ u in S, Real.exp (κ * u) := h1
    _ ≤ max M 0 / (η - a) * Real.exp (η * T) +
          lagWeightTotal * (∫ u in S, Real.exp (κ * u)) * Real.exp (η * T) := by linarith
    _ = (max M 0 / (η - a) + lagWeightTotal * ∫ u in S, Real.exp (κ * u)) *
          Real.exp (η * T) := by ring

/-- **The lower growth criterion off an exponentially thin set.** If `Φ ≥ −M e^{aL}` for `L ≥ 0`
outside `S` with `∫_S e^{κu} < ∞`, and `|Φ| ≤ W e^{αL}`, then `Re ρ ≤ ½ + max(a, α − κ, 0)`. -/
theorem re_le_half_add_of_neg_exp_le_weilLagFunctionReal_except {M κ a α : ℝ} (ha0 : 0 ≤ a)
    {S : Set ℝ} (hS : MeasurableSet S) (hSint : IntegrableOn (fun u => Real.exp (κ * u)) S)
    (hM : ∀ u, 0 ≤ u → u ∉ S → -(M * Real.exp (a * u)) ≤ weilLagFunctionReal u)
    (hgrowth : ∀ u, 0 ≤ u → |weilLagFunctionReal u| ≤ Real.exp (α * u) * lagWeightTotal)
    (q : XiZeroCopy) : (q.1 : ℂ).re ≤ 1 / 2 + max (max a (α - κ)) 0 :=
  re_le_half_add_of_lagNegativePart_integral (le_max_right _ _)
    (fun _ hη => exists_integral_lagNegativePart_le_exp_except_majorant ha0 hS hSint hM hgrowth hη) q

/-- **RH survives exponentially rare exceptions to a lower lag bound.** If `Φ(L) ≥ −M` for all
`L ≥ 0` outside a measurable set `E` with `∫_E e^{κL} dL < ∞`, `κ > 0`, then RH holds. -/
theorem riemannHypothesis_of_neg_le_weilLagFunctionReal_except {M κ : ℝ} (hκ : 0 < κ) {E : Set ℝ}
    (hE : MeasurableSet E) (hEint : IntegrableOn (fun u => Real.exp (κ * u)) E)
    (hM : ∀ u, 0 ≤ u → u ∉ E → -M ≤ weilLagFunctionReal u) : RiemannHypothesis := by
  refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  haveI : Nonempty XiZeroCopy := ⟨q⟩
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = zeroReSup - 1 / 2 := ⟨_, rfl⟩
  have hXi : XiZeroHalfPlaneBound α := by
    intro ρ' hρ'
    obtain ⟨q', rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ'
    have := re_le_zeroReSup q'
    rw [hαdef]; linarith
  have hαall : ∀ q' : XiZeroCopy, |(q'.1 : ℂ).re - 1 / 2| ≤ α :=
    abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi
  have hstrip : ∀ q' : XiZeroCopy, (q'.1 : ℂ).re ≤ 1 / 2 + α := fun q' => by
    linarith [(abs_le.mp (hαall q')).2]
  have hg : ∀ q' : XiZeroCopy, (q'.1 : ℂ).re ≤ 1 / 2 + max (max 0 (α - κ)) 0 := fun q' =>
    re_le_half_add_of_neg_exp_le_weilLagFunctionReal_except (M := M) le_rfl hE hEint
      (fun u hu huE => by simpa using hM u hu huE)
      (fun u hu => abs_weilLagFunctionReal_le_of_strip hstrip hu) q'
  have hsup := zeroReSup_le hg
  have hΘ : zeroReSup = α + 1 / 2 := by rw [hαdef]; ring
  have hle : α ≤ max (max 0 (α - κ)) 0 := by linarith
  have hα0 : α ≤ 0 := by
    by_contra hlt
    push Not at hlt
    have hc1 : max 0 (α - κ) < α := max_lt hlt (by linarith)
    have hc2 : max (max 0 (α - κ)) 0 < α := max_lt hc1 hlt
    linarith
  have hq := hstrip q
  linarith

/-- **Equivalence.** RH holds iff `Φ ≥ −M` off an exponentially thin set of nonnegative lags. -/
theorem riemannHypothesis_iff_exists_neg_le_weilLagFunctionReal_except :
    RiemannHypothesis ↔ ∃ (M κ : ℝ) (E : Set ℝ), 0 < κ ∧ MeasurableSet E ∧
      IntegrableOn (fun u => Real.exp (κ * u)) E ∧
        ∀ u, 0 ≤ u → u ∉ E → -M ≤ weilLagFunctionReal u := by
  constructor
  · intro h
    refine ⟨poleSharpConstant, 1, ∅, one_pos, MeasurableSet.empty, integrableOn_empty,
      fun u _ _ => ?_⟩
    have := norm_weilLagFunction_le_of_riemannHypothesis h u
    rw [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] at this
    linarith [neg_abs_le (weilLagFunctionReal u)]
  · rintro ⟨M, κ, E, hκ, hE, hEint, hM⟩
    exact riemannHypothesis_of_neg_le_weilLagFunctionReal_except hκ hE hEint hM

/-- **Equivalence (negative-excursion form).** RH holds iff for some `M` and `κ > 0`,
`∫_{\{L ≥ 0 : Φ(L) < −M\}} e^{κL} dL < ∞`. -/
theorem riemannHypothesis_iff_integrableOn_exp_lagNegativeExcursion :
    RiemannHypothesis ↔ ∃ M κ : ℝ, 0 < κ ∧
      IntegrableOn (fun u => Real.exp (κ * u)) {u : ℝ | 0 ≤ u ∧ weilLagFunctionReal u < -M} := by
  constructor
  · intro h
    refine ⟨poleSharpConstant, 1, one_pos, ?_⟩
    have hempty : {u : ℝ | 0 ≤ u ∧ weilLagFunctionReal u < -poleSharpConstant} = ∅ := by
      ext u
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
      intro _
      have := norm_weilLagFunction_le_of_riemannHypothesis h u
      rw [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] at this
      linarith [neg_abs_le (weilLagFunctionReal u)]
    rw [hempty]
    exact integrableOn_empty
  · rintro ⟨M, κ, hκ, hint⟩
    exact riemannHypothesis_of_neg_le_weilLagFunctionReal_except hκ
      (measurableSet_Ici.inter (measurableSet_lt measurable_weilLagFunctionReal measurable_const))
      hint (fun u hu huE => not_lt.mp fun h => huE ⟨hu, h⟩)

/-! ## Log-bounds and one-sided coherence on arbitrary short prime windows -/

/-- Every prime in `jasIntervalPrimes (e^u) (e^{θu})` has `log p ∈ [u, u + e^{−(1−θ)u}]`, with no
restriction on `θ`. -/
theorem log_bounds_of_mem_jasIntervalPrimes_exp {θ u : ℝ} {p : Nat.Primes}
    (hp : p ∈ jasIntervalPrimes (Real.exp u) (Real.exp (θ * u))) :
    u ≤ Real.log ((p : ℕ) : ℝ) ∧ Real.log ((p : ℕ) : ℝ) ≤ u + Real.exp (-((1 - θ) * u)) := by
  have hy0 : 0 < Real.exp u := Real.exp_pos u
  have hL0 : 0 < Real.exp (θ * u) := Real.exp_pos (θ * u)
  obtain ⟨h1, h2⟩ := mem_jasIntervalPrimes_bounds hy0.le hL0.le hp
  have hp0 : 0 < ((p : ℕ) : ℝ) := by linarith
  constructor
  · rw [← Real.log_exp u]
    exact Real.log_le_log hy0 h1.le
  · have hlog : Real.log ((p : ℕ) : ℝ) ≤ Real.log (Real.exp u + Real.exp (θ * u)) :=
      Real.log_le_log hp0 h2
    have hfac : Real.exp u + Real.exp (θ * u) = Real.exp u * (1 + Real.exp (-((1 - θ) * u))) := by
      rw [mul_add, mul_one, ← Real.exp_add]; ring_nf
    have hpos : 0 < 1 + Real.exp (-((1 - θ) * u)) := by positivity
    rw [hfac, Real.log_mul hy0.ne' hpos.ne', Real.log_exp] at hlog
    have := Real.log_le_sub_one_of_pos hpos
    linarith

/-- One-sided upper coherence on a nonempty prime window `jasIntervalPrimes (e^u) (e^{θu})`. -/
theorem weilLagFunctionReal_le_of_primeWindow_sum_le {α θ u B : ℝ}
    (hα : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ α) (hθ1 : θ < 1) (hu : 0 ≤ u)
    (hne : (jasIntervalPrimes (Real.exp u) (Real.exp (θ * u))).Nonempty)
    (hsum : ∑ p ∈ jasIntervalPrimes (Real.exp u) (Real.exp (θ * u)),
      weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)) ≤
        B * (jasIntervalPrimes (Real.exp u) (Real.exp (θ * u))).card) :
    weilLagFunctionReal u ≤ B + Real.exp (α * u) * diagCoherence (1 - θ) u := by
  set P := jasIntervalPrimes (Real.exp u) (Real.exp (θ * u)) with hP
  have hδ0 : 0 < 1 - θ := by linarith
  have hcard : (0 : ℝ) < P.card := Nat.cast_pos.mpr hne.card_pos
  have hpt : ∀ p ∈ P, weilLagFunctionReal u ≤
      weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)) +
        Real.exp (α * u) * diagCoherence (1 - θ) u := by
    intro p hp
    have habs := abs_weilLagFunctionReal_log_sub_le hα hδ0 hu
      (log_bounds_of_mem_jasIntervalPrimes_exp hp)
    linarith [(abs_le.mp habs).1]
  have h1 := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul] at h1
  have h2 : (P.card : ℝ) * weilLagFunctionReal u ≤
      (P.card : ℝ) * (B + Real.exp (α * u) * diagCoherence (1 - θ) u) := by
    linarith
  exact le_of_mul_le_mul_left h2 hcard

/-- One-sided lower coherence on a nonempty prime window `jasIntervalPrimes (e^u) (e^{θu})`. -/
theorem neg_le_weilLagFunctionReal_of_le_primeWindow_sum {α θ u B : ℝ}
    (hα : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ α) (hθ1 : θ < 1) (hu : 0 ≤ u)
    (hne : (jasIntervalPrimes (Real.exp u) (Real.exp (θ * u))).Nonempty)
    (hsum : -(B * (jasIntervalPrimes (Real.exp u) (Real.exp (θ * u))).card) ≤
      ∑ p ∈ jasIntervalPrimes (Real.exp u) (Real.exp (θ * u)),
        weilLagFunctionReal (Real.log ((p : ℕ) : ℝ))) :
    -(B + Real.exp (α * u) * diagCoherence (1 - θ) u) ≤ weilLagFunctionReal u := by
  set P := jasIntervalPrimes (Real.exp u) (Real.exp (θ * u)) with hP
  have hδ0 : 0 < 1 - θ := by linarith
  have hcard : (0 : ℝ) < P.card := Nat.cast_pos.mpr hne.card_pos
  have hpt : ∀ p ∈ P,
      weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)) -
        Real.exp (α * u) * diagCoherence (1 - θ) u ≤ weilLagFunctionReal u := by
    intro p hp
    have habs := abs_weilLagFunctionReal_log_sub_le hα hδ0 hu
      (log_bounds_of_mem_jasIntervalPrimes_exp hp)
    linarith [(abs_le.mp habs).2]
  have h1 := Finset.sum_le_sum hpt
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul] at h1
  have h2 : -((P.card : ℝ) * (B + Real.exp (α * u) * diagCoherence (1 - θ) u)) ≤
      (P.card : ℝ) * weilLagFunctionReal u := by
    linarith
  have h3 : (P.card : ℝ) * -(B + Real.exp (α * u) * diagCoherence (1 - θ) u) ≤
      (P.card : ℝ) * weilLagFunctionReal u := by linarith
  exact le_of_mul_le_mul_left h3 hcard

/-- **Arbitrary-exponent one-sided upper prime-window mean criterion with exponential exceptions.**
For ANY `θ ∈ [0, 1)`, if outside a measurable set `S` of log-scales with `∫_S e^{κu} du < ∞`
(`κ > 0`) the prime window `(e^u, e^u + e^{θu}]` is eventually nonempty and has signed mean at most
`C e^{cu}`, then every zero satisfies `|Re ρ − ½| ≤ max(0, c)`. -/
theorem abs_re_sub_half_le_of_primeWindowMean_upper_except {c θ C κ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hC : 0 ≤ C) (hκ : 0 < κ) {S : Set ℝ} (hS : MeasurableSet S)
    (hSint : IntegrableOn (fun u => Real.exp (κ * u)) S)
    (h : ∀ᶠ u : ℝ in atTop, u ∉ S →
      (jasIntervalPrimes (Real.exp u) (Real.exp (θ * u))).Nonempty ∧
      ∑ p ∈ jasIntervalPrimes (Real.exp u) (Real.exp (θ * u)),
        weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)) ≤
          C * Real.exp (c * u) * (jasIntervalPrimes (Real.exp u) (Real.exp (θ * u))).card)
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  haveI : Nonempty XiZeroCopy := ⟨q⟩
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = zeroReSup - 1 / 2 := ⟨_, rfl⟩
  have hXi : XiZeroHalfPlaneBound α := by
    intro ρ hρ
    obtain ⟨q', rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have := re_le_zeroReSup q'
    rw [hαdef]; linarith
  have hαall : ∀ q' : XiZeroCopy, |(q'.1 : ℂ).re - 1 / 2| ≤ α :=
    abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi
  have hstrip : ∀ q' : XiZeroCopy, (q'.1 : ℂ).re ≤ 1 / 2 + α := fun q' => by
    linarith [(abs_le.mp (hαall q')).2]
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = max 0 c := ⟨_, rfl⟩
  rw [← hc']
  have hc'0 : 0 ≤ c' := hc' ▸ le_max_left _ _
  have hcc' : c ≤ c' := hc' ▸ le_max_right _ _
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 - θ := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  have hδ1 : δ ≤ 1 := by rw [hδdef]; linarith
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = max c' (α - δ / 4) := ⟨_, rfl⟩
  have hca : c' ≤ a := hadef ▸ le_max_left _ _
  have hm : α - δ / 4 ≤ a := hadef ▸ le_max_right _ _
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp h
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = C + 2 * Real.exp (1 / 2) * (3 / 2 * lagWeightTotal +
      80 * (|xiLineTwoLogDerivConstant| + 2) + 80 * (4 / δ)) := ⟨_, rfl⟩
  have hW := lagWeightTotal_nonneg
  have hM : ∀ L, 0 ≤ L → L ∉ S → weilLagFunctionReal L ≤
      max K (Real.exp (|u₀| / 2) * lagWeightTotal) * Real.exp (a * L) := by
    intro L hL hLS
    rcases le_or_gt u₀ L with hLu | hLu
    · obtain ⟨hne, hmean⟩ := hu₀ L hLu hLS
      have hΦL := weilLagFunctionReal_le_of_primeWindow_sum_le hαall hθ1 hL hne hmean
      rw [← hδdef] at hΦL
      have hcohb := diagCoherence_le hδ0 hδ1 hL
      have hcc : C * Real.exp (c * L) ≤ C * Real.exp (c' * L) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC
      have hw := windowMean_bound_le_exp (α := α) (c := c') (W := lagWeightTotal) (C := C)
        (D := |xiLineTwoLogDerivConstant|) (u := L) hδ0 hL hW hC (abs_nonneg _) hca hm
      rw [← hK] at hw
      have hfin := hΦL.trans (add_le_add hcc (mul_le_mul_of_nonneg_left hcohb (Real.exp_pos _).le))
      exact (hfin.trans hw).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    · have h1 := abs_weilLagFunctionReal_le L
      rw [abs_of_nonneg hL] at h1
      have h2 : Real.exp (L / 2) ≤ Real.exp (|u₀| / 2) :=
        Real.exp_le_exp.mpr (by linarith [le_abs_self u₀])
      have h3 : 1 ≤ Real.exp (a * L) := Real.one_le_exp (mul_nonneg ha0 hL)
      have h4 : weilLagFunctionReal L ≤ Real.exp (|u₀| / 2) * lagWeightTotal :=
        (le_abs_self _).trans (h1.trans (mul_le_mul_of_nonneg_right h2 hW))
      have h5 : 0 ≤ max K (Real.exp (|u₀| / 2) * lagWeightTotal) :=
        le_trans (by positivity) (le_max_right _ _)
      calc weilLagFunctionReal L ≤ max K (Real.exp (|u₀| / 2) * lagWeightTotal) :=
            h4.trans (le_max_right _ _)
        _ ≤ max K (Real.exp (|u₀| / 2) * lagWeightTotal) * Real.exp (a * L) :=
            le_mul_of_one_le_right h5 h3
  have hg : ∀ q' : XiZeroCopy, (q'.1 : ℂ).re ≤ 1 / 2 + max (max a (α - κ)) 0 := fun q' =>
    re_le_half_add_of_weilLagFunctionReal_le_exp_except ha0 hS hSint hM
      (fun u hu => abs_weilLagFunctionReal_le_of_strip hstrip hu) q'
  have hsup := zeroReSup_le hg
  have hΘ : zeroReSup = α + 1 / 2 := by rw [hαdef]; ring
  have hle : α ≤ max (max a (α - κ)) 0 := by linarith
  have hαc : α ≤ c' := by
    by_contra hlt
    push Not at hlt
    have hc1 : a < α := by rw [hadef]; exact max_lt hlt (by linarith)
    have hc2 : max a (α - κ) < α := max_lt hc1 (by linarith)
    have hc3 : max (max a (α - κ)) 0 < α := max_lt hc2 (by linarith)
    linarith
  exact (hαall q).trans hαc

/-- **Arbitrary-exponent one-sided lower prime-window mean criterion with exponential exceptions.**
For ANY `θ ∈ [0, 1)`, if outside a measurable set `S` of log-scales with `∫_S e^{κu} du < ∞`
(`κ > 0`) the prime window `(e^u, e^u + e^{θu}]` is eventually nonempty and has signed mean at least
`−C e^{cu}`, then every zero satisfies `|Re ρ − ½| ≤ max(0, c)`. -/
theorem abs_re_sub_half_le_of_primeWindowMean_lower_except {c θ C κ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hC : 0 ≤ C) (hκ : 0 < κ) {S : Set ℝ} (hS : MeasurableSet S)
    (hSint : IntegrableOn (fun u => Real.exp (κ * u)) S)
    (h : ∀ᶠ u : ℝ in atTop, u ∉ S →
      (jasIntervalPrimes (Real.exp u) (Real.exp (θ * u))).Nonempty ∧
      -(C * Real.exp (c * u) * (jasIntervalPrimes (Real.exp u) (Real.exp (θ * u))).card) ≤
        ∑ p ∈ jasIntervalPrimes (Real.exp u) (Real.exp (θ * u)),
          weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)))
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  haveI : Nonempty XiZeroCopy := ⟨q⟩
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = zeroReSup - 1 / 2 := ⟨_, rfl⟩
  have hXi : XiZeroHalfPlaneBound α := by
    intro ρ hρ
    obtain ⟨q', rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have := re_le_zeroReSup q'
    rw [hαdef]; linarith
  have hαall : ∀ q' : XiZeroCopy, |(q'.1 : ℂ).re - 1 / 2| ≤ α :=
    abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi
  have hstrip : ∀ q' : XiZeroCopy, (q'.1 : ℂ).re ≤ 1 / 2 + α := fun q' => by
    linarith [(abs_le.mp (hαall q')).2]
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = max 0 c := ⟨_, rfl⟩
  rw [← hc']
  have hc'0 : 0 ≤ c' := hc' ▸ le_max_left _ _
  have hcc' : c ≤ c' := hc' ▸ le_max_right _ _
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 - θ := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  have hδ1 : δ ≤ 1 := by rw [hδdef]; linarith
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = max c' (α - δ / 4) := ⟨_, rfl⟩
  have hca : c' ≤ a := hadef ▸ le_max_left _ _
  have hm : α - δ / 4 ≤ a := hadef ▸ le_max_right _ _
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp h
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = C + 2 * Real.exp (1 / 2) * (3 / 2 * lagWeightTotal +
      80 * (|xiLineTwoLogDerivConstant| + 2) + 80 * (4 / δ)) := ⟨_, rfl⟩
  have hW := lagWeightTotal_nonneg
  have hM : ∀ L, 0 ≤ L → L ∉ S →
      -(max K (Real.exp (|u₀| / 2) * lagWeightTotal) * Real.exp (a * L)) ≤
        weilLagFunctionReal L := by
    intro L hL hLS
    rcases le_or_gt u₀ L with hLu | hLu
    · obtain ⟨hne, hmean⟩ := hu₀ L hLu hLS
      have hΦL := neg_le_weilLagFunctionReal_of_le_primeWindow_sum hαall hθ1 hL hne hmean
      rw [← hδdef] at hΦL
      have hcohb := diagCoherence_le hδ0 hδ1 hL
      have hcc : C * Real.exp (c * L) ≤ C * Real.exp (c' * L) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC
      have hw := windowMean_bound_le_exp (α := α) (c := c') (W := lagWeightTotal) (C := C)
        (D := |xiLineTwoLogDerivConstant|) (u := L) hδ0 hL hW hC (abs_nonneg _) hca hm
      rw [← hK] at hw
      have h1 : C * Real.exp (c * L) + Real.exp (α * L) * diagCoherence δ L ≤
          max K (Real.exp (|u₀| / 2) * lagWeightTotal) * Real.exp (a * L) :=
        ((add_le_add hcc (mul_le_mul_of_nonneg_left hcohb (Real.exp_pos _).le)).trans hw).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
      linarith
    · have h1 := abs_weilLagFunctionReal_le L
      rw [abs_of_nonneg hL] at h1
      have h2 : Real.exp (L / 2) ≤ Real.exp (|u₀| / 2) :=
        Real.exp_le_exp.mpr (by linarith [le_abs_self u₀])
      have h3 : 1 ≤ Real.exp (a * L) := Real.one_le_exp (mul_nonneg ha0 hL)
      have h4 : |weilLagFunctionReal L| ≤ Real.exp (|u₀| / 2) * lagWeightTotal :=
        h1.trans (mul_le_mul_of_nonneg_right h2 hW)
      have h5 : 0 ≤ max K (Real.exp (|u₀| / 2) * lagWeightTotal) :=
        le_trans (by positivity) (le_max_right _ _)
      have h6 : |weilLagFunctionReal L| ≤
          max K (Real.exp (|u₀| / 2) * lagWeightTotal) * Real.exp (a * L) :=
        (h4.trans (le_max_right _ _)).trans (le_mul_of_one_le_right h5 h3)
      linarith [neg_abs_le (weilLagFunctionReal L)]
  have hg : ∀ q' : XiZeroCopy, (q'.1 : ℂ).re ≤ 1 / 2 + max (max a (α - κ)) 0 := fun q' =>
    re_le_half_add_of_neg_exp_le_weilLagFunctionReal_except ha0 hS hSint hM
      (fun u hu => abs_weilLagFunctionReal_le_of_strip hstrip hu) q'
  have hsup := zeroReSup_le hg
  have hΘ : zeroReSup = α + 1 / 2 := by rw [hαdef]; ring
  have hle : α ≤ max (max a (α - κ)) 0 := by linarith
  have hαc : α ≤ c' := by
    by_contra hlt
    push Not at hlt
    have hc1 : a < α := by rw [hadef]; exact max_lt hlt (by linarith)
    have hc2 : max a (α - κ) < α := max_lt hc1 (by linarith)
    have hc3 : max (max a (α - κ)) 0 < α := max_lt hc2 (by linarith)
    linarith
  exact (hαall q).trans hαc

/-! ## Huxley windows (`7/12 < θ < 1`): automatic nonemptiness and one-sided equivalences -/

/-- For `7/12 < θ < 1`, the Huxley prime window `jasIntervalPrimes (e^u) (e^{θu})` is eventually
nonempty. -/
theorem eventually_jasIntervalPrimes_exp_nonempty {θ : ℝ} (hθ : 7 / 12 < θ) (hθ1 : θ < 1) :
    ∀ᶠ u : ℝ in atTop, (jasIntervalPrimes (Real.exp u) (Real.exp (θ * u))).Nonempty := by
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 - θ := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  have hδ : δ < 5 / 12 := by rw [hδdef]; linarith
  obtain ⟨X₀, -, hX₀⟩ := exists_theta_window_lower_seven_twelfths
    (α := (7 / 12 + (1 - δ)) / 2) (by linarith) (by linarith)
  filter_upwards [eventually_diagWindow_conditions 0 (σ := 0) (δ := δ) (c := 1 / 2)
    (α' := (7 / 12 + (1 - δ)) / 2) (X₀ := X₀) (by linarith) (by linarith) (by norm_num)]
    with u ⟨hE1, hE1', hE2, hE3, _, hu1⟩
  obtain ⟨P, hPdef, -, hMass⟩ := exists_window (X := 0) (σ := 0) (c := 1 / 2) le_rfl hδ0
    (by linarith) (by linarith) hX₀ hu1 hE1 hE1' hE2 hE3
  have hcard : (0 : ℝ) < P.card := by
    have h1 : ∑ p ∈ P, Real.exp (-0 * Real.log ((p : ℕ) : ℝ)) = P.card := by simp
    rw [h1] at hMass
    exact lt_of_lt_of_le (Real.exp_pos _) hMass
  have hPne : P.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hcard)
  rwa [hPdef, show (1 - δ) * u = θ * u by rw [hδdef]; ring] at hPne

/-- **One-sided upper Huxley window mean criterion with exponential exceptions.** -/
theorem abs_re_sub_half_le_of_huxleyWindowMean_upper_except {c θ C κ : ℝ} (hθ : 7 / 12 < θ)
    (hθ1 : θ < 1) (hC : 0 ≤ C) (hκ : 0 < κ) {S : Set ℝ} (hS : MeasurableSet S)
    (hSint : IntegrableOn (fun u => Real.exp (κ * u)) S)
    (h : ∀ᶠ u : ℝ in atTop, u ∉ S →
      ∑ p ∈ jasIntervalPrimes (Real.exp u) (Real.exp (θ * u)),
        weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)) ≤
          C * Real.exp (c * u) * (jasIntervalPrimes (Real.exp u) (Real.exp (θ * u))).card)
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  refine abs_re_sub_half_le_of_primeWindowMean_upper_except (by linarith) hθ1 hC hκ hS hSint ?_ q
  filter_upwards [eventually_jasIntervalPrimes_exp_nonempty hθ hθ1, h] with u hne hu hLS
  exact ⟨hne, hu hLS⟩

/-- **One-sided lower Huxley window mean criterion with exponential exceptions.** -/
theorem abs_re_sub_half_le_of_huxleyWindowMean_lower_except {c θ C κ : ℝ} (hθ : 7 / 12 < θ)
    (hθ1 : θ < 1) (hC : 0 ≤ C) (hκ : 0 < κ) {S : Set ℝ} (hS : MeasurableSet S)
    (hSint : IntegrableOn (fun u => Real.exp (κ * u)) S)
    (h : ∀ᶠ u : ℝ in atTop, u ∉ S →
      -(C * Real.exp (c * u) * (jasIntervalPrimes (Real.exp u) (Real.exp (θ * u))).card) ≤
        ∑ p ∈ jasIntervalPrimes (Real.exp u) (Real.exp (θ * u)),
          weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)))
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  refine abs_re_sub_half_le_of_primeWindowMean_lower_except (by linarith) hθ1 hC hκ hS hSint ?_ q
  filter_upwards [eventually_jasIntervalPrimes_exp_nonempty hθ hθ1, h] with u hne hu hLS
  exact ⟨hne, hu hLS⟩

/-- **RH ⟺ one-sided upper subpower Huxley window means off exponentially thin sets.** -/
theorem riemannHypothesis_iff_forall_huxleyWindowMean_upper_except {θ : ℝ} (hθ : 7 / 12 < θ)
    (hθ1 : θ < 1) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ (C κ : ℝ) (S : Set ℝ), 0 ≤ C ∧ 0 < κ ∧
      MeasurableSet S ∧ IntegrableOn (fun u => Real.exp (κ * u)) S ∧
      ∀ᶠ u : ℝ in atTop, u ∉ S →
        ∑ p ∈ jasIntervalPrimes (Real.exp u) (Real.exp (θ * u)),
          weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)) ≤
            C * Real.exp (ε * u) * (jasIntervalPrimes (Real.exp u) (Real.exp (θ * u))).card := by
  constructor
  · intro hRH ε hε
    obtain ⟨C, hC, hev⟩ := (riemannHypothesis_iff_forall_primeWindowMean hθ hθ1).mp hRH ε hε
    refine ⟨C, 1, ∅, hC, one_pos, MeasurableSet.empty, integrableOn_empty, ?_⟩
    filter_upwards [Real.tendsto_exp_atTop.eventually hev] with u hu _
    rw [Real.log_exp] at hu
    exact (le_abs_self _).trans hu
  · intro h
    refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨C, κ, S, hC, hκ, hS, hSint, hev⟩ := h ε hε
    have := abs_re_sub_half_le_of_huxleyWindowMean_upper_except hθ hθ1 hC hκ hS hSint hev q
    rw [max_eq_right hε.le] at this
    linarith [le_abs_self ((q.1 : ℂ).re - 1 / 2)]

/-- **RH ⟺ one-sided lower subpower Huxley window means off exponentially thin sets.** -/
theorem riemannHypothesis_iff_forall_huxleyWindowMean_lower_except {θ : ℝ} (hθ : 7 / 12 < θ)
    (hθ1 : θ < 1) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ (C κ : ℝ) (S : Set ℝ), 0 ≤ C ∧ 0 < κ ∧
      MeasurableSet S ∧ IntegrableOn (fun u => Real.exp (κ * u)) S ∧
      ∀ᶠ u : ℝ in atTop, u ∉ S →
        -(C * Real.exp (ε * u) * (jasIntervalPrimes (Real.exp u) (Real.exp (θ * u))).card) ≤
          ∑ p ∈ jasIntervalPrimes (Real.exp u) (Real.exp (θ * u)),
            weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)) := by
  constructor
  · intro hRH ε hε
    obtain ⟨C, hC, hev⟩ := (riemannHypothesis_iff_forall_primeWindowMean hθ hθ1).mp hRH ε hε
    refine ⟨C, 1, ∅, hC, one_pos, MeasurableSet.empty, integrableOn_empty, ?_⟩
    filter_upwards [Real.tendsto_exp_atTop.eventually hev] with u hu _
    rw [Real.log_exp] at hu
    linarith [(abs_le.mp hu).1]
  · intro h
    refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨C, κ, S, hC, hκ, hS, hSint, hev⟩ := h ε hε
    have := abs_re_sub_half_le_of_huxleyWindowMean_lower_except hθ hθ1 hC hκ hS hSint hev q
    rw [max_eq_right hε.le] at this
    linarith [le_abs_self ((q.1 : ℂ).re - 1 / 2)]

/-! ## Random-phase variance receiver at arbitrary `θ ∈ [0, 1)` off exceptional scales -/

/-- **Arbitrary-exponent random-phase variance receiver with exponential exceptions.**
For ANY `θ ∈ [0, 1)`, `r > 0`, `N ≥ 3`, if outside a measurable set `S` of log-scales with
`∫_S e^{κu} du < ∞` (`κ > 0`) the window `P_u = jasIntervalPrimes (e^u) (e^{θu})` is eventually
nonempty and satisfies the variance budget, then every zero satisfies `|Re ρ − ½| ≤ max(0, c)`. -/
theorem abs_re_sub_half_le_of_phaseVariance_except {c θ C r κ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hC : 0 ≤ C) (hr : 0 < r) (hκ : 0 < κ) {N : ℕ} (hN : 3 ≤ N) {S : Set ℝ}
    (hS : MeasurableSet S) (hSint : IntegrableOn (fun u => Real.exp (κ * u)) S)
    (h : ∀ᶠ u : ℝ in atTop, u ∉ S →
      (jasIntervalPrimes (Real.exp u) (Real.exp (θ * u))).Nonempty ∧
      jasPhaseDevSq r N (jasIntervalPrimes (Real.exp u) (Real.exp (θ * u))) ≤
        jasPhaseVarianceBudget C c r N (jasIntervalPrimes (Real.exp u) (Real.exp (θ * u)))
          (Real.exp u))
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  refine abs_re_sub_half_le_of_primeWindowMean_upper_except hθ0 hθ1
    (C := 2 * Real.sqrt C / (r / (1 + r ^ 2))) (by positivity) hκ hS hSint ?_ q
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with u hu hu0 hLS
  obtain ⟨hne, hdev⟩ := hu hLS
  refine ⟨hne, ?_⟩
  have hx1 : 1 ≤ Real.exp u := Real.one_le_exp hu0
  have hwin : Real.exp (θ * u) ≤ Real.exp u :=
    Real.exp_le_exp.mpr (by nlinarith)
  have habs := abs_sum_weilLag_le_of_phaseDevSq hr hC hx1 hN
    (jasIntervalPrimes (Real.exp u) (Real.exp (θ * u))) (fun p hp => by
      have := mem_jasIntervalPrimes_bounds (Real.exp_pos u).le (Real.exp_pos _).le hp
      exact ⟨this.1, by linarith [this.2]⟩) hdev
  rw [Real.log_exp] at habs
  exact (le_abs_self _).trans habs

/-- **Huxley random-phase variance receiver with exponential exceptions.** -/
theorem abs_re_sub_half_le_of_huxleyPhaseVariance_except {c θ C r κ : ℝ} (hθ : 7 / 12 < θ)
    (hθ1 : θ < 1) (hC : 0 ≤ C) (hr : 0 < r) (hκ : 0 < κ) {N : ℕ} (hN : 3 ≤ N) {S : Set ℝ}
    (hS : MeasurableSet S) (hSint : IntegrableOn (fun u => Real.exp (κ * u)) S)
    (h : ∀ᶠ u : ℝ in atTop, u ∉ S →
      jasPhaseDevSq r N (jasIntervalPrimes (Real.exp u) (Real.exp (θ * u))) ≤
        jasPhaseVarianceBudget C c r N (jasIntervalPrimes (Real.exp u) (Real.exp (θ * u)))
          (Real.exp u))
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  refine abs_re_sub_half_le_of_phaseVariance_except (by linarith) hθ1 hC hr hκ hN hS hSint ?_ q
  filter_upwards [eventually_jasIntervalPrimes_exp_nonempty hθ hθ1, h] with u hne hu hLS
  exact ⟨hne, hu hLS⟩

/-- **RH ⟺ subpower Huxley random-phase variance off exponentially thin sets.** -/
theorem riemannHypothesis_iff_forall_huxleyPhaseVariance_except {θ r : ℝ} (hθ : 7 / 12 < θ)
    (hθ1 : θ < 1) (hr : 0 < r) {N : ℕ} (hN : 3 ≤ N) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ (C κ : ℝ) (S : Set ℝ), 0 ≤ C ∧ 0 < κ ∧
      MeasurableSet S ∧ IntegrableOn (fun u => Real.exp (κ * u)) S ∧
      ∀ᶠ u : ℝ in atTop, u ∉ S →
        jasPhaseDevSq r N (jasIntervalPrimes (Real.exp u) (Real.exp (θ * u))) ≤
          jasPhaseVarianceBudget C ε r N (jasIntervalPrimes (Real.exp u) (Real.exp (θ * u)))
            (Real.exp u) := by
  constructor
  · intro hRH ε hε
    obtain ⟨C, hC, hev⟩ := (riemannHypothesis_iff_forall_phaseVariance hθ hθ1 hr hN).mp hRH ε hε
    refine ⟨C, 1, ∅, hC, one_pos, MeasurableSet.empty, integrableOn_empty, ?_⟩
    filter_upwards [Real.tendsto_exp_atTop.eventually hev] with u hu _
    simpa [Real.log_exp] using hu
  · intro h
    refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨C, κ, S, hC, hκ, hS, hSint, hev⟩ := h ε hε
    have := abs_re_sub_half_le_of_huxleyPhaseVariance_except hθ hθ1 hC hr hκ hN hS hSint hev q
    rw [max_eq_right hε.le] at this
    linarith [le_abs_self ((q.1 : ℂ).re - 1 / 2)]

end

end RHTower
