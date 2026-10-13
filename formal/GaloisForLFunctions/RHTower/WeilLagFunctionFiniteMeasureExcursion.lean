import GaloisForLFunctions.RHTower.WeilLagExponentialExceptionRigidity
import GaloisForLFunctions.RHTower.WeightedScrewPoleContradiction
import GaloisForLFunctions.RHTower.AsymptoticAbscissaLawProducers
import GaloisForLFunctions.RHTower.ZerosApproachLineAttainment
import GaloisForLFunctions.RHTower.JointAncestryExceptionalScales
import GaloisForLFunctions.RHTower.WeilLagFunctionSingleBase

/-!
# Lag excursions of finite measure exclude an attained top

**Theorem** (`re_le_half_add_of_attainedTop_of_le_exp_finiteMeasure`). Let `a` be real. If the
real lag function satisfies `Φ(L) ≤ M e^{aL}` for every `L ≥ 0` outside a measurable set of finite
measure, then an attained maximal real part `β₀` of the zeros satisfies `β₀ ≤ ½ + a`.

**Corollaries.**
* `Φ ≤ M` off a set of finite measure excludes an attained top right of the line, and so gives the
  asymptotic abscissa law (`asymptoticAbscissaLaw_of_weilLagFunctionReal_le_finiteMeasure`).
* RH holds iff the zeros approach the line and some excursion set `{L ≥ 0 : Φ(L) > M}` has finite
  measure (`riemannHypothesis_iff_zerosApproachLine_and_finiteMeasure_lagExcursion`); "zeros
  approach the line" may be replaced by eventual Hadamard positivity.
* Subexponential precision suffices for the abscissa law: if for every `a > 0` some bound
  `Φ ≤ M e^{aL}` holds off a set of finite measure, no top right of the line is attained
  (`asymptoticAbscissaLaw_of_forall_le_exp_finiteMeasure`), and with the zeros approaching the line
  this is RH (`riemannHypothesis_iff_zerosApproachLine_and_forall_le_exp_finiteMeasure`).
* RH holds iff the zeros approach the line and the level-one constant-vector JAS product tests are
  positive on the primes of every interval `(y, y + L]`, `y ≥ X + 1`, with `log y` outside a set of
  log-scales of finite measure
  (`riemannHypothesis_iff_zerosApproachLine_and_jasIntervalProductPositiveExcept_finiteMeasure`).

So once the zeros approach the line, the one-sided lag bound and the JAS producer may fail on any
set of scales of finite measure. Without the large-height input, exponentially thin exceptional sets
are tolerated (`riemannHypothesis_iff_integrableOn_exp_lagExcursion`), while abstract positive
configurations with a non-attained top have excursion sets of finite measure.

**Proof.** Divide by `e^{aL}`: the configuration with weights `1/(ρ(1−ρ))`, whose real parts are
positive, and exponents `ρ − ½ − a` is bounded above by `M` off `E`. Twist by `1 + cos(γ₀L)` at an
attaining zero `ρ₀ = β₀ + iγ₀`. Every weight of the twisted configuration has positive real part,
and it has the real exponent `β₀ − ½ − a` equal to its upper bound. The sharp one-round Landau
theorem across a set of finite measure says that a real exponent lies strictly below the upper bound
or is `≤ 0`, so `β₀ − ½ − a ≤ 0`.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

open OneSidedConfiguration BacklundConverse LindelofSparse

/-! ## The lag function as a positive configuration -/

/-- The exponents `ρ − ½ − a` of the lag function divided by `e^{aL}`. -/
def lagShiftExp (a : ℝ) (q : XiZeroCopy) : ℂ := (q.1 : ℂ) - 1 / 2 - a

theorem re_lagShiftExp (a : ℝ) (q : XiZeroCopy) :
    (lagShiftExp a q).re = (q.1 : ℂ).re - 1 / 2 - a := by
  simp [lagShiftExp]

theorem im_lagShiftExp (a : ℝ) (q : XiZeroCopy) : (lagShiftExp a q).im = (q.1 : ℂ).im := by
  simp [lagShiftExp]

/-- `Re Σ_ρ e^{t(ρ − ½ − a)}/(ρ(1−ρ)) = e^{−at} Φ(t)`. -/
theorem lagRe_lagShiftExp (a t : ℝ) :
    lagRe lagWeight (lagShiftExp a) t = Real.exp (-(a * t)) * weilLagFunctionReal t := by
  have h : ∑' q : XiZeroCopy, lagWeight q * cexp (t * lagShiftExp a q) =
      cexp ((-(a * t) : ℝ) : ℂ) * weilLagFunction t := by
    rw [weilLagFunction, ← tsum_mul_left]
    refine tsum_congr fun q => ?_
    have e : cexp (t * lagShiftExp a q) =
        cexp ((-(a * t) : ℝ) : ℂ) * cexp (t * ((q.1 : ℂ) - 1 / 2)) := by
      rw [← Complex.exp_add]; congr 1; simp only [lagShiftExp]; push_cast; ring
    rw [e, lagWeight]
    ring
  unfold lagRe
  rw [h, weilLagFunction_eq_ofReal, ← Complex.ofReal_exp, ← Complex.ofReal_mul,
    Complex.ofReal_re]

theorem finite_lagShiftExp_norm_le (a R : ℝ) :
    {q : XiZeroCopy | ‖lagShiftExp a q‖ ≤ R}.Finite := by
  refine (finite_xiZeroCopy_norm_le (R + |a|)).subset fun q hq => ?_
  simp only [mem_setOf_eq] at hq ⊢
  rw [norm_xiSpectralPoint]
  have h1 : (q.1 : ℂ) - 1 / 2 = lagShiftExp a q + (a : ℂ) := by simp only [lagShiftExp]; ring
  rw [h1]
  calc ‖lagShiftExp a q + (a : ℂ)‖ ≤ ‖lagShiftExp a q‖ + ‖(a : ℂ)‖ := norm_add_le _ _
    _ ≤ R + |a| := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith

theorem phaseWeight_zero (k : Fin 3) : phaseWeight 0 k = ((twistWeight k : ℝ) : ℂ) := by
  fin_cases k <;> simp [phaseWeight, twistWeight]

/-! ## Finite-measure excursions -/

/-- **Excursions of finite measure bound an attained top.** If `Φ(L) ≤ M e^{aL}` for every
`L ≥ 0` outside a measurable set of finite measure, and the maximal real part `β₀` of the zeros is
attained, then `β₀ ≤ ½ + a`. -/
theorem re_le_half_add_of_attainedTop_of_le_exp_finiteMeasure {M a β₀ : ℝ}
    {E : Set ℝ} (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤)
    (hM : ∀ L, 0 ≤ L → L ∉ E → weilLagFunctionReal L ≤ M * Real.exp (a * L))
    (htop : AttainedTop β₀) : β₀ ≤ 1 / 2 + a := by
  obtain ⟨⟨q₀, hq₀⟩, hall⟩ := htop
  by_contra hlt
  push Not at hlt
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = (q₀.1 : ℂ).im := ⟨_, rfl⟩
  have hBw : ∀ q, (lagShiftExp a q).re ≤ β₀ - 1 / 2 - a := fun q => by
    rw [re_lagShiftExp]; linarith [hall q]
  have hsum := summable_norm_lagWeight
  have hcoef : ∀ q : Fin 3 × XiZeroCopy,
      ‖phaseCoef γ 0 0 lagWeight (lagShiftExp a) q‖ ≤ ‖lagWeight q.2‖ := by
    intro q
    rw [phaseCoef, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_phaseWeight_le 0 q.1)
  have hnormQ : Summable fun q : Fin 3 × XiZeroCopy =>
      ‖phaseCoef γ 0 0 lagWeight (lagShiftExp a) q‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcoef ?_
    exact (summable_prod_of_nonneg fun q => norm_nonneg _).mpr
      ⟨fun _ => hsum, Summable.of_finite⟩
  have hpos : ∀ q : Fin 3 × XiZeroCopy,
      0 < (phaseCoef γ 0 0 lagWeight (lagShiftExp a) q).re := by
    intro q
    rw [phaseCoef, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, phaseWeight_zero,
      Complex.re_mul_ofReal]
    exact mul_pos (lagWeight_re_pos _) (twistWeight_pos _)
  have hMQ : ∀ t : ℝ, 0 ≤ t → t ∉ E →
      lagRe (phaseCoef γ 0 0 lagWeight (lagShiftExp a)) (twistExp γ (lagShiftExp a)) t ≤
        2 * max M 0 := by
    intro t ht htE
    rw [lagRe_phaseTwist hsum hBw γ 0 le_rfl ht]
    simp only [add_zero]
    rw [lagRe_lagShiftExp]
    have he := Real.exp_pos (-(a * t))
    have h2 : Real.exp (-(a * t)) * weilLagFunctionReal t ≤ M :=
      calc Real.exp (-(a * t)) * weilLagFunctionReal t
          ≤ Real.exp (-(a * t)) * (M * Real.exp (a * t)) :=
            mul_le_mul_of_nonneg_left (hM t ht htE) he.le
        _ = M := by
            rw [mul_comm M, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    have hcos := Real.neg_one_le_cos (γ * t)
    have hcos' := Real.cos_le_one (γ * t)
    have hm := le_max_left M 0
    have hm0 := le_max_right M 0
    nlinarith
  have hEint : IntegrableOn (fun u => Real.exp (0 * u)) E := by
    simp only [zero_mul, Real.exp_zero]
    exact integrableOn_const hEfin
  have hj : (twistExp γ (lagShiftExp a) (2, q₀)).im = 0 := by
    simp [twistExp, twistShift, im_lagShiftExp, hγ]
  have key := re_lt_or_nonpos_of_real_except (B := β₀ - 1 / 2 - a) hnormQ
    (finite_twistExp (finite_lagShiftExp_norm_le a) γ) (by linarith)
    (fun q => by rw [re_twistExp]; exact hBw _) (maxRealPositive_of_pos fun q _ _ => hpos q)
    hE le_rfl hEint hMQ (2, q₀) hj
  rw [re_twistExp, re_lagShiftExp, hq₀] at key
  rcases key with h | h <;> linarith

/-- **Excursions of finite measure exclude an attained top right of the line.** -/
theorem not_attainedTop_of_weilLagFunctionReal_le_finiteMeasure {M : ℝ} {E : Set ℝ}
    (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤)
    (hM : ∀ L, 0 ≤ L → L ∉ E → weilLagFunctionReal L ≤ M) :
    ¬ ∃ β₀ : ℝ, 1 / 2 < β₀ ∧ AttainedTop β₀ := by
  rintro ⟨β₀, hβ₀, htop⟩
  have := re_le_half_add_of_attainedTop_of_le_exp_finiteMeasure (M := M) (a := 0) hE hEfin
    (fun L hL hLE => by rw [zero_mul, Real.exp_zero, mul_one]; exact hM L hL hLE) htop
  linarith

/-- **Excursions of finite measure give the asymptotic abscissa law.** -/
theorem asymptoticAbscissaLaw_of_weilLagFunctionReal_le_finiteMeasure {M : ℝ} {E : Set ℝ}
    (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤)
    (hM : ∀ L, 0 ≤ L → L ∉ E → weilLagFunctionReal L ≤ M) : AsymptoticAbscissaLaw :=
  asymptoticAbscissaLaw_of_not_attainedTop
    (not_attainedTop_of_weilLagFunctionReal_le_finiteMeasure hE hEfin hM)

/-- **Zeros approaching the line and excursions of finite measure give RH.** -/
theorem riemannHypothesis_of_zerosApproachLine_of_le_finiteMeasure (hZ : ZerosApproachLine)
    {M : ℝ} {E : Set ℝ} (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤)
    (hM : ∀ L, 0 ≤ L → L ∉ E → weilLagFunctionReal L ≤ M) : RiemannHypothesis := by
  by_contra hRH
  exact not_attainedTop_of_weilLagFunctionReal_le_finiteMeasure hE hEfin hM
    (exists_attainedTop_of_zerosApproachLine hZ hRH)

/-- **RH ⟺ zeros approach the line ∧ some lag excursion set has finite measure.** -/
theorem riemannHypothesis_iff_zerosApproachLine_and_finiteMeasure_lagExcursion :
    RiemannHypothesis ↔ ZerosApproachLine ∧
      ∃ M : ℝ, volume {u : ℝ | 0 ≤ u ∧ M < weilLagFunctionReal u} ≠ ⊤ := by
  constructor
  · intro h
    refine ⟨zerosApproachLine_of_riemannHypothesis h, poleSharpConstant, ?_⟩
    have hempty : {u : ℝ | 0 ≤ u ∧ poleSharpConstant < weilLagFunctionReal u} = ∅ := by
      ext u
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
      intro _
      have := norm_weilLagFunction_le_of_riemannHypothesis h u
      rw [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] at this
      exact (le_abs_self _).trans this
    rw [hempty, measure_empty]
    exact ENNReal.zero_ne_top
  · rintro ⟨hZ, M, hfin⟩
    exact riemannHypothesis_of_zerosApproachLine_of_le_finiteMeasure hZ
      (measurableSet_Ici.inter (measurableSet_lt measurable_const measurable_weilLagFunctionReal))
      hfin (fun u hu huE => not_lt.mp fun h => huE ⟨hu, h⟩)

/-- **Subexponential one-sided precision off sets of finite measure excludes an attained top.** If
for every `a > 0` some bound `Φ(L) ≤ M e^{aL}` holds for all `L ≥ 0` outside a measurable set of
finite measure, then no top right of the line is attained. -/
theorem not_attainedTop_of_forall_le_exp_finiteMeasure
    (h : ∀ a : ℝ, 0 < a → ∃ (M : ℝ) (E : Set ℝ), MeasurableSet E ∧ volume E ≠ ⊤ ∧
      ∀ L, 0 ≤ L → L ∉ E → weilLagFunctionReal L ≤ M * Real.exp (a * L)) :
    ¬ ∃ β₀ : ℝ, 1 / 2 < β₀ ∧ AttainedTop β₀ := by
  rintro ⟨β₀, hβ₀, htop⟩
  obtain ⟨M, E, hE, hEfin, hM⟩ := h ((β₀ - 1 / 2) / 2) (by linarith)
  have := re_le_half_add_of_attainedTop_of_le_exp_finiteMeasure hE hEfin hM htop
  linarith

/-- **Subexponential one-sided precision off sets of finite measure gives the asymptotic abscissa
law.** -/
theorem asymptoticAbscissaLaw_of_forall_le_exp_finiteMeasure
    (h : ∀ a : ℝ, 0 < a → ∃ (M : ℝ) (E : Set ℝ), MeasurableSet E ∧ volume E ≠ ⊤ ∧
      ∀ L, 0 ≤ L → L ∉ E → weilLagFunctionReal L ≤ M * Real.exp (a * L)) :
    AsymptoticAbscissaLaw :=
  asymptoticAbscissaLaw_of_not_attainedTop (not_attainedTop_of_forall_le_exp_finiteMeasure h)

/-- **RH ⟺ zeros approach the line ∧ subexponential one-sided precision off sets of finite
measure.** -/
theorem riemannHypothesis_iff_zerosApproachLine_and_forall_le_exp_finiteMeasure :
    RiemannHypothesis ↔ ZerosApproachLine ∧ ∀ a : ℝ, 0 < a → ∃ (M : ℝ) (E : Set ℝ),
      MeasurableSet E ∧ volume E ≠ ⊤ ∧
        ∀ L, 0 ≤ L → L ∉ E → weilLagFunctionReal L ≤ M * Real.exp (a * L) := by
  constructor
  · intro hRH
    refine ⟨zerosApproachLine_of_riemannHypothesis hRH, fun a ha => ⟨lagWeightTotal, ∅,
      MeasurableSet.empty, by rw [measure_empty]; exact ENNReal.zero_ne_top, fun L hL _ => ?_⟩⟩
    have h1 := abs_weilLagFunctionReal_le_of_strip (a := 0) (fun q => by
      rw [xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q]; norm_num) hL
    rw [zero_mul, Real.exp_zero, one_mul] at h1
    calc weilLagFunctionReal L ≤ lagWeightTotal := (le_abs_self _).trans h1
      _ ≤ lagWeightTotal * Real.exp (a * L) :=
          le_mul_of_one_le_right lagWeightTotal_nonneg (Real.one_le_exp (mul_nonneg ha.le hL))
  · rintro ⟨hZ, h⟩
    by_contra hRH
    exact not_attainedTop_of_forall_le_exp_finiteMeasure h
      (exists_attainedTop_of_zerosApproachLine hZ hRH)

/-- **RH ⟺ eventual Hadamard positivity ∧ some lag excursion set has finite measure.** -/
theorem riemannHypothesis_iff_eventualHadamardPositivity_and_finiteMeasure_lagExcursion :
    RiemannHypothesis ↔ EventualHadamardPositivity ∧
      ∃ M : ℝ, volume {u : ℝ | 0 ≤ u ∧ M < weilLagFunctionReal u} ≠ ⊤ := by
  rw [eventualHadamardPositivity_iff_zerosApproachLine]
  exact riemannHypothesis_iff_zerosApproachLine_and_finiteMeasure_lagExcursion

/-! ## Route JAS off a set of scales of finite measure -/

/-- **Zeros approaching the line and level-one JAS positivity off a set of log-scales of finite
measure give RH.** -/
theorem riemannHypothesis_of_zerosApproachLine_of_jasIntervalProductPositiveExcept
    (hZ : ZerosApproachLine) {X : ℕ} {S : Set ℝ} (hpos : JasIntervalProductPositiveExcept X 1 S)
    (hS : MeasurableSet S) (hSfin : volume S ≠ ⊤) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨β₀, hβ₀, htop⟩ := exists_attainedTop_of_zerosApproachLine hZ hRH
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = β₀ - 1 / 2 := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hαdef]; linarith
  have hXi : XiZeroHalfPlaneBound α := by
    intro ρ hρ
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have := htop.2 q
    rw [hαdef]; linarith
  have hαall := abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi
  have hα1 : α < 1 / 2 := by
    obtain ⟨q₀, hq₀⟩ := htop.1
    have := xiZeroCopy_re_lt_one q₀
    rw [hαdef]; linarith
  have hδ0 : 0 < α / 4 := by linarith
  have hc0 : 0 < α / 2 := by linarith
  have hW := eventually_jasPositiveWindow_of_jasIntervalProductPositiveExcept hpos zero_le_one
    hδ0 (by linarith) hc0 (by linarith)
  obtain ⟨M, hM⟩ := exists_abs_weilLagFunctionReal_le_exp_of_windows_except hαall hδ0
    (by linarith) hc0 hW
  have hmax : max (α / 2) (α - min (α / 2) (α / 4 / 4)) = 15 * α / 16 := by
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]; ring
  rw [hmax] at hM
  have h := re_le_half_add_of_attainedTop_of_le_exp_finiteMeasure hS hSfin
    (fun L hL hLS => (le_abs_self _).trans (hM L hL hLS)) htop
  linarith

/-- **RH ⟺ zeros approach the line ∧ level-one JAS positivity off a set of log-scales of finite
measure.** -/
theorem riemannHypothesis_iff_zerosApproachLine_and_jasIntervalProductPositiveExcept_finiteMeasure :
    RiemannHypothesis ↔ ZerosApproachLine ∧ ∃ (X : ℕ) (S : Set ℝ), MeasurableSet S ∧
      volume S ≠ ⊤ ∧ JasIntervalProductPositiveExcept X 1 S := by
  constructor
  · intro hRH
    obtain ⟨X, hX⟩ := riemannHypothesis_iff_exists_jasIntervalProductPositive_one.mp hRH
    refine ⟨zerosApproachLine_of_riemannHypothesis hRH, X, ∅, MeasurableSet.empty, ?_,
      fun y L hy _ hL => hX y L hy hL⟩
    rw [measure_empty]
    exact ENNReal.zero_ne_top
  · rintro ⟨hZ, X, S, hS, hSfin, hpos⟩
    exact riemannHypothesis_of_zerosApproachLine_of_jasIntervalProductPositiveExcept hZ hpos hS
      hSfin

end

end RHTower
