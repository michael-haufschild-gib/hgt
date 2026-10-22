import GaloisForLFunctions.RHTower.GermExtension
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmSquarefreeFirstTraceExponentialContinuation
import GaloisForLFunctions.RHTower.XiSquarefreePoleUnitRootReduction

/-!
# Valuation-one reduction of the arithmetic Xi half-divisor

The squarefree pole unit still contains the zero-free Hilbert--Carleman determinant `D2`, which
encodes all prime powers of valuation at least two.  Its logarithm already converges on
`Re s > 1/2`, so

`D2_half(s) = exp(log(D2)(s) / 2)`

is an explicit analytic square root.  Dividing it out leaves the pole-cleared valuation-one field

`E1(s) = squarefreeMobiusCriticalPoleUnit(s) / D2(s)`.

On the Euler half-plane this is exactly `(s - 1) * exp(P(s))`, where `P` is the prime-zeta trace,
and its canonical arithmetic half is

`exp((log(s - 1) + P(s)) / 2)`.

Thus `RHLadder 1` is exactly the existence of an analytic continuation of this fixed far-right
arithmetic branch to `Re s > 1/2`.  The theorem removes every zero-free completion and
higher-valuation factor; it does not assert that the continuation exists.
-/

open Complex Filter Topology Set

namespace RHTower

open HedenmalmThetaSource

noncomputable section

/-- Explicit analytic square root of the Hilbert--Carleman determinant. -/
def squarefreeCarlemanHalfDet (s : ℂ) : ℂ :=
  Complex.exp ((1 / 2 : ℂ) * squarefreeCarlemanLogDet s)

/-- The explicit half-determinant squares to the full Carleman determinant. -/
theorem squarefreeCarlemanHalfDet_sq (s : ℂ) :
    squarefreeCarlemanHalfDet s ^ (2 : ℕ) = squarefreeCarlemanDet s := by
  rw [squarefreeCarlemanHalfDet, squarefreeCarlemanDet, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- The explicit half-determinant is analytic on the full Hilbert--Schmidt half-plane. -/
theorem analyticOnNhd_squarefreeCarlemanHalfDet_rightHalf :
    AnalyticOnNhd ℂ squarefreeCarlemanHalfDet rightHalf := by
  have hlog : AnalyticOnNhd ℂ squarefreeCarlemanLogDet rightHalf :=
    differentiableOn_squarefreeCarlemanLogDet.analyticOnNhd isOpen_rightHalf
  intro s hs
  exact (analyticAt_const.mul (hlog s hs)).cexp

/-- The explicit half-determinant is nowhere zero. -/
theorem squarefreeCarlemanHalfDet_ne_zero (s : ℂ) :
    squarefreeCarlemanHalfDet s ≠ 0 :=
  Complex.exp_ne_zero _

/-- Pole-cleared continuation of the exponential of the valuation-one prime trace. -/
def poleClearedFirstTraceExponentialContinuation (s : ℂ) : ℂ :=
  squarefreeMobiusCriticalPoleUnit s / squarefreeCarlemanDet s

/-- The pole unit is the Carleman determinant times the pole-cleared valuation-one field. -/
theorem squarefreeMobiusCriticalPoleUnit_eq_carleman_mul_poleClearedFirstTrace
    (s : ℂ) :
    squarefreeMobiusCriticalPoleUnit s =
      squarefreeCarlemanDet s * poleClearedFirstTraceExponentialContinuation s := by
  unfold poleClearedFirstTraceExponentialContinuation
  field_simp [squarefreeCarlemanDet_ne_zero]

/-- The pole-cleared valuation-one field is analytic on the strict right half-plane. -/
theorem analyticOnNhd_poleClearedFirstTraceExponentialContinuation_rightHalf :
    AnalyticOnNhd ℂ poleClearedFirstTraceExponentialContinuation rightHalf := by
  have hdet : AnalyticOnNhd ℂ squarefreeCarlemanDet rightHalf :=
    differentiableOn_squarefreeCarlemanDet.analyticOnNhd isOpen_rightHalf
  exact analyticOnNhd_squarefreeMobiusCriticalPoleUnit_rightHalf.div hdet
    (fun s _ => squarefreeCarlemanDet_ne_zero s)

/-- Removing the explicit Carleman unit preserves the complete Xi divisor. -/
theorem analyticOrderAt_poleClearedFirstTraceExponentialContinuation_eq_xi
    {s : ℂ} (hs : s ∈ rightHalf) :
    analyticOrderAt poleClearedFirstTraceExponentialContinuation s = analyticOrderAt xi s := by
  have hdet : AnalyticAt ℂ squarefreeCarlemanDet s :=
    (differentiableOn_squarefreeCarlemanDet.analyticOnNhd isOpen_rightHalf) s hs
  have hfirst := analyticOnNhd_poleClearedFirstTraceExponentialContinuation_rightHalf s hs
  have hpole := analyticOrderAt_squarefreeMobiusCriticalPoleUnit_eq_xi hs
  rw [← hpole]
  have heq : squarefreeMobiusCriticalPoleUnit =
      squarefreeCarlemanDet * poleClearedFirstTraceExponentialContinuation := by
    funext z
    exact squarefreeMobiusCriticalPoleUnit_eq_carleman_mul_poleClearedFirstTrace z
  rw [heq, analyticOrderAt_mul hdet hfirst,
    hdet.analyticOrderAt_eq_zero.mpr (squarefreeCarlemanDet_ne_zero s), zero_add]

/-- In the Euler chamber the pole-cleared field is exactly `(s-1) exp(P(s))`. -/
theorem poleClearedFirstTraceExponentialContinuation_eq_sub_one_mul_exp_primeZeta
    {s : ℂ} (hs : 1 < s.re) :
    poleClearedFirstTraceExponentialContinuation s =
      (s - 1) * Complex.exp (coronaPrimeZeta s) := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  rw [poleClearedFirstTraceExponentialContinuation,
    squarefreeMobiusCriticalPoleUnit_eq_sub_one_mul_squarefreePartition hs1,
    squarefreePartition_eq_carleman_mul_exp hs]
  field_simp [squarefreeCarlemanDet_ne_zero]

/-- Fixed arithmetic square-root germ in the Euler chamber. -/
def poleClearedPrimeZetaHalfEulerGerm (s : ℂ) : ℂ :=
  Complex.exp ((1 / 2 : ℂ) *
    (Complex.log (s - 1) + coronaPrimeZeta s))

/-- The fixed Euler germ is analytic on `Re s > 1`. -/
theorem analyticOnNhd_poleClearedPrimeZetaHalfEulerGerm_farHalf :
    AnalyticOnNhd ℂ poleClearedPrimeZetaHalfEulerGerm farHalf := by
  intro s hs
  have hslit : s - 1 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    rw [sub_re, one_re]
    linarith [mem_farHalf.mp hs]
  have hlog : AnalyticAt ℂ (fun z : ℂ => Complex.log (z - 1)) s :=
    (show AnalyticAt ℂ (fun z : ℂ => z - 1) s by fun_prop).clog hslit
  have hprime : AnalyticAt ℂ coronaPrimeZeta s := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_farHalf.mem_nhds hs] with z hz
    exact differentiableAt_coronaPrimeZeta (mem_farHalf.mp hz)
  exact (analyticAt_const.mul (hlog.add hprime)).cexp

/-- The fixed Euler germ squares to the pole-cleared valuation-one continuation. -/
theorem poleClearedPrimeZetaHalfEulerGerm_sq
    {s : ℂ} (hs : s ∈ farHalf) :
    poleClearedPrimeZetaHalfEulerGerm s ^ (2 : ℕ) =
      poleClearedFirstTraceExponentialContinuation s := by
  have hs1 : s - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    rw [h] at hs
    have hfalse := mem_farHalf.mp hs
    norm_num at hfalse
  rw [poleClearedFirstTraceExponentialContinuation_eq_sub_one_mul_exp_primeZeta
      (mem_farHalf.mp hs), poleClearedPrimeZetaHalfEulerGerm,
    ← Complex.exp_nat_mul]
  change Complex.exp ((2 : ℂ) * ((1 / 2 : ℂ) *
      (Complex.log (s - 1) + coronaPrimeZeta s))) = _
  rw [show (2 : ℂ) * ((1 / 2 : ℂ) *
      (Complex.log (s - 1) + coronaPrimeZeta s)) =
      Complex.log (s - 1) + coronaPrimeZeta s by ring]
  rw [Complex.exp_add, Complex.exp_log hs1]

/-- The fixed Euler germ is nowhere zero. -/
theorem poleClearedPrimeZetaHalfEulerGerm_ne_zero (s : ℂ) :
    poleClearedPrimeZetaHalfEulerGerm s ≠ 0 :=
  Complex.exp_ne_zero _

/-- The pole unit has a right-half square root iff its valuation-one factor does. -/
theorem exists_rightHalf_sqrt_squarefreeMobiusCriticalPoleUnit_iff_poleClearedFirstTrace :
    (∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h rightHalf ∧
        ∀ s ∈ rightHalf, h s ^ (2 : ℕ) = squarefreeMobiusCriticalPoleUnit s) ↔
      ∃ e : ℂ → ℂ, AnalyticOnNhd ℂ e rightHalf ∧
        ∀ s ∈ rightHalf, e s ^ (2 : ℕ) = poleClearedFirstTraceExponentialContinuation s := by
  constructor
  · rintro ⟨h, hh, hhsq⟩
    refine ⟨fun s => h s / squarefreeCarlemanHalfDet s,
      hh.div analyticOnNhd_squarefreeCarlemanHalfDet_rightHalf
        (fun s _ => squarefreeCarlemanHalfDet_ne_zero s), ?_⟩
    intro s hs
    rw [div_pow, hhsq s hs, squarefreeCarlemanHalfDet_sq,
      squarefreeMobiusCriticalPoleUnit_eq_carleman_mul_poleClearedFirstTrace]
    field_simp [squarefreeCarlemanDet_ne_zero]
  · rintro ⟨e, he, hesq⟩
    refine ⟨fun s => squarefreeCarlemanHalfDet s * e s,
      analyticOnNhd_squarefreeCarlemanHalfDet_rightHalf.mul he, ?_⟩
    intro s hs
    rw [mul_pow, squarefreeCarlemanHalfDet_sq, hesq s hs]
    exact (squarefreeMobiusCriticalPoleUnit_eq_carleman_mul_poleClearedFirstTrace s).symm

/-- Exact valuation-one arithmetic form of the first ladder rung. -/
theorem rhLadder_one_iff_poleClearedFirstTrace_sqrt :
    RHLadder 1 ↔ ∃ e : ℂ → ℂ, AnalyticOnNhd ℂ e rightHalf ∧
      ∀ s ∈ rightHalf, e s ^ (2 : ℕ) = poleClearedFirstTraceExponentialContinuation s := by
  rw [rhLadder_one_iff_squarefreeMobiusCriticalPoleUnit_sqrt,
    exists_rightHalf_sqrt_squarefreeMobiusCriticalPoleUnit_iff_poleClearedFirstTrace]

/-- Exact continuation criterion: rung one holds iff the fixed arithmetic Euler half-germ extends
analytically to a square root of the pole-cleared valuation-one field on `rightHalf`. -/
theorem rhLadder_one_iff_poleClearedPrimeZetaHalfEulerGerm_extends :
    RHLadder 1 ↔ ∃ e : ℂ → ℂ, AnalyticOnNhd ℂ e rightHalf ∧
      (∀ s ∈ rightHalf, e s ^ (2 : ℕ) = poleClearedFirstTraceExponentialContinuation s) ∧
      EqOn e poleClearedPrimeZetaHalfEulerGerm farHalf := by
  rw [rhLadder_one_iff_poleClearedFirstTrace_sqrt]
  constructor
  · rintro ⟨e, he, hesq⟩
    have hsquares : e 2 ^ (2 : ℕ) = poleClearedPrimeZetaHalfEulerGerm 2 ^ (2 : ℕ) := by
      rw [hesq 2 (farHalf_subset_rightHalf two_mem_farHalf),
        poleClearedPrimeZetaHalfEulerGerm_sq two_mem_farHalf]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquares with hmatch | hmatch
    · refine ⟨e, he, hesq, ?_⟩
      exact Bottcher.eqOn_of_pow_eq_of_isPreconnected (N := 2) (by norm_num)
        convex_farHalf.isPreconnected (he.continuousOn.mono farHalf_subset_rightHalf)
        analyticOnNhd_poleClearedPrimeZetaHalfEulerGerm_farHalf.continuousOn
        (fun s _ => poleClearedPrimeZetaHalfEulerGerm_ne_zero s)
        (fun s hs => by rw [hesq s (farHalf_subset_rightHalf hs),
          poleClearedPrimeZetaHalfEulerGerm_sq hs])
        two_mem_farHalf hmatch
    · refine ⟨fun s => -e s, he.neg, ?_, ?_⟩
      · intro s hs
        rw [neg_sq, hesq s hs]
      · have hanchor : -e 2 = poleClearedPrimeZetaHalfEulerGerm 2 := by
          rw [hmatch]
          ring
        exact Bottcher.eqOn_of_pow_eq_of_isPreconnected (N := 2) (by norm_num)
          convex_farHalf.isPreconnected
          ((he.neg).continuousOn.mono farHalf_subset_rightHalf)
          analyticOnNhd_poleClearedPrimeZetaHalfEulerGerm_farHalf.continuousOn
          (fun s _ => poleClearedPrimeZetaHalfEulerGerm_ne_zero s)
          (fun s hs => by rw [neg_sq, hesq s (farHalf_subset_rightHalf hs),
            poleClearedPrimeZetaHalfEulerGerm_sq hs])
          two_mem_farHalf hanchor
  · rintro ⟨e, he, hesq, _⟩
    exact ⟨e, he, hesq⟩

end

end RHTower
