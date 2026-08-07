import GaloisForLFunctions.RHTower.EulerActivationLevelCascade
import GaloisForLFunctions.RHTower.RouteRGammaCoronaHorizonGaugeIndependence
import Mathlib.MeasureTheory.Measure.MutuallySingular

/-!
# Route R squarefull-tail Gamma--Cartier index

The level-two tail event of the Euler activation product is an explicit
pre-divisor central projection detecting the Route R Gamma--Cartier port.
For an exponent `σ` in the open unit interval, its mass under the reflected
pair of activation measures is equal exactly at `σ = 1/2`.  Away from the
center the same event explicitly witnesses mutual singularity.

Specializing `σ` to the real part of an Xi divisor point identifies equality
on this single source projection with vanishing of the Gamma--Cartier port and
with arithmetic-horizon globalization.  No vanishing, critical-line, norm,
source-dagger, or RH hypothesis is used.

This does not prove the projection masses equal.  It reduces the remaining
producer burden from a full representation comparison to that one concrete
source equality.
-/

open MeasureTheory ProbabilityTheory Set
open GaloisForLFunctions.HTGeometry
open scoped ENNReal

namespace RHTower

noncomputable section

/-! ## The explicit source projection -/

/-- Configurations with only finitely many prime coordinates of multiplicity
at least two. -/
def routeREulerSquarefullTailEvent : Set CriticalEulerConfiguration :=
  {K | {p : Nat.Primes | 2 ≤ K p}.Finite}

theorem measurableSet_routeREulerSquarefullTailEvent :
    MeasurableSet routeREulerSquarefullTailEvent := by
  change MeasurableSet
    {K : CriticalEulerConfiguration |
      (localHitSet (fun _ : Nat.Primes => {k : ℕ | 2 ≤ k}) K).Finite}
  exact measurableSet_finiteHit
    (fun _ : Nat.Primes => {k : ℕ | 2 ≤ k})
    (Classical.choice (inferInstance : Nonempty (ℕ ≃ Nat.Primes)))

/-- Below and at the level-two boundary, the finite-squarefull projection is
null.  This is the zero half complementary to the existing almost-sure
infinite-squarefull theorem. -/
theorem eulerActivationProductMeasure_finiteSquarefull_eq_zero_of_le_half
    {σ : ℝ} (hσ : 0 < σ) (hhalf : σ ≤ 1 / 2) :
    eulerActivationProductMeasure hσ.le routeREulerSquarefullTailEvent = 0 := by
  change eulerActivationProductMeasure hσ.le
    {K : CriticalEulerConfiguration |
      (localHitSet (fun _ : Nat.Primes => {k : ℕ | 2 ≤ k}) K).Finite} = 0
  rw [finiteHit_eq_compl,
    MeasureTheory.prob_compl_eq_zero_iff
      (measurableSet_infiniteHit
        (fun _ : Nat.Primes => {k : ℕ | 2 ≤ k})
        (Classical.choice (inferInstance : Nonempty (ℕ ≃ Nat.Primes))))]
  exact eulerActivationProductMeasure_infiniteSquarefull_of_le_half hσ hhalf

/-- Exact zero classification for the finite-squarefull source projection. -/
theorem eulerActivationProductMeasure_finiteSquarefull_eq_zero_iff
    {σ : ℝ} (hσ : 0 < σ) :
    eulerActivationProductMeasure hσ.le routeREulerSquarefullTailEvent = 0 ↔
      σ ≤ 1 / 2 := by
  constructor
  · intro hzero
    by_contra hnot
    have hgt : 1 / 2 < σ := lt_of_not_ge hnot
    have hone :=
      (eulerActivationProductMeasure_finiteSquarefull_eq_one_iff hσ).2 hgt
    change eulerActivationProductMeasure hσ.le routeREulerSquarefullTailEvent = 1 at hone
    rw [hone] at hzero
    exact one_ne_zero hzero
  · exact eulerActivationProductMeasure_finiteSquarefull_eq_zero_of_le_half hσ

/-- The two reflected activation products assign the same mass to the
squarefull-tail projection exactly at the central exponent. -/
theorem eulerActivationProductMeasure_reflected_finiteSquarefull_eq_iff
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    eulerActivationProductMeasure hσ.le routeREulerSquarefullTailEvent =
        eulerActivationProductMeasure (sub_pos.mpr hσ1).le
          routeREulerSquarefullTailEvent ↔
      σ = 1 / 2 := by
  have href : 0 < 1 - σ := sub_pos.mpr hσ1
  constructor
  · intro hmass
    rcases lt_trichotomy σ (1 / 2) with hlt | heq | hgt
    · have hleft :=
        eulerActivationProductMeasure_finiteSquarefull_eq_zero_of_le_half
          hσ hlt.le
      have hright :=
        (eulerActivationProductMeasure_finiteSquarefull_eq_one_iff href).2 (by linarith)
      change eulerActivationProductMeasure hσ.le routeREulerSquarefullTailEvent = 0 at hleft
      change eulerActivationProductMeasure href.le routeREulerSquarefullTailEvent = 1 at hright
      rw [hleft, hright] at hmass
      exact (zero_ne_one hmass).elim
    · exact heq
    · have hleft :=
        (eulerActivationProductMeasure_finiteSquarefull_eq_one_iff hσ).2 hgt
      have hright :=
        eulerActivationProductMeasure_finiteSquarefull_eq_zero_of_le_half
          href (by linarith)
      change eulerActivationProductMeasure hσ.le routeREulerSquarefullTailEvent = 1 at hleft
      change eulerActivationProductMeasure href.le routeREulerSquarefullTailEvent = 0 at hright
      rw [hleft, hright] at hmass
      exact (one_ne_zero hmass).elim
  · intro heq
    subst σ
    have hleft :=
      eulerActivationProductMeasure_finiteSquarefull_eq_zero_of_le_half hσ (by norm_num)
    have hright :=
      eulerActivationProductMeasure_finiteSquarefull_eq_zero_of_le_half href (by norm_num)
    change eulerActivationProductMeasure hσ.le routeREulerSquarefullTailEvent = 0 at hleft
    change eulerActivationProductMeasure href.le routeREulerSquarefullTailEvent = 0 at hright
    rw [hleft, hright]

/-- Below the center, the finite-squarefull event is an explicit singularity
witness for the reflected activation measures. -/
theorem eulerActivationProductMeasure_reflected_mutuallySingular_of_lt_half
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hhalf : σ < 1 / 2) :
    eulerActivationProductMeasure hσ.le ⟂ₘ
      eulerActivationProductMeasure (sub_pos.mpr hσ1).le := by
  have href : 0 < 1 - σ := sub_pos.mpr hσ1
  refine ⟨routeREulerSquarefullTailEvent,
    measurableSet_routeREulerSquarefullTailEvent, ?_, ?_⟩
  · exact eulerActivationProductMeasure_finiteSquarefull_eq_zero_of_le_half
      hσ hhalf.le
  · rw [MeasureTheory.prob_compl_eq_zero_iff
      measurableSet_routeREulerSquarefullTailEvent]
    exact (eulerActivationProductMeasure_finiteSquarefull_eq_one_iff href).2 (by linarith)

/-- Off the center, the reflected Euler activation products are mutually
singular, witnessed by the finite-squarefull event or its complement. -/
theorem eulerActivationProductMeasure_reflected_mutuallySingular_of_ne_half
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hhalf : σ ≠ 1 / 2) :
    eulerActivationProductMeasure hσ.le ⟂ₘ
      eulerActivationProductMeasure (sub_pos.mpr hσ1).le := by
  rcases lt_or_gt_of_ne hhalf with hlt | hgt
  · exact eulerActivationProductMeasure_reflected_mutuallySingular_of_lt_half
      hσ hσ1 hlt
  · have href : 0 < 1 - σ := sub_pos.mpr hσ1
    refine ⟨routeREulerSquarefullTailEventᶜ,
      measurableSet_routeREulerSquarefullTailEvent.compl, ?_, ?_⟩
    · rw [MeasureTheory.prob_compl_eq_zero_iff
        measurableSet_routeREulerSquarefullTailEvent]
      exact (eulerActivationProductMeasure_finiteSquarefull_eq_one_iff hσ).2 hgt
    · rw [compl_compl]
      exact eulerActivationProductMeasure_finiteSquarefull_eq_zero_of_le_half
        href (by linarith)

/-! ## Xi specialization and Route R bridge -/

/-- Euler activation law at the real part of an Xi divisor point. -/
def routeREulerActivationMeasureAtXi (rho : XiDivisorSupport) :
    Measure CriticalEulerConfiguration :=
  eulerActivationProductMeasure
    (xi_divisor_support_re_mem_open_unit rho).1.le

/-- Reflected Euler activation law at exponent `1 - Re(rho)`. -/
def routeRReflectedEulerActivationMeasureAtXi (rho : XiDivisorSupport) :
    Measure CriticalEulerConfiguration :=
  eulerActivationProductMeasure
    (sub_pos.mpr (xi_divisor_support_re_mem_open_unit rho).2).le

/-- Equality of the two reflected source masses on the explicit level-two
tail projection. -/
def RouteREulerGammaSquarefullTailBalanced (rho : XiDivisorSupport) : Prop :=
  routeREulerActivationMeasureAtXi rho routeREulerSquarefullTailEvent =
    routeRReflectedEulerActivationMeasureAtXi rho routeREulerSquarefullTailEvent

theorem routeREulerGammaSquarefullTailBalanced_iff_re_eq_half
    (rho : XiDivisorSupport) :
    RouteREulerGammaSquarefullTailBalanced rho ↔
      (rho : ℂ).re = 1 / 2 := by
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  exact eulerActivationProductMeasure_reflected_finiteSquarefull_eq_iff
    hstrip.1 hstrip.2

/-- The explicit source projection is a complete detector of the
Gamma--Cartier port. -/
theorem routeREulerGammaSquarefullTailBalanced_iff_port_eq_zero
    (rho : XiDivisorSupport) :
    RouteREulerGammaSquarefullTailBalanced rho ↔
      routeRTwoThreeGammaCartierTransportPort rho = 0 := by
  have hport : routeRTwoThreeGammaCartierTransportPort rho = 0 ↔
      (rho : ℂ).re = 1 / 2 :=
    (routeRTwoThreeGammaCartierTransportPort_eq_zero_iff rho).trans
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho)
  exact (routeREulerGammaSquarefullTailBalanced_iff_re_eq_half rho).trans hport.symm

/-- Pointwise arithmetic-horizon globalization is exactly equality on the
single squarefull-tail source projection. -/
theorem routeRTwoThreeGammaArithmeticCorona_global_eq_local_iff_squarefullTailBalanced
    (rho : XiDivisorSupport) :
    routeRTwoThreeGammaSingularCoronaAction rho
          (routeRTwoThreeGammaArithmeticSingularCoronaPhysicalLift rho) =
        deningerCalderonWittCrossPrimeSingularCoronaClass
          (routeRTwoThreeGammaLocalPacketAction rho
            (routeRTwoThreeGammaArithmeticPacketPhysicalLift rho)) ↔
      RouteREulerGammaSquarefullTailBalanced rho := by
  exact (routeRTwoThreeGammaArithmeticCorona_global_eq_local_iff_port_eq_zero rho).trans
    (routeREulerGammaSquarefullTailBalanced_iff_port_eq_zero rho).symm

/-- Global arithmetic-horizon globalization is reduced to one explicit
pre-divisor source equality at each Xi divisor point. -/
theorem routeRTwoThreeGammaArithmeticCorona_globalization_iff_squarefullTailBalance :
    (∀ rho : XiDivisorSupport,
      routeRTwoThreeGammaSingularCoronaAction rho
          (routeRTwoThreeGammaArithmeticSingularCoronaPhysicalLift rho) =
        deningerCalderonWittCrossPrimeSingularCoronaClass
          (routeRTwoThreeGammaLocalPacketAction rho
            (routeRTwoThreeGammaArithmeticPacketPhysicalLift rho))) ↔
      ∀ rho : XiDivisorSupport, RouteREulerGammaSquarefullTailBalanced rho := by
  exact forall_congr' fun rho =>
    routeRTwoThreeGammaArithmeticCorona_global_eq_local_iff_squarefullTailBalanced rho

end

end RHTower
