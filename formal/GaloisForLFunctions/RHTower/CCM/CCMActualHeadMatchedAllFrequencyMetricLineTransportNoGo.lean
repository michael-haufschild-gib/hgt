import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedAllFrequencyFockGramPositivityNoGo
import GaloisForLFunctions.HTGeometry.PolarizationTransportComponentCollapse

/-!
# Metric-compatible line transport cannot orient the matched all-frequency source

Every literal prime-power reporter has opposite Boolean orientations at its outer-phase `2π` and
`π` frequencies.  A nondegenerate one-dimensional real metric transported isometrically along a
graph has component-constant signature.  Consequently the two exact reporter witnesses cannot lie
in one transport component.

This kills connected metric-compatible line transport as the extra oriented structure left after
the all-frequency Gram-positivity no-go.  The positive survivor is a sharp signature wall: a viable
connection must split components, cross a degenerate or non-isometric edge, or use higher-rank
indefinite data whose orientation is not component-constant.
-/

open Complex MeasureTheory Set
open SimpleGraph

noncomputable section
namespace RHTower

/-- The two explicit reporter frequencies, with `true` denoting outer phase `2π` and `false`
denoting outer phase `π`. -/
def ccmActualHeadMatchedPhasePrimePowerReporterFrequency (n : ℕ) : Bool → ℝ
  | true => ccmActualHeadMatchedPhasePositiveReporterFrequency n
  | false => ccmActualHeadMatchedPhaseNegativeReporterFrequency n

/-- Boolean orientation of the exact all-frequency projective reporter. -/
def ccmActualHeadMatchedPhasePrimePowerReporterOrientation
    (n : ℕ) (side : Bool) : Bool :=
  decide (1 < ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockRatio
    (ccmActualHeadMatchedPhasePrimePowerReporterFrequency n side) n)

/-- Every literal prime power has positive reporter orientation at outer phase `2π`. -/
theorem ccmActualHeadMatchedPhasePrimePowerReporterOrientation_true
    (p : Nat.Primes) (e : ℕ) :
    ccmActualHeadMatchedPhasePrimePowerReporterOrientation
      (xiGammaEulerValuationNat (p, e)) true = true := by
  have h :=
    ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockPrimePowerReporterSignStraddle p e
  dsimp only at h
  simp [ccmActualHeadMatchedPhasePrimePowerReporterOrientation,
    ccmActualHeadMatchedPhasePrimePowerReporterFrequency, h.2.1]

/-- Every literal prime power has negative reporter orientation at outer phase `π`. -/
theorem ccmActualHeadMatchedPhasePrimePowerReporterOrientation_false
    (p : Nat.Primes) (e : ℕ) :
    ccmActualHeadMatchedPhasePrimePowerReporterOrientation
      (xiGammaEulerValuationNat (p, e)) false = false := by
  have h :=
    ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockPrimePowerReporterSignStraddle p e
  dsimp only at h
  have hnot : ¬ 1 < ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockRatio
      (ccmActualHeadMatchedPhaseNegativeReporterFrequency
        (xiGammaEulerValuationNat (p, e)))
      (xiGammaEulerValuationNat (p, e)) :=
    not_lt_of_ge h.2.2.le
  simp [ccmActualHeadMatchedPhasePrimePowerReporterOrientation,
    ccmActualHeadMatchedPhasePrimePowerReporterFrequency, hnot]

/-- **Signature-wall survivor.**  Any nondegenerate real line polarization faithful to the two
exact reporter witnesses has positive signature at outer phase `2π` and negative signature at
outer phase `π`. -/
theorem ccmActualHeadMatchedPhasePrimePowerReporterFaithfulLine_signatureSplit
    (p : Nat.Primes) (e : ℕ) {V : Type*} (c : V → ℝ) (u v : V)
    (hc : ∀ w, c w ≠ 0)
    (hu : GaloisForLFunctions.HTGeometry.signOrientation c u =
      ccmActualHeadMatchedPhasePrimePowerReporterOrientation
        (xiGammaEulerValuationNat (p, e)) true)
    (hv : GaloisForLFunctions.HTGeometry.signOrientation c v =
      ccmActualHeadMatchedPhasePrimePowerReporterOrientation
        (xiGammaEulerValuationNat (p, e)) false) :
    0 < c u ∧ c v < 0 := by
  rw [ccmActualHeadMatchedPhasePrimePowerReporterOrientation_true] at hu
  rw [ccmActualHeadMatchedPhasePrimePowerReporterOrientation_false] at hv
  have hcu : 0 < c u := of_decide_eq_true hu
  have hcv : ¬ 0 < c v := of_decide_eq_false hv
  exact ⟨hcu, lt_of_le_of_ne (le_of_not_gt hcv) (hc v)⟩

/-- **Transport-component separation.**  Edgewise isometric transport of nondegenerate real line
forms cannot connect the two exact reporter orientations of any literal prime power. -/
theorem ccmActualHeadMatchedPhasePrimePowerMetricLineTransport_not_reachable
    (p : Nat.Primes) (e : ℕ) {V : Type*} (G : SimpleGraph V) (u v : V)
    (c : V → ℝ) (hc : ∀ w, c w ≠ 0)
    (t : ∀ a b : V, G.Adj a b → ℝ)
    (hiso : ∀ (a b : V) (h : G.Adj a b) (x : ℝ),
      c b * (t a b h * x) ^ (2 : ℕ) = c a * x ^ (2 : ℕ))
    (hu : GaloisForLFunctions.HTGeometry.signOrientation c u =
      ccmActualHeadMatchedPhasePrimePowerReporterOrientation
        (xiGammaEulerValuationNat (p, e)) true)
    (hv : GaloisForLFunctions.HTGeometry.signOrientation c v =
      ccmActualHeadMatchedPhasePrimePowerReporterOrientation
        (xiGammaEulerValuationNat (p, e)) false) :
    ¬ G.Reachable u v := by
  intro huv
  let eps := GaloisForLFunctions.HTGeometry.compatibleOrientation_signOrientation
    G c hc t hiso
  have heq : GaloisForLFunctions.HTGeometry.signOrientation c u =
      GaloisForLFunctions.HTGeometry.signOrientation c v :=
    GaloisForLFunctions.eq_of_reachable_of_adj_invariant G Bool eps.2 huv
  have htf : true = false := by
    calc
      true = ccmActualHeadMatchedPhasePrimePowerReporterOrientation
          (xiGammaEulerValuationNat (p, e)) true :=
        (ccmActualHeadMatchedPhasePrimePowerReporterOrientation_true p e).symm
      _ = GaloisForLFunctions.HTGeometry.signOrientation c u := hu.symm
      _ = GaloisForLFunctions.HTGeometry.signOrientation c v := heq
      _ = ccmActualHeadMatchedPhasePrimePowerReporterOrientation
          (xiGammaEulerValuationNat (p, e)) false := hv
      _ = false := ccmActualHeadMatchedPhasePrimePowerReporterOrientation_false p e
  exact (by decide : true ≠ false) htf

/-- A connected nondegenerate metric-compatible line carrier claimed to realize both exact
prime-power reporter orientations. -/
def CCMActualHeadMatchedPhasePrimePowerConnectedMetricLineWardAt
    (p : Nat.Primes) (e : ℕ) : Prop :=
  ∃ (V : Type) (G : SimpleGraph V) (u v : V) (c : V → ℝ)
      (t : ∀ a b : V, G.Adj a b → ℝ),
    (∀ w, c w ≠ 0) ∧
    G.Preconnected ∧
    (∀ (a b : V) (h : G.Adj a b) (x : ℝ),
      c b * (t a b h * x) ^ (2 : ℕ) = c a * x ^ (2 : ℕ)) ∧
    GaloisForLFunctions.HTGeometry.signOrientation c u =
      ccmActualHeadMatchedPhasePrimePowerReporterOrientation
        (xiGammaEulerValuationNat (p, e)) true ∧
    GaloisForLFunctions.HTGeometry.signOrientation c v =
      ccmActualHeadMatchedPhasePrimePowerReporterOrientation
        (xiGammaEulerValuationNat (p, e)) false

/-- Connected metric-line realization at even one literal prime power. -/
def CCMActualHeadMatchedPhaseConnectedMetricLineWardRoute : Prop :=
  ∃ (p : Nat.Primes) (e : ℕ),
    CCMActualHeadMatchedPhasePrimePowerConnectedMetricLineWardAt p e

/-- **Connected metric-line Ward route kill.**  No connected nondegenerate metric-compatible
one-dimensional transport can orient the actual matched all-frequency source. -/
theorem ccmActualHeadMatchedPhaseConnectedMetricLineWardRouteKilled :
    ¬ CCMActualHeadMatchedPhaseConnectedMetricLineWardRoute := by
  rintro ⟨p, e, V, G, u, v, c, t, hc, hG, hiso, hu, hv⟩
  exact (ccmActualHeadMatchedPhasePrimePowerMetricLineTransport_not_reachable
    p e G u v c hc t hiso hu hv) (hG u v)

end RHTower
