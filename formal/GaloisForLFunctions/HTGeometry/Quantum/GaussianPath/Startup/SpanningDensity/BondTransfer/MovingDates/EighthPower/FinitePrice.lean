import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.EighthPower.MergerSlack.Finite

/-! # Eighth-power excess after the costs of weak and exceptional bonds -/
open Finset Filter Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open WeakBondDeficit FixedHorizon RepeatedGates RepeatedGates.Temporal RepeatedGates.Temporal.Feedback
noncomputable section

/-- For K ≥ 4j²⁵⁶ and t ≥ j⁻¹², a charge of order K t⁸ exceeds
the O(j¹⁵⁷) weak-bond and packet losses. An O(K t¹⁰) local cap loss
is absorbed up to a fixed positive time. -/
theorem eventual_eighth_price {c A D : ℝ} (hc : 0<c) (hD : 0≤D) :
    ∃ T>0, T≤1 ∧ ∀ᶠ j : ℕ in atTop, ∀ (n : ℕ) (ω : PathPauliDisorder) (t : ℝ),
      let u := pathPauliDisorderShell ω n
      let h := (1/(j:ℝ))^11
      4*(j:ℝ)^256≤((n+1:ℕ):ℝ) → (1/(j:ℝ))^12≤t → t≤T →
      ((weakEdges u h).card:ℝ)≤A*(j:ℝ)^157 →
      ((exceptionalEdges u (1/(3348*t))).card:ℝ)≤D*((n+2:ℕ):ℝ)*t^10 →
      missedBonds n (j^100) (h/1024) ω=∅ →
      ∀ (C : TwoQubitCircuit (n+2)) (z : ℂ), ‖z‖=1 →
        ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖≤1/4 →
        c*((n+1:ℕ):ℝ)*t^8≤(redundant (circuitWord C):ℝ)+1 →
        (1+c/2*t^8)*((n+1:ℕ):ℝ)<(C.gateCount:ℝ) := by
  obtain ⟨T,hT,hT₁,hw⟩ := eventual_eighth_merger_slack (A:=A) hc hD
  refine ⟨T,hT,hT₁,?_⟩
  filter_upwards [hw] with j hj
  intro n ω t u h hN hs ht hw hb hm C z hz he hr
  have hg := hj n ω t hN hs ht hw hb hm C z hz he
  linarith only [hg,hr]

#print axioms eventual_eighth_price
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
