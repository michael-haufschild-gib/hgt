import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePFiveChannelKreinFactorization
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolDeningerSecantGraphCompletion

/-!
# Finite SP-E/P history as a source graph completion

The full finite SP-E strict-cross current already factors through two literal
Route-P Julia blocks, but its ordered P history has distinct left and right
coefficient legs.  A source graph completion must therefore not replace that
history by a positive Gram or by an adjoint-symmetrized packet.

For an arbitrary finite coefficient vector `c`, the upper Deninger source
packet uses `star c`: the upper packet-to-jet map is semilinear, so this is
exactly what realizes `c` in the Xi jet carrier.  Applying this fact to the
four Julia-channel coefficients gives closed finite source graph lifts for
both directed legs of the actual P history.

This is a finite source-category theorem.  It neither bounds a cofinal family
nor identifies a graph pairing with the strict-cross current; those remain the
substantive SP-E/P obstruction.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A finite upper Deninger source packet realizing a prescribed linear combination of
primitive P graph reporters.  The source coefficient is conjugated because the upper packet
realization is semilinear. -/
def routePPrimitiveBurnolDeningerSecantLinearPacket {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ)
    (c : Fin N → ℂ) (n : ℕ) : DeningerPrimeGammaUpperPacket :=
  ∑ i, (starRingEnd ℂ) (c i) •
    routePPrimitiveBurnolDeningerSecantPacket (pe i) (kappa i) n

/-- The strong Xi-jet limit of `routePPrimitiveBurnolDeningerSecantLinearPacket`. -/
def routePPrimitiveBurnolDeningerGraphJetLinearCombination {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ)
    (c : Fin N → ℂ) : DeningerArithmeticJetHilbert :=
  ∑ i, c i • routePDeningerUpperSquaredCauchyJet
    (-finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (pe i)))
    (routePPrimitiveDeningerUpperPoint (pe i) (kappa i))

/-- **Finite source graph-lift law.** Every finite primitive P coefficient vector has a
coefficient-faithful upper Deninger secant realization converging strongly in the complete Xi
jet carrier. -/
theorem tendsto_routePPrimitiveBurnolDeningerSecantLinearPacket_to_graphJet
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ)
    (c : Fin N → ℂ) :
    Tendsto
      (fun n => deningerPrimeGammaUpperToJetHilbert
        (routePPrimitiveBurnolDeningerSecantLinearPacket pe kappa c n))
      atTop
      (nhds (routePPrimitiveBurnolDeningerGraphJetLinearCombination pe kappa c)) := by
  unfold routePPrimitiveBurnolDeningerSecantLinearPacket
    routePPrimitiveBurnolDeningerGraphJetLinearCombination
  simp only [map_sum, map_smulₛₗ _]
  apply tendsto_finsetSum
  intro i _
  simpa using (tendsto_routePPrimitiveBurnolDeningerSecantPacket_to_graphJet
    (pe i) (kappa i)).const_smul (c i)

/-- Coefficient of a primitive source label in the left directed leg of one actual finite
P-G186 history and one of the four nonradical SP-E Julia channels. -/
def speQuantileRieszRoutePDoubleJuliaHistoryCoefficient {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ)
    (i j : Fin N) (a : Fin 4) : ℂ :=
  (routePPrimitiveJointDepthPrimeLogConjugate pe
      (routePPrimitiveBurnolWindowGramMatrix pe kappa)) i j *
    ((speQuantileRieszStrictCrossFiveChannelProfile
        (fun b => xiGammaEulerValuationNat (pe b)) *
        Matrix.transpose speQuantileRieszStrictCrossFiveChannelToDoubleJulia) j a)

/-- Source secant packet for a left directed P history leg and one Julia channel. -/
def speQuantileRieszRoutePForwardDoubleJuliaGraphPacket {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ)
    (i : Fin N) (a : Fin 4) (n : ℕ) : DeningerPrimeGammaUpperPacket :=
  routePPrimitiveBurnolDeningerSecantLinearPacket pe kappa
    (fun j => speQuantileRieszRoutePDoubleJuliaHistoryCoefficient pe kappa i j a) n

/-- Xi jet reached by the left directed P history leg. -/
def speQuantileRieszRoutePForwardDoubleJuliaGraphJet {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ)
    (i : Fin N) (a : Fin 4) : DeningerArithmeticJetHilbert :=
  routePPrimitiveBurnolDeningerGraphJetLinearCombination pe kappa
    (fun j => speQuantileRieszRoutePDoubleJuliaHistoryCoefficient pe kappa i j a)

/-- Every left directed P history Julia channel has its exact finite source graph lift. -/
theorem tendsto_speQuantileRieszRoutePForwardDoubleJuliaGraphPacket_to_jet
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ)
    (i : Fin N) (a : Fin 4) :
    Tendsto
      (fun n => deningerPrimeGammaUpperToJetHilbert
        (speQuantileRieszRoutePForwardDoubleJuliaGraphPacket pe kappa i a n))
      atTop
      (nhds (speQuantileRieszRoutePForwardDoubleJuliaGraphJet pe kappa i a)) := by
  exact tendsto_routePPrimitiveBurnolDeningerSecantLinearPacket_to_graphJet
    pe kappa _

/-- Coefficient of a primitive source label in the right directed leg of the same P history.
It is deliberately not identified with the left leg: the P history is ordered. -/
def speQuantileRieszRoutePRightDoubleJuliaHistoryCoefficient {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ)
    (i j : Fin N) (a : Fin 4) : ℂ :=
  ((speQuantileRieszStrictCrossFiveChannelProfile
      (fun b => xiGammaEulerValuationNat (pe b)) *
      Matrix.transpose speQuantileRieszStrictCrossFiveChannelToDoubleJulia) i a) *
    (routePPrimitiveJointDepthPrimeLogConjugate pe
      (routePPrimitiveBurnolWindowGramMatrix pe kappa)) i j

/-- Source secant packet for a right directed P history leg and one Julia channel. -/
def speQuantileRieszRoutePRightDoubleJuliaGraphPacket {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ)
    (j : Fin N) (a : Fin 4) (n : ℕ) : DeningerPrimeGammaUpperPacket :=
  routePPrimitiveBurnolDeningerSecantLinearPacket pe kappa
    (fun i => speQuantileRieszRoutePRightDoubleJuliaHistoryCoefficient pe kappa i j a) n

/-- Xi jet reached by the right directed P history leg. -/
def speQuantileRieszRoutePRightDoubleJuliaGraphJet {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ)
    (j : Fin N) (a : Fin 4) : DeningerArithmeticJetHilbert :=
  routePPrimitiveBurnolDeningerGraphJetLinearCombination pe kappa
    (fun i => speQuantileRieszRoutePRightDoubleJuliaHistoryCoefficient pe kappa i j a)

/-- Every right directed P history Julia channel has its exact finite source graph lift. -/
theorem tendsto_speQuantileRieszRoutePRightDoubleJuliaGraphPacket_to_jet
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ)
    (j : Fin N) (a : Fin 4) :
    Tendsto
      (fun n => deningerPrimeGammaUpperToJetHilbert
        (speQuantileRieszRoutePRightDoubleJuliaGraphPacket pe kappa j a n))
      atTop
      (nhds (speQuantileRieszRoutePRightDoubleJuliaGraphJet pe kappa j a)) := by
  exact tendsto_routePPrimitiveBurnolDeningerSecantLinearPacket_to_graphJet
    pe kappa _

end

end RHTower
