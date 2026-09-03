import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownMediumMobiusFactor
import GaloisForLFunctions.RHTower.Sieve.MaynardLowOrdinateDerivativeReceiver
import GaloisForLFunctions.RHTower.Sieve.RouteTMoebiusEndpoint

/-!
# Menon's medium Mobius factor receiver

The exact Route-T pointwise saving on a literal medium Mobius atom is made uniform over a
separated frequency band and fed into the erase-complement Montgomery count.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- The literal Route-T contour-edge coefficient is monotone on its zero-free range. -/
theorem routeTContourEdgeBound_mono
    {A s t : ℝ} (hs : 8 * Real.pi ≤ s) (hst : s ≤ t) :
    routeTContourEdgeBound A s ≤ routeTContourEdgeBound A t := by
  have hbudget := routeTZeroFreeBudget_mono (A := A)
    (s := routeTInverseHeight s) (t := routeTInverseHeight t)
    (by unfold routeTInverseHeight; linarith) (by unfold routeTInverseHeight; linarith)
  have hbudget0 : 0 ≤ routeTZeroFreeBudget A (routeTInverseHeight s) :=
    (routeTZeroFreeBudget_pos A (routeTInverseHeight s)).le
  have hsq : routeTZeroFreeBudget A (routeTInverseHeight s) ^ (2 : ℕ) ≤
      routeTZeroFreeBudget A (routeTInverseHeight t) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hbudget0 hbudget 2
  unfold routeTContourEdgeBound
  exact Real.exp_le_exp.mpr (by nlinarith)

set_option maxHeartbeats 800000 in
/-- A literal medium Mobius atom supplies the uniform gain in the exact erase-complement
Montgomery count.  The common coefficient is evaluated at the actual top of the frequency band;
the common saving is the Route-T shift at that same height. -/
theorem exists_derivativeExcised_montgomery_heathBrownBox_moebius_routeTPower :
    ∃ (A C C' delta : ℝ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 < delta ∧
      ∀ (L X k : ℕ) (box : HeathBrownBoxChoice L X k)
          (j : HeathBrownBoxFactorIndex k box.m) (c : ℝ),
        heathBrownBoxFactorKind k box.m j = .moebius →
        1 ≤ heathBrownBoxFactorExponent box.a box.b box.q j →
        2 ^ heathBrownBoxFactorExponent box.a box.b box.q j ≤ L →
        0 ≤ c →
        ∀ {S : Finset ℕ} {lam : ℕ → ℝ} {sep H R Tlo D alpha : ℝ},
          0 < sep →
          0 ≤ H →
          (∀ i, lam i + sep ≤ lam (i + 1)) →
          (∀ r ∈ S, sep / 2 ≤ lam r ∧ lam r + sep / 2 ≤ H) →
          8 * Real.pi ≤ Tlo →
          (∀ r ∈ S, Tlo ≤ lam r) →
          ((((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) ^
              (4 : ℕ)) ≤ R →
          routeTInverseBaseHeight + R ≤ Tlo →
          0 < D →
          (∀ r ∈ S, D ^ (alpha - c) ≤
            ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
              ((c : ℂ) + (lam r : ℝ) * Complex.I)‖) →
          let N : ℝ :=
            (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
          let Edge : ℝ :=
            2 * routeTMoebiusPowerConstant C C' *
              routeTContourEdgeBound A (H + R)
          let Tsave : ℝ :=
            N ^ (routeTContourShift A delta (H + R) / 3)
          let I := {i : HeathBrownBoxFactorIndex k box.m //
            i ∈ (Finset.univ.erase j)}
          let q : I → ℕ := fun i =>
            heathBrownBoxFactorExponent box.a box.b box.q i
          let U : ℕ := groupedDyadicUpper q
          let E : ℕ := 2 * Fintype.card I + (2 ^ (2 * Fintype.card I) - 1)
          (S.card : ℝ) *
              (((Tsave / Edge) * D ^ (alpha - c) * N ^ (c - 1)) ^ 2) ≤
            (H + 4 * (U : ℝ) * (1 + Real.log U)) *
              (1 / sep + 2 * Real.log U) *
              (((groupedDyadicLower q : ℝ) ^ (-c)) ^ 2 *
                ((U : ℝ) * (1 + Real.log (U : ℝ)) ^ E)) := by
  obtain ⟨A, C, C', delta, hC, hC', hdelta, hroute⟩ :=
    exists_norm_heathBrownBoxFactorValue_moebius_le_routeTPower
  refine ⟨A, C, C', delta, hC, hC', hdelta, ?_⟩
  intro L X k box j c hkind hq hqL hc S lam sep H R Tlo D alpha
    hsep hH hgap hband hTlo hlow hR hbase hD hlarge
  let N : ℝ :=
    (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
  let Edge : ℝ :=
    2 * routeTMoebiusPowerConstant C C' * routeTContourEdgeBound A (H + R)
  let Tsave : ℝ := N ^ (routeTContourShift A delta (H + R) / 3)
  have hN1 : 1 ≤ N := by
    dsimp only [N]
    have hp : 0 < 2 ^ heathBrownBoxFactorExponent box.a box.b box.q j := by
      exact pow_pos (by norm_num) _
    exact_mod_cast hp
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have hR0 : 0 ≤ R := by
    exact (pow_nonneg hN0.le 4).trans hR
  have hEdge : 0 < Edge := by
    dsimp only [Edge]
    have hpower : 0 < routeTMoebiusPowerConstant C C' :=
      routeTMoebiusPowerConstant_pos hC hC'
    have hedge : 0 < routeTContourEdgeBound A (H + R) := by
      unfold routeTContourEdgeBound
      positivity
    exact mul_pos (mul_pos (by norm_num) hpower) hedge
  have hTsave : 0 < Tsave := by
    dsimp only [Tsave]
    positivity
  have hpoint : ∀ r ∈ S,
      ‖heathBrownBoxFactorValue L X k box
          ((c : ℂ) + (lam r : ℝ) * Complex.I) j‖ ≤
        Edge / Tsave * N ^ (1 - c) := by
    intro r hr
    let sFreq : ℝ := |lam r| + R
    let tFreq : ℝ := H + R
    let shiftS : ℝ := routeTContourShift A delta sFreq / 3
    let shiftT : ℝ := routeTContourShift A delta tFreq / 3
    let coeffS : ℝ := 2 * routeTMoebiusPowerConstant C C' *
      routeTContourEdgeBound A sFreq
    let coeffT : ℝ := 2 * routeTMoebiusPowerConstant C C' *
      routeTContourEdgeBound A tFreq
    have hlamLow : Tlo ≤ lam r := hlow r hr
    have hlamPos : 0 < lam r := lt_of_lt_of_le
      (by positivity : 0 < 8 * Real.pi) (hTlo.trans hlamLow)
    have habs : |lam r| = lam r := abs_of_pos hlamPos
    have hlamHigh : lam r ≤ H := by
      have := (hband r hr).2
      linarith [hsep]
    have hfreq8 : 8 * Real.pi ≤ sFreq := by
      dsimp only [sFreq]
      rw [habs]
      linarith
    have hfreqTop : sFreq ≤ tFreq := by
      dsimp only [sFreq, tFreq]
      rw [habs]
      linarith
    have hraw := hroute L X k box j c (lam r) R hkind hq hqL hc hR
      (by rw [habs]; exact hbase.trans hlamLow)
    have hedgeMono : routeTContourEdgeBound A sFreq ≤
        routeTContourEdgeBound A tFreq :=
      routeTContourEdgeBound_mono hfreq8 hfreqTop
    have hshiftMono : routeTContourShift A delta tFreq ≤
        routeTContourShift A delta sFreq :=
      routeTContourShift_antitone hfreq8 hfreqTop
    have hshift : shiftT ≤ shiftS := by
      dsimp only [shiftS, shiftT]
      linarith
    have hexp : 1 - c - shiftS ≤ 1 - c - shiftT := by
      linarith
    have hpow : N ^ (1 - c - shiftS) ≤ N ^ (1 - c - shiftT) :=
      Real.rpow_le_rpow_of_exponent_le hN1 hexp
    have hcoeff0 : 0 ≤ 2 * routeTMoebiusPowerConstant C C' := by
      positivity [routeTMoebiusPowerConstant_pos hC hC']
    have hedge0 : 0 ≤ routeTContourEdgeBound A sFreq := by
      unfold routeTContourEdgeBound
      positivity
    have hraw' :
        ‖heathBrownBoxFactorValue L X k box
            ((c : ℂ) + (lam r : ℝ) * Complex.I) j‖ ≤
          coeffS * N ^ (1 - c - shiftS) := by
      simpa only [coeffS, shiftS, sFreq, N] using hraw
    have hcoeffMono : coeffS ≤ coeffT := by
      dsimp only [coeffS, coeffT]
      exact mul_le_mul_of_nonneg_left hedgeMono hcoeff0
    have hpow0 : 0 ≤ N ^ (1 - c - shiftS) :=
      Real.rpow_nonneg hN0.le _
    have hcoeffS0 : 0 ≤ coeffS := by
      dsimp only [coeffS]
      exact mul_nonneg hcoeff0 hedge0
    have hcoeffT0 : 0 ≤ coeffT := hcoeffS0.trans hcoeffMono
    have hcombined : coeffS * N ^ (1 - c - shiftS) ≤
        coeffT * N ^ (1 - c - shiftT) := by
      calc
        coeffS * N ^ (1 - c - shiftS) ≤
            coeffT * N ^ (1 - c - shiftS) :=
          mul_le_mul_of_nonneg_right hcoeffMono hpow0
        _ ≤ coeffT * N ^ (1 - c - shiftT) :=
          mul_le_mul_of_nonneg_left hpow hcoeffT0
    calc
      ‖heathBrownBoxFactorValue L X k box
          ((c : ℂ) + (lam r : ℝ) * Complex.I) j‖ ≤
          coeffS * N ^ (1 - c - shiftS) := hraw'
      _ ≤ coeffT * N ^ (1 - c - shiftT) := hcombined
      _ = Edge / Tsave * N ^ (1 - c) := by
        dsimp only [coeffT, shiftT, tFreq, Edge, Tsave]
        rw [Real.rpow_sub hN0]
        ring
  have hcount := derivativeExcised_montgomery_heathBrownBox_fixedPolylog
    box j hc hsep hH hgap hband hD hN0 hTsave hEdge hpoint hlarge
  simpa only [N, Edge, Tsave] using hcount

end RHTower.Sieve
