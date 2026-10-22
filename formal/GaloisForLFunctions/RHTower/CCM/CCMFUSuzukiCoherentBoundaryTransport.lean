import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiGammaBinetCofinalBridge
import GaloisForLFunctions.RHTower.Suzuki.SuzukiPrimeOutgoingDilationFlux
import GaloisForLFunctions.RHTower.XiMassCriticalDiscreteRemainder
import GaloisForLFunctions.RHTower.CriticalPrimeSourceSchattenIdeal

/-!
# Coefficient-faithful Suzuki boundary transport

Suzuki's normalized signed prime--polar--Gamma curvature is an incoming, strict-causal readout;
the unit-Riesz coherent charge is an outgoing readout.  These are not interchangeable at a finite
aperture: the outgoing weight of the new endpoint atom is zero, whereas the completed Chebyshev
cumulative source contains that atom.

This module proves the exact correction law.  At aperture `X = N + 3`, outgoing minus incoming,
plus the missing endpoint coefficient `Λ(X) / √X`, is exactly the normalized completed Chebyshev
error.  Combining this with the Gamma--Binet curvature landing gives an exact finite transport law
and a cofinal law in which the archimedean renormalization and endpoint atom vanish.  Thus the
normalized Chebyshev error is the surviving cross-boundary defect; no positivity, PNT estimate,
zero-location statement, or RH hypothesis is used.
-/

open Filter MeasureTheory Set Topology

noncomputable section

namespace RHTower

open ArithmeticFunction Finset
open GaloisForLFunctions.RHTower

/-- Exact causal boundary jump.  The endpoint term is forced because the outgoing endpoint atom
has zero weight while `chebyshevPsi` includes it. -/
theorem unitRieszCoherentBoundaryJump_eq_normalizedChebyshevError (N : ℕ) :
    unitRieszCoherentCompletedOutgoingCharge (N + 3) -
        unitRieszCompletedCoherentBarycenter (N + 3) 0 +
        ArithmeticFunction.vonMangoldt (N + 3) /
          Real.sqrt (((N + 3 : ℕ) : ℝ)) =
      criticalMellinNormalizedChebyshevError
        (Real.log (((N + 3 : ℕ) : ℝ))) := by
  have hN1 : 1 ≤ N + 1 := by omega
  have hXpos : (0 : ℝ) < ((N + 3 : ℕ) : ℝ) := by positivity
  have hsqrtX : Real.sqrt (((N + 3 : ℕ) : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.2 hXpos).ne'
  have hcenter :=
    unitRieszCompletedCoherentBarycenter_eq_incoming_weightedPrefix (N + 1) 0
  simp only [NNReal.coe_zero, neg_zero, Real.exp_zero, zero_div, one_div] at hcenter
  have hprefix := unitRieszSqrtWeightedPrimePrefix_zero hN1
  rw [hprefix] at hcenter
  have hout := unitRieszCoherentPrimeOutgoingCharge_eq_dilation_normalForm (N + 3)
  have hsplit :
      (∑ k ∈ Finset.Icc 2 (N + 3),
          ArithmeticFunction.vonMangoldt k *
            (1 / Real.sqrt (((N + 3 : ℕ) : ℝ)) -
              Real.sqrt (k : ℝ) / ((N + 3 : ℕ) : ℝ))) =
        (∑ k ∈ Finset.Ico 2 (N + 3),
          ArithmeticFunction.vonMangoldt k *
            (1 / Real.sqrt (((N + 3 : ℕ) : ℝ)) -
              Real.sqrt (k : ℝ) / ((N + 3 : ℕ) : ℝ))) := by
    rw [show Finset.Ico 2 (N + 3) = Finset.Icc 2 (N + 2) by
      ext k
      simp
      omega]
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ N + 3)]
    have hsqrtSq : Real.sqrt (((N + 3 : ℕ) : ℝ)) ^ 2 =
        ((N + 3 : ℕ) : ℝ) := Real.sq_sqrt hXpos.le
    have hend :
        ArithmeticFunction.vonMangoldt (N + 3) *
            (1 / Real.sqrt (((N + 3 : ℕ) : ℝ)) -
              Real.sqrt (((N + 3 : ℕ) : ℝ)) / ((N + 3 : ℕ) : ℝ)) = 0 := by
      field_simp [hsqrtX]
      rw [hsqrtSq]
      ring
    rw [hend, add_zero]
  rw [unitRieszCoherentCompletedOutgoingCharge,
    unitRieszCoherentPolarOutgoingCharge_eq, hout, hsplit, hcenter]
  have hsumExpand :
      (∑ k ∈ Finset.Ico 2 (N + 3),
          ArithmeticFunction.vonMangoldt k *
            (1 / Real.sqrt (((N + 3 : ℕ) : ℝ)) -
              Real.sqrt (k : ℝ) / ((N + 3 : ℕ) : ℝ))) =
        (∑ k ∈ Finset.Ico 2 (N + 3),
            ArithmeticFunction.vonMangoldt k) /
              Real.sqrt (((N + 3 : ℕ) : ℝ)) -
          (∑ k ∈ Finset.Ico 2 (N + 3),
            ArithmeticFunction.vonMangoldt k * Real.sqrt (k : ℝ)) /
              ((N + 3 : ℕ) : ℝ) := by
    calc
      _ = ∑ k ∈ Finset.Ico 2 (N + 3),
          (ArithmeticFunction.vonMangoldt k /
              Real.sqrt (((N + 3 : ℕ) : ℝ)) -
            (ArithmeticFunction.vonMangoldt k * Real.sqrt (k : ℝ)) /
              ((N + 3 : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_div]
  rw [hsumExpand]
  have hpsi :
      (∑ k ∈ Finset.Ico 2 (N + 3), ArithmeticFunction.vonMangoldt k) +
          ArithmeticFunction.vonMangoldt (N + 3) = chebyshevPsi (N + 3) := by
    rw [show Finset.Ico 2 (N + 3) = Finset.Icc 2 (N + 2) by
      ext k
      simp
      omega]
    rw [← Finset.sum_Icc_succ_top (by omega : 2 ≤ N + 3)]
    change (∑ k ∈ Finset.Icc 2 (N + 3), ArithmeticFunction.vonMangoldt k) =
      ∑ k ∈ Finset.Icc 1 (N + 3), ArithmeticFunction.vonMangoldt k
    rw [show Finset.Icc 1 (N + 3) = insert 1 (Finset.Icc 2 (N + 3)) by
      ext k
      simp
      omega]
    simp [ArithmeticFunction.vonMangoldt_apply_one]
  have herr := criticalMellinNormalizedChebyshevError_eq_discrete_add_floor
    (Real.log (((N + 3 : ℕ) : ℝ)))
  rw [Real.exp_log hXpos, Nat.floor_natCast] at herr
  simp only [sub_self, mul_zero, add_zero] at herr
  have hexp :
      Real.exp (-Real.log (((N + 3 : ℕ) : ℝ)) / 2) =
        1 / Real.sqrt (((N + 3 : ℕ) : ℝ)) := by
    have hsqrt :
        Real.sqrt (((N + 3 : ℕ) : ℝ)) =
          Real.exp (Real.log (((N + 3 : ℕ) : ℝ)) / 2) := by
      symm
      rw [← Real.log_sqrt hXpos.le,
        Real.exp_log (Real.sqrt_pos.mpr hXpos)]
    rw [hsqrt, one_div, ← Real.exp_neg]
    congr 1
    ring
  rw [hexp, psiRemainder, div_eq_mul_inv] at herr
  rw [herr, ← hpsi]
  field_simp [hsqrtX]
  norm_num [Nat.add_assoc] at hcenter ⊢
  have hsqrtSq : Real.sqrt ((N : ℝ) + 3) ^ 2 = (N : ℝ) + 3 :=
    Real.sq_sqrt (by positivity)
  nlinarith [hsqrtSq]

/-- Exact finite transport of the literal prime--polar--Gamma curvature into the outgoing
unit-Riesz charge.  The two extra terms are respectively source-free arch renormalization and the
coefficient-faithful arithmetic boundary defect. -/
theorem unitRieszCoherentOutgoingCharge_eq_primePolarGammaCurvature_add_boundaryDefect
    (N : ℕ) :
    unitRieszCoherentCompletedOutgoingCharge (N + 3) =
      ccmSuzukiWeightedPrimePolarGammaCurvaturePrefix (N + 1) /
          ((N + 3 : ℕ) : ℝ) +
        suzukiCheckpointWeightedArchRenormalization (N + 1) /
          ((N + 3 : ℕ) : ℝ) +
        criticalMellinNormalizedChebyshevError
          (Real.log (((N + 3 : ℕ) : ℝ))) -
        ArithmeticFunction.vonMangoldt (N + 3) /
          Real.sqrt (((N + 3 : ℕ) : ℝ)) := by
  have hN1 : 1 ≤ N + 1 := by omega
  have hbridge :=
    unitRiesz_center_eq_weightedPrimePolarGammaCurvature_add_arch
      (N := N + 1) hN1
  have hjump := unitRieszCoherentBoundaryJump_eq_normalizedChebyshevError N
  norm_num [Nat.add_assoc] at hbridge hjump ⊢
  have hcenter :
      unitRieszCompletedCoherentBarycenter (N + 3) 0 =
        ccmSuzukiWeightedPrimePolarGammaCurvaturePrefix (N + 1) /
            ((N : ℝ) + 3) +
          suzukiCheckpointWeightedArchRenormalization (N + 1) /
            ((N : ℝ) + 3) := by
    field_simp [show (N : ℝ) + 3 ≠ 0 by positivity]
    simpa only [mul_comm] using hbridge
  rw [hcenter] at hjump
  linarith

/-- Cofinal coefficient-faithful boundary transport.  After the source-free arch term and the
single endpoint atom vanish, outgoing charge minus normalized prime--polar--Gamma curvature is
exactly the normalized completed Chebyshev error. -/
theorem tendsto_unitRieszOutgoing_sub_primePolarGammaCurvature_sub_normalizedChebyshevError_zero :
    Tendsto (fun N : ℕ =>
      unitRieszCoherentCompletedOutgoingCharge (N + 3) -
        ccmSuzukiWeightedPrimePolarGammaCurvaturePrefix (N + 1) /
          ((N + 3 : ℕ) : ℝ) -
        criticalMellinNormalizedChebyshevError
          (Real.log (((N + 3 : ℕ) : ℝ))))
      atTop (nhds 0) := by
  have harch :=
    tendsto_suzukiCheckpointWeightedArchRenormalization_div_zero.comp
      (Filter.tendsto_add_atTop_nat 1)
  have harch' :
      Tendsto (fun N : ℕ =>
        suzukiCheckpointWeightedArchRenormalization (N + 1) /
          ((N + 3 : ℕ) : ℝ)) atTop (nhds 0) := by
    apply harch.congr'
    exact Eventually.of_forall fun N => by
      change suzukiCheckpointWeightedArchRenormalization (N + 1) /
          (((N + 1 + 2 : ℕ) : ℝ)) =
        suzukiCheckpointWeightedArchRenormalization (N + 1) /
          (((N + 3 : ℕ) : ℝ))
      congr 2
  have hrpow :=
    (tendsto_vonMangoldt_rpow_atTop (σ := (1 / 2 : ℝ)) (by norm_num)).comp
      (Filter.tendsto_add_atTop_nat 3)
  have hendpoint :
      Tendsto (fun N : ℕ =>
        ArithmeticFunction.vonMangoldt (N + 3) /
          Real.sqrt (((N + 3 : ℕ) : ℝ))) atTop (nhds 0) := by
    apply hrpow.congr'
    exact Eventually.of_forall fun N => by
      have hX : (0 : ℝ) < ((N + 3 : ℕ) : ℝ) := by positivity
      change ArithmeticFunction.vonMangoldt (N + 3) *
          (((N + 3 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) =
        ArithmeticFunction.vonMangoldt (N + 3) /
          Real.sqrt (((N + 3 : ℕ) : ℝ))
      rw [div_eq_mul_inv, Real.rpow_neg hX.le, Real.sqrt_eq_rpow]
      simp only [div_eq_mul_inv, Nat.cast_add, Nat.cast_ofNat, one_mul]
  have hdiff := harch'.sub hendpoint
  simpa only [sub_zero] using hdiff.congr' (Eventually.of_forall fun N => by
    rw [unitRieszCoherentOutgoingCharge_eq_primePolarGammaCurvature_add_boundaryDefect N]
    ring)

/-- Cofinal transport is coefficient-faithful in both directions: outgoing charge minus normalized
prime--polar--Gamma curvature has a limit exactly when normalized completed Chebyshev error has the
same limit. -/
theorem tendsto_unitRieszOutgoing_sub_primePolarGammaCurvature_iff_normalizedChebyshevError
    (L : ℝ) :
    Tendsto (fun N : ℕ =>
      unitRieszCoherentCompletedOutgoingCharge (N + 3) -
        ccmSuzukiWeightedPrimePolarGammaCurvaturePrefix (N + 1) /
          ((N + 3 : ℕ) : ℝ)) atTop (nhds L) ↔
      Tendsto (fun N : ℕ =>
        criticalMellinNormalizedChebyshevError
          (Real.log (((N + 3 : ℕ) : ℝ)))) atTop (nhds L) := by
  have hdiff :=
    tendsto_unitRieszOutgoing_sub_primePolarGammaCurvature_sub_normalizedChebyshevError_zero
  constructor
  · intro hout
    have h := hout.sub hdiff
    simpa only [sub_zero] using h.congr' (Eventually.of_forall fun N => by ring)
  · intro herr
    have h := hdiff.add herr
    simpa only [zero_add] using h.congr' (Eventually.of_forall fun N => by ring)

end RHTower
