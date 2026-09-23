import GaloisForLFunctions.RHTower.TwoLocalAnchorTransversePseudodeterminantLaw

/-!
# Adaptive-anchor pseudodeterminant law for one static local draw

Return removal needs target-dependent first-hit anchors, while Gaussian
anti-concentration needs a fixed linear commutator observer.  These demands
are compatible.  An arbitrary anchor changes the longitudinal return factor
but leaves the physical commutator action unchanged.  Consequently trace-far
targets may retain arbitrary first-hit anchors and pay the transverse
pseudodeterminant alone; only targets near projective scalar recurrence must
use the common zero anchor.

The resulting trace-safe anchor selector is automatic.  For one ordinary
two-local Gaussian perturbation it gives a complete weighted-image bound with
one uniform rate, retaining return-sheet removal without a target count,
minimum spectral gap, or nonlinear Gaussian observer.
-/

open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator
open Matrix Set MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

noncomputable section

namespace RHTower

set_option maxHeartbeats 800000 in
theorem twoLocalPauli_gaussianLaplaceProduct_le_exp_harmonicRate_mul_traceDeficit
    {n : ℕ} (hn : 2 ≤ n)
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    {r : ℕ} (hr : 0 < r) {scale B : ℝ}
    (hscale : scale ≠ 0) (hB : 0 < B) :
    (∏ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
        (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.sqrt (Real.pi /
            (((r : ℝ) *
                (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ)⁻¹ *
                scale ^ (2 : ℕ) / B ^ (2 : ℕ)) *
              (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ (2 : ℕ) +
              1 / 2))) ≤
      Real.exp (-(twoLocalAnchorTransverseHarmonicRate n r scale B *
        RHTower.unitaryProjectiveTraceDeficit U)) := by
  let D : ℝ := (2 : ℝ) ^ n
  let a2 : ℝ := ‖Matrix.trace
      (U : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) / D ^ (2 : ℕ)
  let b : ℝ := 1 - a2
  let tau : ℝ := (r : ℝ) * D⁻¹ * scale ^ (2 : ℕ) / B ^ (2 : ℕ)
  let S : ℝ := ∑ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
    (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ (2 : ℕ)
  let Q : ℝ := ∑ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
    (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ (4 : ℕ)
  let A := twoLocalAnchorTransverseActivationRate n r scale B
  let K := twoLocalAnchorTransverseStableRate n
  let q := twoLocalAnchorTransverseHarmonicRate n r scale B
  have hD : 0 < D := by positivity
  have htau : 0 < tau := by
    dsimp [tau]
    positivity
  have htrace : ‖Matrix.trace
      (U : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) ≤ D ^ (2 : ℕ) := by
    have h := finiteUnitary_trace_normSq_le_card_sq U
    simpa [Complex.sq_norm, D] using h
  have hb0 : 0 ≤ b := by
    dsimp [b, a2]
    have := (div_le_one (sq_pos_of_pos hD)).2 htrace
    linarith
  have hA : 0 < A := by
    dsimp [A, twoLocalAnchorTransverseActivationRate]
    have hn1 : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hn
    positivity
  have hK : 0 < K := by
    dsimp [K, twoLocalAnchorTransverseStableRate]
    exact_mod_cast (show 0 < 6 * n - 4 by omega)
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    exact Finset.sum_nonneg fun i _ => by positivity
  have hSfloor : 4 * ((n - 1 : ℕ) : ℝ) * D * b ≤ S := by
    simpa [S, D, b, a2] using
      sum_sq_twoLocalPauliUnitaryCommutator_singularValues_ge_traceDeficit U
  have hRfloor : K * b ≤ S ^ (2 : ℕ) / Q := by
    simpa [K, twoLocalAnchorTransverseStableRate, S, Q, b, a2, D,
      twoLocalPauliUnitaryCommutatorGramStableRatio] using
      twoLocalPauliUnitaryCommutatorGramStableRatio_ge_sixNSubFour_normalizedTraceDeficit U
  have hprodTotal := gaussianLaplaceProduct_le_exp_stableRatio_total
    (fun i : Fin (Fintype.card (PauliTracelessLabel n 2)) =>
      (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ (2 : ℕ))
    (fun i => sq_nonneg _) htau
  by_cases hb : b = 0
  · have hfrac0 : 0 ≤ (tau * S ^ (2 : ℕ)) / (tau * Q + S) :=
      div_nonneg (mul_nonneg htau.le (sq_nonneg S))
        (add_nonneg (mul_nonneg htau.le hQ0) hS0)
    calc
      (∏ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
          (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.sqrt (Real.pi /
              (((r : ℝ) *
                  (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ)⁻¹ *
                  scale ^ (2 : ℕ) / B ^ (2 : ℕ)) *
                (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ (2 : ℕ) +
                1 / 2))) =
          ∏ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
            (Real.sqrt (2 * Real.pi))⁻¹ *
              Real.sqrt (Real.pi /
                (tau * (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ (2 : ℕ) +
                  1 / 2)) := by simp [tau, D]
      _ ≤ Real.exp (-((tau * S ^ (2 : ℕ)) / (tau * Q + S))) := by
        simpa only [S, Q, ← pow_mul, Nat.reduceMul] using hprodTotal
      _ ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hfrac0)
      _ = Real.exp (-(q * b)) := by rw [hb]; simp
      _ = _ := by
        simp [q, b, a2, D, RHTower.unitaryProjectiveTraceDeficit]

  · have hbpos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
    have hS : 0 < S := by
      have : 0 < 4 * ((n - 1 : ℕ) : ℝ) * D * b := by
        have hn1 : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hn
        positivity
      exact this.trans_le hSfloor
    have hRpos : 0 < S ^ (2 : ℕ) / Q := (mul_pos hK hbpos).trans_le hRfloor
    have hQ : 0 < Q := by
      rcases hQ0.eq_or_lt with hQzero | hQpos
      · rw [← hQzero, div_zero] at hRpos
        exact (lt_irrefl 0 hRpos).elim
      · exact hQpos
    have htauS : A * b ≤ tau * S := by
      have hmul := mul_le_mul_of_nonneg_left hSfloor htau.le
      calc
        A * b = tau * (4 * ((n - 1 : ℕ) : ℝ) * D * b) := by
          dsimp [A, twoLocalAnchorTransverseActivationRate, tau, D]
          field_simp [ne_of_gt hD, ne_of_gt hB]
        _ ≤ tau * S := hmul
    have hharmonic : q * b ≤
        (tau * S) * (S ^ (2 : ℕ) / Q) / (tau * S + S ^ (2 : ℕ) / Q) := by
      simpa [q, twoLocalAnchorTransverseHarmonicRate, A, K] using
        harmonic_mean_lower_of_linear_floors hA hK hbpos htauS hRfloor
    have hprod := gaussianLaplaceProduct_le_exp_activationStableHarmonicMean
      (fun i : Fin (Fintype.card (PauliTracelessLabel n 2)) =>
        (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ (2 : ℕ))
      (fun i => sq_nonneg _) htau hS (by
        simpa only [Q, ← pow_mul, Nat.reduceMul] using hQ)
    calc
      (∏ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
          (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.sqrt (Real.pi /
              (((r : ℝ) *
                  (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ)⁻¹ *
                  scale ^ (2 : ℕ) / B ^ (2 : ℕ)) *
                (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ (2 : ℕ) +
                1 / 2))) =
          ∏ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
            (Real.sqrt (2 * Real.pi))⁻¹ *
              Real.sqrt (Real.pi /
                (tau * (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ (2 : ℕ) +
                  1 / 2)) := by simp [tau, D]
      _ ≤ Real.exp (-((tau * S) * (S ^ (2 : ℕ) / Q) /
          (tau * S + S ^ (2 : ℕ) / Q))) := by
        simpa only [S, Q, ← pow_mul, Nat.reduceMul] using hprod
      _ ≤ Real.exp (-(q * b)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by
        simp [q, b, a2, D, RHTower.unitaryProjectiveTraceDeficit]

theorem twoLocalPauliPencil_gaussianLaplaceProduct_le_exp_harmonicRate_mul_traceDeficit
    {n : ℕ} (hn : 2 ≤ n)
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    {r : ℕ} (hr : 0 < r) {scale B : ℝ}
    (hscale : scale ≠ 0) (hB : 0 < B) :
    (∏ i : Fin (Module.finrank ℝ (TwoLocalPauliCoefficientSpace n)),
        (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.sqrt (Real.pi /
            (((r : ℝ) *
                (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ)⁻¹ *
                scale ^ (2 : ℕ) / B ^ (2 : ℕ)) *
              ((twoLocalPauliGaussianHermitianPencil n).commutatorMap U).singularValues i ^ (2 : ℕ) +
              1 / 2))) ≤
      Real.exp (-(twoLocalAnchorTransverseHarmonicRate n r scale B *
        RHTower.unitaryProjectiveTraceDeficit U)) := by
  rw [twoLocalPauliGaussianHermitianPencil_commutatorMap]
  rw [show Module.finrank ℝ (TwoLocalPauliCoefficientSpace n) =
      Fintype.card (PauliTracelessLabel n 2) from finrank_euclideanSpace]
  exact twoLocalPauli_gaussianLaplaceProduct_le_exp_harmonicRate_mul_traceDeficit
    hn U hr hscale hB

/-- Zero anchors retain return suppression; nonzero anchors pay the transverse
pseudodeterminant alone. -/
def adaptiveAnchorGaussianPrefactor
    {ι C : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℕ) (U : C → Matrix.unitaryGroup ι ℂ)
    (anchor : C → ℝ) (c : C) : ℝ :=
  if anchor c = 0 then
    Real.exp (-(r : ℝ) *
      (‖Matrix.trace (U c : Matrix ι ι ℂ)‖ / Fintype.card ι) ^ (2 : ℕ))
  else 1

/-- Raw first-hit anchors are retained only off the projective scalar sector. -/
def traceSafeCircuitAnchor
    {n : ℕ} {C : Type*} (β : ℝ)
    (U : C → Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (rawAnchor : C → ℝ) (c : C) : ℝ :=
  if β ≤ RHTower.unitaryProjectiveTraceDeficit (U c) then rawAnchor c else 0

def twoLocalAdaptiveAnchorUniformRate
    (n r : ℕ) (scale B β : ℝ) : ℝ :=
  min (twoLocalAnchorTransverseUniformRate n r scale B)
    (twoLocalAnchorTransverseHarmonicRate n r scale B * β)

theorem weighted_twoLocalPauliPencil_traceSafeAnchor_mul_gaussianLaplaceProduct_le_exp_uniformRate
    {n : ℕ} (hn : 2 ≤ n)
    {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (rawAnchor : C → ℝ) (β : ℝ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    {r : ℕ} (hr : 0 < r) {scale B : ℝ}
    (hscale : scale ≠ 0) (hB : 0 < B) :
    (∑ c, w c * adaptiveAnchorGaussianPrefactor r U
        (traceSafeCircuitAnchor β U rawAnchor) c *
      ∏ i : Fin (Module.finrank ℝ (TwoLocalPauliCoefficientSpace n)),
        (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.sqrt (Real.pi /
            (((r : ℝ) *
                (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ)⁻¹ *
                scale ^ (2 : ℕ) / B ^ (2 : ℕ)) *
              ((twoLocalPauliGaussianHermitianPencil n).commutatorMap
                  (U c)).singularValues i ^ (2 : ℕ) +
              1 / 2))) ≤
      Real.exp (-twoLocalAdaptiveAnchorUniformRate n r scale B β) := by
  calc
    _ ≤ ∑ c, w c * Real.exp
        (-twoLocalAdaptiveAnchorUniformRate n r scale B β) := by
      apply Finset.sum_le_sum
      intro c _
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (hw.1 c)
      by_cases ha : traceSafeCircuitAnchor β U rawAnchor c = 0
      · have hzero :=
          twoLocalPauliPencil_anchor_mul_gaussianLaplaceProduct_le_exp_uniformRate
            hn (U c) hr hscale hB
        have hrate : twoLocalAdaptiveAnchorUniformRate n r scale B β ≤
            twoLocalAnchorTransverseUniformRate n r scale B := min_le_left _ _
        calc
          adaptiveAnchorGaussianPrefactor r U
                (traceSafeCircuitAnchor β U rawAnchor) c *
              ∏ i : Fin (Module.finrank ℝ (TwoLocalPauliCoefficientSpace n)),
                (Real.sqrt (2 * Real.pi))⁻¹ *
                  Real.sqrt (Real.pi /
                    (((r : ℝ) *
                        (Fintype.card
                          (FiniteQubitConfiguration (Fin n)) : ℝ)⁻¹ *
                        scale ^ (2 : ℕ) / B ^ (2 : ℕ)) *
                      ((twoLocalPauliGaussianHermitianPencil n).commutatorMap
                          (U c)).singularValues i ^ (2 : ℕ) + 1 / 2)) =
              Real.exp (-(r : ℝ) *
                  (‖Matrix.trace
                    (U c : Matrix (FiniteQubitConfiguration (Fin n))
                      (FiniteQubitConfiguration (Fin n)) ℂ)‖ /
                    Fintype.card (FiniteQubitConfiguration (Fin n))) ^ (2 : ℕ)) *
                ∏ i : Fin (Module.finrank ℝ (TwoLocalPauliCoefficientSpace n)),
                  (Real.sqrt (2 * Real.pi))⁻¹ *
                    Real.sqrt (Real.pi /
                      (((r : ℝ) *
                          (Fintype.card
                            (FiniteQubitConfiguration (Fin n)) : ℝ)⁻¹ *
                          scale ^ (2 : ℕ) / B ^ (2 : ℕ)) *
                        ((twoLocalPauliGaussianHermitianPencil n).commutatorMap
                            (U c)).singularValues i ^ (2 : ℕ) + 1 / 2)) := by
                simp [adaptiveAnchorGaussianPrefactor, ha]
          _ ≤ Real.exp (-twoLocalAnchorTransverseUniformRate n r scale B) := hzero
          _ ≤ Real.exp (-twoLocalAdaptiveAnchorUniformRate n r scale B β) :=
            Real.exp_le_exp.mpr (by linarith)
      · have hfar : β ≤ RHTower.unitaryProjectiveTraceDeficit (U c) := by
          unfold traceSafeCircuitAnchor at ha
          by_contra hnot
          rw [if_neg hnot] at ha
          exact ha rfl
        have hprod :=
          twoLocalPauliPencil_gaussianLaplaceProduct_le_exp_harmonicRate_mul_traceDeficit
            hn (U c) hr hscale hB
        have hq0 : 0 ≤ twoLocalAnchorTransverseHarmonicRate n r scale B := by
          dsimp [twoLocalAnchorTransverseHarmonicRate,
            twoLocalAnchorTransverseActivationRate,
            twoLocalAnchorTransverseStableRate]
          positivity
        have hrate : twoLocalAdaptiveAnchorUniformRate n r scale B β ≤
            twoLocalAnchorTransverseHarmonicRate n r scale B *
              RHTower.unitaryProjectiveTraceDeficit (U c) :=
          (min_le_right _ _).trans
            (mul_le_mul_of_nonneg_left hfar hq0)
        calc
          adaptiveAnchorGaussianPrefactor r U
                (traceSafeCircuitAnchor β U rawAnchor) c *
              ∏ i : Fin (Module.finrank ℝ (TwoLocalPauliCoefficientSpace n)),
                (Real.sqrt (2 * Real.pi))⁻¹ *
                  Real.sqrt (Real.pi /
                    (((r : ℝ) *
                        (Fintype.card
                          (FiniteQubitConfiguration (Fin n)) : ℝ)⁻¹ *
                        scale ^ (2 : ℕ) / B ^ (2 : ℕ)) *
                      ((twoLocalPauliGaussianHermitianPencil n).commutatorMap
                          (U c)).singularValues i ^ (2 : ℕ) + 1 / 2)) =
              ∏ i : Fin (Module.finrank ℝ (TwoLocalPauliCoefficientSpace n)),
                (Real.sqrt (2 * Real.pi))⁻¹ *
                  Real.sqrt (Real.pi /
                    (((r : ℝ) *
                        (Fintype.card
                          (FiniteQubitConfiguration (Fin n)) : ℝ)⁻¹ *
                        scale ^ (2 : ℕ) / B ^ (2 : ℕ)) *
                      ((twoLocalPauliGaussianHermitianPencil n).commutatorMap
                          (U c)).singularValues i ^ (2 : ℕ) + 1 / 2)) := by
                simp [adaptiveAnchorGaussianPrefactor, ha]
          _ ≤ Real.exp (-(twoLocalAnchorTransverseHarmonicRate n r scale B *
              RHTower.unitaryProjectiveTraceDeficit (U c))) := hprod
          _ ≤ Real.exp (-twoLocalAdaptiveAnchorUniformRate n r scale B β) :=
            Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [← Finset.sum_mul, hw.2, one_mul]

theorem directStaticChoiTargetNearActionMass_arbitraryAnchorResidual_hermitianSpectralEndpoint_le_exp_action_of_scale
    {d : ℕ} (hd : 0 < d)
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (anchor : ℝ)
    (r : ℕ) (δ B : ℝ)
    (hscale : staticChoiOscillationScale hH.eigenvalues ≤ B)
    (hB : 0 < B) :
    directStaticChoiTargetNearActionMass
        (staticChoiAnchorResidual hH.eigenvalues anchor
          (GaloisForLFunctions.RHTower.choiVector
            (hermitianSpectralEndpoint hH U : Matrix (Fin d) (Fin d) ℂ)))
        hH.eigenvalues r δ ≤
      Real.exp (-(((r : ℝ) * (d : ℝ)⁻¹ / B ^ (2 : ℕ)) *
        finiteMatrixHilbertSchmidtEnergy
          (H * (U : Matrix (Fin d) (Fin d) ℂ) -
            (U : Matrix (Fin d) (Fin d) ℂ) * H))) := by
  have hraw :=
    directStaticChoiTargetNearActionMass_anchorResidual_choiVector_le_exp_jointDefect
      hd hH.eigenvalues anchor (hermitianSpectralEndpoint hH U).2 r δ
  rw [normalizedSpectralCommutatorEnergy_hermitianSpectralEndpoint hd hH U] at hraw
  refine hraw.trans (Real.exp_le_exp.mpr ?_)
  have hspos : 0 < staticChoiOscillationScale hH.eigenvalues :=
    staticChoiOscillationScale_pos hH.eigenvalues
  have hsq : staticChoiOscillationScale hH.eigenvalues ^ (2 : ℕ) ≤ B ^ (2 : ℕ) :=
    (sq_le_sq₀ hspos.le hB.le).2 hscale
  have hinv : (B ^ (2 : ℕ))⁻¹ ≤
      (staticChoiOscillationScale hH.eigenvalues ^ (2 : ℕ))⁻¹ :=
    (inv_le_inv₀ (sq_pos_of_pos hB) (sq_pos_of_pos hspos)).2 hsq
  let E := finiteMatrixHilbertSchmidtEnergy
    (H * (U : Matrix (Fin d) (Fin d) ℂ) -
      (U : Matrix (Fin d) (Fin d) ℂ) * H)
  have hE : 0 ≤ E := finiteMatrixHilbertSchmidtEnergy_nonneg _
  have hcoef := mul_le_mul_of_nonneg_left hinv
    (mul_nonneg (Nat.cast_nonneg r)
      (inv_nonneg.mpr (Nat.cast_nonneg d)))
  have hfull := mul_le_mul_of_nonneg_right hcoef hE
  have hanchor : 0 ≤ ‖staticChoiAnchorComponent hH.eigenvalues anchor
      (GaloisForLFunctions.RHTower.choiVector
        (hermitianSpectralEndpoint hH U : Matrix (Fin d) (Fin d) ℂ))‖ ^ (2 : ℕ) :=
    sq_nonneg _
  calc
    -(r : ℝ) *
        (‖staticChoiAnchorComponent hH.eigenvalues anchor
            (GaloisForLFunctions.RHTower.choiVector
              (hermitianSpectralEndpoint hH U : Matrix (Fin d) (Fin d) ℂ))‖ ^ (2 : ℕ) +
          (d : ℝ)⁻¹ * E /
            staticChoiOscillationScale hH.eigenvalues ^ (2 : ℕ)) ≤
        -(((r : ℝ) * (d : ℝ)⁻¹) *
          (staticChoiOscillationScale hH.eigenvalues ^ (2 : ℕ))⁻¹ * E) := by
      have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
      rw [div_eq_mul_inv]
      nlinarith [mul_nonneg hr0 hanchor]
    _ ≤ -(((r : ℝ) * (d : ℝ)⁻¹) * (B ^ (2 : ℕ))⁻¹ * E) := by
      linarith
    _ = -(((r : ℝ) * (d : ℝ)⁻¹ / B ^ (2 : ℕ)) * E) := by ring

variable {E ι : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem FiniteGaussianHermitianPencil.affineArbitraryAnchorResidualNearAction_le_exp_action_of_scale
    [Nonempty ι]
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian) (x : E)
    (U : Matrix.unitaryGroup ι ℂ) (anchor : ℝ)
    (r : ℕ) (δ B : ℝ)
    (hscale : staticChoiOscillationScale
      (P.affineSpectralEnergy hH₀ x) ≤ B)
    (hB : 0 < B) :
    directStaticChoiTargetNearActionMass
        (staticChoiAnchorResidual (P.affineSpectralEnergy hH₀ x) anchor
          (GaloisForLFunctions.RHTower.choiVector
            (P.affineSpectralEndpoint hH₀ x U :
              Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ)))
        (P.affineSpectralEnergy hH₀ x) r δ ≤
      Real.exp (-(((r : ℝ) * (Fintype.card ι : ℝ)⁻¹ / B ^ (2 : ℕ)) *
        ‖P.commutatorMap U x - hermitianPencilCommutatorDrift H₀ U‖ ^ (2 : ℕ))) := by
  let Ufin := finiteGaussianHermitianPencilReindexedEndpoint U
  have h :=
    directStaticChoiTargetNearActionMass_arbitraryAnchorResidual_hermitianSpectralEndpoint_le_exp_action_of_scale
      (d := Fintype.card ι) Fintype.card_pos
      (P.affineReindexedHamiltonian_isHermitian hH₀ x) Ufin anchor r δ B hscale hB
  rw [P.affineReindexedCommutatorEnergy H₀ x U] at h
  exact h

omit [FiniteDimensional ℝ E] in
theorem FiniteGaussianHermitianPencil.scaledAffineArbitraryAnchorResidualNearAction_le_exp_action_of_scale
    [Nonempty ι]
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian)
    {scale : ℝ} (hscale : scale ≠ 0) (x : E)
    (U : Matrix.unitaryGroup ι ℂ) (anchor : ℝ)
    (r : ℕ) (δ B : ℝ)
    (hosc : staticChoiOscillationScale
      (P.scaledAffineSpectralEnergy hH₀ scale x) ≤ B)
    (hB : 0 < B) :
    directStaticChoiTargetNearActionMass
        (staticChoiAnchorResidual
          (P.scaledAffineSpectralEnergy hH₀ scale x) anchor
          (GaloisForLFunctions.RHTower.choiVector
            (P.scaledAffineSpectralEndpoint hH₀ scale x U :
              Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ)))
        (P.scaledAffineSpectralEnergy hH₀ scale x) r δ ≤
      Real.exp (-(((r : ℝ) * (Fintype.card ι : ℝ)⁻¹ * scale ^ (2 : ℕ) / B ^ (2 : ℕ)) *
        ‖P.commutatorMap U x -
          scaledHermitianPencilCommutatorDrift scale H₀ U‖ ^ (2 : ℕ))) := by
  have h := P.affineArbitraryAnchorResidualNearAction_le_exp_action_of_scale
    hH₀ (scale • x) U anchor r δ B hosc hB
  rw [P.scaledAffineCommutatorEnergy hscale H₀ x U] at h
  exact h.trans_eq (by
    congr 1
    congr 1
    ring)

theorem FiniteGaussianHermitianPencil.stdGaussian_measure_weightedScaledAffineAdaptiveAnchorResidualNearAction_on_scaleSet_ge_le
    [Nonempty ι] [MeasurableSpace E] [BorelSpace E]
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian)
    {scale : ℝ} (hscale : scale ≠ 0)
    {C : Type*} [Fintype C]
    (G : Set E) (U : C → Matrix.unitaryGroup ι ℂ)
    (anchor : C → ℝ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (r : ℕ) (δ B : ℝ)
    (hosc : ∀ x ∈ G, staticChoiOscillationScale
      (P.scaledAffineSpectralEnergy hH₀ scale x) ≤ B)
    (hB : 0 < B) (n : ℕ) (hn : Module.finrank ℝ E = n)
    {κ : ℝ} (hκ : 0 < κ) :
    (ProbabilityTheory.stdGaussian E).real
        {x | x ∈ G ∧ κ ≤ ∑ c, w c * directStaticChoiTargetNearActionMass
          (staticChoiAnchorResidual
            (P.scaledAffineSpectralEnergy hH₀ scale x) (anchor c)
            (GaloisForLFunctions.RHTower.choiVector
              (P.scaledAffineSpectralEndpoint hH₀ scale x (U c) :
                Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ)))
          (P.scaledAffineSpectralEnergy hH₀ scale x) r δ} ≤
      (∑ c, w c * adaptiveAnchorGaussianPrefactor r U anchor c *
        ∏ i : Fin n, (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.sqrt (Real.pi /
            (((r : ℝ) * (Fintype.card ι : ℝ)⁻¹ * scale ^ (2 : ℕ) / B ^ (2 : ℕ)) *
              (P.commutatorMap (U c)).singularValues i ^ (2 : ℕ) + 1 / 2))) / κ := by
  let tau : ℝ :=
    (r : ℝ) * (Fintype.card ι : ℝ)⁻¹ * scale ^ (2 : ℕ) / B ^ (2 : ℕ)
  let prefactor : C → ℝ := adaptiveAnchorGaussianPrefactor r U anchor
  have htau : 0 ≤ tau := by
    dsimp [tau]
    positivity
  have hprefactor0 : ∀ c, 0 ≤ prefactor c := by
    intro c
    dsimp [prefactor, adaptiveAnchorGaussianPrefactor]
    split_ifs
    · exact (Real.exp_pos _).le
    · norm_num
  have hprefactor1 : ∀ c, prefactor c ≤ 1 := by
    intro c
    dsimp [prefactor, adaptiveAnchorGaussianPrefactor]
    split_ifs
    · apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (Nat.cast_nonneg r)) (sq_nonneg _)
    · exact le_rfl
  apply GaloisForLFunctions.HTGeometry.stdGaussian_measure_weightedReporter_on_set_ge_le_of_prefactoredAffineLaplace
    G (fun c => P.commutatorMap (U c))
      (fun c => scaledHermitianPencilCommutatorDrift scale H₀ (U c))
      prefactor hprefactor0 hprefactor1
      (fun c x => directStaticChoiTargetNearActionMass
        (staticChoiAnchorResidual
          (P.scaledAffineSpectralEnergy hH₀ scale x) (anchor c)
          (GaloisForLFunctions.RHTower.choiVector
            (P.scaledAffineSpectralEndpoint hH₀ scale x (U c) :
              Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ)))
        (P.scaledAffineSpectralEnergy hH₀ scale x) r δ)
      w hw hn tau htau
  · intro x hx c
    by_cases ha : anchor c = 0
    · have hpoint :=
        P.scaledAffineZeroAnchorResidualNearAction_le_exp_trace_mul_action_of_scale
          hH₀ hscale x (U c) r δ B (hosc x hx) hB
      simpa [tau, prefactor, adaptiveAnchorGaussianPrefactor, ha] using hpoint
    · have hpoint :=
        P.scaledAffineArbitraryAnchorResidualNearAction_le_exp_action_of_scale
          hH₀ hscale x (U c) (anchor c) r δ B (hosc x hx) hB
      simpa [tau, prefactor, adaptiveAnchorGaussianPrefactor, ha] using hpoint
  · exact hκ

/-- **Adaptive first-sheet pseudodeterminant law.**  Arbitrary proposed
first-hit anchors are retained for trace-far endpoints and reset to the common
zero anchor near projective scalar recurrence.  The complete weighted target
image then pays one uniform growing-replica rate. -/
theorem stdGaussian_measure_weightedScaledAffineTwoLocalTraceSafeAnchorResidualNearAction_on_scaleSet_ge_le
    {n : ℕ} (hn : 2 ≤ n)
    {H₀ : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ} (hH₀ : H₀.IsHermitian)
    {scale : ℝ} (hscale : scale ≠ 0)
    {C : Type*} [Fintype C]
    (G : Set (TwoLocalPauliCoefficientSpace n))
    (U : C → Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (rawAnchor : C → ℝ) (β : ℝ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (r : ℕ) (hr : 0 < r) (δ B : ℝ)
    (hosc : ∀ x ∈ G, staticChoiOscillationScale
      ((twoLocalPauliGaussianHermitianPencil n).scaledAffineSpectralEnergy
        hH₀ scale x) ≤ B)
    (hB : 0 < B) {κ : ℝ} (hκ : 0 < κ) :
    (ProbabilityTheory.stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        {x | x ∈ G ∧ κ ≤ ∑ c, w c * directStaticChoiTargetNearActionMass
          (staticChoiAnchorResidual
            ((twoLocalPauliGaussianHermitianPencil n).scaledAffineSpectralEnergy
              hH₀ scale x)
            (traceSafeCircuitAnchor β U rawAnchor c)
            (GaloisForLFunctions.RHTower.choiVector
              ((twoLocalPauliGaussianHermitianPencil n).scaledAffineSpectralEndpoint
                  hH₀ scale x (U c) :
                Matrix (Fin (Fintype.card
                  (FiniteQubitConfiguration (Fin n))))
                  (Fin (Fintype.card
                    (FiniteQubitConfiguration (Fin n)))) ℂ)))
          ((twoLocalPauliGaussianHermitianPencil n).scaledAffineSpectralEnergy
            hH₀ scale x) r δ} ≤
      Real.exp (-twoLocalAdaptiveAnchorUniformRate n r scale B β) / κ := by
  have hbase :=
    FiniteGaussianHermitianPencil.stdGaussian_measure_weightedScaledAffineAdaptiveAnchorResidualNearAction_on_scaleSet_ge_le
        (twoLocalPauliGaussianHermitianPencil n) hH₀ hscale G U
        (traceSafeCircuitAnchor β U rawAnchor) w hw r δ B hosc hB
        (Module.finrank ℝ (TwoLocalPauliCoefficientSpace n)) rfl hκ
  refine hbase.trans ?_
  apply div_le_div_of_nonneg_right _ hκ.le
  exact weighted_twoLocalPauliPencil_traceSafeAnchor_mul_gaussianLaplaceProduct_le_exp_uniformRate
    hn U rawAnchor β w hw hr hscale hB

end RHTower
