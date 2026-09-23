import GaloisForLFunctions.RHTower.ReturnExcisedGrowingReplicaPseudodeterminantLaw
import GaloisForLFunctions.RHTower.AffineTwoLocalPauliSpectralActionLaw

/-!
# Uniform anchor--transverse pseudodeterminant law

For every unitary endpoint, either its normalized trace is bounded away from one
and the return anchor supplies exponential suppression, or its trace is close to
one and the two-local Pauli commutator map supplies transverse Gaussian
suppression.  The harmonic combination is uniform over the entire target image.
-/

open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator
open Matrix Set MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

noncomputable section

namespace RHTower

theorem harmonic_mean_lower_of_linear_floors
    {A K b x y : ℝ} (hA : 0 < A) (hK : 0 < K) (hb : 0 < b)
    (hx : A * b ≤ x) (hy : K * b ≤ y) :
    A * K / (A + K) * b ≤ x * y / (x + y) := by
  have hAb : 0 < A * b := mul_pos hA hb
  have hKb : 0 < K * b := mul_pos hK hb
  have hxpos : 0 < x := hAb.trans_le hx
  have hypos : 0 < y := hKb.trans_le hy
  have hfirst :
      (A * b) * (K * b) / (A * b + K * b) ≤
        x * (K * b) / (x + K * b) := by
    rw [div_le_div_iff₀ (add_pos hAb hKb) (add_pos hxpos hKb)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg (K * b))]
  have hsecond :
      x * (K * b) / (x + K * b) ≤ x * y / (x + y) := by
    rw [div_le_div_iff₀ (add_pos hxpos hKb) (add_pos hxpos hypos)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hy) (sq_nonneg x)]
  calc
    A * K / (A + K) * b =
        (A * b) * (K * b) / (A * b + K * b) := by
      field_simp [ne_of_gt hb, ne_of_gt (add_pos hA hK)]
    _ ≤ x * (K * b) / (x + K * b) := hfirst
    _ ≤ x * y / (x + y) := hsecond

theorem min_le_convex_complement
    {r q z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    min r q ≤ r * z + q * (1 - z) := by
  by_cases h : r ≤ q
  · rw [min_eq_left h]
    nlinarith
  · rw [min_eq_right (le_of_not_ge h)]
    nlinarith

def twoLocalAnchorTransverseActivationRate
    (n r : ℕ) (scale B : ℝ) : ℝ :=
  4 * (r : ℝ) * ((n - 1 : ℕ) : ℝ) * scale ^ (2 : ℕ) / B ^ (2 : ℕ)

def twoLocalAnchorTransverseStableRate (n : ℕ) : ℝ :=
  ((6 * n - 4 : ℕ) : ℝ)

def twoLocalAnchorTransverseHarmonicRate
    (n r : ℕ) (scale B : ℝ) : ℝ :=
  let A := twoLocalAnchorTransverseActivationRate n r scale B
  let K := twoLocalAnchorTransverseStableRate n
  A * K / (A + K)

def twoLocalAnchorTransverseUniformRate
    (n r : ℕ) (scale B : ℝ) : ℝ :=
  min (r : ℝ) (twoLocalAnchorTransverseHarmonicRate n r scale B)

set_option maxHeartbeats 800000 in
theorem twoLocalPauli_anchor_mul_gaussianLaplaceProduct_le_exp_uniformRate
    {n : ℕ} (hn : 2 ≤ n)
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    {r : ℕ} (hr : 0 < r) {scale B : ℝ}
    (hscale : scale ≠ 0) (hB : 0 < B) :
    Real.exp (-(r : ℝ) *
        (‖Matrix.trace
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)‖ /
          Fintype.card (FiniteQubitConfiguration (Fin n))) ^ (2 : ℕ)) *
      ∏ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
        (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.sqrt (Real.pi /
            (((r : ℝ) *
                (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ)⁻¹ *
                scale ^ (2 : ℕ) / B ^ (2 : ℕ)) *
              (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ (2 : ℕ) +
              1 / 2)) ≤
      Real.exp (-twoLocalAnchorTransverseUniformRate n r scale B) := by
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
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have htau : 0 < tau := by
    dsimp [tau]
    positivity
  have htrace : ‖Matrix.trace
      (U : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) ≤ D ^ (2 : ℕ) := by
    have h := finiteUnitary_trace_normSq_le_card_sq U
    simpa [Complex.sq_norm, D] using h
  have ha20 : 0 ≤ a2 := by dsimp [a2]; positivity
  have ha21 : a2 ≤ 1 := by
    dsimp [a2]
    exact (div_le_one (sq_pos_of_pos hD)).2 htrace
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hb1 : b ≤ 1 := by dsimp [b]; linarith
  have hA : 0 < A := by
    dsimp [A, twoLocalAnchorTransverseActivationRate]
    have hn1 : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hn
    positivity
  have hK : 0 < K := by
    dsimp [K, twoLocalAnchorTransverseStableRate]
    exact_mod_cast (show 0 < 6 * n - 4 by omega)
  have hq : 0 < q := by
    dsimp [q, twoLocalAnchorTransverseHarmonicRate]
    exact div_pos (mul_pos hA hK) (add_pos hA hK)
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
  · have ha2 : a2 = 1 := by dsimp [b] at hb; linarith
    have hfrac0 : 0 ≤ (tau * S ^ (2 : ℕ)) / (tau * Q + S) :=
      div_nonneg (mul_nonneg htau.le (sq_nonneg S))
        (add_nonneg (mul_nonneg htau.le hQ0) hS0)
    have hprodOne :
        (∏ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
          (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.sqrt (Real.pi /
              (tau * (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ (2 : ℕ) +
                1 / 2))) ≤ 1 := by
      calc
        _ ≤ Real.exp (-((tau * S ^ (2 : ℕ)) / (tau * Q + S))) := by
          simpa only [S, Q, ← pow_mul, Nat.reduceMul] using hprodTotal
        _ ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hfrac0)
    have hrate : twoLocalAnchorTransverseUniformRate n r scale B ≤ (r : ℝ) := by
      dsimp [twoLocalAnchorTransverseUniformRate]
      exact min_le_left _ _
    have hanchor : Real.exp (-(r : ℝ) * a2) ≤
        Real.exp (-twoLocalAnchorTransverseUniformRate n r scale B) := by
      apply Real.exp_le_exp.mpr
      rw [ha2, mul_one]
      linarith
    calc
      Real.exp (-(r : ℝ) *
          (‖Matrix.trace
            (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)‖ /
            Fintype.card (FiniteQubitConfiguration (Fin n))) ^ (2 : ℕ)) *
        ∏ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
          (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.sqrt (Real.pi /
              (((r : ℝ) *
                  (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ)⁻¹ *
                  scale ^ (2 : ℕ) / B ^ (2 : ℕ)) *
                (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ (2 : ℕ) +
                1 / 2)) =
          Real.exp (-(r : ℝ) * a2) *
            ∏ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
              (Real.sqrt (2 * Real.pi))⁻¹ *
                Real.sqrt (Real.pi /
                  (tau * (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ (2 : ℕ) +
                    1 / 2)) := by simp [a2, D, tau, div_pow]
      _ ≤ Real.exp (-(r : ℝ) * a2) * 1 :=
        mul_le_mul_of_nonneg_left hprodOne (Real.exp_pos _).le
      _ ≤ _ := by simpa using hanchor
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
    have hprodRate :
        (∏ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
          (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.sqrt (Real.pi /
              (tau * (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ (2 : ℕ) +
                1 / 2))) ≤ Real.exp (-(q * b)) := by
      calc
        _ ≤ Real.exp (-((tau * S) * (S ^ (2 : ℕ) / Q) /
            (tau * S + S ^ (2 : ℕ) / Q))) := by
          simpa only [S, Q, ← pow_mul, Nat.reduceMul] using hprod
        _ ≤ Real.exp (-(q * b)) := Real.exp_le_exp.mpr (by linarith)
    have hconvex : twoLocalAnchorTransverseUniformRate n r scale B ≤
        (r : ℝ) * a2 + q * b := by
      simpa [twoLocalAnchorTransverseUniformRate, q] using
        min_le_convex_complement ha20 ha21
    calc
      Real.exp (-(r : ℝ) *
          (‖Matrix.trace
            (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)‖ /
            Fintype.card (FiniteQubitConfiguration (Fin n))) ^ (2 : ℕ)) *
        ∏ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
          (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.sqrt (Real.pi /
              (((r : ℝ) *
                  (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ)⁻¹ *
                  scale ^ (2 : ℕ) / B ^ (2 : ℕ)) *
                (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ (2 : ℕ) +
                1 / 2)) =
          Real.exp (-(r : ℝ) * a2) *
            ∏ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
              (Real.sqrt (2 * Real.pi))⁻¹ *
                Real.sqrt (Real.pi /
                  (tau * (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ (2 : ℕ) +
                    1 / 2)) := by simp [a2, D, tau, div_pow]
      _ ≤ Real.exp (-(r : ℝ) * a2) * Real.exp (-(q * b)) :=
        mul_le_mul_of_nonneg_left hprodRate (Real.exp_pos _).le
      _ = Real.exp (-((r : ℝ) * a2 + q * b)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem twoLocalPauliPencil_anchor_mul_gaussianLaplaceProduct_le_exp_uniformRate
    {n : ℕ} (hn : 2 ≤ n)
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    {r : ℕ} (hr : 0 < r) {scale B : ℝ}
    (hscale : scale ≠ 0) (hB : 0 < B) :
    Real.exp (-(r : ℝ) *
        (‖Matrix.trace
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)‖ /
          Fintype.card (FiniteQubitConfiguration (Fin n))) ^ (2 : ℕ)) *
      ∏ i : Fin (Module.finrank ℝ (TwoLocalPauliCoefficientSpace n)),
        (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.sqrt (Real.pi /
            (((r : ℝ) *
                (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ)⁻¹ *
                scale ^ (2 : ℕ) / B ^ (2 : ℕ)) *
              ((twoLocalPauliGaussianHermitianPencil n).commutatorMap U).singularValues i ^ (2 : ℕ) +
              1 / 2)) ≤
      Real.exp (-twoLocalAnchorTransverseUniformRate n r scale B) := by
  rw [twoLocalPauliGaussianHermitianPencil_commutatorMap]
  rw [show Module.finrank ℝ (TwoLocalPauliCoefficientSpace n) =
      Fintype.card (PauliTracelessLabel n 2) from finrank_euclideanSpace]
  exact twoLocalPauli_anchor_mul_gaussianLaplaceProduct_le_exp_uniformRate
    hn U hr hscale hB

theorem weighted_twoLocalPauliPencil_anchor_mul_gaussianLaplaceProduct_le_exp_uniformRate
    {n : ℕ} (hn : 2 ≤ n)
    {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    {r : ℕ} (hr : 0 < r) {scale B : ℝ}
    (hscale : scale ≠ 0) (hB : 0 < B) :
    (∑ c, w c *
      (Real.exp (-(r : ℝ) *
          (‖Matrix.trace
            (U c : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)‖ /
            Fintype.card (FiniteQubitConfiguration (Fin n))) ^ (2 : ℕ)) *
        ∏ i : Fin (Module.finrank ℝ (TwoLocalPauliCoefficientSpace n)),
          (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.sqrt (Real.pi /
              (((r : ℝ) *
                  (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ)⁻¹ *
                  scale ^ (2 : ℕ) / B ^ (2 : ℕ)) *
                ((twoLocalPauliGaussianHermitianPencil n).commutatorMap
                    (U c)).singularValues i ^ (2 : ℕ) +
                1 / 2)))) ≤
      Real.exp (-twoLocalAnchorTransverseUniformRate n r scale B) := by
  calc
    _ ≤ ∑ c, w c * Real.exp
        (-twoLocalAnchorTransverseUniformRate n r scale B) :=
      Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left
        (twoLocalPauliPencil_anchor_mul_gaussianLaplaceProduct_le_exp_uniformRate
          hn (U c) hr hscale hB) (hw.1 c)
    _ = _ := by rw [← Finset.sum_mul, hw.2, one_mul]

theorem pairQubitProjectiveSeedWeightedReturnExcisedGrowingReplicaBudget_le_uniformRate
    {L : ℕ} (hL : 1 ≤ L)
    {rho scale : ℝ} (hrho : 0 ≤ rho) (hscale : scale ≠ 0)
    {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    {r : ℕ} (hr : 0 < r) {kappa : ℝ} (hkappa : 0 < kappa) :
    pairQubitProjectiveSeedWeightedReturnExcisedGrowingReplicaBudget
        L rho scale U w r kappa ≤
      Real.exp (-twoLocalAnchorTransverseUniformRate (L * 2) r scale
        (pairQubitProjectiveSeedGrowingReplicaOscillationCeiling L rho scale)) / kappa := by
  have hB : 0 < pairQubitProjectiveSeedGrowingReplicaOscillationCeiling L rho scale :=
    pairQubitProjectiveSeedGrowingReplicaOscillationCeiling_pos L hrho
  have hsum :=
    weighted_twoLocalPauliPencil_anchor_mul_gaussianLaplaceProduct_le_exp_uniformRate
      (n := L * 2) (by omega)
      (fun c => pairQubitPathUnitaryReindex L (U c)) w hw hr hscale hB
  have hsum' :
      (∑ c, w c *
        Real.exp (-(r : ℝ) *
          (‖Matrix.trace
            (pairQubitPathUnitaryReindex L (U c) :
              Matrix (FiniteQubitConfiguration (Fin (L * 2)))
                (FiniteQubitConfiguration (Fin (L * 2))) ℂ)‖ /
            Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))) ^ (2 : ℕ)) *
        ∏ i : Fin (Module.finrank ℝ
            (TwoLocalPauliCoefficientSpace (L * 2))),
          (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.sqrt (Real.pi /
              (((r : ℝ) *
                  (Fintype.card
                    (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ *
                  scale ^ (2 : ℕ) /
                    pairQubitProjectiveSeedGrowingReplicaOscillationCeiling
                      L rho scale ^ (2 : ℕ)) *
                ((twoLocalPauliGaussianHermitianPencil
                    (L * 2)).commutatorMap
                      (pairQubitPathUnitaryReindex L (U c))).singularValues i ^ (2 : ℕ) +
                1 / 2))) ≤
        Real.exp (-twoLocalAnchorTransverseUniformRate (L * 2) r scale
          (pairQubitProjectiveSeedGrowingReplicaOscillationCeiling L rho scale)) := by
    simpa only [mul_assoc] using hsum
  exact div_le_div_of_nonneg_right hsum' hkappa.le

end RHTower
