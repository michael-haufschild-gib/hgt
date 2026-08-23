import GaloisForLFunctions.HTGeometry.ProjectiveChoiAdaptiveCubeUnionWindowLaw

open Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : ℕ}

/-- Translation changes only packet phases, never packet magnitude. -/
theorem norm_packetAmp_center_independent
    (N : ℕ) (rho : ℝ) (c c' : Fin d → ℝ) (k : Fin d → ℕ × ℕ) :
    ‖packetAmp N rho c k‖ = ‖packetAmp N rho c' k‖ := by
  classical
  simp only [packetAmp, norm_prod, norm_mul, Complex.norm_exp]
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  simp

/-- Exact multiplicative packet cost is independent of target centre. -/
theorem periodicFejerMultiplicativeCost_center_independent
    (N : ℕ) (rho : ℝ) (c c' : Fin d → ℝ) (eps : ℝ) :
    periodicFejerMultiplicativeCost N rho c eps =
      periodicFejerMultiplicativeCost N rho c' eps := by
  classical
  simp only [periodicFejerMultiplicativeCost,
    KleinbockMargulis.indexedMultiplicativeFourierL1Cost]
  apply Finset.sum_congr rfl
  intro k _
  rw [norm_packetAmp_center_independent N rho c c' k.1]

/-- Every Fejér packet character has multiplicative height at most the
displayed finite-resolution scale. -/
theorem packetCharacter_piPlus_le
    (N : ℕ) {k : Fin d → ℕ × ℕ}
    (hk : k ∈ nonconstantPacketIndexSet N d) :
    KleinbockMargulis.PiPlus (packetCharacter k) ≤
      (2 * ((N : ℝ) + 1)) ^ d := by
  classical
  have hfull : k ∈ Fintype.piFinset (fun _ : Fin d =>
      Finset.range (N + 1) ×ˢ Finset.range (N + 1)) :=
    (Finset.mem_sdiff.mp hk).1
  rw [KleinbockMargulis.PiPlus]
  calc
    (∏ j, max |(packetCharacter k j : ℝ)| 1) ≤
        ∏ _j : Fin d, (2 * ((N : ℝ) + 1)) := by
      refine Finset.prod_le_prod (fun j _ => by positivity) ?_
      intro j _
      have hj := Fintype.mem_piFinset.mp hfull j
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hj
      have ha : ((k j).1 : ℝ) < (N : ℝ) + 1 := by exact_mod_cast hj.1
      have hb : ((k j).2 : ℝ) < (N : ℝ) + 1 := by exact_mod_cast hj.2
      apply max_le
      · simp only [packetCharacter]
        rw [abs_le]
        constructor <;> push_cast <;> linarith
      · have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        linarith
    _ = (2 * ((N : ℝ) + 1)) ^ d := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem div_rpow_neg_eq_rpow_one_add {x eps : ℝ} (hx : 0 < x) :
    x / x ^ (-eps) = x ^ (1 + eps) := by
  rw [Real.rpow_neg hx.le, div_eq_mul_inv, inv_inv, Real.rpow_add hx, Real.rpow_one]

/-- Explicit multiplicative weight bound for every retained packet sheet. -/
theorem packetCharacter_multiplicativeWeight_le
    (N : ℕ) {eps : ℝ} (heps : 0 ≤ eps) {k : Fin d → ℕ × ℕ}
    (hk : k ∈ nonconstantPacketIndexSet N d) :
    KleinbockMargulis.PiPlus (packetCharacter k) /
        KleinbockMargulis.PiPlus (packetCharacter k) ^ (-eps) ≤
      (2 * ((N : ℝ) + 1)) ^ ((d : ℝ) * (1 + eps)) := by
  let P := KleinbockMargulis.PiPlus (packetCharacter k)
  let B := 2 * ((N : ℝ) + 1)
  have hP : 0 < P := KleinbockMargulis.PiPlus_pos _
  have hB : 0 < B := by dsimp [B]; positivity
  have hPB : P ≤ B ^ d := packetCharacter_piPlus_le N hk
  rw [div_rpow_neg_eq_rpow_one_add hP]
  calc
    P ^ (1 + eps) ≤ (B ^ d) ^ (1 + eps) :=
      Real.rpow_le_rpow hP.le hPB (by linarith)
    _ = B ^ ((d : ℝ) * (1 + eps)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hB.le]

/-- Centre-free explicit upper envelope for every translated Fejér packet. -/
noncomputable def periodicFejerMultiplicativeCostUpperBound
    (N d : ℕ) (rho eps : ℝ) : ℝ :=
  ((N : ℝ) + 1) ^ (2 * d) *
    (((((N : ℝ) + 1)⁻¹ * (rho / (2 * π))) ^ d) *
      (2 * ((N : ℝ) + 1)) ^ ((d : ℝ) * (1 + eps)))

/-- The exact multiplicative Fourier cost is bounded uniformly over every
centre by an explicit resolution-height envelope. -/
theorem periodicFejerMultiplicativeCost_le_explicit
    (N : ℕ) {rho eps : ℝ} (hrho : 0 < rho) (hrhopi : rho ≤ π)
    (heps : 0 ≤ eps) (c : Fin d → ℝ) :
    periodicFejerMultiplicativeCost N rho c eps ≤
      periodicFejerMultiplicativeCostUpperBound N d rho eps := by
  classical
  let A : ℝ := (((N : ℝ) + 1)⁻¹ * (rho / (2 * π))) ^ d
  let W : ℝ := (2 * ((N : ℝ) + 1)) ^ ((d : ℝ) * (1 + eps))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hW : 0 ≤ W := Real.rpow_nonneg (by positivity) _
  rw [periodicFejerMultiplicativeCost,
    KleinbockMargulis.indexedMultiplicativeFourierL1Cost]
  calc
    (∑ k : {k // k ∈ nonconstantPacketIndexSet N d},
        ‖packetAmp N rho c k.1‖ *
          (KleinbockMargulis.PiPlus (packetCharacter k.1) /
            KleinbockMargulis.PiPlus (packetCharacter k.1) ^ (-eps))) ≤
      ∑ _k : {k // k ∈ nonconstantPacketIndexSet N d}, A * W := by
        refine Finset.sum_le_sum fun k _ => ?_
        apply mul_le_mul
        · exact norm_packetAmp_le N hrho hrhopi c k.1
        · exact packetCharacter_multiplicativeWeight_le N heps k.2
        · have hP := KleinbockMargulis.PiPlus_pos (packetCharacter k.1)
          exact div_nonneg hP.le (Real.rpow_pos_of_pos hP _).le
        · exact hA
    _ = (((nonconstantPacketIndexSet N d).card : ℝ) * (A * W)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      exact_mod_cast Fintype.card_coe (nonconstantPacketIndexSet N d)
    _ ≤ ((N : ℝ) + 1) ^ (2 * d) * (A * W) := by
      exact mul_le_mul_of_nonneg_right (card_modeIndex_le (d := d) N)
        (mul_nonneg hA hW)
    _ = periodicFejerMultiplicativeCostUpperBound N d rho eps := by rfl

/-- A complete adaptive family pays exactly its cardinality times one
centre-free packet cost. -/
theorem sum_periodicFejerMultiplicativeCost_eq_card_mul_centerFree
    (N m : ℕ) (rho eps : ℝ) (c : Fin m → Fin d → ℝ)
    (c0 : Fin d → ℝ) :
    (∑ a : Fin m, periodicFejerMultiplicativeCost N rho (c a) eps) =
      (m : ℝ) * periodicFejerMultiplicativeCost N rho c0 eps := by
  calc
    (∑ a : Fin m, periodicFejerMultiplicativeCost N rho (c a) eps) =
        ∑ _a : Fin m, periodicFejerMultiplicativeCost N rho c0 eps := by
      exact Finset.sum_congr rfl fun a _ =>
        periodicFejerMultiplicativeCost_center_independent N rho (c a) c0 eps
    _ = (m : ℝ) * periodicFejerMultiplicativeCost N rho c0 eps := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Centre-free adaptive projective-Choi union law.** Arbitrary finite
target families selected after the same spectrum draw pay only cardinality;
their locations disappear from the spectral-resolution cost. -/
theorem exists_zeroAnchoredMetricBallFamilyAngularVisit_centerFreeWindowUpper
    {omega : Fin d → ℝ}
    (homega : ¬ KleinbockMargulis.VWMA omega)
    {eps delta : ℝ} (heps : 0 < eps) (hdelta : 0 < delta)
    (N m : ℕ)
    (hsmall : 2 * zeroAnchoredChoiAngularRadius d delta ≤ π) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (target : Fin m →
          EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
        (u T : ℝ), 0 < T →
        (MeasureTheory.volume
          (zeroAnchoredMetricBallFamilyAngularVisit d m delta target omega ∩
            Set.Ioc u (u + T))).toReal ≤
          (2 : ℝ) ^ d * T *
            (((m : ℕ) : ℝ) *
                (((2 * zeroAnchoredChoiAngularRadius d delta / (2 * π)) ^ d : ℝ) +
                  (d : ℝ) *
                    ((1 / (2 * zeroAnchoredChoiAngularRadius d delta)) *
                      (2 * π / Real.sqrt ((N : ℝ) + 1))))
              + (2 * C / T) * ((m : ℝ) *
                  periodicFejerMultiplicativeCostUpperBound N d
                    (2 * zeroAnchoredChoiAngularRadius d delta) eps)) := by
  obtain ⟨C, hC, hbase⟩ :=
    exists_zeroAnchoredMetricBallFamilyAngularVisit_multiplicativeWindowUpper
      homega heps hdelta N m hsmall
  refine ⟨C, hC, ?_⟩
  intro target u T hT
  refine (hbase target u T hT).trans ?_
  have hrho : 0 < 2 * zeroAnchoredChoiAngularRadius d delta := by
    rw [zeroAnchoredChoiAngularRadius]
    positivity
  have hrhopi : 2 * zeroAnchoredChoiAngularRadius d delta ≤ π := hsmall
  have hsum :
      (∑ a : Fin m,
          periodicFejerMultiplicativeCost N
            (2 * zeroAnchoredChoiAngularRadius d delta)
            (zeroAnchoredMetricBallAngularCenter d (target a) delta) eps) ≤
        (m : ℝ) * periodicFejerMultiplicativeCostUpperBound N d
          (2 * zeroAnchoredChoiAngularRadius d delta) eps := by
    calc
      (∑ a : Fin m,
          periodicFejerMultiplicativeCost N
            (2 * zeroAnchoredChoiAngularRadius d delta)
            (zeroAnchoredMetricBallAngularCenter d (target a) delta) eps) ≤
        ∑ _a : Fin m, periodicFejerMultiplicativeCostUpperBound N d
          (2 * zeroAnchoredChoiAngularRadius d delta) eps := by
            exact Finset.sum_le_sum fun a _ =>
              periodicFejerMultiplicativeCost_le_explicit N hrho hrhopi heps.le _
      _ = (m : ℝ) * periodicFejerMultiplicativeCostUpperBound N d
          (2 * zeroAnchoredChoiAngularRadius d delta) eps := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  gcongr

end

end GaloisForLFunctions.HTGeometry
