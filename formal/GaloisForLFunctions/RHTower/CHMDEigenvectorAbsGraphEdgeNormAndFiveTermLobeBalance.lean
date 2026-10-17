import GaloisForLFunctions.RHTower.CHMDPrimeGeneratorBeurlingDenyAndDiagonalPotentialBalance

/-!
# Eigenvector `absGraph` Edge-Norm Identity, Factor-Four Cross-Jump Bound, and Five-Term Lobe Balance

This module establishes the exact `absGraph` edge-norm identity for `resolvent` eigenvectors, the
resulting factor-four upper bound `-4 * sourcePair (posGraph q) (negGraph q) ≤ ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2`,
the five-term nonnegative positive- and negative-lobe jump-vs.-diagonal potential balance, and the
uniform potential upper bound on the local diagonal quadratic form:

1. **Exact `absGraph` Edge-Norm Identity and Factor-Four Cross-Jump Bound**:
   - `norm_absGraph_snd_sq_sub_self_snd_sq`: for every `p : SourceGraph`,
     `‖(absGraph p).val.snd‖ ^ 2 - ‖p.val.snd‖ ^ 2 = 4 * sourcePair (posGraph p) (negGraph p)`.
   - `norm_posGraph_snd_sq_add_negGraph_snd_sq_eq_absGraph`:
     `‖(posGraph p).val.snd‖ ^ 2 + ‖(negGraph p).val.snd‖ ^ 2 = ‖(absGraph p).val.snd‖ ^ 2 - 2 * sourcePair (posGraph p) (negGraph p)`.
   - `norm_absGraph_snd_sq_rieszLift_of_eigenvector`: for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`)
     with `q = rieszLift w`,
     `‖(absGraph q).val.snd‖ ^ 2 - 4 * sourcePair (posGraph q) (negGraph q) = ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2`,
     and equivalently
     `‖(absGraph q).val.snd‖ ^ 2 - 4 * ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ + 4 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ = ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2`.
   - `neg_four_sourcePair_posGraph_negGraph_le_of_eigenvector`:
     `-4 * sourcePair (posGraph q) (negGraph q) ≤ ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2`.

2. **Five-Term Nonnegative Positive- and Negative-Lobe Jump-vs.-Diagonal Balance**:
   - `posGraph_five_term_jump_eq_diagonals_of_eigenvector` and
     `negGraph_five_term_jump_eq_diagonals_of_eigenvector`:
     for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
     `stationaryEnergy (thetaProduct (posGraph q).val.fst) - ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ + ⟪primeGenerator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ + ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ + ((2 * μ - 1) / μ) * ‖(posGraph q).val.fst‖ ^ 2 = archGroundConstant * ‖thetaToVolume (posGraph q).val.fst‖ ^ 2 + ⟪primeDiagonalOperator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ`
     (and symmetrically for `negGraph q`), where all five left-hand summands are nonnegative whenever `1 / 2 ≤ μ`.

3. **Uniform Potential Upper Bound on the Local Diagonal Form**:
   - `arch_add_primeDiagonal_eq_norm_sq_sub_groundPotential`: for every `u : MassSpace`,
     `archGroundConstant * ‖thetaToVolume u‖ ^ 2 + ⟪primeDiagonalOperator u, u⟫_ℝ = ‖u‖ ^ 2 - ⟪groundPotentialOperator u, u⟫_ℝ`.
   - `arch_add_primeDiagonal_nonneg_and_le`: for every `u : MassSpace`,
     `0 ≤ archGroundConstant * ‖thetaToVolume u‖ ^ 2 + ⟪primeDiagonalOperator u, u⟫_ℝ ≤ (1 + thetaGroundPotentialBound) * ‖u‖ ^ 2`.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace BigOperators
noncomputable section

namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump CHMDTranslation ThetaSourceWard

/-! ## Section 1: Exact `absGraph` Edge-Norm Identity and Factor-Four Cross-Jump Bound -/

/-- For every `p : SourceGraph`,
`‖(absGraph p).val.snd‖ ^ 2 - ‖p.val.snd‖ ^ 2 = 4 * sourcePair (posGraph p) (negGraph p)`. -/
theorem norm_absGraph_snd_sq_sub_self_snd_sq (p : SourceGraph) :
    ‖(absGraph p).val.snd‖ ^ 2 - ‖p.val.snd‖ ^ 2 =
      4 * sourcePair (posGraph p) (negGraph p) := by
  have hEp : sourceEnergy p = ‖p.val.snd‖ ^ 2 - ‖p.val.fst‖ ^ 2 := rfl
  have hEabs : sourceEnergy (absGraph p) =
      ‖(absGraph p).val.snd‖ ^ 2 - ‖(absGraph p).val.fst‖ ^ 2 := rfl
  have h1 := sourceEnergy_absGraph_eq p
  have h2 := norm_absGraph_fst_sq p
  rw [hEp, hEabs, h2] at h1
  linarith

/-- For every `p : SourceGraph`,
`‖(posGraph p).val.snd‖ ^ 2 + ‖(negGraph p).val.snd‖ ^ 2 = ‖(absGraph p).val.snd‖ ^ 2 - 2 * sourcePair (posGraph p) (negGraph p)`. -/
theorem norm_posGraph_snd_sq_add_negGraph_snd_sq_eq_absGraph (p : SourceGraph) :
    ‖(posGraph p).val.snd‖ ^ 2 + ‖(negGraph p).val.snd‖ ^ 2 =
      ‖(absGraph p).val.snd‖ ^ 2 - 2 * sourcePair (posGraph p) (negGraph p) := by
  have h1 := norm_posGraph_snd_sq_add_negGraph_snd_sq p
  have h2 := norm_absGraph_snd_sq_sub_self_snd_sq p
  linarith

/-- For every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
`‖q.val.snd‖ ^ 2 = ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2`. -/
theorem norm_snd_sq_rieszLift_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace}
    (heig : resolvent w = μ • w) :
    ‖(rieszLift w).val.snd‖ ^ 2 = ((1 - μ) / μ) * ‖(rieszLift w).val.fst‖ ^ 2 := by
  set q := rieszLift w
  have hEq : sourceEnergy q = ‖q.val.snd‖ ^ 2 - ‖q.val.fst‖ ^ 2 := rfl
  have h1 := sourceEnergy_eq_inner_of_sourcePair_eq_inner
    (sourcePair_rieszLift_eq_inner_of_eigenvector hμ heig)
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hEq] at h1
  have hid : ((1 - 2 * μ) / μ) * ‖q.val.fst‖ ^ 2 + ‖q.val.fst‖ ^ 2 =
      ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2 := by
    field_simp [hμ]
    ring
  linarith

/-- **Exact `absGraph` Edge-Norm and Bilateral Cross-Jump Identity for Any Eigenvector**:
for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
`‖(absGraph q).val.snd‖ ^ 2 - 4 * sourcePair (posGraph q) (negGraph q) = ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2`
and
`‖(absGraph q).val.snd‖ ^ 2 - 4 * ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ + 4 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ = ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2`. -/
theorem norm_absGraph_snd_sq_rieszLift_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace}
    (heig : resolvent w = μ • w) :
    let q := rieszLift w
    ‖(absGraph q).val.snd‖ ^ 2 - 4 * sourcePair (posGraph q) (negGraph q) =
        ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2 ∧
      ‖(absGraph q).val.snd‖ ^ 2 -
          4 * ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
          4 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ =
        ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2 := by
  intro q
  have h1 := norm_absGraph_snd_sq_sub_self_snd_sq q
  have h2 := norm_snd_sq_rieszLift_of_eigenvector hμ heig
  have h3 := neg_four_sourcePair_posGraph_negGraph_eq_stationary_add_primeShift q
  exact ⟨by linarith, by linarith⟩

/-- **Factor-Four Cross-Jump Upper Bound for Any Eigenvector**:
for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
`-4 * sourcePair (posGraph q) (negGraph q) ≤ ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2`,
`-4 * ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ ≤ ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2`,
and
`4 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ≤ ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2`. -/
theorem neg_four_sourcePair_posGraph_negGraph_le_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0)
    {w : MassSpace} (heig : resolvent w = μ • w) :
    let q := rieszLift w;
    -4 * sourcePair (posGraph q) (negGraph q) ≤ ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2 ∧
      -4 * ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ ≤
        ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2 ∧
      4 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ≤
        ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2 := by
  intro q
  obtain ⟨h1, h2⟩ := norm_absGraph_snd_sq_rieszLift_of_eigenvector hμ heig
  have hnn : 0 ≤ ‖(absGraph q).val.snd‖ ^ 2 := sq_nonneg _
  have hstat : 0 ≤ -⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ :=
    neg_nonneg.mpr (inner_fullGroundEquiv_posGraph_negGraph_snd_nonpos q)
  have hprime : 0 ≤ ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ :=
    inner_primeShiftOperator_posGraph_negGraph_nonneg q
  exact ⟨by linarith, by linarith, by linarith⟩

/-! ## Section 2: Five-Term Nonnegative Positive- and Negative-Lobe Jump-vs.-Diagonal Balance -/

/-- **Positive-Lobe Five-Term Jump-vs.-Diagonal Potential Balance**:
for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
`stationaryEnergy (thetaProduct (posGraph q).val.fst) - ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ + ⟪primeGenerator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ + ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ + ((2 * μ - 1) / μ) * ‖(posGraph q).val.fst‖ ^ 2 = archGroundConstant * ‖thetaToVolume (posGraph q).val.fst‖ ^ 2 + ⟪primeDiagonalOperator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ`. -/
theorem posGraph_five_term_jump_eq_diagonals_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0)
    {w : MassSpace} (heig : resolvent w = μ • w) :
    let q := rieszLift w
    stationaryEnergy (thetaProduct (posGraph q).val.fst) -
        ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        ⟪primeGenerator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ +
        ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ +
        ((2 * μ - 1) / μ) * ‖(posGraph q).val.fst‖ ^ 2 =
      archGroundConstant * ‖thetaToVolume (posGraph q).val.fst‖ ^ 2 +
        ⟪primeDiagonalOperator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ := by
  intro q
  have h1 := sourceEnergy_posGraph_rieszLift_of_eigenvector hμ heig
  have h2 := sourceEnergy_eq_stationary_add_primeGenerator_sub_diagonals (posGraph q)
  have h3 := sourcePair_posGraph_negGraph_eq_stationary_sub_primeShift q
  have hid : ((1 - 2 * μ) / μ) * ‖(posGraph q).val.fst‖ ^ 2 +
      ((2 * μ - 1) / μ) * ‖(posGraph q).val.fst‖ ^ 2 = 0 := by
    field_simp [hμ]
    ring
  linarith

/-- **Negative-Lobe Five-Term Jump-vs.-Diagonal Potential Balance**:
for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
`stationaryEnergy (thetaProduct (negGraph q).val.fst) - ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ + ⟪primeGenerator (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ + ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ + ((2 * μ - 1) / μ) * ‖(negGraph q).val.fst‖ ^ 2 = archGroundConstant * ‖thetaToVolume (negGraph q).val.fst‖ ^ 2 + ⟪primeDiagonalOperator (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ`. -/
theorem negGraph_five_term_jump_eq_diagonals_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0)
    {w : MassSpace} (heig : resolvent w = μ • w) :
    let q := rieszLift w
    stationaryEnergy (thetaProduct (negGraph q).val.fst) -
        ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        ⟪primeGenerator (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ +
        ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ +
        ((2 * μ - 1) / μ) * ‖(negGraph q).val.fst‖ ^ 2 =
      archGroundConstant * ‖thetaToVolume (negGraph q).val.fst‖ ^ 2 +
        ⟪primeDiagonalOperator (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ := by
  intro q
  have h1 := sourceEnergy_negGraph_rieszLift_of_eigenvector hμ heig
  have h2 := sourceEnergy_eq_stationary_add_primeGenerator_sub_diagonals (negGraph q)
  have h3 := sourcePair_posGraph_negGraph_eq_stationary_sub_primeShift q
  have hid : ((1 - 2 * μ) / μ) * ‖(negGraph q).val.fst‖ ^ 2 +
      ((2 * μ - 1) / μ) * ‖(negGraph q).val.fst‖ ^ 2 = 0 := by
    field_simp [hμ]
    ring
  linarith

/-! ## Section 3: Uniform Potential Upper Bound on the Local Diagonal Form -/

/-- For every `u : MassSpace`,
`archGroundConstant * ‖thetaToVolume u‖ ^ 2 + ⟪primeDiagonalOperator u, u⟫_ℝ = ‖u‖ ^ 2 - ⟪groundPotentialOperator u, u⟫_ℝ`. -/
theorem arch_add_primeDiagonal_eq_norm_sq_sub_groundPotential (u : MassSpace) :
    archGroundConstant * ‖thetaToVolume u‖ ^ 2 + ⟪primeDiagonalOperator u, u⟫_ℝ =
      ‖u‖ ^ 2 - ⟪groundPotentialOperator u, u⟫_ℝ := by
  have hsub := congrArg (fun T : MassSpace →L[ℝ] MassSpace => ⟪T u, u⟫_ℝ)
    sub_groundPotentialOperator_eq
  change ⟪u - groundPotentialOperator u, u⟫_ℝ =
    ⟪primeDiagonalOperator u + archDiagonalOperator u, u⟫_ℝ at hsub
  rw [inner_sub_left, real_inner_self_eq_norm_sq, inner_add_left,
    inner_archDiagonalOperator_self] at hsub
  linarith

/-- For every `u : MassSpace`,
`0 ≤ archGroundConstant * ‖thetaToVolume u‖ ^ 2 + ⟪primeDiagonalOperator u, u⟫_ℝ`
and
`archGroundConstant * ‖thetaToVolume u‖ ^ 2 + ⟪primeDiagonalOperator u, u⟫_ℝ ≤ (1 + thetaGroundPotentialBound) * ‖u‖ ^ 2`. -/
theorem arch_add_primeDiagonal_nonneg_and_le (u : MassSpace) :
    0 ≤ archGroundConstant * ‖thetaToVolume u‖ ^ 2 + ⟪primeDiagonalOperator u, u⟫_ℝ ∧
      archGroundConstant * ‖thetaToVolume u‖ ^ 2 + ⟪primeDiagonalOperator u, u⟫_ℝ ≤
        (1 + thetaGroundPotentialBound) * ‖u‖ ^ 2 := by
  have harch : 0 ≤ archGroundConstant * ‖thetaToVolume u‖ ^ 2 :=
    mul_nonneg archGroundConstant_pos.le (sq_nonneg _)
  have hprime : 0 ≤ ⟪primeDiagonalOperator u, u⟫_ℝ :=
    primeDiagonalOperator_isPositive.inner_nonneg_left u
  refine ⟨add_nonneg harch hprime, ?_⟩
  rw [arch_add_primeDiagonal_eq_norm_sq_sub_groundPotential]
  have hcs : -⟪groundPotentialOperator u, u⟫_ℝ ≤ ‖groundPotentialOperator u‖ * ‖u‖ :=
    (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  have hnorm : ‖groundPotentialOperator u‖ ≤ thetaGroundPotentialBound * ‖u‖ := by
    have h1 := ContinuousLinearMap.le_opNorm groundPotentialOperator u
    have h2 : ‖groundPotentialOperator‖ ≤ thetaGroundPotentialBound :=
      MeasureTheory.norm_lpBoundedMulCLM_le measurable_thetaGroundPotential
        thetaGroundPotentialBound_nonneg norm_thetaGroundPotential_le
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg u))
  nlinarith [norm_nonneg u]

end RHTower.CHMDPolar
