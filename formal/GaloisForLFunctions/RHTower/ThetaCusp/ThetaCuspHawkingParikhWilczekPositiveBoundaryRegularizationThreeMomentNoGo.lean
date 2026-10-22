import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekCountableMatrixThreeMomentNoGo

/-!
# Positive boundary regularization cannot escape the PW three-moment collapse

Every moment-admissible countable Parikh--Wilczek cross-grade matrix has residual energy equal to
one quadratic in the common spectral coordinate. This module proves that allowing the matrix to
vary through a boundary regularization does not create a new infinite-grade invariant.

Finite boundary limits at only three source-independent samples, with spectral coordinates
`1, 2, 5`, recover all three limiting matrix moments by Vandermonde inversion. Consequently every
pointwise boundary limit is the same reconstructed quadratic. For an eventually entrywise
nonnegative regularization, its three limiting moments are nonnegative. The boundary observable
then has a sharp dichotomy: all three moments vanish and the limit is identically blind, or the
residual is strictly positive on every actual Xi divisor and full PW energy vanishes exactly on the
critical wall. Universal extinction in the second branch is therefore RH-equivalent.

This kills positive pointwise Abel, Cesaro, cutoff, and other moment-admissible boundary
regularizations as PW-B balance producers. A survivor must lose a finite three-sample boundary
value, use signed/complex coupling, become nonlinear, or use a genuinely singular non-pointwise
operation.

`[NEW] [PW-B ROUTE-CLASS NO-GO] [BOUNDARY RIGIDITY] [LEAN-PROVED]`
-/

open Complex Filter Topology
open scoped BigOperators Topology

namespace RHTower

noncomputable section

def pwBoundaryLimitMomentZero (L1 L2 L5 : ℝ) : ℝ :=
  (L5 - 4 * L2 + 3 * L1) / 12

def pwBoundaryLimitMomentOne (L1 L2 L5 : ℝ) : ℝ :=
  (8 * L2 - 7 * L1 - L5) / 4

def pwBoundaryLimitMomentTwo (L1 L2 L5 : ℝ) : ℝ :=
  (15 * L1 - 10 * L2 + L5) / 6

def pwBoundaryResidualLimit (L1 L2 L5 : ℝ) (s : ℂ) : ℝ :=
  pwBoundaryLimitMomentZero L1 L2 L5 *
      schwarzschildParikhWilczekBorelSpectralCoordinate s ^ (2 : ℕ) +
    pwBoundaryLimitMomentOne L1 L2 L5 *
      schwarzschildParikhWilczekBorelSpectralCoordinate s +
    pwBoundaryLimitMomentTwo L1 L2 L5

def pwBoundaryCrossGradeEnergyLimit (L1 L2 L5 : ℝ) (s : ℂ) : ℝ :=
  schwarzschildParikhWilczekBorelWallFactor s ^ (2 : ℕ) *
    pwBoundaryResidualLimit L1 L2 L5 s

theorem pwCountableMatrixMoments_eq_three_samples
    {M : ℕ → ℕ → ℝ}
    (hM : schwarzschildParikhWilczekCountableMatrixMomentAdmissible M) :
    schwarzschildParikhWilczekCountableMatrixMomentZero M =
        pwBoundaryLimitMomentZero
          (schwarzschildParikhWilczekCountableMatrixResidualEnergy M 0)
          (schwarzschildParikhWilczekCountableMatrixResidualEnergy M I)
          (schwarzschildParikhWilczekCountableMatrixResidualEnergy M (2 * I)) ∧
      schwarzschildParikhWilczekCountableMatrixMomentOne M =
        pwBoundaryLimitMomentOne
          (schwarzschildParikhWilczekCountableMatrixResidualEnergy M 0)
          (schwarzschildParikhWilczekCountableMatrixResidualEnergy M I)
          (schwarzschildParikhWilczekCountableMatrixResidualEnergy M (2 * I)) ∧
      schwarzschildParikhWilczekCountableMatrixMomentTwo M =
        pwBoundaryLimitMomentTwo
          (schwarzschildParikhWilczekCountableMatrixResidualEnergy M 0)
          (schwarzschildParikhWilczekCountableMatrixResidualEnergy M I)
          (schwarzschildParikhWilczekCountableMatrixResidualEnergy M (2 * I)) := by
  have h1 := schwarzschildParikhWilczekCountableMatrixResidualEnergy_three_moment hM (0 : ℂ)
  have h2 := schwarzschildParikhWilczekCountableMatrixResidualEnergy_three_moment hM I
  have h5 := schwarzschildParikhWilczekCountableMatrixResidualEnergy_three_moment hM (2 * I)
  norm_num [schwarzschildParikhWilczekCountableMatrixResidualPolynomial,
    schwarzschildParikhWilczekBorelSpectralCoordinate] at h1 h2 h5
  constructor
  · rw [pwBoundaryLimitMomentZero]
    linarith
  constructor
  · rw [pwBoundaryLimitMomentOne]
    linarith
  · rw [pwBoundaryLimitMomentTwo]
    linarith

def PWCountableMatrixBoundaryRegularizationAdmissible
    (M : ℝ → ℕ → ℕ → ℝ) : Prop :=
  ∀ᶠ r in 𝓝[<] (1 : ℝ),
    schwarzschildParikhWilczekCountableMatrixMomentAdmissible (M r)

def PWCountableMatrixBoundaryRegularizationPositive
    (M : ℝ → ℕ → ℕ → ℝ) : Prop :=
  ∀ᶠ r in 𝓝[<] (1 : ℝ), ∀ i j, 0 ≤ M r i j

theorem tendsto_pwCountableMatrixMoments_of_three_samples
    {M : ℝ → ℕ → ℕ → ℝ} {L1 L2 L5 : ℝ}
    (hM : PWCountableMatrixBoundaryRegularizationAdmissible M)
    (h1 : Tendsto
      (fun r => schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) 0)
      (𝓝[<] (1 : ℝ)) (𝓝 L1))
    (h2 : Tendsto
      (fun r => schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) I)
      (𝓝[<] (1 : ℝ)) (𝓝 L2))
    (h5 : Tendsto
      (fun r => schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) (2 * I))
      (𝓝[<] (1 : ℝ)) (𝓝 L5)) :
    Tendsto
        (fun r => schwarzschildParikhWilczekCountableMatrixMomentZero (M r))
        (𝓝[<] (1 : ℝ)) (𝓝 (pwBoundaryLimitMomentZero L1 L2 L5)) ∧
      Tendsto
        (fun r => schwarzschildParikhWilczekCountableMatrixMomentOne (M r))
        (𝓝[<] (1 : ℝ)) (𝓝 (pwBoundaryLimitMomentOne L1 L2 L5)) ∧
      Tendsto
        (fun r => schwarzschildParikhWilczekCountableMatrixMomentTwo (M r))
        (𝓝[<] (1 : ℝ)) (𝓝 (pwBoundaryLimitMomentTwo L1 L2 L5)) := by
  have hA : Tendsto
      (fun r => pwBoundaryLimitMomentZero
        (schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) 0)
        (schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) I)
        (schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) (2 * I)))
      (𝓝[<] (1 : ℝ)) (𝓝 (pwBoundaryLimitMomentZero L1 L2 L5)) := by
    unfold pwBoundaryLimitMomentZero
    simpa using
      (((h5.sub (h2.const_mul 4)).add (h1.const_mul 3)).div_const 12)
  have hB : Tendsto
      (fun r => pwBoundaryLimitMomentOne
        (schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) 0)
        (schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) I)
        (schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) (2 * I)))
      (𝓝[<] (1 : ℝ)) (𝓝 (pwBoundaryLimitMomentOne L1 L2 L5)) := by
    unfold pwBoundaryLimitMomentOne
    simpa using
      ((((h2.const_mul 8).sub (h1.const_mul 7)).sub h5).div_const 4)
  have hC : Tendsto
      (fun r => pwBoundaryLimitMomentTwo
        (schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) 0)
        (schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) I)
        (schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) (2 * I)))
      (𝓝[<] (1 : ℝ)) (𝓝 (pwBoundaryLimitMomentTwo L1 L2 L5)) := by
    unfold pwBoundaryLimitMomentTwo
    simpa using
      ((((h1.const_mul 15).sub (h2.const_mul 10)).add h5).div_const 6)
  have hEqA :
      (fun r => schwarzschildParikhWilczekCountableMatrixMomentZero (M r)) =ᶠ[𝓝[<] (1 : ℝ)]
        fun r => pwBoundaryLimitMomentZero
          (schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) 0)
          (schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) I)
          (schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) (2 * I)) :=
    hM.mono fun r hr => (pwCountableMatrixMoments_eq_three_samples hr).1
  have hEqB :
      (fun r => schwarzschildParikhWilczekCountableMatrixMomentOne (M r)) =ᶠ[𝓝[<] (1 : ℝ)]
        fun r => pwBoundaryLimitMomentOne
          (schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) 0)
          (schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) I)
          (schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) (2 * I)) :=
    hM.mono fun r hr => (pwCountableMatrixMoments_eq_three_samples hr).2.1
  have hEqC :
      (fun r => schwarzschildParikhWilczekCountableMatrixMomentTwo (M r)) =ᶠ[𝓝[<] (1 : ℝ)]
        fun r => pwBoundaryLimitMomentTwo
          (schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) 0)
          (schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) I)
          (schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) (2 * I)) :=
    hM.mono fun r hr => (pwCountableMatrixMoments_eq_three_samples hr).2.2
  exact ⟨hA.congr' hEqA.symm, hB.congr' hEqB.symm, hC.congr' hEqC.symm⟩

theorem tendsto_pwCountableMatrixResidualEnergy_of_three_samples
    {M : ℝ → ℕ → ℕ → ℝ} {L1 L2 L5 : ℝ}
    (hM : PWCountableMatrixBoundaryRegularizationAdmissible M)
    (h1 : Tendsto
      (fun r => schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) 0)
      (𝓝[<] (1 : ℝ)) (𝓝 L1))
    (h2 : Tendsto
      (fun r => schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) I)
      (𝓝[<] (1 : ℝ)) (𝓝 L2))
    (h5 : Tendsto
      (fun r => schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) (2 * I))
      (𝓝[<] (1 : ℝ)) (𝓝 L5))
    (s : ℂ) :
    Tendsto
      (fun r => schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) s)
      (𝓝[<] (1 : ℝ)) (𝓝 (pwBoundaryResidualLimit L1 L2 L5 s)) := by
  obtain ⟨hA, hB, hC⟩ :=
    tendsto_pwCountableMatrixMoments_of_three_samples hM h1 h2 h5
  have hpoly : Tendsto
      (fun r => schwarzschildParikhWilczekCountableMatrixResidualPolynomial (M r) s)
      (𝓝[<] (1 : ℝ)) (𝓝 (pwBoundaryResidualLimit L1 L2 L5 s)) := by
    unfold schwarzschildParikhWilczekCountableMatrixResidualPolynomial
      pwBoundaryResidualLimit
    exact ((hA.mul_const _).add (hB.mul_const _)).add hC
  have hEq :
      (fun r => schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) s) =ᶠ[𝓝[<] (1 : ℝ)]
        fun r => schwarzschildParikhWilczekCountableMatrixResidualPolynomial (M r) s :=
    hM.mono fun r hr =>
      schwarzschildParikhWilczekCountableMatrixResidualEnergy_three_moment hr s
  exact hpoly.congr' hEq.symm

theorem tendsto_pwCountableMatrixCrossGradeEnergy_of_three_samples
    {M : ℝ → ℕ → ℕ → ℝ} {L1 L2 L5 : ℝ}
    (hM : PWCountableMatrixBoundaryRegularizationAdmissible M)
    (h1 : Tendsto
      (fun r => schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) 0)
      (𝓝[<] (1 : ℝ)) (𝓝 L1))
    (h2 : Tendsto
      (fun r => schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) I)
      (𝓝[<] (1 : ℝ)) (𝓝 L2))
    (h5 : Tendsto
      (fun r => schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) (2 * I))
      (𝓝[<] (1 : ℝ)) (𝓝 L5))
    (s : ℂ) :
    Tendsto
      (fun r => schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy (M r) s)
      (𝓝[<] (1 : ℝ)) (𝓝 (pwBoundaryCrossGradeEnergyLimit L1 L2 L5 s)) := by
  have hres := tendsto_pwCountableMatrixResidualEnergy_of_three_samples hM h1 h2 h5 s
  have hmul : Tendsto
      (fun r => schwarzschildParikhWilczekBorelWallFactor s ^ (2 : ℕ) *
        schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) s)
      (𝓝[<] (1 : ℝ)) (𝓝 (pwBoundaryCrossGradeEnergyLimit L1 L2 L5 s)) := by
    unfold pwBoundaryCrossGradeEnergyLimit
    exact hres.const_mul _
  have hEq :
      (fun r => schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy (M r) s) =ᶠ[𝓝[<] (1 : ℝ)]
        fun r => schwarzschildParikhWilczekBorelWallFactor s ^ (2 : ℕ) *
          schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) s := by
    filter_upwards with r
    exact schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy_factorization (M r) s
  exact hmul.congr' hEq.symm

theorem pwCountableMatrixMomentZero_nonneg
    {M : ℕ → ℕ → ℝ} (hM : ∀ i j, 0 ≤ M i j) :
    0 ≤ schwarzschildParikhWilczekCountableMatrixMomentZero M := by
  rw [schwarzschildParikhWilczekCountableMatrixMomentZero]
  exact tsum_nonneg fun ij => hM ij.1 ij.2

theorem pwCountableMatrixMomentOne_nonneg
    {M : ℕ → ℕ → ℝ} (hM : ∀ i j, 0 ≤ M i j) :
    0 ≤ schwarzschildParikhWilczekCountableMatrixMomentOne M := by
  rw [schwarzschildParikhWilczekCountableMatrixMomentOne]
  apply tsum_nonneg
  intro ij
  apply mul_nonneg (hM ij.1 ij.2)
  apply add_nonneg <;>
    rw [schwarzschildParikhWilczekBorelGradeShift] <;> positivity

theorem pwCountableMatrixMomentTwo_nonneg
    {M : ℕ → ℕ → ℝ} (hM : ∀ i j, 0 ≤ M i j) :
    0 ≤ schwarzschildParikhWilczekCountableMatrixMomentTwo M := by
  rw [schwarzschildParikhWilczekCountableMatrixMomentTwo]
  apply tsum_nonneg
  intro ij
  apply mul_nonneg
  · apply mul_nonneg (hM ij.1 ij.2)
    rw [schwarzschildParikhWilczekBorelGradeShift]
    positivity
  · rw [schwarzschildParikhWilczekBorelGradeShift]
    positivity

theorem pwBoundaryLimitMoments_nonneg_of_positive_regularization
    {M : ℝ → ℕ → ℕ → ℝ} {L1 L2 L5 : ℝ}
    (hM : PWCountableMatrixBoundaryRegularizationAdmissible M)
    (hpos : PWCountableMatrixBoundaryRegularizationPositive M)
    (h1 : Tendsto
      (fun r => schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) 0)
      (𝓝[<] (1 : ℝ)) (𝓝 L1))
    (h2 : Tendsto
      (fun r => schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) I)
      (𝓝[<] (1 : ℝ)) (𝓝 L2))
    (h5 : Tendsto
      (fun r => schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) (2 * I))
      (𝓝[<] (1 : ℝ)) (𝓝 L5)) :
    0 ≤ pwBoundaryLimitMomentZero L1 L2 L5 ∧
      0 ≤ pwBoundaryLimitMomentOne L1 L2 L5 ∧
      0 ≤ pwBoundaryLimitMomentTwo L1 L2 L5 := by
  obtain ⟨hA, hB, hC⟩ :=
    tendsto_pwCountableMatrixMoments_of_three_samples hM h1 h2 h5
  have hAe : ∀ᶠ r in 𝓝[<] (1 : ℝ),
      0 ≤ schwarzschildParikhWilczekCountableMatrixMomentZero (M r) :=
    hpos.mono fun r hr => pwCountableMatrixMomentZero_nonneg hr
  have hBe : ∀ᶠ r in 𝓝[<] (1 : ℝ),
      0 ≤ schwarzschildParikhWilczekCountableMatrixMomentOne (M r) :=
    hpos.mono fun r hr => pwCountableMatrixMomentOne_nonneg hr
  have hCe : ∀ᶠ r in 𝓝[<] (1 : ℝ),
      0 ≤ schwarzschildParikhWilczekCountableMatrixMomentTwo (M r) :=
    hpos.mono fun r hr => pwCountableMatrixMomentTwo_nonneg hr
  have hA0 : 0 ≤ pwBoundaryLimitMomentZero L1 L2 L5 :=
    ge_of_tendsto hA hAe
  have hB0 : 0 ≤ pwBoundaryLimitMomentOne L1 L2 L5 :=
    ge_of_tendsto hB hBe
  have hC0 : 0 ≤ pwBoundaryLimitMomentTwo L1 L2 L5 :=
    ge_of_tendsto hC hCe
  exact ⟨hA0, hB0, hC0⟩

theorem pwBoundaryResidualLimit_pos_of_nonnegative_nonzero
    {L1 L2 L5 : ℝ}
    (hA : 0 ≤ pwBoundaryLimitMomentZero L1 L2 L5)
    (hB : 0 ≤ pwBoundaryLimitMomentOne L1 L2 L5)
    (hC : 0 ≤ pwBoundaryLimitMomentTwo L1 L2 L5)
    (hnonzero :
      pwBoundaryLimitMomentZero L1 L2 L5 +
        pwBoundaryLimitMomentOne L1 L2 L5 +
        pwBoundaryLimitMomentTwo L1 L2 L5 ≠ 0)
    {s : ℂ} (hs : 1 < schwarzschildParikhWilczekBorelSpectralCoordinate s) :
    0 < pwBoundaryResidualLimit L1 L2 L5 s := by
  let x := schwarzschildParikhWilczekBorelSpectralCoordinate s
  have hx : 1 < x := hs
  have hx2 : 1 ≤ x ^ (2 : ℕ) := by nlinarith
  have hAx : pwBoundaryLimitMomentZero L1 L2 L5 ≤
      pwBoundaryLimitMomentZero L1 L2 L5 * x ^ (2 : ℕ) :=
    by simpa using mul_le_mul_of_nonneg_left hx2 hA
  have hBx : pwBoundaryLimitMomentOne L1 L2 L5 ≤
      pwBoundaryLimitMomentOne L1 L2 L5 * x :=
    by simpa using mul_le_mul_of_nonneg_left hx.le hB
  have hsum : 0 <
      pwBoundaryLimitMomentZero L1 L2 L5 +
        pwBoundaryLimitMomentOne L1 L2 L5 +
        pwBoundaryLimitMomentTwo L1 L2 L5 := by
    have hnonneg : 0 ≤
        pwBoundaryLimitMomentZero L1 L2 L5 +
          pwBoundaryLimitMomentOne L1 L2 L5 +
          pwBoundaryLimitMomentTwo L1 L2 L5 := by positivity
    exact lt_of_le_of_ne hnonneg (Ne.symm hnonzero)
  rw [pwBoundaryResidualLimit]
  change 0 < pwBoundaryLimitMomentZero L1 L2 L5 * x ^ (2 : ℕ) +
    pwBoundaryLimitMomentOne L1 L2 L5 * x +
    pwBoundaryLimitMomentTwo L1 L2 L5
  linarith

theorem pwBoundaryCrossGradeEnergyLimit_eq_zero_iff_wall
    {L1 L2 L5 : ℝ}
    (hA : 0 ≤ pwBoundaryLimitMomentZero L1 L2 L5)
    (hB : 0 ≤ pwBoundaryLimitMomentOne L1 L2 L5)
    (hC : 0 ≤ pwBoundaryLimitMomentTwo L1 L2 L5)
    (hnonzero :
      pwBoundaryLimitMomentZero L1 L2 L5 +
        pwBoundaryLimitMomentOne L1 L2 L5 +
        pwBoundaryLimitMomentTwo L1 L2 L5 ≠ 0)
    (rho : XiDivisorSupport) :
    pwBoundaryCrossGradeEnergyLimit L1 L2 L5 (rho : ℂ) = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [pwBoundaryCrossGradeEnergyLimit]
  have hres : 0 < pwBoundaryResidualLimit L1 L2 L5 (rho : ℂ) :=
    pwBoundaryResidualLimit_pos_of_nonnegative_nonzero hA hB hC hnonzero
      (schwarzschildParikhWilczekBorelSpectralCoordinate_gt_one rho)
  constructor
  · intro hzero
    have hwallSq : schwarzschildParikhWilczekBorelWallFactor (rho : ℂ) ^ (2 : ℕ) = 0 :=
      (mul_eq_zero.mp hzero).resolve_right hres.ne'
    have hwall : schwarzschildParikhWilczekBorelWallFactor (rho : ℂ) = 0 :=
      (sq_eq_zero_iff).mp hwallSq
    rw [schwarzschildParikhWilczekBorelWallFactor] at hwall
    rcases mul_eq_zero.mp hwall with him | hcenter
    · exact False.elim (xi_divisor_support_im_ne_zero rho (by linarith))
    · linarith
  · intro hre
    rw [schwarzschildParikhWilczekBorelWallFactor, hre]
    norm_num

theorem riemannHypothesis_iff_pwBoundaryCrossGradeEnergyLimit_zero
    {L1 L2 L5 : ℝ}
    (hA : 0 ≤ pwBoundaryLimitMomentZero L1 L2 L5)
    (hB : 0 ≤ pwBoundaryLimitMomentOne L1 L2 L5)
    (hC : 0 ≤ pwBoundaryLimitMomentTwo L1 L2 L5)
    (hnonzero :
      pwBoundaryLimitMomentZero L1 L2 L5 +
        pwBoundaryLimitMomentOne L1 L2 L5 +
        pwBoundaryLimitMomentTwo L1 L2 L5 ≠ 0) :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        pwBoundaryCrossGradeEnergyLimit L1 L2 L5 (rho : ℂ) = 0 := by
  constructor
  · intro hRH rho
    exact (pwBoundaryCrossGradeEnergyLimit_eq_zero_iff_wall
      hA hB hC hnonzero rho).mpr (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho =>
      (pwBoundaryCrossGradeEnergyLimit_eq_zero_iff_wall
        hA hB hC hnonzero rho).mp (h rho)

theorem pwPositiveBoundaryRegularization_blind_or_exactReceiver
    {M : ℝ → ℕ → ℕ → ℝ} {L1 L2 L5 : ℝ}
    (hM : PWCountableMatrixBoundaryRegularizationAdmissible M)
    (hpos : PWCountableMatrixBoundaryRegularizationPositive M)
    (h1 : Tendsto
      (fun r => schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) 0)
      (𝓝[<] (1 : ℝ)) (𝓝 L1))
    (h2 : Tendsto
      (fun r => schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) I)
      (𝓝[<] (1 : ℝ)) (𝓝 L2))
    (h5 : Tendsto
      (fun r => schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) (2 * I))
      (𝓝[<] (1 : ℝ)) (𝓝 L5)) :
    ((pwBoundaryLimitMomentZero L1 L2 L5 = 0 ∧
        pwBoundaryLimitMomentOne L1 L2 L5 = 0 ∧
        pwBoundaryLimitMomentTwo L1 L2 L5 = 0) ∧
      ∀ s : ℂ, pwBoundaryCrossGradeEnergyLimit L1 L2 L5 s = 0) ∨
    (0 < pwBoundaryLimitMomentZero L1 L2 L5 +
        pwBoundaryLimitMomentOne L1 L2 L5 +
        pwBoundaryLimitMomentTwo L1 L2 L5 ∧
      (RiemannHypothesis ↔
        ∀ rho : XiDivisorSupport,
          pwBoundaryCrossGradeEnergyLimit L1 L2 L5 (rho : ℂ) = 0)) := by
  obtain ⟨hA, hB, hC⟩ :=
    pwBoundaryLimitMoments_nonneg_of_positive_regularization hM hpos h1 h2 h5
  by_cases hsum :
      pwBoundaryLimitMomentZero L1 L2 L5 +
        pwBoundaryLimitMomentOne L1 L2 L5 +
        pwBoundaryLimitMomentTwo L1 L2 L5 = 0
  · left
    have hA0 : pwBoundaryLimitMomentZero L1 L2 L5 = 0 := by nlinarith
    have hB0 : pwBoundaryLimitMomentOne L1 L2 L5 = 0 := by nlinarith
    have hC0 : pwBoundaryLimitMomentTwo L1 L2 L5 = 0 := by nlinarith
    refine ⟨⟨hA0, hB0, hC0⟩, ?_⟩
    intro s
    simp [pwBoundaryCrossGradeEnergyLimit, pwBoundaryResidualLimit, hA0, hB0, hC0]
  · right
    have hsumpos : 0 <
        pwBoundaryLimitMomentZero L1 L2 L5 +
          pwBoundaryLimitMomentOne L1 L2 L5 +
          pwBoundaryLimitMomentTwo L1 L2 L5 := by
      have hsum0 : 0 ≤
          pwBoundaryLimitMomentZero L1 L2 L5 +
            pwBoundaryLimitMomentOne L1 L2 L5 +
            pwBoundaryLimitMomentTwo L1 L2 L5 := by positivity
      exact lt_of_le_of_ne hsum0 (Ne.symm hsum)
    exact ⟨hsumpos,
      riemannHypothesis_iff_pwBoundaryCrossGradeEnergyLimit_zero hA hB hC hsum⟩

def PWPositiveBoundaryRegularizationThreeMomentNoGo : Prop :=
  ∀ (M : ℝ → ℕ → ℕ → ℝ) (L1 L2 L5 : ℝ),
    PWCountableMatrixBoundaryRegularizationAdmissible M →
    PWCountableMatrixBoundaryRegularizationPositive M →
    Tendsto
      (fun r => schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) 0)
      (𝓝[<] (1 : ℝ)) (𝓝 L1) →
    Tendsto
      (fun r => schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) I)
      (𝓝[<] (1 : ℝ)) (𝓝 L2) →
    Tendsto
      (fun r => schwarzschildParikhWilczekCountableMatrixResidualEnergy (M r) (2 * I))
      (𝓝[<] (1 : ℝ)) (𝓝 L5) →
    ((pwBoundaryLimitMomentZero L1 L2 L5 = 0 ∧
        pwBoundaryLimitMomentOne L1 L2 L5 = 0 ∧
        pwBoundaryLimitMomentTwo L1 L2 L5 = 0) ∧
      ∀ s : ℂ, pwBoundaryCrossGradeEnergyLimit L1 L2 L5 s = 0) ∨
    (0 < pwBoundaryLimitMomentZero L1 L2 L5 +
        pwBoundaryLimitMomentOne L1 L2 L5 +
        pwBoundaryLimitMomentTwo L1 L2 L5 ∧
      (RiemannHypothesis ↔
        ∀ rho : XiDivisorSupport,
          pwBoundaryCrossGradeEnergyLimit L1 L2 L5 (rho : ℂ) = 0))

theorem pwPositiveBoundaryRegularization_threeMoment_noGo :
    PWPositiveBoundaryRegularizationThreeMomentNoGo := by
  intro M L1 L2 L5 hM hpos h1 h2 h5
  exact pwPositiveBoundaryRegularization_blind_or_exactReceiver hM hpos h1 h2 h5

end
end RHTower

