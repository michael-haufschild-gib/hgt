import GaloisForLFunctions.RHTower.XiTransverseValuationSzegoMetric
import GaloisForLFunctions.RHTower.GammaConductorSchurCapacity

/-!
# Gamma Schur elimination is valuation translation

The diagonal prime--Gamma model has an infinite scalar-capacity obstruction.  The successive
valuation differences of the actual transverse Xi source supply the missing coherent prime
covariance.  After the source-forced rational Gamma renormalization, the normalized
prime-to-conductor cross-coordinate is exactly the first half-shifted valuation coordinate.

Consequently its Schur complement removes valuation depth zero and leaves exactly the same
Szego kernel multiplied by the two prime disk nodes.  In other words, archimedean Schur
elimination advances the prime-valuation filtration by one step.  This is the Hilbert-space
counterpart of the finite-fusion valuation successor law.

The construction is source-side.  It does not assert the remaining contractive transport from
this prime--Gamma block to the Xi boundary leakage operator.
-/

namespace RHTower

noncomputable section

open scoped BigOperators
open Matrix

/-- Unit aperture identifies the prime disk node with the reciprocal prime. -/
theorem xiTransversePrimeApertureDiskNode_one_eq_inv (p : Nat.Primes) :
    xiTransversePrimeApertureDiskNode 1 p = ((p : ℝ))⁻¹ := by
  rw [xiTransversePrimeApertureDiskNode]
  norm_num
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [Real.exp_neg, Real.exp_log hp]

/-- Distinct primes give distinct unit-aperture disk nodes. -/
theorem xiTransversePrimeApertureDiskNode_one_injective :
    Function.Injective (fun p : Nat.Primes =>
      xiTransversePrimeApertureDiskNode 1 p) := by
  intro p q hpq
  change xiTransversePrimeApertureDiskNode 1 p =
    xiTransversePrimeApertureDiskNode 1 q at hpq
  rw [xiTransversePrimeApertureDiskNode_one_eq_inv,
    xiTransversePrimeApertureDiskNode_one_eq_inv] at hpq
  have hreal : (p : ℝ) = (q : ℝ) := by
    have h := congrArg (fun x : ℝ => x⁻¹) hpq
    simpa using h
  apply Subtype.ext
  exact_mod_cast hreal

/-- The positive rational Gamma gauge which exposes the valuation Hardy coordinate. -/
def gammaValuationHardyRenormalizer (p : Nat.Primes) : ℝ :=
  (((p : ℝ) ^ 2 + 1) ^ 2) /
    ((p : ℝ) ^ 2 * ((p : ℝ) + 1) ^ 2)

theorem gammaValuationHardyRenormalizer_pos (p : Nat.Primes) :
    0 < gammaValuationHardyRenormalizer p := by
  unfold gammaValuationHardyRenormalizer
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  apply div_pos
  · positivity
  · exact mul_pos (sq_pos_of_pos hp) (sq_pos_of_pos (by positivity))

/-- The half-shifted first valuation difference.  The half shift is forced by the square-root
decay of the normalized Gamma cross-coordinate. -/
def xiTransversePrimeHalfShiftedValuationCoordinate
    (p : Nat.Primes) (e : ℕ) : ℝ :=
  Real.sqrt (xiTransversePrimeApertureDiskNode 1 p) *
    xiTransversePrimeValuationIncrement 1 e p

/-- The Gamma-coupled vacuum coordinate. -/
def xiTransversePrimeHalfShiftedFirstValuationCoordinate (p : Nat.Primes) : ℝ :=
  xiTransversePrimeHalfShiftedValuationCoordinate p 0

/-- Valuation translation is the Hardy backward-shift eigenvector law at the prime disk node. -/
theorem xiTransversePrimeHalfShiftedValuationCoordinate_succ
    (p : Nat.Primes) (e : ℕ) :
    xiTransversePrimeHalfShiftedValuationCoordinate p (e + 1) =
      xiTransversePrimeApertureDiskNode 1 p *
        xiTransversePrimeHalfShiftedValuationCoordinate p e := by
  simp only [xiTransversePrimeHalfShiftedValuationCoordinate,
    xiTransversePrimeValuationIncrement, pow_succ]
  ring

theorem xiTransversePrimeHalfShiftedFirstValuationCoordinate_eq (p : Nat.Primes) :
    xiTransversePrimeHalfShiftedFirstValuationCoordinate p =
      Real.sqrt (xiTransversePrimeApertureDiskNode 1 p) *
        (1 - xiTransversePrimeApertureDiskNode 1 p) := by
  simp [xiTransversePrimeHalfShiftedFirstValuationCoordinate,
    xiTransversePrimeHalfShiftedValuationCoordinate,
    xiTransversePrimeValuationIncrement]

theorem xiTransversePrimeHalfShiftedFirstValuationCoordinate_pos (p : Nat.Primes) :
    0 < xiTransversePrimeHalfShiftedFirstValuationCoordinate p := by
  rw [xiTransversePrimeHalfShiftedFirstValuationCoordinate_eq]
  exact mul_pos
    (Real.sqrt_pos.2 (xiTransversePrimeApertureDiskNode_pos 1 p))
    (sub_pos.mpr (xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p))

theorem gammaConductorPrimeNormalizedCross_neg (p : Nat.Primes) :
    gammaConductorPrimeNormalizedCross p < 0 := by
  rw [gammaConductorPrimeNormalizedCross]
  apply div_neg_of_neg_of_pos
  · rw [gammaConductorPrimeCross]
    apply semilocalArchimedeanSecondMomentCovarianceKernel_neg
    have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
    exact (Real.log_pos hp).ne'
  · exact Real.sqrt_pos.2 (gammaConductorPrimeVariance_pos p)

/-- Squared form of the exact Gamma-to-valuation coordinate identity. -/
theorem gammaValuationHardyCorrectedCross_sq (p : Nat.Primes) :
    (gammaValuationHardyRenormalizer p *
        gammaConductorPrimeNormalizedCross p) ^ 2 =
      (9 / 8 : ℝ) *
        xiTransversePrimeHalfShiftedFirstValuationCoordinate p ^ 2 := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hplus : (p : ℝ) + 1 ≠ 0 := by positivity
  have hquad : (p : ℝ) ^ 2 + 1 ≠ 0 := by positivity
  rw [mul_pow, gammaConductorPrimeNormalizedCross_sq,
    gammaConductorPrimeSchurCost_eq,
    xiTransversePrimeHalfShiftedFirstValuationCoordinate_eq,
    xiTransversePrimeApertureDiskNode_one_eq_inv, mul_pow,
    Real.sq_sqrt (inv_nonneg.mpr hp0.le)]
  unfold gammaValuationHardyRenormalizer
  field_simp [hp0.ne', hplus, hquad]

/-- The normalized Gamma cross-coordinate, after its explicit positive rational correction, is
exactly the first half-shifted valuation-Hardy coordinate. -/
theorem gammaValuationHardyCorrectedCross_eq (p : Nat.Primes) :
    gammaValuationHardyRenormalizer p *
        gammaConductorPrimeNormalizedCross p =
      -(3 * Real.sqrt 2 / 4) *
        xiTransversePrimeHalfShiftedFirstValuationCoordinate p := by
  let L := gammaValuationHardyRenormalizer p *
    gammaConductorPrimeNormalizedCross p
  let C := (3 * Real.sqrt 2 / 4) *
    xiTransversePrimeHalfShiftedFirstValuationCoordinate p
  have hconst : (3 * Real.sqrt 2 / 4 : ℝ) ^ 2 = 9 / 8 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsq : L ^ 2 = C ^ 2 := by
    calc
      L ^ 2 = (9 / 8 : ℝ) *
          xiTransversePrimeHalfShiftedFirstValuationCoordinate p ^ 2 := by
        simpa [L] using gammaValuationHardyCorrectedCross_sq p
      _ = C ^ 2 := by
        dsimp only [C]
        rw [mul_pow, hconst]
  have hLneg : L < 0 := by
    exact mul_neg_of_pos_of_neg (gammaValuationHardyRenormalizer_pos p)
      (gammaConductorPrimeNormalizedCross_neg p)
  have hCpos : 0 < C := by
    exact mul_pos (by positivity)
      (xiTransversePrimeHalfShiftedFirstValuationCoordinate_pos p)
  have hfactor : (L - C) * (L + C) = 0 := by
    nlinarith
  have hLC : L = -C := by
    rcases mul_eq_zero.mp hfactor with hminus | hplus
    · nlinarith
    · nlinarith
  simpa [L, C] using hLC

/-- The completed half-shifted valuation Gram across two primes. -/
def xiTransverseGammaValuationSzegoKernel
    (p q : Nat.Primes) : ℝ :=
  let x := xiTransversePrimeApertureDiskNode 1 p
  let y := xiTransversePrimeApertureDiskNode 1 q
  Real.sqrt x * Real.sqrt y * (1 - x) * (1 - y) / (1 - x * y)

/-- **Gamma Schur elimination is valuation translation.**  Eliminating the corrected Gamma
conductor coordinate removes valuation depth zero and leaves the same completed valuation kernel
shifted by one depth. -/
theorem xiTransverseGammaValuationSzegoKernel_schurResidual_eq_shift
    (p q : Nat.Primes) :
    xiTransverseGammaValuationSzegoKernel p q -
        (gammaValuationHardyRenormalizer p *
            gammaConductorPrimeNormalizedCross p) *
          (gammaValuationHardyRenormalizer q *
            gammaConductorPrimeNormalizedCross q) / (9 / 8 : ℝ) =
      xiTransversePrimeApertureDiskNode 1 p *
        xiTransversePrimeApertureDiskNode 1 q *
          xiTransverseGammaValuationSzegoKernel p q := by
  let x := xiTransversePrimeApertureDiskNode 1 p
  let y := xiTransversePrimeApertureDiskNode 1 q
  have hx0 : 0 ≤ x := (xiTransversePrimeApertureDiskNode_pos 1 p).le
  have hy0 : 0 ≤ y := (xiTransversePrimeApertureDiskNode_pos 1 q).le
  have hx1 : x < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hy1 : y < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) q
  have hxy : 1 - x * y ≠ 0 := by
    have : x * y < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_left hx0 hx1 hy1.le
    linarith
  have hconst : (3 * Real.sqrt 2 / 4 : ℝ) ^ 2 = 9 / 8 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [gammaValuationHardyCorrectedCross_eq,
    gammaValuationHardyCorrectedCross_eq,
    xiTransversePrimeHalfShiftedFirstValuationCoordinate_eq,
    xiTransversePrimeHalfShiftedFirstValuationCoordinate_eq]
  simp only [xiTransverseGammaValuationSzegoKernel]
  rw [show xiTransversePrimeApertureDiskNode 1 p = x by rfl,
    show xiTransversePrimeApertureDiskNode 1 q = y by rfl]
  field_simp [hxy]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- The first `N` half-shifted valuation coordinates of a prime. -/
def xiTransversePrimeHalfShiftedValuationFeature
    (N : ℕ) (p : Nat.Primes) : Fin N → ℝ :=
  fun e => xiTransversePrimeHalfShiftedValuationCoordinate p e

/-- Finite coherent prime covariance supplied by the valuation tower. -/
def xiTransversePrimeHalfShiftedValuationKernel
    (N : ℕ) (p q : Nat.Primes) : ℝ :=
  ∑ e : Fin N, xiTransversePrimeHalfShiftedValuationFeature N p e *
    xiTransversePrimeHalfShiftedValuationFeature N q e

/-- The first `N` marked valuation coordinates sampled on an `N`-prime packet. -/
def xiTransversePrimeHalfShiftedValuationSamplingMatrix
    {N : ℕ} (p : Fin N → Nat.Primes) : Matrix (Fin N) (Fin N) ℝ :=
  fun e j => xiTransversePrimeHalfShiftedValuationFeature N (p j) e

/-- The prime sampling matrix is a weighted Vandermonde in the actual reciprocal-prime nodes. -/
theorem xiTransversePrimeHalfShiftedValuationSamplingMatrix_factorization
    {N : ℕ} (p : Fin N → Nat.Primes) :
    xiTransversePrimeHalfShiftedValuationSamplingMatrix p =
      (Matrix.vandermonde
        (fun j => xiTransversePrimeApertureDiskNode 1 (p j)))ᵀ *
      Matrix.diagonal
        (fun j => Real.sqrt (xiTransversePrimeApertureDiskNode 1 (p j)) *
          (1 - xiTransversePrimeApertureDiskNode 1 (p j))) := by
  classical
  ext e j
  rw [Matrix.mul_diagonal]
  simp [xiTransversePrimeHalfShiftedValuationSamplingMatrix,
    xiTransversePrimeHalfShiftedValuationFeature,
    xiTransversePrimeHalfShiftedValuationCoordinate,
    xiTransversePrimeValuationIncrement, Matrix.vandermonde]
  ring

/-- Valuation depth is an intrinsic finite marking: the first `N` coordinates reconstruct every
injective `N`-prime packet. -/
theorem xiTransversePrimeHalfShiftedValuationSamplingMatrix_det_ne_zero
    {N : ℕ} {p : Fin N → Nat.Primes} (hp : Function.Injective p) :
    (xiTransversePrimeHalfShiftedValuationSamplingMatrix p).det ≠ 0 := by
  let q : Fin N → ℝ := fun j => xiTransversePrimeApertureDiskNode 1 (p j)
  let d : Fin N → ℝ := fun j => Real.sqrt (q j) * (1 - q j)
  have hq : Function.Injective q :=
    xiTransversePrimeApertureDiskNode_one_injective.comp hp
  have hd : ∀ j, d j ≠ 0 := by
    intro j
    apply mul_ne_zero
    · exact (Real.sqrt_pos.2
        (xiTransversePrimeApertureDiskNode_pos 1 (p j))).ne'
    · exact (sub_pos.mpr
        (xiTransversePrimeApertureDiskNode_lt_one (by norm_num) (p j))).ne'
  rw [xiTransversePrimeHalfShiftedValuationSamplingMatrix_factorization,
    Matrix.det_mul, Matrix.det_transpose]
  apply mul_ne_zero
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr hq
  · rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    exact fun j _ => hd j

/-- Every nonempty finite valuation prefix gives a positive prime--Gamma block with the exact
scalar conductor capacity `9/8`.  The old diagonal-capacity obstruction is therefore resolved by
the source's explicit coherent valuation covariance. -/
theorem xiTransverseGammaValuationFiniteBlock_nonneg
    {N : ℕ} (hN : 0 < N) {I : Type*} [Fintype I]
    (p : I → Nat.Primes) (u : I → ℝ) (v : ℝ) :
    0 ≤
      (∑ i, ∑ j,
        xiTransversePrimeHalfShiftedValuationKernel N (p i) (p j) * u i * u j) +
      2 * v *
        (∑ i, gammaValuationHardyRenormalizer (p i) *
          gammaConductorPrimeNormalizedCross (p i) * u i) +
      (9 / 8 : ℝ) * v ^ 2 := by
  let H : Fin N → I → ℝ := fun e i =>
    xiTransversePrimeHalfShiftedValuationFeature N (p i) e
  let S : Fin N → ℝ := fun e => ∑ i, H e i * u i
  let e0 : Fin N := ⟨0, hN⟩
  have henergy :
      (∑ i, ∑ j,
        xiTransversePrimeHalfShiftedValuationKernel N (p i) (p j) * u i * u j) =
        ∑ e, S e ^ 2 := by
    unfold xiTransversePrimeHalfShiftedValuationKernel
    simp_rw [Finset.sum_mul]
    let F : I → I → Fin N → ℝ := fun i j e =>
      xiTransversePrimeHalfShiftedValuationFeature N (p i) e *
        xiTransversePrimeHalfShiftedValuationFeature N (p j) e * u i * u j
    change (∑ i, ∑ j, ∑ e, F i j e) = ∑ e, S e ^ 2
    calc
      (∑ i, ∑ j, ∑ e, F i j e) = ∑ i, ∑ e, ∑ j, F i j e := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
      _ = ∑ e, ∑ i, ∑ j, F i j e := by rw [Finset.sum_comm]
      _ = ∑ e, S e ^ 2 := by
        apply Finset.sum_congr rfl
        intro e he
        dsimp only [F, S, H]
        rw [sq, Fintype.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hcross :
      (∑ i, gammaValuationHardyRenormalizer (p i) *
          gammaConductorPrimeNormalizedCross (p i) * u i) =
        -(3 * Real.sqrt 2 / 4) * S e0 := by
    calc
      (∑ i, gammaValuationHardyRenormalizer (p i) *
          gammaConductorPrimeNormalizedCross (p i) * u i) =
          ∑ i, (-(3 * Real.sqrt 2 / 4) *
            xiTransversePrimeHalfShiftedFirstValuationCoordinate (p i)) * u i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [gammaValuationHardyCorrectedCross_eq]
      _ = -(3 * Real.sqrt 2 / 4) * S e0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp [H, e0, xiTransversePrimeHalfShiftedValuationFeature,
          xiTransversePrimeHalfShiftedFirstValuationCoordinate,
          xiTransversePrimeHalfShiftedValuationCoordinate]
        ring
  have hfirst : S e0 ^ 2 ≤ ∑ e, S e ^ 2 :=
    Finset.single_le_sum (fun e _ => sq_nonneg (S e)) (Finset.mem_univ e0)
  have hconst : (3 * Real.sqrt 2 / 4 : ℝ) ^ 2 = 9 / 8 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [henergy, hcross]
  nlinarith [sq_nonneg (S e0 - (3 * Real.sqrt 2 / 4) * v)]

end

end RHTower
