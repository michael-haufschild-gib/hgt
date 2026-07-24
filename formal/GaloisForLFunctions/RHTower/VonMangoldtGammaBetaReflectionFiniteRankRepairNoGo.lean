import GaloisForLFunctions.RHTower.VonMangoldtGammaFactorialBetaReflection
import GaloisForLFunctions.HTGeometry.EventualNegDefFromEntrywise
import GaloisForLFunctions.HTGeometry.KreinLangerInertia
import GaloisForLFunctions.HTGeometry.ReciprocalFactorialHankelInertia

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.ReciprocalFactorialHankel

/-- Complexification of the cofinal factorial/Beta-reflected source on all
Borel orders below `n`. -/
def betaFactorialAllOrderComplexGram (n : ℕ) (x : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    (infiniteVonMangoldtGammaFactorialTraceGram x
      (fun k : Fin n => (k : ℕ)) i j : ℂ)

/-- First-prime projective limit on all Borel orders below `n`. -/
def betaFactorialAllOrderFirstPrimeLimit (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    ((Real.log 2) ^ ((i : ℕ) + (j : ℕ) + 2) /
      (((i : ℕ) + (j : ℕ) + 1).factorial : ℝ) : ℂ)

theorem tendsto_scaled_infiniteVonMangoldtGammaRawMoment_allOrder (m : ℕ) :
    Tendsto
      (fun x : ℝ =>
        (2 : ℝ) ^ (x + 1) * infiniteVonMangoldtGammaRawMoment x m)
      atTop (nhds ((Real.log 2) ^ (m + 1))) := by
  have hshift : Tendsto (fun x : ℝ => x + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_id
  have h := (tendsto_scaled_vonMangoldtLogMoment m).comp hshift
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [infiniteVonMangoldtGammaRawMoment_eq_vonMangoldtLogMoment hx]
  rfl

theorem tendsto_scaled_betaFactorialAllOrderComplexGram_apply
    {n : ℕ} (i j : Fin n) :
    Tendsto
      (fun x : ℝ =>
        Complex.ofReal ((2 : ℝ) ^ (x + 1)) *
          betaFactorialAllOrderComplexGram n x i j)
      atTop (nhds (betaFactorialAllOrderFirstPrimeLimit n i j)) := by
  have hreal :=
    (tendsto_scaled_infiniteVonMangoldtGammaRawMoment_allOrder
      ((i : ℕ) + (j : ℕ) + 1)).div_const
        ((((i : ℕ) + (j : ℕ) + 1).factorial : ℝ))
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  convert hcomplex using 1
  · funext x
    simp only [Function.comp_apply, betaFactorialAllOrderComplexGram,
      infiniteVonMangoldtGammaFactorialTraceGram, Complex.ofReal_mul,
      Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  · simp only [betaFactorialAllOrderFirstPrimeLimit, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_natCast]

def logTwoDiagonal (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => (((Real.log 2) ^ (i : ℕ) : ℝ) : ℂ))

def logTwoInverseDiagonal (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => ((((Real.log 2) ^ (i : ℕ))⁻¹ : ℝ) : ℂ))

theorem logTwoDiagonal_mul_inverse (n : ℕ) :
    logTwoDiagonal n * logTwoInverseDiagonal n = 1 := by
  have hclog_ne : Complex.log (2 : ℂ) ≠ 0 := by
    have heq : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
      (Complex.ofReal_log (by norm_num)).symm
    rw [heq]
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.log_pos (by norm_num)))
  rw [logTwoDiagonal, logTwoInverseDiagonal,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
      Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofNat_log]
    exact mul_inv_cancel₀ (pow_ne_zero _ hclog_ne)
  · simp [hij]

theorem logTwoInverse_mul_diagonal (n : ℕ) :
    logTwoInverseDiagonal n * logTwoDiagonal n = 1 := by
  have hclog_ne : Complex.log (2 : ℂ) ≠ 0 := by
    have heq : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
      (Complex.ofReal_log (by norm_num)).symm
    rw [heq]
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.log_pos (by norm_num)))
  rw [logTwoDiagonal, logTwoInverseDiagonal,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
      Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofNat_log]
    exact inv_mul_cancel₀ (pow_ne_zero _ hclog_ne)
  · simp [hij]

theorem logTwoInverseDiagonal_conjTranspose (n : ℕ) :
    (logTwoInverseDiagonal n)ᴴ = logTwoInverseDiagonal n := by
  have heq : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
    (Complex.ofReal_log (by norm_num)).symm
  have hstar : star (Complex.log (2 : ℂ)) = Complex.log (2 : ℂ) := by
    calc
      star (Complex.log (2 : ℂ)) = star (Real.log 2 : ℂ) :=
        congrArg star heq
      _ = (Real.log 2 : ℂ) := Complex.conj_ofReal _
      _ = Complex.log (2 : ℂ) := heq.symm
  ext i j
  by_cases hij : i = j
  · subst j
    simp [logTwoInverseDiagonal, Matrix.conjTranspose_apply, hstar]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [logTwoInverseDiagonal, Matrix.conjTranspose_apply, hij, hji]

theorem betaFactorialAllOrderFirstPrimeLimit_factorization (n : ℕ) :
    betaFactorialAllOrderFirstPrimeLimit n =
      (((Real.log 2) ^ 2 : ℝ) : ℂ) •
        (logTwoDiagonal n * complexH n * logTwoDiagonal n) := by
  ext i j
  simp only [betaFactorialAllOrderFirstPrimeLimit, Matrix.smul_apply,
    smul_eq_mul, logTwoDiagonal]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp [complexH, H_apply]
  rw [show (i : ℕ) + (j : ℕ) + 2 = 2 + (i : ℕ) + (j : ℕ) by omega,
    pow_add, pow_add]
  ring

/-- Odd-pivot flag frame after undoing logarithmic diagonal dressing. -/
def betaFactorialAllOrderNegativeFrame (m : ℕ) :
    Matrix (Fin (2 * m)) (Fin m) ℂ :=
  logTwoInverseDiagonal (2 * m) * oddInverseFlagFrame m

set_option maxHeartbeats 800000 in
theorem betaFactorialAllOrderNegativeFrame_compresses_limit (m : ℕ) :
    (betaFactorialAllOrderNegativeFrame m)ᴴ *
        betaFactorialAllOrderFirstPrimeLimit (2 * m) *
          betaFactorialAllOrderNegativeFrame m =
      Matrix.diagonal (fun a : Fin m =>
        ((((Real.log 2) ^ 2 * lastInvDiag
          ((oddIndex m a : Fin (2 * m)) : ℕ) : ℝ)) : ℂ)) := by
  rw [betaFactorialAllOrderNegativeFrame,
    betaFactorialAllOrderFirstPrimeLimit_factorization]
  rw [Matrix.conjTranspose_mul, logTwoInverseDiagonal_conjTranspose]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  have hcore :
      (oddInverseFlagFrame m)ᴴ *
          logTwoInverseDiagonal (2 * m) *
          (logTwoDiagonal (2 * m) * complexH (2 * m) *
            logTwoDiagonal (2 * m)) *
          (logTwoInverseDiagonal (2 * m) * oddInverseFlagFrame m) =
        (oddInverseFlagFrame m)ᴴ * complexH (2 * m) *
          oddInverseFlagFrame m := by
    calc
      _ = (oddInverseFlagFrame m)ᴴ *
          (logTwoInverseDiagonal (2 * m) * logTwoDiagonal (2 * m)) *
          complexH (2 * m) *
          (logTwoDiagonal (2 * m) * logTwoInverseDiagonal (2 * m)) *
          oddInverseFlagFrame m := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [logTwoInverse_mul_diagonal, logTwoDiagonal_mul_inverse]
        simp
  rw [hcore, oddInverseFlagFrame_compression]
  ext a b
  by_cases hab : a = b
  · subst b
    simp
  · simp [hab]

def betaFactorialAllOrderCompressedScaledGram (m : ℕ) (x : ℝ) :
    Matrix (Fin m) (Fin m) ℂ :=
  (betaFactorialAllOrderNegativeFrame m)ᴴ *
    ((Complex.ofReal ((2 : ℝ) ^ (x + 1))) •
      betaFactorialAllOrderComplexGram (2 * m) x) *
      betaFactorialAllOrderNegativeFrame m

def betaFactorialAllOrderCompressedLimit (m : ℕ) :
    Matrix (Fin m) (Fin m) ℂ :=
  Matrix.diagonal (fun a : Fin m =>
    ((((Real.log 2) ^ 2 * lastInvDiag
      ((oddIndex m a : Fin (2 * m)) : ℕ) : ℝ)) : ℂ))

theorem betaFactorialAllOrderNegativeFrame_compresses_limit' (m : ℕ) :
    (betaFactorialAllOrderNegativeFrame m)ᴴ *
        betaFactorialAllOrderFirstPrimeLimit (2 * m) *
          betaFactorialAllOrderNegativeFrame m =
      betaFactorialAllOrderCompressedLimit m :=
  betaFactorialAllOrderNegativeFrame_compresses_limit m

set_option maxHeartbeats 800000 in
theorem tendsto_betaFactorialAllOrderCompressedScaledGram_apply
    {m : ℕ} (i j : Fin m) :
    Tendsto
      (fun x : ℝ => betaFactorialAllOrderCompressedScaledGram m x i j)
      atTop (nhds (betaFactorialAllOrderCompressedLimit m i j)) := by
  rw [← betaFactorialAllOrderNegativeFrame_compresses_limit']
  simp only [betaFactorialAllOrderCompressedScaledGram, Matrix.mul_apply,
    Matrix.smul_apply, smul_eq_mul]
  apply tendsto_finsetSum
  intro k hk
  apply Tendsto.mul_const
  apply tendsto_finsetSum
  intro l hl
  exact tendsto_const_nhds.mul
    (tendsto_scaled_betaFactorialAllOrderComplexGram_apply l k)

private theorem exists_negative_margin_fin_succ
    (m : ℕ) (c : Fin (m + 1) → ℝ) (hc : ∀ i, c i < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, c i ≤ -δ := by
  let s : Finset ℝ := Finset.univ.image c
  have hs : s.Nonempty := by
    refine ⟨c 0, ?_⟩
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  let M : ℝ := s.max' hs
  have hM : M < 0 := by
    apply (Finset.max'_lt_iff s hs).2
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact hc i
  refine ⟨-M, by linarith, fun i => ?_⟩
  have hi : c i ≤ M :=
    Finset.le_max' s (c i)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  simpa using hi

theorem betaFactorialAllOrderCompressedScaledGram_eventually_negDef (m : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ z : Fin (m + 1) → ℂ, z ≠ 0 →
      (star z ⬝ᵥ
        (betaFactorialAllOrderCompressedScaledGram (m + 1) x).mulVec z).re < 0 := by
  let c : Fin (m + 1) → ℝ := fun a =>
    (Real.log 2) ^ 2 * lastInvDiag
      ((oddIndex (m + 1) a : Fin (2 * (m + 1))) : ℕ)
  have hell : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : ∀ a, c a < 0 := by
    intro a
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos hell)
      (oddNegativeIndex (m + 1) a).2
  obtain ⟨δ, hδ, hmargin⟩ := exists_negative_margin_fin_succ m c hc
  apply eventually_negDef_of_entrywise_tendsto_diagonal
    (betaFactorialAllOrderCompressedScaledGram (m + 1)) c hδ hmargin
  intro ε hε
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  have hball :=
    (tendsto_betaFactorialAllOrderCompressedScaledGram_apply i j).eventually
      (Metric.ball_mem_nhds _ hε)
  filter_upwards [hball] with x hx
  have hlt :
      ‖betaFactorialAllOrderCompressedScaledGram (m + 1) x i j -
        betaFactorialAllOrderCompressedLimit (m + 1) i j‖ < ε := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hlimit :
      betaFactorialAllOrderCompressedLimit (m + 1) i j =
        (Matrix.diagonal fun a => ((c a : ℝ) : ℂ)) i j := by
    rfl
  rw [← hlimit]
  exact le_of_lt hlt

theorem betaFactorialAllOrderNegativeFrame_mulVec_injective (m : ℕ) :
    Function.Injective (betaFactorialAllOrderNegativeFrame m).mulVec := by
  intro z w hzw
  apply oddInverseFlagFrame_mulVec_injective m
  have h := congrArg (logTwoDiagonal (2 * m)).mulVec hzw
  simp only [betaFactorialAllOrderNegativeFrame, Matrix.mulVec_mulVec] at h
  rw [← Matrix.mul_assoc, logTwoDiagonal_mul_inverse, Matrix.one_mul] at h
  exact h

def betaFactorialAllOrderNegativeSubspace (m : ℕ) :
    Submodule ℂ (Fin (2 * m) → ℂ) :=
  LinearMap.range (betaFactorialAllOrderNegativeFrame m).mulVecLin

theorem finrank_betaFactorialAllOrderNegativeSubspace (m : ℕ) :
    Module.finrank ℂ (betaFactorialAllOrderNegativeSubspace m) = m := by
  rw [betaFactorialAllOrderNegativeSubspace,
    LinearMap.finrank_range_of_inj
      (betaFactorialAllOrderNegativeFrame_mulVec_injective m),
    Module.finrank_fin_fun]

theorem betaFactorialAllOrderCompressedScaledGram_quadForm
    (m : ℕ) (x : ℝ) (z : Fin m → ℂ) :
    star z ⬝ᵥ (betaFactorialAllOrderCompressedScaledGram m x).mulVec z =
      Complex.ofReal ((2 : ℝ) ^ (x + 1)) *
        (star ((betaFactorialAllOrderNegativeFrame m).mulVec z) ⬝ᵥ
          (betaFactorialAllOrderComplexGram (2 * m) x).mulVec
            ((betaFactorialAllOrderNegativeFrame m).mulVec z)) := by
  simp only [betaFactorialAllOrderCompressedScaledGram,
    Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mul_assoc]

theorem betaFactorialAllOrderComplexGram_eventually_negDef_on_subspace
    (m : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      ∀ y ∈ betaFactorialAllOrderNegativeSubspace (m + 1), y ≠ 0 →
        (star y ⬝ᵥ
          (betaFactorialAllOrderComplexGram (2 * (m + 1)) x).mulVec y).re < 0 := by
  filter_upwards
    [betaFactorialAllOrderCompressedScaledGram_eventually_negDef m] with x hx
  intro y hy hy0
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hy
  have hz : z ≠ 0 := by
    intro hz
    apply hy0
    rw [hz]
    exact (betaFactorialAllOrderNegativeFrame (m + 1)).mulVecLin.map_zero
  have hscaled := hx z hz
  rw [betaFactorialAllOrderCompressedScaledGram_quadForm] at hscaled
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hscaled
  have hscale : 0 < (2 : ℝ) ^ (x + 1) := by positivity
  change
    (star ((betaFactorialAllOrderNegativeFrame (m + 1)).mulVec z) ⬝ᵥ
      (betaFactorialAllOrderComplexGram (2 * (m + 1)) x).mulVec
        ((betaFactorialAllOrderNegativeFrame (m + 1)).mulVec z)).re < 0
  nlinarith

/-- On the order-`2m` source, every positive repair needs at least `m`
rank-one channels.  This is the sharp linear rank-growth obstruction supplied
by the odd flag pivots. -/
theorem betaFactorialAllOrderComplexGram_eventually_not_posSemidef_add_rank_lt_half
    {k m : ℕ} (hkm : k < m) :
    ∀ᶠ x : ℝ in atTop,
      ∀ v : Fin k → (Fin (2 * m) → ℂ),
        ¬ (betaFactorialAllOrderComplexGram (2 * m) x +
          ∑ a, Matrix.of (fun i j => v a i * star (v a j))).PosSemidef := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le k) hkm))
  filter_upwards
    [betaFactorialAllOrderComplexGram_eventually_negDef_on_subspace r] with x hneg
  intro v hPSD
  have hle := GaloisForLFunctions.neg_inertia_le_of_posSemidef
    (betaFactorialAllOrderComplexGram (2 * (r + 1)) x) v hPSD
      (betaFactorialAllOrderNegativeSubspace (r + 1)) hneg
  rw [finrank_betaFactorialAllOrderNegativeSubspace] at hle
  exact (Nat.not_le_of_lt hkm) hle

/-- No fixed finite number of positive boundary channels repairs the cofinal
factorial/Beta-reflected source. -/
theorem betaFactorialAllOrderComplexGram_eventually_not_posSemidef_add_finiteRank
    (k : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      ∀ v : Fin k → (Fin (2 * (k + 1)) → ℂ),
        ¬ (betaFactorialAllOrderComplexGram (2 * (k + 1)) x +
          ∑ a, Matrix.of (fun i j => v a i * star (v a j))).PosSemidef :=
  betaFactorialAllOrderComplexGram_eventually_not_posSemidef_add_rank_lt_half
    (Nat.lt_succ_self k)

end

end RHTower
