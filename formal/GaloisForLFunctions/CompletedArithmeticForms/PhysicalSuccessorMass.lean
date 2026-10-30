import GaloisForLFunctions.CompletedArithmeticForms.PhysicalQuadraticHorizon

/-!
# Physical mass and monomial scale of the exact native successor

The full signed Gaussian successor is its monic Hermite norm. Exact source
mass and length rescaling multiplies every successor by the corresponding
terminal monomial scale. The complete native form estimate therefore gives
a literal physical successor reserve at every rank, with no inverse-head loss.
-/

noncomputable section

open Matrix Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower _root_.RHTower.ThetaCuspGaussianLimit

/-- Exact simultaneous mass and length transport of a moment source. -/
def rescaledMoment (c t : ℝ) (m : ℕ → ℝ) (k : ℕ) : ℝ := c * t ^ k * m k

theorem rescaledMoment_head (c t : ℝ) (m : ℕ → ℝ) (N : ℕ) :
    finiteHankelMatrix (rescaledMoment c t m) N =
      c • (diagonal (fun i : Fin N => t ^ i.val) * finiteHankelMatrix m N *
        diagonal (fun i : Fin N => t ^ i.val)) := by
  ext i j
  simp only [finiteHankelMatrix, rescaledMoment, Matrix.smul_apply, smul_eq_mul,
    diagonal_mul, mul_diagonal, pow_add]
  ring

theorem rescaledMoment_head_posDef {c t : ℝ} (hc : 0 < c) (ht : t ≠ 0)
    {m : ℕ → ℝ} {N : ℕ} (hm : (finiteHankelMatrix m N).PosDef) :
    (finiteHankelMatrix (rescaledMoment c t m) N).PosDef := by
  rw [rescaledMoment_head]
  have hi : Function.Injective (diagonal (fun i : Fin N => t ^ i.val)).mulVec := by
    intro v w h
    funext i
    have he := congrFun h i
    simp only [Matrix.mulVec_diagonal] at he
    exact mul_left_cancel₀ (pow_ne_zero _ ht) he
  simpa only [diagonal_conjTranspose, star_trivial] using
    (hm.conjTranspose_mul_mul_same hi).smul hc

theorem rescaledMoment_head_det (c t : ℝ) (m : ℕ → ℝ) (N : ℕ) :
    (finiteHankelMatrix (rescaledMoment c t m) N).det =
      (∏ i : Fin N, c * t ^ (2 * i.val)) * (finiteHankelMatrix m N).det := by
  rw [rescaledMoment_head, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal]
  simp only [Fintype.card_fin]
  have hp : c ^ N * (∏ i : Fin N, t ^ i.val) * (∏ i : Fin N, t ^ i.val) =
      ∏ i : Fin N, c * t ^ (2 * i.val) := by
    rw [show c ^ N = ∏ _i : Fin N, c by simp,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [show 2 * i.val = i.val + i.val by omega, pow_add]
    ring
  calc
    _ = (c ^ N * (∏ i : Fin N, t ^ i.val) * (∏ i : Fin N, t ^ i.val)) *
        (finiteHankelMatrix m N).det := by ring
    _ = _ := by rw [hp]

/-- Source mass and length have an exact terminal-degree payment in every successor. -/
theorem rescaledMoment_successorSchur {c t : ℝ} (hc : 0 < c) (ht : t ≠ 0)
    {m : ℕ → ℝ} {N : ℕ} (hm : (finiteHankelMatrix m N).PosDef) :
    finiteHankelSuccessorSchur (rescaledMoment c t m) N =
      c * t ^ (2 * N) * finiteHankelSuccessorSchur m N := by
  have hs := finiteHankelMatrix_succ_det_eq_schur (rescaledMoment_head_posDef hc ht hm)
  rw [rescaledMoment_head_det, rescaledMoment_head_det,
    Fin.prod_univ_castSucc, finiteHankelMatrix_succ_det_eq_schur hm] at hs
  have hp : (∏ i : Fin N, c * t ^ (2 * i.val)) * (finiteHankelMatrix m N).det ≠ 0 := by
    rw [← rescaledMoment_head_det]
    exact (rescaledMoment_head_posDef hc ht hm).det_pos.ne'
  apply mul_left_cancel₀ hp
  calc
    _ = ((∏ i : Fin N, c * t ^ (2 * i.val)) * (c * t ^ (2 * N))) *
        ((finiteHankelMatrix m N).det * finiteHankelSuccessorSchur m N) := hs.symm
    _ = _ := by ring

/-- The unit triangular Hermite transform exposes every full Gaussian determinant factor. -/
theorem gaussianFullHead_det (N : ℕ) :
    (gaussianFullHead N).det = ∏ i : Fin N, hermiteGaussianNormSq i.val := by
  have he := congrArg Matrix.det (hermiteGaussianHead_eq_full_congruence N)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hermiteJetMatrix_det,
    one_mul, mul_one] at he
  simpa only [hermiteGaussianHead, Matrix.det_diagonal] using he.symm

/-- The exact full signed Gaussian successor is the monic Hermite squared norm. -/
theorem gaussianFull_successorSchur (N : ℕ) :
    finiteHankelSuccessorSchur (evenMomentSequence gaussianMoment) N = hermiteGaussianNormSq N := by
  have he := finiteHankelMatrix_succ_det_eq_schur (gaussianFullHead_posDef N)
  change (gaussianFullHead (N + 1)).det =
    (gaussianFullHead N).det * finiteHankelSuccessorSchur (evenMomentSequence gaussianMoment) N at he
  rw [gaussianFullHead_det, gaussianFullHead_det, Fin.prod_univ_castSucc] at he
  have hp : (∏ i : Fin N, hermiteGaussianNormSq i.val) ≠ 0 := by
    rw [← gaussianFullHead_det]
    exact (gaussianFullHead_posDef N).det_pos.ne'
  exact (mul_left_cancel₀ hp he).symm

/-- Every complete balanced native head is strict on its quadratic source-scale domain. -/
theorem nativeBalancedFullHead_strict_on_quadratic_scale (N : ℕ) {x : ℝ}
    (hq : nativeQuadraticRankScale N ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (finiteHankelMatrix (nativeBalancedFullMoment x) N).PosDef := by
  have hA : (finiteHankelMatrix (nativeBalancedFullMoment x) N).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [finiteHankelMatrix, Nat.add_comm]
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hη : nativeQuadraticFormCost N / thetaCuspSingleAtomReflectionScale 1 x < 1 / 2 := by
    apply (div_lt_iff₀ hqp).mpr
    have hc := (nativeQuadraticRankScale_cost_lt N).trans_le hq
    linarith only [hc]
  have hh := halfReserve_posDef_of_relative_error hA (gaussianFullHead_posDef N) hη
    (nativeBalancedFullHead_quadratic_rank_error_le N ((nativeQuadraticRankScale_base_le N).trans hq))
  simpa only [sub_add_cancel] using
    hh.add ((gaussianFullHead_posDef N).smul (by norm_num : (0 : ℝ) < 1 / 2))

/-- The full normalized native successor retains a strict half-Hermite reserve. -/
theorem nativeBalancedFull_successor_half_bounds (N : ℕ) {x : ℝ}
    (hq : nativeQuadraticRankScale (N + 1) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    hermiteGaussianNormSq N / 2 < finiteHankelSuccessorSchur (nativeBalancedFullMoment x) N ∧
      finiteHankelSuccessorSchur (nativeBalancedFullMoment x) N < 3 * hermiteGaussianNormSq N / 2 := by
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hη0 : 0 ≤ nativeQuadraticFormCost (N + 1) / thetaCuspSingleAtomReflectionScale 1 x :=
    div_nonneg (nativeQuadraticFormCost_pos _).le hqp.le
  have hη : nativeQuadraticFormCost (N + 1) / thetaCuspSingleAtomReflectionScale 1 x < 1 / 2 := by
    apply (div_lt_iff₀ hqp).mpr
    have hc := (nativeQuadraticRankScale_cost_lt (N + 1)).trans_le hq
    linarith only [hc]
  have he := successorSchur_relative_error (gaussianFullHead_posDef (N + 1)) hη0
    (by linarith only [hη] : nativeQuadraticFormCost (N + 1) /
      thetaCuspSingleAtomReflectionScale 1 x < 1)
    (nativeBalancedFullHead_quadratic_rank_error_le (N + 1)
      ((nativeQuadraticRankScale_base_le (N + 1)).trans hq))
  rw [gaussianFull_successorSchur] at he
  obtain ⟨hl, hu⟩ := abs_le.mp he
  have hp := mul_pos (sub_pos.mpr hη) (hermiteGaussianNormSq_pos N)
  constructor <;> nlinarith only [hl, hu, hp]

/-- The exact physical signed sequence is the mass and square-root-scale transport of its normalization. -/
theorem nativeSignedMoment_eq_rescaled {x : ℝ} (hf : thetaCuspSourceTerm x 1 ≠ 0) :
    thetaCuspNativeSignedJet x =
      rescaledMoment (thetaCuspSourceTerm x 1 ^ 2)
        (Real.sqrt (thetaCuspSingleAtomReflectionScale 1 x)) (nativeBalancedFullMoment x) := by
  have hq : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  rw [thetaCuspNativeSignedJet_eq_evenMomentSequence]
  funext k
  rcases Nat.even_or_odd k with he | ho
  · obtain ⟨j, hj⟩ := he
    have hp : Real.sqrt (thetaCuspSingleAtomReflectionScale 1 x) ^ (2 * j) =
        thetaCuspSingleAtomReflectionScale 1 x ^ j := by
      rw [pow_mul, Real.sq_sqrt hq.le]
    rw [show k = 2 * j by omega, rescaledMoment, nativeBalancedFullMoment,
      evenMomentSequence_even, evenMomentSequence_even, thetaCuspNativeScaledEvenJet, hp]
    field_simp [hf, hq.ne']
  · obtain ⟨j, hj⟩ := ho
    rw [show k = 2 * j + 1 by omega, rescaledMoment, nativeBalancedFullMoment,
      evenMomentSequence_odd, evenMomentSequence_odd, mul_zero]

/-- Literal physical successor bounds retain the source mass and the entire terminal monomial scale. -/
theorem nativePhysicalSuccessor_half_bounds (N : ℕ) {x : ℝ}
    (hq : nativeQuadraticRankScale (N + 1) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspSourceTerm x 1 ^ 2 * thetaCuspSingleAtomReflectionScale 1 x ^ N *
        hermiteGaussianNormSq N / 2 < finiteHankelSuccessorSchur (thetaCuspNativeSignedJet x) N ∧
      finiteHankelSuccessorSchur (thetaCuspNativeSignedJet x) N <
        3 * (thetaCuspSourceTerm x 1 ^ 2 * thetaCuspSingleAtomReflectionScale 1 x ^ N *
          hermiteGaussianNormSq N) / 2 := by
  have hb := (nativeQuadraticRankScale_base_le (N + 1)).trans hq
  have hq3 : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
    push_cast at hb
    nlinarith only [hb, Nat.cast_nonneg (α := ℝ) N, sq_nonneg (N : ℝ)]
  have hf2 := firstAtom_mass_pos hq3
  have hf : thetaCuspSourceTerm x 1 ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by omega : (2 : ℕ) ≠ 0)] at hf2
    exact lt_irrefl 0 hf2
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith only [hq3]
  have hfull := nativeBalancedFullHead_strict_on_quadratic_scale (N + 1) hq
  have hi : Function.Injective (Fin.castSucc : Fin N → Fin (N + 1)) := by
    intro i j hij
    exact Fin.ext (congrArg (fun z : Fin (N + 1) => z.val) hij)
  have hm : (finiteHankelMatrix (nativeBalancedFullMoment x) N).PosDef := hfull.submatrix hi
  have hp : Real.sqrt (thetaCuspSingleAtomReflectionScale 1 x) ^ (2 * N) =
      thetaCuspSingleAtomReflectionScale 1 x ^ N := by rw [pow_mul, Real.sq_sqrt hqp.le]
  rw [nativeSignedMoment_eq_rescaled hf,
    rescaledMoment_successorSchur hf2 (Real.sqrt_pos.mpr hqp).ne' hm, hp]
  obtain ⟨hl, hu⟩ := nativeBalancedFull_successor_half_bounds N hq
  have hc : 0 < thetaCuspSourceTerm x 1 ^ 2 * thetaCuspSingleAtomReflectionScale 1 x ^ N :=
    mul_pos hf2 (pow_pos hqp N)
  constructor
  · simpa only [mul_div_assoc] using mul_lt_mul_of_pos_left hl hc
  · calc
      _ < (thetaCuspSourceTerm x 1 ^ 2 * thetaCuspSingleAtomReflectionScale 1 x ^ N) *
          (3 * hermiteGaussianNormSq N / 2) := mul_lt_mul_of_pos_left hu hc
      _ = _ := by ring

theorem nativeQuadraticRankHorizon_mono {M K : ℕ} (hMK : M ≤ K) :
    nativeQuadraticRankHorizon M ≤ nativeQuadraticRankHorizon K := by
  unfold nativeQuadraticRankHorizon
  apply max_le_max le_rfl
  exact add_le_add le_rfl (Real.log_le_log (by positivity)
    (by exact_mod_cast Nat.add_le_add_right hMK 2))

/-- Physical successor mass is controlled on an explicit logarithmic center domain. -/
theorem nativePhysicalSuccessor_half_bounds_of_horizon (N : ℕ) {x : ℝ}
    (hx : nativeQuadraticRankHorizon (N + 1) ≤ x) :
    thetaCuspSourceTerm x 1 ^ 2 * thetaCuspSingleAtomReflectionScale 1 x ^ N *
        hermiteGaussianNormSq N / 2 < finiteHankelSuccessorSchur (thetaCuspNativeSignedJet x) N ∧
      finiteHankelSuccessorSchur (thetaCuspNativeSignedJet x) N <
        3 * (thetaCuspSourceTerm x 1 ^ 2 * thetaCuspSingleAtomReflectionScale 1 x ^ N *
          hermiteGaussianNormSq N) / 2 :=
  nativePhysicalSuccessor_half_bounds N (nativeQuadraticRankScale_le_of_horizon _ hx)

/-- The explicit physical half-Hermite mass in the terminal monomial direction. -/
def nativePhysicalSuccessorFloor (N : ℕ) (x : ℝ) : ℝ :=
  thetaCuspSourceTerm x 1 ^ 2 * thetaCuspSingleAtomReflectionScale 1 x ^ N *
    hermiteGaussianNormSq N / 2

theorem nativePhysicalSuccessorFloor_nonneg (N : ℕ) (x : ℝ) :
    0 ≤ nativePhysicalSuccessorFloor N x := by
  have hd := hermiteGaussianNormSq_pos N
  unfold nativePhysicalSuccessorFloor thetaCuspSingleAtomReflectionScale
  positivity

theorem continuous_nativePhysicalSuccessorFloor (N : ℕ) :
    Continuous (nativePhysicalSuccessorFloor N) := by
  unfold nativePhysicalSuccessorFloor thetaCuspSourceTerm thetaCuspSeed
    thetaCuspSingleAtomReflectionScale
  fun_prop

theorem nativePhysicalSuccessorFloor_pos (N : ℕ) {x : ℝ}
    (hx : nativeQuadraticRankHorizon (N + 1) ≤ x) : 0 < nativePhysicalSuccessorFloor N x := by
  have hb := (nativeQuadraticRankScale_base_le (N + 1)).trans
    (nativeQuadraticRankScale_le_of_horizon _ hx)
  have hq3 : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
    push_cast at hb
    nlinarith only [hb, Nat.cast_nonneg (α := ℝ) N, sq_nonneg (N : ℝ)]
  have hf := firstAtom_mass_pos hq3
  have hq : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith only [hq3]
  have hd := hermiteGaussianNormSq_pos N
  unfold nativePhysicalSuccessorFloor
  positivity

#print axioms rescaledMoment_successorSchur
#print axioms gaussianFull_successorSchur
#print axioms nativeBalancedFull_successor_half_bounds
#print axioms nativeSignedMoment_eq_rescaled
#print axioms nativePhysicalSuccessor_half_bounds

end GaloisForLFunctions.CompletedArithmeticForms
