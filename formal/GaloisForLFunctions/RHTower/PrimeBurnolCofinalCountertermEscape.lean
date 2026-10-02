import GaloisForLFunctions.RHTower.PrimeBurnolMixedCubicPrincipal
import GaloisForLFunctions.RHTower.PrimeBurnolDepthCompletion
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Cofinal escape of the actual confluent Burnol counterterm

The full confluent inverse constructs canonical physical radial duals with Gram
`G K^-1 G`. At every single prime, the literal depth span is dense, so the ground
radial dual has norm tending to infinity. Both the positive dual synthesis operator's
norm and its finite Gram trace diverge. The actual reflected cubic principal coefficient
is exactly that trace times its scalar theta factor, giving an unconditional dichotomy.

The positive survivor is source-native: normalized duals converge weakly to zero,
and their self-adjoint rank-one projections converge strongly to zero while retaining
rank one and operator norm one. Strong convergence alone loses this finite-rank carrier.

This excludes a bounded uncompensated dual counterterm. It does not exclude joint
prime–Gamma cancellation, construct a Hardy index comparison, or prove RH.
-/

open Complex Matrix Set Filter Topology
open scoped BigOperators
open GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

private def confluentFamily {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) :
    Fin N ⊕ Fin N → primeBurnolHalfLineL2 :=
  Sum.elim (fun i => primeBurnolRadialJetLp (pe i) 0)
    (fun i => primeBurnolRadialJetLp (pe i) 1)

private def confluentTarget {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) :
    Matrix (Fin N ⊕ Fin N) (Fin N) ℂ :=
  Matrix.fromRows 0 (primeBurnolMomentMatrix pe 0)

private def confluentDualCoefficients {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) :
    Matrix (Fin N ⊕ Fin N) (Fin N) ℂ :=
  (primeBurnolConfluentBlockGram pe)⁻¹ * confluentTarget pe

/-- Canonical physical dual to the radial jet, orthogonal to the original source packet. -/
def primeBurnolConfluentDual {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (j : Fin N) :
    primeBurnolHalfLineL2 :=
  ∑ i, confluentDualCoefficients pe i j • confluentFamily pe i

private theorem confluentDual_pairing {N : ℕ} (pe : Fin N ↪ Nat.Primes × ℕ)
    (i : Fin N ⊕ Fin N) (j : Fin N) :
    inner ℂ (confluentFamily pe i) (primeBurnolConfluentDual pe j) =
      confluentTarget pe i j := by
  have hm : primeBurnolConfluentBlockGram pe * confluentDualCoefficients pe = confluentTarget pe := by
    rw [confluentDualCoefficients, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (det_primeBurnolConfluentBlockGram_ne_zero pe))]
    exact Matrix.one_mul _
  have h := congrFun (congrFun hm i) j
  rw [primeBurnolConfluentBlockGram_eq_gram] at h
  simpa only [primeBurnolConfluentDual, inner_sum, inner_smul_right,
    Matrix.mul_apply, Matrix.gram_apply, confluentFamily, mul_comm] using h

theorem inner_primeBurnolRadialJet_zero_confluentDual {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ) (i j : Fin N) :
    inner ℂ (primeBurnolRadialJetLp (pe i) 0) (primeBurnolConfluentDual pe j) = 0 :=
  confluentDual_pairing pe (Sum.inl i) j

theorem inner_primeBurnolRadialJet_one_confluentDual {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ) (i j : Fin N) :
    inner ℂ (primeBurnolRadialJetLp (pe i) 1) (primeBurnolConfluentDual pe j) =
      primeBurnolMomentMatrix pe 0 i j :=
  confluentDual_pairing pe (Sum.inr i) j

theorem gram_primeBurnolConfluentDual {N : ℕ} (pe : Fin N ↪ Nat.Primes × ℕ) :
    Matrix.gram ℂ (primeBurnolConfluentDual pe) =
      primeBurnolMomentMatrix pe 0 * (primeBurnolRadialSchurComplement pe)⁻¹ *
        primeBurnolMomentMatrix pe 0 := by
  have hH : (primeBurnolConfluentBlockGram pe)⁻¹.IsHermitian := by
    rw [primeBurnolConfluentBlockGram_eq_gram]
    exact (Matrix.isHermitian_gram ℂ _).inv
  have hG : (primeBurnolMomentMatrix pe 0).IsHermitian := by
    rw [primeBurnolMomentMatrix_zero_eq]
    exact Matrix.isHermitian_gram ℂ _
  calc
    Matrix.gram ℂ (primeBurnolConfluentDual pe) =
        (confluentDualCoefficients pe)ᴴ * confluentTarget pe := by
      ext j l
      change inner ℂ (∑ i, confluentDualCoefficients pe i j • confluentFamily pe i)
        (primeBurnolConfluentDual pe l) = _
      simp only [sum_inner, inner_smul_left, confluentDual_pairing,
        Matrix.mul_apply, Matrix.conjTranspose_apply, starRingEnd_apply]
    _ = (confluentTarget pe)ᴴ * (primeBurnolConfluentBlockGram pe)⁻¹ * confluentTarget pe := by
      rw [confluentDualCoefficients, Matrix.conjTranspose_mul, hH.eq]
    _ = _ := by
      rw [confluentTarget, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose]
      conv_lhs => arg 1; arg 2; rw [← Matrix.fromBlocks_toBlocks (primeBurnolConfluentBlockGram pe)⁻¹]
      simp only [Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows,
        Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, hG.eq]
      rw [primeBurnolRadialSchurComplement_inverse]

theorem primeBurnolRadialJetLp_zero_eq_window (pe : Nat.Primes × ℕ) :
    primeBurnolRadialJetLp pe 0 = primeBurnolWindowFeatureLp pe 0 := by
  apply MeasureTheory.Lp.ext
  filter_upwards [primeBurnolRadialJetLp_coeFn pe 0,
    primeBurnolWindowFeatureLp_coeFn pe 0] with r hr hw
  rw [hr,hw]
  simp [primeBurnolRadialJet, primeBurnolWindowFeature, primeBurnolComplexExponent, mul_assoc]

def primeBurnolDepthPacket (p : Nat.Primes) (N : ℕ) : Fin (N+1) ↪ Nat.Primes × ℕ where
  toFun i := (p,i.val)
  inj' := by intro i j h; exact Fin.ext (congrArg Prod.snd h)

def primeBurnolDepthDual (p : Nat.Primes) (N : ℕ) : primeBurnolHalfLineL2 :=
  primeBurnolConfluentDual (primeBurnolDepthPacket p N) 0

theorem inner_primeBurnolWindow_depthDual (p : Nat.Primes) (n N : ℕ) (hn : n ≤ N) :
    inner ℂ (primeBurnolWindowFeatureLp (p,n) 0) (primeBurnolDepthDual p N) = 0 := by
  rw [← primeBurnolRadialJetLp_zero_eq_window]
  exact inner_primeBurnolRadialJet_zero_confluentDual (primeBurnolDepthPacket p N)
    ⟨n,Nat.lt_succ_of_le hn⟩ 0

theorem inner_primeBurnolJet_depthDual (p : Nat.Primes) (N : ℕ) :
    inner ℂ (primeBurnolRadialJetLp (p,0) 1) (primeBurnolDepthDual p N) =
      inner ℂ (primeBurnolWindowFeatureLp (p,0) 0) (primeBurnolWindowFeatureLp (p,0) 0) := by
  have h := inner_primeBurnolRadialJet_one_confluentDual (primeBurnolDepthPacket p N) 0 0
  rw [primeBurnolMomentMatrix_zero_eq] at h
  exact h


private theorem window_zero_ne_zero (p : Nat.Primes) : primeBurnolWindowFeatureLp (p,0) 0 ≠ 0 := by
  have h := (primeBurnolConfluentPair_linearIndependent (primeBurnolDepthPacket p 0)).ne_zero (0,0)
  simpa [primeBurnolDepthPacket, primeBurnolRadialJetLp_zero_eq_window] using h

private theorem window_mass_pos (p : Nat.Primes) :
    0 < ‖inner ℂ (primeBurnolWindowFeatureLp (p,0) 0) (primeBurnolWindowFeatureLp (p,0) 0)‖ := by
  rw [inner_self_eq_norm_sq_to_K, norm_pow]
  change 0 < ‖(‖primeBurnolWindowFeatureLp (p,0) 0‖ : ℂ)‖^2
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  exact sq_pos_of_pos (norm_pos_iff.mpr (window_zero_ne_zero p))

theorem eventually_inner_primeBurnolDepthSpan_dual_zero (p : Nat.Primes)
    (y : primeBurnolHalfLineL2) (hy : y ∈ primeBurnolLiteralDepthSpan p) :
    ∀ᶠ N : ℕ in atTop, inner ℂ y (primeBurnolDepthDual p N)=0 := by
  change y ∈ Submodule.span ℂ (Set.range (fun n => primeBurnolWindowFeatureLp (p,n) 0)) at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨n,rfl⟩
    filter_upwards [eventually_ge_atTop n] with N hN
    exact inner_primeBurnolWindow_depthDual p n N hN
  | zero => exact Filter.Eventually.of_forall fun _ => by simp
  | add x y _ _ hx hy =>
    filter_upwards [hx,hy] with N hx hy
    simp [inner_add_left,hx,hy]
  | smul a x _ hx =>
    filter_upwards [hx] with N hx
    simp [inner_smul_left,hx]

theorem primeBurnolDepthDual_norm_atTop (p : Nat.Primes) :
    Tendsto (fun N : ℕ => ‖primeBurnolDepthDual p N‖) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  let x := primeBurnolRadialJetLp (p,0) 1
  let m := ‖inner ℂ (primeBurnolWindowFeatureLp (p,0) 0) (primeBurnolWindowFeatureLp (p,0) 0)‖
  have hm : 0 < m := window_mass_pos p
  have hB : 0 < |B|+1 := by positivity
  obtain ⟨y,hy,hxy⟩ := (dense_primeBurnolLiteralDepthSpan p).exists_dist_lt x (div_pos hm hB)
  rw [dist_eq_norm] at hxy
  have heps : ‖x-y‖*(|B|+1) < m := (lt_div_iff₀ hB).mp hxy
  filter_upwards [eventually_inner_primeBurnolDepthSpan_dual_zero p y hy] with N hN
  have hinner : inner ℂ (x-y) (primeBurnolDepthDual p N) =
      inner ℂ (primeBurnolWindowFeatureLp (p,0) 0) (primeBurnolWindowFeatureLp (p,0) 0) := by
    rw [inner_sub_left,hN,sub_zero]
    exact inner_primeBurnolJet_depthDual p N
  have hbound := norm_inner_le_norm (𝕜 := ℂ) (x-y) (primeBurnolDepthDual p N)
  rw [hinner] at hbound
  by_contra h
  have hn : ‖primeBurnolDepthDual p N‖ ≤ |B|+1 := by
    exact le_trans (le_of_lt (lt_of_not_ge h)) (by linarith [le_abs_self B])
  have hmul := mul_le_mul_of_nonneg_left hn (norm_nonneg (x-y))
  exact (not_lt_of_ge (le_trans hbound hmul)) heps

def primeBurnolDepthCountertermEnergy (p : Nat.Primes) (N : ℕ) : ℝ :=
  (primeBurnolMomentMatrix (primeBurnolDepthPacket p N) 0 *
    (primeBurnolRadialSchurComplement (primeBurnolDepthPacket p N))⁻¹ *
    primeBurnolMomentMatrix (primeBurnolDepthPacket p N) 0).trace.re

theorem primeBurnolDepthCountertermEnergy_eq (p : Nat.Primes) (N : ℕ) :
    primeBurnolDepthCountertermEnergy p N =
      ∑ j : Fin (N+1), ‖primeBurnolConfluentDual (primeBurnolDepthPacket p N) j‖^2 := by
  rw [primeBurnolDepthCountertermEnergy, ← gram_primeBurnolConfluentDual]
  simp only [Matrix.trace, Matrix.diag, Matrix.gram_apply, Complex.re_sum]
  exact Finset.sum_congr rfl fun j _ => inner_self_eq_norm_sq (𝕜 := ℂ) _

theorem primeBurnolDepthCountertermEnergy_atTop (p : Nat.Primes) :
    Tendsto (primeBurnolDepthCountertermEnergy p) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (primeBurnolDepthDual_norm_atTop p)
  filter_upwards [(primeBurnolDepthDual_norm_atTop p).eventually_ge_atTop 1] with N hN
  have hle : ‖primeBurnolDepthDual p N‖^2 ≤ primeBurnolDepthCountertermEnergy p N := by
    rw [primeBurnolDepthCountertermEnergy_eq]
    exact Finset.single_le_sum
      (f := fun j : Fin (N+1) => ‖primeBurnolConfluentDual (primeBurnolDepthPacket p N) j‖^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ (0 : Fin (N+1)))
  nlinarith

theorem primeBurnolDepthDual_ne_zero (p : Nat.Primes) (N : ℕ) : primeBurnolDepthDual p N ≠ 0 := by
  intro h
  have hh := inner_primeBurnolJet_depthDual p N
  rw [h,inner_zero_right] at hh
  have hm := window_mass_pos p
  rw [← hh,norm_zero] at hm
  exact (lt_irrefl (0 : ℝ)) hm

/-- Positive operator synthesized by all canonical radial duals in the depth packet. -/
def primeBurnolDepthCountertermOperator (p : Nat.Primes) (N : ℕ) :
    primeBurnolHalfLineL2 →L[ℂ] primeBurnolHalfLineL2 :=
  ∑ j : Fin (N+1), InnerProductSpace.rankOne ℂ
    (primeBurnolConfluentDual (primeBurnolDepthPacket p N) j)
    (primeBurnolConfluentDual (primeBurnolDepthPacket p N) j)

theorem primeBurnolDepthCountertermOperator_quadratic (p : Nat.Primes) (N : ℕ)
    (x : primeBurnolHalfLineL2) :
    (inner ℂ x (primeBurnolDepthCountertermOperator p N x)).re =
      ∑ j : Fin (N+1), ‖inner ℂ (primeBurnolConfluentDual (primeBurnolDepthPacket p N) j) x‖^2 := by
  simp only [primeBurnolDepthCountertermOperator, _root_.sum_apply,
    inner_sum, Complex.re_sum, InnerProductSpace.inner_right_rankOne_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [← inner_conj_symm (𝕜 := ℂ) x (primeBurnolConfluentDual (primeBurnolDepthPacket p N) j),
    Complex.conj_mul']
  change ((‖inner ℂ (primeBurnolConfluentDual (primeBurnolDepthPacket p N) j) x‖ : ℂ)^2).re = _
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem primeBurnolDepthDual_sq_le_countertermOperator_norm (p : Nat.Primes) (N : ℕ) :
    ‖primeBurnolDepthDual p N‖^2 ≤ ‖primeBurnolDepthCountertermOperator p N‖ := by
  let z := primeBurnolDepthDual p N
  let T := primeBurnolDepthCountertermOperator p N
  have hdiag : ‖z‖^4 ≤ (inner ℂ z (T z)).re := by
    rw [primeBurnolDepthCountertermOperator_quadratic]
    have hs := Finset.single_le_sum
      (f := fun j : Fin (N+1) =>
        ‖inner ℂ (primeBurnolConfluentDual (primeBurnolDepthPacket p N) j) z‖^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ (0 : Fin (N+1)))
    change ‖inner ℂ z z‖^2 ≤ _ at hs
    simpa [inner_self_eq_norm_sq_to_K, norm_pow, ← pow_mul] using hs
  have hb := re_inner_le_norm (𝕜 := ℂ) z (T z)
  change (inner ℂ z (T z)).re ≤ ‖z‖ * ‖T z‖ at hb
  have ho := mul_le_mul_of_nonneg_left (T.le_opNorm z) (norm_nonneg z)
  have hz := sq_pos_of_pos (norm_pos_iff.mpr (primeBurnolDepthDual_ne_zero p N))
  change 0 < ‖z‖^2 at hz
  change ‖z‖^2 ≤ ‖T‖
  nlinarith

theorem primeBurnolDepthCountertermOperator_norm_atTop (p : Nat.Primes) :
    Tendsto (fun N : ℕ => ‖primeBurnolDepthCountertermOperator p N‖) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (primeBurnolDepthDual_norm_atTop p)
  filter_upwards [(primeBurnolDepthDual_norm_atTop p).eventually_ge_atTop 1] with N hN
  have h := primeBurnolDepthDual_sq_le_countertermOperator_norm p N
  nlinarith

def primeBurnolDepthEscapeUnit (p : Nat.Primes) (N : ℕ) : primeBurnolHalfLineL2 :=
  (‖primeBurnolDepthDual p N‖ : ℂ)⁻¹ • primeBurnolDepthDual p N

theorem primeBurnolDepthEscapeUnit_norm (p : Nat.Primes) (N : ℕ) :
    ‖primeBurnolDepthEscapeUnit p N‖=1 := by
  have h := norm_ne_zero_iff.mpr (primeBurnolDepthDual_ne_zero p N)
  simp [primeBurnolDepthEscapeUnit,norm_smul,h]

theorem primeBurnolDepthEscapeUnit_weak_zero (p : Nat.Primes) (x : primeBurnolHalfLineL2) :
    Tendsto (fun N : ℕ => inner ℂ x (primeBurnolDepthEscapeUnit p N)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨y,hy,hxy⟩ := (dense_primeBurnolLiteralDepthSpan p).exists_dist_lt x hε
  rw [dist_eq_norm] at hxy
  filter_upwards [eventually_inner_primeBurnolDepthSpan_dual_zero p y hy] with N hN
  have hy' : inner ℂ y (primeBurnolDepthEscapeUnit p N)=0 := by
    simp [primeBurnolDepthEscapeUnit,inner_smul_right,hN]
  have he : inner ℂ x (primeBurnolDepthEscapeUnit p N) =
      inner ℂ (x-y) (primeBurnolDepthEscapeUnit p N) := by rw [inner_sub_left,hy',sub_zero]
  rw [dist_zero_right,he]
  have h := norm_inner_le_norm (𝕜 := ℂ) (x-y) (primeBurnolDepthEscapeUnit p N)
  rw [primeBurnolDepthEscapeUnit_norm,mul_one] at h
  exact lt_of_le_of_lt h hxy


def primeBurnolDepthEscapeProjection (p : Nat.Primes) (N : ℕ) :
    primeBurnolHalfLineL2 →L[ℂ] primeBurnolHalfLineL2 :=
  InnerProductSpace.rankOne ℂ (primeBurnolDepthEscapeUnit p N) (primeBurnolDepthEscapeUnit p N)

theorem primeBurnolDepthEscapeProjection_norm (p : Nat.Primes) (N : ℕ) :
    ‖primeBurnolDepthEscapeProjection p N‖=1 := by
  simp [primeBurnolDepthEscapeProjection,primeBurnolDepthEscapeUnit_norm]

theorem primeBurnolDepthEscapeProjection_idempotent (p : Nat.Primes) (N : ℕ) :
    IsIdempotentElem (primeBurnolDepthEscapeProjection p N) :=
  InnerProductSpace.isIdempotentElem_rankOne_self (primeBurnolDepthEscapeUnit_norm p N)

theorem primeBurnolDepthEscapeProjection_adjoint (p : Nat.Primes) (N : ℕ) :
    ContinuousLinearMap.adjoint (primeBurnolDepthEscapeProjection p N) =
      primeBurnolDepthEscapeProjection p N :=
  InnerProductSpace.adjoint_rankOne _ _

theorem primeBurnolDepthEscapeProjection_fixes (p : Nat.Primes) (N : ℕ) :
    primeBurnolDepthEscapeProjection p N (primeBurnolDepthEscapeUnit p N) =
      primeBurnolDepthEscapeUnit p N := by
  simp [primeBurnolDepthEscapeProjection,inner_self_eq_norm_sq_to_K,primeBurnolDepthEscapeUnit_norm]

theorem primeBurnolDepthEscapeProjection_range (p : Nat.Primes) (N : ℕ) :
    LinearMap.range (primeBurnolDepthEscapeProjection p N).toLinearMap =
      Submodule.span ℂ {primeBurnolDepthEscapeUnit p N} := by
  apply le_antisymm
  · rintro x ⟨y,rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    rintro x (rfl : x=primeBurnolDepthEscapeUnit p N)
    exact ⟨primeBurnolDepthEscapeUnit p N,primeBurnolDepthEscapeProjection_fixes p N⟩

theorem primeBurnolDepthEscapeProjection_rank (p : Nat.Primes) (N : ℕ) :
    Module.finrank ℂ (LinearMap.range (primeBurnolDepthEscapeProjection p N).toLinearMap) = 1 := by
  rw [primeBurnolDepthEscapeProjection_range]
  apply finrank_span_singleton
  intro h
  have hn := primeBurnolDepthEscapeUnit_norm p N
  rw [h,norm_zero] at hn
  exact zero_ne_one hn

theorem primeBurnolDepthEscapeProjection_strong_zero (p : Nat.Primes) (x : primeBurnolHalfLineL2) :
    Tendsto (fun N : ℕ => primeBurnolDepthEscapeProjection p N x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [primeBurnolDepthEscapeProjection,InnerProductSpace.rankOne_apply,norm_smul,
    primeBurnolDepthEscapeUnit_norm,mul_one]
  simp_rw [norm_inner_symm (primeBurnolDepthEscapeUnit p _) x]
  simpa only [norm_zero] using (primeBurnolDepthEscapeUnit_weak_zero p x).norm

def primeBurnolDepthCubicFactor (p : Nat.Primes) (a : ℝ) : ℂ :=
  -((primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ)) *
    ((primeBurnolThetaVisibility a p : ℂ)^2-(2 : ℂ)⁻¹)

theorem primeBurnolDepthCubicPrincipal_eq (p : Nat.Primes) (a : ℝ) (N : ℕ) :
    primeBurnolMixedCubicPrincipalCoefficient (primeBurnolDepthPacket p N) a =
      primeBurnolDepthCubicFactor p a * (primeBurnolDepthCountertermEnergy p N : ℂ) := by
  have hU : primeBurnolThetaSquareMatrix (primeBurnolDepthPacket p N) a =
      (primeBurnolThetaVisibility a p : ℂ)^2 • 1 := by
    simp [primeBurnolThetaSquareMatrix,primeBurnolDepthPacket,Matrix.smul_one_eq_diagonal]
  have hV : primeBurnolThetaMixedMatrix (primeBurnolDepthPacket p N) a =
      ((primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ)) • 1 := by
    simp [primeBurnolThetaMixedMatrix,primeBurnolDepthPacket,Matrix.smul_one_eq_diagonal]
  have hE : (primeBurnolDepthCountertermEnergy p N : ℂ) =
      (primeBurnolMomentMatrix (primeBurnolDepthPacket p N) 0 *
        (primeBurnolRadialSchurComplement (primeBurnolDepthPacket p N))⁻¹ *
        primeBurnolMomentMatrix (primeBurnolDepthPacket p N) 0).trace := by
    rw [primeBurnolDepthCountertermEnergy_eq,← gram_primeBurnolConfluentDual]
    simp [Matrix.trace,Matrix.diag,inner_self_eq_norm_sq_to_K]
  rw [primeBurnolMixedCubicPrincipalCoefficient,hU,hV,← sub_smul,hE]
  simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,Matrix.trace_smul,
    primeBurnolDepthCubicFactor]
  ring

/-- Exact dichotomy: a vanishing theta factor or unbounded actual cubic principal coefficient. -/
theorem primeBurnolDepthCubicPrincipal_dichotomy (p : Nat.Primes) (a : ℝ) :
    if primeBurnolDepthCubicFactor p a = 0 then
      ∀ N, primeBurnolMixedCubicPrincipalCoefficient (primeBurnolDepthPacket p N) a=0
    else Tendsto (fun N : ℕ =>
      ‖primeBurnolMixedCubicPrincipalCoefficient (primeBurnolDepthPacket p N) a‖) atTop atTop := by
  split_ifs with h
  · intro N
    rw [primeBurnolDepthCubicPrincipal_eq,h,zero_mul]
  · have ht := (primeBurnolDepthCountertermEnergy_atTop p).const_mul_atTop (norm_pos_iff.mpr h)
    have hpos (N : ℕ) : 0 ≤ primeBurnolDepthCountertermEnergy p N := by
      rw [primeBurnolDepthCountertermEnergy_eq]
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    simpa only [primeBurnolDepthCubicPrincipal_eq,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (hpos _)] using ht

end
end RHTower
