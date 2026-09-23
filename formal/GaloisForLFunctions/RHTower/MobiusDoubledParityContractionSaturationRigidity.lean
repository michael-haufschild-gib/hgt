import GaloisForLFunctions.RHTower.MobiusDoubledParityHardyTransverseGram
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardCofinalBoundaryLift
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Matrix.PosDef

/-!
# Saturated contractions cannot create the Xi Ward codiagonal

The doubled Möbius source has exactly orthogonal Hardy-father and four-unit
detail channels.  This module proves the relevant universal Hilbert-space
rigidity law.

For a contraction `T`, its Gram loss

`gram(v) - gram(T ∘ v)`

is positive semidefinite on every finite packet.  If `T` preserves the norm of
one vector `d`, then `T† T d = d`; consequently `T` preserves every inner
product against `d`.  In particular, a contraction which saturates the
four-unit Möbius detail cannot turn its zero father/detail codiagonal into a
nonzero Xi Ward column.

Thus the desired source transport cannot be an ordinary saturated contraction,
in any Hilbert-space dimension.  Quantitatively, the same conclusion survives
cofinal families with vanishing detail loss.  If a moving target detail also
contains an operator-connection term, that term carries the entire limiting
Ward column.  For the actual doubled Möbius source, existence of the direct
cofinal contraction realization is classified exactly by RH.
-/

open Complex
open scoped InnerProduct ComplexOrder

namespace RHTower

noncomputable section

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Gram loss of a contraction candidate on a finite Hilbert packet. -/
def contractionGramDefect {ι : Type*}
    (T : H →L[ℂ] K) (v : ι → H) : Matrix ι ι ℂ :=
  Matrix.gram ℂ v - Matrix.gram ℂ (T ∘ v)

omit [CompleteSpace H] [CompleteSpace K] in
/-- **Universal contraction Gram-loss law.**  Every finite packet loses a
positive-semidefinite Gram matrix under a contraction. -/
theorem contractionGramDefect_posSemidef
    {ι : Type*} [Finite ι]
    (T : H →L[ℂ] K) (hT : ‖T‖ ≤ 1) (v : ι → H) :
    (contractionGramDefect T v).PosSemidef := by
  have hnormsq : ‖T‖ ^ (2 : ℕ) ≤ 1 := by
    nlinarith [norm_nonneg T]
  let c : ℝ := 1 - ‖T‖ ^ (2 : ℕ)
  have hcR : 0 ≤ c := by
    dsimp [c]
    exact sub_nonneg.mpr hnormsq
  have hc : (0 : ℂ) ≤ (c : ℂ) := by
    exact_mod_cast hcR
  have hsource := (Matrix.posSemidef_gram ℂ v).smul hc
  have hop :=
    Matrix.posSemidef_opNorm_smul_gram_sub_gram v T
  have hsum := hsource.add hop
  have heq : contractionGramDefect T v =
      (c : ℂ) • Matrix.gram ℂ v +
        (((‖T‖ ^ (2 : ℕ) : ℝ) : ℂ) • Matrix.gram ℂ v -
          Matrix.gram ℂ (T ∘ v)) := by
    ext i j
    simp [contractionGramDefect, c]
    ring
  rw [heq]
  exact hsum

/-- Saturating one vector forces the adjoint defect to vanish on that vector. -/
theorem adjoint_apply_apply_eq_of_contraction_saturates
    (T : H →L[ℂ] K) (hT : ‖T‖ ≤ 1) (d : H)
    (hsat : ‖T d‖ = ‖d‖) :
    ContinuousLinearMap.adjoint T (T d) = d := by
  let v : H := ContinuousLinearMap.adjoint T (T d)
  have hvnorm : ‖v‖ ≤ ‖d‖ := by
    calc
      ‖v‖ ≤ ‖ContinuousLinearMap.adjoint T‖ * ‖T d‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖T‖ * ‖d‖ := by
        rw [LinearIsometryEquiv.norm_map, hsat]
      _ ≤ 1 * ‖d‖ :=
        mul_le_mul_of_nonneg_right hT (norm_nonneg d)
      _ = ‖d‖ := one_mul _
  have hvnormsq : ‖v‖ ^ (2 : ℕ) ≤ ‖d‖ ^ (2 : ℕ) :=
    pow_le_pow_left₀ (norm_nonneg v) hvnorm 2
  have hinner : RCLike.re (inner ℂ v d) = ‖d‖ ^ (2 : ℕ) := by
    change RCLike.re
        (inner ℂ (ContinuousLinearMap.adjoint T (T d)) d) =
      ‖d‖ ^ (2 : ℕ)
    rw [ContinuousLinearMap.adjoint_inner_left]
    calc
      RCLike.re (inner ℂ (T d) (T d)) = ‖T d‖ ^ (2 : ℕ) :=
        inner_self_eq_norm_sq _
      _ = ‖d‖ ^ (2 : ℕ) := by rw [hsat]
  have hdist : ‖v - d‖ ^ (2 : ℕ) ≤ 0 := by
    rw [norm_sub_sq (𝕜 := ℂ), hinner]
    linarith
  have hz : ‖v - d‖ = 0 := by
    nlinarith [sq_nonneg ‖v - d‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- **Saturated-column rigidity.**  A contraction preserving the norm of
`d` preserves every codiagonal inner product against `d`. -/
theorem inner_map_detail_eq_of_contraction_saturates
    (T : H →L[ℂ] K) (hT : ‖T‖ ≤ 1) (x d : H)
    (hsat : ‖T d‖ = ‖d‖) :
    inner ℂ (T x) (T d) = inner ℂ x d := by
  rw [← ContinuousLinearMap.adjoint_inner_right]
  rw [adjoint_apply_apply_eq_of_contraction_saturates T hT d hsat]

/-- **Quantitative saturation law.**  The squared distance from `d` to its
adjoint defect image is at most the norm-square lost by `d`. -/
theorem norm_adjoint_apply_apply_sub_sq_le_detail_loss
    (T : H →L[ℂ] K) (hT : ‖T‖ ≤ 1) (d : H) :
    ‖ContinuousLinearMap.adjoint T (T d) - d‖ ^ (2 : ℕ) ≤
      ‖d‖ ^ (2 : ℕ) - ‖T d‖ ^ (2 : ℕ) := by
  let v : H := ContinuousLinearMap.adjoint T (T d)
  have hvnorm : ‖v‖ ≤ ‖T d‖ := by
    calc
      ‖v‖ ≤ ‖ContinuousLinearMap.adjoint T‖ * ‖T d‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖T‖ * ‖T d‖ := by
        rw [LinearIsometryEquiv.norm_map]
      _ ≤ 1 * ‖T d‖ :=
        mul_le_mul_of_nonneg_right hT (norm_nonneg (T d))
      _ = ‖T d‖ := one_mul _
  have hvnormsq : ‖v‖ ^ (2 : ℕ) ≤ ‖T d‖ ^ (2 : ℕ) :=
    pow_le_pow_left₀ (norm_nonneg v) hvnorm 2
  have hinner : RCLike.re (inner ℂ v d) = ‖T d‖ ^ (2 : ℕ) := by
    change RCLike.re
        (inner ℂ (ContinuousLinearMap.adjoint T (T d)) d) =
      ‖T d‖ ^ (2 : ℕ)
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact inner_self_eq_norm_sq _
  rw [norm_sub_sq (𝕜 := ℂ), hinner]
  linarith

/-- The codiagonal created by a contraction is controlled by the square root
of the detail energy it loses.  This is the quantitative form needed for
singular/cofinal boundary lifts. -/
theorem norm_codiagonal_defect_le
    (T : H →L[ℂ] K) (hT : ‖T‖ ≤ 1) (x d : H) :
    ‖inner ℂ (T x) (T d) - inner ℂ x d‖ ≤
      ‖x‖ * Real.sqrt (‖d‖ ^ (2 : ℕ) - ‖T d‖ ^ (2 : ℕ)) := by
  have hdist :=
    norm_adjoint_apply_apply_sub_sq_le_detail_loss T hT d
  calc
    ‖inner ℂ (T x) (T d) - inner ℂ x d‖ =
        ‖inner ℂ x (ContinuousLinearMap.adjoint T (T d) - d)‖ := by
      rw [inner_sub_right, ContinuousLinearMap.adjoint_inner_right]
    _ ≤ ‖x‖ * ‖ContinuousLinearMap.adjoint T (T d) - d‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖x‖ * Real.sqrt (‖d‖ ^ (2 : ℕ) - ‖T d‖ ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left
        (Real.le_sqrt_of_sq_le hdist) (norm_nonneg x)

/-- **Universal cofinal saturation rigidity.**  For any sequence of
contractions, an orthogonal source codiagonal stays asymptotically zero when
father norms are uniformly bounded and detail loss tends to zero.  Source and
target Hilbert spaces may be infinite-dimensional. -/
theorem codiagonal_tendsto_zero_of_cofinal_contractions
    (T : ℕ → H →L[ℂ] K) (x d : ℕ → H) (B : ℝ)
    (hT : ∀ n, ‖T n‖ ≤ 1)
    (hbound : ∀ n, ‖x n‖ ≤ B)
    (horth : ∀ n, inner ℂ (x n) (d n) = 0)
    (hloss : Filter.Tendsto
      (fun n => ‖d n‖ ^ (2 : ℕ) - ‖T n (d n)‖ ^ (2 : ℕ))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => inner ℂ (T n (x n)) (T n (d n)))
      Filter.atTop (nhds 0) := by
  have hB : 0 ≤ B :=
    (norm_nonneg (x 0)).trans (hbound 0)
  have hsqrt :
      Filter.Tendsto
        (fun n => Real.sqrt (‖d n‖ ^ (2 : ℕ) - ‖T n (d n)‖ ^ (2 : ℕ)))
        Filter.atTop (nhds 0) := by
    simpa using hloss.sqrt
  have hnorm :
      Filter.Tendsto
        (fun n => ‖inner ℂ (T n (x n)) (T n (d n)) -
          inner ℂ (x n) (d n)‖)
        Filter.atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact norm_nonneg _
    · intro n
      exact
        (norm_codiagonal_defect_le (T n) (hT n) (x n) (d n)).trans
          (mul_le_mul_of_nonneg_right (hbound n) (Real.sqrt_nonneg _))
    · simpa using hsqrt.const_mul B
  have hdiff :
      Filter.Tendsto
        (fun n => inner ℂ (T n (x n)) (T n (d n)) -
          inner ℂ (x n) (d n))
        Filter.atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  convert hdiff using 1
  ext n
  rw [horth n, sub_zero]

/-- Any proposed cofinal codiagonal limit in the setting of
`codiagonal_tendsto_zero_of_cofinal_contractions` is forced to vanish. -/
theorem codiagonal_limit_eq_zero_of_cofinal_contractions
    (T : ℕ → H →L[ℂ] K) (x d : ℕ → H) (B : ℝ) (r : ℂ)
    (hT : ∀ n, ‖T n‖ ≤ 1)
    (hbound : ∀ n, ‖x n‖ ≤ B)
    (horth : ∀ n, inner ℂ (x n) (d n) = 0)
    (hloss : Filter.Tendsto
      (fun n => ‖d n‖ ^ (2 : ℕ) - ‖T n (d n)‖ ^ (2 : ℕ))
      Filter.atTop (nhds 0))
    (hcolumn : Filter.Tendsto
      (fun n => inner ℂ (T n (x n)) (T n (d n)))
      Filter.atTop (nhds r)) :
    r = 0 :=
  tendsto_nhds_unique hcolumn
    (codiagonal_tendsto_zero_of_cofinal_contractions
      T x d B hT hbound horth hloss)

/-- **Cofinal connection conservation law.**  If a target detail `e n`
contains both the transported source detail and a moving-operator connection,
then every nonzero limiting codiagonal is carried by that connection.  The
direct transported detail contributes asymptotically zero. -/
theorem connection_codiagonal_tendsto_of_cofinal_contractions
    (T : ℕ → H →L[ℂ] K) (x d : ℕ → H) (e : ℕ → K)
    (B : ℝ) (r : ℂ)
    (hT : ∀ n, ‖T n‖ ≤ 1)
    (hbound : ∀ n, ‖x n‖ ≤ B)
    (horth : ∀ n, inner ℂ (x n) (d n) = 0)
    (hloss : Filter.Tendsto
      (fun n => ‖d n‖ ^ (2 : ℕ) - ‖T n (d n)‖ ^ (2 : ℕ))
      Filter.atTop (nhds 0))
    (htarget : Filter.Tendsto
      (fun n => inner ℂ (T n (x n)) (e n))
      Filter.atTop (nhds r)) :
    Filter.Tendsto
      (fun n =>
        inner ℂ (T n (x n)) (e n - T n (d n)))
      Filter.atTop (nhds r) := by
  have hdirect :=
    codiagonal_tendsto_zero_of_cofinal_contractions
      T x d B hT hbound horth hloss
  have hsub := htarget.sub hdirect
  simpa only [sub_zero, inner_sub_right] using hsub

/-- The exact doubled Möbius father/detail split therefore stays codiagonal
under every contraction which preserves its detail norm. -/
theorem inner_map_infiniteMobiusDoubledParityFather_detail_eq_zero
    (T : infiniteMobiusDoubledHilbert →L[ℂ] K)
    (hT : ‖T‖ ≤ 1)
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u)
    (hsat :
      ‖T (infiniteMobiusDoubledParityFisherDetail sigma hsigma)‖ =
        ‖infiniteMobiusDoubledParityFisherDetail sigma hsigma‖) :
    inner ℂ
        (T (infiniteMobiusDoubledParityFather sigma u hsigma hu))
        (T (infiniteMobiusDoubledParityFisherDetail sigma hsigma)) = 0 := by
  rw [inner_map_detail_eq_of_contraction_saturates T hT _ _ hsat]
  rw [← inner_conj_symm]
  simp only [
    inner_infiniteMobiusDoubledParityFisherDetail_father_eq_zero
      hsigma hu,
    map_zero]

/-- A bounded saturated contraction realization of the continued Ward column.
The definition uses the actual doubled Möbius father/detail source, not an
abstract replacement Gram. -/
def ContinuedXiWardSaturatedMobiusParityRealization
    (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] : Prop :=
  ∀ w : ℂ, 0 < w.re →
    ∃ (sigma u : ℝ) (hsigma : 1 < sigma) (hu : 0 ≤ u)
      (T : infiniteMobiusDoubledHilbert →L[ℂ] K),
      ‖T‖ ≤ 1 ∧
      ‖T (infiniteMobiusDoubledParityFisherDetail sigma hsigma)‖ =
        ‖infiniteMobiusDoubledParityFisherDetail sigma hsigma‖ ∧
      inner ℂ
          (T (infiniteMobiusDoubledParityFather sigma u hsigma hu))
          (T (infiniteMobiusDoubledParityFisherDetail sigma hsigma)) =
        continuedXiAntiCausalWardResponse w

/-- Every saturated doubled-Möbius realization makes the entire continued Xi
Ward column vanish on the right half-plane. -/
theorem continuedXiAntiCausalWardResponse_eq_zero_of_saturatedMobiusParityRealization
    (hreal : ContinuedXiWardSaturatedMobiusParityRealization K)
    (w : ℂ) (hw : 0 < w.re) :
    continuedXiAntiCausalWardResponse w = 0 := by
  obtain ⟨sigma, u, hsigma, hu, T, hT, hsat, hcolumn⟩ :=
    hreal w hw
  rw [← hcolumn]
  exact
    inner_map_infiniteMobiusDoubledParityFather_detail_eq_zero
      T hT hsigma hu hsat

/-- **CCM endpoint connector.**  Constructing a genuine saturated contraction
from the exact doubled Möbius source to the continued Ward column proves RH.
The conclusion follows by testing a hypothetical strict-right zero at its
adapted Hardy node, where the response has strictly positive real part. -/
theorem riemannHypothesis_of_saturatedMobiusParityRealization
    (hreal : ContinuedXiWardSaturatedMobiusParityRealization K) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_for_boundaryLift hRH
  let w : ℂ :=
    (starRingEnd ℂ) (xiRightCenteredZero q.1)
  have hw : 0 < w.re := by
    simp only [w, Complex.conj_re]
    exact xiRightCenteredZero_re_pos q.1
  have hzero :
      continuedXiAntiCausalWardResponse w = 0 :=
    continuedXiAntiCausalWardResponse_eq_zero_of_saturatedMobiusParityRealization
      hreal w hw
  have hpos :
      0 < (continuedXiAntiCausalWardResponse w).re := by
    have hgt :=
      re_continuedXiAntiCausalWardResponse_at_adaptedNode_gt_inv q
    have hinv :
        0 < ((xiRightCenteredZero q.1).re)⁻¹ :=
      inv_pos.mpr (xiRightCenteredZero_re_pos q.1)
    simpa only [w] using hinv.trans hgt
  rw [hzero] at hpos
  simp at hpos

/-- At aperture zero the doubled Möbius father is a unit vector at every
Euler parameter. -/
theorem norm_infiniteMobiusDoubledParityFather_zero
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖infiniteMobiusDoubledParityFather sigma 0 hsigma (le_refl 0)‖ = 1 := by
  have hinner :=
    inner_infiniteMobiusDoubledParityFather hsigma (le_refl 0) (le_refl 0)
  rw [inner_infiniteMobiusCriticalDampedSignedWeightLp_eq_boundaryLayerLaplace
    hsigma (le_refl 0) (le_refl 0)] at hinner
  have hlaplace :
      squarefreeMobiusBoundaryLayerLaplace sigma (0 + 0) = 1 := by
    rw [squarefreeMobiusBoundaryLayerLaplace]
    simp only [mobiusCriticalBoundaryParameter, zero_mul, add_zero]
    exact_mod_cast div_self (ne_of_gt (squarefreeMobiusTotal_pos hsigma))
  rw [inner_self_eq_norm_sq_to_K, hlaplace] at hinner
  have hsq :
      ‖infiniteMobiusDoubledParityFather
        sigma 0 hsigma (le_refl 0)‖ ^ (2 : ℕ) = 1 := by
    have hc :
        ((‖infiniteMobiusDoubledParityFather
          sigma 0 hsigma (le_refl 0)‖ ^ (2 : ℕ) : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_pow]
      exact hinner
    exact Complex.ofReal_injective (by
      simpa only [Complex.ofReal_one] using hc)
  nlinarith [norm_nonneg
    (infiniteMobiusDoubledParityFather sigma 0 hsigma (le_refl 0))]

/-- Explicit cofinal Euler sequence approaching the critical boundary from
the source half-plane. -/
def mobiusParityCriticalSigmaSequence (n : ℕ) : ℝ :=
  1 + 1 / (n + 1)

theorem mobiusParityCriticalSigmaSequence_gt_one (n : ℕ) :
    1 < mobiusParityCriticalSigmaSequence n := by
  rw [mobiusParityCriticalSigmaSequence]
  have hden : (0 : ℝ) < n + 1 := by positivity
  have hinv : (0 : ℝ) < 1 / (n + 1) := one_div_pos.mpr hden
  linarith

theorem tendsto_mobiusParityCriticalSigmaSequence :
    Filter.Tendsto mobiusParityCriticalSigmaSequence Filter.atTop
      (nhdsWithin 1 (Set.Ioi 1)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hzero :
        Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1))
          Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [mobiusParityCriticalSigmaSequence, add_zero] using!
      tendsto_const_nhds.add hzero
  · exact Filter.Eventually.of_forall
      mobiusParityCriticalSigmaSequence_gt_one

/-- A cofinal contraction family from the actual doubled Möbius source to the
continued Xi Ward column.  The source approaches its four-unit boundary and
the transported detail loses asymptotically no energy. -/
def ContinuedXiWardCofinalMobiusParityRealization
    (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] : Prop :=
  ∀ w : ℂ, 0 < w.re →
    ∃ (sigma u : ℕ → ℝ)
      (hsigma : ∀ n, 1 < sigma n) (hu : ∀ n, 0 ≤ u n)
      (T : ℕ → infiniteMobiusDoubledHilbert →L[ℂ] K) (B : ℝ),
      Filter.Tendsto sigma Filter.atTop (nhdsWithin 1 (Set.Ioi 1)) ∧
      (∀ n, ‖T n‖ ≤ 1) ∧
      (∀ n,
        ‖infiniteMobiusDoubledParityFather
          (sigma n) (u n) (hsigma n) (hu n)‖ ≤ B) ∧
      Filter.Tendsto
        (fun n =>
          ‖infiniteMobiusDoubledParityFisherDetail
            (sigma n) (hsigma n)‖ ^ (2 : ℕ) -
          ‖T n (infiniteMobiusDoubledParityFisherDetail
            (sigma n) (hsigma n))‖ ^ (2 : ℕ))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun n =>
          inner ℂ
            (T n (infiniteMobiusDoubledParityFather
              (sigma n) (u n) (hsigma n) (hu n)))
            (T n (infiniteMobiusDoubledParityFisherDetail
              (sigma n) (hsigma n))))
        Filter.atTop (nhds (continuedXiAntiCausalWardResponse w))

/-- A cofinal four-unit Möbius realization forces the continued Ward response
to vanish throughout the right half-plane. -/
theorem continuedXiAntiCausalWardResponse_eq_zero_of_cofinalMobiusParityRealization
    (hreal : ContinuedXiWardCofinalMobiusParityRealization K)
    (w : ℂ) (hw : 0 < w.re) :
    continuedXiAntiCausalWardResponse w = 0 := by
  obtain ⟨sigma, u, hsigma, hu, T, B, _hsigmaLimit,
    hT, hbound, hloss, hcolumn⟩ := hreal w hw
  apply codiagonal_limit_eq_zero_of_cofinal_contractions
    T
    (fun n => infiniteMobiusDoubledParityFather
      (sigma n) (u n) (hsigma n) (hu n))
    (fun n => infiniteMobiusDoubledParityFisherDetail
      (sigma n) (hsigma n))
    B
  · exact hT
  · exact hbound
  · intro n
    rw [← inner_conj_symm]
    simp only [
      inner_infiniteMobiusDoubledParityFisherDetail_father_eq_zero
        (hsigma n) (hu n),
      map_zero]
  · exact hloss
  · exact hcolumn

/-- **Cofinal CCM endpoint connector.**  A bounded source-side contraction
lift with boundary diagonal four and column `r_P` proves RH. -/
theorem riemannHypothesis_of_cofinalMobiusParityRealization
    (hreal : ContinuedXiWardCofinalMobiusParityRealization K) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_for_boundaryLift hRH
  let w : ℂ :=
    (starRingEnd ℂ) (xiRightCenteredZero q.1)
  have hw : 0 < w.re := by
    simp only [w, Complex.conj_re]
    exact xiRightCenteredZero_re_pos q.1
  have hzero :
      continuedXiAntiCausalWardResponse w = 0 :=
    continuedXiAntiCausalWardResponse_eq_zero_of_cofinalMobiusParityRealization
      hreal w hw
  have hpos :
      0 < (continuedXiAntiCausalWardResponse w).re := by
    have hgt :=
      re_continuedXiAntiCausalWardResponse_at_adaptedNode_gt_inv q
    have hinv :
        0 < ((xiRightCenteredZero q.1).re)⁻¹ :=
      inv_pos.mpr (xiRightCenteredZero_re_pos q.1)
    simpa only [w] using hinv.trans hgt
  rw [hzero] at hpos
  simp at hpos

/-- Under RH the cofinal realization exists concretely: the Ward column
vanishes, so the identity contraction on the doubled Möbius source realizes
it while preserving the four-unit detail exactly. -/
theorem cofinalMobiusParityRealization_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ContinuedXiWardCofinalMobiusParityRealization
      infiniteMobiusDoubledHilbert := by
  intro w hw
  let sigma : ℕ → ℝ := mobiusParityCriticalSigmaSequence
  let u : ℕ → ℝ := fun _ => 0
  have hsigma : ∀ n, 1 < sigma n :=
    mobiusParityCriticalSigmaSequence_gt_one
  have hu : ∀ n, 0 ≤ u n := fun _ => le_refl 0
  let T : ℕ →
      infiniteMobiusDoubledHilbert →L[ℂ]
        infiniteMobiusDoubledHilbert :=
    fun _ => ContinuousLinearMap.id ℂ infiniteMobiusDoubledHilbert
  refine ⟨sigma, u, hsigma, hu, T, 1, ?_, ?_, ?_, ?_, ?_⟩
  · exact tendsto_mobiusParityCriticalSigmaSequence
  · intro n
    exact ContinuousLinearMap.norm_id_le
  · intro n
    simpa only [u] using
      (norm_infiniteMobiusDoubledParityFather_zero (hsigma n)).le
  · have hloss :
        (fun n =>
          ‖infiniteMobiusDoubledParityFisherDetail
            (sigma n) (hsigma n)‖ ^ (2 : ℕ) -
          ‖T n (infiniteMobiusDoubledParityFisherDetail
            (sigma n) (hsigma n))‖ ^ (2 : ℕ)) =
          fun _ => 0 := by
      funext n
      simp [T]
    rw [hloss]
    exact tendsto_const_nhds
  · have hresponse :
        continuedXiAntiCausalWardResponse w = 0 :=
      continuedXiAntiCausalWardResponse_eq_zero_of_riemannHypothesis
        hRH hw
    have hcolumn :
        (fun n =>
          inner ℂ
            (T n (infiniteMobiusDoubledParityFather
              (sigma n) (u n) (hsigma n) (hu n)))
            (T n (infiniteMobiusDoubledParityFisherDetail
              (sigma n) (hsigma n)))) =
          fun _ => 0 := by
      funext n
      simp only [T, ContinuousLinearMap.id_apply]
      rw [← inner_conj_symm]
      simp only [
        inner_infiniteMobiusDoubledParityFisherDetail_father_eq_zero
          (hsigma n) (hu n),
        map_zero]
    rw [hcolumn, hresponse]
    exact tendsto_const_nhds

/-- **Exact classification of the cofinal contraction proposal.**  A
four-unit cofinal contraction from the concrete doubled Möbius source creates
the continued Xi Ward column exactly if RH is true.  Thus this construction is
not an independent shortcut: its missing source contraction is an RH-complete
object. -/
theorem riemannHypothesis_iff_cofinalMobiusParityRealization :
    RiemannHypothesis ↔
      ContinuedXiWardCofinalMobiusParityRealization
        infiniteMobiusDoubledHilbert :=
  ⟨cofinalMobiusParityRealization_of_riemannHypothesis,
    riemannHypothesis_of_cofinalMobiusParityRealization⟩

end

end RHTower
