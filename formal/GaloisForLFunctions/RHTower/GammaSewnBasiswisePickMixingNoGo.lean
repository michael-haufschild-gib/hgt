import GaloisForLFunctions.HTGeometry.BasiswiseBoundaryPickRigidity
import GaloisForLFunctions.RHTower.GammaSewnMobiusPickObstruction

/-!
# Gamma-sewn basiswise Pick mixing no-go

The fixed-prime Gamma-sewn scalar multipliers have quadratic contact with the lossless boundary.
When all primes are placed in an arbitrary Hilbert basis and given the common aperture node
`exp (-x)`, this makes every basiswise normalized loss vanish at zero aperture.  The universal
basiswise boundary-charge law then proves that no off-diagonal operator mixing, in any Hilbert
dimension, can restore Pick positivity while preserving all Gamma-sewn prime marginals.

The obstruction assumes only strong convergence on basis vectors.  A second theorem records the
norm-continuous specialization.  No finite-rank, compactness, trace-class, or separability
hypothesis is present.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-- Gamma-sewn diagonal loss after replacing the prime-dependent Möbius disk node by the common
physical aperture node `exp (-x)`. -/
def gammaSewnMobiusCommonAperturePickDiagonal
    (x : ℝ) (p : Nat.Primes) : ℝ :=
  HTGeometry.pickDiagonalDefect
    (gammaSewnMobiusValuationContractionMultiplier x p)
    (Real.exp (-x))

private theorem tendsto_one_sub_exp_neg_mul_div_self_nhdsGT_zero (L : ℝ) :
    Tendsto (fun x : ℝ => (1 - Real.exp (-(L * x))) / x)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 L) := by
  have hderiv : HasDerivAt (fun x : ℝ => 1 - Real.exp (-(L * x))) L 0 := by
    have hlinear : HasDerivAt (fun x : ℝ => -(L * x)) (-L) 0 := by
      simpa only [id_eq, neg_mul, mul_one] using!
        (hasDerivAt_id (𝕜 := ℝ) 0).const_mul (-L)
    have hraw := (hasDerivAt_const (x := 0) (c := (1 : ℝ))).sub
      ((Real.hasDerivAt_exp (-(L * 0))).comp 0 hlinear)
    simpa only [Function.comp_apply] using! hraw.congr_deriv (by norm_num)
  have hslope := hderiv.tendsto_slope_zero_right
  apply hslope.congr'
  filter_upwards with x
  simp only [zero_add, mul_zero, neg_zero, Real.exp_zero, sub_self, sub_zero,
    smul_eq_mul, div_eq_mul_inv]
  ring

/-- Every actual Gamma-sewn prime marginal has zero first-order normalized loss at the common
aperture boundary. -/
theorem tendsto_gammaSewnMobius_commonAperturePickDiagonal_nhdsGT_zero
    (p : Nat.Primes) :
    Tendsto (fun x : ℝ => gammaSewnMobiusCommonAperturePickDiagonal x p)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 0) := by
  let L := Real.log (p : ℝ)
  let qp : ℝ → ℝ := fun x => xiMobiusContinuousApertureDiskNode x p
  let r : ℝ → ℝ := fun x => Real.exp (-x)
  have hnumSlope : Tendsto (fun x : ℝ => (1 - qp x ^ (2 : ℕ)) / x)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (2 * L)) := by
    have h := tendsto_one_sub_exp_neg_mul_div_self_nhdsGT_zero (2 * L)
    convert h using 1
    funext x
    simp only [qp, xiMobiusContinuousApertureDiskNode, L]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hdenSlope : Tendsto (fun x : ℝ => (1 - r x ^ (2 : ℕ)) / x)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 2) := by
    have h := tendsto_one_sub_exp_neg_mul_div_self_nhdsGT_zero 2
    convert h using 1
    funext x
    simp only [r]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hratio : Tendsto (fun x : ℝ => (1 - qp x ^ (2 : ℕ)) / (1 - r x ^ (2 : ℕ)))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 L) := by
    have hdiv := hnumSlope.div hdenSlope (by norm_num)
    have heq :
        ((fun x : ℝ => (1 - qp x ^ (2 : ℕ)) / x) /
            (fun x : ℝ => (1 - r x ^ (2 : ℕ)) / x)) =ᶠ[nhdsWithin (0 : ℝ) (Ioi 0)]
          (fun x : ℝ => (1 - qp x ^ (2 : ℕ)) / (1 - r x ^ (2 : ℕ))) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      have hr0 : 0 < r x := Real.exp_pos _
      have hr1 : r x < 1 := by
        dsimp only [r]
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (neg_lt_zero.mpr hx)
      have hrden : 1 - r x ^ (2 : ℕ) ≠ 0 := by nlinarith
      change ((1 - qp x ^ (2 : ℕ)) / x) / ((1 - r x ^ (2 : ℕ)) / x) =
        (1 - qp x ^ (2 : ℕ)) / (1 - r x ^ (2 : ℕ))
      field_simp [hx0, hrden]
    convert hdiv.congr' heq using 1
    ring
  have hprime := tendsto_gammaSewnMobius_pickDiagonalDefect_nhdsGT_zero p
  have hprod := hprime.mul hratio
  have heq :
      (fun x : ℝ => HTGeometry.pickDiagonalDefect
          (gammaSewnMobiusValuationContractionMultiplier x p) (qp x) *
        ((1 - qp x ^ (2 : ℕ)) / (1 - r x ^ (2 : ℕ)))) =ᶠ[nhdsWithin (0 : ℝ) (Ioi 0)]
      (fun x : ℝ => gammaSewnMobiusCommonAperturePickDiagonal x p) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hqp : qp x < 1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
    have hqp0 : 0 < qp x := xiMobiusContinuousApertureDiskNode_pos x p
    have hr : r x < 1 := by
      dsimp only [r]
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (neg_lt_zero.mpr hx)
    have hr0 : 0 < r x := Real.exp_pos _
    simp only [gammaSewnMobiusCommonAperturePickDiagonal, r,
      HTGeometry.pickDiagonalDefect]
    field_simp [show 1 - qp x ^ (2 : ℕ) ≠ 0 by nlinarith,
      show 1 - r x ^ (2 : ℕ) ≠ 0 by nlinarith]
  simpa only [zero_mul] using hprod.congr' heq

/-- **Gamma-sewn infinite-dimensional mixing no-go.**  For an arbitrary Hilbert basis indexed by
actual primes, there is no operator family which simultaneously

* converges strongly to the identity on every basis vector at zero aperture;
* preserves every actual Gamma-sewn prime marginal norm; and
* satisfies the common-aperture operator Pick inequalities.

The index type and Hilbert space are arbitrary; in particular this theorem is not finite-rank.
-/
theorem not_exists_gammaSewnMobius_basisMarginal_commonAperturePickFamily
    {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [Nonempty ι] (b : HilbertBasis ι ℝ E) (prime : ι → Nat.Primes) :
    ¬ ∃ T : ℝ → E →L[ℝ] E,
        (∀ i, Tendsto (fun y : ℝ => T y (b i))
          (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (b i))) ∧
        (∀ x, 0 < x → ∀ i,
          ‖T x (b i)‖ =
            gammaSewnMobiusValuationContractionMultiplier x (prime i)) ∧
        (∀ x y, 0 < x → 0 < y → ∀ u v,
          HTGeometry.operatorPickCross (T x) (T y)
                (Real.exp (-x)) (Real.exp (-y)) u v ^ (2 : ℕ) ≤
            HTGeometry.operatorPickDiagonal (T x) (Real.exp (-x)) u *
              HTGeometry.operatorPickDiagonal (T y) (Real.exp (-y)) v) := by
  rintro ⟨T, hTbasis, hmarginal, hpick⟩
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0)
  have hq : Tendsto (fun y : ℝ => Real.exp (-y)) l (𝓝 1) := by
    have hcont : ContinuousAt (fun y : ℝ => Real.exp (-y)) 0 := by fun_prop
    simpa only [Real.exp_zero, neg_zero] using! hcont.tendsto.mono_left inf_le_left
  have hqone : Real.exp (-(1 : ℝ)) ≠ 1 := by
    have hlt : Real.exp (-(1 : ℝ)) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    exact hlt.ne
  have hdiag : ∀ i,
      Tendsto
        (fun y : ℝ => HTGeometry.operatorPickDiagonal
          (T y) (Real.exp (-y)) (b i)) l (𝓝 0) := by
    intro i
    have hscalar :=
      tendsto_gammaSewnMobius_commonAperturePickDiagonal_nhdsGT_zero (prime i)
    apply hscalar.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [HTGeometry.operatorPickDiagonal,
      gammaSewnMobiusCommonAperturePickDiagonal,
      HTGeometry.pickDiagonalDefect, hmarginal y hy i,
      b.orthonormal.norm_eq_one, one_pow]
  have hpickOne : ∀ᶠ y in l, ∀ u v,
      HTGeometry.operatorPickCross (T 1) (T y)
            (Real.exp (-(1 : ℝ))) (Real.exp (-y)) u v ^ (2 : ℕ) ≤
        HTGeometry.operatorPickDiagonal (T 1) (Real.exp (-(1 : ℝ))) u *
          HTGeometry.operatorPickDiagonal (T y) (Real.exp (-y)) v := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hpick 1 y (by norm_num) hy
  have hidentity : T 1 = ContinuousLinearMap.id ℝ E :=
    HTGeometry.continuousLinearMap_eq_id_of_basiswise_boundaryPick b
      (T 1) (Real.exp (-(1 : ℝ))) T (fun y : ℝ => Real.exp (-y))
      hq hqone hTbasis hdiag hpickOne
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  have hm := hmarginal 1 (by norm_num) i
  rw [hidentity] at hm
  have hone : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
  simp only [ContinuousLinearMap.id_apply, hone] at hm
  have hlt := gammaSewnMobiusValuationContractionMultiplier_lt_one
    (x := (1 : ℝ)) (by norm_num) (prime i)
  linarith

/-- Operator-norm continuity at the lossless endpoint implies the strong basis convergence used
by the dimension-free no-go theorem. -/
theorem not_exists_continuous_gammaSewnMobius_basisMarginal_commonAperturePickFamily
    {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [Nonempty ι] (b : HilbertBasis ι ℝ E) (prime : ι → Nat.Primes) :
    ¬ ∃ T : ℝ → E →L[ℝ] E,
        T 0 = ContinuousLinearMap.id ℝ E ∧
        ContinuousAt T 0 ∧
        (∀ x, 0 < x → ∀ i,
          ‖T x (b i)‖ =
            gammaSewnMobiusValuationContractionMultiplier x (prime i)) ∧
        (∀ x y, 0 < x → 0 < y → ∀ u v,
          HTGeometry.operatorPickCross (T x) (T y)
                (Real.exp (-x)) (Real.exp (-y)) u v ^ (2 : ℕ) ≤
            HTGeometry.operatorPickDiagonal (T x) (Real.exp (-x)) u *
              HTGeometry.operatorPickDiagonal (T y) (Real.exp (-y)) v) := by
  rintro ⟨T, hT0, hTcont, hmarginal, hpick⟩
  apply not_exists_gammaSewnMobius_basisMarginal_commonAperturePickFamily b prime
  refine ⟨T, ?_, hmarginal, hpick⟩
  intro i
  have hTop : Tendsto T (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (T 0)) :=
    hTcont.tendsto.mono_left inf_le_left
  have heval :=
    (ContinuousLinearMap.apply ℝ E (b i)).continuous.continuousAt.tendsto.comp hTop
  simpa only [hT0, ContinuousLinearMap.id_apply] using! heval

end

end RHTower
