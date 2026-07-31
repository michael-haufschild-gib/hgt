/-
# First and second jets of Bourgain's normalized Taylor phases

The normalized cubic and quartic remainders used in Bourgain's local
mean-value reduction are exact functions, not asymptotic placeholders.
This module computes their first two jets.  These are the entries of the
two-base osculating coordinate matrix used by the planar decoupling step.
-/
import GaloisForLFunctions.RHTower.BourgainNormalizedTaylorRemainderBound

namespace RHTower

noncomputable section

/-- First derivative of a translated and scaled real power. -/
theorem iteratedDeriv_bourgainAffineRpow_one
    {q r t : ℝ} (hbase : 0 < 1 + q * t) :
    iteratedDeriv 1 (bourgainAffineRpow q r) t =
      q * r * (1 + q * t) ^ (r - 1) := by
  rw [iteratedDeriv_one]
  unfold bourgainAffineRpow
  have haffine :
      HasDerivAt (fun y : ℝ => 1 + q * y) q t := by
    convert! (hasDerivAt_const t (1 : ℝ)).add
      ((hasDerivAt_id t).const_mul q) using 1 ; ring_nf
  convert! (haffine.rpow_const (p := r) (Or.inl hbase.ne')).deriv using 1

/-- Second derivative of a translated and scaled real power. -/
theorem iteratedDeriv_bourgainAffineRpow_two
    {q r t : ℝ} (hbase : 0 < 1 + q * t) :
    iteratedDeriv 2 (bourgainAffineRpow q r) t =
      q ^ (2 : ℕ) * (descPochhammer ℝ 2).eval r *
        (1 + q * t) ^ (r - 2) := by
  let g : ℝ → ℝ := fun u => u ^ r
  let f : ℝ → ℝ := fun x => 1 + q * x
  have hg : ContDiffAt ℝ 2 g (f t) :=
    Real.contDiffAt_rpow_const_of_ne hbase.ne'
  have hf : ContDiffAt ℝ 2 f t := by
    dsimp [f]
    fun_prop
  have hcomp := iteratedDeriv_comp_two hg hf
  change iteratedDeriv 2 (g ∘ f) t = _ at hcomp
  change iteratedDeriv 2 (g ∘ f) t = _
  rw [hcomp]
  dsimp [g, f]
  simp only [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
  norm_num [Function.iterate_succ_apply', descPochhammer]
  ring

theorem iteratedDeriv_bourgainThreeHalvesTaylorPolynomial_one
    (q t : ℝ) :
    iteratedDeriv 1 (bourgainThreeHalvesTaylorPolynomial q) t =
      (3 / 2 : ℝ) * q + (3 / 4 : ℝ) * q ^ (2 : ℕ) * t := by
  rw [iteratedDeriv_one]
  unfold bourgainThreeHalvesTaylorPolynomial
  convert!
    (((hasDerivAt_const t (1 : ℝ)).add
      ((hasDerivAt_id t).const_mul ((3 / 2 : ℝ) * q))).add
        (((hasDerivAt_id t).pow 2).const_mul
          ((3 / 8 : ℝ) * q ^ (2 : ℕ)))).deriv using 1 ;
    simp only [id_eq] ; ring

theorem iteratedDeriv_bourgainThreeHalvesTaylorPolynomial_two
    (q t : ℝ) :
    iteratedDeriv 2 (bourgainThreeHalvesTaylorPolynomial q) t =
      (3 / 4 : ℝ) * q ^ (2 : ℕ) := by
  rw [show
    iteratedDeriv 2 (bourgainThreeHalvesTaylorPolynomial q) t =
      deriv (iteratedDeriv 1
        (bourgainThreeHalvesTaylorPolynomial q)) t by
      simpa using congrFun
        (iteratedDeriv_succ
          (n := 1) (f := bourgainThreeHalvesTaylorPolynomial q)) t]
  have heq :
      iteratedDeriv 1 (bourgainThreeHalvesTaylorPolynomial q) =
        fun x : ℝ =>
          (3 / 2 : ℝ) * q + (3 / 4 : ℝ) * q ^ (2 : ℕ) * x := by
    funext x
    exact iteratedDeriv_bourgainThreeHalvesTaylorPolynomial_one q x
  rw [heq]
  convert!
    ((hasDerivAt_const t ((3 / 2 : ℝ) * q)).add
      ((hasDerivAt_id t).const_mul
        ((3 / 4 : ℝ) * q ^ (2 : ℕ)))).deriv using 1 ; ring

/-- Exact first jet of the normalized cubic phase. -/
theorem iteratedDeriv_bourgainNormalizedCubicRemainder_one
    {q t : ℝ} (hq : q ≠ 0) (hbase : 0 < 1 + q * t) :
    iteratedDeriv 1 (bourgainNormalizedCubicRemainder q) t =
      12 / q ^ (2 : ℕ) *
        ((1 + q * t) ^ (1 / 2 : ℝ) - 1) ^ (2 : ℕ) := by
  unfold bourgainNormalizedCubicRemainder
  rw [iteratedDeriv_const_mul_field]
  change (-16 / q ^ (3 : ℕ)) *
    iteratedDeriv 1
      (bourgainAffineRpow q (3 / 2 : ℝ) -
        bourgainThreeHalvesTaylorPolynomial q) t = _
  rw [iteratedDeriv_sub
    (contDiffAt_bourgainAffineRpow hbase)
    (by
      unfold bourgainThreeHalvesTaylorPolynomial
      fun_prop)]
  rw [iteratedDeriv_bourgainAffineRpow_one hbase,
    iteratedDeriv_bourgainThreeHalvesTaylorPolynomial_one]
  have hrpow :
      ((1 + q * t) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = 1 + q * t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
    norm_num
  norm_num
  field_simp
  nlinarith

/-- Exact second jet of the normalized cubic phase. -/
theorem iteratedDeriv_bourgainNormalizedCubicRemainder_two
    {q t : ℝ} (hq : q ≠ 0) (hbase : 0 < 1 + q * t) :
    iteratedDeriv 2 (bourgainNormalizedCubicRemainder q) t =
      12 / q * (1 - (1 + q * t) ^ (-(1 / 2 : ℝ))) := by
  unfold bourgainNormalizedCubicRemainder
  rw [iteratedDeriv_const_mul_field]
  change (-16 / q ^ (3 : ℕ)) *
    iteratedDeriv 2
      (bourgainAffineRpow q (3 / 2 : ℝ) -
        bourgainThreeHalvesTaylorPolynomial q) t = _
  rw [iteratedDeriv_sub
    (contDiffAt_bourgainAffineRpow hbase)
    (by
      unfold bourgainThreeHalvesTaylorPolynomial
      fun_prop)]
  rw [iteratedDeriv_bourgainAffineRpow_two hbase,
    iteratedDeriv_bourgainThreeHalvesTaylorPolynomial_two]
  norm_num [descPochhammer]
  field_simp
  ring

theorem iteratedDeriv_bourgainHalfTaylorPolynomial_one
    (q t : ℝ) :
    iteratedDeriv 1 (bourgainHalfTaylorPolynomial q) t =
      (1 / 2 : ℝ) * q - (1 / 4 : ℝ) * q ^ (2 : ℕ) * t := by
  rw [iteratedDeriv_one]
  unfold bourgainHalfTaylorPolynomial
  convert!
    (((hasDerivAt_const t (1 : ℝ)).add
      ((hasDerivAt_id t).const_mul ((1 / 2 : ℝ) * q))).sub
        (((hasDerivAt_id t).pow 2).const_mul
          ((1 / 8 : ℝ) * q ^ (2 : ℕ)))).deriv using 1 ;
    simp only [id_eq] ; ring

theorem iteratedDeriv_bourgainHalfTaylorPolynomial_two
    (q t : ℝ) :
    iteratedDeriv 2 (bourgainHalfTaylorPolynomial q) t =
      -(1 / 4 : ℝ) * q ^ (2 : ℕ) := by
  rw [show
    iteratedDeriv 2 (bourgainHalfTaylorPolynomial q) t =
      deriv (iteratedDeriv 1 (bourgainHalfTaylorPolynomial q)) t by
      simpa using congrFun
        (iteratedDeriv_succ
          (n := 1) (f := bourgainHalfTaylorPolynomial q)) t]
  have heq :
      iteratedDeriv 1 (bourgainHalfTaylorPolynomial q) =
        fun x : ℝ =>
          (1 / 2 : ℝ) * q - (1 / 4 : ℝ) * q ^ (2 : ℕ) * x := by
    funext x
    exact iteratedDeriv_bourgainHalfTaylorPolynomial_one q x
  rw [heq]
  convert!
    ((hasDerivAt_const t ((1 / 2 : ℝ) * q)).sub
      ((hasDerivAt_id t).const_mul
        ((1 / 4 : ℝ) * q ^ (2 : ℕ)))).deriv using 1 ; ring

/-- Exact first jet of the normalized quartic phase. -/
theorem iteratedDeriv_bourgainNormalizedQuarticRemainder_one
    {q t : ℝ} (hq : q ≠ 0) (hbase : 0 < 1 + q * t) :
    iteratedDeriv 1 (bourgainNormalizedQuarticRemainder q) t =
      32 / q ^ (3 : ℕ) *
        ((1 + q * t) -
          3 * (1 + q * t) ^ (1 / 2 : ℝ) + 3 -
          (1 + q * t) ^ (-(1 / 2 : ℝ))) := by
  unfold bourgainNormalizedQuarticRemainder
  change iteratedDeriv 1
    ((fun x : ℝ => (4 / q) * bourgainNormalizedCubicRemainder q x) -
      (fun x : ℝ =>
        (64 / q ^ (4 : ℕ)) *
          (bourgainAffineRpow q (1 / 2 : ℝ) x -
            bourgainHalfTaylorPolynomial q x))) t = _
  rw [iteratedDeriv_sub
    (contDiffAt_const.mul
      (contDiffAt_bourgainNormalizedCubicRemainder hbase))
    (contDiffAt_const.mul
      ((contDiffAt_bourgainAffineRpow hbase).sub
        (by
          unfold bourgainHalfTaylorPolynomial
          fun_prop)))]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  change (4 / q) *
      iteratedDeriv 1 (bourgainNormalizedCubicRemainder q) t -
    (64 / q ^ (4 : ℕ)) *
      iteratedDeriv 1
        (bourgainAffineRpow q (1 / 2 : ℝ) -
          bourgainHalfTaylorPolynomial q) t = _
  rw [iteratedDeriv_bourgainNormalizedCubicRemainder_one hq hbase]
  rw [iteratedDeriv_sub
    (contDiffAt_bourgainAffineRpow hbase)
    (by
      unfold bourgainHalfTaylorPolynomial
      fun_prop)]
  rw [iteratedDeriv_bourgainAffineRpow_one hbase,
    iteratedDeriv_bourgainHalfTaylorPolynomial_one]
  have hrpow :
      ((1 + q * t) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = 1 + q * t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
    norm_num
  norm_num
  field_simp
  nlinarith

/-- Exact second jet of the normalized quartic phase. -/
theorem iteratedDeriv_bourgainNormalizedQuarticRemainder_two
    {q t : ℝ} (hq : q ≠ 0) (hbase : 0 < 1 + q * t) :
    iteratedDeriv 2 (bourgainNormalizedQuarticRemainder q) t =
      16 / q ^ (2 : ℕ) *
        (2 - 3 * (1 + q * t) ^ (-(1 / 2 : ℝ)) +
          (1 + q * t) ^ (-(3 / 2 : ℝ))) := by
  unfold bourgainNormalizedQuarticRemainder
  change iteratedDeriv 2
    ((fun x : ℝ => (4 / q) * bourgainNormalizedCubicRemainder q x) -
      (fun x : ℝ =>
        (64 / q ^ (4 : ℕ)) *
          (bourgainAffineRpow q (1 / 2 : ℝ) x -
            bourgainHalfTaylorPolynomial q x))) t = _
  rw [iteratedDeriv_sub
    (contDiffAt_const.mul
      (contDiffAt_bourgainNormalizedCubicRemainder hbase))
    (contDiffAt_const.mul
      ((contDiffAt_bourgainAffineRpow hbase).sub
        (by
          unfold bourgainHalfTaylorPolynomial
          fun_prop)))]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  change (4 / q) *
      iteratedDeriv 2 (bourgainNormalizedCubicRemainder q) t -
    (64 / q ^ (4 : ℕ)) *
      iteratedDeriv 2
        (bourgainAffineRpow q (1 / 2 : ℝ) -
          bourgainHalfTaylorPolynomial q) t = _
  rw [iteratedDeriv_bourgainNormalizedCubicRemainder_two hq hbase]
  rw [iteratedDeriv_sub
    (contDiffAt_bourgainAffineRpow hbase)
    (by
      unfold bourgainHalfTaylorPolynomial
      fun_prop)]
  rw [iteratedDeriv_bourgainAffineRpow_two hbase,
    iteratedDeriv_bourgainHalfTaylorPolynomial_two]
  norm_num [descPochhammer]
  field_simp
  ring

end

end RHTower
