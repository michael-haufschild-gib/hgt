import GaloisForLFunctions.RHTower.HeatMultiplierTail
import GaloisForLFunctions.HTGeometry.FinitePiProductSummability

/-!
# Derivative control for the off-centre heat remainder

The off-centre Poisson bumps are not only uniformly exponentially small on the phase window; their
sum is uniformly Lipschitz there with one additional inverse-aperture factor.  This is the endpoint
estimate needed for pole-filled logarithmic Mellin moments.
-/

open Filter Set Topology

namespace RHTower

noncomputable section

/-- Phase derivative of one real Poisson Gaussian bump. -/
theorem hasDerivAt_heatGauss_phase (x : ℝ) (n : ℤ) (theta : ℝ) :
    HasDerivAt (heatGauss x n)
      (-((theta - 2 * Real.pi * (n : ℝ)) / (2 * Real.pi * x)) *
        heatGauss x n theta) theta := by
  have hraw : HasDerivAt (heatGauss x n)
      (Real.exp (-((theta - 2 * Real.pi * (n : ℝ)) ^ 2 /
          (4 * Real.pi * x))) *
        (-(2 * (theta - 2 * Real.pi * (n : ℝ)) ^ (2 - 1) * 1 /
          (4 * Real.pi * x)))) theta := by
    change HasDerivAt
      (fun t : ℝ => Real.exp (-((t - 2 * Real.pi * (n : ℝ)) ^ 2 /
        (4 * Real.pi * x)))) _ theta
    have h := (((((hasDerivAt_id theta).sub_const
      (2 * Real.pi * (n : ℝ))).pow 2).div_const
        (4 * Real.pi * x)).neg.exp)
    simpa only [Nat.cast_ofNat, one_mul, id_eq, Pi.neg_apply, Pi.pow_apply] using h
  apply hraw.congr_deriv
  rw [heatGauss]
  ring

/-- Closed-window version of the off-centre Gaussian majorant, including the endpoint `theta=0`. -/
theorem heatGauss_le_majorant_closed {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    {theta : ℝ} (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ Real.pi)
    (n : ℤ) (hn : n ≠ 0) :
    heatGauss x n theta ≤
      Real.exp (-(Real.pi / (4 * x))) * heatTailMajorant n := by
  rcases htheta0.eq_or_lt with rfl | htheta
  · have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have hnabs : (1 : ℝ) ≤ |(n : ℝ)| := by
        have : (1 : ℤ) ≤ |n| := Int.one_le_abs (by exact_mod_cast hn)
        calc
          (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
          _ ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast this
          _ = |(n : ℝ)| := by push_cast [Int.cast_abs]; ring
      nlinarith [sq_abs ((n : ℝ))]
    rw [heatGauss, heatTailMajorant, if_neg hn, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hsplit : Real.pi / (4 * x) + Real.pi * ((n : ℝ) ^ 2 - 1) / 4
        ≤ Real.pi * ((n : ℝ) ^ 2) / x := by
      have hA : Real.pi * ((n : ℝ) ^ 2 - 1) / 4
          ≤ Real.pi * ((n : ℝ) ^ 2 - 1) / (4 * x) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        nlinarith [mul_nonneg (mul_nonneg hpi.le (sub_nonneg.mpr hn2))
          (sub_nonneg.mpr hx1)]
      have hB : Real.pi / (4 * x) +
          Real.pi * ((n : ℝ) ^ 2 - 1) / (4 * x) =
          Real.pi * ((n : ℝ) ^ 2) / (4 * x) := by
        field_simp
        ring
      calc
        _ ≤ Real.pi * ((n : ℝ) ^ 2) / (4 * x) := by linarith
        _ ≤ Real.pi * ((n : ℝ) ^ 2) / x := by
          gcongr
          nlinarith [hx]
    have hzero :
        -((0 - 2 * Real.pi * (n : ℝ)) ^ 2 / (4 * Real.pi * x)) =
          -(Real.pi * (n : ℝ) ^ 2 / x) := by
      field_simp
      ring
    rw [hzero]
    linarith
  · exact heatGauss_le_majorant hx hx1 htheta htheta1 n hn

/-- Weighted off-centre lattice majorant for one phase derivative. -/
noncomputable def heatTailDerivativeMajorant (n : ℤ) : ℝ :=
  |(n : ℝ)| * heatTailMajorant n

theorem heatTailDerivativeMajorant_nonneg (n : ℤ) :
    0 ≤ heatTailDerivativeMajorant n := by
  exact mul_nonneg (abs_nonneg _) (heatTailMajorant_nonneg n)

theorem summable_heatTailDerivativeMajorant :
    Summable heatTailDerivativeMajorant := by
  let B : ℤ → ℝ := fun n => Real.exp (Real.pi / 4) *
    ((1 + (n.natAbs : ℝ)) ^ 1 *
      Real.exp (-(Real.pi / 4) * (n : ℝ) ^ 2))
  have hB : Summable B := by
    exact (GaloisForLFunctions.summable_one_add_natAbs_pow_mul_exp_neg_int_sq
      1 (by positivity : 0 < Real.pi / 4)).mul_left _
  refine Summable.of_nonneg_of_le heatTailDerivativeMajorant_nonneg (fun n => ?_) hB
  rw [heatTailDerivativeMajorant, heatTailMajorant]
  by_cases hn : n = 0
  · simp [hn, B, Real.exp_nonneg]
  · rw [if_neg hn]
    have habs : |(n : ℝ)| = (n.natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [habs, show -(Real.pi * ((n : ℝ) ^ 2 - 1) / 4) =
      Real.pi / 4 + (-(Real.pi / 4) * (n : ℝ) ^ 2) by ring,
      Real.exp_add]
    dsimp [B]
    have hnonneg : 0 ≤ Real.exp (Real.pi / 4) *
        Real.exp (-(Real.pi / 4) * (n : ℝ) ^ 2) := by positivity
    calc
      (n.natAbs : ℝ) *
          (Real.exp (Real.pi / 4) * Real.exp (-(Real.pi / 4) * (n : ℝ) ^ 2)) ≤
          (1 + (n.natAbs : ℝ)) *
            (Real.exp (Real.pi / 4) * Real.exp (-(Real.pi / 4) * (n : ℝ) ^ 2)) := by
              gcongr
              norm_num
      _ = Real.exp (Real.pi / 4) *
          ((1 + (n.natAbs : ℝ)) ^ 1 *
            Real.exp (-(Real.pi / 4) * (n : ℝ) ^ 2)) := by ring

/-- Total derivative majorant mass. -/
noncomputable def heatTailDerivativeConst : ℝ :=
  ∑' n : ℤ, heatTailDerivativeMajorant n

theorem heatTailDerivativeConst_nonneg : 0 ≤ heatTailDerivativeConst :=
  tsum_nonneg heatTailDerivativeMajorant_nonneg

/-- One off-centre bump is Lipschitz on the positive phase half-window with an exponentially small
constant. -/
theorem abs_heatGauss_sub_zero_le {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    {theta : ℝ} (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ Real.pi)
    (n : ℤ) (hn : n ≠ 0) :
    |heatGauss x n theta - heatGauss x n 0| ≤
      theta * ((3 / (2 * x)) * Real.exp (-(Real.pi / (4 * x))) *
        heatTailDerivativeMajorant n) := by
  let C : ℝ := (3 / (2 * x)) * Real.exp (-(Real.pi / (4 * x))) *
    heatTailDerivativeMajorant n
  have hdiff : ∀ t ∈ Icc (0 : ℝ) theta, DifferentiableAt ℝ (heatGauss x n) t := by
    intro t ht
    exact (hasDerivAt_heatGauss_phase x n t).differentiableAt
  have hbound : ∀ t ∈ Icc (0 : ℝ) theta,
      ‖fderiv ℝ (heatGauss x n) t‖ ≤ C := by
    intro t ht
    have hderiv := hasDerivAt_heatGauss_phase x n t
    rw [hderiv.hasFDerivAt.fderiv, ContinuousLinearMap.norm_toSpanSingleton,
      Real.norm_eq_abs, abs_mul, abs_neg, abs_div,
      abs_of_pos (mul_pos (mul_pos (by positivity) Real.pi_pos) hx),
      abs_of_pos (heatGauss_pos x n t)]
    have htpi : t ≤ Real.pi := ht.2.trans htheta1
    have hgauss := heatGauss_le_majorant_closed hx hx1 ht.1 htpi n hn
    have hdist : |t - 2 * Real.pi * (n : ℝ)| ≤
        3 * Real.pi * |(n : ℝ)| := by
      have hnabs : (1 : ℝ) ≤ |(n : ℝ)| := by
        have : (1 : ℤ) ≤ |n| := Int.one_le_abs (by exact_mod_cast hn)
        calc
          (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
          _ ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast this
          _ = |(n : ℝ)| := by push_cast [Int.cast_abs]; ring
      calc
        |t - 2 * Real.pi * (n : ℝ)|
            ≤ |t| + |2 * Real.pi * (n : ℝ)| := abs_sub _ _
        _ = t + 2 * Real.pi * |(n : ℝ)| := by
          rw [abs_of_nonneg ht.1, abs_mul,
            abs_of_pos (by positivity : 0 < 2 * Real.pi)]
        _ ≤ 3 * Real.pi * |(n : ℝ)| := by
          nlinarith [htpi, Real.pi_pos]
    dsimp [C, heatTailDerivativeMajorant]
    have hden : 0 < 2 * Real.pi * x := by positivity
    calc
      |t - 2 * Real.pi * (n : ℝ)| / (2 * Real.pi * x) * heatGauss x n t
          ≤ (3 * Real.pi * |(n : ℝ)|) / (2 * Real.pi * x) *
            (Real.exp (-(Real.pi / (4 * x))) * heatTailMajorant n) := by
              gcongr
              exact (heatGauss_pos x n t).le
      _ = (3 / (2 * x)) * Real.exp (-(Real.pi / (4 * x))) *
            (|(n : ℝ)| * heatTailMajorant n) := by
              field_simp
  have hmv := (convex_Icc (0 : ℝ) theta).norm_image_sub_le_of_norm_fderiv_le
    hdiff hbound ⟨le_rfl, htheta0⟩ ⟨htheta0, le_rfl⟩
  dsimp [C] at hmv
  simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg htheta0, mul_comm] using hmv

/-- Off-centre summand, with the central lattice point deleted. -/
noncomputable def heatRemainderTerm (x theta : ℝ) (n : ℤ) : ℝ :=
  if n = 0 then 0 else heatGauss x n theta

theorem summable_heatRemainderTerm {x : ℝ} (hx : 0 < x) (theta : ℝ) :
    Summable (heatRemainderTerm x theta) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (summable_heatGauss hx theta)
  · by_cases hn : n = 0
    · simp [heatRemainderTerm, hn]
    · rw [heatRemainderTerm, if_neg hn]
      exact (heatGauss_pos x n theta).le
  · by_cases hn : n = 0
    · rw [heatRemainderTerm, if_pos hn]
      exact (heatGauss_pos x n theta).le
    · rw [heatRemainderTerm, if_neg hn]

theorem heatRemainder_zero_le {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    heatRemainder x 0 ≤
      Real.exp (-(Real.pi / (4 * x))) * heatTailConst := by
  have hterm : ∀ n : ℤ, heatRemainderTerm x 0 n ≤
      Real.exp (-(Real.pi / (4 * x))) * heatTailMajorant n := by
    intro n
    by_cases hn : n = 0
    · simp [heatRemainderTerm, heatTailMajorant, hn]
    · rw [heatRemainderTerm, if_neg hn]
      exact heatGauss_le_majorant_closed hx hx1 le_rfl Real.pi_pos.le n hn
  change (∑' n : ℤ, heatRemainderTerm x 0 n) ≤ _
  calc
    (∑' n : ℤ, heatRemainderTerm x 0 n) ≤
        ∑' n : ℤ,
          Real.exp (-(Real.pi / (4 * x))) * heatTailMajorant n :=
      Summable.tsum_le_tsum hterm (summable_heatRemainderTerm hx 0)
        (summable_heatTailMajorant.mul_left _)
    _ = Real.exp (-(Real.pi / (4 * x))) * heatTailConst := by
      rw [heatTailConst, tsum_mul_left]

/-- Difference summand anchored at phase zero. -/
noncomputable def heatRemainderDifferenceTerm (x theta : ℝ) (n : ℤ) : ℝ :=
  heatRemainderTerm x theta n - heatRemainderTerm x 0 n

theorem heatRemainder_sub_zero_eq_tsum {x : ℝ} (hx : 0 < x) (theta : ℝ) :
    heatRemainder x theta - heatRemainder x 0 =
      ∑' n : ℤ, heatRemainderDifferenceTerm x theta n := by
  change (∑' n : ℤ, heatRemainderTerm x theta n) -
      (∑' n : ℤ, heatRemainderTerm x 0 n) = _
  exact ((summable_heatRemainderTerm hx theta).tsum_sub
    (summable_heatRemainderTerm hx 0)).symm

theorem abs_heatRemainderDifferenceTerm_le {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    {theta : ℝ} (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ Real.pi) (n : ℤ) :
    |heatRemainderDifferenceTerm x theta n| ≤
      theta * ((3 / (2 * x)) * Real.exp (-(Real.pi / (4 * x))) *
        heatTailDerivativeMajorant n) := by
  by_cases hn : n = 0
  · simp [heatRemainderDifferenceTerm, heatRemainderTerm, hn,
      heatTailDerivativeMajorant]
  · simpa only [heatRemainderDifferenceTerm, heatRemainderTerm, if_neg hn] using
      abs_heatGauss_sub_zero_le hx hx1 htheta0 htheta1 n hn

theorem summable_heatRemainderDerivativeBound (x theta : ℝ) :
    Summable (fun n : ℤ =>
      theta * ((3 / (2 * x)) * Real.exp (-(Real.pi / (4 * x))) *
        heatTailDerivativeMajorant n)) := by
  have h := summable_heatTailDerivativeMajorant.mul_left
    (theta * (3 / (2 * x)) * Real.exp (-(Real.pi / (4 * x))))
  exact h.congr (fun n => by ring)

/-- Absolute summation bound, factored out to avoid repeated normalization under `tsum`. -/
theorem abs_tsum_le_tsum_of_abs_le {iota : Type*} {f b : iota → ℝ}
    (hb : Summable b) (hfb : ∀ i, |f i| ≤ b i) :
    |∑' i, f i| ≤ ∑' i, b i := by
  have hfnorm : Summable (fun i => ‖f i‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => by
      simpa only [Real.norm_eq_abs] using hfb i) hb
  rw [← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hfnorm).trans
    (Summable.tsum_mono hfnorm hb (fun i => by
      simpa only [Real.norm_eq_abs] using hfb i))

/-- The full off-centre remainder has the same Lipschitz estimate after summation. -/
theorem abs_heatRemainder_sub_zero_le {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    {theta : ℝ} (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ Real.pi) :
    |heatRemainder x theta - heatRemainder x 0| ≤
      theta * ((3 / (2 * x)) * Real.exp (-(Real.pi / (4 * x))) *
        heatTailDerivativeConst) := by
  rw [heatRemainder_sub_zero_eq_tsum hx theta]
  calc
    |∑' n : ℤ, heatRemainderDifferenceTerm x theta n| ≤
        ∑' n : ℤ, theta * ((3 / (2 * x)) *
          Real.exp (-(Real.pi / (4 * x))) * heatTailDerivativeMajorant n) :=
      abs_tsum_le_tsum_of_abs_le
        (summable_heatRemainderDerivativeBound x theta)
        (abs_heatRemainderDifferenceTerm_le hx hx1 htheta0 htheta1)
    _ = theta * ((3 / (2 * x)) * Real.exp (-(Real.pi / (4 * x))) *
          heatTailDerivativeConst) := by
      rw [show (fun n : ℤ => theta * ((3 / (2 * x)) *
          Real.exp (-(Real.pi / (4 * x))) * heatTailDerivativeMajorant n)) =
          fun n : ℤ =>
            (theta * (3 / (2 * x)) * Real.exp (-(Real.pi / (4 * x)))) *
              heatTailDerivativeMajorant n by
            funext n
            ring,
        tsum_mul_left, heatTailDerivativeConst]
      ring

end

end RHTower
