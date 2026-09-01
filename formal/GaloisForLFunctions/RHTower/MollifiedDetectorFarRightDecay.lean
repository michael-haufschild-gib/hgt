import GaloisForLFunctions.RHTower.LevinsonRightEdge
import GaloisForLFunctions.RHTower.EntireDirichletPolynomial

/-!
# Exponential decay of the mollified detector far to the right

The far-right edge of Levinson's Littlewood rectangle is estimated through the analyticity and
decay of `Log (G·Ψ)` on a half-plane, not through a pointwise bound.  This file supplies the decay:
every ingredient of `G·Ψ − 1` is `O(2^{-Re s})`, uniformly in the mollifier length.

The exponential normalization `e^{-(log 2)·Re s}` is used throughout because that is the shape the
Cauchy/decay lemma `norm_integral_vertical_le_of_halfPlane_decay` consumes.
-/

open Complex Metric Set

noncomputable section

namespace RHTower

theorem exp_neg_log_two_eq (x : ℝ) : Real.exp (-(Real.log 2) * x) = ((2 : ℝ) ^ x)⁻¹ := by
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2) x, ← Real.exp_neg]
  congr 1
  ring

theorem exp_neg_log_two_pos (x : ℝ) : 0 < Real.exp (-(Real.log 2) * x) := Real.exp_pos _

/-- Zeta's far-right tail with an exponential rate. -/
theorem norm_riemannZeta_sub_one_le_exp {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ 3 * Real.exp (-(Real.log 2) * s.re) := by
  have h := norm_riemannZeta_sub_one_le_scaled (m := s.re - 2) (by linarith) (by linarith)
  have hrw : ((2 : ℝ) ^ (s.re - 2))⁻¹ = 4 * Real.exp (-(Real.log 2) * s.re) := by
    rw [exp_neg_log_two_eq, Real.rpow_sub (by norm_num : (0:ℝ) < 2),
      Real.rpow_two]
    field_simp
    norm_num
  rw [hrw] at h
  linarith

/-- Cauchy's estimate turns the tail bound into an exponential bound for `ζ′`. -/
theorem norm_deriv_riemannZeta_le_exp {s : ℂ} (hs : 3 ≤ s.re) :
    ‖deriv riemannZeta s‖ ≤ 6 * Real.exp (-(Real.log 2) * s.re) := by
  set f : ℂ → ℂ := fun w => riemannZeta w - 1 with hf
  have hre : ∀ w : ℂ, ‖w - s‖ ≤ 1 → s.re - 1 ≤ w.re := by
    intro w hw
    have h := Complex.abs_re_le_norm (w - s)
    rw [Complex.sub_re] at h
    have habs : |w.re - s.re| ≤ 1 := le_trans h hw
    rw [abs_le] at habs
    linarith [habs.1]
  have hne : ∀ w : ℂ, ‖w - s‖ ≤ 1 → w ≠ 1 := by
    intro w hw heq
    have hh := hre w hw
    rw [heq, Complex.one_re] at hh
    linarith
  have hdcc : DiffContOnCl ℂ f (ball s 1) := by
    constructor
    · intro w hw
      rw [mem_ball, Complex.dist_eq] at hw
      exact ((differentiableAt_riemannZeta (hne w hw.le)).sub_const 1).differentiableWithinAt
    · rw [closure_ball s (by norm_num : (1 : ℝ) ≠ 0)]
      intro w hw
      rw [mem_closedBall, Complex.dist_eq] at hw
      exact ((differentiableAt_riemannZeta (hne w hw)).sub_const
        1).continuousAt.continuousWithinAt
  have hC : ∀ z ∈ sphere s (1 : ℝ), ‖f z‖ ≤ 6 * Real.exp (-(Real.log 2) * s.re) := by
    intro z hz
    rw [mem_sphere, Complex.dist_eq] at hz
    have hzre : s.re - 1 ≤ z.re := hre z hz.le
    have h2 : (2 : ℝ) ≤ z.re := by linarith
    refine le_trans (norm_riemannZeta_sub_one_le_exp h2) ?_
    have hmono : Real.exp (-(Real.log 2) * z.re) ≤ Real.exp (-(Real.log 2) * (s.re - 1)) := by
      refine Real.exp_le_exp.mpr ?_
      have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      nlinarith [hzre, hlog]
    have hval : Real.exp (-(Real.log 2) * (s.re - 1)) = 2 * Real.exp (-(Real.log 2) * s.re) := by
      rw [show -(Real.log 2) * (s.re - 1) = -(Real.log 2) * s.re + Real.log 2 by ring,
        Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 2)]
      ring
    rw [hval] at hmono
    linarith
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1) hdcc hC
  have hderiv : deriv f s = deriv riemannZeta s := by
    rw [hf]; exact deriv_sub_const 1
  rw [hderiv] at h
  simpa using h

/-- The Levinson detector is `1 + O(2^{-Re s})` far to the right. -/
theorem norm_levinsonG_sub_one_le_exp {lam : ℂ} (hlam : ‖lam‖ ≤ 1) {s : ℂ} (hs : 3 ≤ s.re) :
    ‖levinsonG lam s - 1‖ ≤ 9 * Real.exp (-(Real.log 2) * s.re) := by
  have h1 := norm_riemannZeta_sub_one_le_exp (s := s) (by linarith)
  have h2 := norm_deriv_riemannZeta_le_exp hs
  have hsplit : levinsonG lam s - 1 = (riemannZeta s - 1) + lam * deriv riemannZeta s := by
    rw [levinsonG]; ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have hlm : ‖lam * deriv riemannZeta s‖ ≤ 6 * Real.exp (-(Real.log 2) * s.re) := by
    rw [norm_mul]
    have hnn : (0 : ℝ) ≤ ‖deriv riemannZeta s‖ := norm_nonneg _
    nlinarith [h2, hlam, norm_nonneg lam]
  linarith

/-- A finite reciprocal-power tail over integers `≥ 2` decays exponentially in the exponent. -/
theorem sum_rpow_neg_le_exp {x : ℝ} (hx : 2 ≤ x) (t : Finset ℕ) (ht : ∀ n ∈ t, 2 ≤ n) :
    (∑ n ∈ t, ((n : ℝ) ^ (-x))) ≤ 11 * Real.exp (-(Real.log 2) * x) := by
  have hstep : ∀ n ∈ t, ((n : ℝ) ^ (-x)) ≤ (1 / (n : ℝ) ^ 2) * ((2 : ℝ) ^ (2 - x)) := by
    intro n hn
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast ht n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hsplit : ((n : ℝ) ^ (-x)) = ((n : ℝ) ^ (-(2:ℝ))) * ((n : ℝ) ^ (2 - x)) := by
      rw [← Real.rpow_add hnpos]
      ring_nf
    rw [hsplit]
    have hfirst : ((n : ℝ) ^ (-(2:ℝ))) = 1 / (n : ℝ) ^ 2 := by
      rw [Real.rpow_neg hnpos.le, Real.rpow_two, one_div]
    have hsecond : ((n : ℝ) ^ (2 - x)) ≤ ((2 : ℝ) ^ (2 - x)) := by
      have hxx : (0 : ℝ) ≤ x - 2 := by linarith
      have hb : ((2 : ℝ) ^ (x - 2)) ≤ ((n : ℝ) ^ (x - 2)) :=
        Real.rpow_le_rpow (by norm_num) hn2 hxx
      have h2p : (0 : ℝ) < (2 : ℝ) ^ (x - 2) := Real.rpow_pos_of_pos (by norm_num) _
      have hinv : ((n : ℝ) ^ (x - 2))⁻¹ ≤ ((2 : ℝ) ^ (x - 2))⁻¹ := by
        exact inv_anti₀ h2p hb
      rw [show (2 : ℝ) - x = -(x - 2) by ring, Real.rpow_neg hnpos.le,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      exact hinv
    rw [hfirst]
    have hpos : (0 : ℝ) < 1 / (n : ℝ) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hsecond hpos.le
  have hsum : (∑ n ∈ t, ((n : ℝ) ^ (-x)))
      ≤ ∑ n ∈ t, (1 / (n : ℝ) ^ 2) * ((2 : ℝ) ^ (2 - x)) := Finset.sum_le_sum hstep
  rw [← Finset.sum_mul] at hsum
  have hzeta : (∑ n ∈ t, (1 : ℝ) / (n : ℝ) ^ 2) ≤ Real.pi ^ 2 / 6 :=
    sum_le_hasSum t (fun n _ => by positivity) hasSum_zeta_two
  have hpi : Real.pi ^ 2 / 6 ≤ 8 / 3 := by
    nlinarith [Real.pi_le_four, Real.pi_pos]
  have hpow : (0 : ℝ) < ((2 : ℝ) ^ (2 - x)) := Real.rpow_pos_of_pos (by norm_num) _
  have hval : ((2 : ℝ) ^ (2 - x)) = 4 * Real.exp (-(Real.log 2) * x) := by
    rw [exp_neg_log_two_eq, Real.rpow_sub (by norm_num : (0:ℝ) < 2), Real.rpow_two]
    field_simp
    norm_num
  have hchain : (∑ n ∈ t, ((n : ℝ) ^ (-x))) ≤ (8 / 3) * ((2 : ℝ) ^ (2 - x)) := by
    refine le_trans hsum ?_
    exact mul_le_mul_of_nonneg_right (le_trans hzeta hpi) hpow.le
  rw [hval] at hchain
  linarith

/-- A Dirichlet polynomial with unit head and bounded coefficients is `1 + O(2^{-Re z})`. -/
theorem norm_edPoly_sub_one_le_exp (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n)
    (h1 : 1 ∈ s) (ha1 : a 1 = 1) (hcoeff : ∀ n ∈ s, ‖a n‖ ≤ 1) {z : ℂ} (hz : 2 ≤ z.re) :
    ‖edPoly a s z - 1‖ ≤ 11 * Real.exp (-(Real.log 2) * z.re) := by
  classical
  have hsplit : edPoly a s z - 1 = ∑ n ∈ s.erase 1, a n * ((n : ℝ) : ℂ) ^ (-z) := by
    unfold edPoly
    rw [← Finset.sum_erase_add _ _ h1, ha1]
    norm_num
  rw [hsplit]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ n ∈ s.erase 1, ‖a n * ((n : ℝ) : ℂ) ^ (-z)‖ ≤ ((n : ℝ) ^ (-z.re)) := by
    intro n hn
    have hmem : n ∈ s := Finset.mem_of_mem_erase hn
    have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hs n hmem
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    have hrw : (-z).re = -z.re := by simp
    rw [hrw]
    have hnn : (0 : ℝ) ≤ ((n : ℝ) ^ (-z.re)) := (Real.rpow_pos_of_pos hpos _).le
    nlinarith [hcoeff n hmem, norm_nonneg (a n)]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  refine sum_rpow_neg_le_exp hz _ ?_
  intro n hn
  have hmem : n ∈ s := Finset.mem_of_mem_erase hn
  have hne1 : n ≠ 1 := Finset.ne_of_mem_erase hn
  have := hs n hmem
  omega


/-! ## Elementary consequences used by the far-right edge -/

/-- The distance of a product from `1`. -/
theorem norm_mul_sub_one_le {A B : ℂ} {p q : ℝ} (hA : ‖A - 1‖ ≤ p) (hB : ‖B - 1‖ ≤ q) :
    ‖A * B - 1‖ ≤ p * q + p + q := by
  have hsplit : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by ring
  have hp : (0 : ℝ) ≤ p := le_trans (norm_nonneg _) hA
  have hq : (0 : ℝ) ≤ q := le_trans (norm_nonneg _) hB
  rw [hsplit]
  have h1 := norm_add_le ((A - 1) * (B - 1) + (A - 1)) (B - 1)
  have h2 := norm_add_le ((A - 1) * (B - 1)) (A - 1)
  have h3 : ‖(A - 1) * (B - 1)‖ = ‖A - 1‖ * ‖B - 1‖ := norm_mul _ _
  nlinarith [norm_nonneg (A - 1), norm_nonneg (B - 1)]

/-- Near `1` the principal logarithm is comparable to the displacement. -/
theorem norm_clog_le_of_norm_sub_one_le {w : ℂ} (h : ‖w - 1‖ ≤ 1 / 2) :
    ‖Complex.log w‖ ≤ 2 * ‖w - 1‖ := by
  have hz1 : ‖w - 1‖ < 1 := by linarith
  have hbase := Complex.norm_log_one_add_sub_self_le (z := w - 1) hz1
  have hw : (1 : ℂ) + (w - 1) = w := by ring
  rw [hw] at hbase
  have htri : ‖Complex.log w‖ ≤ ‖Complex.log w - (w - 1)‖ + ‖w - 1‖ := by
    have hadd := norm_add_le (Complex.log w - (w - 1)) (w - 1)
    simpa using hadd
  have hpos : (0 : ℝ) < 1 - ‖w - 1‖ := by linarith
  have hinv : (1 - ‖w - 1‖)⁻¹ ≤ 2 := by
    have hstep : (1 - ‖w - 1‖)⁻¹ ≤ ((1 : ℝ) / 2)⁻¹ :=
      inv_anti₀ (by norm_num) (by linarith)
    simpa using hstep
  have hquad : ‖w - 1‖ ^ 2 * (1 - ‖w - 1‖)⁻¹ / 2 ≤ ‖w - 1‖ ^ 2 := by
    nlinarith [sq_nonneg ‖w - 1‖]
  have hsq2 : ‖w - 1‖ ^ 2 ≤ (1 / 2) * ‖w - 1‖ := by nlinarith [norm_nonneg (w - 1)]
  linarith [norm_nonneg (w - 1)]

/-- A point close to `1` avoids the branch cut. -/
theorem mem_slitPlane_of_norm_sub_one_le {w : ℂ} (h : ‖w - 1‖ ≤ 1 / 2) :
    w ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have h1 : |(w - 1).re| ≤ 1 / 2 := le_trans (Complex.abs_re_le_norm _) h
  rw [Complex.sub_re, Complex.one_re, abs_le] at h1
  linarith [h1.1]

end RHTower

end
