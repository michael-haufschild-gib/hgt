import GaloisForLFunctions.CompletedArithmeticForms.FirstAtomRankBoundary
import GaloisForLFunctions.HTGeometry.ApproximateMultipointSchwarz
import GaloisForLFunctions.HTGeometry.BesselOrderIntegral

/-!
# Effective physical scale of the first-atom rank obstruction

Cauchy's estimate bounds how long nonnegative signed moments can coexist with the
literal decrease of the rotated source between a half period and a full period.
The least negative order and the least failing mixed head have explicit upper
bounds proportional to the physical first-atom scale on the nonnegative source ray.
-/

noncomputable section

open Finset Filter Topology Matrix Metric

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower

private def sourceTaylorTerm (f : ℂ → ℂ) (z : ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ • z ^ n • iteratedDeriv n f 0

private theorem sourceTaylorTerm_hasSum {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    HasSum (sourceTaylorTerm f z) (f z) := by
  convert Complex.hasSum_taylorSeries_of_entire hf 0 z using 1 <;>
    first | rfl | (funext n; simp only [sourceTaylorTerm, sub_zero])

private theorem entire_taylor_tail_norm_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {ρ r M : ℝ} (hM0 : 0 ≤ M) (hρ : 0 ≤ ρ) (hr : ρ < r)
    (hM : ∀ w ∈ sphere (0 : ℂ) r, ‖f w‖ ≤ M) {z : ℂ} (hz : ‖z‖ ≤ ρ) (J : ℕ) :
    ‖∑' n, sourceTaylorTerm f z (n + J)‖ ≤ M * (ρ / r) ^ J / (1 - ρ / r) := by
  have hrpos : 0 < r := lt_of_le_of_lt hρ hr
  have hq0 : (0 : ℝ) ≤ ρ / r := div_nonneg hρ hrpos.le
  have hq1 : ρ / r < 1 := (div_lt_one hrpos).mpr hr
  have hcauchy (n : ℕ) : ‖iteratedDeriv n f 0‖ ≤ (n.factorial : ℝ) * M / r ^ n :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hrpos hf.diffContOnCl hM
  have hgeo (n : ℕ) : ‖sourceTaylorTerm f z n‖ ≤ M * (ρ / r) ^ n := by
    have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
    have he : ‖sourceTaylorTerm f z n‖ =
        ‖iteratedDeriv n f 0‖ * ‖z‖ ^ n / (n.factorial : ℝ) := by
      simp only [sourceTaylorTerm, norm_smul, norm_inv, norm_pow, Complex.norm_natCast]
      field_simp
    rw [he, div_le_iff₀ hfac]
    have hb := mul_le_mul (hcauchy n) (pow_le_pow_left₀ (norm_nonneg _) hz n)
      (pow_nonneg (norm_nonneg _) n) (by positivity : 0 ≤ (n.factorial : ℝ) * M / r ^ n)
    refine hb.trans (le_of_eq ?_)
    rw [div_pow]
    field_simp
  have hm : Summable fun n : ℕ => (M * (ρ / r) ^ J) * (ρ / r) ^ n :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have ht (n : ℕ) : ‖sourceTaylorTerm f z (n + J)‖ ≤
      (M * (ρ / r) ^ J) * (ρ / r) ^ n := by
    refine (hgeo (n + J)).trans (le_of_eq ?_)
    rw [pow_add]
    ring
  have hs : Summable fun n : ℕ => ‖sourceTaylorTerm f z (n + J)‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) ht hm
  refine (norm_tsum_le_tsum_norm hs).trans ((Summable.tsum_le_tsum ht hs hm).trans (le_of_eq ?_))
  rw [(summable_geometric_of_lt_one hq0 hq1).tsum_mul_left,
    tsum_geometric_of_lt_one hq0 hq1]
  ring

/-- A nonnegative Taylor head can decrease only by its two explicitly bounded analytic tails. -/
theorem entire_decrease_le_of_nonneg_initial_jets {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {u v r M : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvr : v < r) (hM0 : 0 ≤ M)
    (hM : ∀ w ∈ sphere (0 : ℂ) r, ‖f w‖ ≤ M) (J : ℕ)
    (hjet : ∀ n < J, 0 ≤ (iteratedDeriv n f 0).re) :
    (f u).re - (f v).re ≤ 2 * (M * (v / r) ^ J / (1 - v / r)) := by
  have hv : 0 ≤ v := hu.trans huv
  have hhead : (∑ n ∈ range J, sourceTaylorTerm f (u : ℂ) n).re ≤
      (∑ n ∈ range J, sourceTaylorTerm f (v : ℂ) n).re := by
    have hs (y : ℝ) : (∑ n ∈ range J, sourceTaylorTerm f (y : ℂ) n).re =
        ∑ n ∈ range J, (sourceTaylorTerm f (y : ℂ) n).re :=
      map_sum Complex.reAddGroupHom _ _
    rw [hs, hs]
    apply sum_le_sum
    intro n hn
    have he (y : ℝ) : (sourceTaylorTerm f (y : ℂ) n).re =
        (n.factorial : ℝ)⁻¹ * y ^ n * (iteratedDeriv n f 0).re := by
      simp only [sourceTaylorTerm, smul_eq_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
        ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      ring
    rw [he, he]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu huv n) (by positivity))
      (hjet n (mem_range.mp hn))
  have hsplit (y : ℝ) : (∑ n ∈ range J, sourceTaylorTerm f (y : ℂ) n) +
      ∑' n, sourceTaylorTerm f (y : ℂ) (n + J) = f y := by
    have hs := sourceTaylorTerm_hasSum hf (y : ℂ)
    rw [hs.summable.sum_add_tsum_nat_add J, hs.tsum_eq]
  have htu := entire_taylor_tail_norm_le hf hM0 hv hvr hM
    (show ‖(u : ℂ)‖ ≤ v by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu] using huv) J
  have htv := entire_taylor_tail_norm_le hf hM0 hv hvr hM
    (show ‖(v : ℂ)‖ ≤ v by simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv, le_refl]) J
  have hru := (Complex.re_le_norm (∑' n, sourceTaylorTerm f (u : ℂ) (n + J))).trans htu
  have hrv := (Complex.re_le_norm (-(∑' n, sourceTaylorTerm f (v : ℂ) (n + J))))
  rw [Complex.neg_re, norm_neg] at hrv
  have hvlow := hrv.trans htv
  have heu := congrArg Complex.re (hsplit u)
  have hev := congrArg Complex.re (hsplit v)
  simp only [Complex.add_re] at heu hev
  linarith only [hhead, hru, hvlow, heu, hev]

/-- Explicit boundary maximum on the fixed circle enclosing one source period. -/
def firstAtomPeriodCircleBound (x : ℝ) : ℝ :=
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let H := Real.exp (4 * Real.pi)
  4 * q ^ 2 * Real.exp (x - 2 * q) * Real.exp (2 * q * (H + 1)) *
    ((2 * q - 3) ^ 2 + 12 * q * (H + 1))

theorem firstAtomPeriodCircleBound_nonneg (x : ℝ) : 0 ≤ firstAtomPeriodCircleBound x := by
  have hq : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  unfold firstAtomPeriodCircleBound
  positivity

/-- The literal entire source obeys its explicit period-circle envelope. -/
theorem firstAtomRotatedPair_circle_bound (x : ℝ) {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) (2 * Real.pi)) :
    ‖firstAtomRotatedPair x z‖ ≤ firstAtomPeriodCircleBound x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let B := (2 * q - 3) ^ 2
  let C := 4 * q ^ 2 * Real.exp (x - 2 * q)
  let H := Real.exp (4 * Real.pi)
  have hq : 0 < q := by dsimp [q, thetaCuspSingleAtomReflectionScale]; positivity
  have hB : 0 ≤ B := sq_nonneg _
  have hC : 0 < C := by dsimp [C]; positivity
  have hzn : ‖z‖ = 2 * Real.pi := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
  have hw : ‖2 * (Complex.I * z)‖ = 4 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, hzn]
    norm_num
    ring
  have hc : ‖Complex.cosh (2 * (Complex.I * z)) - 1‖ ≤ H + 1 := by
    calc
      _ ≤ ‖Complex.cosh (2 * (Complex.I * z))‖ + 1 := by
        simpa using (norm_sub_le (Complex.cosh (2 * (Complex.I * z))) (1 : ℂ))
      _ ≤ Real.exp ‖2 * (Complex.I * z)‖ + 1 := by
        linarith only [norm_complex_cosh_le_exp_norm (2 * (Complex.I * z))]
      _ = _ := by rw [hw]
  have hmul : ‖-2 * (q : ℂ) * (Complex.cosh (2 * (Complex.I * z)) - 1)‖ ≤
      2 * q * (H + 1) := by
    rw [norm_mul]
    have hnorm : ‖(-2 : ℂ) * (q : ℂ)‖ = 2 * q := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
      norm_num
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  have he := (Complex.norm_exp_le_exp_norm
    (-2 * (q : ℂ) * (Complex.cosh (2 * (Complex.I * z)) - 1))).trans
      (Real.exp_le_exp.mpr hmul)
  have ha : ‖(B : ℂ) - 12 * (q : ℂ) * (Complex.cosh (2 * (Complex.I * z)) - 1)‖ ≤
      B + 12 * q * (H + 1) := by
    calc
      _ ≤ ‖(B : ℂ)‖ + ‖12 * (q : ℂ) * (Complex.cosh (2 * (Complex.I * z)) - 1)‖ :=
        norm_sub_le _ _
      _ = B + 12 * q * ‖Complex.cosh (2 * (Complex.I * z)) - 1‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB, norm_mul, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
        norm_num
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 12 * q by positivity)
        linarith only [hm]
  change ‖(C : ℂ) * Complex.exp (-2 * (q : ℂ) * (Complex.cosh (2 * (Complex.I * z)) - 1)) *
      ((B : ℂ) - 12 * (q : ℂ) * (Complex.cosh (2 * (Complex.I * z)) - 1))‖ ≤
    C * Real.exp (2 * q * (H + 1)) * (B + 12 * q * (H + 1))
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
  exact mul_le_mul (mul_le_mul_of_nonneg_left he hC.le) ha (norm_nonneg _) (by positivity)

private theorem firstAtomRotatedPair_initial_jets_nonneg (x : ℝ) :
    ∀ n < 2 * firstAtomNegativeOrder x, 0 ≤ (iteratedDeriv n (firstAtomRotatedPair x) 0).re := by
  intro n hn
  rw [firstAtomRotatedPair_jet]
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    have hI : Complex.I ^ (2 * k) = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by
      rw [pow_mul, Complex.I_sq]
      norm_cast
    rw [show n = 2 * k by omega, hI, ← Complex.ofReal_mul, Complex.ofReal_re]
    exact firstAtom_signed_moment_nonneg_before_negativeOrder x (by omega)
  · rw [thetaCuspFirstAtomReflectionJet_odd_zero ho, Complex.ofReal_zero, mul_zero,
      Complex.zero_re]

/-- The actual period decrease has a positive lower bound in literal source mass. -/
theorem firstAtomRotatedPair_period_decrease (x : ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    24 * q * (4 * q ^ 2 * Real.exp (x - 2 * q)) ≤
      (firstAtomRotatedPair x ((Real.pi / 2 : ℝ) : ℂ)).re - (firstAtomRotatedPair x Real.pi).re := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let B := (2 * q - 3) ^ 2
  let C := 4 * q ^ 2 * Real.exp (x - 2 * q)
  have hq : 0 < q := by dsimp [q, thetaCuspSingleAtomReflectionScale]; positivity
  have hB : 0 ≤ B := sq_nonneg _
  have hC : 0 < C := by dsimp [C]; positivity
  have he : B + 24 * q ≤ Real.exp (4 * q) * (B + 24 * q) :=
    le_mul_of_one_le_left (by positivity) (Real.one_le_exp (by positivity))
  have hc := mul_le_mul_of_nonneg_left he hC.le
  rw [firstAtomRotatedPair_ofReal, firstAtomRotatedPair_ofReal]
  simp only [show 2 * (Real.pi / 2) = Real.pi by ring, Real.cos_pi, Real.cos_two_pi,
    Complex.ofReal_re]
  change 24 * q * C ≤ C * Real.exp (-2 * q * (-1 - 1)) * (B - 12 * q * (-1 - 1)) -
    C * Real.exp (-2 * q * (1 - 1)) * (B - 12 * q * (1 - 1))
  rw [show -2 * q * (-1 - 1) = 4 * q by ring]
  norm_num only [sub_self, mul_zero, Real.exp_zero, mul_one, sub_zero]
  nlinarith only [hc]

/-- An explicit all-center bound on the first negative moment order in physical source scale. -/
theorem firstAtomNegativeOrder_pow_bound (x : ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let H := Real.exp (4 * Real.pi)
    (2 : ℝ) ^ (2 * firstAtomNegativeOrder x) ≤
      Real.exp (2 * q * (H + 1)) * ((2 * q - 3) ^ 2 + 12 * q * (H + 1)) / (6 * q) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let C := 4 * q ^ 2 * Real.exp (x - 2 * q)
  let H := Real.exp (4 * Real.pi)
  let E := Real.exp (2 * q * (H + 1)) * ((2 * q - 3) ^ 2 + 12 * q * (H + 1))
  let J := 2 * firstAtomNegativeOrder x
  have hq : 0 < q := by dsimp [q, thetaCuspSingleAtomReflectionScale]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have ht := entire_decrease_le_of_nonneg_initial_jets (firstAtomRotatedPair_entire x)
    (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
    (show Real.pi / 2 ≤ Real.pi by linarith only [Real.pi_pos])
    (show Real.pi < 2 * Real.pi by linarith only [Real.pi_pos])
    (firstAtomPeriodCircleBound_nonneg x) (fun z hz => firstAtomRotatedPair_circle_bound x hz)
    J (firstAtomRotatedPair_initial_jets_nonneg x)
  have hl := firstAtomRotatedPair_period_decrease x
  have hratio : Real.pi / (2 * Real.pi) = (1 / 2 : ℝ) := by field_simp
  rw [hratio] at ht
  have h : 24 * q * C ≤ 4 * (C * E) * (1 / 2 : ℝ) ^ J := by
    change 24 * q * C ≤ _ at hl
    have hM : firstAtomPeriodCircleBound x = C * E := by
      dsimp [firstAtomPeriodCircleBound, C, E, q, H]
      ring
    rw [hM] at ht
    have ht' : (firstAtomRotatedPair x ((Real.pi / 2 : ℝ) : ℂ)).re -
        (firstAtomRotatedPair x Real.pi).re ≤ 4 * (C * E) * (1 / 2 : ℝ) ^ J := by
      convert ht using 1
      ring
    exact hl.trans ht'
  have hp : (1 / 2 : ℝ) ^ J * (2 : ℝ) ^ J = 1 := by
    rw [← mul_pow]
    norm_num
  have hm := mul_le_mul_of_nonneg_right h (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) J)
  have hm' : C * (24 * q * (2 : ℝ) ^ J) ≤ C * (4 * E) := by
    calc
      _ = (24 * q * C) * (2 : ℝ) ^ J := by ring
      _ ≤ (4 * (C * E) * (1 / 2 : ℝ) ^ J) * (2 : ℝ) ^ J := hm
      _ = C * (4 * E) := by rw [mul_assoc, hp]; ring
  have hm'' : (24 * q * (2 : ℝ) ^ J) * C ≤ (4 * E) * C := by
    nlinarith only [hm']
  have hc := (mul_le_mul_iff_left₀ hC).mp hm''
  change (2 : ℝ) ^ J ≤ E / (6 * q)
  apply (le_div_iff₀ (by positivity : 0 < 6 * q)).mpr
  linarith only [hc]

/-- A fixed explicit constant controlling the negative order in the physical source scale. -/
def firstAtomRankScaleConstant : ℝ :=
  (9 * Real.exp (4 * Real.pi) + 2) / (2 * Real.log 2)

/-- The least negative moment order grows at most linearly in the physical first-atom scale. -/
theorem firstAtomNegativeOrder_le_physicalScale {x : ℝ} (hx : 0 ≤ x) :
    (firstAtomNegativeOrder x : ℝ) ≤
      firstAtomRankScaleConstant * thetaCuspSingleAtomReflectionScale 1 x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let H := Real.exp (4 * Real.pi)
  have hq3 : 3 < q := three_lt_thetaCuspSingleAtomReflectionScale (by omega) hx
  have hq : 1 ≤ q := by linarith only [hq3]
  have hq0 : 0 < q := by linarith only [hq3]
  have hH : 1 ≤ H := Real.one_le_exp (by positivity)
  have hqSq : q ≤ q ^ 2 := by nlinarith only [hq, sq_nonneg (q - 1)]
  have hsq : 1 ≤ q ^ 2 := hq.trans hqSq
  have hB : (2 * q - 3) ^ 2 ≤ 13 * q ^ 2 := by nlinarith only [hsq, hq0.le]
  have hp : ((2 * q - 3) ^ 2 + 12 * q * (H + 1)) / (6 * q) ≤ 7 * H * q := by
    apply (div_le_iff₀ (by positivity : 0 < 6 * q)).mpr
    have ht := mul_le_mul_of_nonneg_left hqSq (show 0 ≤ 12 * (H + 1) by positivity)
    have hh : 25 + 12 * H ≤ 42 * H := by linarith only [hH]
    have hhq := mul_le_mul_of_nonneg_right hh (sq_nonneg q)
    nlinarith only [hB, ht, hhq]
  have hpow : (2 : ℝ) ^ (2 * firstAtomNegativeOrder x) ≤ Real.exp ((9 * H + 2) * q) := by
    calc
      _ ≤ Real.exp (2 * q * (H + 1)) *
          ((2 * q - 3) ^ 2 + 12 * q * (H + 1)) / (6 * q) := firstAtomNegativeOrder_pow_bound x
      _ = Real.exp (2 * q * (H + 1)) *
          (((2 * q - 3) ^ 2 + 12 * q * (H + 1)) / (6 * q)) := by ring
      _ ≤ Real.exp (2 * q * (H + 1)) * (7 * H * q) :=
        mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)
      _ ≤ Real.exp (2 * q * (H + 1)) * Real.exp (7 * H * q) :=
        mul_le_mul_of_nonneg_left (by linarith only [Real.add_one_le_exp (7 * H * q)])
          (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpow
  rw [Real.log_pow, Real.log_exp] at hlog
  push_cast at hlog
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  change (firstAtomNegativeOrder x : ℝ) ≤ ((9 * H + 2) / (2 * Real.log 2)) * q
  calc
    _ ≤ ((9 * H + 2) * q) / (2 * Real.log 2) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith only [hlog])
    _ = _ := by ring

/-- The first failing full mixed head has the same effective physical-scale ceiling. -/
theorem firstAtomFailureRank_le_physicalScale {x : ℝ} (hx : 0 ≤ x) :
    (firstAtomFailureRank x : ℝ) ≤
      1 + firstAtomRankScaleConstant * thetaCuspSingleAtomReflectionScale 1 x := by
  have hκ : (firstAtomFailureRank x : ℝ) ≤ (firstAtomNegativeOrder x : ℝ) + 1 := by
    exact_mod_cast firstAtomFailureRank_le_negativeOrder_succ x
  have hν := firstAtomNegativeOrder_le_physicalScale hx
  linarith only [hκ, hν]

/-- A failing literal mixed head occurs within the explicit source-scale rank window. -/
theorem exists_firstAtom_signed_head_failure_le_scale {x : ℝ} (hx : 0 ≤ x) :
    ∃ N : ℕ, (N : ℝ) ≤ 1 + firstAtomRankScaleConstant * thetaCuspSingleAtomReflectionScale 1 x ∧
      ¬ (finiteHankelMatrix (firstAtomSignedSequence x) N).PosSemidef :=
  ⟨firstAtomFailureRank x, firstAtomFailureRank_le_physicalScale hx, firstAtomFailureRank_spec x⟩

#print axioms entire_decrease_le_of_nonneg_initial_jets
#print axioms firstAtomRotatedPair_circle_bound
#print axioms firstAtomNegativeOrder_pow_bound
#print axioms firstAtomNegativeOrder_le_physicalScale
#print axioms firstAtomFailureRank_le_physicalScale
#print axioms exists_firstAtom_signed_head_failure_le_scale

end GaloisForLFunctions.CompletedArithmeticForms
