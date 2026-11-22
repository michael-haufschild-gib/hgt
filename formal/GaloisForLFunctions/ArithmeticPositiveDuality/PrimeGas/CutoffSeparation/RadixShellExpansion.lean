import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.Renormalization
import GaloisForLFunctions.RHTower.ZetaCentredSawtoothContinuation

/-!
# Sub-Mellin radix-shell expansion and antipodal zero-spike law

Along radix powers `X = C^K`, the floor divisions in the prime-gas energy-cutoff recursion are
exact. Substituting the centred second-Bernoulli representation of `ζ(w)` at every inner shell
`C^m` (`0 ≤ m < K`) cancels the `X^(1-w)/(1-w)` density counterterm identically and expands
`renormalizedCutoff t j (C^K) w` past the non-summable imaginary-axis Mellin pole comb to order
`O(C^(-K(Re w + 1)))`.

Across the single integer step from `C^K - 1` to `C^K`, the raw shell cutoff jumps by `2 K C^(-Kw)`.
Consequently, at every zero of `ζ(w)` in `Re w > 0`, `renormalizedCutoff` has exact rescaled limits
`+1` along `C^K` and `-1` along `C^K - 1` against `K C^(-Kw)`, so their ratio tends to `-1` and no
point in `Re w > 0`, `w ≠ 1` admits `o(X^(-Re w) log X)` cutoff decay.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation

open AntipodalSpectrum Filter MeasureTheory Set
open scoped Topology

/-- Explicit unfolding of `renormalizedCutoff` exposing the density power term. -/
theorem renormalizedCutoff_eq (t : ExceptionalTime) (j X : ℕ) (w : ℂ) :
    renormalizedCutoff t j X w =
      shellCutoff t j X w - (2 / ((tailRadix t j).val - 1 : ℂ)) * ((X : ℂ) ^ (1 - w) / (1 - w)) :=
  rfl

/-- No positive-integer pair has product at most zero. -/
theorem shellCutoff_zero (t : ExceptionalTime) (j : ℕ) (w : ℂ) :
    shellCutoff t j 0 w = 0 := by
  haveI : IsEmpty (countingStates t j 0) :=
    ⟨fun u => (u.val.val false * u.val.val true).pos.not_ge (by simpa using u.property)⟩
  simp [shellCutoff]

@[simp]
theorem radialCutoff_zero (w : ℂ) : radialCutoff 0 w = 0 := by
  simp [radialCutoff]

/-- Powers of a positive integer under `n ↦ n^(-w)` match powers of the heat factor. -/
theorem nat_pow_cpow_neg (C : ℕ+) (m : ℕ) (w : ℂ) :
    ((C.val ^ m : ℕ) : ℂ) ^ (-w) = (heat w C) ^ m := by
  have hp : ∀ k : ℕ, heat w (C ^ k) = (heat w C) ^ k := by
    intro k
    induction k with
    | zero => simp [heat, energy]
    | succ k ih => rw [pow_succ, heat_mul, ih, pow_succ]
  rw [← hp m, heat_eq_cpow, PNat.pow_coe]

/-- Factorization `N^(1 - w) = N * N^(-w)` for positive integers `N`. -/
theorem nat_cpow_one_sub {N : ℕ} (hN : 0 < N) (w : ℂ) :
    (N : ℂ) ^ (1 - w) = (N : ℂ) * (N : ℂ) ^ (-w) := by
  have h0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [show (1 - w : ℂ) = 1 + (-w) by ring, Complex.cpow_add _ _ h0, Complex.cpow_one]

/-- Exact norm of `q^K = (heat w C)^K` as a real power of `C`. -/
theorem norm_heat_pow (C : ℕ+) (K : ℕ) (w : ℂ) :
    ‖(heat w C) ^ K‖ = (C.val : ℝ) ^ (-(K : ℝ) * w.re) := by
  have hC0 : (0 : ℝ) < C.val := Nat.cast_pos.mpr C.pos
  rw [norm_pow, norm_heat, energy, ← Real.exp_nat_mul, Real.rpow_def_of_pos hC0]
  congr 1; ring

/-- Exact unrolled shell cutoff at radix powers `C^K`, free of floor rounding. -/
theorem shellCutoff_radix_pow (t : ExceptionalTime) (j K : ℕ) (w : ℂ) :
    let C := tailRadix t j
    shellCutoff t j (C.val ^ K) w =
      2 * ∑ m ∈ Finset.range K, (heat w C) ^ (K - m) * radialCutoff (C.val ^ m) w := by
  dsimp only
  set C := tailRadix t j with hCdef
  have hC1 : 1 < C.val := radix_gt_one t j
  induction K with
  | zero =>
    have hdiv : 1 / C.val = 0 := Nat.div_eq_of_lt hC1
    have hrec := shell_cutoff_recursion t j 1 w
    dsimp only at hrec
    rw [pow_zero, hrec, ← hCdef, hdiv, radialCutoff_zero, shellCutoff_zero]
    simp
  | succ K ih =>
    have hdiv : C.val ^ (K + 1) / C.val = C.val ^ K := by
      rw [pow_succ', Nat.mul_div_cancel_left _ C.pos]
    have hrec := shell_cutoff_recursion t j (C.val ^ (K + 1)) w
    dsimp only at hrec
    rw [hrec, ← hCdef, hdiv, ih, Finset.sum_range_succ, Nat.add_sub_cancel_left, pow_one, mul_add,
      ← mul_assoc, Finset.mul_sum, Finset.mul_sum]
    have hsum : (∑ x ∈ Finset.range K,
        heat w C * (2 * ((heat w C) ^ (K - x) * radialCutoff (C.val ^ x) w))) =
        ∑ x ∈ Finset.range K,
          2 * ((heat w C) ^ (K + 1 - x) * radialCutoff (C.val ^ x) w) := by
      refine Finset.sum_congr rfl fun m hm => ?_
      have hsub : K + 1 - m = K - m + 1 := Nat.succ_sub (Finset.mem_range.mp hm).le
      rw [hsub, pow_succ]
      ring
    rw [hsum, ← Finset.mul_sum]
    ring

/-- Single-step jump of `shellCutoff` across a radix shell `C^K`. -/
theorem shellCutoff_radix_pow_sub_pred (t : ExceptionalTime) (j K : ℕ) (w : ℂ) :
    let C := tailRadix t j
    shellCutoff t j (C.val ^ K) w - shellCutoff t j (C.val ^ K - 1) w =
      2 * (K : ℂ) * (heat w C) ^ K := by
  dsimp only
  let C := tailRadix t j
  have hC1 : 1 < C.val := radix_gt_one t j
  induction K with
  | zero =>
    have hdiv : 1 / C.val = 0 := Nat.div_eq_of_lt hC1
    have hrec := shell_cutoff_recursion t j 1 w
    dsimp only at hrec
    rw [pow_zero, Nat.sub_self, hrec, hdiv, radialCutoff_zero, shellCutoff_zero]
    simp
  | succ K ih =>
    have hpow1 : 1 ≤ C.val ^ K := Nat.one_le_pow K C.val C.pos
    have hdiv1 : C.val ^ (K + 1) / C.val = C.val ^ K := by
      rw [pow_succ', Nat.mul_div_cancel_left _ C.pos]
    have hdiv2 : (C.val ^ (K + 1) - 1) / C.val = C.val ^ K - 1 := by
      have hsplit : C.val ^ (K + 1) - 1 = (C.val - 1) + C.val * (C.val ^ K - 1) := by
        have hle1 : 1 ≤ C.val := C.pos
        have hle2 : 1 ≤ C.val ^ (K + 1) := Nat.one_le_pow _ _ C.pos
        zify [hle1, hpow1, hle2]
        rw [pow_succ']
        ring
      rw [hsplit, Nat.add_mul_div_left _ _ C.pos,
        Nat.div_eq_of_lt (Nat.sub_lt C.pos zero_lt_one), zero_add]
    have hrad : radialCutoff (C.val ^ K) w - radialCutoff (C.val ^ K - 1) w = (heat w C) ^ K := by
      unfold radialCutoff
      have htop : C.val ^ K = C.val ^ K - 1 + 1 := (Nat.sub_add_cancel hpow1).symm
      conv_lhs => rw [htop, Finset.sum_Icc_succ_top (by omega : 1 ≤ C.val ^ K - 1 + 1), ← htop]
      rw [add_sub_cancel_left, nat_pow_cpow_neg]
    have hr1 := shell_cutoff_recursion t j (C.val ^ (K + 1)) w
    have hr2 := shell_cutoff_recursion t j (C.val ^ (K + 1) - 1) w
    dsimp only at hr1 hr2
    change shellCutoff t j (C.val ^ (K + 1)) w - shellCutoff t j (C.val ^ (K + 1) - 1) w = _
    rw [hr1, hr2, hdiv1, hdiv2]
    change heat w C * (2 * radialCutoff (C.val ^ K) w + shellCutoff t j (C.val ^ K) w) -
      heat w C * (2 * radialCutoff (C.val ^ K - 1) w + shellCutoff t j (C.val ^ K - 1) w) = _
    have hstep : heat w C * (2 * radialCutoff (C.val ^ K) w + shellCutoff t j (C.val ^ K) w) -
        heat w C * (2 * radialCutoff (C.val ^ K - 1) w + shellCutoff t j (C.val ^ K - 1) w) =
        heat w C * (2 * (radialCutoff (C.val ^ K) w - radialCutoff (C.val ^ K - 1) w) +
          (shellCutoff t j (C.val ^ K) w - shellCutoff t j (C.val ^ K - 1) w)) := by ring
    rw [hstep, hrad, ih, pow_succ, Nat.cast_add, Nat.cast_one]
    ring

/-- Exact finite-order second-Bernoulli decomposition of `renormalizedCutoff` at `X = C^K`. -/
theorem renormalizedCutoff_radix_pow_eq (t : ExceptionalTime) (j K : ℕ)
    {w : ℂ} (hw : -1 < w.re) (hw1 : w ≠ 1) (hq1 : heat w (tailRadix t j) ≠ 1) :
    let C := tailRadix t j
    let q := heat w C
    renormalizedCutoff t j (C.val ^ K) w - 2 * q * riemannZeta w / (1 - q) =
      q ^ K * ((K : ℂ) - 2 * q * riemannZeta w / (1 - q) -
        2 / (((C.val : ℂ) - 1) * (1 - w)) +
        2 * w * (w + 1) * ∑ m ∈ Finset.range K,
          q⁻¹ ^ m * RHTower.zetaBernoulliTail (C.val ^ m) w) := by
  dsimp only
  set C := tailRadix t j
  set q := heat w C
  have hC1 : 1 < C.val := radix_gt_one t j
  have hc1 : (C.val : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hC1.ne')
  have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr hw1.symm
  have h1q : (1 : ℂ) - q ≠ 0 := sub_ne_zero.mpr hq1.symm
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  have hterm : ∀ m ∈ Finset.range K,
      2 * (q ^ (K - m) * radialCutoff (C.val ^ m) w) =
        2 * riemannZeta w * q ^ (K - m) +
        (2 * q ^ K / (1 - w)) * (C.val : ℂ) ^ m +
        q ^ K +
        2 * w * (w + 1) * q ^ K * (q⁻¹ ^ m * RHTower.zetaBernoulliTail (C.val ^ m) w) := by
    intro m hm
    have hmle : m ≤ K := (Finset.mem_range.mp hm).le
    have hCm1 : 1 ≤ C.val ^ m := Nat.one_le_pow m C.val C.pos
    have hzeta := RHTower.zeta_eq_centredTruncated_of_re_gt_neg_one hCm1 hw hw1
    unfold RHTower.zetaCentredTruncated at hzeta
    have hrad : radialCutoff (C.val ^ m) w =
        riemannZeta w + ((C.val ^ m : ℕ) : ℂ) ^ (1 - w) / (1 - w) +
        ((C.val ^ m : ℕ) : ℂ) ^ (-w) / 2 +
        w * (w + 1) * RHTower.zetaBernoulliTail (C.val ^ m) w := by
      unfold radialCutoff
      have hdiv_neg : ((C.val ^ m : ℕ) : ℂ) ^ (1 - w) / (w - 1) =
          -(((C.val ^ m : ℕ) : ℂ) ^ (1 - w) / (1 - w)) := by
        rw [show w - 1 = -(1 - w) by ring, div_neg]
      rw [hdiv_neg] at hzeta
      linear_combination -hzeta
    have hpow1 : ((C.val ^ m : ℕ) : ℂ) ^ (1 - w) = (C.val : ℂ) ^ m * q ^ m := by
      rw [nat_cpow_one_sub (Nat.pos_of_ne_zero (by omega)) w, nat_pow_cpow_neg, Nat.cast_pow]
    have hpow2 : ((C.val ^ m : ℕ) : ℂ) ^ (-w) = q ^ m := nat_pow_cpow_neg C m w
    have hqK : q ^ (K - m) * q ^ m = q ^ K := by rw [← pow_add, Nat.sub_add_cancel hmle]
    have hqinv : q ^ (K - m) = q ^ K * q⁻¹ ^ m := by
      rw [← hqK, mul_assoc, ← mul_pow, mul_inv_cancel₀ hq0, one_pow, mul_one]
    rw [hrad, hpow1, hpow2]
    calc 2 * (q ^ (K - m) * (riemannZeta w + (C.val : ℂ) ^ m * q ^ m / (1 - w) +
          q ^ m / 2 + w * (w + 1) * RHTower.zetaBernoulliTail (C.val ^ m) w))
        = 2 * riemannZeta w * q ^ (K - m) +
          2 * (q ^ (K - m) * q ^ m) * (C.val : ℂ) ^ m / (1 - w) +
          (q ^ (K - m) * q ^ m) +
          2 * w * (w + 1) * q ^ (K - m) * RHTower.zetaBernoulliTail (C.val ^ m) w := by ring
      _ = _ := by
        rw [hqK]
        conv_lhs => arg 2; rw [hqinv]
        ring
  have hgeom_q : (∑ m ∈ Finset.range K, q ^ (K - m)) = q * (1 - q ^ K) / (1 - q) := by
    have hrev : (∑ m ∈ Finset.range K, q ^ (K - m)) = ∑ j ∈ Finset.range K, q ^ (j + 1) := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjlt : j < K := Finset.mem_range.mp hj
      congr 1
      omega
    rw [hrev]
    simp_rw [pow_succ', ← Finset.mul_sum]
    have hg := geom_sum_mul q K
    have h1 : (∑ i ∈ Finset.range K, q ^ i) = (1 - q ^ K) / (1 - q) := by
      rw [eq_div_iff h1q]
      linear_combination -hg
    rw [h1, mul_div_assoc]
  have hgeom_C : (∑ m ∈ Finset.range K, (C.val : ℂ) ^ m) = ((C.val : ℂ) ^ K - 1) / ((C.val : ℂ) - 1) := by
    rw [eq_div_iff hc1]
    exact geom_sum_mul (C.val : ℂ) K
  have hCK_pow : ((C.val ^ K : ℕ) : ℂ) ^ (1 - w) = (C.val : ℂ) ^ K * q ^ K := by
    rw [nat_cpow_one_sub (pow_pos C.pos K) w, nat_pow_cpow_neg, Nat.cast_pow]
  have hsh := shellCutoff_radix_pow t j K w
  dsimp only at hsh
  rw [renormalizedCutoff_eq, hsh]
  change 2 * (∑ m ∈ Finset.range K, q ^ (K - m) * radialCutoff (C.val ^ m) w) -
    2 / ((C.val : ℂ) - 1) * (((C.val ^ K : ℕ) : ℂ) ^ (1 - w) / (1 - w)) -
    2 * q * riemannZeta w / (1 - q) = _
  rw [Finset.mul_sum, Finset.sum_congr rfl hterm]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, hgeom_q, hgeom_C, hCK_pow]
  field_simp [hc1, h1w, h1q]
  ring

/-- Pointwise bound on the second-Bernoulli tail `∫_N^∞ B₂({u}) u^(-w-2) du`. -/
theorem norm_zetaBernoulliTail_le {N : ℕ} (hN : 1 ≤ N) {w : ℂ} (hw : -1 < w.re) :
    ‖RHTower.zetaBernoulliTail N w‖ ≤ (N : ℝ) ^ (-w.re - 1) / (8 * (w.re + 1)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hre : -w.re - 2 < -1 := by linarith
  have hint : IntegrableOn (fun u : ℝ => (1 / 8 : ℝ) * u ^ (-w.re - 2)) (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt hre hN0).const_mul _
  unfold RHTower.zetaBernoulliTail
  refine (norm_integral_le_integral_norm _).trans ?_
  have hae : ∀ᵐ u ∂volume.restrict (Ioi (N : ℝ)),
      ‖((RHTower.bernoulliPeriodic u : ℝ) : ℂ) * (u : ℂ) ^ (-w - 1 - 1)‖ ≤
        (1 / 8 : ℝ) * u ^ (-w.re - 2) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := hN0.trans hu
    have hexp : (-w - 1 - 1).re = -w.re - 2 := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]; ring
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hu0, hexp]
    exact mul_le_mul_of_nonneg_right (RHTower.abs_bernoulliPeriodic_le u)
      (Real.rpow_nonneg hu0.le _)
  refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint hae).trans_eq ?_
  rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt hre hN0]
  have h1 : -w.re - 2 + 1 = -w.re - 1 := by ring
  rw [h1]
  have hwpos : 0 < w.re + 1 := by linarith
  have hden : -w.re - 1 = -(w.re + 1) := by ring
  conv_lhs => arg 2; arg 2; rw [hden]
  field_simp [hwpos.ne']

/-- Geometric decay `C^(-m)` of the weighted Bernoulli shell terms across `Re w > -1`. -/
theorem norm_inv_heat_mul_bernoulliTail_le (C : ℕ+) {w : ℂ} (hw : -1 < w.re) (m : ℕ) :
    ‖(heat w C)⁻¹ ^ m * RHTower.zetaBernoulliTail (C.val ^ m) w‖ ≤
      (1 / (8 * (w.re + 1))) * ((C.val : ℝ)⁻¹) ^ m := by
  have hC0 : (0 : ℝ) < C.val := Nat.cast_pos.mpr C.pos
  have hCm1 : 1 ≤ C.val ^ m := Nat.one_le_pow m C.val C.pos
  have hqnorm : ‖(heat w C)⁻¹ ^ m‖ = (C.val : ℝ) ^ ((m : ℝ) * w.re) := by
    rw [norm_pow, norm_inv, norm_heat, energy, ← Real.exp_neg, neg_mul, neg_neg,
      ← Real.exp_nat_mul, Real.rpow_def_of_pos hC0]
    congr 1; ring
  have hNpow : ((C.val ^ m : ℕ) : ℝ) ^ (-w.re - 1) =
      (C.val : ℝ) ^ (-(m : ℝ) * w.re) * ((C.val : ℝ)⁻¹) ^ m := by
    rw [Nat.cast_pow, ← Real.rpow_natCast (C.val : ℝ) m,
      ← Real.rpow_mul hC0.le, show (m : ℝ) * (-w.re - 1) = -(m : ℝ) * w.re + -(m : ℝ) by ring,
      Real.rpow_add hC0, Real.rpow_neg hC0.le, Real.rpow_natCast, inv_pow]
  rw [norm_mul, hqnorm]
  refine (mul_le_mul_of_nonneg_left (norm_zetaBernoulliTail_le hCm1 hw)
    (Real.rpow_nonneg hC0.le _)).trans_eq ?_
  rw [hNpow]
  have hcancel : (C.val : ℝ) ^ ((m : ℝ) * w.re) * (C.val : ℝ) ^ (-(m : ℝ) * w.re) = 1 := by
    rw [← Real.rpow_add hC0, show (m : ℝ) * w.re + -(m : ℝ) * w.re = 0 by ring, Real.rpow_zero]
  calc (C.val : ℝ) ^ ((m : ℝ) * w.re) *
        (((C.val : ℝ) ^ (-(m : ℝ) * w.re) * ((C.val : ℝ)⁻¹) ^ m) / (8 * (w.re + 1)))
      = ((C.val : ℝ) ^ ((m : ℝ) * w.re) * (C.val : ℝ) ^ (-(m : ℝ) * w.re)) *
          ((1 / (8 * (w.re + 1))) * ((C.val : ℝ)⁻¹) ^ m) := by ring
    _ = _ := by rw [hcancel, one_mul]

theorem summable_inv_heat_mul_bernoulliTail (C : ℕ+) (hC : 1 < C.val) {w : ℂ} (hw : -1 < w.re) :
    Summable fun m : ℕ => (heat w C)⁻¹ ^ m * RHTower.zetaBernoulliTail (C.val ^ m) w := by
  have hC1 : (1 : ℝ) < C.val := by exact_mod_cast hC
  have hinv : (C.val : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hC1
  have hgeom : Summable fun m : ℕ => (1 / (8 * (w.re + 1))) * ((C.val : ℝ)⁻¹) ^ m :=
    (summable_geometric_of_lt_one (by positivity) hinv).mul_left _
  exact Summable.of_norm_bounded hgeom (norm_inv_heat_mul_bernoulliTail_le C hw)

/-- Second-order radix-shell coefficient `A_{t,j}(w)` multiplying `C^(-Kw)` after the `K C^(-Kw)` spike. -/
def radixShellConstant (t : ExceptionalTime) (j : ℕ) (w : ℂ) : ℂ :=
  let C := tailRadix t j;
  let q := heat w C;
  -(2 * q * riemannZeta w / (1 - q)) - 2 / (((C.val : ℂ) - 1) * (1 - w)) +
    2 * w * (w + 1) * (∑' m : ℕ, q⁻¹ ^ m * RHTower.zetaBernoulliTail (C.val ^ m) w)

/-- Explicit `O(C^(-K(Re w + 1)))` sub-Mellin asymptotic bound for `renormalizedCutoff` at `X = C^K`. -/
theorem norm_renormalizedCutoff_radix_pow_sub_le (t : ExceptionalTime) (j K : ℕ)
    {w : ℂ} (hw : -1 < w.re) (hw1 : w ≠ 1) (hq1 : heat w (tailRadix t j) ≠ 1) :
    let C := tailRadix t j
    let q := heat w C
    ‖renormalizedCutoff t j (C.val ^ K) w - 2 * q * riemannZeta w / (1 - q) -
        ((K : ℂ) + radixShellConstant t j w) * q ^ K‖ ≤
      (C.val : ℝ) * ‖w * (w + 1)‖ / (4 * (w.re + 1) * ((C.val : ℝ) - 1)) *
        (C.val : ℝ) ^ (-(K : ℝ) * (w.re + 1)) := by
  dsimp only
  set C := tailRadix t j
  set q := heat w C
  have hC1 : 1 < C.val := radix_gt_one t j
  have hCr1 : (1 : ℝ) < C.val := by exact_mod_cast hC1
  have hC0 : (0 : ℝ) < C.val := by positivity
  have hwpos : 0 < w.re + 1 := by linarith
  have hs := summable_inv_heat_mul_bernoulliTail C hC1 hw
  have hsplit := hs.sum_add_tsum_nat_add K
  have hdiff : renormalizedCutoff t j (C.val ^ K) w - 2 * q * riemannZeta w / (1 - q) -
      ((K : ℂ) + radixShellConstant t j w) * q ^ K =
      -(2 * (w * (w + 1)) * q ^ K *
        ∑' m : ℕ, q⁻¹ ^ (m + K) * RHTower.zetaBernoulliTail (C.val ^ (m + K)) w) := by
    have heq := renormalizedCutoff_radix_pow_eq t j K hw hw1 hq1
    dsimp only at heq
    change renormalizedCutoff t j (C.val ^ K) w - 2 * q * riemannZeta w / (1 - q) -
      ((K : ℂ) + radixShellConstant t j w) * q ^ K = _
    rw [heq]
    unfold radixShellConstant
    dsimp only
    change q ^ K * ((K : ℂ) - 2 * q * riemannZeta w / (1 - q) -
        2 / (((C.val : ℂ) - 1) * (1 - w)) +
        2 * w * (w + 1) * ∑ m ∈ Finset.range K, q⁻¹ ^ m * RHTower.zetaBernoulliTail (C.val ^ m) w) -
      ((K : ℂ) + (-(2 * q * riemannZeta w / (1 - q)) - 2 / (((C.val : ℂ) - 1) * (1 - w)) +
        2 * w * (w + 1) * ∑' m : ℕ, q⁻¹ ^ m * RHTower.zetaBernoulliTail (C.val ^ m) w)) * q ^ K = _
    rw [← hsplit]
    ring
  have hinv : (C.val : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hCr1
  have hgeom : Summable fun m : ℕ => (1 / (8 * (w.re + 1))) * ((C.val : ℝ)⁻¹) ^ (m + K) := by
    have h := (summable_geometric_of_lt_one (by positivity) hinv).mul_left
      ((1 / (8 * (w.re + 1))) * ((C.val : ℝ)⁻¹) ^ K)
    exact h.congr fun m => by rw [pow_add]; ring
  have htail : ‖∑' m : ℕ, q⁻¹ ^ (m + K) * RHTower.zetaBernoulliTail (C.val ^ (m + K)) w‖ ≤
      (1 / (8 * (w.re + 1))) * ((C.val : ℝ)⁻¹) ^ K / (1 - (C.val : ℝ)⁻¹) := by
    refine (norm_tsum_le_tsum_norm (hs.norm.comp_injective (add_left_injective K))).trans ?_
    refine (Summable.tsum_le_tsum (fun m => norm_inv_heat_mul_bernoulliTail_le C hw (m + K))
      (hs.norm.comp_injective (add_left_injective K)) hgeom).trans_eq ?_
    have hfactor : (fun m : ℕ => (1 / (8 * (w.re + 1))) * ((C.val : ℝ)⁻¹) ^ (m + K)) =
        fun m : ℕ => ((1 / (8 * (w.re + 1))) * ((C.val : ℝ)⁻¹) ^ K) * ((C.val : ℝ)⁻¹) ^ m := by
      funext m; rw [pow_add]; ring
    rw [hfactor, tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hinv, ← div_eq_mul_inv]
  have hqK_norm : ‖q ^ K‖ = (C.val : ℝ) ^ (-(K : ℝ) * w.re) := norm_heat_pow C K w
  have hpow_comb : (C.val : ℝ) ^ (-(K : ℝ) * w.re) * ((C.val : ℝ)⁻¹) ^ K =
      (C.val : ℝ) ^ (-(K : ℝ) * (w.re + 1)) := by
    rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hC0.le, ← Real.rpow_add hC0]
    congr 1; ring
  have hden_simp : 1 - (C.val : ℝ)⁻¹ = ((C.val : ℝ) - 1) / (C.val : ℝ) := by
    field_simp [hC0.ne']
  rw [hdiff, norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, hqK_norm]
  refine (mul_le_mul_of_nonneg_left htail (by positivity)).trans_eq ?_
  rw [hden_simp]
  calc 2 * ‖w * (w + 1)‖ * (C.val : ℝ) ^ (-(K : ℝ) * w.re) *
        (1 / (8 * (w.re + 1)) * ((C.val : ℝ)⁻¹) ^ K / (((C.val : ℝ) - 1) / (C.val : ℝ)))
      = (2 * ‖w * (w + 1)‖ * (1 / (8 * (w.re + 1))) / (((C.val : ℝ) - 1) / (C.val : ℝ))) *
          ((C.val : ℝ) ^ (-(K : ℝ) * w.re) * ((C.val : ℝ)⁻¹) ^ K) := by ring
    _ = _ := by
      rw [hpow_comb]
      field_simp [hwpos.ne', (sub_pos.mpr hCr1).ne', hC0.ne']
      ring

/-- Normalized step of `renormalizedCutoff` from `C^K - 1` to `C^K` tends to `2` for all `w ≠ 1`. -/
theorem tendsto_renormalizedCutoff_step_div (t : ExceptionalTime) (j : ℕ)
    {w : ℂ} (hw1 : w ≠ 1) :
    let C := tailRadix t j
    let q := heat w C
    Tendsto (fun K : ℕ =>
      (renormalizedCutoff t j (C.val ^ K) w - renormalizedCutoff t j (C.val ^ K - 1) w) /
        ((K : ℂ) * q ^ K)) atTop (𝓝 2) := by
  dsimp only
  set C := tailRadix t j
  set q := heat w C
  have hC1 : 1 < C.val := radix_gt_one t j
  have hCr1 : (1 : ℝ) < C.val := by exact_mod_cast hC1
  have hC0 : (0 : ℝ) < C.val := by positivity
  have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr hw1.symm
  set D : ℂ := 2 / ((C.val : ℂ) - 1)
  have hstep_bound : ∀ᶠ K : ℕ in atTop,
      ‖D * (((C.val ^ K : ℕ) : ℂ) ^ (1 - w) / (1 - w) -
          (((C.val ^ K - 1 : ℕ) : ℂ) ^ (1 - w) / (1 - w)))‖ ≤
        4 * ‖D‖ * (2 : ℝ) ^ |w.re| * ‖q ^ K‖ := by
    have hpow_top : Tendsto (fun K : ℕ => (C.val : ℝ) ^ K) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hCr1
    filter_upwards [eventually_ge_atTop 1,
      hpow_top.eventually_ge_atTop (max 2 (‖1 - w‖ + 2))] with K hK1 hKM
    have hCK_ge2 : 2 ≤ C.val ^ K := by
      have : (2 : ℝ) ≤ (C.val : ℝ) ^ K := (le_max_left _ _).trans hKM
      exact_mod_cast this
    set N : ℕ := C.val ^ K - 1
    have hN1 : 1 ≤ N := by omega
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hlog : Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ) ≤ (N : ℝ)⁻¹ := by
      have hpos1 : (0 : ℝ) < (N + 1 : ℕ) := by positivity
      rw [← Real.log_div hpos1.ne' hNpos.ne', Nat.cast_add, Nat.cast_one]
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
      rw [add_div, div_self hNpos.ne', add_sub_cancel_left, one_div]
    have hlog0 : 0 ≤ Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ) :=
      sub_nonneg.mpr (Real.log_le_log hNpos (by exact_mod_cast Nat.le_succ N))
    set z : ℂ := ((Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ) : ℝ) : ℂ) * (1 - w)
    have hNw : ‖1 - w‖ ≤ (N : ℝ) := by
      have h2 : ‖1 - w‖ + 2 ≤ (C.val : ℝ) ^ K := (le_max_right _ _).trans hKM
      have hcast : (N : ℝ) = (C.val : ℝ) ^ K - 1 := by
        have : (N + 1 : ℕ) = C.val ^ K := Nat.sub_add_cancel (by omega)
        have hc : ((N + 1 : ℕ) : ℝ) = (C.val : ℝ) ^ K := by exact_mod_cast this
        push_cast at hc; linarith
      linarith
    have hznorm : ‖z‖ ≤ ‖1 - w‖ * (N : ℝ)⁻¹ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0, mul_comm]
      exact mul_le_mul_of_nonneg_left hlog (norm_nonneg _)
    have hz1 : ‖z‖ ≤ 1 := hznorm.trans ((mul_inv_le_iff₀ hNpos).mpr (by linarith))
    have hfac : (((N + 1 : ℕ) : ℝ) : ℂ) ^ (1 - w) = ((N : ℝ) : ℂ) ^ (1 - w) * Complex.exp z := by
      rw [RHTower.cpow_ofReal_eq_exp (by positivity), RHTower.cpow_ofReal_eq_exp hNpos,
        ← Complex.exp_add]
      congr 1; push_cast [z]; ring
    have hexp : ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ := Complex.norm_exp_sub_one_le hz1
    have hN1_eq : N + 1 = C.val ^ K := Nat.sub_add_cancel (by omega)
    have hdiff_pow : ‖((C.val ^ K : ℕ) : ℂ) ^ (1 - w) - ((N : ℕ) : ℂ) ^ (1 - w)‖ ≤
        2 * ‖1 - w‖ * (N : ℝ) ^ (-w.re) := by
      rw [← hN1_eq]
      change ‖(((N + 1 : ℕ) : ℝ) : ℂ) ^ (1 - w) - ((N : ℝ) : ℂ) ^ (1 - w)‖ ≤ _
      rw [hfac, show ((N : ℝ) : ℂ) ^ (1 - w) * Complex.exp z - ((N : ℝ) : ℂ) ^ (1 - w) =
        ((N : ℝ) : ℂ) ^ (1 - w) * (Complex.exp z - 1) by ring,
        norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
      have hre : (1 - w).re = 1 - w.re := by simp
      rw [hre]
      calc (N : ℝ) ^ (1 - w.re) * ‖Complex.exp z - 1‖
          ≤ (N : ℝ) ^ (1 - w.re) * (2 * (‖1 - w‖ * (N : ℝ)⁻¹)) :=
            mul_le_mul_of_nonneg_left (hexp.trans (by linarith)) (Real.rpow_nonneg hNpos.le _)
        _ = 2 * ‖1 - w‖ * (N : ℝ) ^ (-w.re) := by
            rw [show (1 - w.re : ℝ) = -w.re + 1 by ring, Real.rpow_add hNpos, Real.rpow_one]
            field_simp [hNpos.ne']
    have hN_half : (C.val : ℝ) ^ K / 2 ≤ (N : ℝ) := by
      have : ((N + 1 : ℕ) : ℝ) = (C.val : ℝ) ^ K := by exact_mod_cast hN1_eq
      push_cast at this
      have : (2 : ℝ) ≤ (C.val : ℝ) ^ K := by exact_mod_cast hCK_ge2
      linarith
    have hqK_norm : ‖q ^ K‖ = ((C.val : ℝ) ^ K) ^ (-w.re) := by
      rw [norm_heat_pow, ← Real.rpow_natCast, ← Real.rpow_mul hC0.le]
      ring_nf
    have hNrpow : (N : ℝ) ^ (-w.re) ≤ (2 : ℝ) ^ |w.re| * ‖q ^ K‖ := by
      rw [hqK_norm]
      rcases le_or_gt 0 (-w.re) with hnonneg | hneg
      · have hle : (N : ℝ) ≤ (C.val : ℝ) ^ K := by
          have : ((N + 1 : ℕ) : ℝ) = (C.val : ℝ) ^ K := by exact_mod_cast hN1_eq
          push_cast at this; linarith
        calc (N : ℝ) ^ (-w.re) ≤ ((C.val : ℝ) ^ K) ^ (-w.re) :=
              Real.rpow_le_rpow hNpos.le hle hnonneg
          _ = 1 * ((C.val : ℝ) ^ K) ^ (-w.re) := (one_mul _).symm
          _ ≤ (2 : ℝ) ^ |w.re| * ((C.val : ℝ) ^ K) ^ (-w.re) :=
              mul_le_mul_of_nonneg_right
                (Real.one_le_rpow (by norm_num) (abs_nonneg _)) (by positivity)
      · have hwpos' : 0 ≤ w.re := by linarith
        have habs : |w.re| = w.re := abs_of_nonneg hwpos'
        calc (N : ℝ) ^ (-w.re) ≤ ((C.val : ℝ) ^ K / 2) ^ (-w.re) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hN_half hneg.le
          _ = (2 : ℝ) ^ |w.re| * ((C.val : ℝ) ^ K) ^ (-w.re) := by
              rw [Real.div_rpow (by positivity) (by norm_num), div_eq_mul_inv,
                ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), neg_neg, habs, mul_comm]
    have hnw_pos : 0 < ‖1 - w‖ := norm_pos_iff.mpr h1w
    rw [← sub_div, norm_mul D, norm_div (((C.val ^ K : ℕ) : ℂ) ^ (1 - w) - ((N : ℕ) : ℂ) ^ (1 - w))]
    have hdiv_le : ‖((C.val ^ K : ℕ) : ℂ) ^ (1 - w) - ((N : ℕ) : ℂ) ^ (1 - w)‖ / ‖1 - w‖ ≤
        2 * (N : ℝ) ^ (-w.re) := by
      rw [div_le_iff₀ hnw_pos]
      linarith [hdiff_pow]
    calc ‖D‖ * (‖((C.val ^ K : ℕ) : ℂ) ^ (1 - w) - ((N : ℕ) : ℂ) ^ (1 - w)‖ / ‖1 - w‖)
        ≤ ‖D‖ * (2 * (N : ℝ) ^ (-w.re)) :=
          mul_le_mul_of_nonneg_left hdiv_le (norm_nonneg D)
      _ = 2 * ‖D‖ * (N : ℝ) ^ (-w.re) := by ring
      _ ≤ 2 * ‖D‖ * ((2 : ℝ) ^ |w.re| * ‖q ^ K‖) :=
          mul_le_mul_of_nonneg_left hNrpow (by positivity)
      _ ≤ 4 * ‖D‖ * (2 : ℝ) ^ |w.re| * ‖q ^ K‖ := by
          have : 0 ≤ ‖D‖ * ((2 : ℝ) ^ |w.re| * ‖q ^ K‖) := by positivity
          linarith
  have herr : Tendsto (fun K : ℕ =>
      (D * (((C.val ^ K : ℕ) : ℂ) ^ (1 - w) / (1 - w) -
        (((C.val ^ K - 1 : ℕ) : ℂ) ^ (1 - w) / (1 - w)))) / ((K : ℂ) * q ^ K))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hinvK : Tendsto (fun K : ℕ => (4 * ‖D‖ * (2 : ℝ) ^ |w.re|) / (K : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hinvK
    filter_upwards [eventually_gt_atTop 0, hstep_bound] with K hK0 hb
    have hqK0 : 0 < ‖q ^ K‖ := norm_pos_iff.mpr (pow_ne_zero K (Complex.exp_ne_zero _))
    have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr hK0
    rw [norm_div _ ((K : ℂ) * q ^ K), norm_mul (K : ℂ) (q ^ K), Complex.norm_natCast]
    calc ‖D * (((C.val ^ K : ℕ) : ℂ) ^ (1 - w) / (1 - w) -
            (((C.val ^ K - 1 : ℕ) : ℂ) ^ (1 - w) / (1 - w)))‖ / ((K : ℝ) * ‖q ^ K‖)
        ≤ (4 * ‖D‖ * (2 : ℝ) ^ |w.re| * ‖q ^ K‖) / ((K : ℝ) * ‖q ^ K‖) :=
          div_le_div_of_nonneg_right hb (by positivity)
      _ = (4 * ‖D‖ * (2 : ℝ) ^ |w.re|) / (K : ℝ) := by
          field_simp [hqK0.ne', hKpos.ne']
  have hmain := (tendsto_const_nhds (x := (2 : ℂ))).sub herr
  rw [sub_zero] at hmain
  change Tendsto (fun K : ℕ =>
    (renormalizedCutoff t j (C.val ^ K) w - renormalizedCutoff t j (C.val ^ K - 1) w) /
      ((K : ℂ) * q ^ K)) atTop (𝓝 2)
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with K hK0
  have hK_ne : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hK0.ne'
  have hqK_ne : q ^ K ≠ 0 := pow_ne_zero K (Complex.exp_ne_zero _)
  rw [renormalizedCutoff_eq, renormalizedCutoff_eq]
  have hjump := shellCutoff_radix_pow_sub_pred t j K w
  dsimp only at hjump
  change 2 - D * _ / ((K : ℂ) * q ^ K) =
    ((shellCutoff t j (C.val ^ K) w - D * _) - (shellCutoff t j (C.val ^ K - 1) w - D * _)) /
      ((K : ℂ) * q ^ K)
  have hrew : (shellCutoff t j (C.val ^ K) w - D * (((C.val ^ K : ℕ) : ℂ) ^ (1 - w) / (1 - w))) -
      (shellCutoff t j (C.val ^ K - 1) w - D * (((C.val ^ K - 1 : ℕ) : ℂ) ^ (1 - w) / (1 - w))) =
      (shellCutoff t j (C.val ^ K) w - shellCutoff t j (C.val ^ K - 1) w) -
      D * (((C.val ^ K : ℕ) : ℂ) ^ (1 - w) / (1 - w) -
        (((C.val ^ K - 1 : ℕ) : ℂ) ^ (1 - w) / (1 - w))) := by ring
  rw [hrew, hjump, sub_div]
  congr 1
  change (2 : ℂ) = 2 * (K : ℂ) * q ^ K / ((K : ℂ) * q ^ K)
  field_simp [hK_ne, hqK_ne]

/-- Universal lower bound on consecutive radix-shell cutoffs: at every `w ≠ 1`, no smooth
power subtraction can eliminate the `K C^(-K Re w)` oscillation. -/
theorem eventually_max_norm_renormalizedCutoff_radix_ge (t : ExceptionalTime) (j : ℕ)
    {w : ℂ} (hw1 : w ≠ 1) :
    let C := tailRadix t j
    ∀ᶠ K : ℕ in atTop,
      ((K : ℝ) / 2) * (C.val : ℝ) ^ (-(K : ℝ) * w.re) ≤
        max ‖renormalizedCutoff t j (C.val ^ K) w‖ ‖renormalizedCutoff t j (C.val ^ K - 1) w‖ := by
  dsimp only
  let C := tailRadix t j
  let q := heat w C
  have hC0 : (0 : ℝ) < C.val := Nat.cast_pos.mpr C.pos
  have hstep := (tendsto_renormalizedCutoff_step_div t j hw1).norm
  rw [show ‖(2 : ℂ)‖ = 2 by norm_num] at hstep
  filter_upwards [eventually_gt_atTop 0,
    hstep.eventually (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2))] with K hK0 hgt
  change 1 < ‖(renormalizedCutoff t j (C.val ^ K) w - renormalizedCutoff t j (C.val ^ K - 1) w) /
    ((K : ℂ) * q ^ K)‖ at hgt
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr hK0
  have hqK_norm : ‖q ^ K‖ = (C.val : ℝ) ^ (-(K : ℝ) * w.re) := norm_heat_pow C K w
  have hden_pos : 0 < (K : ℝ) * (C.val : ℝ) ^ (-(K : ℝ) * w.re) := by positivity
  rw [norm_div, norm_mul, Complex.norm_natCast, hqK_norm, one_lt_div hden_pos] at hgt
  have htri : ‖renormalizedCutoff t j (C.val ^ K) w - renormalizedCutoff t j (C.val ^ K - 1) w‖ ≤
      2 * max ‖renormalizedCutoff t j (C.val ^ K) w‖
        ‖renormalizedCutoff t j (C.val ^ K - 1) w‖ := by
    calc ‖renormalizedCutoff t j (C.val ^ K) w - renormalizedCutoff t j (C.val ^ K - 1) w‖
        ≤ ‖renormalizedCutoff t j (C.val ^ K) w‖ +
            ‖renormalizedCutoff t j (C.val ^ K - 1) w‖ := norm_sub_le _ _
      _ ≤ max _ _ + max _ _ := add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = 2 * max _ _ := (two_mul _).symm
  linarith

/-- Exact zero-spike characterization: in `Re w > 0`, `w ≠ 1`, `ζ(w) = 0` iff the radix-shell
cutoffs `renormalizedCutoff t j (C^K) w` are asymptotic to `+K C^(-Kw)`. -/
theorem zeta_zero_iff_radix_pow_spike (t : ExceptionalTime) (j : ℕ)
    {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) :
    let C := tailRadix t j
    let q := heat w C
    riemannZeta w = 0 ↔
      Tendsto (fun K : ℕ => renormalizedCutoff t j (C.val ^ K) w / ((K : ℂ) * q ^ K))
        atTop (𝓝 1) := by
  dsimp only
  set C := tailRadix t j
  set q := heat w C
  have hC1 : 1 < C.val := radix_gt_one t j
  have hCr1 : (1 : ℝ) < C.val := by exact_mod_cast hC1
  have hq_lt : ‖q‖ < 1 := heat_contraction C hC1 w hw
  have hq1 : q ≠ 1 := fun he => hq_lt.ne (by rw [he, norm_one])
  constructor
  · intro hz
    have hrem : Tendsto (fun K : ℕ =>
        (renormalizedCutoff t j (C.val ^ K) w -
          ((K : ℂ) + radixShellConstant t j w) * q ^ K) / ((K : ℂ) * q ^ K))
        atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      let B := (C.val : ℝ) * ‖w * (w + 1)‖ / (4 * (w.re + 1) * ((C.val : ℝ) - 1))
      have hCinv : (C.val : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hCr1
      have hpow0 : Tendsto (fun K : ℕ => B * ((C.val : ℝ)⁻¹) ^ K) atTop (𝓝 0) := by
        simpa only [mul_zero] using
          (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hCinv).const_mul B
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hpow0
      filter_upwards [eventually_ge_atTop 1] with K hK1
      have hC0 : (0 : ℝ) < C.val := by positivity
      have hb := norm_renormalizedCutoff_radix_pow_sub_le t j K (by linarith) hw1 hq1
      dsimp only at hb
      rw [hz, mul_zero, zero_div, sub_zero] at hb
      have hqK_norm : ‖q ^ K‖ = (C.val : ℝ) ^ (-(K : ℝ) * w.re) := norm_heat_pow C K w
      have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
      rw [norm_div, norm_mul (K : ℂ) (q ^ K), Complex.norm_natCast, hqK_norm]
      have hsplit_pow : (C.val : ℝ) ^ (-(K : ℝ) * (w.re + 1)) =
          (C.val : ℝ) ^ (-(K : ℝ) * w.re) * ((C.val : ℝ)⁻¹) ^ K := by
        rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hC0.le, ← Real.rpow_add hC0]
        congr 1; ring
      calc ‖renormalizedCutoff t j (C.val ^ K) w -
              ((K : ℂ) + radixShellConstant t j w) * q ^ K‖ /
              ((K : ℝ) * (C.val : ℝ) ^ (-(K : ℝ) * w.re))
          ≤ (B * (C.val : ℝ) ^ (-(K : ℝ) * (w.re + 1))) /
              (1 * (C.val : ℝ) ^ (-(K : ℝ) * w.re)) := by
            gcongr
        _ = B * ((C.val : ℝ)⁻¹) ^ K := by
            rw [hsplit_pow, one_mul]
            have hp : (0 : ℝ) < (C.val : ℝ) ^ (-(K : ℝ) * w.re) := by positivity
            field_simp [hp.ne']
    have hconst : Tendsto (fun K : ℕ => (1 : ℂ) + radixShellConstant t j w / (K : ℂ))
        atTop (𝓝 1) := by
      have h0 : Tendsto (fun K : ℕ => radixShellConstant t j w / (K : ℂ)) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simp_rw [norm_div, Complex.norm_natCast]
        exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      simpa only [add_zero] using tendsto_const_nhds.add h0
    have hsum := hrem.add hconst
    rw [zero_add] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with K hK0
    have hK_ne : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hK0.ne'
    have hqK_ne : q ^ K ≠ 0 := pow_ne_zero K (Complex.exp_ne_zero _)
    field_simp [hK_ne, hqK_ne]
    ring
  · intro hspike
    have hKq0 : Tendsto (fun K : ℕ => (K : ℂ) * q ^ K) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      let s : ℝ := w.re * Real.log C.val
      have hs_pos : 0 < s := mul_pos hw (Real.log_pos hCr1)
      have hexp := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop hs_pos)).const_mul s⁻¹
      rw [mul_zero] at hexp
      refine hexp.congr fun K => ?_
      dsimp only [Function.comp_apply]
      rw [pow_one, norm_mul, Complex.norm_natCast, norm_pow, norm_heat, energy]
      have hmul : s⁻¹ * (s * (K : ℝ) * Real.exp (-(s * (K : ℝ)))) =
          (K : ℝ) * Real.exp (-w.re * Real.log C.val) ^ K := by
        rw [← Real.exp_nat_mul]
        have : -(s * (K : ℝ)) = (K : ℝ) * (-w.re * Real.log C.val) := by dsimp [s]; ring
        rw [this]
        field_simp [hs_pos.ne']
      exact hmul
    have hsub0 : Tendsto (fun K : ℕ => renormalizedCutoff t j (C.val ^ K) w) atTop (𝓝 0) := by
      have hm := hspike.mul hKq0
      rw [one_mul] at hm
      refine hm.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with K hK0
      have hK_ne : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hK0.ne'
      have hqK_ne : q ^ K ≠ 0 := pow_ne_zero K (Complex.exp_ne_zero _)
      exact div_mul_cancel₀ _ (mul_ne_zero hK_ne hqK_ne)
    have hfull := (renormalized_cutoff_limit t j ⟨w, hw, hw1⟩).comp
      (tendsto_pow_atTop_atTop_of_one_lt hC1)
    have heq := tendsto_nhds_unique hfull hsub0
    have h1q : (1 : ℂ) - q ≠ 0 := sub_ne_zero.mpr hq1.symm
    have hq0 : q ≠ 0 := Complex.exp_ne_zero _
    exact (mul_eq_zero.mp ((div_eq_zero_iff.mp heq).resolve_right h1q)).resolve_left
      (mul_ne_zero two_ne_zero hq0)

/-- At every zero of `ζ(w)` in `Re w > 0`, the pre-shell cutoff `C^K - 1` has opposite spike `-1`
and the consecutive ratio across the radix boundary tends to `-1`. -/
theorem tendsto_antipodal_spike_at_zeta_zero (t : ExceptionalTime) (j : ℕ)
    {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) (hz : riemannZeta w = 0) :
    let C := tailRadix t j
    let q := heat w C
    Tendsto (fun K : ℕ => renormalizedCutoff t j (C.val ^ K - 1) w / ((K : ℂ) * q ^ K))
        atTop (𝓝 (-1)) ∧
      Tendsto (fun K : ℕ =>
        renormalizedCutoff t j (C.val ^ K) w / renormalizedCutoff t j (C.val ^ K - 1) w)
        atTop (𝓝 (-1)) := by
  dsimp only
  let C := tailRadix t j
  let q := heat w C
  have htop := (zeta_zero_iff_radix_pow_spike t j hw hw1).mp hz
  have hstep := tendsto_renormalizedCutoff_step_div t j hw1
  dsimp only at htop hstep
  have hpred : Tendsto (fun K : ℕ =>
      renormalizedCutoff t j (C.val ^ K - 1) w / ((K : ℂ) * q ^ K)) atTop (𝓝 (-1)) := by
    have h := htop.sub hstep
    rw [show (1 : ℂ) - 2 = -1 by ring] at h
    refine h.congr fun K => ?_
    rw [← sub_div]
    congr 1; ring
  refine ⟨hpred, ?_⟩
  have hrat := htop.div hpred (by norm_num : (-1 : ℂ) ≠ 0)
  rw [show (1 : ℂ) / (-1) = -1 by ring] at hrat
  refine hrat.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with K hK0
  have hden_ne : (K : ℂ) * q ^ K ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr hK0.ne') (pow_ne_zero K (Complex.exp_ne_zero _))
  exact div_div_div_cancel_right₀ hden_ne _ _

#print axioms shellCutoff_radix_pow
#print axioms shellCutoff_radix_pow_sub_pred
#print axioms renormalizedCutoff_radix_pow_eq
#print axioms norm_renormalizedCutoff_radix_pow_sub_le
#print axioms tendsto_renormalizedCutoff_step_div
#print axioms eventually_max_norm_renormalizedCutoff_radix_ge
#print axioms zeta_zero_iff_radix_pow_spike
#print axioms tendsto_antipodal_spike_at_zeta_zero

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation
