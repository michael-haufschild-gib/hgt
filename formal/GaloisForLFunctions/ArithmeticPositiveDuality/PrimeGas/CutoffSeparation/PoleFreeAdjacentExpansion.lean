import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation.RadixShellExpansion
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.HolomorphicContrast

/-!
# Pole-cancelled sub-Mellin expansion of `adjacentCutoff` across `Re w > -1`

At even radix powers `X = C^(2K)`, `adjacentCutoff t j (C^(2K)) w` compares level `j` (radix `C`,
depth `2K`) against `C + 1` copies of level `j + 1` (radix `C^2`, depth `K`). Expanding both inner
shells through the centred second-Bernoulli identity cancels **both** singularities at `w = 1`
identically:
1. the external `X^(1 - w) / (1 - w)` density counterterm is absent from `adjacentCutoff`;
2. the internal `N^(1 - w) / (1 - w)` shell terms cancel via `∑_{m<2K} C^m = (C + 1) ∑_{r<K} C^(2r)`.

Defining the denominator-free entire finite-shell transfer `finiteContrastTransfer C K w` (which
equals `(1 - q^(2K)) * contrastTransfer C w` whenever `q^2 ≠ 1`), we prove for **every** `w` with
`Re w > -1` — including the pole `w = 1`, the critical line `Re w = 0`, and the reflected Euler
strip `-1 < Re w ≤ 0` — an exact decomposition whose remainder is completely free of `|ζ(w)|` and
completely free of `1 / ‖1 - w‖`, together with a pure-exponential `O(C^(-2K Re w))` bound after
removing the deterministic spike `-(C - 1) K C^(-2Kw)`.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation

open AntipodalSpectrum Complex Filter Set
open scoped Topology

/-- Entire finite-shell transfer `-2 C q · dslope(z ↦ C^(-z), 1, w) · ∑_{r < K} q^(2r)`, free of
the `1 - q^2` denominator so it remains regular across `Re w = 0` as well as `w = 1`. -/
def finiteContrastTransfer (C : ℕ+) (K : ℕ) (w : ℂ) : ℂ :=
  -2 * (C.val : ℂ) * heat w C * dslope (fun z => heat z C) 1 w *
    ∑ r ∈ Finset.range K, (heat w C) ^ (2 * r)

/-- Finite second-Bernoulli shell contrast appearing in `adjacentCutoff t j (C^(2K)) w`. -/
def adjacentBernoulliFinite (C : ℕ+) (K : ℕ) (w : ℂ) : ℂ :=
  let q := heat w C
  (∑ m ∈ Finset.range (2 * K), q⁻¹ ^ m * _root_.RHTower.zetaBernoulliTail (C.val ^ m) w) -
    ((C.val : ℂ) + 1) *
      ∑ r ∈ Finset.range K, q⁻¹ ^ (2 * r) * _root_.RHTower.zetaBernoulliTail (C.val ^ (2 * r)) w

/-- Convergent infinite second-Bernoulli contrast on `Re w > -1`. -/
def adjacentBernoulliSeries (C : ℕ+) (w : ℂ) : ℂ :=
  let q := heat w C
  (∑' m : ℕ, q⁻¹ ^ m * _root_.RHTower.zetaBernoulliTail (C.val ^ m) w) -
    ((C.val : ℂ) + 1) *
      ∑' r : ℕ, q⁻¹ ^ (2 * r) * _root_.RHTower.zetaBernoulliTail (C.val ^ (2 * r)) w

/-- Deterministic spike-subtracted adjacent shell reading at `X = C^(2K)`, adding back the
elementary endpoint jump `(C - 1) K C^(-2Kw)` to eliminate the linear factor `K` from the error. -/
def spikeSubtractedAdjacentCutoff (t : ExceptionalTime) (j K : ℕ) (w : ℂ) : ℂ :=
  let C := tailRadix t j
  adjacentCutoff t j (C.val ^ (2 * K)) w +
    (((C.val : ℂ) - 1) * (K : ℂ)) * (heat w C) ^ (2 * K)

/-- `finiteContrastTransfer C K` is entire on `ℂ`. -/
theorem differentiable_finiteContrastTransfer (C : ℕ+) (K : ℕ) :
    Differentiable ℂ (finiteContrastTransfer C K) := by
  intro w
  have hheat : ∀ z : ℂ, AnalyticAt ℂ (fun u => heat u C) z := fun z =>
    (analyticAt_id.neg.mul analyticAt_const).cexp
  have hdslope : DifferentiableAt ℂ (dslope (fun z => heat z C) 1) w :=
    (_root_.RHTower.analyticAt_dslope_of_analyticAt (hheat 1) (hheat w)).differentiableAt
  have hq : DifferentiableAt ℂ (fun z => heat z C) w := (hheat w).differentiableAt
  unfold finiteContrastTransfer
  exact (((differentiableAt_const _).mul hq).mul hdslope).mul
    (DifferentiableAt.fun_sum fun r _ => hq.pow (2 * r))

/-- Off the imaginary-axis return locus `q^2 = 1`, `finiteContrastTransfer` equals
`(1 - q^(2K)) * contrastTransfer`. -/
theorem finiteContrastTransfer_eq_damped (C : ℕ+) (K : ℕ) {w : ℂ}
    (hq2 : (1 : ℂ) - (heat w C) ^ 2 ≠ 0) :
    finiteContrastTransfer C K w = (1 - (heat w C) ^ (2 * K)) * contrastTransfer C w := by
  set q := heat w C
  have hsum : (∑ r ∈ Finset.range K, q ^ (2 * r)) = (1 - q ^ (2 * K)) / (1 - q ^ 2) := by
    have hpow : (∑ r ∈ Finset.range K, q ^ (2 * r)) = ∑ r ∈ Finset.range K, (q ^ 2) ^ r :=
      Finset.sum_congr rfl fun r _ => pow_mul q 2 r
    rw [hpow, eq_div_iff hq2, pow_mul q 2 K]
    linear_combination -(geom_sum_mul (q ^ 2) K)
  unfold finiteContrastTransfer contrastTransfer
  change -2 * (C.val : ℂ) * q * dslope (fun z => heat z C) 1 w *
      (∑ r ∈ Finset.range K, q ^ (2 * r)) =
    (1 - q ^ (2 * K)) * (-2 * (C.val : ℂ) * q * dslope (fun z => heat z C) 1 w / (1 - q ^ 2))
  rw [hsum]
  field_simp [hq2]

/-- Throughout `Re w > 0` (including `w = 1`), `zetaPoleUnit w * finiteContrastTransfer C K w`
equals the damped holomorphic response `(1 - q^(2K)) * contrastResponse C w`. -/
theorem zetaPoleUnit_mul_finiteContrastTransfer_eq {C : ℕ+} (hC : 1 < C.val) (K : ℕ)
    {w : ℂ} (hw : 0 < w.re) :
    _root_.RHTower.zetaPoleUnit w * finiteContrastTransfer C K w =
      (1 - (heat w C) ^ (2 * K)) * contrastResponse C w := by
  have hq : ‖(heat w C) ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (heat_contraction C hC w hw) (by norm_num)
  have hq2 : (1 : ℂ) - (heat w C) ^ 2 ≠ 0 :=
    sub_ne_zero.mpr fun he => hq.ne (by rw [← he, norm_one])
  rw [finiteContrastTransfer_eq_damped C K hq2, contrastResponse]
  ring

private theorem sum_range_two_mul {α : Type*} [AddCommMonoid α] (f : ℕ → α) (K : ℕ) :
    (∑ m ∈ Finset.range (2 * K), f m) = ∑ r ∈ Finset.range K, (f (2 * r) + f (2 * r + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

private theorem sum_pow_even_contrast (q c : ℂ) (K : ℕ) :
    (∑ m ∈ Finset.range (2 * K), q ^ (2 * K - m)) -
      (c + 1) * (∑ r ∈ Finset.range K, q ^ (2 * K - 2 * r)) =
      q * (1 - c * q) * ∑ r ∈ Finset.range K, q ^ (2 * r) := by
  have h1 : (∑ m ∈ Finset.range (2 * K), q ^ (2 * K - m)) =
      ∑ u ∈ Finset.range (2 * K), q ^ (u + 1) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun u hu => ?_
    have := Finset.mem_range.mp hu
    congr 1; omega
  have h2 : (∑ r ∈ Finset.range K, q ^ (2 * K - 2 * r)) =
      ∑ v ∈ Finset.range K, q ^ (2 * v + 2) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun v hv => ?_
    have := Finset.mem_range.mp hv
    congr 1; omega
  rw [h1, h2, sum_range_two_mul (fun u => q ^ (u + 1)) K,
    Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hp1 : q ^ (2 * r + 1) = q ^ (2 * r) * q := pow_succ q (2 * r)
  have hp2 : q ^ (2 * r + 2) = q ^ (2 * r) * q * q := by rw [pow_succ, hp1]
  rw [hp1, hp2]
  ring

private theorem sum_pow_pole_cancel (c : ℂ) (K : ℕ) :
    (∑ m ∈ Finset.range (2 * K), c ^ m) - (c + 1) * (∑ r ∈ Finset.range K, c ^ (2 * r)) = 0 := by
  rw [sum_range_two_mul (fun m => c ^ m) K, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [pow_succ]
  ring

private theorem adjacentCutoff_radix_even_pow_eq_of_ne_one
    (t : ExceptionalTime) (j K : ℕ) {w : ℂ} (hw : -1 < w.re) (hw1 : w ≠ 1) :
    let C := tailRadix t j
    let q := heat w C
    adjacentCutoff t j (C.val ^ (2 * K)) w -
        _root_.RHTower.zetaPoleUnit w * finiteContrastTransfer C K w =
      q ^ (2 * K) * (-(((C.val : ℂ) - 1) * (K : ℂ)) +
        2 * w * (w + 1) * adjacentBernoulliFinite C K w) := by
  dsimp only
  set C := tailRadix t j
  set c : ℂ := (C.val : ℂ)
  set q := heat w C
  have hc_ne : c ≠ 0 := Nat.cast_ne_zero.mpr C.ne_zero
  have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr hw1.symm
  have hw1_sub : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  -- Unroll both shells at `C^(2K) = (C^2)^K` without dividing by `1 - q` or `1 - q^2`.
  have hrad_succ : tailRadix t (j + 1) = C ^ 2 := tailRadix_succ t j
  have hpow_eq : (tailRadix t (j + 1)).val ^ K = C.val ^ (2 * K) := by
    rw [hrad_succ, PNat.pow_coe, ← pow_mul]
  have hheat_succ : heat w (tailRadix t (j + 1)) = q ^ 2 := by
    rw [hrad_succ, sq, heat_mul, sq]
  have hsh0 := shellCutoff_radix_pow t j (2 * K) w
  have hsh1 := shellCutoff_radix_pow t (j + 1) K w
  dsimp only at hsh0 hsh1
  rw [hpow_eq, hheat_succ] at hsh1
  -- Expand each radial harmonic cutoff via the centred second-Bernoulli formula.
  have hterm1 : ∀ m ∈ Finset.range (2 * K),
      2 * (q ^ (2 * K - m) * radialCutoff (C.val ^ m) w) =
        2 * riemannZeta w * q ^ (2 * K - m) +
        (2 * q ^ (2 * K) / (1 - w)) * c ^ m +
        q ^ (2 * K) +
        2 * w * (w + 1) * q ^ (2 * K) *
          (q⁻¹ ^ m * _root_.RHTower.zetaBernoulliTail (C.val ^ m) w) := by
    intro m hm
    have hmle : m ≤ 2 * K := (Finset.mem_range.mp hm).le
    have hCm1 : 1 ≤ C.val ^ m := Nat.one_le_pow m C.val C.pos
    have hzeta := _root_.RHTower.zeta_eq_centredTruncated_of_re_gt_neg_one hCm1 hw hw1
    unfold _root_.RHTower.zetaCentredTruncated at hzeta
    have hrad : radialCutoff (C.val ^ m) w =
        riemannZeta w + ((C.val ^ m : ℕ) : ℂ) ^ (1 - w) / (1 - w) +
        ((C.val ^ m : ℕ) : ℂ) ^ (-w) / 2 +
        w * (w + 1) * _root_.RHTower.zetaBernoulliTail (C.val ^ m) w := by
      unfold radialCutoff
      rw [show ((C.val ^ m : ℕ) : ℂ) ^ (1 - w) / (w - 1) =
        -(((C.val ^ m : ℕ) : ℂ) ^ (1 - w) / (1 - w)) by
        rw [show w - 1 = -(1 - w) by ring, div_neg]] at hzeta
      linear_combination -hzeta
    have hpow1 : ((C.val ^ m : ℕ) : ℂ) ^ (1 - w) = c ^ m * q ^ m := by
      rw [nat_cpow_one_sub (pow_pos C.pos m) w, nat_pow_cpow_neg, Nat.cast_pow]
    have hpow2 : ((C.val ^ m : ℕ) : ℂ) ^ (-w) = q ^ m := nat_pow_cpow_neg C m w
    have hqK : q ^ (2 * K - m) * q ^ m = q ^ (2 * K) := by
      rw [← pow_add, Nat.sub_add_cancel hmle]
    have hqinv : q ^ (2 * K - m) = q ^ (2 * K) * q⁻¹ ^ m := by
      rw [← hqK, mul_assoc, ← mul_pow, mul_inv_cancel₀ hq0, one_pow, mul_one]
    rw [hrad, hpow1, hpow2]
    calc 2 * (q ^ (2 * K - m) * (riemannZeta w + c ^ m * q ^ m / (1 - w) +
          q ^ m / 2 + w * (w + 1) * _root_.RHTower.zetaBernoulliTail (C.val ^ m) w))
        = 2 * riemannZeta w * q ^ (2 * K - m) +
          2 * (q ^ (2 * K - m) * q ^ m) * c ^ m / (1 - w) +
          (q ^ (2 * K - m) * q ^ m) +
          2 * w * (w + 1) * q ^ (2 * K - m) *
            _root_.RHTower.zetaBernoulliTail (C.val ^ m) w := by ring
      _ = _ := by
        rw [hqK]
        conv_lhs => arg 2; rw [hqinv]
        ring
  have hterm2 : ∀ r ∈ Finset.range K,
      2 * ((q ^ 2) ^ (K - r) * radialCutoff ((tailRadix t (j + 1)).val ^ r) w) =
        2 * riemannZeta w * q ^ (2 * K - 2 * r) +
        (2 * q ^ (2 * K) / (1 - w)) * c ^ (2 * r) +
        q ^ (2 * K) +
        2 * w * (w + 1) * q ^ (2 * K) *
          (q⁻¹ ^ (2 * r) * _root_.RHTower.zetaBernoulliTail (C.val ^ (2 * r)) w) := by
    intro r hr
    have hrlt : r < K := Finset.mem_range.mp hr
    have hrad_r : (tailRadix t (j + 1)).val ^ r = C.val ^ (2 * r) := by
      rw [hrad_succ, PNat.pow_coe, ← pow_mul]
    have hq_r : (q ^ 2) ^ (K - r) = q ^ (2 * K - 2 * r) := by
      rw [← pow_mul]
      congr 1; omega
    rw [hrad_r, hq_r]
    exact hterm1 (2 * r) (Finset.mem_range.mpr (by omega))
  -- Combine both shell sums and identify the four grouped pieces.
  rw [adjacentCutoff, hsh0, hsh1]
  change 2 * (∑ m ∈ Finset.range (2 * K), q ^ (2 * K - m) * radialCutoff (C.val ^ m) w) -
      (c + 1) * (2 * ∑ r ∈ Finset.range K,
        (q ^ 2) ^ (K - r) * radialCutoff ((tailRadix t (j + 1)).val ^ r) w) -
      _root_.RHTower.zetaPoleUnit w * finiteContrastTransfer C K w = _
  rw [Finset.mul_sum, Finset.sum_congr rfl hterm1,
    Finset.mul_sum (Finset.range K), Finset.sum_congr rfl hterm2]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  -- Match the `ζ(w)` geometric contrast with `zetaPoleUnit w * finiteContrastTransfer C K w`.
  have hzeta_piece :
      2 * riemannZeta w * ((∑ m ∈ Finset.range (2 * K), q ^ (2 * K - m)) -
          (c + 1) * ∑ r ∈ Finset.range K, q ^ (2 * K - 2 * r)) =
        _root_.RHTower.zetaPoleUnit w * finiteContrastTransfer C K w := by
    rw [sum_pow_even_contrast q c K, _root_.RHTower.zetaPoleUnit_of_ne hw1,
      finiteContrastTransfer, dslope_of_ne _ hw1, slope_def_field,
      show heat 1 C = c⁻¹ by rw [heat_eq_cpow, Complex.cpow_neg_one]]
    change 2 * riemannZeta w * (q * (1 - c * q) * ∑ r ∈ Finset.range K, q ^ (2 * r)) =
      (w - 1) * riemannZeta w *
        (-2 * c * q * ((q - c⁻¹) / (w - 1)) * ∑ r ∈ Finset.range K, q ^ (2 * r))
    field_simp [hw1_sub, hc_ne]
    ring
  have hpole_piece :
      (2 * q ^ (2 * K) / (1 - w)) * (∑ m ∈ Finset.range (2 * K), c ^ m) -
        (c + 1) * ((2 * q ^ (2 * K) / (1 - w)) * ∑ r ∈ Finset.range K, c ^ (2 * r)) = 0 := by
    have h0 := sum_pow_pole_cancel c K
    linear_combination (2 * q ^ (2 * K) / (1 - w)) * h0
  unfold adjacentBernoulliFinite
  dsimp only
  linear_combination hzeta_piece + hpole_piece

/-- Exact pole-cancelled sub-Mellin identity for `adjacentCutoff` at `X = C^(2K)` across **every**
`w` with `Re w > -1` — including `w = 1`, `Re w = 0`, and `-1 < Re w ≤ 0`. -/
theorem adjacentCutoff_radix_even_pow_eq (t : ExceptionalTime) (j K : ℕ)
    {w : ℂ} (hw : -1 < w.re) :
    let C := tailRadix t j
    let q := heat w C
    adjacentCutoff t j (C.val ^ (2 * K)) w -
        _root_.RHTower.zetaPoleUnit w * finiteContrastTransfer C K w =
      q ^ (2 * K) * (-(((C.val : ℂ) - 1) * (K : ℂ)) +
        2 * w * (w + 1) * adjacentBernoulliFinite C K w) := by
  dsimp only
  rcases ne_or_eq w 1 with hw1 | rfl
  · exact adjacentCutoff_radix_even_pow_eq_of_ne_one t j K hw hw1
  · -- Pass to `w = 1` along `w_n = 1 + (n + 1)⁻¹ → 1` by continuity of every finite shell term.
    set C := tailRadix t j
    have hcont_sum : ∀ (s : Finset ℕ) (g : ℕ → ℂ → ℂ),
        (∀ i ∈ s, ContinuousAt (g i) 1) → ContinuousAt (fun z => ∑ i ∈ s, g i z) 1 :=
      fun s _ hg => tendsto_finsetSum s fun i hi => (hg i hi).tendsto
    have hheat_cont : ∀ B : ℕ+, Continuous (fun z : ℂ => heat z B) := fun B => by
      unfold heat; fun_prop
    let lhs (z : ℂ) : ℂ :=
      adjacentCutoff t j (C.val ^ (2 * K)) z -
        _root_.RHTower.zetaPoleUnit z * finiteContrastTransfer C K z
    let rhs (z : ℂ) : ℂ :=
      (heat z C) ^ (2 * K) * (-(((C.val : ℂ) - 1) * (K : ℂ)) +
        2 * z * (z + 1) * adjacentBernoulliFinite C K z)
    have hcont_rad : ∀ N : ℕ, ContinuousAt (fun z : ℂ => radialCutoff N z) 1 := fun N => by
      unfold radialCutoff
      refine hcont_sum (Finset.Icc 1 N) (fun n z => (n : ℂ) ^ (-z)) fun n hn => ?_
      have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by linarith [Finset.mem_Icc.mp hn])
      exact continuousAt_id.neg.const_cpow (Or.inl hn0)
    have hcont_sh0 : ContinuousAt (fun z : ℂ => shellCutoff t j (C.val ^ (2 * K)) z) 1 := by
      have heq : (fun z : ℂ => shellCutoff t j (C.val ^ (2 * K)) z) =
          fun z => 2 * ∑ m ∈ Finset.range (2 * K),
            (heat z C) ^ (2 * K - m) * radialCutoff (C.val ^ m) z :=
        funext fun z => shellCutoff_radix_pow t j (2 * K) z
      rw [heq]
      refine continuousAt_const.mul
        (hcont_sum (Finset.range (2 * K))
          (fun m z => (heat z C) ^ (2 * K - m) * radialCutoff (C.val ^ m) z) fun m _ => ?_)
      exact ((hheat_cont C).continuousAt.pow _).mul (hcont_rad _)
    have hcont_sh1 : ContinuousAt (fun z : ℂ => shellCutoff t (j + 1) (C.val ^ (2 * K)) z) 1 := by
      have hpow_eq : (tailRadix t (j + 1)).val ^ K = C.val ^ (2 * K) := by
        rw [tailRadix_succ, PNat.pow_coe, ← pow_mul]
      have heq : (fun z : ℂ => shellCutoff t (j + 1) (C.val ^ (2 * K)) z) =
          fun z => 2 * ∑ r ∈ Finset.range K,
            (heat z (tailRadix t (j + 1))) ^ (K - r) *
              radialCutoff ((tailRadix t (j + 1)).val ^ r) z := by
        funext z
        rw [← hpow_eq]
        exact shellCutoff_radix_pow t (j + 1) K z
      rw [heq]
      refine continuousAt_const.mul
        (hcont_sum (Finset.range K)
          (fun r z => (heat z (tailRadix t (j + 1))) ^ (K - r) *
            radialCutoff ((tailRadix t (j + 1)).val ^ r) z) fun r _ => ?_)
      exact ((hheat_cont (tailRadix t (j + 1))).continuousAt.pow _).mul (hcont_rad _)
    have hcont_lhs : ContinuousAt lhs 1 := by
      refine (hcont_sh0.sub (continuousAt_const.mul hcont_sh1)).sub ?_
      exact _root_.RHTower.differentiable_zetaPoleUnit.continuous.continuousAt.mul
        (differentiable_finiteContrastTransfer C K).continuous.continuousAt
    have hcont_bern : ContinuousAt (adjacentBernoulliFinite C K) 1 := by
      unfold adjacentBernoulliFinite
      have hq_cont : ContinuousAt (fun z : ℂ => heat z C) 1 := (hheat_cont C).continuousAt
      have hq1_ne : heat 1 C ≠ 0 := Complex.exp_ne_zero _
      have hqinv : ContinuousAt (fun z : ℂ => (heat z C)⁻¹) 1 := hq_cont.inv₀ hq1_ne
      have htail : ∀ N : ℕ, 1 ≤ N → ContinuousAt (_root_.RHTower.zetaBernoulliTail N) 1 :=
        fun N hN => (_root_.RHTower.differentiableAt_zetaBernoulliTail hN
          (by norm_num : (-1 : ℝ) < (1 : ℂ).re)).continuousAt
      refine (hcont_sum (Finset.range (2 * K))
          (fun m z => (heat z C)⁻¹ ^ m * _root_.RHTower.zetaBernoulliTail (C.val ^ m) z)
          fun m _ => (hqinv.pow m).mul (htail _ (Nat.one_le_pow m C.val C.pos))).sub
        (continuousAt_const.mul (hcont_sum (Finset.range K)
          (fun r z => (heat z C)⁻¹ ^ (2 * r) *
            _root_.RHTower.zetaBernoulliTail (C.val ^ (2 * r)) z)
          fun r _ => (hqinv.pow (2 * r)).mul (htail _ (Nat.one_le_pow (2 * r) C.val C.pos))))
    have hcont_rhs : ContinuousAt rhs 1 := by
      have hq_cont : ContinuousAt (fun z : ℂ => (heat z C) ^ (2 * K)) 1 :=
        (hheat_cont C).continuousAt.pow (2 * K)
      refine hq_cont.mul (continuousAt_const.add ?_)
      exact (((continuousAt_const.mul continuousAt_id).mul
        (continuousAt_id.add continuousAt_const)).mul hcont_bern)
    let rseq (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ)⁻¹
    let wseq (n : ℕ) : ℂ := 1 + (rseq n : ℂ)
    have hwseq_tendsto : Tendsto wseq atTop (𝓝 1) := by
      have hr : Tendsto rseq atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
      have hinv : Tendsto (fun n : ℕ => (rseq n : ℂ)) atTop (𝓝 0) := by
        simpa only [Complex.ofReal_zero, Function.comp_def] using
          Complex.continuous_ofReal.continuousAt.tendsto.comp hr
      simpa only [add_zero] using tendsto_const_nhds.add hinv
    have heq_seq : ∀ n : ℕ, lhs (wseq n) = rhs (wseq n) := fun n => by
      have hpos : (0 : ℝ) < rseq n := inv_pos.mpr (by positivity)
      have hre : -1 < (wseq n).re := by
        dsimp only [wseq]; rw [Complex.add_re, Complex.one_re, Complex.ofReal_re]; linarith
      have hne : wseq n ≠ 1 := by
        intro h
        have := congrArg Complex.re h
        dsimp only [wseq] at this
        rw [Complex.add_re, Complex.one_re, Complex.ofReal_re] at this
        linarith
      exact adjacentCutoff_radix_even_pow_eq_of_ne_one t j K hre hne
    exact tendsto_nhds_unique (hcont_lhs.tendsto.comp hwseq_tendsto)
      ((hcont_rhs.tendsto.comp hwseq_tendsto).congr fun n => (heq_seq n).symm)

/-- Uniform bound on `‖adjacentBernoulliFinite C K w‖` across `Re w > -1`. -/
theorem norm_adjacentBernoulliFinite_le {C : ℕ+} (hC : 1 < C.val) (K : ℕ)
    {w : ℂ} (hw : -1 < w.re) :
    ‖adjacentBernoulliFinite C K w‖ ≤
      (C.val : ℝ) * ((C.val : ℝ) + 1) / (8 * (w.re + 1) * ((C.val : ℝ) - 1)) := by
  let Cr : ℝ := C.val
  have hw1_pos : 0 < w.re + 1 := by linarith
  have hCr1 : (1 : ℝ) < Cr := by dsimp only [Cr]; exact_mod_cast hC
  have hCr0 : (0 : ℝ) < Cr := by positivity
  have hc_sub : Cr - 1 ≠ 0 := (sub_pos.mpr hCr1).ne'
  have hc2_sub : Cr ^ 2 - 1 ≠ 0 := (sub_pos.mpr (one_lt_pow₀ hCr1 (by norm_num : 2 ≠ 0))).ne'
  have hgeom1 : (∑ m ∈ Finset.range (2 * K), (Cr⁻¹) ^ m) ≤ Cr / (Cr - 1) := by
    have h1_pos : 0 < 1 - Cr⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hCr1)
    have hg : (∑ m ∈ Finset.range (2 * K), (Cr⁻¹) ^ m) =
        (1 - (Cr⁻¹) ^ (2 * K)) / (1 - Cr⁻¹) := by
      rw [eq_div_iff h1_pos.ne']
      linear_combination -(geom_sum_mul (Cr⁻¹) (2 * K))
    rw [hg]
    calc (1 - (Cr⁻¹) ^ (2 * K)) / (1 - Cr⁻¹)
        ≤ 1 / (1 - Cr⁻¹) := div_le_div_of_nonneg_right
          (sub_le_self 1 (pow_nonneg (inv_nonneg.mpr hCr0.le) _)) h1_pos.le
      _ = Cr / (Cr - 1) := by field_simp [hCr0.ne', hc_sub, h1_pos.ne']
  have hgeom2 : (∑ r ∈ Finset.range K, (Cr⁻¹) ^ (2 * r)) ≤ Cr ^ 2 / (Cr ^ 2 - 1) := by
    have hCr2 : (1 : ℝ) < Cr ^ 2 := one_lt_pow₀ hCr1 (by norm_num)
    have h1_pos : 0 < 1 - (Cr ^ 2)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hCr2)
    have hpow : (∑ r ∈ Finset.range K, (Cr⁻¹) ^ (2 * r)) =
        ∑ r ∈ Finset.range K, ((Cr ^ 2)⁻¹) ^ r := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [pow_mul, inv_pow]
    have hg : (∑ r ∈ Finset.range K, ((Cr ^ 2)⁻¹) ^ r) =
        (1 - ((Cr ^ 2)⁻¹) ^ K) / (1 - (Cr ^ 2)⁻¹) := by
      rw [eq_div_iff h1_pos.ne']
      linear_combination -(geom_sum_mul ((Cr ^ 2)⁻¹) K)
    rw [hpow, hg]
    calc (1 - ((Cr ^ 2)⁻¹) ^ K) / (1 - (Cr ^ 2)⁻¹)
        ≤ 1 / (1 - (Cr ^ 2)⁻¹) := div_le_div_of_nonneg_right
          (sub_le_self 1 (pow_nonneg (inv_nonneg.mpr (sq_pos_of_pos hCr0).le) _)) h1_pos.le
      _ = Cr ^ 2 / (Cr ^ 2 - 1) := by
          have hc2_0 : Cr ^ 2 ≠ 0 := (sq_pos_of_pos hCr0).ne'
          field_simp [hc2_0, hc2_sub, h1_pos.ne']
  unfold adjacentBernoulliFinite
  dsimp only
  refine (norm_sub_le _ _).trans ?_
  have hb1 : ‖∑ m ∈ Finset.range (2 * K),
      (heat w C)⁻¹ ^ m * _root_.RHTower.zetaBernoulliTail (C.val ^ m) w‖ ≤
      (1 / (8 * (w.re + 1))) * (Cr / (Cr - 1)) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun m _ =>
      norm_inv_heat_mul_bernoulliTail_le C hw m).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hgeom1 (by positivity)
  have hnorm_cp1 : ‖(C.val : ℂ) + 1‖ = Cr + 1 := by
    have : (C.val : ℂ) + 1 = ((Cr + 1 : ℝ) : ℂ) := by simp [Cr]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hb2 : ‖((C.val : ℂ) + 1) * ∑ r ∈ Finset.range K,
      (heat w C)⁻¹ ^ (2 * r) * _root_.RHTower.zetaBernoulliTail (C.val ^ (2 * r)) w‖ ≤
      (Cr + 1) * ((1 / (8 * (w.re + 1))) * (Cr ^ 2 / (Cr ^ 2 - 1))) := by
    rw [norm_mul, hnorm_cp1]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun r _ =>
      norm_inv_heat_mul_bernoulliTail_le C hw (2 * r)).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hgeom2 (by positivity)
  refine (add_le_add hb1 hb2).trans_eq ?_
  have hwpos : 8 * (w.re + 1) ≠ 0 := by linarith
  dsimp only [Cr] at hc_sub hc2_sub ⊢
  field_simp [hwpos, hc_sub, hc2_sub]
  ring

/-- Pure-exponential, `|ζ(w)|`-free, pole-free error bound for `spikeSubtractedAdjacentCutoff`
across **every** `w` with `Re w > -1` (including `w = 1`, `Re w = 0`, and `-1 < Re w ≤ 0`). -/
theorem norm_spikeSubtractedAdjacentCutoff_sub_le (t : ExceptionalTime) (j K : ℕ)
    {w : ℂ} (hw : -1 < w.re) :
    let C := tailRadix t j
    ‖spikeSubtractedAdjacentCutoff t j K w -
        _root_.RHTower.zetaPoleUnit w * finiteContrastTransfer C K w‖ ≤
      ((C.val : ℝ) * ((C.val : ℝ) + 1) * ‖w * (w + 1)‖ /
        (4 * (w.re + 1) * ((C.val : ℝ) - 1))) *
        (C.val : ℝ) ^ (-(2 * K : ℝ) * w.re) := by
  dsimp only
  set C := tailRadix t j
  have hC1 : 1 < C.val := radix_gt_one t j
  have hCr1 : (1 : ℝ) < C.val := by exact_mod_cast hC1
  have hCr0 : (0 : ℝ) < C.val := by positivity
  have heq := adjacentCutoff_radix_even_pow_eq t j K hw
  dsimp only at heq
  have hsub : spikeSubtractedAdjacentCutoff t j K w -
      _root_.RHTower.zetaPoleUnit w * finiteContrastTransfer C K w =
      (2 * (w * (w + 1)) * adjacentBernoulliFinite C K w) * (heat w C) ^ (2 * K) := by
    unfold spikeSubtractedAdjacentCutoff
    dsimp only
    linear_combination heq
  rw [hsub, norm_mul, norm_heat_pow, Nat.cast_mul, Nat.cast_ofNat]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hCr0.le _)
  rw [norm_mul, norm_mul, Complex.norm_ofNat]
  have hb := norm_adjacentBernoulliFinite_le hC1 K hw
  calc 2 * ‖w * (w + 1)‖ * ‖adjacentBernoulliFinite C K w‖
      ≤ 2 * ‖w * (w + 1)‖ *
          ((C.val : ℝ) * ((C.val : ℝ) + 1) / (8 * (w.re + 1) * ((C.val : ℝ) - 1))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (C.val : ℝ) * ((C.val : ℝ) + 1) * ‖w * (w + 1)‖ /
          (4 * (w.re + 1) * ((C.val : ℝ) - 1)) := by
        have hd4 : 4 * (w.re + 1) * ((C.val : ℝ) - 1) ≠ 0 :=
          mul_ne_zero (by linarith) (sub_pos.mpr hCr1).ne'
        have hd8 : 8 * (w.re + 1) * ((C.val : ℝ) - 1) ≠ 0 :=
          mul_ne_zero (by linarith) (sub_pos.mpr hCr1).ne'
        rw [mul_div_assoc', div_eq_div_iff hd8 hd4]
        ring

/-- `|ζ(w)|`-free, pole-free error bound for raw `adjacentCutoff t j (C^(2K)) w` across **every**
`w` with `Re w > -1` (including `w = 1`). -/
theorem norm_adjacentCutoff_radix_even_pow_sub_le (t : ExceptionalTime) (j K : ℕ)
    {w : ℂ} (hw : -1 < w.re) :
    let C := tailRadix t j
    ‖adjacentCutoff t j (C.val ^ (2 * K)) w -
        _root_.RHTower.zetaPoleUnit w * finiteContrastTransfer C K w‖ ≤
      (((C.val : ℝ) - 1) * (K : ℝ) +
        (C.val : ℝ) * ((C.val : ℝ) + 1) * ‖w * (w + 1)‖ /
          (4 * (w.re + 1) * ((C.val : ℝ) - 1))) *
        (C.val : ℝ) ^ (-(2 * K : ℝ) * w.re) := by
  dsimp only
  set C := tailRadix t j
  have hC1 : 1 < C.val := radix_gt_one t j
  have hCr1 : (1 : ℝ) < C.val := by exact_mod_cast hC1
  have hsub_bd := norm_spikeSubtractedAdjacentCutoff_sub_le t j K hw
  dsimp only at hsub_bd
  have hsplit : adjacentCutoff t j (C.val ^ (2 * K)) w -
      _root_.RHTower.zetaPoleUnit w * finiteContrastTransfer C K w =
      (spikeSubtractedAdjacentCutoff t j K w -
        _root_.RHTower.zetaPoleUnit w * finiteContrastTransfer C K w) -
      (((C.val : ℂ) - 1) * (K : ℂ)) * (heat w C) ^ (2 * K) := by
    unfold spikeSubtractedAdjacentCutoff; dsimp only; ring
  have hspike_norm : ‖(((C.val : ℂ) - 1) * (K : ℂ)) * (heat w C) ^ (2 * K)‖ =
      ((C.val : ℝ) - 1) * (K : ℝ) * (C.val : ℝ) ^ (-(2 * K : ℝ) * w.re) := by
    have hc1_norm : ‖(C.val : ℂ) - 1‖ = (C.val : ℝ) - 1 := by
      have : (C.val : ℂ) - 1 = (((C.val : ℝ) - 1 : ℝ) : ℂ) := by simp
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hCr1)]
    rw [norm_mul, norm_mul, hc1_norm, Complex.norm_natCast, norm_heat_pow,
      Nat.cast_mul, Nat.cast_ofNat]
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  rw [hspike_norm]
  dsimp only [C] at hsub_bd ⊢
  linarith

/-- Sub-Mellin `O(C^(-2K(Re w + 1)))` asymptotic bound for `adjacentCutoff t j (C^(2K)) w` across
all `Re w > -1` (converging exponentially as `K → ∞` even in the reflected Euler strip
`-1 < Re w ≤ 0` and on `Re w = 0`, as well as at `w = 1`). -/
theorem norm_adjacentCutoff_radix_even_pow_sub_subMellin_le
    (t : ExceptionalTime) (j K : ℕ) {w : ℂ} (hw : -1 < w.re) :
    let C := tailRadix t j
    let q := heat w C
    ‖adjacentCutoff t j (C.val ^ (2 * K)) w -
        _root_.RHTower.zetaPoleUnit w * finiteContrastTransfer C K w +
        (((C.val : ℂ) - 1) * (K : ℂ) - 2 * w * (w + 1) * adjacentBernoulliSeries C w) *
          q ^ (2 * K)‖ ≤
      ((C.val : ℝ) * ((C.val : ℝ) + 1) * ‖w * (w + 1)‖ /
        (4 * (w.re + 1) * ((C.val : ℝ) - 1))) *
        (C.val : ℝ) ^ (-(2 * K : ℝ) * (w.re + 1)) := by
  dsimp only
  set C := tailRadix t j
  let Cr : ℝ := C.val
  have hw1_pos : 0 < w.re + 1 := by linarith
  have hC1 : 1 < C.val := radix_gt_one t j
  have hCr1 : (1 : ℝ) < Cr := by dsimp only [Cr]; exact_mod_cast hC1
  have hCr0 : (0 : ℝ) < Cr := by positivity
  have hc_sub : Cr - 1 ≠ 0 := (sub_pos.mpr hCr1).ne'
  have hc2_sub : Cr ^ 2 - 1 ≠ 0 := (sub_pos.mpr (one_lt_pow₀ hCr1 (by norm_num : 2 ≠ 0))).ne'
  let term (m : ℕ) : ℂ := (heat w C)⁻¹ ^ m * _root_.RHTower.zetaBernoulliTail (C.val ^ m) w
  have hsum1 : Summable term := summable_inv_heat_mul_bernoulliTail C hC1 hw
  have hsum2 : Summable (fun r : ℕ => term (2 * r)) := by
    have hCr2 : (1 : ℝ) < Cr ^ 2 := one_lt_pow₀ hCr1 (by norm_num)
    have hinv2 : (Cr ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hCr2
    have hgeom2 : Summable fun r : ℕ => (1 / (8 * (w.re + 1))) * ((Cr ^ 2)⁻¹) ^ r :=
      (summable_geometric_of_lt_one (by positivity) hinv2).mul_left _
    refine Summable.of_norm_bounded hgeom2 fun r => ?_
    have hbd := norm_inv_heat_mul_bernoulliTail_le C hw (2 * r)
    have hexp : ((C.val : ℝ)⁻¹) ^ (2 * r) = ((Cr ^ 2)⁻¹) ^ r := by
      dsimp only [Cr]; rw [pow_mul, inv_pow]
    rwa [hexp] at hbd
  have htail1 : ‖(∑' m : ℕ, term m) - ∑ m ∈ Finset.range (2 * K), term m‖ ≤
      (1 / (8 * (w.re + 1))) * (Cr / (Cr - 1)) * (Cr⁻¹) ^ (2 * K) := by
    rw [← hsum1.sum_add_tsum_nat_add (2 * K), add_sub_cancel_left]
    have hinv1 : Cr⁻¹ < 1 := inv_lt_one_of_one_lt₀ hCr1
    have hinj1 : Function.Injective (fun n : ℕ => n + 2 * K) := fun _ _ h => Nat.add_right_cancel h
    have hsum_shift1 : Summable (fun n : ℕ => ‖term (n + 2 * K)‖) :=
      (hsum1.comp_injective hinj1).norm
    have hg : Summable fun n : ℕ =>
        (1 / (8 * (w.re + 1))) * (Cr⁻¹) ^ (2 * K) * (Cr⁻¹) ^ n :=
      (summable_geometric_of_lt_one (by positivity) hinv1).mul_left _
    refine (norm_tsum_le_tsum_norm hsum_shift1).trans ?_
    refine (Summable.tsum_le_tsum (fun n => ?_) hsum_shift1 hg).trans_eq ?_
    · have hbd := norm_inv_heat_mul_bernoulliTail_le C hw (n + 2 * K)
      have hexp : ((C.val : ℝ)⁻¹) ^ (n + 2 * K) = (Cr⁻¹) ^ (2 * K) * (Cr⁻¹) ^ n := by
        dsimp only [Cr]; rw [pow_add, mul_comm]
      dsimp only [term]
      rwa [hexp, ← mul_assoc] at hbd
    · rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hinv1]
      have h1_pos : 0 < 1 - Cr⁻¹ := sub_pos.mpr hinv1
      have : (1 - Cr⁻¹)⁻¹ = Cr / (Cr - 1) := by field_simp [hCr0.ne', hc_sub, h1_pos.ne']
      rw [this]; ring
  have htail2 : ‖(∑' r : ℕ, term (2 * r)) - ∑ r ∈ Finset.range K, term (2 * r)‖ ≤
      (1 / (8 * (w.re + 1))) * (Cr ^ 2 / (Cr ^ 2 - 1)) * (Cr⁻¹) ^ (2 * K) := by
    rw [← hsum2.sum_add_tsum_nat_add K, add_sub_cancel_left]
    have hCr2 : (1 : ℝ) < Cr ^ 2 := one_lt_pow₀ hCr1 (by norm_num)
    have hinv2 : (Cr ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hCr2
    have hinj2 : Function.Injective (fun n : ℕ => n + K) := fun _ _ h => Nat.add_right_cancel h
    have hsum_shift2 : Summable (fun n : ℕ => ‖term (2 * (n + K))‖) :=
      (hsum2.comp_injective hinj2).norm
    have hg : Summable fun n : ℕ =>
        (1 / (8 * (w.re + 1))) * ((Cr ^ 2)⁻¹) ^ K * ((Cr ^ 2)⁻¹) ^ n :=
      (summable_geometric_of_lt_one (by positivity) hinv2).mul_left _
    refine (norm_tsum_le_tsum_norm hsum_shift2).trans ?_
    refine (Summable.tsum_le_tsum (fun n => ?_) hsum_shift2 hg).trans_eq ?_
    · have hbd := norm_inv_heat_mul_bernoulliTail_le C hw (2 * (n + K))
      have hexp : ((C.val : ℝ)⁻¹) ^ (2 * (n + K)) = ((Cr ^ 2)⁻¹) ^ K * ((Cr ^ 2)⁻¹) ^ n := by
        dsimp only [Cr]; rw [Nat.mul_add, pow_add, pow_mul, pow_mul, inv_pow]; ring
      dsimp only [term]
      rwa [hexp, ← mul_assoc] at hbd
    · rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hinv2]
      have h1_pos : 0 < 1 - (Cr ^ 2)⁻¹ := sub_pos.mpr hinv2
      have hc2_0 : Cr ^ 2 ≠ 0 := (sq_pos_of_pos hCr0).ne'
      have : (1 - (Cr ^ 2)⁻¹)⁻¹ = Cr ^ 2 / (Cr ^ 2 - 1) := by
        field_simp [hc2_0, hc2_sub, h1_pos.ne']
      have hpowK : ((Cr ^ 2)⁻¹) ^ K = (Cr⁻¹) ^ (2 * K) := by rw [inv_pow, ← pow_mul, ← inv_pow]
      rw [this, hpowK]; ring
  have heq := adjacentCutoff_radix_even_pow_eq t j K hw
  dsimp only at heq
  have hdiff : adjacentCutoff t j (C.val ^ (2 * K)) w -
      _root_.RHTower.zetaPoleUnit w * finiteContrastTransfer C K w +
      (((C.val : ℂ) - 1) * (K : ℂ) - 2 * w * (w + 1) * adjacentBernoulliSeries C w) *
        (heat w C) ^ (2 * K) =
      -(2 * (w * (w + 1)) * (adjacentBernoulliSeries C w - adjacentBernoulliFinite C K w)) *
        (heat w C) ^ (2 * K) := by
    linear_combination heq
  have hser_diff : ‖adjacentBernoulliSeries C w - adjacentBernoulliFinite C K w‖ ≤
      (Cr * (Cr + 1) / (8 * (w.re + 1) * (Cr - 1))) * (Cr⁻¹) ^ (2 * K) := by
    have hsplit : adjacentBernoulliSeries C w - adjacentBernoulliFinite C K w =
        ((∑' m : ℕ, term m) - ∑ m ∈ Finset.range (2 * K), term m) -
        ((C.val : ℂ) + 1) * ((∑' r : ℕ, term (2 * r)) - ∑ r ∈ Finset.range K, term (2 * r)) := by
      unfold adjacentBernoulliSeries adjacentBernoulliFinite
      dsimp only [term]
      ring
    have hnorm_cp1 : ‖(C.val : ℂ) + 1‖ = Cr + 1 := by
      have : (C.val : ℂ) + 1 = ((Cr + 1 : ℝ) : ℂ) := by simp [Cr]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hsplit]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, hnorm_cp1]
    refine (add_le_add htail1 (mul_le_mul_of_nonneg_left htail2 (by positivity))).trans_eq ?_
    have hwpos : 8 * (w.re + 1) ≠ 0 := by linarith
    field_simp [hwpos, hc_sub, hc2_sub]
    ring
  have hrpow_comb : (Cr⁻¹) ^ (2 * K) * Cr ^ (-(2 * K : ℝ) * w.re) =
      Cr ^ (-(2 * K : ℝ) * (w.re + 1)) := by
    rw [inv_pow, ← Real.rpow_neg_one (Cr ^ (2 * K)), ← Real.rpow_natCast Cr (2 * K),
      ← Real.rpow_mul hCr0.le, ← Real.rpow_add hCr0, Nat.cast_mul, Nat.cast_ofNat]
    congr 1; ring
  have h84 : 2 * ‖w * (w + 1)‖ * (Cr * (Cr + 1) / (8 * (w.re + 1) * (Cr - 1))) =
      Cr * (Cr + 1) * ‖w * (w + 1)‖ / (4 * (w.re + 1) * (Cr - 1)) := by
    have hd4 : 4 * (w.re + 1) * (Cr - 1) ≠ 0 := mul_ne_zero (by linarith) hc_sub
    have hd8 : 8 * (w.re + 1) * (Cr - 1) ≠ 0 := mul_ne_zero (by linarith) hc_sub
    rw [mul_div_assoc', div_eq_div_iff hd8 hd4]
    ring
  rw [hdiff, norm_mul, norm_neg, norm_mul, norm_mul, Complex.norm_ofNat, norm_heat_pow,
    Nat.cast_mul, Nat.cast_ofNat]
  calc 2 * ‖w * (w + 1)‖ * ‖adjacentBernoulliSeries C w - adjacentBernoulliFinite C K w‖ *
        Cr ^ (-(2 * (K : ℝ)) * w.re)
      ≤ 2 * ‖w * (w + 1)‖ *
          ((Cr * (Cr + 1) / (8 * (w.re + 1) * (Cr - 1))) * (Cr⁻¹) ^ (2 * K)) *
          Cr ^ (-(2 * (K : ℝ)) * w.re) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hser_diff (by positivity))
          (Real.rpow_nonneg hCr0.le _)
    _ = (2 * ‖w * (w + 1)‖ * (Cr * (Cr + 1) / (8 * (w.re + 1) * (Cr - 1)))) *
          ((Cr⁻¹) ^ (2 * K) * Cr ^ (-(2 * (K : ℝ)) * w.re)) := by ring
    _ = _ := by rw [h84, hrpow_comb]

#print axioms differentiable_finiteContrastTransfer
#print axioms zetaPoleUnit_mul_finiteContrastTransfer_eq
#print axioms adjacentCutoff_radix_even_pow_eq
#print axioms norm_spikeSubtractedAdjacentCutoff_sub_le
#print axioms norm_adjacentCutoff_radix_even_pow_sub_le
#print axioms norm_adjacentCutoff_radix_even_pow_sub_subMellin_le

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation
