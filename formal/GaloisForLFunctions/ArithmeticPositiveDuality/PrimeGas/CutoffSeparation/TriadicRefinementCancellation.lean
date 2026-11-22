import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation.RadixShellExpansion

/-!
# Counterterm-free and spike-free triadic refinement Dirichlet sums

Successive clock refinements `j, j + 1, j + 2` square the square-shell radix to `C, C^2, C^4`.
Comparing two refinements `S_j(X, w) - (C + 1) S_{j+1}(X, w)` cancels the `X^(1-w)/(1-w)` density
divergence without `w`-dependent counterterms, yet at every zero of `ζ(w)` in `Re w > 0` it retains
a nonzero logarithmic radix-shell spike asymptotic to `-(C - 1) K C^(-2Kw)` along `X = C^(2K)`.

Combining three consecutive refinements with integer weights depending only on `C`,

`T_{t,j}(X, w) = (C + 1) S_j(X, w) - (C^2 + 2C + 3) S_{j+1}(X, w) + 2(C^2 + 1) S_{j+2}(X, w)`,

cancels both the `X^(1-w)/(1-w)` power divergence at all cutoffs `X` and the `K C^(-4Kw)`
logarithmic spike along aligned radix shells `X = C^(4K)`, while converging on `0 < Re w < 1` to
`ζ(w)` times an elementary rational function of `C^(-w)` that never vanishes in `0 ≤ Re w < 1`.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation

open AntipodalSpectrum Filter
open scoped Topology

/-- Each clock halving squares `tailRadix`. -/
theorem tailRadix_succ_sq (t : ExceptionalTime) (j : ℕ) :
    tailRadix t (j + 1) = (tailRadix t j) ^ 2 := by
  rw [radix_sq]
  change (block t) ^ (windingOrder (refined t (j + 1)) / 2) = _
  rw [(refined_parameters t (j + 1)).2.2, (refined_parameters t j).2.2, pow_succ' 2 j,
    Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

theorem tailRadix_add_two_pow_four (t : ExceptionalTime) (j : ℕ) :
    tailRadix t (j + 2) = (tailRadix t j) ^ 4 := by
  rw [show j + 2 = (j + 1) + 1 by omega, tailRadix_succ_sq, tailRadix_succ_sq, ← pow_mul]

theorem heat_tailRadix_succ (t : ExceptionalTime) (j : ℕ) (w : ℂ) :
    heat w (tailRadix t (j + 1)) = (heat w (tailRadix t j)) ^ 2 := by
  rw [tailRadix_succ_sq, sq, heat_mul, sq]

theorem heat_tailRadix_add_two (t : ExceptionalTime) (j : ℕ) (w : ℂ) :
    heat w (tailRadix t (j + 2)) = (heat w (tailRadix t j)) ^ 4 := by
  rw [show j + 2 = (j + 1) + 1 by omega, heat_tailRadix_succ, heat_tailRadix_succ, ← pow_mul]

/-- Two-refinement integer-weighted finite shell contrast `S_j(X, w) - (C + 1) S_{j+1}(X, w)`. -/
def dyadicRefinementContrast (t : ExceptionalTime) (j X : ℕ) (w : ℂ) : ℂ :=
  shellCutoff t j X w - (((tailRadix t j).val : ℂ) + 1) * shellCutoff t (j + 1) X w

theorem dyadicRefinementContrast_eq_renormalized (t : ExceptionalTime) (j X : ℕ) {w : ℂ} :
    dyadicRefinementContrast t j X w =
      renormalizedCutoff t j X w -
        (((tailRadix t j).val : ℂ) + 1) * renormalizedCutoff t (j + 1) X w := by
  let C := tailRadix t j
  have hC1 : 1 < C.val := radix_gt_one t j
  have hc1 : (C.val : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hC1.ne')
  have hC2 : 1 < C.val ^ 2 := one_lt_pow₀ hC1 (by norm_num)
  have hc2 : (C.val : ℂ) ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hC2.ne')
  have hden : 2 / ((C.val : ℂ) - 1) - ((C.val : ℂ) + 1) * (2 / ((C.val : ℂ) ^ 2 - 1)) = 0 := by
    field_simp [hc1, hc2]; ring
  rw [dyadicRefinementContrast, renormalizedCutoff_eq, renormalizedCutoff_eq,
    tailRadix_succ_sq, PNat.pow_coe, Nat.cast_pow]
  linear_combination ((X : ℂ) ^ (1 - w) / (1 - w)) * hden

/-- Two-refinement spike obstruction: at every zero of `ζ(w)` in `Re w > 0`, the density-matched
contrast `S_j(C^(2K), w) - (C + 1) S_{j+1}(C^(2K), w)` still retains a nonzero logarithmic spike
asymptotic to `-(C - 1) K C^(-2Kw)`. -/
theorem tendsto_dyadicRefinementContrast_zero_spike (t : ExceptionalTime) (j : ℕ)
    {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) (hz : riemannZeta w = 0) :
    Tendsto (fun K : ℕ =>
      dyadicRefinementContrast t j ((tailRadix t j).val ^ (2 * K)) w /
        ((K : ℂ) * (heat w (tailRadix t j)) ^ (2 * K)))
      atTop (𝓝 (-(((tailRadix t j).val : ℂ) - 1))) := by
  let C := tailRadix t j
  let q := heat w C
  have h0 := (zeta_zero_iff_radix_pow_spike t j hw hw1).mp hz
  have h1 := (zeta_zero_iff_radix_pow_spike t (j + 1) hw hw1).mp hz
  have hdouble : Tendsto (fun K : ℕ => 2 * K) atTop atTop :=
    tendsto_atTop_mono (fun K => by dsimp; omega) tendsto_id
  have h0_even := (h0.comp hdouble).const_mul (2 : ℂ)
  rw [mul_one] at h0_even
  have hcomb := h0_even.sub (h1.const_mul (((C.val : ℂ) + 1)))
  rw [mul_one, show (2 : ℂ) - ((C.val : ℂ) + 1) = -((C.val : ℂ) - 1) by ring] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with K hK0
  dsimp only [Function.comp_apply]
  have hK_ne : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hK0.ne'
  have hq_ne : q ^ (2 * K) ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  have hrad_sq : (tailRadix t (j + 1)).val ^ K = C.val ^ (2 * K) := by
    rw [tailRadix_succ_sq, PNat.pow_coe, ← pow_mul]
  have hheat_sq : (heat w (tailRadix t (j + 1))) ^ K = q ^ (2 * K) := by
    rw [heat_tailRadix_succ, ← pow_mul]
  rw [hrad_sq, hheat_sq, dyadicRefinementContrast_eq_renormalized, Nat.cast_mul, Nat.cast_ofNat]
  dsimp only [C, q]
  field_simp [hK_ne, hq_ne]

/-- Three-refinement integer-weighted finite shell combination eliminating both the `X^(1-w)/(1-w)`
counterterm and the `K C^(-4Kw)` radix-shell logarithmic spike. -/
def triadicRefinementCutoff (t : ExceptionalTime) (j X : ℕ) (w : ℂ) : ℂ :=
  let c : ℂ := (tailRadix t j).val
  (c + 1) * shellCutoff t j X w -
    (c ^ 2 + 2 * c + 3) * shellCutoff t (j + 1) X w +
    2 * (c ^ 2 + 1) * shellCutoff t (j + 2) X w

/-- Elementary nonvanishing multiplier in the limit of `triadicRefinementCutoff`. -/
def triadicMultiplier (C : ℕ+) (w : ℂ) : ℂ :=
  let c : ℂ := C.val
  let q := heat w C
  2 * q * (1 - c * q) * ((c + 1) + (c - 1) * q) / ((1 + q) * (1 + q ^ 2))

/-- Exact cancellation of the `X^(1-w)/(1-w)` density counterterms across `j, j + 1, j + 2`. -/
theorem triadicRefinementCutoff_eq_renormalized (t : ExceptionalTime) (j X : ℕ) (w : ℂ) :
    let c : ℂ := (tailRadix t j).val
    triadicRefinementCutoff t j X w =
      (c + 1) * renormalizedCutoff t j X w -
        (c ^ 2 + 2 * c + 3) * renormalizedCutoff t (j + 1) X w +
        2 * (c ^ 2 + 1) * renormalizedCutoff t (j + 2) X w := by
  dsimp only
  let C := tailRadix t j
  let c : ℂ := C.val
  have hC1 : 1 < C.val := radix_gt_one t j
  have hc1 : c - 1 ≠ 0 := sub_ne_zero.mpr (by dsimp only [c]; exact_mod_cast hC1.ne')
  have hc2 : c ^ 2 - 1 ≠ 0 :=
    sub_ne_zero.mpr (by dsimp only [c]; exact_mod_cast (one_lt_pow₀ hC1 (by norm_num : 2 ≠ 0)).ne')
  have hc4 : c ^ 4 - 1 ≠ 0 :=
    sub_ne_zero.mpr (by dsimp only [c]; exact_mod_cast (one_lt_pow₀ hC1 (by norm_num : 4 ≠ 0)).ne')
  have hden : (c + 1) * (2 / (c - 1)) - (c ^ 2 + 2 * c + 3) * (2 / (c ^ 2 - 1)) +
      2 * (c ^ 2 + 1) * (2 / (c ^ 4 - 1)) = 0 := by
    field_simp [hc1, hc2, hc4]; ring
  rw [triadicRefinementCutoff, renormalizedCutoff_eq, renormalizedCutoff_eq, renormalizedCutoff_eq,
    tailRadix_succ_sq, tailRadix_add_two_pow_four, PNat.pow_coe, PNat.pow_coe,
    Nat.cast_pow, Nat.cast_pow]
  linear_combination ((X : ℂ) ^ (1 - w) / (1 - w)) * hden

/-- Convergence of the unrenormalized integer combination `triadicRefinementCutoff` on `Re w > 0`, `w ≠ 1`. -/
theorem triadicRefinementCutoff_limit (t : ExceptionalTime) (j : ℕ)
    {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) :
    Tendsto (fun X => triadicRefinementCutoff t j X w) atTop
      (𝓝 (riemannZeta w * triadicMultiplier (tailRadix t j) w)) := by
  let C := tailRadix t j
  let c : ℂ := C.val
  let q := heat w C
  have hC1 : 1 < C.val := radix_gt_one t j
  have hq : ‖q‖ < 1 := heat_contraction C hC1 w hw
  have hq2 : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  have hq4 : ‖q ^ 4‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  have hn1 : (1 : ℂ) - q ≠ 0 := sub_ne_zero.mpr fun he => hq.ne (by rw [← he, norm_one])
  have hn2 : (1 : ℂ) - q ^ 2 ≠ 0 := sub_ne_zero.mpr fun he => hq2.ne (by rw [← he, norm_one])
  have hn4 : (1 : ℂ) - q ^ 4 ≠ 0 := sub_ne_zero.mpr fun he => hq4.ne (by rw [← he, norm_one])
  have hp1 : (1 : ℂ) + q ≠ 0 := fun he =>
    hq.ne (by rw [show q = -1 by linear_combination he, norm_neg, norm_one])
  have hp2 : (1 : ℂ) + q ^ 2 ≠ 0 := fun he =>
    hq2.ne (by rw [show q ^ 2 = -1 by linear_combination he, norm_neg, norm_one])
  have hl0 := (renormalized_cutoff_limit t j ⟨w, hw, hw1⟩).const_mul (c + 1)
  have hl1 := (renormalized_cutoff_limit t (j + 1) ⟨w, hw, hw1⟩).const_mul (c ^ 2 + 2 * c + 3)
  have hl2 := (renormalized_cutoff_limit t (j + 2) ⟨w, hw, hw1⟩).const_mul (2 * (c ^ 2 + 1))
  dsimp only at hl0 hl1 hl2
  rw [heat_tailRadix_succ] at hl1
  rw [heat_tailRadix_add_two] at hl2
  have hcomb := (hl0.sub hl1).add hl2
  have halg : (c + 1) * (2 * q * riemannZeta w / (1 - q)) -
      (c ^ 2 + 2 * c + 3) * (2 * q ^ 2 * riemannZeta w / (1 - q ^ 2)) +
      2 * (c ^ 2 + 1) * (2 * q ^ 4 * riemannZeta w / (1 - q ^ 4)) =
      riemannZeta w * triadicMultiplier C w := by
    unfold triadicMultiplier
    dsimp only [c, q] at hn1 hn2 hn4 hp1 hp2 ⊢
    field_simp [hn1, hn2, hn4, hp1, hp2]
    ring
  rw [halg] at hcomb
  refine hcomb.congr fun X => ?_
  have heq := triadicRefinementCutoff_eq_renormalized t j X w
  dsimp only at heq
  exact heq.symm

/-- Nonvanishing of `triadicMultiplier` throughout the open critical strip `0 < Re w < 1`. -/
theorem triadicMultiplier_ne_zero {C : ℕ+} (hC : 1 < C.val) {w : ℂ}
    (hlo : 0 < w.re) (hhi : w.re < 1) :
    triadicMultiplier C w ≠ 0 := by
  let c : ℂ := C.val
  let q := heat w C
  have hCr1 : (1 : ℝ) < C.val := by exact_mod_cast hC
  have hCr0 : (0 : ℝ) < C.val := by positivity
  have hq_ne : q ≠ 0 := Complex.exp_ne_zero _
  have hq_lt : ‖q‖ < 1 := heat_contraction C hC w hlo
  have hq2_lt : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq_lt (by norm_num)
  have hp1 : (1 : ℂ) + q ≠ 0 := fun he =>
    hq_lt.ne (by rw [show q = -1 by linear_combination he, norm_neg, norm_one])
  have hp2 : (1 : ℂ) + q ^ 2 ≠ 0 := fun he =>
    hq2_lt.ne (by rw [show q ^ 2 = -1 by linear_combination he, norm_neg, norm_one])
  have h1cq : (1 : ℂ) - c * q ≠ 0 := by
    intro he
    have heq1 : c * q = 1 := by linear_combination -he
    have hnorm := congrArg norm heq1
    dsimp only [c, q] at hnorm
    rw [norm_mul, norm_one, Complex.norm_natCast, norm_heat, energy,
      mul_comm (-w.re) (Real.log C.val),
      ← Real.rpow_def_of_pos hCr0, ← Real.rpow_one_add' hCr0.le (by linarith)] at hnorm
    exact (Real.one_lt_rpow hCr1 (by linarith : 0 < 1 + -w.re)).ne' hnorm
  have hlin : (c + 1) + (c - 1) * q ≠ 0 := by
    intro he
    have heq : (c + 1) = -((c - 1) * q) := by linear_combination he
    have hnorm := congrArg norm heq
    have hc_p1 : ‖c + 1‖ = (C.val : ℝ) + 1 := by
      have : c + 1 = (((C.val : ℝ) + 1 : ℝ) : ℂ) := by simp [c]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hc_m1 : ‖c - 1‖ = (C.val : ℝ) - 1 := by
      have : c - 1 = (((C.val : ℝ) - 1 : ℝ) : ℂ) := by simp [c]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hCr1)]
    rw [norm_neg, norm_mul, hc_p1, hc_m1] at hnorm
    have hle : ((C.val : ℝ) - 1) * ‖q‖ ≤ ((C.val : ℝ) - 1) * 1 :=
      mul_le_mul_of_nonneg_left hq_lt.le (sub_pos.mpr hCr1).le
    linarith
  unfold triadicMultiplier
  dsimp only
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hq_ne) h1cq) hlin)
    (mul_ne_zero hp1 hp2)

/-- Faithful zero detection in `0 < Re w < 1` by the counterterm-free triadic sum. -/
theorem triadicRefinementCutoff_zero_iff (t : ExceptionalTime) (j : ℕ)
    {w : ℂ} (hlo : 0 < w.re) (hhi : w.re < 1) :
    Tendsto (fun X => triadicRefinementCutoff t j X w) atTop (𝓝 0) ↔ riemannZeta w = 0 := by
  have hw1 : w ≠ 1 := fun he => hhi.ne (by rw [he, Complex.one_re])
  have hlim := triadicRefinementCutoff_limit t j hlo hw1
  have hmul_ne := triadicMultiplier_ne_zero (radix_gt_one t j) hlo hhi
  constructor
  · intro h0
    have heq := tendsto_nhds_unique hlim h0
    exact (mul_eq_zero.mp heq).resolve_right hmul_ne
  · intro hz
    simpa only [hz, zero_mul] using hlim

/-- Exact elimination of the `K C^(-4Kw)` logarithmic spike at aligned radix shells `X = C^(4K)`,
reducing the error of `triadicRefinementCutoff` from `O(X^(-Re w) log X)` to `O(X^(-Re w))`. -/
theorem norm_triadicRefinementCutoff_radix_pow_sub_le (t : ExceptionalTime) (j K : ℕ)
    {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) :
    let C := tailRadix t j
    let Cr : ℝ := C.val
    let A0 := radixShellConstant t j w
    let A1 := radixShellConstant t (j + 1) w
    let A2 := radixShellConstant t (j + 2) w
    let Bconst : ℝ :=
      ‖((C.val : ℂ) + 1) * A0 - (((C.val : ℂ) ^ 2 + 2 * (C.val : ℂ) + 3) * A1) +
        2 * ((C.val : ℂ) ^ 2 + 1) * A2‖ +
      (Cr + 1 + (Cr ^ 2 + 2 * Cr + 3) * Cr + 2 * (Cr ^ 2 + 1) * Cr ^ 3) *
        (Cr * ‖w * (w + 1)‖ / (4 * (w.re + 1) * (Cr - 1)))
    ‖triadicRefinementCutoff t j (C.val ^ (4 * K)) w - riemannZeta w * triadicMultiplier C w‖ ≤
      Bconst * ((C.val ^ (4 * K) : ℕ) : ℝ) ^ (-w.re) := by
  dsimp only
  let C := tailRadix t j
  let c : ℂ := C.val
  let Cr : ℝ := C.val
  let q := heat w C
  have hC1 : 1 < C.val := radix_gt_one t j
  have hCr1 : (1 : ℝ) < Cr := by dsimp only [Cr]; exact_mod_cast hC1
  have hCr0 : (0 : ℝ) < Cr := by positivity
  have hq0_lt : ‖q‖ < 1 := heat_contraction C hC1 w hw
  have hq1_lt : ‖heat w (tailRadix t (j + 1))‖ < 1 := heat_contraction _ (radix_gt_one t (j + 1)) w hw
  have hq2_lt : ‖heat w (tailRadix t (j + 2))‖ < 1 := heat_contraction _ (radix_gt_one t (j + 2)) w hw
  have hq0_ne1 : q ≠ 1 := fun he => hq0_lt.ne (by rw [he, norm_one])
  have hq1_ne1 : heat w (tailRadix t (j + 1)) ≠ 1 := fun he => hq1_lt.ne (by rw [he, norm_one])
  have hq2_ne1 : heat w (tailRadix t (j + 2)) ≠ 1 := fun he => hq2_lt.ne (by rw [he, norm_one])
  have hb0 := norm_renormalizedCutoff_radix_pow_sub_le t j (4 * K) (by linarith) hw1 hq0_ne1
  have hb1 := norm_renormalizedCutoff_radix_pow_sub_le t (j + 1) (2 * K) (by linarith) hw1 hq1_ne1
  have hb2 := norm_renormalizedCutoff_radix_pow_sub_le t (j + 2) K (by linarith) hw1 hq2_ne1
  dsimp only at hb0 hb1 hb2
  -- Align radices and heat powers to `C^(4*K)` and `q^(4*K)`.
  have hrad1 : (tailRadix t (j + 1)).val ^ (2 * K) = C.val ^ (4 * K) := by
    dsimp only [C]; rw [tailRadix_succ_sq, PNat.pow_coe, ← pow_mul, ← mul_assoc]; rfl
  have hrad2 : (tailRadix t (j + 2)).val ^ K = C.val ^ (4 * K) := by
    dsimp only [C]; rw [tailRadix_add_two_pow_four, PNat.pow_coe, ← pow_mul]
  have hheat1 : (heat w (tailRadix t (j + 1))) ^ (2 * K) = q ^ (4 * K) := by
    dsimp only [q, C]; rw [heat_tailRadix_succ, ← pow_mul, ← mul_assoc]; rfl
  have hheat2 : (heat w (tailRadix t (j + 2))) ^ K = q ^ (4 * K) := by
    dsimp only [q, C]; rw [heat_tailRadix_add_two, ← pow_mul]
  rw [hrad1, hheat1] at hb1
  rw [hrad2, hheat2] at hb2
  -- Verify that the limit combination equals `riemannZeta w * triadicMultiplier C w`.
  have hq2_lt' : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq0_lt (by norm_num)
  have hq4_lt' : ‖q ^ 4‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq0_lt (by norm_num)
  have hn1 : (1 : ℂ) - q ≠ 0 := sub_ne_zero.mpr hq0_ne1.symm
  have hn2 : (1 : ℂ) - q ^ 2 ≠ 0 := sub_ne_zero.mpr fun he => hq2_lt'.ne (by rw [← he, norm_one])
  have hn4 : (1 : ℂ) - q ^ 4 ≠ 0 := sub_ne_zero.mpr fun he => hq4_lt'.ne (by rw [← he, norm_one])
  have hp1 : (1 : ℂ) + q ≠ 0 := fun he =>
    hq0_lt.ne (by rw [show q = -1 by linear_combination he, norm_neg, norm_one])
  have hp2 : (1 : ℂ) + q ^ 2 ≠ 0 := fun he =>
    hq2_lt'.ne (by rw [show q ^ 2 = -1 by linear_combination he, norm_neg, norm_one])
  let Z0 := 2 * q * riemannZeta w / (1 - q)
  let Z1 := 2 * heat w (tailRadix t (j + 1)) * riemannZeta w / (1 - heat w (tailRadix t (j + 1)))
  let Z2 := 2 * heat w (tailRadix t (j + 2)) * riemannZeta w / (1 - heat w (tailRadix t (j + 2)))
  have hZ_comb : (c + 1) * Z0 - (c ^ 2 + 2 * c + 3) * Z1 + 2 * (c ^ 2 + 1) * Z2 =
      riemannZeta w * triadicMultiplier C w := by
    dsimp only [Z0, Z1, Z2]
    rw [heat_tailRadix_succ, heat_tailRadix_add_two]
    unfold triadicMultiplier
    dsimp only [c, q, C] at hn1 hn2 hn4 hp1 hp2 ⊢
    field_simp [hn1, hn2, hn4, hp1, hp2]; ring
  -- Cancel the `K * q^(4*K)` spike identically!
  let R0 := renormalizedCutoff t j (C.val ^ (4 * K)) w - Z0 -
    (((4 * K : ℕ) : ℂ) + radixShellConstant t j w) * q ^ (4 * K)
  let R1 := renormalizedCutoff t (j + 1) (C.val ^ (4 * K)) w - Z1 -
    (((2 * K : ℕ) : ℂ) + radixShellConstant t (j + 1) w) * q ^ (4 * K)
  let R2 := renormalizedCutoff t (j + 2) (C.val ^ (4 * K)) w - Z2 -
    ((K : ℂ) + radixShellConstant t (j + 2) w) * q ^ (4 * K)
  let Atri := (c + 1) * radixShellConstant t j w -
    ((c ^ 2 + 2 * c + 3) * radixShellConstant t (j + 1) w) +
    2 * (c ^ 2 + 1) * radixShellConstant t (j + 2) w
  have hident : triadicRefinementCutoff t j (C.val ^ (4 * K)) w -
      riemannZeta w * triadicMultiplier C w =
      Atri * q ^ (4 * K) +
        ((c + 1) * R0 - (c ^ 2 + 2 * c + 3) * R1 + 2 * (c ^ 2 + 1) * R2) := by
    have htri := triadicRefinementCutoff_eq_renormalized t j (C.val ^ (4 * K)) w
    dsimp only at htri
    rw [htri, ← hZ_comb]
    dsimp only [R0, R1, R2, Atri, c, C, q]
    push_cast
    ring
  -- Bound `‖R0‖, ‖R1‖, ‖R2‖` by `X^(-w.re)`.
  let Xr : ℝ := ((C.val ^ (4 * K) : ℕ) : ℝ)
  have hXr_pow : Xr ^ (-w.re) = Cr ^ (-(4 * (K : ℝ)) * w.re) := by
    dsimp only [Xr, Cr]; rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hCr0.le]
    push_cast; congr 1; ring
  have hq4K : ‖q ^ (4 * K)‖ = Xr ^ (-w.re) := by
    rw [hXr_pow]; dsimp only [q, Cr]; rw [norm_heat_pow]; push_cast; rfl
  let Ebase : ℝ := Cr * ‖w * (w + 1)‖ / (4 * (w.re + 1) * (Cr - 1))
  have hEbase0 : 0 ≤ Ebase := by
    dsimp only [Ebase]
    exact div_nonneg (by positivity) (mul_nonneg (by linarith) (sub_pos.mpr hCr1).le)
  have hR0 : ‖R0‖ ≤ Ebase * Xr ^ (-w.re) := by
    refine hb0.trans ?_
    rw [hXr_pow]
    dsimp only [Ebase, Cr, C] at hEbase0 ⊢
    refine mul_le_mul_of_nonneg_left ?_ hEbase0
    apply Real.rpow_le_rpow_of_exponent_le hCr1.le
    push_cast; nlinarith
  have hR1 : ‖R1‖ ≤ Cr * Ebase * Xr ^ (-w.re) := by
    refine hb1.trans ?_
    have hrad1_val : ((tailRadix t (j + 1)).val : ℝ) = Cr ^ 2 := by
      dsimp only [Cr, C]; rw [tailRadix_succ_sq, PNat.pow_coe, Nat.cast_pow]
    rw [hrad1_val, hXr_pow]
    have hcoeff : Cr ^ 2 * ‖w * (w + 1)‖ / (4 * (w.re + 1) * (Cr ^ 2 - 1)) ≤ Cr * Ebase := by
      dsimp only [Ebase]
      rw [show Cr * (Cr * ‖w * (w + 1)‖ / (4 * (w.re + 1) * (Cr - 1))) =
        Cr ^ 2 * ‖w * (w + 1)‖ / (4 * (w.re + 1) * (Cr - 1)) by ring]
      exact div_le_div_of_nonneg_left (by positivity)
        (mul_pos (by linarith) (sub_pos.mpr hCr1))
        (mul_le_mul_of_nonneg_left (by nlinarith) (by linarith))
    have hexp_le : (Cr ^ 2) ^ (-((2 * K : ℕ) : ℝ) * (w.re + 1)) ≤ Cr ^ (-(4 * (K : ℝ)) * w.re) := by
      rw [← Real.rpow_natCast Cr 2, ← Real.rpow_mul hCr0.le]
      apply Real.rpow_le_rpow_of_exponent_le hCr1.le
      push_cast; nlinarith
    exact mul_le_mul hcoeff hexp_le (by positivity) (mul_nonneg hCr0.le hEbase0)
  have hR2 : ‖R2‖ ≤ Cr ^ 3 * Ebase * Xr ^ (-w.re) := by
    refine hb2.trans ?_
    have hrad2_val : ((tailRadix t (j + 2)).val : ℝ) = Cr ^ 4 := by
      dsimp only [Cr, C]; rw [tailRadix_add_two_pow_four, PNat.pow_coe, Nat.cast_pow]
    rw [hrad2_val, hXr_pow]
    have hcoeff : Cr ^ 4 * ‖w * (w + 1)‖ / (4 * (w.re + 1) * (Cr ^ 4 - 1)) ≤ Cr ^ 3 * Ebase := by
      dsimp only [Ebase]
      rw [show Cr ^ 3 * (Cr * ‖w * (w + 1)‖ / (4 * (w.re + 1) * (Cr - 1))) =
        Cr ^ 4 * ‖w * (w + 1)‖ / (4 * (w.re + 1) * (Cr - 1)) by ring]
      exact div_le_div_of_nonneg_left (by positivity)
        (mul_pos (by linarith) (sub_pos.mpr hCr1))
        (mul_le_mul_of_nonneg_left
          (sub_le_sub_right (le_self_pow₀ hCr1.le (by norm_num)) 1) (by linarith))
    have hexp_le : (Cr ^ 4) ^ (-(K : ℝ) * (w.re + 1)) ≤ Cr ^ (-(4 * (K : ℝ)) * w.re) := by
      rw [← Real.rpow_natCast Cr 4, ← Real.rpow_mul hCr0.le]
      apply Real.rpow_le_rpow_of_exponent_le hCr1.le
      push_cast; nlinarith
    exact mul_le_mul hcoeff hexp_le (by positivity) (by positivity)
  -- Norm of the real integer weights.
  have hnc1 : ‖c + 1‖ = Cr + 1 := by
    have : c + 1 = ((Cr + 1 : ℝ) : ℂ) := by simp [c, Cr]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hnc2 : ‖c ^ 2 + 2 * c + 3‖ = Cr ^ 2 + 2 * Cr + 3 := by
    have : c ^ 2 + 2 * c + 3 = ((Cr ^ 2 + 2 * Cr + 3 : ℝ) : ℂ) := by simp [c, Cr]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hnc3 : ‖2 * (c ^ 2 + 1)‖ = 2 * (Cr ^ 2 + 1) := by
    have : 2 * (c ^ 2 + 1) = ((2 * (Cr ^ 2 + 1) : ℝ) : ℂ) := by simp [c, Cr]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hident]
  refine ((norm_add_le _ _).trans (add_le_add le_rfl
    ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)))).trans ?_
  rw [norm_mul Atri, hq4K, norm_mul (c + 1), hnc1, norm_mul (c ^ 2 + 2 * c + 3), hnc2,
    norm_mul (2 * (c ^ 2 + 1)), hnc3]
  have hr0 := mul_le_mul_of_nonneg_left hR0 (by positivity : 0 ≤ Cr + 1)
  have hr1 := mul_le_mul_of_nonneg_left hR1 (by positivity : 0 ≤ Cr ^ 2 + 2 * Cr + 3)
  have hr2 := mul_le_mul_of_nonneg_left hR2 (by positivity : 0 ≤ 2 * (Cr ^ 2 + 1))
  dsimp only [Atri, c, Cr, Ebase, Xr] at hr0 hr1 hr2 ⊢
  linarith

#print axioms tailRadix_succ_sq
#print axioms dyadicRefinementContrast_eq_renormalized
#print axioms tendsto_dyadicRefinementContrast_zero_spike
#print axioms triadicRefinementCutoff_eq_renormalized
#print axioms triadicRefinementCutoff_limit
#print axioms triadicMultiplier_ne_zero
#print axioms triadicRefinementCutoff_zero_iff
#print axioms norm_triadicRefinementCutoff_radix_pow_sub_le

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation
