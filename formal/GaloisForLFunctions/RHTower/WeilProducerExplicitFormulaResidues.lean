import GaloisForLFunctions.RHTower.WeilProducerPerronExplicitFormula
import GaloisForLFunctions.RHTower.TrigammaVertical

/-!
# The weighted explicit formula of a Weil-positive system in residue form

Let `lam` be full-cone Weil-positive and `A_lam = U − Φ_lam` on `Re z > ½`, the continuation of
`Σ lam(n) n^{−z}` (`producerA`).  For `Re z > ½`, `z ≠ 1`, `L ≥ 0`
(`tsum_lamC_mul_max_eq_residue`):

`Σ_n lam(n) n^{−z} (L − log n)⁺ = L·A_lam(z) + A_lam'(z) + E_L(z)`,

`E_L(z) = e^{(1−z)L}/(1−z)² + e^{−zL}/z² − Σ_k e^{−(z+2k)L}/(z+2k)² − ∫ e^{βL}/β² dμ_lam(r)`,
`β = ir + ½ − z`.

The first two terms are the residue at the double pole `s = 0` of `A_lam(z + s)e^{sL}/s²`; `E_L`
collects the residues at the poles `1 − z`, `−z`, the trivial points `−z − 2k` and the points
`ir + ½ − z` of the boundary measure.  The derivative is identified in `hasDerivAt_producerA`
from the trigamma series and the derivative of the Herglotz function.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz PerronPole

/-- The continuation `A_lam = U − Φ_lam` of `Σ lam(n) n^{−z}` to `Re z > ½`. -/
def producerA {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (z : ℂ) : ℂ :=
  zetaArchimedeanDatum z + 1 / (z - 1) - weilContinuation hW z

/-- The derivative of `A_lam`, as a residue sum. -/
def producerDA {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (z : ℂ) : ℂ :=
  (∑' k : ℕ, 1 / (z + 2 * k) ^ 2) - 1 / z ^ 2 - 1 / (z - 1) ^ 2 +
    ∫ r, 1 / (z - 1 / 2 - I * r) ^ 2 ∂boundaryMeasure hW

/-- The residues of `A_lam(z + s)e^{sL}/s²` away from `s = 0`. -/
def producerE {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (L : ℝ) (z : ℂ) : ℂ :=
  cexp ((1 - z) * L) / (1 - z) ^ 2 + cexp (-z * L) / z ^ 2 -
    (∑' k : ℕ, cexp ((-z - 2 * k) * L) / (-z - 2 * k) ^ 2) -
    ∫ r, cexp ((I * r - (z - 1 / 2)) * L) / (I * r - (z - 1 / 2)) ^ 2 ∂boundaryMeasure hW

theorem summable_inv_add_nat_sq {v : ℂ} (hv : 0 < v.re) :
    Summable fun n : ℕ => ((v + n) ^ 2)⁻¹ := by
  set a : ℝ := min v.re 1 with ha
  have ha0 : 0 < a := lt_min hv one_pos
  have hs : Summable fun n : ℕ => (a ^ 2)⁻¹ * (1 / |(n : ℝ) + 1| ^ (2 : ℝ)) :=
    ((Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)).mul_left _
  refine Summable.of_norm_bounded hs fun n => ?_
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlow : a * ((n : ℝ) + 1) ≤ ‖v + n‖ := by
    have h := Complex.re_le_norm (v + n)
    have hre : (v + n).re = v.re + n := by simp
    rw [hre] at h
    have h1 : a ≤ v.re := min_le_left _ _
    have h2 : a ≤ 1 := min_le_right _ _
    nlinarith
  rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1), Real.rpow_two, norm_inv, norm_pow]
  rw [one_div, ← mul_inv, ← mul_pow]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hlow 2)

theorem deriv_digamma_eq_tsum {v : ℂ} (hv : 0 < v.re) :
    deriv Complex.digamma v = ∑' n : ℕ, ((v + n) ^ 2)⁻¹ :=
  tendsto_nhds_unique (deriv_digamma_partialSum_tendsto hv)
    (summable_inv_add_nat_sq hv).hasSum.tendsto_sum_nat

/-- **The derivative of `A_lam`.** -/
theorem hasDerivAt_producerA {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {z : ℂ}
    (hz : 1 / 2 < z.re) (hz1 : z ≠ 1) :
    HasDerivAt (producerA hW) (producerDA hW z) z := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz; linarith
  have hz10 : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hv : 0 < (z / 2).re := by
    have : (z / 2).re = z.re / 2 := by simp
    rw [this]; linarith
  -- digamma part
  have hpsi : HasDerivAt (fun x : ℂ => Complex.digamma (x / 2))
      (deriv Complex.digamma (z / 2) * (1 / 2)) z :=
    (differentiableAt_digamma_of_re_pos hv).hasDerivAt.comp z
      ((hasDerivAt_id z).div_const 2 |>.congr_deriv (by simp))
  have hinv : HasDerivAt (fun x : ℂ => 1 / x) (-(z ^ 2)⁻¹) z := by
    simpa only [one_div] using hasDerivAt_inv hz0
  have hU : HasDerivAt zetaArchimedeanDatum
      (deriv Complex.digamma (z / 2) * (1 / 2) / 2 + -(z ^ 2)⁻¹) z := by
    have h1 := (hpsi.div_const 2).sub_const ((Real.log Real.pi : ℂ) / 2)
    exact (h1.add hinv).congr_of_eventuallyEq
      (Eventually.of_forall fun x => by simp [zetaArchimedeanDatum])
  have hpole : HasDerivAt (fun x : ℂ => 1 / (x - 1)) (-((z - 1) ^ 2)⁻¹) z := by
    have h := (hasDerivAt_inv hz10).comp z ((hasDerivAt_id z).sub_const 1)
    simpa only [one_div, Function.comp_def, id, mul_one] using h
  have hw0 : 0 < (z - 1 / 2).re := by simp; linarith
  have hH : HasDerivAt (weilContinuation hW)
      (∫ r, -(1 / (z - 1 / 2 - I * r) ^ 2) ∂boundaryMeasure hW) z := by
    have h := (hasDerivAt_herglotzFunction hW hw0).comp_sub_const z (1 / 2)
    have h2 := h.add_const (weilFunction lam 2 - herglotzFunction hW (2 - 1 / 2))
    exact h2.congr_of_eventuallyEq (Eventually.of_forall fun x => by simp [weilContinuation])
  have hA := (hU.add hpole).sub hH
  refine hA.congr_of_eventuallyEq (Eventually.of_forall fun x => by simp [producerA]) |>.congr_deriv ?_
  rw [producerDA, integral_neg, deriv_digamma_eq_tsum hv]
  have hsum : ∑' k : ℕ, 1 / (z + 2 * k) ^ 2 = (∑' n : ℕ, ((z / 2 + n) ^ 2)⁻¹) / 4 := by
    rw [← tsum_div_const]
    refine tsum_congr fun k => ?_
    have hk : z / 2 + k ≠ 0 := fun h => by
      have := congrArg Complex.re h
      simp at this
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have hk2 : z + 2 * k ≠ 0 := fun h => hk (by linear_combination h / 2)
    field_simp
    ring
  rw [hsum]
  ring

theorem poleWeight_eq {b : ℂ} (hb : b ≠ 0) (L : ℝ) :
    poleWeight L b = cexp (b * L) / b ^ 2 - 1 / b ^ 2 - L / b := by
  unfold poleWeight; field_simp

theorem norm_inv_sub_I_mul_sq_eq {w : ℂ} (hw : 0 < w.re) (r : ℝ) :
    ‖1 / (w - I * r) ^ 2‖ = (herglotzKernel w r).re / w.re := by
  rw [re_herglotzKernel hw, norm_div, norm_one, norm_pow, norm_div, norm_one, div_pow]
  field_simp

theorem integrable_inv_sub_I_mul_sq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {w : ℂ}
    (hw : 0 < w.re) : Integrable (fun r : ℝ => 1 / (w - I * r) ^ 2) (boundaryMeasure hW) := by
  have hc : Continuous fun r : ℝ => 1 / (w - I * r) ^ 2 :=
    continuous_const.div (by fun_prop) fun r => pow_ne_zero 2 (sub_I_mul_ne_zero hw r)
  refine Integrable.mono' ((integrable_herglotzKernel hW hw).re.div_const w.re)
    hc.aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  rw [norm_inv_sub_I_mul_sq_eq hw]
  exact le_rfl

theorem norm_cexp_mul_le_one {b : ℂ} (hb : b.re ≤ 0) {L : ℝ} (hL : 0 ≤ L) :
    ‖cexp (b * L)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have : (b * (L : ℂ)).re = b.re * L := by simp
  rw [this]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hb hL)

theorem integrable_cexp_div_sq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {w : ℂ}
    (hw : 0 < w.re) {L : ℝ} (hL : 0 ≤ L) :
    Integrable (fun r : ℝ => cexp ((I * r - w) * L) / (I * r - w) ^ 2) (boundaryMeasure hW) := by
  have hne : ∀ r : ℝ, (I * (r : ℂ) - w) ^ 2 ≠ 0 := fun r => by
    rw [show (I * (r : ℂ) - w) ^ 2 = (w - I * r) ^ 2 by ring]
    exact pow_ne_zero 2 (sub_I_mul_ne_zero hw r)
  have hc : Continuous fun r : ℝ => cexp ((I * r - w) * L) / (I * r - w) ^ 2 :=
    Continuous.div (by fun_prop) (by fun_prop) hne
  refine Integrable.mono' (integrable_inv_sub_I_mul_sq hW hw).norm hc.aestronglyMeasurable
    (Eventually.of_forall fun r => ?_)
  rw [norm_div, show (I * (r : ℂ) - w) ^ 2 = (w - I * r) ^ 2 by ring, norm_div (1 : ℂ), norm_one]
  have h1 : ‖cexp ((I * r - w) * L)‖ ≤ 1 :=
    norm_cexp_mul_le_one (by simp; linarith) hL
  exact div_le_div_of_nonneg_right h1 (norm_nonneg _)

/-- **The weighted explicit formula in residue form.**  For `Re z > ½`, `z ≠ 1`, `L ≥ 0`:
`Σ_n lam(n) n^{−z}(L − log n)⁺ = L·A_lam(z) + A_lam'(z) + E_L(z)`. -/
theorem tsum_lamC_mul_max_eq_residue {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {z : ℂ}
    (hz : 1 / 2 < z.re) (hz1 : z ≠ 1) {L : ℝ} (hL : 0 ≤ L) :
    ∑' n : ℕ, LSeries.term (lamC lam) z n * ((max (L - Real.log n) 0 : ℝ) : ℂ) =
      L * producerA hW z + producerDA hW z + producerE hW L z := by
  rw [tsum_lamC_mul_max_eq hW hz hz1 hL]
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz; linarith
  have hv : 0 < (z / 2).re := by
    have : (z / 2).re = z.re / 2 := by simp
    rw [this]; linarith
  set w : ℂ := z - 1 / 2 with hwdef
  have hw : 0 < w.re := by rw [hwdef]; simp; linarith
  -- the trivial points
  have hbk : ∀ k : ℕ, (-z - 2 * k : ℂ) ≠ 0 := fun k h => by
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hzk : ∀ k : ℕ, z / 2 + k ≠ 0 := fun k h => by
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hsg := summable_gaussDigammaSeriesTerm hv
  have hsa : Summable fun k : ℕ => 1 / (z + 2 * k) ^ 2 := by
    refine ((summable_inv_add_nat_sq hv).div_const 4).congr fun k => ?_
    have hk2 : z + 2 * k ≠ 0 := fun h => hzk k (by linear_combination h / 2)
    field_simp
    ring
  have hse : Summable fun k : ℕ => cexp ((-z - 2 * k) * L) / (-z - 2 * k) ^ 2 := by
    refine Summable.of_norm_bounded hsa.norm fun k => ?_
    rw [norm_div, show (-z - 2 * (k : ℂ)) ^ 2 = (z + 2 * k) ^ 2 by ring, norm_div (1 : ℂ),
      norm_one]
    have h1 : ‖cexp ((-z - 2 * k) * L)‖ ≤ 1 := norm_cexp_mul_le_one (by
      simp
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith) hL
    exact div_le_div_of_nonneg_right h1 (norm_nonneg _)
  have hseries : ∑' k : ℕ, ((L : ℂ) / ((k : ℂ) + 1) - 2 * poleWeight L (-z - 2 * k)) =
      L * ∑' k : ℕ, gaussDigammaSeriesTerm (z / 2) k + 2 * ∑' k : ℕ, 1 / (z + 2 * k) ^ 2 -
        2 * ∑' k : ℕ, cexp ((-z - 2 * k) * L) / (-z - 2 * k) ^ 2 := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left, ← (hsg.mul_left _).tsum_add
      (hsa.mul_left _), ← ((hsg.mul_left _).add (hsa.mul_left _)).tsum_sub (hse.mul_left _)]
    refine tsum_congr fun k => ?_
    rw [poleWeight_eq (hbk k), gaussDigammaSeriesTerm]
    have hk2 : z + 2 * k ≠ 0 := fun h => hzk k (by linear_combination h / 2)
    have hb := hbk k
    have hk3 := hzk k
    have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have e1 : (-z - 2 * (k : ℂ)) ^ 2 = (z + 2 * k) ^ 2 := by ring
    have e2 : (L : ℂ) / (-z - 2 * k) = -(L / (z + 2 * k)) := by
      rw [show (-z - 2 * (k : ℂ)) = -(z + 2 * k) by ring, div_neg]
    have e3 : 1 / (z / 2 + k) = 2 / (z + 2 * k) := by field_simp
    rw [e1, e2, e3]
    ring
  -- the boundary measure
  have hker := integrable_herglotzKernel hW hw
  have hsq := integrable_inv_sub_I_mul_sq hW hw
  have hex := integrable_cexp_div_sq hW hw hL
  have hint : ∫ r, (poleWeight L (I * r - (z - 1 / 2)) - I * r / (1 + (r : ℂ) ^ 2) * L)
        ∂boundaryMeasure hW =
      L * herglotzFunction hW w - (∫ r, 1 / (w - I * r) ^ 2 ∂boundaryMeasure hW) +
        ∫ r, cexp ((I * r - w) * L) / (I * r - w) ^ 2 ∂boundaryMeasure hW := by
    have hpt : ∀ r : ℝ, poleWeight L (I * r - (z - 1 / 2)) - I * r / (1 + (r : ℂ) ^ 2) * L =
        L * herglotzKernel w r - 1 / (w - I * r) ^ 2 +
          cexp ((I * r - w) * L) / (I * r - w) ^ 2 := by
      intro r
      have hβ : (I * (r : ℂ) - w) ≠ 0 := fun h =>
        sub_I_mul_ne_zero hw r (by linear_combination -h)
      have hβ' : w - I * (r : ℂ) ≠ 0 := sub_I_mul_ne_zero hw r
      rw [← hwdef, poleWeight_eq hβ, herglotzKernel]
      have h1 := one_add_sq_ne_zero r
      field_simp
      ring
    have hA : Integrable (fun r : ℝ => L * herglotzKernel w r - 1 / (w - I * r) ^ 2)
        (boundaryMeasure hW) := (hker.const_mul _).sub hsq
    have hB : Integrable (fun r : ℝ => (L : ℂ) * herglotzKernel w r) (boundaryMeasure hW) :=
      hker.const_mul _
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_add hA hex, integral_sub hB hsq,
      integral_const_mul]
    rfl
  rw [hseries, hint]
  have hpsi := digamma_eq_neg_euler_add_tsum_gauss hv
  have hts : ∑' k : ℕ, gaussDigammaSeriesTerm (z / 2) k =
      Complex.digamma (z / 2) + (Real.eulerMascheroniConstant : ℂ) := by
    rw [hpsi]; ring
  rw [hts, poleWeight_eq (neg_ne_zero.mpr hz0), poleWeight_eq (sub_ne_zero.mpr (Ne.symm hz1))]
  have hDA : producerDA hW z = (∑' k : ℕ, 1 / (z + 2 * k) ^ 2) - 1 / z ^ 2 - 1 / (z - 1) ^ 2 +
      ∫ r, 1 / (w - I * r) ^ 2 ∂boundaryMeasure hW := rfl
  have hE : producerE hW L z = cexp ((1 - z) * L) / (1 - z) ^ 2 + cexp (-z * L) / z ^ 2 -
      (∑' k : ℕ, cexp ((-z - 2 * k) * L) / (-z - 2 * k) ^ 2) -
      ∫ r, cexp ((I * r - w) * L) / (I * r - w) ^ 2 ∂boundaryMeasure hW := rfl
  have hA : producerA hW z = Complex.digamma (z / 2) / 2 - (Real.log Real.pi : ℂ) / 2 + 1 / z +
      1 / (z - 1) - (herglotzFunction hW w + weilConst hW) := rfl
  rw [hDA, hE, hA]
  have hz10 : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  have e4 : (-z) * (L : ℂ) = -z * L := rfl
  have e5 : (1 : ℂ) / (1 - z) ^ 2 = 1 / (z - 1) ^ 2 := by ring
  have e6 : (L : ℂ) / (1 - z) = -(L / (z - 1)) := by
    rw [show (1 : ℂ) - z = -(z - 1) by ring, div_neg]
  have e7 : (L : ℂ) / -z = -(L / z) := div_neg _
  have e8 : (1 : ℂ) / (-z) ^ 2 = 1 / z ^ 2 := by ring
  have e9 : cexp (-z * L) / (-z) ^ 2 = cexp (-z * L) / z ^ 2 := by ring
  rw [e5, e6, e7, e8, e9]
  ring

end RHTower.WeilSpectral

end
