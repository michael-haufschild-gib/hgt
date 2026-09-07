import GaloisForLFunctions.RHTower.ChiIncrementDifferenceJets
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftDisplacedDerivative
import GaloisForLFunctions.RHTower.ArchLadderRegular

/-!
# Height jets of the two-ratio product of the product AFE

Along the Levinson lines `s₁ = ½−d+it`, `s₂ = ½−d−it` and for the dual shift `w = −(1+iv)`, the
two-ratio product `F(t) = [χ(s₁+w)/χ(s₁)]·[χ(s₂+w)/χ(s₂)]` satisfies `F' = F·D` with `D` the
difference of chi-increments.  Since `‖D^{(j)}(t)‖ ≤ 10(j+1)!·A^{j+1}` with `A = 2(1+|v|)/t`, the
Leibniz rule and a strong induction give

  `‖F^{(n)}(t)‖ ≤ n!·‖F(t)‖·(11 A)^n = n!·‖F(t)‖·(22(1+|v|)/t)^n`

for `t ≥ 4`, `2|v| ≤ t`: every height derivative of the exact dual weight's archimedean carrier
gains one power of `t`.
-/

noncomputable section

namespace RHTower

open Complex GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- The two-ratio product along the Levinson lines. -/
def chiRatioProduct (d v : ℝ) (t : ℝ) : ℂ :=
  smoothAFEZetaChiShiftRatio (displacedLinePt d t) (levinsonShift v) *
    smoothAFEZetaChiShiftRatio (displacedLinePt d (-t)) (levinsonShift v)

theorem displacedLinePt_add_levinsonShift_re (d τ v : ℝ) :
    (displacedLinePt d τ + levinsonShift v).re = -1 / 2 - d := by
  simp [displacedLinePt, levinsonShift]
  ring

theorem displacedLinePt_add_levinsonShift_im (d τ v : ℝ) :
    (displacedLinePt d τ + levinsonShift v).im = τ - v := by
  simp [displacedLinePt, levinsonShift]
  ring

theorem gammaR_one_sub_shifted_ne_zero {d : ℝ} (hd : 0 < d) (τ v : ℝ) :
    Gammaℝ (1 - (displacedLinePt d τ + levinsonShift v)) ≠ 0 := by
  apply Gammaℝ_ne_zero_of_re_pos
  rw [Complex.sub_re, Complex.one_re, displacedLinePt_add_levinsonShift_re]
  linarith

theorem shifted_half_ne_neg_nat {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (τ v : ℝ) (m : ℕ) :
    (displacedLinePt d τ + levinsonShift v) / 2 ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  rw [Complex.div_ofNat_re, displacedLinePt_add_levinsonShift_re] at hre
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp at hre
    linarith
  · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith

theorem zetaChi_shifted_ne_zero {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (τ v : ℝ) :
    zetaChi (displacedLinePt d τ + levinsonShift v) ≠ 0 := by
  unfold zetaChi
  exact div_ne_zero (gammaR_one_sub_shifted_ne_zero hd τ v)
    (Gammaℝ_ne_zero_off_poles (shifted_half_ne_neg_nat hd hdq τ v))

/-- The single-ratio height derivative along the displaced line, in increment form. -/
theorem hasDerivAt_ratio_levinson {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (v τ : ℝ) :
    HasDerivAt (fun u : ℝ => smoothAFEZetaChiShiftRatio (displacedLinePt d u) (levinsonShift v))
      (I * smoothAFEZetaChiShiftRatio (displacedLinePt d τ) (levinsonShift v) *
        chiIncrement (((1 / 2 - d : ℝ)) : ℂ) (levinsonShift v) τ) τ := by
  have h := hasDerivAt_smoothAFEZetaChiShiftRatio_displaced_logDeriv hd (by linarith)
    (gammaR_one_sub_shifted_ne_zero hd τ v) (zetaChi_shifted_ne_zero hd hdq τ v)
  exact h

/-- **`F' = F·D`**: the two-ratio product is differentiable everywhere with logarithmic
derivative the chi-increment difference. -/
theorem hasDerivAt_chiRatioProduct {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (v t : ℝ) :
    HasDerivAt (chiRatioProduct d v)
      (chiRatioProduct d v t * chiIncrementDifference (1 / 2 - d) v t) t := by
  have h1 := hasDerivAt_ratio_levinson hd hdq v t
  have h2raw := hasDerivAt_ratio_levinson hd hdq v (-t)
  have h2 := h2raw.scomp t (hasDerivAt_neg t)
  have h := h1.mul h2
  have hfun : chiRatioProduct d v =
      fun x : ℝ => smoothAFEZetaChiShiftRatio (displacedLinePt d x) (levinsonShift v) *
        ((fun u : ℝ => smoothAFEZetaChiShiftRatio (displacedLinePt d u) (levinsonShift v)) ∘
          Neg.neg) x := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  unfold chiIncrementDifference
  simp only [Function.comp_apply, Complex.real_smul]
  push_cast
  ring

/-! ## The combinatorial estimate behind the Leibniz induction -/

theorem sum_range_inv_eleven_pow_le (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (1 / 11 : ℝ) ^ (n - i + 1) ≤ 1 / 10 := by
  have hreflect : ∑ i ∈ Finset.range (n + 1), (1 / 11 : ℝ) ^ (n - i + 1)
      = ∑ i ∈ Finset.range (n + 1), (1 / 11 : ℝ) ^ (i + 1) := by
    rw [← Finset.sum_range_reflect (fun i => (1 / 11 : ℝ) ^ (i + 1)) (n + 1)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < n + 1 := Finset.mem_range.mp hi
    congr 1
  rw [hreflect]
  have hgeom : ∑ i ∈ Finset.range (n + 1), (1 / 11 : ℝ) ^ (i + 1)
      = (1 / 11) * ∑ i ∈ Finset.range (n + 1), (1 / 11 : ℝ) ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hgeom, geom_sum_eq (by norm_num : (1 / 11 : ℝ) ≠ 1)]
  have hpow : (0 : ℝ) ≤ (1 / 11 : ℝ) ^ (n + 1) := by positivity
  have hpow1 : (1 / 11 : ℝ) ^ (n + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rw [show ((1 / 11 : ℝ) ^ (n + 1) - 1) / (1 / 11 - 1) = (1 - (1 / 11 : ℝ) ^ (n + 1)) * (11 / 10) by
    field_simp; ring]
  nlinarith

/-- The Leibniz-sum estimate: factorial-type bounds on the two factors give a factorial-type
bound on the product's `(n+1)`-st jet. -/
theorem leibniz_factorial_sum_le (n : ℕ) {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) (a b : ℕ → ℝ)
    (hb0 : ∀ j, 0 ≤ b j)
    (ha : ∀ i, i ≤ n → a i ≤ i.factorial * K * B ^ i)
    (hb : ∀ j, j ≤ n → b j ≤ 10 * (j + 1).factorial * (B / 11) ^ (j + 1)) :
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * a i * b (n - i)
      ≤ (n + 1).factorial * K * B ^ (n + 1) := by
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * a i * b (n - i)
        ≤ 10 * K * B ^ (n + 1) * n.factorial * (n + 1) * (1 / 11 : ℝ) ^ (n - i + 1) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hai := ha i hi'
    have hbi := hb (n - i) (Nat.sub_le n i)
    have hchoose : ((n.choose i : ℕ) : ℝ) * (i.factorial : ℝ) * ((n - i).factorial : ℝ)
        = (n.factorial : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
    have hfac : ((n - i + 1).factorial : ℝ) = ((n - i : ℕ) + 1 : ℝ) * ((n - i).factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hle : ((n - i : ℕ) + 1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (n - i : ℕ) ≤ n := Nat.sub_le n i
      have : ((n - i : ℕ) : ℝ) ≤ n := by exact_mod_cast this
      linarith
    have hpowB : B ^ i * (B / 11) ^ (n - i + 1) = B ^ (n + 1) * (1 / 11 : ℝ) ^ (n - i + 1) := by
      have hk : i + (n - i + 1) = n + 1 := by omega
      rw [div_pow, one_div_pow, ← hk, pow_add]
      ring
    have hchoose0 : (0 : ℝ) ≤ n.choose i := by positivity
    calc (n.choose i : ℝ) * a i * b (n - i)
        ≤ (n.choose i : ℝ) * (i.factorial * K * B ^ i)
          * (10 * (n - i + 1).factorial * (B / 11) ^ (n - i + 1)) := by
          have h1 : (n.choose i : ℝ) * a i * b (n - i)
              ≤ (n.choose i : ℝ) * (i.factorial * K * B ^ i) * b (n - i) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hai hchoose0) (hb0 _)
          have h2 : (n.choose i : ℝ) * (i.factorial * K * B ^ i) * b (n - i)
              ≤ (n.choose i : ℝ) * (i.factorial * K * B ^ i)
                * (10 * (n - i + 1).factorial * (B / 11) ^ (n - i + 1)) :=
            mul_le_mul_of_nonneg_left hbi (by positivity)
          exact h1.trans h2
    _ = 10 * K * (B ^ i * (B / 11) ^ (n - i + 1))
          * (((n.choose i : ℕ) : ℝ) * (i.factorial : ℝ) * ((n - i).factorial : ℝ))
          * (((n - i : ℕ) + 1 : ℝ)) := by
          rw [hfac]
          ring
    _ = 10 * K * B ^ (n + 1) * n.factorial * ((n - i : ℕ) + 1 : ℝ) * (1 / 11 : ℝ) ^ (n - i + 1) := by
          rw [hpowB, hchoose]
          ring
    _ ≤ 10 * K * B ^ (n + 1) * n.factorial * (n + 1) * (1 / 11 : ℝ) ^ (n - i + 1) := by
          gcongr
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hgeom := sum_range_inv_eleven_pow_le n
  have hC : (0 : ℝ) ≤ 10 * K * B ^ (n + 1) * n.factorial * (n + 1) := by positivity
  calc 10 * K * B ^ (n + 1) * n.factorial * (n + 1) * ∑ i ∈ Finset.range (n + 1), (1 / 11 : ℝ) ^ (n - i + 1)
      ≤ 10 * K * B ^ (n + 1) * n.factorial * (n + 1) * (1 / 10) :=
        mul_le_mul_of_nonneg_left hgeom hC
    _ = (n + 1).factorial * K * B ^ (n + 1) := by
        rw [Nat.factorial_succ]
        push_cast
        ring

/-! ## Smoothness on the height window and the jet bound -/

/-- The open height window on which all four line points stay off the real axis. -/
def levinsonWindow (v : ℝ) : Set ℝ := {t | 2 * |v| < t + 1 ∧ 3 < t}

theorem isOpen_levinsonWindow (v : ℝ) : IsOpen (levinsonWindow v) :=
  (isOpen_lt continuous_const (continuous_id.add continuous_const)).inter
    (isOpen_lt continuous_const continuous_id)

theorem mem_levinsonWindow_of {v t : ℝ} (ht : 4 ≤ t) (hv : 2 * |v| ≤ t) : t ∈ levinsonWindow v :=
  ⟨by linarith, by linarith⟩

theorem window_mem_shiftSet {v t : ℝ} (ht : t ∈ levinsonWindow v) (σ₀ : ℝ) :
    (σ₀ : ℂ) + (t : ℂ) * I ∈ shiftSet (levinsonShift v) ∧
      (σ₀ : ℂ) + ((-t : ℝ) : ℂ) * I ∈ shiftSet (levinsonShift v) := by
  obtain ⟨h1, h2⟩ := ht
  have hv0 : 0 ≤ |v| := abs_nonneg v
  have hsub : ∀ τ : ℝ, ((σ₀ : ℂ) + (τ : ℂ) * I + levinsonShift v).im = τ - v := by
    intro τ
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add, add_zero, levinsonShift_im]
    ring
  have hbase : ∀ τ : ℝ, ((σ₀ : ℂ) + (τ : ℂ) * I).im = τ := by
    intro τ
    simp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · show 1 < |((σ₀ : ℂ) + (t : ℂ) * I).im|
    rw [hbase]; linarith [le_abs_self t]
  · show 1 < |((σ₀ : ℂ) + (t : ℂ) * I + levinsonShift v).im|
    rw [hsub]
    have := abs_sub_abs_le_abs_sub t v
    rw [abs_of_pos (by linarith : (0 : ℝ) < t)] at this
    linarith
  · show 1 < |((σ₀ : ℂ) + ((-t : ℝ) : ℂ) * I).im|
    rw [hbase, abs_neg]; linarith [le_abs_self t]
  · show 1 < |((σ₀ : ℂ) + ((-t : ℝ) : ℂ) * I + levinsonShift v).im|
    rw [hsub]
    have := abs_sub_abs_le_abs_sub (-t) v
    rw [abs_neg, abs_of_pos (by linarith : (0 : ℝ) < t)] at this
    linarith

theorem contDiffOn_chiIncrementDifference (σ₀ v : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (chiIncrementDifference σ₀ v) (levinsonWindow v) := by
  intro t ht
  obtain ⟨h1, h2⟩ := window_mem_shiftSet ht σ₀
  have hA : ContDiffAt ℝ n (chiIncrement (σ₀ : ℂ) (levinsonShift v)) t :=
    contDiffAt_chiIncrement h1 n
  have hA' : ContDiffAt ℝ n (chiIncrement (σ₀ : ℂ) (levinsonShift v)) (-t) :=
    contDiffAt_chiIncrement (t := -t) h2 n
  have hB : ContDiffAt ℝ n (fun s : ℝ => chiIncrement (σ₀ : ℂ) (levinsonShift v) (-s)) t :=
    hA'.comp t contDiffAt_id.neg
  exact ((contDiffAt_const.mul hA).sub (contDiffAt_const.mul hB)).contDiffWithinAt

theorem analyticAt_displacedLine (d : ℝ) (u : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => displacedLinePt d s) u := by
  show AnalyticAt ℝ (fun s : ℝ => ((1 / 2 - d : ℝ) : ℂ) + (s : ℂ) * I) u
  exact analyticAt_const.add ((Complex.ofRealCLM.analyticAt u).mul analyticAt_const)

theorem analyticAt_ratio_levinson {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (v u : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => smoothAFEZetaChiShiftRatio (displacedLinePt d s) (levinsonShift v))
      u := by
  have hline := analyticAt_displacedLine d u
  have hnum : AnalyticAt ℝ (fun s : ℝ => zetaChi (displacedLinePt d s + levinsonShift v)) u := by
    have hχ : AnalyticAt ℂ zetaChi (displacedLinePt d u + levinsonShift v) :=
      zetaChi_analyticAt (gammaR_one_sub_shifted_ne_zero hd u v)
    exact AnalyticAt.comp (g := zetaChi) (f := fun s : ℝ => displacedLinePt d s + levinsonShift v)
      hχ.restrictScalars (hline.add analyticAt_const)
  have hden : AnalyticAt ℝ (fun s : ℝ => zetaChi (displacedLinePt d s)) u := by
    have hG : Gammaℝ (1 - displacedLinePt d u) ≠ 0 := by
      apply Gammaℝ_ne_zero_of_re_pos
      rw [Complex.sub_re, Complex.one_re, displacedLinePt_re]
      linarith
    exact AnalyticAt.comp (g := zetaChi) (f := fun s : ℝ => displacedLinePt d s)
      (zetaChi_analyticAt hG).restrictScalars hline
  have hden0 : zetaChi (displacedLinePt d u) ≠ 0 :=
    zetaChi_ne_zero_of_mem_openStrip (displacedLinePt_mem_openStrip hd (by linarith) u).1
      (displacedLinePt_mem_openStrip hd (by linarith) u).2
  exact hnum.div hden hden0

theorem contDiff_chiRatioProduct {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (v : ℝ) (n : ℕ) :
    ContDiff ℝ n (chiRatioProduct d v) := by
  refine contDiff_iff_contDiffAt.mpr fun t => ?_
  have h1 := analyticAt_ratio_levinson hd hdq v t
  have h2 := analyticAt_ratio_levinson hd hdq v (-t)
  have h2' : AnalyticAt ℝ (fun s : ℝ =>
      smoothAFEZetaChiShiftRatio (displacedLinePt d (-s)) (levinsonShift v)) t :=
    AnalyticAt.comp (g := fun s : ℝ => smoothAFEZetaChiShiftRatio (displacedLinePt d s)
      (levinsonShift v)) (f := fun s : ℝ => -s) h2 analyticAt_id.neg
  exact (h1.mul h2').contDiffAt

/-- **All-order height jets of the two-ratio product**: for `0 < d ≤ 1/4`, `t ≥ 4`, `2|v| ≤ t`,
`‖F^{(n)}(t)‖ ≤ n!·‖F(t)‖·(22(1+|v|)/t)^n`. -/
theorem norm_iteratedDeriv_chiRatioProduct_le {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) {v t : ℝ}
    (ht : 4 ≤ t) (hv : 2 * |v| ≤ t) (n : ℕ) :
    ‖iteratedDeriv n (chiRatioProduct d v) t‖
      ≤ n.factorial * ‖chiRatioProduct d v t‖ * (22 * (1 + |v|) / t) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  cases n with
  | zero => simp
  | succ n =>
    have ht0 : (0 : ℝ) < t := by linarith
    have hderiv : deriv (chiRatioProduct d v) =
        fun s => chiRatioProduct d v s * chiIncrementDifference (1 / 2 - d) v s :=
      funext fun s => (hasDerivAt_chiRatioProduct hd hdq v s).deriv
    rw [iteratedDeriv_succ', hderiv]
    have hwin := isOpen_levinsonWindow v
    have htw : t ∈ levinsonWindow v := mem_levinsonWindow_of ht hv
    have hFc : ContDiffOn ℝ n (chiRatioProduct d v) (levinsonWindow v) :=
      (contDiff_chiRatioProduct hd hdq v n).contDiffOn
    have hDc : ContDiffOn ℝ n (chiIncrementDifference (1 / 2 - d) v) (levinsonWindow v) :=
      contDiffOn_chiIncrementDifference (1 / 2 - d) v n
    have hleib := norm_iteratedFDerivWithin_mul_le hFc hDc hwin.uniqueDiffOn htw
      (le_refl ((n : ℕ∞) : WithTop ℕ∞))
    have hconv : ∀ (k : ℕ) (f : ℝ → ℂ),
        iteratedFDerivWithin ℝ k f (levinsonWindow v) t = iteratedFDeriv ℝ k f t :=
      fun k f => iteratedFDerivWithin_of_isOpen k hwin htw
    simp only [hconv, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hleib
    refine hleib.trans ?_
    have hDb : ∀ j, j ≤ n → ‖iteratedDeriv j (chiIncrementDifference (1 / 2 - d) v) t‖
        ≤ 10 * (j + 1).factorial * ((22 * (1 + |v|) / t) / 11) ^ (j + 1) := by
      intro j _
      refine (norm_iteratedDeriv_chiIncrementDifference_le (by linarith) (by linarith) ht hv j).trans ?_
      rw [show 22 * (1 + |v|) / t / 11 = 2 * (1 + |v|) / t by ring, div_pow, mul_pow]
      have h1v : (1 + |v|) ≤ (1 + |v|) ^ (j + 1) :=
        le_self_pow₀ (by linarith [abs_nonneg v]) (by omega)
      have hrhs : 10 * ((j + 1).factorial : ℝ) * (2 ^ (j + 1) * (1 + |v|) ^ (j + 1) / t ^ (j + 1))
          = (10 * (j + 1).factorial * 2 ^ (j + 1) * (1 + |v|) ^ (j + 1)) / t ^ (j + 1) := by ring
      rw [hrhs]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1v (by positivity))
        (by positivity)
    have hFb : ∀ i, i ≤ n → ‖iteratedDeriv i (chiRatioProduct d v) t‖
        ≤ i.factorial * ‖chiRatioProduct d v t‖ * (22 * (1 + |v|) / t) ^ i :=
      fun i hi => ih i (Nat.lt_succ_of_le hi)
    exact leibniz_factorial_sum_le n (norm_nonneg _) (by positivity)
      (fun i => ‖iteratedDeriv i (chiRatioProduct d v) t‖)
      (fun j => ‖iteratedDeriv j (chiIncrementDifference (1 / 2 - d) v) t‖)
      (fun j => norm_nonneg _) hFb hDb

end RHTower

end
