import GaloisForLFunctions.RHTower.ZetaTypicalLocalZeroCount
import GaloisForLFunctions.RHTower.GaussianCentralGapBohrSpectrum
import GaloisForLFunctions.RHTower.XiZeroBandFinite
import GaloisForLFunctions.RHTower.XiLineHalfGaussInstance

/-!
# The slope of `ξ` is a Poisson sum

At `s = ½ + r + iY` the partial fraction of `ξ′/ξ`, paired under `ρ ↦ 1 − ρ̄`, reads

`2 Re ξ′/ξ(s) = Σ_ρ P(r, a, u)`,   `P = 2r v/(v² + e²)`,   `v = r² − a² + u²`,   `e = 2|a u|`,

with `a = Re ρ − ½`, `u = Y − Im ρ`. A zero *keeps away* from `Y` at level `R₀` when `|a| ≤ R₀` or `|u| > 4|a|`. If all zeros keep away, then for `r ≥ 2R₀` one has `v > e`, and two laws follow from elementary properties of `P`.

* **Poisson comparison.** `P ≥ 0` and `P/r` is nonincreasing in `r`, so `r₁ Re ξ′/ξ(r₂) ≤ r₂ Re ξ′/ξ(r₁)` for `2R₀ ≤ r₁ ≤ r₂` (`re_logDeriv_mul_le`). The slope at one scale controls all larger scales, so `|ξ|` grows at most like `exp(A(w² − b²)/2b)` above `b` (`norm_xiLine_le_growth`).
* **The lower strip.** `((r − a)² + u²)((r + a)² + u²)` is `v² + e²`, which is increasing from `w` to `r` once `r² + 2u² ≥ 2a²`. So `|ξ(½ + w + iY)| ≤ |ξ(½ + r + iY)|` for `0 ≤ w ≤ r` (`norm_xiLine_le_of_keeping`), although zeros may lie inside the strip. No loss of a power of `log T` occurs.

A height at which all zeros keep away is typical in the sense of Selberg's density theorem, at the critical scale `R₀ ≍ κ/log T` (`exists_volume_zetaZeroShadowScaled_le`). So these laws replace, at typical heights, the size bounds for `ζ` below the saddle.
-/

open Complex Filter Topology Set
open _root_.RHTower _root_.RHTower.DeBruijn

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-! ## The pair function -/

theorem xiLinePairRe_eq {r a u : ℝ} (h1 : 0 < (r - a) ^ 2 + u ^ 2) (h2 : 0 < (r + a) ^ 2 + u ^ 2) :
    xiLinePairRe r a u = 2 * r * (r ^ 2 - a ^ 2 + u ^ 2) / ((r ^ 2 - a ^ 2 + u ^ 2) ^ 2 + (2 * a * u) ^ 2) := by
  have hprod : (r ^ 2 - a ^ 2 + u ^ 2) ^ 2 + (2 * a * u) ^ 2 = ((r - a) ^ 2 + u ^ 2) * ((r + a) ^ 2 + u ^ 2) := by
    ring
  rw [hprod]
  unfold xiLinePairRe
  field_simp
  ring

/-- A zero that keeps away is admissible for every `r ≥ 2R₀`. -/
theorem pair_admissible {r R₀ a u : ℝ} (hR₀ : 0 < R₀) (hr : 2 * R₀ ≤ r) (h : |a| ≤ R₀ ∨ 4 * |a| < |u|) :
    2 * |a| * |u| < r ^ 2 - a ^ 2 + u ^ 2 := by
  have ha2 : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
  have hu2 : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
  have ha0 := abs_nonneg a
  have hr0 : 0 < r := by linarith only [hR₀, hr]
  have hr2 : (2 * R₀) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by positivity) hr 2
  rw [ha2, hu2]
  rcases h with h | h
  · have h1 : |a| ^ 2 ≤ R₀ ^ 2 := pow_le_pow_left₀ ha0 h 2
    nlinarith only [sq_nonneg (|u| - |a|), h1, hr2, sq_pos_of_pos hR₀]
  · have h3 : 3 * |a| ≤ |u| - |a| := by linarith only [h]
    have h4 : (3 * |a|) ^ 2 ≤ (|u| - |a|) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
    nlinarith only [h4, sq_pos_of_pos hr0, sq_nonneg |a|]

theorem pair_denominators_pos {r a u : ℝ} (h : 2 * |a| * |u| < r ^ 2 - a ^ 2 + u ^ 2) :
    0 < (r - a) ^ 2 + u ^ 2 ∧ 0 < (r + a) ^ 2 + u ^ 2 := by
  have he : 0 ≤ 2 * |a| * |u| := by positivity
  have hv : 0 < r ^ 2 - a ^ 2 + u ^ 2 := by linarith only [h, he]
  have hprod : 0 < ((r - a) ^ 2 + u ^ 2) * ((r + a) ^ 2 + u ^ 2) := by
    have heq : ((r - a) ^ 2 + u ^ 2) * ((r + a) ^ 2 + u ^ 2) =
        (r ^ 2 - a ^ 2 + u ^ 2) ^ 2 + (2 * a * u) ^ 2 := by ring
    rw [heq]
    positivity
  have h1 : 0 ≤ (r - a) ^ 2 + u ^ 2 := by positivity
  have h2 : 0 ≤ (r + a) ^ 2 + u ^ 2 := by positivity
  exact ⟨lt_of_le_of_ne h1 fun h0 => by rw [← h0, zero_mul] at hprod; exact lt_irrefl _ hprod,
    lt_of_le_of_ne h2 fun h0 => by rw [← h0, mul_zero] at hprod; exact lt_irrefl _ hprod⟩

/-- `P ≥ 0` for an admissible zero. -/
theorem pairRe_nonneg {r a u : ℝ} (hr : 0 ≤ r) (h : 2 * |a| * |u| < r ^ 2 - a ^ 2 + u ^ 2) :
    0 ≤ xiLinePairRe r a u := by
  obtain ⟨h1, h2⟩ := pair_denominators_pos h
  rw [xiLinePairRe_eq h1 h2]
  have he : 0 ≤ 2 * |a| * |u| := by positivity
  have hv : 0 ≤ r ^ 2 - a ^ 2 + u ^ 2 := by linarith only [h, he]
  positivity

/-- `P/r` is nonincreasing in `r` on the admissible range. -/
theorem pairRe_scale_le {r₁ r₂ a u : ℝ} (hr₁ : 0 < r₁) (hr : r₁ ≤ r₂) (h : 2 * |a| * |u| < r₁ ^ 2 - a ^ 2 + u ^ 2) :
    r₁ * xiLinePairRe r₂ a u ≤ r₂ * xiLinePairRe r₁ a u := by
  have hr₂ : 0 < r₂ := hr₁.trans_le hr
  have hsq : r₁ ^ 2 ≤ r₂ ^ 2 := pow_le_pow_left₀ hr₁.le hr 2
  have h' : 2 * |a| * |u| < r₂ ^ 2 - a ^ 2 + u ^ 2 := by linarith only [h, hsq]
  obtain ⟨h1, h2⟩ := pair_denominators_pos h
  obtain ⟨h3, h4⟩ := pair_denominators_pos h'
  rw [xiLinePairRe_eq h1 h2, xiLinePairRe_eq h3 h4]
  set v₁ := r₁ ^ 2 - a ^ 2 + u ^ 2 with hv₁
  set v₂ := r₂ ^ 2 - a ^ 2 + u ^ 2 with hv₂
  set e := 2 * |a| * |u| with he
  have he0 : 0 ≤ e := by positivity
  have hee : (2 * a * u) ^ 2 = e ^ 2 := by
    rw [he]
    simp only [mul_pow, sq_abs]
  rw [hee]
  have hv₁0 : 0 < v₁ := by linarith only [h, he0]
  have hv₂0 : 0 < v₂ := by linarith only [h', he0]
  have hvv : v₁ ≤ v₂ := by rw [hv₁, hv₂]; linarith only [hsq]
  have hkey : v₂ * (v₁ ^ 2 + e ^ 2) ≤ v₁ * (v₂ ^ 2 + e ^ 2) := by
    have h5 : e ^ 2 ≤ v₁ * v₂ := by
      have h6 := mul_le_mul h.le (h.le.trans hvv) he0 hv₁0.le
      nlinarith only [h6]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hvv) (sub_nonneg.mpr h5)]
  have hc : 0 ≤ 2 * r₁ * r₂ := by positivity
  have hd₁ : 0 < v₁ ^ 2 + e ^ 2 := by positivity
  have hd₂ : 0 < v₂ ^ 2 + e ^ 2 := by positivity
  have h7 : r₁ * (2 * r₂ * v₂ / (v₂ ^ 2 + e ^ 2)) = 2 * r₁ * r₂ * (v₂ / (v₂ ^ 2 + e ^ 2)) := by ring
  have h8 : r₂ * (2 * r₁ * v₁ / (v₁ ^ 2 + e ^ 2)) = 2 * r₁ * r₂ * (v₁ / (v₁ ^ 2 + e ^ 2)) := by ring
  rw [h7, h8]
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [div_le_div_iff₀ hd₂ hd₁]
  linarith only [hkey]

/-- The product of the two distances grows from `w` to `r`. -/
theorem pair_product_le {w r a u : ℝ} (hw : 0 ≤ w) (hwr : w ≤ r) (h : 2 * a ^ 2 ≤ r ^ 2 + 2 * u ^ 2) :
    ((w - a) ^ 2 + u ^ 2) * ((w + a) ^ 2 + u ^ 2) ≤ ((r - a) ^ 2 + u ^ 2) * ((r + a) ^ 2 + u ^ 2) := by
  have hsq : w ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hw hwr 2
  have hid : ((r - a) ^ 2 + u ^ 2) * ((r + a) ^ 2 + u ^ 2) - ((w - a) ^ 2 + u ^ 2) * ((w + a) ^ 2 + u ^ 2) =
      (r ^ 2 - w ^ 2) * (r ^ 2 + w ^ 2 + 2 * u ^ 2 - 2 * a ^ 2) := by ring
  have h1 : 0 ≤ (r ^ 2 - w ^ 2) * (r ^ 2 + w ^ 2 + 2 * u ^ 2 - 2 * a ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hsq) (by nlinarith only [h, sq_nonneg w])
  linarith only [hid, h1]

/-! ## The zeros keeping away -/

/-- The depth of a zero. -/
def zeroDepth (q : XiZeroCopy) : ℝ := ((q.1 : ℂ)).re - 1 / 2

/-- The distance in ordinate from a height. -/
def zeroOrdGap (Y : ℝ) (q : XiZeroCopy) : ℝ := Y - ((q.1 : ℂ)).im

/-- All zeros keep away from the height `Y` at level `R₀`. -/
def KeepsAway (Y R₀ : ℝ) : Prop := ∀ q : XiZeroCopy, |zeroDepth q| ≤ R₀ ∨ 4 * |zeroDepth q| < |zeroOrdGap Y q|

/-- All zeros of depth above `R₀` lie at distance more than five depths from `X`. -/
def ZeroKeeping (X R₀ : ℝ) : Prop := ∀ q : XiZeroCopy, R₀ < |zeroDepth q| → 5 * |zeroDepth q| < |zeroOrdGap X q|

theorem ZeroKeeping.keepsAway {X R₀ Y : ℝ} (h : ZeroKeeping X R₀) (hY : |Y - X| ≤ R₀) : KeepsAway Y R₀ := by
  intro q
  rcases le_or_gt |zeroDepth q| R₀ with hq | hq
  · exact Or.inl hq
  · refine Or.inr ?_
    have h1 := h q hq
    have h2 : |zeroOrdGap X q| ≤ |zeroOrdGap Y q| + |Y - X| := by
      have : zeroOrdGap X q = zeroOrdGap Y q - (Y - X) := by
        unfold zeroOrdGap
        ring
      rw [this]
      exact abs_sub _ _
    linarith only [h1, h2, hY, hq]

theorem abs_zeroDepth_lt (q : XiZeroCopy) : |zeroDepth q| < 1 / 2 := by
  have h1 := xiZeroCopy_re_pos q
  have h2 := xiZeroCopy_re_lt_one q
  unfold zeroDepth
  rw [abs_lt]
  constructor <;> linarith only [h1, h2]

/-- The reflected zero has the opposite depth and the same ordinate. -/
theorem zeroDepth_lineConj (q : XiZeroCopy) : zeroDepth (xiZeroCopyLineConjEquiv q) = -zeroDepth q := by
  have hρ := xiZero_lineConj_eq q
  unfold zeroDepth
  rw [hρ]
  simp
  ring

theorem zeroOrdGap_lineConj (Y : ℝ) (q : XiZeroCopy) :
    zeroOrdGap Y (xiZeroCopyLineConjEquiv q) = zeroOrdGap Y q := by
  have hρ := xiZero_lineConj_eq q
  unfold zeroOrdGap
  rw [hρ]
  simp

/-- The point of the critical strip at depth `r` and height `Y`. -/
abbrev linePt (Y r : ℝ) : ℂ := ((r + 1 / 2 : ℝ) : ℂ) + Y * I

theorem linePt_re (Y r : ℝ) : (linePt Y r).re = r + 1 / 2 := by simp [linePt]

theorem linePt_im (Y r : ℝ) : (linePt Y r).im = Y := by simp [linePt]

theorem xiLine_eq (Y r : ℝ) : xiLine Y r = xi (linePt Y r) := by
  rw [xiLine, xiLine_point]

/-- A zero of `ξ` on the line is a zero copy of that depth. -/
theorem exists_copy_of_xiLine_eq_zero {Y r : ℝ} (h : xiLine Y r = 0) :
    ∃ q : XiZeroCopy, zeroDepth q = r ∧ zeroOrdGap Y q = 0 := by
  rw [xiLine_eq] at h
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_eq_of_xi_eq_zero h
  have hq' : (q.1 : ℂ) = linePt Y r := hq
  refine ⟨q, ?_, ?_⟩
  · unfold zeroDepth
    rw [hq', linePt_re]
    ring
  · unfold zeroOrdGap
    rw [hq', linePt_im]
    ring

/-- A point of the line off the zeros has positive distance from every zero and its reflection. -/
theorem pair_denominators_pos_of_ne {Y r : ℝ} (h : xiLine Y r ≠ 0) (q : XiZeroCopy) :
    0 < (r - zeroDepth q) ^ 2 + zeroOrdGap Y q ^ 2 ∧ 0 < (r + zeroDepth q) ^ 2 + zeroOrdGap Y q ^ 2 := by
  have hgen (p : XiZeroCopy) : 0 < (r - zeroDepth p) ^ 2 + zeroOrdGap Y p ^ 2 := by
    by_contra hcon
    have h0 : (r - zeroDepth p) ^ 2 + zeroOrdGap Y p ^ 2 = 0 :=
      le_antisymm (not_lt.mp hcon) (by positivity)
    have h1 : r - zeroDepth p = 0 := by nlinarith only [h0, sq_nonneg (r - zeroDepth p), sq_nonneg (zeroOrdGap Y p)]
    have h2 : zeroOrdGap Y p = 0 := by nlinarith only [h0, sq_nonneg (r - zeroDepth p), sq_nonneg (zeroOrdGap Y p)]
    apply h
    rw [xiLine_eq]
    have hpt : linePt Y r = (p.1 : ℂ) := by
      apply Complex.ext
      · rw [linePt_re]
        unfold zeroDepth at h1
        linarith only [h1]
      · rw [linePt_im]
        unfold zeroOrdGap at h2
        linarith only [h2]
    rw [hpt]
    exact xi_xiZeroCopy_eq_zero p
  refine ⟨hgen q, ?_⟩
  have h3 := hgen (xiZeroCopyLineConjEquiv q)
  rwa [zeroDepth_lineConj, zeroOrdGap_lineConj, sub_neg_eq_add] at h3

/-- The zeros keeping away leave no zero at depth `r ≥ 2R₀`. -/
theorem xiLine_ne_zero_of_keepsAway {Y R₀ r : ℝ} (hR₀ : 0 < R₀) (hZ : KeepsAway Y R₀) (hr : 2 * R₀ ≤ r) :
    xiLine Y r ≠ 0 := by
  intro h
  obtain ⟨q, h1, h2⟩ := exists_copy_of_xiLine_eq_zero h
  have hr0 : 0 < r := by linarith only [hR₀, hr]
  rcases hZ q with h3 | h3
  · rw [h1, abs_of_pos hr0] at h3
    linarith only [h3, hr, hR₀]
  · rw [h1, h2, abs_zero, abs_of_pos hr0] at h3
    linarith only [h3, hr0]

/-! ## The sum over the zeros -/

/-- The pair sum over the zeros, at a point off the zeros. -/
theorem summable_pairRe {Y r : ℝ} (h : xiLine Y r ≠ 0) :
    Summable fun q : XiZeroCopy => xiLinePairRe r (zeroDepth q) (zeroOrdGap Y q) := by
  rw [xiLine_eq] at h
  have hsum : Summable (pfTerm (linePt Y r)) := summable_partialFractionTerm h
  have hsumJ : Summable (fun q => pfTerm (linePt Y r) (xiZeroCopyLineConjEquiv q)) :=
    (xiZeroCopyLineConjEquiv.summable_iff).mpr hsum
  have hpairs := hsum.add hsumJ
  have hre := Complex.reCLM.summable hpairs
  refine hre.congr fun q => ?_
  have h1 := re_partialFraction_pair_eq (linePt Y r) q
  rw [linePt_re, linePt_im, add_sub_cancel_right] at h1
  exact h1

theorem two_mul_re_logDeriv_eq {Y r : ℝ} (h : xiLine Y r ≠ 0) :
    2 * (logDeriv xi (linePt Y r)).re = ∑' q : XiZeroCopy, xiLinePairRe r (zeroDepth q) (zeroOrdGap Y q) := by
  rw [xiLine_eq] at h
  have h1 := two_mul_re_logDeriv_xi_eq_tsum_pair h
  rw [linePt_re, linePt_im, add_sub_cancel_right] at h1
  exact h1

/-- **The slope is nonnegative above the keeping level.** -/
theorem re_logDeriv_nonneg {Y R₀ r : ℝ} (hR₀ : 0 < R₀) (hZ : KeepsAway Y R₀) (hr : 2 * R₀ ≤ r) :
    0 ≤ (logDeriv xi (linePt Y r)).re := by
  have hne := xiLine_ne_zero_of_keepsAway hR₀ hZ hr
  have h := two_mul_re_logDeriv_eq hne
  have h1 : 0 ≤ ∑' q : XiZeroCopy, xiLinePairRe r (zeroDepth q) (zeroOrdGap Y q) :=
    tsum_nonneg fun q => pairRe_nonneg (by linarith only [hR₀, hr]) (pair_admissible hR₀ hr (hZ q))
  linarith only [h, h1]

/-- **Poisson comparison.** The slope at a scale `r₁ ≥ 2R₀` bounds the slope at all larger scales. -/
theorem re_logDeriv_mul_le {Y R₀ r₁ r₂ : ℝ} (hR₀ : 0 < R₀) (hZ : KeepsAway Y R₀) (hr₁ : 2 * R₀ ≤ r₁) (hr : r₁ ≤ r₂) :
    r₁ * (logDeriv xi (linePt Y r₂)).re ≤ r₂ * (logDeriv xi (linePt Y r₁)).re := by
  have hne₁ := xiLine_ne_zero_of_keepsAway hR₀ hZ hr₁
  have hne₂ := xiLine_ne_zero_of_keepsAway hR₀ hZ (hr₁.trans hr)
  have h₁ := two_mul_re_logDeriv_eq hne₁
  have h₂ := two_mul_re_logDeriv_eq hne₂
  have hr₁0 : 0 < r₁ := by linarith only [hR₀, hr₁]
  have hle : ∑' q : XiZeroCopy, r₁ * xiLinePairRe r₂ (zeroDepth q) (zeroOrdGap Y q) ≤
      ∑' q : XiZeroCopy, r₂ * xiLinePairRe r₁ (zeroDepth q) (zeroOrdGap Y q) :=
    Summable.tsum_le_tsum (fun q => pairRe_scale_le hr₁0 hr (pair_admissible hR₀ hr₁ (hZ q)))
      ((summable_pairRe hne₂).mul_left _) ((summable_pairRe hne₁).mul_left _)
  rw [tsum_mul_left, tsum_mul_left, ← h₁, ← h₂] at hle
  linarith only [hle]

/-! ## The logarithm of the norm -/

theorem hasDerivAt_log_norm {g : ℝ → ℂ} {D : ℂ} {x : ℝ} (hne : g x ≠ 0) (hg : HasDerivAt g (D * g x) x) :
    HasDerivAt (fun u => Real.log ‖g u‖) D.re x := by
  have hinner : inner ℝ (g x) (D * g x) = ‖g x‖ ^ 2 * D.re := by
    rw [Complex.inner, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hq : HasDerivAt (fun u => ‖g u‖ ^ 2) (2 * (‖g x‖ ^ 2 * D.re)) x := by
    have hraw := hg.norm_sq
    rwa [hinner] at hraw
  have hqpos : 0 < ‖g x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hlog := (hq.log hqpos.ne').const_mul (1 / 2 : ℝ)
  have heq : (fun u => (1 / 2 : ℝ) * Real.log (‖g u‖ ^ 2)) = fun u => Real.log ‖g u‖ := by
    funext u
    rw [Real.log_pow]
    push_cast
    ring
  rw [heq] at hlog
  refine hlog.congr_deriv ?_
  field_simp

theorem hasDerivAt_log_norm_xiLine {Y r : ℝ} (h : xiLine Y r ≠ 0) :
    HasDerivAt (fun s => Real.log ‖xiLine Y s‖) (logDeriv xi (linePt Y r)).re r := by
  refine hasDerivAt_log_norm h ?_
  have he : xiLineDeriv Y r = logDeriv xi (linePt Y r) * xiLine Y r := by
    have h' := h
    rw [xiLine_eq] at h' ⊢
    rw [logDeriv_apply, div_mul_cancel₀ _ h']
    unfold xiLineDeriv
    rw [xiLine_point]
  rw [← he]
  exact hasDerivAt_xiLine Y r

/-- **Growth above a scale.** If the slope at `b` is at most `A`, then `|ξ|` grows at most like `exp(A(w² − b²)/2b)`. -/
theorem norm_xiLine_le_growth {Y R₀ b w A : ℝ} (hR₀ : 0 < R₀) (hZ : KeepsAway Y R₀) (hb : 2 * R₀ ≤ b) (hbw : b ≤ w)
    (hA : (logDeriv xi (linePt Y b)).re ≤ A) :
    ‖xiLine Y w‖ ≤ ‖xiLine Y b‖ * Real.exp (A * (w ^ 2 - b ^ 2) / (2 * b)) := by
  have hb0 : 0 < b := by linarith only [hR₀, hb]
  set G : ℝ → ℝ := fun s => Real.log ‖xiLine Y s‖ - A * s ^ 2 / (2 * b) with hG
  have hne (s : ℝ) (hs : b ≤ s) : xiLine Y s ≠ 0 := xiLine_ne_zero_of_keepsAway hR₀ hZ (hb.trans hs)
  have hd (s : ℝ) (hs : b ≤ s) : HasDerivAt G ((logDeriv xi (linePt Y s)).re - A * s / b) s := by
    have h1 := hasDerivAt_log_norm_xiLine (hne s hs)
    have h2 : HasDerivAt (fun s : ℝ => A * s ^ 2 / (2 * b)) (A * s / b) s := by
      have h3 := ((hasDerivAt_pow 2 s).const_mul A).div_const (2 * b)
      refine h3.congr_deriv ?_
      field_simp
      push_cast
      ring
    exact h1.sub h2
  have hanti : AntitoneOn G (Icc b w) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc b w) (fun s hs => (hd s hs.1).continuousAt.continuousWithinAt)
      (fun s hs => (hd s (interior_subset hs).1).differentiableAt.differentiableWithinAt) ?_
    intro s hs
    have hs' := interior_subset hs
    rw [(hd s hs'.1).deriv]
    have h1 := re_logDeriv_mul_le hR₀ hZ hb hs'.1
    have hs0 : 0 < s := hb0.trans_le hs'.1
    have h2 : s * (logDeriv xi (linePt Y b)).re ≤ s * A := mul_le_mul_of_nonneg_left hA hs0.le
    have h3 : (logDeriv xi (linePt Y s)).re ≤ A * s / b := by
      rw [le_div_iff₀ hb0]
      linarith only [h1, h2]
    linarith only [h3]
  have hle := hanti (left_mem_Icc.mpr hbw) (right_mem_Icc.mpr hbw) hbw
  simp only [hG] at hle
  have hpos₁ := norm_pos_iff.mpr (hne w hbw)
  have hpos₂ := norm_pos_iff.mpr (hne b le_rfl)
  have hlog : Real.log ‖xiLine Y w‖ ≤ Real.log ‖xiLine Y b‖ + A * (w ^ 2 - b ^ 2) / (2 * b) := by
    have h4 : A * (w ^ 2 - b ^ 2) / (2 * b) = A * w ^ 2 / (2 * b) - A * b ^ 2 / (2 * b) := by ring
    linarith only [hle, h4]
  calc ‖xiLine Y w‖ = Real.exp (Real.log ‖xiLine Y w‖) := (Real.exp_log hpos₁).symm
    _ ≤ Real.exp (Real.log ‖xiLine Y b‖ + A * (w ^ 2 - b ^ 2) / (2 * b)) := Real.exp_le_exp.mpr hlog
    _ = _ := by rw [Real.exp_add, Real.exp_log hpos₂]

/-! ## The lower strip -/

/-- The strip law on a segment free of zeros. -/
theorem norm_xiLine_le_of_no_zero {Y R₀ w r : ℝ} (hR₀ : 0 < R₀) (hZ : KeepsAway Y R₀) (hw : 0 ≤ w) (hwr : w ≤ r)
    (hr : 2 * R₀ ≤ r) (hno : ∀ s ∈ Icc w r, xiLine Y s ≠ 0) : ‖xiLine Y w‖ ≤ ‖xiLine Y r‖ := by
  classical
  set N : Finset XiZeroCopy := (finite_xiZeroCopy_band Y (zero_le_one)).toFinset with hN
  have hnotN (q : XiZeroCopy) (hq : q ∉ N) : 1 < |zeroOrdGap Y q| := by
    rw [hN, Set.Finite.mem_toFinset, mem_setOf_eq, not_le] at hq
    unfold zeroOrdGap
    rw [abs_sub_comm]
    exact hq
  set ψ : XiZeroCopy → ℝ → ℝ := fun q s =>
    (1 / 2) * (Real.log ((s - zeroDepth q) ^ 2 + zeroOrdGap Y q ^ 2) +
      Real.log ((s + zeroDepth q) ^ 2 + zeroOrdGap Y q ^ 2)) with hψ
  have hψd (q : XiZeroCopy) (s : ℝ) (hs : s ∈ Icc w r) :
      HasDerivAt (ψ q) (xiLinePairRe s (zeroDepth q) (zeroOrdGap Y q)) s := by
    obtain ⟨h1, h2⟩ := pair_denominators_pos_of_ne (hno s hs) q
    have h3 : HasDerivAt (fun s : ℝ => (s - zeroDepth q) ^ 2 + zeroOrdGap Y q ^ 2) (2 * (s - zeroDepth q)) s := by
      have := (((hasDerivAt_id s).sub_const (zeroDepth q)).pow 2).add_const (zeroOrdGap Y q ^ 2)
      refine this.congr_deriv ?_
      simp
    have h4 : HasDerivAt (fun s : ℝ => (s + zeroDepth q) ^ 2 + zeroOrdGap Y q ^ 2) (2 * (s + zeroDepth q)) s := by
      have := (((hasDerivAt_id s).add_const (zeroDepth q)).pow 2).add_const (zeroOrdGap Y q ^ 2)
      refine this.congr_deriv ?_
      simp
    have h5 := ((h3.log h1.ne').add (h4.log h2.ne')).const_mul (1 / 2 : ℝ)
    refine h5.congr_deriv ?_
    unfold xiLinePairRe
    field_simp
  set H : ℝ → ℝ := fun s => Real.log ‖xiLine Y s‖ - (1 / 2) * ∑ q ∈ N, ψ q s with hH
  have hHd (s : ℝ) (hs : s ∈ Icc w r) :
      HasDerivAt H ((logDeriv xi (linePt Y s)).re -
        (1 / 2) * ∑ q ∈ N, xiLinePairRe s (zeroDepth q) (zeroOrdGap Y q)) s :=
    (hasDerivAt_log_norm_xiLine (hno s hs)).sub
      ((HasDerivAt.fun_sum fun q _ => hψd q s hs).const_mul (1 / 2 : ℝ))
  have hmono : MonotoneOn H (Icc w r) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc w r) (fun s hs => (hHd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hHd s (interior_subset hs)).differentiableAt.differentiableWithinAt) ?_
    intro s hs
    have hs' := interior_subset hs
    rw [(hHd s hs').deriv]
    rw [interior_Icc] at hs
    have hs0 : 0 < s := lt_of_le_of_lt hw hs.1
    have hne := hno s hs'
    have hsum := two_mul_re_logDeriv_eq hne
    have hle : ∑ q ∈ N, xiLinePairRe s (zeroDepth q) (zeroOrdGap Y q) ≤
        ∑' q : XiZeroCopy, xiLinePairRe s (zeroDepth q) (zeroOrdGap Y q) := by
      refine (summable_pairRe hne).sum_le_tsum N fun q hq => ?_
      refine xiLinePairRe_nonneg_of_sq_lt hs0 ?_
      have h1 := hnotN q hq
      have h2 := abs_zeroDepth_lt q
      rw [← sq_abs (zeroDepth q), ← sq_abs (zeroOrdGap Y q)]
      nlinarith only [h1, h2, abs_nonneg (zeroDepth q)]
    linarith only [hsum, hle]
  have hle := hmono (left_mem_Icc.mpr hwr) (right_mem_Icc.mpr hwr) hwr
  simp only [hH] at hle
  -- the near zeros only help
  have hψle : ∑ q ∈ N, ψ q w ≤ ∑ q ∈ N, ψ q r := by
    refine Finset.sum_le_sum fun q _ => ?_
    obtain ⟨h1, h2⟩ := pair_denominators_pos_of_ne (hno w (left_mem_Icc.mpr hwr)) q
    obtain ⟨h3, h4⟩ := pair_denominators_pos_of_ne (hno r (right_mem_Icc.mpr hwr)) q
    have hcond : 2 * zeroDepth q ^ 2 ≤ r ^ 2 + 2 * zeroOrdGap Y q ^ 2 := by
      have hr2 : (2 * R₀) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by positivity) hr 2
      rw [← sq_abs (zeroDepth q), ← sq_abs (zeroOrdGap Y q)]
      rcases hZ q with h5 | h5
      · have h6 : |zeroDepth q| ^ 2 ≤ R₀ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h5 2
        nlinarith only [h6, hr2, sq_nonneg |zeroOrdGap Y q|, sq_nonneg R₀]
      · have h6 : (4 * |zeroDepth q|) ^ 2 ≤ |zeroOrdGap Y q| ^ 2 :=
          pow_le_pow_left₀ (by positivity) h5.le 2
        nlinarith only [h6, sq_nonneg r, sq_nonneg |zeroDepth q|]
    have hprod := pair_product_le hw hwr hcond
    simp only [hψ]
    rw [← Real.log_mul h1.ne' h2.ne', ← Real.log_mul h3.ne' h4.ne']
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (mul_pos h1 h2) hprod) (by norm_num)
  have hlog : Real.log ‖xiLine Y w‖ ≤ Real.log ‖xiLine Y r‖ := by linarith only [hle, hψle]
  have hpos₁ := norm_pos_iff.mpr (hno w (left_mem_Icc.mpr hwr))
  have hpos₂ := norm_pos_iff.mpr (hno r (right_mem_Icc.mpr hwr))
  exact (Real.log_le_log_iff hpos₁ hpos₂).mp hlog

theorem countable_xiZeroCopy : Countable XiZeroCopy := by
  have h : (Set.univ : Set XiZeroCopy) = ⋃ n : ℕ, {q : XiZeroCopy | |((q.1 : ℂ)).im - 0| ≤ n} := by
    ext q
    simp only [mem_univ, mem_iUnion, mem_setOf_eq, true_iff]
    exact ⟨⌈|((q.1 : ℂ)).im - 0|⌉₊, Nat.le_ceil _⟩
  have hc : (Set.univ : Set XiZeroCopy).Countable := by
    rw [h]
    exact Set.countable_iUnion fun n => (finite_xiZeroCopy_band 0 (Nat.cast_nonneg n)).countable
  exact Set.countable_univ_iff.mp hc

theorem continuous_xiLine_height (w : ℝ) : Continuous fun Y : ℝ => xiLine Y w := by
  unfold xiLine
  exact xi_differentiable.continuous.comp (by fun_prop)

/-- **The lower strip.** If all zeros of depth above `R₀` are far from `X`, then near `X` the modulus of `ξ` at depth `w ≤ r` is at most its modulus at depth `r ≥ 2R₀`. -/
theorem norm_xiLine_le_of_keeping {X R₀ Y w r : ℝ} (hR₀ : 0 < R₀) (hK : ZeroKeeping X R₀) (hY : |Y - X| < R₀)
    (hw : 0 ≤ w) (hwr : w ≤ r) (hr : 2 * R₀ ≤ r) : ‖xiLine Y w‖ ≤ ‖xiLine Y r‖ := by
  haveI := countable_xiZeroCopy
  by_contra hcon
  push Not at hcon
  have hE : (Set.range fun q : XiZeroCopy => ((q.1 : ℂ)).im).Countable := Set.countable_range _
  have hdense := hE.dense_compl ℝ
  set U : Set ℝ := {Y' | ‖xiLine Y' r‖ < ‖xiLine Y' w‖} ∩ {Y' | |Y' - X| < R₀} with hU
  have hUo : IsOpen U := by
    refine IsOpen.inter ?_ ?_
    · exact isOpen_lt (continuous_xiLine_height r).norm (continuous_xiLine_height w).norm
    · exact isOpen_lt (by fun_prop) continuous_const
  obtain ⟨Y', hYE, hY'⟩ := hdense.exists_mem_open hUo ⟨Y, hcon, hY⟩
  refine not_le_of_gt hY'.1 (norm_xiLine_le_of_no_zero hR₀ (hK.keepsAway (le_of_lt hY'.2)) hw hwr hr ?_)
  intro s _ h0
  obtain ⟨q, -, h2⟩ := exists_copy_of_xiLine_eq_zero h0
  apply hYE
  refine ⟨q, ?_⟩
  unfold zeroOrdGap at h2
  linarith only [h2]

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
