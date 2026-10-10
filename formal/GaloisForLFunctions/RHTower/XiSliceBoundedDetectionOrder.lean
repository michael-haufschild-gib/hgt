import GaloisForLFunctions.RHTower.XiSliceDetectionOrderBound
import GaloisForLFunctions.RHTower.XiReciprocalSliceDominance
import GaloisForLFunctions.RHTower.LorentzianZeroMass

/-!
# Near-line off-line zeros are detected at bounded slice order

Let `ρ` be a zero of `ξ` off the critical line, with ordinate `γ`, displacement
`δ = |Re ρ − ½| > 0` and `ξ(½ + iγ) ≠ 0`.  In spectral coordinates `ρ` and its reflection
`1 − ρ̄` are the points `γ ∓ iδ`.  Both have `(z − γ)² = −δ²`, so the slice product factors as

  `g_γ(x)/g_γ(0) = (1 − x²/δ²)^{m} · ∏_{other z} (1 + x²/(z − γ)²)`,

where `m` counts the copies of the two points.  On `|x| = 2δ` the first factor is at most `5^m`.
Each other factor is at most `exp(4δ²/|z − γ|²)`.  The detection bound
(`exists_re_xiSliceCoeff_neg_of_tail_lt`) at `R = 2δ` then gives:

**Theorem** (`exists_re_xiSliceCoeff_neg_of_offLine_mass`).  If the other zeros have
inverse-square mass `Σ 1/|z − γ|² ≤ S` about `γ`, and `2 · 5^m · e^{4δ²S} < 2^N`, then some
slice coefficient `c_n(γ)` with `n < N` has negative real part.

So the detection order is at most `log₂(2·5^m) + 4δ²S/log 2`.  A simple off-line zero (`m = 2`)
with `δ² S ≤ 1` is detected below order `12`, uniformly in the height.  The finite-order reduction
needs orders up to `κ log γ` in general.  Off-line zeros with bounded `δ²S`, in particular zeros
within `O(1/log γ)` of the critical line and isolated at that scale, are already excluded by
bounded-order slice positivity at their ordinates.

**Explicit form** (`exists_re_xiSliceCoeff_neg_of_isolated_offLine`).  If every other zero copy
lies at distance at least `r₀` from `γ`, the Lorentzian mass bound
(`lorentzMass_le_log`) gives `S ≤ 16 (1 + r₀^{−2}) (K + log(|γ| + 4))`.  So the detection order is
below `log₂(2·5^m) + (64/log 2) δ² (1 + r₀^{−2}) (K + log(|γ| + 4))`.  An off-line zero with
`δ ≤ min(1, r₀)/√(log γ)` is detected at bounded order.
-/

open Complex Filter Topology Metric

namespace RHTower

noncomputable section

/-- The slice product as a limit of finite products over the zero copies. -/
theorem tendsto_prod_one_add_sq_div_xiSliceProduct {t : ℝ} (ht : XiC t ≠ 0) (x : ℂ) :
    Tendsto (fun S : Finset XiZeroCopy => ∏ q ∈ S, (1 + x ^ 2 / (xiSpectralPoint q - t) ^ 2))
      atTop (𝓝 (xiSliceProduct t x / xiSliceProduct t 0)) := by
  have h := tendsto_prod_one_sub_sq_div ht (-I * x)
  have e1 : xiHorizontalPair t (-I * x) = xiSliceProduct t x := by
    rw [xiHorizontalPair_eq_xiSliceProduct]
    congr 1
    rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]
  have e2 : xiHorizontalPair t 0 = xiSliceProduct t 0 := by
    rw [xiHorizontalPair_eq_xiSliceProduct, mul_zero]
  rw [e1, e2] at h
  refine h.congr fun S => Finset.prod_congr rfl fun q _ => ?_
  rw [mul_pow, neg_sq, I_sq]
  ring

/-- **Bounded detection order.**  Let `ρ` be a zero of `ξ` off the critical line with
`ξ(½ + iγ) ≠ 0`, `γ = Im ρ`, `δ = |Re ρ − ½|`.  Suppose at most `m` zero copies sit at the points
`γ ± iδ`, and the other copies have `Σ 1/|z − γ|² ≤ S`.  If `2 · 5^m · e^{4δ²S} < 2^N`, some slice
coefficient `c_n(γ)` with `n < N` has negative real part. -/
theorem exists_re_xiSliceCoeff_neg_of_offLine_mass {ρ : ℂ} (hρ : xi ρ = 0) (hne : ρ.re ≠ 1 / 2)
    (hΞ : XiC ρ.im ≠ 0) {m : ℕ}
    (hown : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I) → F.card ≤ m)
    {S : ℝ} (hS : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        ¬ (xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I)) →
      ∑ q ∈ F, 1 / ‖xiSpectralPoint q - ρ.im‖ ^ 2 ≤ S)
    {N : ℕ} (hN : 2 * 5 ^ m * Real.exp (4 * |ρ.re - 1 / 2| ^ 2 * S) < 2 ^ N) :
    ∃ n < N, (xiSliceCoeff ρ.im n).re < 0 := by
  classical
  set t : ℝ := ρ.im with htdef
  set δ : ℝ := |ρ.re - 1 / 2| with hδdef
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hne)
  -- the constant term
  have hc0 : xiSliceCoeff t 0 = xiSliceProduct t 0 := by
    simp [xiSliceCoeff]
  have hc0pos : 0 < (xiSliceCoeff t 0).re := xiSliceCoeff_zero_re_pos hΞ
  have hc0im : (xiSliceCoeff t 0).im = 0 := xiSliceCoeff_im_eq_zero t 0
  have hg0norm : ‖xiSliceProduct t 0‖ = (xiSliceCoeff t 0).re := by
    rw [← hc0]
    have hreal : xiSliceCoeff t 0 = (((xiSliceCoeff t 0).re : ℝ) : ℂ) :=
      Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im]; exact hc0im)
    conv_lhs => rw [hreal]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0pos]
  have hg0 : xiSliceProduct t 0 ≠ 0 := by
    intro h; rw [h, norm_zero] at hg0norm; linarith
  -- the bound on the circle `|x| = 2δ`
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 5 ^ m * Real.exp (4 * δ ^ 2 * S) := ⟨_, rfl⟩
  have hfinite : ∀ x : ℂ, ‖x‖ = 2 * δ → ∀ F : Finset XiZeroCopy,
      ‖∏ q ∈ F, (1 + x ^ 2 / (xiSpectralPoint q - t) ^ 2)‖ ≤ B := by
    intro x hx F
    set own : XiZeroCopy → Prop := fun q =>
      xiSpectralPoint q = (t : ℂ) + (δ : ℂ) * I ∨ xiSpectralPoint q = (t : ℂ) - (δ : ℂ) * I
    rw [← Finset.prod_filter_mul_prod_filter_not F own, norm_mul, norm_prod, norm_prod]
    have hx2 : ‖x ^ 2‖ = 4 * δ ^ 2 := by rw [norm_pow, hx]; ring
    have h1 : ∏ q ∈ F with own q, ‖1 + x ^ 2 / (xiSpectralPoint q - t) ^ 2‖ ≤ 5 ^ m := by
      calc ∏ q ∈ F with own q, ‖1 + x ^ 2 / (xiSpectralPoint q - t) ^ 2‖
          ≤ ∏ q ∈ F with own q, (5 : ℝ) := by
            refine Finset.prod_le_prod (fun q _ => norm_nonneg _) fun q hq => ?_
            have hsq : (xiSpectralPoint q - t) ^ 2 = -((δ : ℂ) ^ 2) := by
              rcases (Finset.mem_filter.mp hq).2 with h | h <;> rw [h] <;> ring_nf <;>
                rw [I_sq] <;> ring
            rw [hsq]
            calc ‖1 + x ^ 2 / -((δ : ℂ) ^ 2)‖ ≤ ‖(1 : ℂ)‖ + ‖x ^ 2 / -((δ : ℂ) ^ 2)‖ :=
                  norm_add_le _ _
              _ = 5 := by
                  rw [norm_one, norm_div, norm_neg, hx2, norm_pow, Complex.norm_real,
                    Real.norm_eq_abs, abs_of_pos hδ]
                  field_simp
                  norm_num
        _ = 5 ^ (F.filter own).card := by rw [Finset.prod_const]
        _ ≤ 5 ^ m := pow_le_pow_right₀ (by norm_num)
            (hown _ fun q hq => (Finset.mem_filter.mp hq).2)
    have h2 : ∏ q ∈ F with ¬ own q, ‖1 + x ^ 2 / (xiSpectralPoint q - t) ^ 2‖ ≤
        Real.exp (4 * δ ^ 2 * S) := by
      calc ∏ q ∈ F with ¬ own q, ‖1 + x ^ 2 / (xiSpectralPoint q - t) ^ 2‖
          ≤ ∏ q ∈ F with ¬ own q, Real.exp (4 * δ ^ 2 * (1 / ‖xiSpectralPoint q - t‖ ^ 2)) := by
            refine Finset.prod_le_prod (fun q _ => norm_nonneg _) fun q _ => ?_
            have hc : 0 < ‖xiSpectralPoint q - t‖ :=
              norm_pos_iff.mpr (sub_ne_zero.mpr (xiSpectralPoint_ne_ofReal hΞ q))
            calc ‖1 + x ^ 2 / (xiSpectralPoint q - t) ^ 2‖
                ≤ ‖(1 : ℂ)‖ + ‖x ^ 2 / (xiSpectralPoint q - t) ^ 2‖ := norm_add_le _ _
              _ = 4 * δ ^ 2 * (1 / ‖xiSpectralPoint q - t‖ ^ 2) + 1 := by
                  rw [norm_one, norm_div, hx2, norm_pow]; ring
              _ ≤ Real.exp (4 * δ ^ 2 * (1 / ‖xiSpectralPoint q - t‖ ^ 2)) :=
                  Real.add_one_le_exp _
        _ = Real.exp (4 * δ ^ 2 * ∑ q ∈ F with ¬ own q, 1 / ‖xiSpectralPoint q - t‖ ^ 2) := by
            rw [Finset.mul_sum, Real.exp_sum]
        _ ≤ Real.exp (4 * δ ^ 2 * S) := by
            apply Real.exp_le_exp.mpr
            have hsum := hS (F.filter fun q => ¬ own q) (fun q hq => (Finset.mem_filter.mp hq).2)
            exact mul_le_mul_of_nonneg_left hsum (by positivity)
    rw [hB]
    exact mul_le_mul h1 h2 (Finset.prod_nonneg fun q _ => norm_nonneg _) (by positivity)
  have hM : ∀ x ∈ sphere (0 : ℂ) (2 * δ), ‖xiSliceProduct t x‖ ≤ B * (xiSliceCoeff t 0).re := by
    intro x hx
    have hx' : ‖x‖ = 2 * δ := mem_sphere_zero_iff_norm.mp hx
    have hlim := (tendsto_prod_one_add_sq_div_xiSliceProduct hΞ x).norm
    have hle := le_of_tendsto hlim (Eventually.of_forall (hfinite x hx'))
    rw [norm_div, hg0norm, div_le_iff₀ hc0pos] at hle
    exact hle
  -- the detection bound at `R = 2δ`
  refine exists_re_xiSliceCoeff_neg_of_tail_lt hρ (R := 2 * δ) (by linarith) hM ?_
  have hhalf : δ / (2 * δ) = 1 / 2 := by field_simp
  rw [← hδdef, hhalf]
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have e : B * (xiSliceCoeff t 0).re * (1 / 2) ^ N / (1 - 1 / 2) =
      (2 * B / 2 ^ N) * (xiSliceCoeff t 0).re := by
    rw [one_div_pow]; field_simp; ring
  rw [e]
  have hB2 : 2 * B / 2 ^ N < 1 := by
    rw [div_lt_one h2N, hB]
    simpa [mul_assoc] using hN
  nlinarith

/-- **Bounded-order positivity excludes near-line zeros.**  If the slice coefficients of order
`< N` at the ordinate of a zero `ρ` have nonnegative real parts, then `ρ` lies on the critical line.
This holds whenever `ξ(½ + iγ) ≠ 0`, at most `m` copies sit at `γ ± iδ`, the other copies have
inverse-square mass `≤ S` about `γ`, and `2 · 5^m · e^{4δ²S} < 2^N`. -/
theorem re_eq_half_of_xiSliceCoeff_nonneg_lt {ρ : ℂ} (hρ : xi ρ = 0) (hΞ : XiC ρ.im ≠ 0)
    {m : ℕ}
    (hown : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I) → F.card ≤ m)
    {S : ℝ} (hS : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        ¬ (xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I)) →
      ∑ q ∈ F, 1 / ‖xiSpectralPoint q - ρ.im‖ ^ 2 ≤ S)
    {N : ℕ} (hN : 2 * 5 ^ m * Real.exp (4 * |ρ.re - 1 / 2| ^ 2 * S) < 2 ^ N)
    (hpos : ∀ n < N, 0 ≤ (xiSliceCoeff ρ.im n).re) : ρ.re = 1 / 2 := by
  by_contra hne
  obtain ⟨n, hn, hneg⟩ := exists_re_xiSliceCoeff_neg_of_offLine_mass hρ hne hΞ hown hS hN
  linarith [hpos n hn]

/-- **Explicit bounded detection order for isolated off-line zeros.**  Let `ρ` be a zero of `ξ` off
the critical line with `ξ(½ + iγ) ≠ 0`, at most `m` copies at `γ ± iδ`, and every other copy at
distance at least `r₀ > 0` from `γ`.  If
`2 · 5^m · exp(64 δ² (1 + 1/r₀²)(K + log(|γ| + 4))) < 2^N`, where `K` is
`xiLineTwoLogDerivConstant`, then some slice coefficient `c_n(γ)` with `n < N` has negative real
part. -/
theorem exists_re_xiSliceCoeff_neg_of_isolated_offLine {ρ : ℂ} (hρ : xi ρ = 0)
    (hne : ρ.re ≠ 1 / 2) (hΞ : XiC ρ.im ≠ 0) {m : ℕ}
    (hown : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I) → F.card ≤ m)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hiso : ∀ q : XiZeroCopy, ¬ (xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I) →
        r₀ ≤ ‖xiSpectralPoint q - ρ.im‖)
    {N : ℕ} (hN : 2 * 5 ^ m * Real.exp (64 * |ρ.re - 1 / 2| ^ 2 * (1 + 1 / r₀ ^ 2) *
        (xiLineTwoLogDerivConstant + Real.log (|ρ.im| + 4))) < 2 ^ N) :
    ∃ n < N, (xiSliceCoeff ρ.im n).re < 0 := by
  set t : ℝ := ρ.im with ht
  set A : ℝ := 2 * (1 + 1 / r₀ ^ 2) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  refine exists_re_xiSliceCoeff_neg_of_offLine_mass hρ hne hΞ hown
    (S := A * (8 * (xiLineTwoLogDerivConstant + Real.log (|t| + 4)))) (fun F hF => ?_) ?_
  · -- the other copies are dominated by the Lorentzian mass
    have hterm : ∀ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ A * lorentzMassTerm t q := by
      intro q hq
      have hr := hiso q (hF q hq)
      have hc : 0 < ‖xiSpectralPoint q - t‖ := lt_of_lt_of_le hr₀ hr
      have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
      have hsq : ((q.1 : ℂ).im - t) ^ 2 ≤ ‖xiSpectralPoint q - t‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero,
          hre]
        nlinarith [sq_nonneg (xiSpectralPoint q).im]
      have hr2 : r₀ ^ 2 ≤ ‖xiSpectralPoint q - t‖ ^ 2 := pow_le_pow_left₀ hr₀.le hr 2
      unfold lorentzMassTerm
      rw [hA, div_le_iff₀ (by positivity), show (t - (q.1 : ℂ).im) ^ 2 = ((q.1 : ℂ).im - t) ^ 2 by
        ring]
      rw [show 2 * (1 + 1 / r₀ ^ 2) * (1 / (1 + ((q.1 : ℂ).im - t) ^ 2)) *
          ‖xiSpectralPoint q - t‖ ^ 2 =
          2 * (‖xiSpectralPoint q - t‖ ^ 2 + ‖xiSpectralPoint q - t‖ ^ 2 / r₀ ^ 2) /
            (1 + ((q.1 : ℂ).im - t) ^ 2) by field_simp]
      rw [le_div_iff₀ (by positivity), one_mul]
      have : 1 ≤ ‖xiSpectralPoint q - t‖ ^ 2 / r₀ ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    calc ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ ∑ q ∈ F, A * lorentzMassTerm t q :=
          Finset.sum_le_sum hterm
      _ = A * ∑ q ∈ F, lorentzMassTerm t q := by rw [Finset.mul_sum]
      _ ≤ A * lorentzMass t := by
          refine mul_le_mul_of_nonneg_left ?_ hA0
          exact (summable_lorentzMassTerm t).sum_le_tsum F (fun q _ => lorentzMassTerm_nonneg t q)
      _ ≤ A * (8 * (xiLineTwoLogDerivConstant + Real.log (|t| + 4))) :=
          mul_le_mul_of_nonneg_left (lorentzMass_le_log t) hA0
  · convert hN using 3
    rw [hA]
    ring

end

end RHTower
