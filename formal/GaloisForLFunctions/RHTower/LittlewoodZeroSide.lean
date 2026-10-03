import GaloisForLFunctions.RHTower.LittlewoodWindowIdentity
import GaloisForLFunctions.RHTower.XiZeroCopyCosWeightTail
import GaloisForLFunctions.RHTower.XiOrderedZeroCopyEnumeration

/-!
# The zero side of Littlewood's argument

Under RH, `Φ(v) = Σ_q w_q cos(γ_q v)`, `w_q = 1/(¼ + γ_q²)`.  Put `δ = 1 - e^{-h/2}` and let `u` be
aligned on the copies with `|γ| ≤ T`: `cos(γ u) ≥ 1 - ε₁`, `|sin(γ u)| ≤ ε₂`.  Then for the lag
difference `Δ_h(v) = Φ(v + h)e^{-h/2} - Φ(v)`

```text
Δ_h(u)     ≤ -(8/(5π²)) h² M + (δ + 2ε₁ + ε₂) W + 2τ(T),
Δ_h(u - h) ≥ (1 - ε₁)(8/(5π²)) h² M - (δ + ε₂) W - 2τ(T),
```

with `M = #{|γ| ≤ min(T, 1/h)}`, `W = Σ w_q` and `τ(T) = Σ_{|γ|>T} w_q`.  Each aligned term is
`-2 sin²(γh/2) + O(δ + ε₁ + ε₂)`, and Jordan's inequality gives `w sin²(γh/2) ≥ (4/(5π²))h²` when
`1 ≤ |γ| ≤ 1/h`; every term has the same sign, so no cancellation among the zeros is needed.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The copies with `|γ| ≤ T`. -/
def xiCopiesBelow (T : ℝ) : Finset XiZeroCopy := (finite_xiOrdinateWindow T 0).toFinset

theorem mem_xiCopiesBelow {T : ℝ} {q : XiZeroCopy} :
    q ∈ xiCopiesBelow T ↔ |zeroOrdinate q| ≤ T := by
  unfold xiCopiesBelow
  rw [Set.Finite.mem_toFinset, mem_xiOrdinateWindow_iff, sub_zero]
  rfl

/-- **The aligned term, lower window.** -/
theorem aligned_term_le {γ u h ε₁ ε₂ : ℝ} (hh : 0 ≤ h) (hc : 1 - ε₁ ≤ Real.cos (γ * u))
    (hs : |Real.sin (γ * u)| ≤ ε₂) :
    Real.exp (-(h / 2)) * Real.cos (γ * (u + h)) - Real.cos (γ * u)
      ≤ -2 * Real.sin (γ * h / 2) ^ 2 + (1 - Real.exp (-(h / 2))) + 2 * ε₁ + ε₂ := by
  have he0 := Real.exp_pos (-(h / 2))
  have he1 : Real.exp (-(h / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hadd : γ * (u + h) = γ * u + γ * h := by ring
  have hcosh : Real.cos (γ * h) = 1 - 2 * Real.sin (γ * h / 2) ^ 2 := by
    rw [← Real.cos_two_mul_eq_one_sub]; congr 1; ring
  have hcb := Real.cos_le_one (γ * h)
  have hcb' := Real.neg_one_le_cos (γ * h)
  have hcu := Real.cos_le_one (γ * u)
  set D := Real.exp (-(h / 2)) * Real.cos (γ * h) - 1 with hD
  have hD0 : D ≤ 0 := by
    rw [hD]; nlinarith
  have hD2 : -2 ≤ D := by rw [hD]; nlinarith
  have hDle : D ≤ -2 * Real.sin (γ * h / 2) ^ 2 + (1 - Real.exp (-(h / 2))) := by
    rw [hD, hcosh]
    have hs2 : 0 ≤ Real.sin (γ * h / 2) ^ 2 := sq_nonneg _
    have hs2' : Real.sin (γ * h / 2) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]; exact Real.abs_sin_le_one _
    nlinarith
  have hsinb : |Real.exp (-(h / 2)) * Real.sin (γ * u) * Real.sin (γ * h)| ≤ ε₂ := by
    rw [abs_mul, abs_mul, abs_of_pos he0]
    have h1 := Real.abs_sin_le_one (γ * h)
    have h2 : Real.exp (-(h / 2)) * |Real.sin (γ * u)| ≤ |Real.sin (γ * u)| := by
      nlinarith [abs_nonneg (Real.sin (γ * u))]
    nlinarith [abs_nonneg (Real.sin (γ * u)), abs_nonneg (Real.sin (γ * h))]
  have hsplit : Real.exp (-(h / 2)) * Real.cos (γ * (u + h)) - Real.cos (γ * u)
      = Real.cos (γ * u) * D - Real.exp (-(h / 2)) * Real.sin (γ * u) * Real.sin (γ * h) := by
    rw [hadd, Real.cos_add, hD]; ring
  have hcD : Real.cos (γ * u) * D ≤ (1 - ε₁) * D := by nlinarith
  have habs := (abs_le.mp hsinb).1
  rw [hsplit]
  nlinarith

/-- **The aligned term, upper window.** -/
theorem aligned_term_ge {γ u h ε₁ ε₂ : ℝ} (hh : 0 ≤ h)
    (hc : 1 - ε₁ ≤ Real.cos (γ * u)) (hs : |Real.sin (γ * u)| ≤ ε₂) :
    2 * (1 - ε₁) * Real.sin (γ * h / 2) ^ 2 - (1 - Real.exp (-(h / 2))) - ε₂
      ≤ Real.exp (-(h / 2)) * Real.cos (γ * u) - Real.cos (γ * (u - h)) := by
  have he0 := Real.exp_pos (-(h / 2))
  have he1 : Real.exp (-(h / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hsub : γ * (u - h) = γ * u - γ * h := by ring
  have hcosh : Real.cos (γ * h) = 1 - 2 * Real.sin (γ * h / 2) ^ 2 := by
    rw [← Real.cos_two_mul_eq_one_sub]; congr 1; ring
  have hcu := Real.cos_le_one (γ * u)
  have hs2 : 0 ≤ Real.sin (γ * h / 2) ^ 2 := sq_nonneg _
  have hsinb : |Real.sin (γ * u) * Real.sin (γ * h)| ≤ ε₂ := by
    rw [abs_mul]
    have h1 := Real.abs_sin_le_one (γ * h)
    nlinarith [abs_nonneg (Real.sin (γ * u)), abs_nonneg (Real.sin (γ * h))]
  have habs := (abs_le.mp hsinb).2
  have hsplit : Real.exp (-(h / 2)) * Real.cos (γ * u) - Real.cos (γ * (u - h))
      = Real.cos (γ * u) * (2 * Real.sin (γ * h / 2) ^ 2 - (1 - Real.exp (-(h / 2))))
        - Real.sin (γ * u) * Real.sin (γ * h) := by
    rw [hsub, Real.cos_sub, hcosh]; ring
  rw [hsplit]
  have h1 : (1 - ε₁) * (2 * Real.sin (γ * h / 2) ^ 2)
      ≤ Real.cos (γ * u) * (2 * Real.sin (γ * h / 2) ^ 2) :=
    mul_le_mul_of_nonneg_right hc (by positivity)
  have h2 : -(Real.cos (γ * u) * (1 - Real.exp (-(h / 2)))) ≥ -(1 - Real.exp (-(h / 2))) := by
    have : 0 ≤ 1 - Real.exp (-(h / 2)) := by linarith
    nlinarith
  nlinarith

/-- **Jordan's bound for the low zeros.**  `w sin²(γh/2) ≥ (4/(5π²))h²` when `1 ≤ |γ| ≤ 1/h`. -/
theorem cosWeight_mul_sin_sq_ge {q : XiZeroCopy} {h : ℝ} (hh : 0 < h)
    (hq1 : 1 ≤ |zeroOrdinate q|) (hqh : |zeroOrdinate q| ≤ 1 / h) :
    4 / (5 * Real.pi ^ 2) * h ^ 2 ≤ cosWeight q * Real.sin (zeroOrdinate q * h / 2) ^ 2 := by
  set γ := zeroOrdinate q with hγ
  have hπ := Real.pi_pos
  have hx0 : 0 ≤ |γ| * h / 2 := by positivity
  have hxh : |γ| * h ≤ 1 := by rw [le_div_iff₀ hh] at hqh; linarith
  have hxπ : |γ| * h / 2 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hjordan := Real.mul_le_sin hx0 hxπ
  have hsin_abs : |Real.sin (γ * h / 2)| = Real.sin (|γ| * h / 2) := by
    have hpos : 0 ≤ Real.sin (|γ| * h / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [Real.pi_pos])
    rcases le_or_gt 0 γ with hγ0 | hγ0
    · rw [abs_of_nonneg hγ0] at hpos ⊢
      exact abs_of_nonneg hpos
    · have he : γ * h / 2 = -(|γ| * h / 2) := by rw [abs_of_neg hγ0]; ring
      rw [he, Real.sin_neg, abs_neg, abs_of_nonneg hpos]
  have hsq : (|γ| * h / Real.pi) ^ 2 ≤ Real.sin (γ * h / 2) ^ 2 := by
    rw [← sq_abs (Real.sin (γ * h / 2)), hsin_abs]
    have h1 : |γ| * h / Real.pi = 2 / Real.pi * (|γ| * h / 2) := by field_simp
    rw [h1]
    exact pow_le_pow_left₀ (by positivity) hjordan 2
  have hγ2 : 1 ≤ γ ^ 2 := by rw [← sq_abs]; nlinarith
  have hw : 4 / (5 * γ ^ 2) ≤ cosWeight q := by
    unfold cosWeight
    rw [← hγ, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hsq' : (|γ| * h / Real.pi) ^ 2 = γ ^ 2 * h ^ 2 / Real.pi ^ 2 := by
    rw [div_pow, mul_pow, sq_abs]
  rw [hsq'] at hsq
  have hprod := mul_le_mul hw hsq (by positivity) (by unfold cosWeight; positivity)
  have hγne : γ ≠ 0 := by
    intro h0; rw [h0] at hγ2; norm_num at hγ2
  have hcalc : 4 / (5 * γ ^ 2) * (γ ^ 2 * h ^ 2 / Real.pi ^ 2) = 4 / (5 * Real.pi ^ 2) * h ^ 2 := by
    field_simp
  linarith


/-- The tail bound `τ(T) ≤ 40(C₀ + 1 + log(T + 4))/T`. -/
def lagTailBound (T : ℝ) : ℝ := 40 * (xiLineTwoLogDerivConstant + 1 + Real.log (T + 4)) / T

/-- **Splitting off the low copies.**  If `|f q| ≤ 2 w_q`, then `Σ' f` is within `2τ(T)` of the
finite sum over `|γ| ≤ T`. -/
theorem abs_tsum_sub_sum_xiCopiesBelow_le (hRH : RiemannHypothesis) {T : ℝ} (hT : 4 ≤ T)
    {f : XiZeroCopy → ℝ} (hf : ∀ q, |f q| ≤ 2 * cosWeight q) :
    |∑' q, f q - ∑ q ∈ xiCopiesBelow T, f q| ≤ 2 * lagTailBound T := by
  classical
  have hw := summable_cosWeight hRH
  have hsf : Summable f := Summable.of_norm_bounded (hw.mul_left 2) (fun q => by
    rw [Real.norm_eq_abs]; exact hf q)
  set S := xiCopiesBelow T with hS
  set g : XiZeroCopy → ℝ := fun q => if q ∈ S then 0 else f q with hg
  set k : XiZeroCopy → ℝ := fun q => if q ∈ S then f q else 0 with hk
  have hw2 : ∀ q, 0 ≤ 2 * cosWeight q := fun q => by unfold cosWeight; positivity
  have hfg : ∀ q, f q = k q + g q := by
    intro q; by_cases hq : q ∈ S <;> simp [hk, hg, hq]
  have hsk : Summable k := Summable.of_norm_bounded (hw.mul_left 2) (fun q => by
    rw [Real.norm_eq_abs]
    by_cases hq : q ∈ S <;> simp [hk, hq, hf q, hw2 q])
  have hsg : Summable g := Summable.of_norm_bounded (hw.mul_left 2) (fun q => by
    rw [Real.norm_eq_abs]
    by_cases hq : q ∈ S <;> simp [hg, hq, hf q, hw2 q])
  have hsplit : ∑' q, f q = ∑' q, k q + ∑' q, g q := by
    rw [← Summable.tsum_add hsk hsg]; congr 1; funext q; exact hfg q
  have hkfin : ∑' q, k q = ∑ q ∈ S, f q := by
    rw [tsum_eq_sum (s := S) (fun q hq => by rw [hk]; simp [hq])]
    exact Finset.sum_congr rfl (fun q hq => by rw [hk]; simp [hq])
  set t : XiZeroCopy → ℝ := fun q => if T < |zeroOrdinate q| then cosWeight q else 0 with ht
  have hwq0 : ∀ q, 0 ≤ cosWeight q := fun q => by unfold cosWeight; positivity
  have hst : Summable t := Summable.of_norm_bounded hw (fun q => by
    rw [Real.norm_eq_abs]
    by_cases hq : T < |zeroOrdinate q| <;> simp [ht, hq, abs_of_nonneg (hwq0 q), hwq0 q])
  have hgt : ∀ q, |g q| ≤ 2 * t q := by
    intro q
    by_cases hq : q ∈ S
    · by_cases hq' : T < |zeroOrdinate q| <;> simp [hg, ht, hq, hq', hwq0 q]
    · have hT' : T < |zeroOrdinate q| := by
        rw [hS, mem_xiCopiesBelow] at hq; exact lt_of_not_ge hq
      simp only [hg, ht, hq, hT', if_true, if_false]
      exact hf q
  have htail := tsum_cosWeight_tail_le hT
  have hgle : |∑' q, g q| ≤ 2 * ∑' q, t q := by
    rw [← tsum_mul_left]
    refine le_trans (norm_tsum_le_tsum_norm (f := g) ?_ |>.trans_eq' (by rw [Real.norm_eq_abs]))
      ?_
    · exact Summable.of_norm_bounded (hst.mul_left 2) (fun q => by
        rw [norm_norm]; exact hgt q)
    · exact Summable.tsum_le_tsum (fun q => by rw [Real.norm_eq_abs]; exact hgt q)
        (Summable.of_norm_bounded (hst.mul_left 2) (fun q => by
          rw [norm_norm]; exact hgt q)) (hst.mul_left 2)
  rw [hsplit, hkfin, add_sub_cancel_left]
  unfold lagTailBound
  linarith

/-- **The lag difference at an aligned point, lower window.** -/
theorem lagDifference_le_of_aligned (hRH : RiemannHypothesis) {T h u ε₁ ε₂ : ℝ} (hT : 4 ≤ T)
    (hh : 0 < h) (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (halign : ∀ q ∈ xiCopiesBelow T,
      1 - ε₁ ≤ Real.cos (zeroOrdinate q * u) ∧ |Real.sin (zeroOrdinate q * u)| ≤ ε₂) :
    weilLagFunctionReal (u + h) * Real.exp (-(h / 2)) - weilLagFunctionReal u
      ≤ -(8 / (5 * Real.pi ^ 2)) * h ^ 2
          * (((xiCopiesBelow T).filter (fun q => |zeroOrdinate q| ≤ 1 / h)).card : ℝ)
        + ((1 - Real.exp (-(h / 2))) + 2 * ε₁ + ε₂) * ∑' q, cosWeight q
        + 2 * lagTailBound T := by
  classical
  have hw := summable_cosWeight hRH
  set f : XiZeroCopy → ℝ := fun q => cosWeight q
    * (Real.exp (-(h / 2)) * Real.cos (zeroOrdinate q * (u + h)) - Real.cos (zeroOrdinate q * u))
    with hfdef
  have hwq : ∀ q, 0 ≤ cosWeight q := fun q => by unfold cosWeight; positivity
  have he1 : Real.exp (-(h / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he0 := Real.exp_pos (-(h / 2))
  have hfb : ∀ q, |f q| ≤ 2 * cosWeight q := by
    intro q
    rw [hfdef, abs_mul, abs_of_nonneg (hwq q)]
    have h1 := Real.abs_cos_le_one (zeroOrdinate q * (u + h))
    have h2 := Real.abs_cos_le_one (zeroOrdinate q * u)
    have h3 : |Real.exp (-(h / 2)) * Real.cos (zeroOrdinate q * (u + h))
        - Real.cos (zeroOrdinate q * u)| ≤ 2 := by
      refine le_trans (abs_sub _ _) ?_
      rw [abs_mul, abs_of_pos he0]
      nlinarith
    nlinarith [hwq q]
  have hΔ : weilLagFunctionReal (u + h) * Real.exp (-(h / 2)) - weilLagFunctionReal u
      = ∑' q, f q := by
    rw [weilLagFunctionReal_eq_cos_series hRH, weilLagFunctionReal_eq_cos_series hRH,
      ← tsum_mul_right, ← Summable.tsum_sub]
    · congr 1; funext q; rw [hfdef]; ring
    · exact Summable.of_norm_bounded hw (fun q => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hwq q), abs_of_pos he0]
        have hc := Real.abs_cos_le_one (zeroOrdinate q * (u + h))
        have h1 := mul_le_mul_of_nonneg_left hc (hwq q)
        have h2 := mul_le_mul h1 he1 he0.le (by rw [mul_one]; exact hwq q)
        linarith)
    · exact Summable.of_norm_bounded hw (fun q => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hwq q)]
        have := Real.abs_cos_le_one (zeroOrdinate q * u)
        nlinarith [hwq q])
  have hsplit := abs_tsum_sub_sum_xiCopiesBelow_le hRH hT hfb
  -- the finite sum
  set S := xiCopiesBelow T with hS
  set δ := 1 - Real.exp (-(h / 2)) with hδ
  have hterm : ∀ q ∈ S, f q
      ≤ -2 * (cosWeight q * Real.sin (zeroOrdinate q * h / 2) ^ 2)
        + (δ + 2 * ε₁ + ε₂) * cosWeight q := by
    intro q hq
    have h1 := aligned_term_le (γ := zeroOrdinate q) (u := u) hh.le (halign q hq).1 (halign q hq).2
    have h2 := mul_le_mul_of_nonneg_left h1 (hwq q)
    have hfq : f q = cosWeight q * (Real.exp (-(h / 2)) * Real.cos (zeroOrdinate q * (u + h))
        - Real.cos (zeroOrdinate q * u)) := rfl
    rw [hfq]
    nlinarith
  have hsum0 := Finset.sum_le_sum hterm
  have hsum : ∑ q ∈ S, f q ≤ -2 * ∑ q ∈ S, cosWeight q * Real.sin (zeroOrdinate q * h / 2) ^ 2
      + (δ + 2 * ε₁ + ε₂) * ∑ q ∈ S, cosWeight q := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]; exact hsum0
  have hSw : ∑ q ∈ S, cosWeight q ≤ ∑' q, cosWeight q :=
    Summable.sum_le_tsum S (fun q _ => hwq q) hw
  have hsin : (4 / (5 * Real.pi ^ 2) * h ^ 2)
        * ((S.filter (fun q => |zeroOrdinate q| ≤ 1 / h)).card : ℝ)
      ≤ ∑ q ∈ S, cosWeight q * Real.sin (zeroOrdinate q * h / 2) ^ 2 := by
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun q => cosWeight q * Real.sin (zeroOrdinate q * h / 2) ^ 2)
      (Finset.filter_subset (fun q => |zeroOrdinate q| ≤ 1 / h) S)
      (fun q _ _ => mul_nonneg (hwq q) (sq_nonneg (Real.sin (zeroOrdinate q * h / 2))))
    have hlow : ∀ q ∈ S.filter (fun q => |zeroOrdinate q| ≤ 1 / h),
        4 / (5 * Real.pi ^ 2) * h ^ 2 ≤ cosWeight q * Real.sin (zeroOrdinate q * h / 2) ^ 2 := by
      intro q hq
      have hq' := (Finset.mem_filter.mp hq).2
      have h4 := four_lt_abs_zeroOrdinate q
      exact cosWeight_mul_sin_sq_ge hh (by linarith) hq'
    have := Finset.card_nsmul_le_sum _ _ _ hlow
    rw [nsmul_eq_mul] at this
    linarith
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  have hcoef : 0 ≤ δ + 2 * ε₁ + ε₂ := by linarith
  have hW := mul_le_mul_of_nonneg_left hSw hcoef
  have habs := (abs_le.mp hsplit).2
  rw [hΔ]
  have hfin : ∑' q, f q ≤ 2 * lagTailBound T
      + (-2 * ((4 / (5 * Real.pi ^ 2) * h ^ 2)
          * ((S.filter (fun q => |zeroOrdinate q| ≤ 1 / h)).card : ℝ))
        + (δ + 2 * ε₁ + ε₂) * ∑' q, cosWeight q) := by
    linarith
  have hconst : -(8 / (5 * Real.pi ^ 2)) * h ^ 2
        * ((S.filter (fun q => |zeroOrdinate q| ≤ 1 / h)).card : ℝ)
      = -2 * ((4 / (5 * Real.pi ^ 2) * h ^ 2)
          * ((S.filter (fun q => |zeroOrdinate q| ≤ 1 / h)).card : ℝ)) := by ring
  rw [hconst]
  linarith


/-- **The lag difference at an aligned point, upper window.** -/
theorem lagDifference_ge_of_aligned (hRH : RiemannHypothesis) {T h u ε₁ ε₂ : ℝ} (hT : 4 ≤ T)
    (hh : 0 < h) (hε₁1 : ε₁ ≤ 1) (hε₂ : 0 ≤ ε₂)
    (halign : ∀ q ∈ xiCopiesBelow T,
      1 - ε₁ ≤ Real.cos (zeroOrdinate q * u) ∧ |Real.sin (zeroOrdinate q * u)| ≤ ε₂) :
    (1 - ε₁) * (8 / (5 * Real.pi ^ 2)) * h ^ 2
          * (((xiCopiesBelow T).filter (fun q => |zeroOrdinate q| ≤ 1 / h)).card : ℝ)
        - ((1 - Real.exp (-(h / 2))) + ε₂) * ∑' q, cosWeight q - 2 * lagTailBound T
      ≤ weilLagFunctionReal u * Real.exp (-(h / 2)) - weilLagFunctionReal (u - h) := by
  classical
  have hw := summable_cosWeight hRH
  set f : XiZeroCopy → ℝ := fun q => cosWeight q
    * (Real.exp (-(h / 2)) * Real.cos (zeroOrdinate q * u) - Real.cos (zeroOrdinate q * (u - h)))
    with hfdef
  have hwq : ∀ q, 0 ≤ cosWeight q := fun q => by unfold cosWeight; positivity
  have he1 : Real.exp (-(h / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he0 := Real.exp_pos (-(h / 2))
  have hfb : ∀ q, |f q| ≤ 2 * cosWeight q := by
    intro q
    rw [hfdef, abs_mul, abs_of_nonneg (hwq q)]
    have h1 := Real.abs_cos_le_one (zeroOrdinate q * u)
    have h2 := Real.abs_cos_le_one (zeroOrdinate q * (u - h))
    have h3 : |Real.exp (-(h / 2)) * Real.cos (zeroOrdinate q * u)
        - Real.cos (zeroOrdinate q * (u - h))| ≤ 2 := by
      refine le_trans (abs_sub _ _) ?_
      rw [abs_mul, abs_of_pos he0]
      nlinarith
    nlinarith [hwq q]
  have hΔ : weilLagFunctionReal u * Real.exp (-(h / 2)) - weilLagFunctionReal (u - h)
      = ∑' q, f q := by
    rw [weilLagFunctionReal_eq_cos_series hRH, weilLagFunctionReal_eq_cos_series hRH,
      ← tsum_mul_right, ← Summable.tsum_sub]
    · congr 1; funext q; rw [hfdef]; ring
    · exact Summable.of_norm_bounded hw (fun q => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hwq q), abs_of_pos he0]
        have hc := Real.abs_cos_le_one (zeroOrdinate q * u)
        have h1 := mul_le_mul_of_nonneg_left hc (hwq q)
        have h2 := mul_le_mul h1 he1 he0.le (by rw [mul_one]; exact hwq q)
        linarith)
    · exact Summable.of_norm_bounded hw (fun q => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hwq q)]
        have := Real.abs_cos_le_one (zeroOrdinate q * (u - h))
        nlinarith [hwq q])
  have hsplit := abs_tsum_sub_sum_xiCopiesBelow_le hRH hT hfb
  set S := xiCopiesBelow T with hS
  set δ := 1 - Real.exp (-(h / 2)) with hδ
  have hterm : ∀ q ∈ S,
      2 * (1 - ε₁) * (cosWeight q * Real.sin (zeroOrdinate q * h / 2) ^ 2)
        - (δ + ε₂) * cosWeight q ≤ f q := by
    intro q hq
    have h1 := aligned_term_ge (γ := zeroOrdinate q) (u := u) hh.le (halign q hq).1
      (halign q hq).2
    have h2 := mul_le_mul_of_nonneg_left h1 (hwq q)
    have hfq : f q = cosWeight q * (Real.exp (-(h / 2)) * Real.cos (zeroOrdinate q * u)
        - Real.cos (zeroOrdinate q * (u - h))) := rfl
    rw [hfq]
    nlinarith
  have hsum0 := Finset.sum_le_sum hterm
  have hsum : 2 * (1 - ε₁) * ∑ q ∈ S, cosWeight q * Real.sin (zeroOrdinate q * h / 2) ^ 2
      - (δ + ε₂) * ∑ q ∈ S, cosWeight q ≤ ∑ q ∈ S, f q := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]; exact hsum0
  have hSw : ∑ q ∈ S, cosWeight q ≤ ∑' q, cosWeight q :=
    Summable.sum_le_tsum S (fun q _ => hwq q) hw
  have hsin : (4 / (5 * Real.pi ^ 2) * h ^ 2)
        * ((S.filter (fun q => |zeroOrdinate q| ≤ 1 / h)).card : ℝ)
      ≤ ∑ q ∈ S, cosWeight q * Real.sin (zeroOrdinate q * h / 2) ^ 2 := by
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun q => cosWeight q * Real.sin (zeroOrdinate q * h / 2) ^ 2)
      (Finset.filter_subset (fun q => |zeroOrdinate q| ≤ 1 / h) S)
      (fun q _ _ => mul_nonneg (hwq q) (sq_nonneg (Real.sin (zeroOrdinate q * h / 2))))
    have hlow : ∀ q ∈ S.filter (fun q => |zeroOrdinate q| ≤ 1 / h),
        4 / (5 * Real.pi ^ 2) * h ^ 2 ≤ cosWeight q * Real.sin (zeroOrdinate q * h / 2) ^ 2 := by
      intro q hq
      have hq' := (Finset.mem_filter.mp hq).2
      have h4 := four_lt_abs_zeroOrdinate q
      exact cosWeight_mul_sin_sq_ge hh (by linarith) hq'
    have := Finset.card_nsmul_le_sum _ _ _ hlow
    rw [nsmul_eq_mul] at this
    linarith
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  have hcoef : 0 ≤ δ + ε₂ := by linarith
  have hW := mul_le_mul_of_nonneg_left hSw hcoef
  have habs := (abs_le.mp hsplit).1
  have h1e : 0 ≤ 2 * (1 - ε₁) := by linarith
  have hsin2 := mul_le_mul_of_nonneg_left hsin h1e
  rw [hΔ]
  have hconst : (1 - ε₁) * (8 / (5 * Real.pi ^ 2)) * h ^ 2
        * ((S.filter (fun q => |zeroOrdinate q| ≤ 1 / h)).card : ℝ)
      = 2 * (1 - ε₁) * ((4 / (5 * Real.pi ^ 2) * h ^ 2)
          * ((S.filter (fun q => |zeroOrdinate q| ≤ 1 / h)).card : ℝ)) := by ring
  rw [hconst]
  linarith

end

end RHTower
