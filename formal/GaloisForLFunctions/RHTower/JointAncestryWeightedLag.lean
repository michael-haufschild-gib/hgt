import GaloisForLFunctions.RHTower.JointAncestryDiagonalBochnerLevel
import GaloisForLFunctions.RHTower.DeningerDivisorSchwarzMonodromy

/-!
# Dressed lag functions

A *dressing* is a function `g` on `ℂ`, bounded by `K` and nonvanishing at the zeros of `ξ`, with
`g(s̄) = conj g(s)` and `g(1 − s) = g(s)`.  The dressed lag function is

`Φ_g(L) = Σ_ρ g(ρ) e^{(ρ−½)L}/(ρ(1−ρ))`.

It is real (`dLag_eq_ofReal`, from the conjugation symmetry of the zeros) and even (`dLag_neg`,
from the functional-equation reflection).  Since `|g(ρ)| ≤ K`, it inherits the bounds of the
undressed lag function: `|Φ_g(L)| ≤ K W e^{|L|/2}` and the coherence estimate on short windows
(`abs_dLagReal_add_sub_le`).

Examples are the Gaussian `g(s) = e^{τ(s−½)²}`, the Mellin transform of a Gaussian kernel, and
`g(s) = φ(|Im s|)` for a positive function `φ`.
-/

open Complex Filter
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- A dressing of the zero weights. -/
structure LagDressing where
  g : ℂ → ℂ
  K : ℝ
  K_nonneg : 0 ≤ K
  norm_le : ∀ q : XiZeroCopy, ‖g (q.1 : ℂ)‖ ≤ K
  ne_zero : ∀ q : XiZeroCopy, g (q.1 : ℂ) ≠ 0
  conj_eq : ∀ s : ℂ, g (conj s) = conj (g s)
  reflect_eq : ∀ s : ℂ, g (1 - s) = g s

namespace LagDressing

variable (D : LagDressing)

/-- The dressed weight `g(ρ)/(ρ(1−ρ))`. -/
def weight (q : XiZeroCopy) : ℂ := D.g (q.1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))

theorem weight_eq (q : XiZeroCopy) :
    D.weight q = D.g (q.1 : ℂ) * (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
  unfold weight; ring

theorem norm_weight_le (q : XiZeroCopy) :
    ‖D.weight q‖ ≤ D.K * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
  rw [weight_eq, norm_mul]
  exact mul_le_mul_of_nonneg_right (D.norm_le q) (norm_nonneg _)

theorem summable_norm_weight : Summable fun q : XiZeroCopy => ‖D.weight q‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) D.norm_weight_le
    (summable_inv_mul_one_sub.norm.mul_left _)

theorem weight_ne_zero (q : XiZeroCopy) : D.weight q ≠ 0 := by
  unfold weight
  exact div_ne_zero (D.ne_zero q) (mul_ne_zero (xiZeroCopy_ne_zero q) (xiZeroCopy_one_sub_ne_zero q))

/-- The total dressed weight `Σ_ρ |g(ρ)|/|ρ(1−ρ)|`. -/
def total : ℝ := ∑' q : XiZeroCopy, ‖D.weight q‖

theorem total_nonneg : 0 ≤ D.total := tsum_nonneg fun _ => norm_nonneg _

theorem total_le : D.total ≤ D.K * lagWeightTotal := by
  unfold total lagWeightTotal
  rw [← tsum_mul_left]
  exact D.summable_norm_weight.tsum_le_tsum (fun q => D.norm_weight_le q)
    (summable_norm_lagWeight.mul_left _)

end LagDressing

/-! ## The dressed lag function -/

/-- `Φ_g(L) = Σ_ρ e^{L(ρ−½)} g(ρ)/(ρ(1−ρ))`. -/
def dLag (D : LagDressing) (L : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) * D.weight q

theorem norm_cexp_lag_le (L : ℝ) (q : XiZeroCopy) :
    ‖Complex.exp (L * ((q.1 : ℂ) - 1 / 2))‖ ≤ Real.exp (|L| / 2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  have hre : ((L : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = L * ((q.1 : ℂ).re - 1 / 2) := by
    simp [Complex.mul_re]
  rw [hre]
  have hb : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  calc L * ((q.1 : ℂ).re - 1 / 2) ≤ |L * ((q.1 : ℂ).re - 1 / 2)| := le_abs_self _
    _ = |L| * |(q.1 : ℂ).re - 1 / 2| := abs_mul _ _
    _ ≤ |L| * (1 / 2) := by gcongr
    _ = |L| / 2 := by ring

theorem norm_dLagTerm_le (D : LagDressing) (L : ℝ) (q : XiZeroCopy) :
    ‖Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) * D.weight q‖ ≤ Real.exp (|L| / 2) * ‖D.weight q‖ := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_cexp_lag_le L q) (norm_nonneg _)

theorem summable_dLagTerm (D : LagDressing) (L : ℝ) :
    Summable fun q : XiZeroCopy => Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) * D.weight q :=
  Summable.of_norm_bounded (D.summable_norm_weight.mul_left _) (norm_dLagTerm_le D L)

theorem norm_dLag_le (D : LagDressing) (L : ℝ) : ‖dLag D L‖ ≤ Real.exp (|L| / 2) * D.total := by
  unfold dLag LagDressing.total
  rw [← tsum_mul_left]
  exact (norm_tsum_le_tsum_norm (summable_dLagTerm D L).norm).trans
    ((summable_dLagTerm D L).norm.tsum_le_tsum (norm_dLagTerm_le D L)
      (D.summable_norm_weight.mul_left _))

/-- `Φ_g` is even. -/
theorem dLag_neg (D : LagDressing) (L : ℝ) : dLag D (-L) = dLag D L := by
  unfold dLag
  rw [← xiZeroCopyReflectEquiv.tsum_eq (fun q : XiZeroCopy =>
    Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) * D.weight q)]
  refine tsum_congr fun q => ?_
  unfold LagDressing.weight
  rw [xiZeroCopy_reflect_val, D.reflect_eq]
  congr 1
  · congr 1; push_cast; ring
  · ring

/-- `Φ_g` is real. -/
theorem conj_dLag (D : LagDressing) (L : ℝ) : conj (dLag D L) = dLag D L := by
  unfold dLag
  rw [Complex.conj_tsum, ← xiZeroCopyConjEquiv.tsum_eq (fun q : XiZeroCopy =>
    conj (Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) * D.weight q))]
  refine tsum_congr fun q => ?_
  have hq : ((xiZeroCopyConjEquiv q).1 : ℂ) = conj (q.1 : ℂ) := rfl
  unfold LagDressing.weight
  rw [hq, map_mul, map_div₀, ← Complex.exp_conj, ← D.conj_eq, map_mul, map_sub, map_mul,
    map_sub, Complex.conj_conj, map_one, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]

theorem dLag_im_eq_zero (D : LagDressing) (L : ℝ) : (dLag D L).im = 0 := by
  have h := congrArg Complex.im (conj_dLag D L)
  rw [Complex.conj_im] at h
  linarith

/-- The real dressed lag function. -/
def dLagReal (D : LagDressing) (L : ℝ) : ℝ := (dLag D L).re

theorem dLag_eq_ofReal (D : LagDressing) (L : ℝ) : dLag D L = (dLagReal D L : ℂ) :=
  Complex.ext rfl (by rw [Complex.ofReal_im, dLag_im_eq_zero])

theorem dLagReal_neg (D : LagDressing) (L : ℝ) : dLagReal D (-L) = dLagReal D L := by
  unfold dLagReal; rw [dLag_neg]

theorem abs_dLagReal_le (D : LagDressing) (L : ℝ) :
    |dLagReal D L| ≤ Real.exp (|L| / 2) * D.total := by
  rw [← Real.norm_eq_abs, ← Complex.norm_real, ← dLag_eq_ofReal]
  exact norm_dLag_le D L

theorem dLag_zero (D : LagDressing) : dLag D 0 = ∑' q : XiZeroCopy, D.weight q := by
  unfold dLag
  simp

theorem measurable_dLag (D : LagDressing) : Measurable (dLag D) := by
  unfold dLag
  refine Measurable.tsum fun q => ?_
  exact (Complex.measurable_exp.comp (Complex.measurable_ofReal.mul_const _)).mul_const _

theorem measurable_dLagReal (D : LagDressing) : Measurable (dLagReal D) :=
  Complex.measurable_re.comp (measurable_dLag D)

/-! ## Coherence on short windows -/

/-- **Coherence.**  For `0 ≤ y ≤ 1` and `T ≥ 1`,
`|Φ_g(u + y) − Φ_g(u)| ≤ K e^{αu} · 2e^{½}((½ + T) y W + 80(C + log(3T + 4))/T)`. -/
theorem abs_dLagReal_add_sub_le (D : LagDressing) {α : ℝ}
    (hα : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ α) {u y T : ℝ} (hu : 0 ≤ u) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) (hT : 1 ≤ T) :
    |dLagReal D (u + y) - dLagReal D u| ≤
      D.K * (Real.exp (α * u) * (2 * Real.exp (1 / 2) * ((1 / 2 + T) * y * lagWeightTotal +
        80 * (xiLineTwoLogDerivConstant + Real.log (3 * T + 4)) / T))) := by
  rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sub, ← dLag_eq_ofReal,
    ← dLag_eq_ofReal]
  unfold dLag
  rw [← (summable_dLagTerm D (u + y)).tsum_sub (summable_dLagTerm D u)]
  obtain ⟨g, hgdef⟩ : ∃ g : XiZeroCopy → ℝ, g = fun q =>
      2 * Real.exp (1 / 2) * ((1 / 2 + T) * y * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ +
        {q : XiZeroCopy | T < |(q.1 : ℂ).im|}.indicator
          (fun q => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) q) := ⟨_, rfl⟩
  have hterm : ∀ q : XiZeroCopy,
      ‖Complex.exp (((u + y : ℝ) : ℂ) * ((q.1 : ℂ) - 1 / 2)) * D.weight q -
        Complex.exp ((u : ℂ) * ((q.1 : ℂ) - 1 / 2)) * D.weight q‖ ≤
        D.K * (Real.exp (α * u) * g q) := by
    intro q
    have hab := hα q
    have e : Complex.exp (((u + y : ℝ) : ℂ) * ((q.1 : ℂ) - 1 / 2)) * D.weight q -
        Complex.exp ((u : ℂ) * ((q.1 : ℂ) - 1 / 2)) * D.weight q =
        D.g (q.1 : ℂ) * (Complex.exp ((u : ℂ) * ((q.1 : ℂ) - 1 / 2)) *
          (Complex.exp ((y : ℂ) * ((q.1 : ℂ) - 1 / 2)) - 1) *
            (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))))) := by
      rw [LagDressing.weight_eq, show ((u + y : ℝ) : ℂ) * ((q.1 : ℂ) - 1 / 2) =
        (u : ℂ) * ((q.1 : ℂ) - 1 / 2) + (y : ℂ) * ((q.1 : ℂ) - 1 / 2) by push_cast; ring,
        Complex.exp_add]
      ring
    rw [e, norm_mul]
    refine mul_le_mul (D.norm_le q) ?_ (norm_nonneg _) D.K_nonneg
    rw [norm_mul, norm_mul, Complex.norm_exp]
    have hre1 : ((u : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = u * ((q.1 : ℂ).re - 1 / 2) := by
      simp [Complex.mul_re]
    have hre2 : ((y : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = y * ((q.1 : ℂ).re - 1 / 2) := by
      simp [Complex.mul_re]
    have hb : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith [xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q]
    have h1 : Real.exp ((u : ℂ) * ((q.1 : ℂ) - 1 / 2)).re ≤ Real.exp (α * u) := by
      rw [hre1]
      apply Real.exp_le_exp.mpr
      have := abs_le.mp hab
      nlinarith
    have hz : |((y : ℂ) * ((q.1 : ℂ) - 1 / 2)).re| ≤ 1 / 2 := by
      rw [hre2, abs_mul, abs_of_nonneg hy0]
      nlinarith [abs_nonneg ((q.1 : ℂ).re - 1 / 2)]
    have h2 := norm_cexp_sub_one_le_min hz
    have hw := norm_nonneg (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))))
    have hmin : min 1 ‖(y : ℂ) * ((q.1 : ℂ) - 1 / 2)‖ * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤
        (1 / 2 + T) * y * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ +
          {q : XiZeroCopy | T < |(q.1 : ℂ).im|}.indicator
            (fun q => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) q := by
      by_cases hq : T < |(q.1 : ℂ).im|
      · rw [Set.indicator_of_mem (show q ∈ {q : XiZeroCopy | T < |(q.1 : ℂ).im|} from hq)]
        have : min 1 ‖(y : ℂ) * ((q.1 : ℂ) - 1 / 2)‖ ≤ 1 := min_le_left _ _
        have h0 : 0 ≤ (1 / 2 + T) * y * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by positivity
        nlinarith
      · rw [Set.indicator_of_notMem (show q ∉ {q : XiZeroCopy | T < |(q.1 : ℂ).im|} from hq),
          add_zero]
        push Not at hq
        have hnz : ‖(y : ℂ) * ((q.1 : ℂ) - 1 / 2)‖ ≤ (1 / 2 + T) * y := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy0]
          have hn := Complex.norm_le_abs_re_add_abs_im ((q.1 : ℂ) - 1 / 2)
          simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
            Complex.div_ofNat_re, Complex.div_ofNat_im, zero_div, sub_zero] at hn
          nlinarith [abs_nonneg ((q.1 : ℂ).im)]
        have := (min_le_right 1 ‖(y : ℂ) * ((q.1 : ℂ) - 1 / 2)‖).trans hnz
        exact mul_le_mul_of_nonneg_right this hw
    rw [hgdef]
    calc Real.exp ((u : ℂ) * ((q.1 : ℂ) - 1 / 2)).re *
          ‖Complex.exp ((y : ℂ) * ((q.1 : ℂ) - 1 / 2)) - 1‖ * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖
        ≤ Real.exp (α * u) * (2 * Real.exp (1 / 2) * min 1 ‖(y : ℂ) * ((q.1 : ℂ) - 1 / 2)‖) *
            ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by gcongr
      _ = Real.exp (α * u) * (2 * Real.exp (1 / 2) *
            (min 1 ‖(y : ℂ) * ((q.1 : ℂ) - 1 / 2)‖ * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖)) := by ring
      _ ≤ _ := by beta_reduce; gcongr
  have hgs : Summable g := by
    rw [hgdef]
    exact ((summable_inv_mul_one_sub.norm.mul_left _).add
      (summable_inv_mul_one_sub.norm.indicator _)).mul_left _
  have hgs' : Summable fun q => D.K * (Real.exp (α * u) * g q) := (hgs.mul_left _).mul_left _
  have hsum : Summable fun q : XiZeroCopy =>
      Complex.exp (((u + y : ℝ) : ℂ) * ((q.1 : ℂ) - 1 / 2)) * D.weight q -
        Complex.exp ((u : ℂ) * ((q.1 : ℂ) - 1 / 2)) * D.weight q :=
    Summable.of_norm_bounded hgs' hterm
  refine (norm_tsum_le_tsum_norm hsum.norm).trans ?_
  refine (Summable.tsum_le_tsum hterm hsum.norm hgs').trans ?_
  rw [tsum_mul_left, tsum_mul_left, hgdef, tsum_mul_left,
    (summable_inv_mul_one_sub.norm.mul_left _).tsum_add (summable_inv_mul_one_sub.norm.indicator _),
    tsum_mul_left]
  have htail := tsum_indicator_abs_im_gt_weight_le hT
  have hW : ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ = lagWeightTotal := rfl
  rw [hW]
  have hexp := Real.exp_pos (α * u)
  have he := Real.exp_pos (1 / 2 : ℝ)
  have hK := D.K_nonneg
  gcongr

end

end RHTower
