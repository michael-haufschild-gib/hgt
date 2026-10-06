import GaloisForLFunctions.RHTower.KuznetsovSameSignWeightOfOdd
import GaloisForLFunctions.HTGeometry.BesselTestFunctionSineTransform
import GaloisForLFunctions.HTGeometry.ExponentialSeriesSmooth

/-!
# The same-sign weight of a test function orthogonal to `J_1`

Let `φ` be a smooth test function supported in `[a, b]`, `a > 0`, with Bessel coefficients
`φ̃(l) = ∫ J_l(y) φ(y) dy/y`, sine transform `S(u) = ∫ φ(y) sin(yu) dy/y` and
`P(x) = ∑_k (-1)^k φ̃(2k+1) x^{2k+1}`.  If `φ̃(1) = 0`, the profile

`G_φ(w) = (cosh w/4) S(cosh w) - (cosh w/2) P(e^{-w}) = (cosh w/4) (P(e^w) - P(e^{-w}))`

is odd (`besselProfile_neg`).  Its first part lies in the span `𝒜_{1/2π}` of the functions
`cosh^a sinh^b χ(cosh/2π)` and decays faster than any exponential; since `φ̃(1) = 0`, its second
part is the exponential series `(1/4) ∑_k c_{k+1} (e^{-(2k+2)w} + e^{-(2k+4)w})`,
`c_k = (-1)^k φ̃(2k+1)`.  Hence all derivatives of `G_φ` are `O(e^{-2w})` on `w ≥ 0`, and `G_φ` is
an `OddDecayProfile`: it defines a rapid same-sign weight (`besselWeight`, `besselWeight_isRapid`).
-/

open MeasureTheory Set Filter Topology Complex
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower.DeckPointPair

noncomputable section

variable (T : BesselTestFunction)

/-- `c_k = (-1)^k φ̃(2k+1)`. -/
def besselOddCoeff (k : ℕ) : ℂ := (-1) ^ k * T.besselCoeff (2 * k + 1)

theorem norm_besselOddCoeff_le (k : ℕ) :
    ‖besselOddCoeff T k‖ ≤ T.besselMajor (2 * k + 1) * ∫ y, ‖T.ψ y‖ := by
  rw [besselOddCoeff, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact T.norm_besselCoeff_le _

/-- The coefficients `c_{k+1}/4` of the exponential tail. -/
def tailCoeff (k : ℕ) : ℂ := besselOddCoeff T (k + 1) / 4

theorem expSeriesAdmissible_tailCoeff (j : ℝ) (hj0 : 0 ≤ j) (hj : j ≤ 4) :
    ExpSeriesAdmissible (tailCoeff T) (fun k => (2 * k + j : ℝ)) := by
  intro n R
  set r := Real.exp (2 * (1 + |R|))
  set I := ∫ y, ‖T.ψ y‖
  have hI : 0 ≤ I := integral_nonneg fun _ => norm_nonneg _
  have hs := ((T.summable_besselMajor_mul_pow r).comp_injective Nat.succ_injective).mul_right
    (n.factorial / 4 * I)
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hs
  simp only [Function.comp, Nat.succ_eq_add_one]
  have hm0 : (0 : ℝ) ≤ 2 * k + j := by positivity
  rw [abs_of_nonneg hm0]
  have hpow : ((2 * k + j : ℝ)) ^ n ≤ n.factorial * Real.exp (2 * k + j) := by
    have := Real.pow_div_factorial_le_exp (2 * k + j : ℝ) hm0 n
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hexp : Real.exp (2 * k + j) * Real.exp ((2 * k + j) * R) ≤ r ^ (2 * (k + 1) + 1) := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    have hR : (2 * k + j) * R ≤ (2 * k + j) * |R| :=
      mul_le_mul_of_nonneg_left (le_abs_self R) hm0
    push_cast
    nlinarith [abs_nonneg R, hj]
  have hc := norm_besselOddCoeff_le T (k + 1)
  rw [tailCoeff, norm_div, Complex.norm_ofNat]
  calc ‖besselOddCoeff T (k + 1)‖ / 4 * (2 * k + j : ℝ) ^ n * Real.exp ((2 * k + j) * R)
      ≤ (T.besselMajor (2 * (k + 1) + 1) * I) / 4 * (n.factorial * Real.exp (2 * k + j)) *
          Real.exp ((2 * k + j) * R) := by
        gcongr
        exact div_nonneg (mul_nonneg (T.besselMajor_nonneg _) hI) (by norm_num)
    _ = T.besselMajor (2 * (k + 1) + 1) * (n.factorial / 4 * I) *
          (Real.exp (2 * k + j) * Real.exp ((2 * k + j) * R)) := by ring
    _ ≤ T.besselMajor (2 * (k + 1) + 1) * (n.factorial / 4 * I) * r ^ (2 * (k + 1) + 1) := by
        gcongr
        exact mul_nonneg (T.besselMajor_nonneg _) (by positivity)
    _ = _ := by ring

/-- The tail `G_P(w) = (1/4) ∑_k c_{k+1} (e^{-(2k+2)w} + e^{-(2k+4)w})`. -/
def tailProfile : ℝ → ℂ :=
  expSeries (tailCoeff T) (fun k => (2 * k + 2 : ℝ)) + expSeries (tailCoeff T) (fun k => (2 * k + 4 : ℝ))

/-- The main part `G_F(w) = (cosh w/4) S(cosh w)`. -/
def mainProfile (w : ℝ) : ℂ := (Real.cosh w : ℂ) * T.sineTransform (Real.cosh w) / 4

/-- The profile `G_φ = G_F - G_P`. -/
def besselProfile : ℝ → ℂ := mainProfile T - tailProfile T

theorem mainProfile_mem : mainProfile T ∈ coshSchwartzSpan (1 / (2 * Real.pi)) := by
  have := Submodule.smul_mem _ (1 / 4 : ℂ) T.cosh_mul_sineTransform_cosh_mem
  convert this using 1
  funext w
  simp only [mainProfile, Pi.smul_apply, smul_eq_mul]
  ring

theorem oddSeries_eq_tail (h1 : T.besselCoeff 1 = 0) (x : ℝ) :
    T.oddSeries x = ∑' k : ℕ, besselOddCoeff T (k + 1) * ((x ^ (2 * (k + 1) + 1) : ℝ) : ℂ) := by
  rw [BesselTestFunction.oddSeries, (T.summable_oddSeries x).tsum_eq_zero_add]
  simp only [pow_zero, one_mul, Nat.mul_zero, zero_add, h1, zero_mul, besselOddCoeff]

/-- **`G_P(w) = (cosh w/2) P(e^{-w})`** when `φ̃(1) = 0`. -/
theorem tailProfile_eq (h1 : T.besselCoeff 1 = 0) (w : ℝ) :
    tailProfile T w = (Real.cosh w : ℂ) / 2 * T.oddSeries (Real.exp (-w)) := by
  have hs1 := summable_expSeries (expSeriesAdmissible_tailCoeff T 2 (by norm_num) (by norm_num)) w
  have hs2 := summable_expSeries (expSeriesAdmissible_tailCoeff T 4 (by norm_num) le_rfl) w
  rw [oddSeries_eq_tail T h1, tailProfile, Pi.add_apply, expSeries, expSeries,
    ← hs1.tsum_add hs2, ← tsum_mul_left]
  congr 1; funext k
  have e1 : Real.exp (-((2 * k + 2 : ℝ) * w)) = Real.exp w * Real.exp (-w) ^ (2 * (k + 1) + 1) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have e2 : Real.exp (-((2 * k + 4 : ℝ) * w)) = Real.exp (-w) * Real.exp (-w) ^ (2 * (k + 1) + 1) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  rw [e1, e2, tailCoeff]
  push_cast
  rw [Complex.cosh]
  ring

theorem mainProfile_eq (w : ℝ) :
    mainProfile T w = (Real.cosh w : ℂ) / 4 * (T.oddSeries (Real.exp w) + T.oddSeries (Real.exp (-w))) := by
  rw [mainProfile, T.sineTransform_cosh_eq]; ring

/-- **`G_φ(w) = (cosh w/4)(P(e^w) - P(e^{-w}))`.** -/
theorem besselProfile_eq (h1 : T.besselCoeff 1 = 0) (w : ℝ) :
    besselProfile T w =
      (Real.cosh w : ℂ) / 4 * (T.oddSeries (Real.exp w) - T.oddSeries (Real.exp (-w))) := by
  rw [besselProfile, Pi.sub_apply, mainProfile_eq, tailProfile_eq T h1]; ring

theorem besselProfile_neg (h1 : T.besselCoeff 1 = 0) (w : ℝ) :
    besselProfile T (-w) = -besselProfile T w := by
  rw [besselProfile_eq T h1, besselProfile_eq T h1, Real.cosh_neg, neg_neg]; ring

theorem contDiff_mainProfile (n : ℕ) : ContDiff ℝ n (mainProfile T) :=
  contDiff_of_mem_coshSchwartzSpan (mainProfile_mem T) n

theorem contDiff_tailProfile (n : ℕ) : ContDiff ℝ n (tailProfile T) :=
  (contDiff_expSeries (expSeriesAdmissible_tailCoeff T 2 (by norm_num) (by norm_num)) n).add
    (contDiff_expSeries (expSeriesAdmissible_tailCoeff T 4 (by norm_num) le_rfl) n)

theorem contDiff_besselProfile (n : ℕ) : ContDiff ℝ n (besselProfile T) :=
  (contDiff_mainProfile T n).sub (contDiff_tailProfile T n)

theorem exists_bound_iteratedDeriv_tailProfile (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w, 0 ≤ w →
      ‖iteratedDeriv n (tailProfile T) w‖ ≤ C * Real.exp (-(2 * w)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_bound_iteratedDeriv_expSeries
    (expSeriesAdmissible_tailCoeff T 2 (by norm_num) (by norm_num)) (μ := 2) (fun k => by
      have : (0 : ℝ) ≤ k := k.cast_nonneg
      linarith) n
  obtain ⟨C₂, hC₂, h₂⟩ := exists_bound_iteratedDeriv_expSeries
    (expSeriesAdmissible_tailCoeff T 4 (by norm_num) le_rfl) (μ := 2) (fun k => by
      have : (0 : ℝ) ≤ k := k.cast_nonneg
      linarith) n
  refine ⟨C₁ + C₂, by positivity, fun w hw => ?_⟩
  rw [tailProfile, iteratedDeriv_add
    ((contDiff_expSeries (expSeriesAdmissible_tailCoeff T 2 (by norm_num) (by norm_num)) n).contDiffAt)
    ((contDiff_expSeries (expSeriesAdmissible_tailCoeff T 4 (by norm_num) le_rfl) n).contDiffAt)]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ C₁ * Real.exp (-(2 * w)) + C₂ * Real.exp (-(2 * w)) := add_le_add (h₁ w hw) (h₂ w hw)
    _ = _ := by ring

theorem exists_bound_iteratedDeriv_besselProfile (n : ℕ) :
    ∃ C : ℝ, ∀ w, 0 ≤ w → ‖iteratedDeriv n (besselProfile T) w‖ ≤ C * Real.exp (-(2 * w)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_bound_iteratedDeriv_of_mem_coshSchwartzSpan
    (by positivity : (1 / (2 * Real.pi) : ℝ) ≠ 0) (mainProfile_mem T) n 2
  obtain ⟨C₂, hC₂, h₂⟩ := exists_bound_iteratedDeriv_tailProfile T n
  refine ⟨C₁ + C₂, fun w hw => ?_⟩
  rw [besselProfile, iteratedDeriv_sub (contDiff_mainProfile T n).contDiffAt
    (contDiff_tailProfile T n).contDiffAt]
  have h1 := h₁ w
  rw [abs_of_nonneg hw] at h1
  push_cast at h1
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ C₁ * Real.exp (-(2 * w)) + C₂ * Real.exp (-(2 * w)) := add_le_add h1 (h₂ w hw)
    _ = _ := by ring

/-- The odd profile `G_φ`. -/
def besselOddProfile (h1 : T.besselCoeff 1 = 0) : OddDecayProfile where
  G := besselProfile T
  contDiff := contDiff_besselProfile T
  odd := besselProfile_neg T h1
  decay := exists_bound_iteratedDeriv_besselProfile T

/-- **The same-sign weight of `φ`**, for `φ̃(1) = 0`. -/
def besselWeight (h1 : T.besselCoeff 1 = 0) : SameSignWeight := (besselOddProfile T h1).toWeight

theorem besselWeight_G (h1 : T.besselCoeff 1 = 0) : (besselWeight T h1).G = besselProfile T := rfl

theorem besselWeight_isRapid (h1 : T.besselCoeff 1 = 0) : (besselWeight T h1).IsRapid :=
  (besselOddProfile T h1).isRapid

end

end GaloisForLFunctions.RHTower.DeckPointPair
