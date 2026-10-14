import GaloisForLFunctions.RHTower.CosDilationBlindSesquiSupportVanishing
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex

/-!
# Blind cores of support ratio below the golden ratio vanish

Let `f` be continuous and supported in `[α, β]` with `0 < α ≤ β`, dilation autocorrelation `A_f`,
and cosine–dilation kernel `Ψ_f = Cf ⋆ f` vanishing at every integer `n ≥ 2`.

**Theorem** (`eq_zero_of_cosDilationKernel_blind_of_golden`).  If `β² < αβ + α²`, i.e. the
support ratio `R = β/α` is below the golden ratio `(1 + √5)/2`, then `f = 0`.  No hypothesis on
`Ψ_f(0)` (the mean) is needed.  This extends
`eq_zero_of_cosDilationKernel_blind_of_lt_three_halves_mul` (`R < 3/2`).

**The Farey recursion.**  Put `H(v) = A_f(1 − 1/v)/v`.  For `v ≥ 2` with `v(2α − β) ≥ α`, Poisson
periodization at `x = 1 − 1/v` keeps only the translates `1 − 1/v` and `1 + 1/v`, and the inversion
law `A_f(1/r) = r A_f(r)` turns the second into `v/(v+1) · A_f(1 − 1/(v+1))`.  Hence
(`dilationAutocorr_farey_recursion`)

`H(v) + H(v + 1) = (Ψ_f(0) + 2Ψ_f(1) cos(2π/v))/v`.

In the variable `u = 1 − 1/v` this is the transfer equation at `s = ½` of the parabolic Farey
branch `u ↦ 1/(2 − u)`; the second branch `u ↦ 1/(1 + u)` lands below `α/β` exactly when
`v(2α − β) ≥ α`.

**Proof.**
* *Decaying solutions are unique.*  The explicit series
  `F(v) = a·Σ_k 1/((v+2k)(v+2k+1)) + b·Σ_i (−1)^i (cos(2π/(v+i)) − 1)/(v+i)`, with
  `a = Ψ_f(0) + 2Ψ_f(1)` and `b = 2Ψ_f(1)`, satisfies the same recursion and tends to `0`, as does
  `H`.  The difference alternates in sign along `v + ℕ` and tends to `0`, so `H = F`
  (`goldenSeries_eq`).
* *A zero interval.*  `H(v) = 0` when `1 − 1/v ≤ α/β`.  The recursion holds for
  `v ≥ max(2, α/(2α − β))`, the vanishing for `v ≤ β/(β − α)`, and
  `α/(2α − β) < β/(β − α) ⟺ β² < αβ + α²`.  So `F` vanishes on an interval.
* *Analytic continuation.*  `F` extends holomorphically to `Re z > ½`
  (`differentiableOn_altHarmonic`, `differentiableOn_altCosDefect`), so it vanishes identically
  there.  The recursion then gives `(Ψ_f(0) + 2Ψ_f(1) cos(2π/v))/v = 0` for all `v ≥ 1`.  At
  `v = 2` and `v = 4` this forces `Ψ_f(0) = Ψ_f(1) = 0`, and the short-core rigidity theorem
  finishes.
-/

open MeasureTheory Set Real Filter Topology

namespace RHTower

noncomputable section

/-! ### Complex bounds -/

/-- The half-plane `Re z > ½`. -/
def halfPlaneHalf : Set ℂ := {z | 1 / 2 < z.re}

theorem isOpen_halfPlaneHalf : IsOpen halfPlaneHalf :=
  isOpen_lt continuous_const Complex.continuous_re

theorem half_add_le_norm_add {z : ℂ} (hz : z ∈ halfPlaneHalf) (c : ℝ) :
    1 / 2 + c ≤ ‖z + (c : ℂ)‖ := by
  have h1 : (z + (c : ℂ)).re = z.re + c := by simp
  have h2 := Complex.re_le_norm (z + (c : ℂ))
  have hz' : 1 / 2 < z.re := hz
  linarith

theorem add_ne_zero_of_mem_halfPlaneHalf {z : ℂ} (hz : z ∈ halfPlaneHalf) {c : ℝ} (hc : 0 ≤ c) :
    z + (c : ℂ) ≠ 0 := by
  intro h
  have := half_add_le_norm_add hz c
  rw [h, norm_zero] at this
  linarith

theorem norm_cos_le_exp_norm (x : ℂ) : ‖Complex.cos x‖ ≤ Real.exp ‖x‖ := by
  have h2 := Complex.two_cos (x := x)
  have e1 : ‖Complex.exp (x * Complex.I)‖ ≤ Real.exp ‖x‖ := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have : (x * Complex.I).re = -x.im := by simp
    rw [this]
    linarith [neg_abs_le x.im, Complex.abs_im_le_norm x]
  have e2 : ‖Complex.exp (-x * Complex.I)‖ ≤ Real.exp ‖x‖ := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have : (-x * Complex.I).re = x.im := by simp
    rw [this]
    linarith [le_abs_self x.im, Complex.abs_im_le_norm x]
  have : ‖(2 : ℂ) * Complex.cos x‖ ≤ 2 * Real.exp ‖x‖ := by
    rw [h2]
    calc ‖Complex.exp (x * Complex.I) + Complex.exp (-x * Complex.I)‖
        ≤ ‖Complex.exp (x * Complex.I)‖ + ‖Complex.exp (-x * Complex.I)‖ := norm_add_le _ _
      _ ≤ 2 * Real.exp ‖x‖ := by linarith
  rw [norm_mul, Complex.norm_two] at this
  linarith

/-- `‖cos x − 1‖ ≤ (e^{4π} + 1)‖x‖²` for `‖x‖ ≤ 4π`. -/
theorem norm_cos_sub_one_le {x : ℂ} (hx : ‖x‖ ≤ 4 * π) :
    ‖Complex.cos x - 1‖ ≤ (Real.exp (4 * π) + 1) * ‖x‖ ^ 2 := by
  have hM : 1 ≤ Real.exp (4 * π) + 1 := by
    have := Real.exp_pos (4 * π); linarith
  rcases le_or_gt ‖x‖ 1 with h1 | h1
  · have hI : ‖x * Complex.I‖ = ‖x‖ := by rw [norm_mul, Complex.norm_I, mul_one]
    have hI' : ‖-x * Complex.I‖ = ‖x‖ := by rw [norm_mul, norm_neg, Complex.norm_I, mul_one]
    have a1 := Complex.norm_exp_sub_one_sub_id_le (x := x * Complex.I) (by rw [hI]; exact h1)
    have a2 := Complex.norm_exp_sub_one_sub_id_le (x := -x * Complex.I) (by rw [hI']; exact h1)
    rw [hI] at a1
    rw [hI'] at a2
    have hsplit : (2 : ℂ) * (Complex.cos x - 1) =
        (Complex.exp (x * Complex.I) - 1 - x * Complex.I) +
          (Complex.exp (-x * Complex.I) - 1 - -x * Complex.I) := by
      rw [mul_sub, Complex.two_cos]; ring
    have : ‖(2 : ℂ) * (Complex.cos x - 1)‖ ≤ 2 * ‖x‖ ^ 2 := by
      rw [hsplit]
      exact (norm_add_le _ _).trans (by linarith)
    rw [norm_mul, Complex.norm_two] at this
    nlinarith [sq_nonneg ‖x‖]
  · have hc := norm_cos_le_exp_norm x
    have he : Real.exp ‖x‖ ≤ Real.exp (4 * π) := Real.exp_le_exp.mpr hx
    have hx2 : 1 ≤ ‖x‖ ^ 2 := by nlinarith
    calc ‖Complex.cos x - 1‖ ≤ ‖Complex.cos x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ Real.exp (4 * π) + 1 := by rw [norm_one]; linarith
      _ ≤ (Real.exp (4 * π) + 1) * ‖x‖ ^ 2 := le_mul_of_one_le_right (by linarith) hx2

/-! ### The two alternating series -/

/-- Paired terms of `Σ (−1)^i/(z + i)`. -/
def altHarmonicTerm (z : ℂ) (k : ℕ) : ℂ := 1 / ((z + (2 * k : ℝ)) * (z + (2 * k + 1 : ℝ)))

def altHarmonic (z : ℂ) : ℂ := ∑' k : ℕ, altHarmonicTerm z k

/-- The cosine defect `(cos(2π/w) − 1)/w`. -/
def cosDefect (w : ℂ) : ℂ := (Complex.cos (2 * π / w) - 1) / w

def altCosDefectTerm (z : ℂ) (i : ℕ) : ℂ := (-1 : ℂ) ^ i * cosDefect (z + (i : ℝ))

def altCosDefect (z : ℂ) : ℂ := ∑' i : ℕ, altCosDefectTerm z i

theorem summable_inv_succ_sq : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  refine h.congr fun k => ?_
  push_cast
  ring

theorem norm_altHarmonicTerm_le {z : ℂ} (hz : z ∈ halfPlaneHalf) (k : ℕ) :
    ‖altHarmonicTerm z k‖ ≤ 4 / 3 * (1 / ((k : ℝ) + 1) ^ 2) := by
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have h1 := half_add_le_norm_add hz (2 * k)
  have h2 := half_add_le_norm_add hz (2 * k + 1)
  rw [altHarmonicTerm, norm_div, norm_one, norm_mul]
  have hp : 0 < (1 / 2 + 2 * (k : ℝ)) * (1 / 2 + (2 * k + 1)) := by positivity
  calc 1 / (‖z + ((2 * k : ℝ) : ℂ)‖ * ‖z + ((2 * k + 1 : ℝ) : ℂ)‖)
      ≤ 1 / ((1 / 2 + 2 * (k : ℝ)) * (1 / 2 + (2 * k + 1))) := by
        apply one_div_le_one_div_of_le hp
        exact mul_le_mul h1 h2 (by positivity) (by positivity)
    _ ≤ 4 / 3 * (1 / ((k : ℝ) + 1) ^ 2) := by
        rw [show (4 / 3 : ℝ) * (1 / ((k : ℝ) + 1) ^ 2) = 4 / (3 * ((k : ℝ) + 1) ^ 2) by
          field_simp, div_le_div_iff₀ hp (by positivity)]
        nlinarith

theorem norm_altCosDefectTerm_le {z : ℂ} (hz : z ∈ halfPlaneHalf) (i : ℕ) :
    ‖altCosDefectTerm z i‖ ≤ 32 * π ^ 2 * (Real.exp (4 * π) + 1) * (1 / ((i : ℝ) + 1) ^ 2) := by
  have hi : (0 : ℝ) ≤ i := i.cast_nonneg
  set w := z + ((i : ℝ) : ℂ) with hw
  have hw1 : 1 / 2 + (i : ℝ) ≤ ‖w‖ := half_add_le_norm_add hz i
  have hwpos : 0 < ‖w‖ := by linarith
  have hx : ‖(2 * π : ℂ) / w‖ ≤ 4 * π := by
    rw [norm_div]
    have : ‖(2 * π : ℂ)‖ = 2 * π := by
      rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    rw [this, div_le_iff₀ hwpos]
    nlinarith [Real.pi_pos]
  have hc := norm_cos_sub_one_le hx
  have hM : 0 < Real.exp (4 * π) + 1 := by positivity
  rw [altCosDefectTerm, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, cosDefect,
    norm_div]
  have hn : ‖(2 * π : ℂ) / w‖ = 2 * π / ‖w‖ := by
    rw [norm_div]
    congr 1
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [hn] at hc
  have hw3 : ((i : ℝ) + 1) ^ 2 ≤ 8 * ‖w‖ ^ 3 := by
    set t := 1 / 2 + (i : ℝ) with ht
    have ht0 : 1 / 2 ≤ t := by rw [ht]; linarith
    have h1 : ((i : ℝ) + 1) ^ 2 ≤ 4 * t ^ 2 := by nlinarith
    have h2 : 4 * t ^ 2 ≤ 8 * t ^ 3 := by nlinarith
    have h3 : t ^ 3 ≤ ‖w‖ ^ 3 := pow_le_pow_left₀ (by linarith) hw1 3
    linarith
  have key : ‖Complex.cos (2 * ↑π / w) - 1‖ / ‖w‖ ≤
      4 * π ^ 2 * (Real.exp (4 * π) + 1) / ‖w‖ ^ 3 := by
    calc ‖Complex.cos (2 * ↑π / w) - 1‖ / ‖w‖
        ≤ (Real.exp (4 * π) + 1) * (2 * π / ‖w‖) ^ 2 / ‖w‖ :=
          div_le_div_of_nonneg_right hc hwpos.le
      _ = 4 * π ^ 2 * (Real.exp (4 * π) + 1) / ‖w‖ ^ 3 := by field_simp; ring
  refine key.trans ?_
  have hpos : 0 < ((i : ℝ) + 1) ^ 2 := by positivity
  rw [show 32 * π ^ 2 * (Real.exp (4 * π) + 1) * (1 / ((i : ℝ) + 1) ^ 2) =
    32 * π ^ 2 * (Real.exp (4 * π) + 1) / ((i : ℝ) + 1) ^ 2 by field_simp,
    div_le_div_iff₀ (by positivity) hpos]
  have hP : 0 < 4 * π ^ 2 * (Real.exp (4 * π) + 1) := by positivity
  nlinarith

theorem differentiableOn_altHarmonic : DifferentiableOn ℂ altHarmonic halfPlaneHalf := by
  refine Complex.differentiableOn_tsum_of_summable_norm (summable_inv_succ_sq.mul_left (4 / 3))
    (fun k => ?_) isOpen_halfPlaneHalf (fun k z hz => norm_altHarmonicTerm_le hz k)
  unfold altHarmonicTerm
  refine (differentiableOn_const 1).div ?_ fun z hz => ?_
  · exact ((differentiableOn_id.add_const _).mul (differentiableOn_id.add_const _))
  · exact mul_ne_zero (add_ne_zero_of_mem_halfPlaneHalf hz (by positivity))
      (add_ne_zero_of_mem_halfPlaneHalf hz (by positivity))

theorem differentiableOn_altCosDefect : DifferentiableOn ℂ altCosDefect halfPlaneHalf := by
  refine Complex.differentiableOn_tsum_of_summable_norm
    (summable_inv_succ_sq.mul_left (32 * π ^ 2 * (Real.exp (4 * π) + 1)))
    (fun i => ?_) isOpen_halfPlaneHalf (fun i z hz => norm_altCosDefectTerm_le hz i)
  unfold altCosDefectTerm cosDefect
  have hne : ∀ z ∈ halfPlaneHalf, z + ((i : ℝ) : ℂ) ≠ 0 := fun z hz =>
    add_ne_zero_of_mem_halfPlaneHalf hz i.cast_nonneg
  refine DifferentiableOn.const_mul ?_ _
  refine DifferentiableOn.div ?_ (differentiableOn_id.add_const _) hne
  refine DifferentiableOn.sub_const ?_ _
  refine Complex.differentiable_cos.comp_differentiableOn ?_
  exact (differentiableOn_const _).div (differentiableOn_id.add_const _) hne

/-! ### The real series -/

/-- Real values of the paired alternating harmonic series. -/
def altHarmonicR (v : ℝ) : ℝ := ∑' k : ℕ, 1 / ((v + 2 * k) * (v + 2 * k + 1))

/-- Real values of the alternating cosine-defect series. -/
def altCosDefectR (v : ℝ) : ℝ :=
  ∑' i : ℕ, (-1 : ℝ) ^ i * ((Real.cos (2 * π / (v + i)) - 1) / (v + i))

theorem altHarmonic_ofReal (v : ℝ) : altHarmonic v = (altHarmonicR v : ℂ) := by
  rw [altHarmonic, altHarmonicR, Complex.ofReal_tsum]
  congr 1
  funext k
  simp only [altHarmonicTerm]
  push_cast
  ring_nf

theorem altCosDefect_ofReal (v : ℝ) : altCosDefect v = (altCosDefectR v : ℂ) := by
  rw [altCosDefect, altCosDefectR, Complex.ofReal_tsum]
  congr 1
  funext i
  simp only [altCosDefectTerm, cosDefect]
  push_cast
  ring_nf

theorem hasSum_telescope_two {v : ℝ} (hv : 0 < v) :
    HasSum (fun k : ℕ => 1 / (v + 2 * k) - 1 / (v + 2 * (k + 1))) (1 / v) := by
  have hnn : ∀ k : ℕ, 0 ≤ 1 / (v + 2 * k) - 1 / (v + 2 * (k + 1)) := by
    intro k
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hsum : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 / (v + 2 * k) - 1 / (v + 2 * (k + 1))) =
      1 / v - 1 / (v + 2 * n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  simp_rw [hsum]
  have ht : Tendsto (fun n : ℕ => 1 / (v + 2 * (n : ℝ))) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => v + 2 * (n : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left _ _
        (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
    exact (tendsto_inv_atTop_zero.comp this).congr fun n => by simp [one_div]
  simpa using (tendsto_const_nhds (x := 1 / v)).sub ht

theorem summable_altHarmonicR {v : ℝ} (hv : 0 < v) :
    Summable fun k : ℕ => 1 / ((v + 2 * k) * (v + 2 * k + 1)) := by
  refine (hasSum_telescope_two hv).summable.of_nonneg_of_le (fun k => by positivity) fun k => ?_
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have e : 1 / (v + 2 * k) - 1 / (v + 2 * (k + 1)) = 2 / ((v + 2 * k) * (v + 2 * k + 2)) := by
    field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem altHarmonicR_add_one {v : ℝ} (hv : 0 < v) :
    altHarmonicR v + altHarmonicR (v + 1) = 1 / v := by
  have h1 := (summable_altHarmonicR hv).hasSum
  have h2 := (summable_altHarmonicR (show 0 < v + 1 by linarith)).hasSum
  have h := h1.add h2
  refine h.unique ((hasSum_telescope_two hv).congr_fun fun k => ?_)
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  field_simp
  ring

theorem altHarmonicR_nonneg_le {v : ℝ} (hv : 0 < v) :
    0 ≤ altHarmonicR v ∧ altHarmonicR v ≤ 1 / v := by
  constructor
  · exact tsum_nonneg fun k => by positivity
  · refine ((summable_altHarmonicR hv).tsum_le_tsum (fun k => ?_)
      (hasSum_telescope_two hv).summable).trans (hasSum_telescope_two hv).tsum_eq.le
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    have e : 1 / (v + 2 * k) - 1 / (v + 2 * (k + 1)) = 2 / ((v + 2 * k) * (v + 2 * k + 2)) := by
      field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

theorem abs_cosDefectR_le {w : ℝ} (hw : 1 ≤ w) (i : ℕ) :
    |(Real.cos (2 * π / (w + i)) - 1) / (w + i)| ≤ 2 * π ^ 2 / w * (1 / ((i : ℝ) + 1) ^ 2) := by
  have hi : (0 : ℝ) ≤ i := i.cast_nonneg
  have hpos : 0 < w + i := by linarith
  have hc1 := Real.cos_le_one (2 * π / (w + i))
  have hc2 := Real.one_sub_sq_div_two_le_cos (x := 2 * π / (w + i))
  rw [abs_div, abs_of_pos hpos, abs_of_nonpos (by linarith)]
  have hb : 1 - Real.cos (2 * π / (w + i)) ≤ (2 * π / (w + i)) ^ 2 / 2 := by linarith
  rw [div_le_iff₀ hpos]
  calc -(Real.cos (2 * π / (w + i)) - 1) ≤ (2 * π / (w + i)) ^ 2 / 2 := by linarith
    _ ≤ 2 * π ^ 2 / w * (1 / ((i : ℝ) + 1) ^ 2) * (w + i) := by
        rw [div_pow]
        have h3 : w * ((i : ℝ) + 1) ^ 2 ≤ (w + i) ^ 3 := by
          have hq : ((i : ℝ) + 1) ^ 2 ≤ (w + i) ^ 2 :=
            pow_le_pow_left₀ (by linarith) (by linarith) 2
          have hw0 : 0 ≤ w := by linarith
          calc w * ((i : ℝ) + 1) ^ 2 ≤ w * (w + i) ^ 2 := mul_le_mul_of_nonneg_left hq hw0
            _ ≤ (w + i) * (w + i) ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
            _ = (w + i) ^ 3 := by ring
        rw [div_div, div_le_iff₀ (by positivity)]
        field_simp
        nlinarith [Real.pi_pos, sq_nonneg π, mul_pos (by positivity : (0 : ℝ) < π ^ 2) hpos]

theorem summable_altCosDefectR {w : ℝ} (hw : 1 ≤ w) :
    Summable fun i : ℕ => (-1 : ℝ) ^ i * ((Real.cos (2 * π / (w + i)) - 1) / (w + i)) := by
  refine Summable.of_norm_bounded (summable_inv_succ_sq.mul_left (2 * π ^ 2 / w)) fun i => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact abs_cosDefectR_le hw i

theorem altCosDefectR_add_one {w : ℝ} (hw : 1 ≤ w) :
    altCosDefectR w + altCosDefectR (w + 1) = (Real.cos (2 * π / w) - 1) / w := by
  have hs := summable_altCosDefectR hw
  have h := hs.tsum_eq_zero_add
  unfold altCosDefectR
  rw [h]
  have e : ∀ i : ℕ, (-1 : ℝ) ^ (i + 1) * ((Real.cos (2 * π / (w + ((i + 1 : ℕ) : ℝ))) - 1) /
      (w + ((i + 1 : ℕ) : ℝ))) =
      -((-1 : ℝ) ^ i * ((Real.cos (2 * π / (w + 1 + (i : ℝ))) - 1) / (w + 1 + (i : ℝ)))) := by
    intro i
    push_cast
    rw [pow_succ]
    ring_nf
  simp_rw [e, tsum_neg]
  simp

theorem abs_altCosDefectR_le {w : ℝ} (hw : 1 ≤ w) :
    |altCosDefectR w| ≤ 2 * π ^ 2 / w * ∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ 2 := by
  have hs := summable_altCosDefectR hw
  rw [altCosDefectR, ← tsum_mul_left]
  have hn : Summable fun i : ℕ => ‖(-1 : ℝ) ^ i * ((Real.cos (2 * π / (w + i)) - 1) / (w + i))‖ :=
    hs.norm
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum (fun i => ?_)
    (summable_inv_succ_sq.mul_left _))
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact abs_cosDefectR_le hw i

/-! ### The Farey recursion for blind cores -/

variable {f : ℝ → ℝ}

/-- **Two-term periodization.** -/
theorem dilationAutocorr_farey_periodization (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hβ2 : β ≤ 2 * α) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) {v : ℝ} (hv2 : 2 ≤ v)
    (hvw : α ≤ v * (2 * α - β)) :
    dilationAutocorr f (1 - 1 / v) + dilationAutocorr f (1 + 1 / v) =
      cosDilationKernel f 0 + 2 * cosDilationKernel f 1 * Real.cos (2 * π / v) := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hv0 : 0 < v := by linarith
  have hlo : 1 / 2 ≤ α / β := by rw [le_div_iff₀ hβ0]; linarith
  have hhi : β / α ≤ 2 := by rw [div_le_iff₀ hα]; linarith
  have hk1 : β / α ≤ 2 - 1 / v := by
    rw [div_le_iff₀ hα]
    have : α / v ≤ 2 * α - β := by rw [div_le_iff₀ hv0]; linarith
    have e : (2 - 1 / v) * α = 2 * α - α / v := by ring
    linarith
  have hinvv : 1 / v ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hv2
  have hinvv0 : 0 < 1 / v := by positivity
  have hblindℤ := cosDilationKernel_int_eq_zero hf hα hαβ hsupp hblind
  have h := tsum_dilationAutocorr_abs_eq hf hα hαβ hsupp hblindℤ (1 - 1 / v)
  rw [tsum_eq_sum (s := {0, -2}) fun k hk => ?_] at h
  · rw [Finset.sum_insert (by norm_num), Finset.sum_singleton] at h
    have a0 : |1 - 1 / v + ((0 : ℤ) : ℝ)| = 1 - 1 / v := by
      rw [Int.cast_zero, add_zero, abs_of_pos (by linarith)]
    have a2 : |1 - 1 / v + ((-2 : ℤ) : ℝ)| = 1 + 1 / v := by
      rw [abs_of_neg (by push_cast; linarith)]; push_cast; ring
    have hcos : Real.cos (2 * π * (1 - 1 / v)) = Real.cos (2 * π / v) := by
      rw [show 2 * π * (1 - 1 / v) = 2 * π - 2 * π / v by ring, Real.cos_two_pi_sub]
    rw [a0, a2, hcos] at h
    exact_mod_cast h
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [dilationAutocorr_eq_zero_of_not_mem_Ioo hf hα hαβ hsupp, Complex.ofReal_zero]
    intro hm
    rcases le_or_gt 1 k with hk1' | hk1'
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk1'
      rw [abs_of_pos (by linarith)] at hm
      linarith [hm.2]
    rcases le_or_gt (-1) k with hkm | hkm
    · have : k = -1 := by omega
      subst this
      rw [abs_of_neg (by push_cast; linarith)] at hm
      push_cast at hm
      linarith [hm.1]
    · have hk3 : k ≤ -3 := by omega
      have : (k : ℝ) ≤ -3 := by exact_mod_cast hk3
      rw [abs_of_neg (by linarith)] at hm
      linarith [hm.2]

/-- **The Farey recursion** `H(v) + H(v + 1) = (Ψ_f(0) + 2Ψ_f(1) cos(2π/v))/v`. -/
theorem dilationAutocorr_farey_recursion (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hβ2 : β ≤ 2 * α) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) {v : ℝ} (hv2 : 2 ≤ v)
    (hvw : α ≤ v * (2 * α - β)) :
    dilationAutocorr f (1 - 1 / v) / v + dilationAutocorr f (1 - 1 / (v + 1)) / (v + 1) =
      (cosDilationKernel f 0 + 2 * cosDilationKernel f 1 * Real.cos (2 * π / v)) / v := by
  have hv0 : 0 < v := by linarith
  have hp := dilationAutocorr_farey_periodization hf hα hαβ hβ2 hsupp hblind hv2 hvw
  have hr : 0 < 1 - 1 / (v + 1) := by
    have : 1 / (v + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hinv := dilationAutocorr_inv f hr
  have hv1 : v + 1 ≠ 0 := by linarith
  have e : (1 - 1 / (v + 1))⁻¹ = 1 + 1 / v := by
    rw [show 1 - 1 / (v + 1) = v / (v + 1) by field_simp; ring, inv_div]
    field_simp
  rw [e] at hinv
  rw [hinv] at hp
  rw [← hp]
  field_simp
  ring

/-! ### The theorem -/

/-! ### The decaying series solution -/

/-- The decaying solution `a·Σ_k 1/((v+2k)(v+2k+1)) + b·Σ_i (−1)^i (cos(2π/(v+i)) − 1)/(v+i)`. -/
def fareySeriesR (a b v : ℝ) : ℝ := a * altHarmonicR v + b * altCosDefectR v

/-- Its holomorphic extension to `Re z > ½`. -/
def fareySeries (a b : ℝ) (z : ℂ) : ℂ := (a : ℂ) * altHarmonic z + (b : ℂ) * altCosDefect z

theorem fareySeries_ofReal (a b v : ℝ) : fareySeries a b v = (fareySeriesR a b v : ℂ) := by
  simp only [fareySeries, fareySeriesR, altHarmonic_ofReal, altCosDefect_ofReal]
  push_cast
  ring

theorem differentiableOn_fareySeries (a b : ℝ) :
    DifferentiableOn ℂ (fareySeries a b) halfPlaneHalf :=
  (differentiableOn_altHarmonic.const_mul _).add (differentiableOn_altCosDefect.const_mul _)

theorem fareySeriesR_add_one (a b : ℝ) {v : ℝ} (hv : 1 ≤ v) :
    fareySeriesR a b v + fareySeriesR a b (v + 1) = (a + b * (Real.cos (2 * π / v) - 1)) / v := by
  have h1 := altHarmonicR_add_one (show 0 < v by linarith)
  have h2 := altCosDefectR_add_one hv
  have hv0 : v ≠ 0 := by linarith
  simp only [fareySeriesR]
  have : a * altHarmonicR v + b * altCosDefectR v + (a * altHarmonicR (v + 1) +
      b * altCosDefectR (v + 1)) = a * (1 / v) + b * ((Real.cos (2 * π / v) - 1) / v) := by
    rw [← h1, ← h2]; ring
  rw [this]
  field_simp

theorem abs_fareySeriesR_le (a b : ℝ) {v : ℝ} (hv : 1 ≤ v) :
    |fareySeriesR a b v| ≤
      (|a| + |b| * (2 * π ^ 2 * ∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ 2)) / v := by
  have hv0 : 0 < v := by linarith
  have hA := altHarmonicR_nonneg_le hv0
  have hC := abs_altCosDefectR_le hv
  simp only [fareySeriesR]
  calc |a * altHarmonicR v + b * altCosDefectR v|
      ≤ |a| * |altHarmonicR v| + |b| * |altCosDefectR v| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |a| * (1 / v) + |b| * (2 * π ^ 2 / v * ∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ 2) := by
        gcongr
        rw [abs_of_nonneg hA.1]; exact hA.2
    _ = _ := by field_simp

/-- **Decaying solutions of the Farey recursion are unique.**  If
`H v + H (v + 1) = (a + b(cos(2π/v) − 1))/v` for `v ≥ v₁ ≥ 1` and `|H v| ≤ C/v` for `v ≥ 1`,
then `H = fareySeriesR a b` on `[v₁, ∞)`. -/
theorem eq_fareySeriesR_of_recursion {H : ℝ → ℝ} {a b v₁ C : ℝ} (hv₁ : 1 ≤ v₁)
    (hrec : ∀ v, v₁ ≤ v → H v + H (v + 1) = (a + b * (Real.cos (2 * π / v) - 1)) / v)
    (hH : ∀ v, 1 ≤ v → |H v| ≤ C / v) : ∀ v, v₁ ≤ v → H v = fareySeriesR a b v := by
  set F := fareySeriesR a b with hF
  set K := C + (|a| + |b| * (2 * π ^ 2 * ∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ 2)) with hK
  have hdecay : ∀ v, 1 ≤ v → |H v - F v| ≤ K / v := by
    intro v hv
    calc |H v - F v| ≤ |H v| + |F v| := abs_sub _ _
      _ ≤ C / v + (|a| + |b| * (2 * π ^ 2 * ∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ 2)) / v :=
          add_le_add (hH v hv) (abs_fareySeriesR_le a b hv)
      _ = K / v := by rw [hK]; ring
  intro v hv
  have hstep : ∀ n : ℕ, |H (v + n) - F (v + n)| = |H v - F v| := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hvn : v₁ ≤ v + n := by have := n.cast_nonneg (α := ℝ); linarith
      have e1 := hrec _ hvn
      have e2 := fareySeriesR_add_one a b (v := v + n) (by linarith)
      have : H (v + ↑(n + 1)) - F (v + ↑(n + 1)) = -(H (v + n) - F (v + n)) := by
        push_cast
        rw [← add_assoc]
        rw [hF] at *
        linarith
      rw [this, abs_neg, ih]
  by_contra hne
  have hpos : 0 < |H v - F v| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (K / |H v - F v|)
  have hvn : 1 ≤ v + n := by have := n.cast_nonneg (α := ℝ); linarith
  have hd := hdecay (v + n) hvn
  rw [hstep n] at hd
  have hvn0 : 0 < v + n := by linarith
  rw [le_div_iff₀ hvn0] at hd
  have : K < |H v - F v| * n := by rwa [div_lt_iff₀ hpos, mul_comm] at hn
  have : |H v - F v| * n ≤ |H v - F v| * (v + n) :=
    mul_le_mul_of_nonneg_left (by linarith) hpos.le
  linarith

/-- `|A_f|` is bounded. -/
theorem exists_abs_dilationAutocorr_le (hf : Continuous f) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) : ∃ C, ∀ r, |dilationAutocorr f r| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := α / β) (b := β / α)).exists_bound_of_continuousOn
    (continuous_dilationAutocorr hf hα hsupp).continuousOn
  refine ⟨max C 0, fun r => ?_⟩
  by_cases hr : r ∈ Icc (α / β) (β / α)
  · exact (hC r hr).trans (le_max_left _ _)
  · rw [dilationAutocorr_eq_zero_of_not_mem_Ioo hf hα hαβ hsupp fun h => hr ⟨h.1.le, h.2.le⟩,
      abs_zero]
    exact le_max_right _ _

/-- **The core profile is the series** on `[max 2 (α/(2α − β)), ∞)`. -/
theorem dilationAutocorr_profile_eq_fareySeriesR (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hβ2 : β < 2 * α) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) {v : ℝ}
    (hv : max 2 (α / (2 * α - β)) ≤ v) :
    dilationAutocorr f (1 - 1 / v) / v = fareySeriesR
      (cosDilationKernel f 0 + 2 * cosDilationKernel f 1) (2 * cosDilationKernel f 1) v := by
  have h2ab : 0 < 2 * α - β := by linarith
  obtain ⟨CA, hCA⟩ := exists_abs_dilationAutocorr_le hf hα hαβ hsupp
  refine eq_fareySeriesR_of_recursion (H := fun v => dilationAutocorr f (1 - 1 / v) / v)
    (C := CA) (le_trans (by norm_num) (le_max_left _ _)) (fun w hw => ?_) (fun w hw => ?_) v hv
  · have hvw : α ≤ w * (2 * α - β) := by
      have := (le_max_right 2 (α / (2 * α - β))).trans hw
      rwa [div_le_iff₀ h2ab] at this
    rw [dilationAutocorr_farey_recursion hf hα hαβ hβ2.le hsupp hblind
      ((le_max_left _ _).trans hw) hvw]
    ring
  · have hw0 : 0 < w := by linarith
    rw [abs_div, abs_of_pos hw0]
    exact div_le_div_of_nonneg_right (hCA _) hw0.le

/-- Frequent real zeros near a real point of `Re z > ½` make an analytic function vanish there. -/
theorem eqOn_zero_of_real_interval {G : ℂ → ℂ} {U : Set ℂ} (hG : AnalyticOnNhd ℂ G U)
    (hU : IsPreconnected U) {p q : ℝ} (hpq : p < q) (hmU : (((p + q) / 2 : ℝ) : ℂ) ∈ U)
    (hzero : ∀ x : ℝ, p < x → x < q → G x = 0) : EqOn G 0 U := by
  set m := (p + q) / 2 with hm
  refine hG.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hmU ?_
  have hev : ∀ᶠ x : ℝ in 𝓝[≠] m, G (x : ℂ) = 0 := by
    have hI : Ioo p q ∈ 𝓝 m := Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [nhdsWithin_le_nhds hI] with x hx
    exact hzero x hx.1 hx.2
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] m) (𝓝[≠] (m : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact fun h => hx (Complex.ofReal_injective h)
  exact ht.frequently hev.frequently

/-! ### The theorem -/

/-- **Blind cores of support ratio below the golden ratio vanish.** -/
theorem eq_zero_of_cosDilationKernel_blind_of_golden (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hgold : β ^ 2 < α * β + α ^ 2)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) (y : ℝ) : f y = 0 := by
  rcases lt_or_ge β (3 / 2 * α) with h32 | h32
  · exact eq_zero_of_cosDilationKernel_blind_of_lt_three_halves_mul hf hα hαβ h32 hsupp hblind y
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hβ2 : β < 2 * α := by nlinarith
  have hβα : α < β := by linarith
  set Ψ0 := cosDilationKernel f 0 with hΨ0
  set Ψ1 := cosDilationKernel f 1 with hΨ1
  set F := fareySeriesR (Ψ0 + 2 * Ψ1) (2 * Ψ1) with hF
  set v₁ := max 2 (α / (2 * α - β)) with hv₁
  have h2ab : 0 < 2 * α - β := by linarith
  have hv₁2 : 2 ≤ v₁ := le_max_left _ _
  -- the zero interval
  set w₂ := β / (β - α) with hw₂
  have hβα' : 0 < β - α := by linarith
  have hv₁w₂ : v₁ < w₂ := by
    rw [hv₁, max_lt_iff]
    constructor
    · rw [hw₂, lt_div_iff₀ hβα']; linarith
    · rw [hw₂, div_lt_div_iff₀ h2ab hβα']; nlinarith
  set v₂ := (v₁ + w₂) / 2 with hv₂
  have hFzero : ∀ v, v₁ ≤ v → v ≤ v₂ → F v = 0 := by
    intro v hv1 hv2
    have hv0 : 0 < v := by linarith
    rw [hF, ← dilationAutocorr_profile_eq_fareySeriesR hf hα hαβ hβ2 hsupp hblind hv1,
      dilationAutocorr_eq_zero_of_not_mem_Ioo hf hα hαβ hsupp, zero_div]
    intro hm
    have hvw : v ≤ w₂ := by linarith
    have : 1 - 1 / v ≤ α / β := by
      rw [hw₂, le_div_iff₀ hβα'] at hvw
      rw [show 1 - 1 / v = (v - 1) / v by field_simp, div_le_div_iff₀ hv0 hβ0]
      nlinarith
    linarith [hm.1]
  -- analytic continuation
  have hGa := (differentiableOn_fareySeries (Ψ0 + 2 * Ψ1) (2 * Ψ1)).analyticOnNhd
    isOpen_halfPlaneHalf
  have hv₁v₂ : v₁ < v₂ := by rw [hv₂]; linarith
  have hzero := eqOn_zero_of_real_interval hGa (convex_halfSpace_re_gt (1 / 2)).isPreconnected
    hv₁v₂ (by show 1 / 2 < (((v₁ + v₂) / 2 : ℝ) : ℂ).re; rw [Complex.ofReal_re]; linarith)
    fun x hx1 hx2 => by rw [fareySeries_ofReal, ← hF, hFzero x hx1.le hx2.le, Complex.ofReal_zero]
  have hFall : ∀ v : ℝ, 1 ≤ v → F v = 0 := by
    intro v hv
    have hvU : ((v : ℝ) : ℂ) ∈ halfPlaneHalf := by
      show 1 / 2 < ((v : ℝ) : ℂ).re
      rw [Complex.ofReal_re]; linarith
    have := hzero hvU
    rw [fareySeries_ofReal, Pi.zero_apply, ← hF] at this
    exact_mod_cast this
  have e2 := fareySeriesR_add_one (Ψ0 + 2 * Ψ1) (2 * Ψ1) (v := 2) (by norm_num)
  have e4 := fareySeriesR_add_one (Ψ0 + 2 * Ψ1) (2 * Ψ1) (v := 4) (by norm_num)
  rw [← hF, hFall 2 (by norm_num), hFall (2 + 1) (by norm_num), add_zero] at e2
  rw [← hF, hFall 4 (by norm_num), hFall (4 + 1) (by norm_num), add_zero] at e4
  have c2 : Real.cos (2 * π / 2) = -1 := by rw [show 2 * π / 2 = π by ring, Real.cos_pi]
  have c4 : Real.cos (2 * π / 4) = 0 := by
    rw [show 2 * π / 4 = π / 2 by ring, Real.cos_pi_div_two]
  rw [c2] at e2
  rw [c4] at e4
  have h0 : Ψ0 = 0 := by
    have e2' : (Ψ0 + 2 * Ψ1 + 2 * Ψ1 * (-1 - 1)) = 0 := by
      have := e2; field_simp at this; linarith
    have e4' : (Ψ0 + 2 * Ψ1 + 2 * Ψ1 * (0 - 1)) = 0 := by
      have := e4; field_simp at this; linarith
    linarith
  exact eq_zero_of_cosDilationKernel_blind_of_le_two_mul hf hα hαβ hβ2.le hsupp h0 hblind y

end

end RHTower
