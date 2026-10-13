import GaloisForLFunctions.HTGeometry.SechComplexFourierTransform
import Mathlib.Analysis.Analytic.Binomial

/-!
# The symmetric kernel `(cosh v + c)^{−½} + (cosh v − c)^{−½}` is strictly positive definite

For `|c| < 1` put `𝒦_c(v) = (cosh v + c)^{−1/2} + (cosh v − c)^{−1/2}`.

**Theorem** (`integral_cos_mul_symCoshKernel_pos`).  `∫ cos(τ v) 𝒦_c(v) dv > 0` for every real `τ`.

Proof.  With `x = c / cosh v ∈ (−1, 1)`, the binomial series of `(1 ± x)^{−1/2}` gives

`𝒦_c(v) = Σ_{j ≥ 0} 2 C(−½, 2j) c^{2j} (cosh v)^{−1/2−2j}`  (`hasSum_symCoshKernel`):

the odd terms cancel, and every even coefficient `C(−½, 2j)` is positive, since
`C(a, n+1) = C(a, n)(a − n)/(n + 1)` and `a − n < 0` (`choose_neg_half_even_pos`).  Each
`(cosh v)^{−s}` has the positive cosine transform `2^{s−1} |Γ((s + iτ)/2)|² / Γ(s)`
(`integral_cos_mul_cosh_rpow_neg`, from `integral_cosh_rpow_neg_mul_cexp_complex`), and the series
may be integrated termwise because `(cosh v)^{−1/2−2j} ≤ (cosh v)^{−1/2}`.

On the unit circle `z = u + iy = e^{iα}`, `e^{v/2}(y/|e^v − z|²)^{1/2} = (y/2)^{1/2}(cosh v − u)^{−1/2}`,
so this is the positive definiteness, in the logarithmic variable, of every `u ↦ −u` symmetric
superposition of the `s = ½` Poisson vectors attached to points of the unit circle.
-/

open MeasureTheory Set Filter Topology Polynomial

namespace GaloisForLFunctions
namespace HTGeometry

noncomputable section

/-! ### Binomial coefficients at `−½` -/

theorem smeval_descPochhammer_real (a : ℝ) (n : ℕ) :
    (descPochhammer ℤ n).smeval a = (descPochhammer ℝ n).eval a := by
  rw [← Polynomial.aeval_eq_smeval, ← descPochhammer_map (algebraMap ℤ ℝ), Polynomial.eval_map,
    Polynomial.aeval_def]

theorem ringChoose_succ_real (a : ℝ) (n : ℕ) :
    Ring.choose a (n + 1) = Ring.choose a n * (a - n) / (n + 1) := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul, smul_eq_mul, smul_eq_mul,
    smeval_descPochhammer_real, smeval_descPochhammer_real, descPochhammer_succ_eval,
    Nat.factorial_succ]
  push_cast
  field_simp

/-- `C(−½, 2j) > 0`. -/
theorem choose_neg_half_even_pos (j : ℕ) : 0 < Ring.choose (-1 / 2 : ℝ) (2 * j) := by
  have key : ∀ n : ℕ, 0 < (-1 : ℝ) ^ n * Ring.choose (-1 / 2 : ℝ) n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ringChoose_succ_real, pow_succ]
      have h1 : (0 : ℝ) < n + 1 := by positivity
      have h2 : (-1 / 2 : ℝ) - n < 0 := by have := n.cast_nonneg (α := ℝ); linarith
      have e : (-1 : ℝ) ^ n * (-1) * (Ring.choose (-1 / 2) n * (-1 / 2 - n) / (n + 1)) =
          ((-1 : ℝ) ^ n * Ring.choose (-1 / 2) n) * (-((-1 / 2 : ℝ) - n) / (n + 1)) := by ring
      rw [e]
      exact mul_pos ih (div_pos (by linarith) h1)
  have := key (2 * j)
  rwa [pow_mul, neg_one_sq, one_pow, one_mul] at this

/-- `|C(−½, n)| ≤ 1`. -/
theorem abs_choose_neg_half_le_one (n : ℕ) : |Ring.choose (-1 / 2 : ℝ) n| ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ringChoose_succ_real, abs_div, abs_mul]
    have h1 : (0 : ℝ) < n + 1 := by positivity
    rw [abs_of_pos h1, div_le_one h1]
    have h2 : |(-1 / 2 : ℝ) - n| ≤ n + 1 := by
      rw [abs_le]; constructor <;> nlinarith [n.cast_nonneg (α := ℝ)]
    calc |Ring.choose (-1 / 2 : ℝ) n| * |(-1 / 2 : ℝ) - n| ≤ 1 * (n + 1) :=
          mul_le_mul ih h2 (abs_nonneg _) zero_le_one
      _ = n + 1 := one_mul _

/-! ### The binomial series -/

theorem hasSum_one_add_rpow (a : ℝ) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ => Ring.choose a k * x ^ k) ((1 + x) ^ a) := by
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := a)).hasSum
    (y := x) (by simpa [edist_dist, Real.dist_eq] using hx)
  rw [zero_add] at h
  refine h.congr_fun ?_
  intro n
  simp only [binomialSeries_apply, List.ofFn_const, List.prod_replicate, smul_eq_mul]

/-- **The even binomial series.** -/
theorem hasSum_one_add_rpow_add_one_sub {x : ℝ} (hx : |x| < 1) :
    HasSum (fun j : ℕ => 2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * x ^ (2 * j))
      ((1 + x) ^ (-1 / 2 : ℝ) + (1 - x) ^ (-1 / 2 : ℝ)) := by
  have h1 := hasSum_one_add_rpow (-1 / 2) hx
  have h2 := hasSum_one_add_rpow (-1 / 2) (x := -x) (by rwa [abs_neg])
  have h := h1.add h2
  rw [← sub_eq_add_neg] at h
  have hinj : Function.Injective (fun j : ℕ => 2 * j) := fun a b hab => by simpa using hab
  have hzero : ∀ k ∉ Set.range (fun j : ℕ => 2 * j),
      Ring.choose (-1 / 2 : ℝ) k * x ^ k + Ring.choose (-1 / 2 : ℝ) k * (-x) ^ k = 0 := by
    intro k hk
    have hodd : Odd k := by
      rcases Nat.even_or_odd k with ⟨m, hm⟩ | ho
      · exact absurd ⟨m, show 2 * m = k by omega⟩ hk
      · exact ho
    rw [hodd.neg_pow]; ring
  have := (hinj.hasSum_iff hzero).mpr h
  convert this using 1
  funext j
  simp only [Function.comp_apply]
  rw [(even_two_mul j).neg_pow]; ring

/-! ### The kernel -/

/-- `𝒦_c(v) = (cosh v + c)^{−1/2} + (cosh v − c)^{−1/2}`. -/
def symCoshKernel (c v : ℝ) : ℝ :=
  (Real.cosh v + c) ^ (-1 / 2 : ℝ) + (Real.cosh v - c) ^ (-1 / 2 : ℝ)

/-- The `j`-th term `2 C(−½, 2j) c^{2j} (cosh v)^{−1/2−2j}`. -/
def symCoshTerm (c : ℝ) (j : ℕ) (v : ℝ) : ℝ :=
  2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * c ^ (2 * j) * Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ))

theorem symCoshTerm_nonneg (c : ℝ) (j : ℕ) (v : ℝ) : 0 ≤ symCoshTerm c j v := by
  unfold symCoshTerm
  have := choose_neg_half_even_pos j
  have hc : 0 ≤ c ^ (2 * j) := by rw [pow_mul]; positivity
  have : 0 ≤ Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ)) := Real.rpow_nonneg (Real.cosh_pos v).le _
  positivity

theorem hasSum_symCoshKernel {c : ℝ} (hc : |c| < 1) (v : ℝ) :
    HasSum (fun j => symCoshTerm c j v) (symCoshKernel c v) := by
  have hch := Real.cosh_pos v
  have h1 := Real.one_le_cosh v
  have hx : |c / Real.cosh v| < 1 := by
    rw [abs_div, abs_of_pos hch, div_lt_one hch]; linarith
  have h := (hasSum_one_add_rpow_add_one_sub hx).mul_left (Real.cosh v ^ (-1 / 2 : ℝ))
  have e1 : ∀ s : ℝ, 0 ≤ s → 0 < Real.cosh v → (Real.cosh v + c) ^ s =
      Real.cosh v ^ s * (1 + c / Real.cosh v) ^ s := by
    intro s _ hpos
    rw [← Real.mul_rpow hpos.le (by
      have := abs_lt.mp hx; rw [abs_div] at *; linarith [this.1])]
    congr 1; field_simp
  unfold symCoshKernel
  have hp : 0 < 1 + c / Real.cosh v := by have := abs_lt.mp hx; linarith [this.1]
  have hm : 0 < 1 - c / Real.cosh v := by have := abs_lt.mp hx; linarith [this.2]
  have ep : (Real.cosh v + c) ^ (-1 / 2 : ℝ) =
      Real.cosh v ^ (-1 / 2 : ℝ) * (1 + c / Real.cosh v) ^ (-1 / 2 : ℝ) := by
    rw [← Real.mul_rpow hch.le hp.le]; congr 1; field_simp
  have em : (Real.cosh v - c) ^ (-1 / 2 : ℝ) =
      Real.cosh v ^ (-1 / 2 : ℝ) * (1 - c / Real.cosh v) ^ (-1 / 2 : ℝ) := by
    rw [← Real.mul_rpow hch.le hm.le]; congr 1; field_simp
  rw [ep, em, ← mul_add]
  refine h.congr_fun fun j => ?_
  unfold symCoshTerm
  have e : Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ)) =
      Real.cosh v ^ (-1 / 2 : ℝ) * (Real.cosh v ^ (2 * j))⁻¹ := by
    rw [show -(1 / 2 + 2 * (j : ℝ)) = -1 / 2 + -((2 * j : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add hch, Real.rpow_neg hch.le, Real.rpow_natCast]
  rw [e, div_pow]
  field_simp

/-! ### The cosine transform of `(cosh v)^{−s}` -/

/-- `∫ cos(τ v) (cosh v)^{−s} dv = 2^{s−1} |Γ((s + iτ)/2)|² / Γ(s) > 0`. -/
theorem integral_cos_mul_cosh_rpow_neg_pos {s : ℝ} (hs : 0 < s) (τ : ℝ) :
    0 < ∫ v : ℝ, Real.cos (τ * v) * Real.cosh v ^ (-s) := by
  have h := integral_cosh_rpow_neg_mul_cexp_complex hs (z := (τ : ℂ)) (by simpa using hs)
  have hint : Integrable (fun v : ℝ => (((Real.cosh v) ^ (-s) : ℝ) : ℂ) *
      Complex.exp (-((τ : ℂ) * (v : ℂ)) * Complex.I)) := by
    by_contra hni
    rw [integral_undef hni] at h
    have hG : Complex.Gamma (((s : ℂ) - (τ : ℂ) * Complex.I) / 2) *
        Complex.Gamma (((s : ℂ) + (τ : ℂ) * Complex.I) / 2) / Complex.Gamma (s : ℂ) ≠ 0 := by
      refine div_ne_zero (mul_ne_zero ?_ ?_) ?_ <;> apply Complex.Gamma_ne_zero <;> intro m hm
      · have := congrArg Complex.re hm; simp at this; nlinarith [m.cast_nonneg (α := ℝ)]
      · have := congrArg Complex.re hm; simp at this; nlinarith [m.cast_nonneg (α := ℝ)]
      · have := congrArg Complex.re hm; simp at this; nlinarith [m.cast_nonneg (α := ℝ)]
    have h2 : ((2 : ℝ) ^ (s - 1) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos two_pos _).ne'
    exact absurd h.symm (mul_ne_zero (by exact_mod_cast h2) hG)
  have hcos0 : (fun v : ℝ => ((((Real.cosh v) ^ (-s) : ℝ) : ℂ) *
      Complex.exp (-((τ : ℂ) * (v : ℂ)) * Complex.I)).re) =
      fun v => Real.cos (τ * v) * Real.cosh v ^ (-s) := by
    funext v
    rw [show -((τ : ℂ) * (v : ℂ)) * Complex.I = ((-(τ * v) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    ring
  have hkey : ∫ v : ℝ, Real.cos (τ * v) * Real.cosh v ^ (-s) =
      (((2 : ℝ) ^ (s - 1) : ℝ) * (Complex.Gamma (((s : ℂ) - (τ : ℂ) * Complex.I) / 2) *
        Complex.Gamma (((s : ℂ) + (τ : ℂ) * Complex.I) / 2) / Complex.Gamma (s : ℂ))).re := by
    rw [← h, ← hcos0]
    exact integral_re hint
  rw [hkey]
  set w : ℂ := ((s : ℂ) + (τ : ℂ) * Complex.I) / 2 with hw
  have hconj : ((s : ℂ) - (τ : ℂ) * Complex.I) / 2 = (starRingEnd ℂ) w := by
    rw [hw, map_div₀, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I,
      map_ofNat]
    ring
  rw [hconj, Complex.Gamma_conj, Complex.Gamma_ofReal]
  have hGs : 0 < Real.Gamma s := Real.Gamma_pos_of_pos hs
  have hnorm : (starRingEnd ℂ) (Complex.Gamma w) * Complex.Gamma w =
      ((Complex.normSq (Complex.Gamma w) : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
  rw [hnorm]
  have hw0 : Complex.Gamma w ≠ 0 := by
    apply Complex.Gamma_ne_zero; intro m hm
    have := congrArg Complex.re hm; simp [hw] at this; nlinarith [m.cast_nonneg (α := ℝ)]
  have hpos : 0 < Complex.normSq (Complex.Gamma w) := Complex.normSq_pos.mpr hw0
  rw [show ((((2 : ℝ) ^ (s - 1) : ℝ) : ℂ) * (((Complex.normSq (Complex.Gamma w) : ℝ) : ℂ) /
      ((Real.Gamma s : ℝ) : ℂ))) = (((2 : ℝ) ^ (s - 1) * (Complex.normSq (Complex.Gamma w) /
        Real.Gamma s) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  exact mul_pos (Real.rpow_pos_of_pos two_pos _) (div_pos hpos hGs)

/-! ### Termwise integration -/

theorem cosh_rpow_neg_le_of_le {s t : ℝ} (hst : s ≤ t) (v : ℝ) :
    Real.cosh v ^ (-t) ≤ Real.cosh v ^ (-s) :=
  Real.rpow_le_rpow_of_exponent_le (Real.one_le_cosh v) (by linarith)

/-- **Strict positive definiteness of the symmetric kernel.** -/
theorem integral_cos_mul_symCoshKernel_pos {c : ℝ} (hc : |c| < 1) (τ : ℝ) :
    0 < ∫ v : ℝ, Real.cos (τ * v) * symCoshKernel c v := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hI := _root_.HTGeometry.integrable_cosh_rpow_neg hhalf
  set A : ℕ → ℝ := fun j => 2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * c ^ (2 * j) with hA
  have hA0 : ∀ j, 0 ≤ A j := fun j => by
    have := choose_neg_half_even_pos j
    have hc2 : 0 ≤ c ^ (2 * j) := by rw [pow_mul]; positivity
    simp only [hA]; positivity
  have hAsum : Summable A := by
    have h0 := hasSum_one_add_rpow_add_one_sub (x := c) hc
    exact h0.summable
  set F : ℕ → ℝ → ℝ := fun j v => Real.cos (τ * v) * symCoshTerm c j v with hF
  have hterm : ∀ j v, symCoshTerm c j v = A j * Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ)) := by
    intro j v; simp [symCoshTerm, hA]
  have hFint : ∀ j, Integrable (F j) := by
    intro j
    refine (hI.const_mul (A j)).mono' (by
      simp only [hF, symCoshTerm]; fun_prop) (Eventually.of_forall fun v => ?_)
    simp only [hF]
    rw [hterm, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (hA0 j), abs_of_nonneg (Real.rpow_nonneg (Real.cosh_pos v).le _)]
    calc |Real.cos (τ * v)| * (A j * Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ)))
        ≤ 1 * (A j * Real.cosh v ^ (-(1 / 2) : ℝ)) := by
          apply mul_le_mul (Real.abs_cos_le_one _) _
            (mul_nonneg (hA0 j) (Real.rpow_nonneg (Real.cosh_pos v).le _)) zero_le_one
          exact mul_le_mul_of_nonneg_left
            (cosh_rpow_neg_le_of_le (by have := j.cast_nonneg (α := ℝ); linarith) v)
            (hA0 j)
      _ = A j * Real.cosh v ^ (-(1 / 2) : ℝ) := one_mul _
  have hnormsum : Summable fun j => ∫ v, ‖F j v‖ := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun v => norm_nonneg _)
      (fun j => ?_) (hAsum.mul_right (∫ v, Real.cosh v ^ (-(1 / 2) : ℝ)))
    rw [← integral_const_mul]
    refine integral_mono (hFint j).norm (hI.const_mul (A j)) fun v => ?_
    simp only [hF]
    rw [hterm, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (hA0 j), abs_of_nonneg (Real.rpow_nonneg (Real.cosh_pos v).le _)]
    calc |Real.cos (τ * v)| * (A j * Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ)))
        ≤ 1 * (A j * Real.cosh v ^ (-(1 / 2) : ℝ)) := by
          apply mul_le_mul (Real.abs_cos_le_one _) _
            (mul_nonneg (hA0 j) (Real.rpow_nonneg (Real.cosh_pos v).le _)) zero_le_one
          exact mul_le_mul_of_nonneg_left
            (cosh_rpow_neg_le_of_le (by have := j.cast_nonneg (α := ℝ); linarith) v)
            (hA0 j)
      _ = A j * Real.cosh v ^ (-(1 / 2) : ℝ) := one_mul _
  have hswap := integral_tsum_of_summable_integral_norm hFint hnormsum
  have hpt : ∀ v, Real.cos (τ * v) * symCoshKernel c v = ∑' j, F j v := by
    intro v
    rw [(hasSum_symCoshKernel hc v).tsum_eq.symm, ← tsum_mul_left]
  simp_rw [hpt]
  rw [← hswap]
  have hterm_int : ∀ j, ∫ v, F j v =
      A j * ∫ v, Real.cos (τ * v) * Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ)) := by
    intro j
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [hF, hterm]; ring
  have hnn : ∀ j, 0 ≤ ∫ v, F j v := fun j => by
    rw [hterm_int]
    exact mul_nonneg (hA0 j) (integral_cos_mul_cosh_rpow_neg_pos (by positivity) τ).le
  have hsumm : Summable fun j => ∫ v, F j v :=
    Summable.of_norm_bounded hnormsum fun j => norm_integral_le_integral_norm _
  refine hsumm.tsum_pos hnn 0 ?_
  rw [hterm_int]
  have hA00 : 0 < A 0 := by simp [hA]
  have := integral_cos_mul_cosh_rpow_neg_pos (s := 1 / 2 + 2 * ((0 : ℕ) : ℝ)) (by norm_num) τ
  exact mul_pos hA00 this

end

end HTGeometry
end GaloisForLFunctions
