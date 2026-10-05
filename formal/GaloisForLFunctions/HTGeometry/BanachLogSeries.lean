import GaloisForLFunctions.HTGeometry.BanachTriangularExponential
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The logarithm series in a commutative Banach algebra

In a commutative unital complex Banach algebra with `‖1‖ = 1`:

* `log(1 + x) = Σ_{r ≥ 0} (-1)^r x^{r+1}/(r+1)` converges in norm for `‖x‖ < 1`, with
  `‖log(1 + x)‖ ≤ ‖x‖/(1 - ‖x‖)`;
* `exp(log(1 + x)) = 1 + x`.  Along `t ↦ exp(-L(t)) (1 + tx)`, `L(t) = log(1 + tx)`, the
  derivative vanishes: termwise `L'(t) = x Σ_k (-tx)^k`, so `L'(t)(1 + tx) = x`;
* an element with `‖c‖ e^{‖c‖} < 1` and `exp c = 1` is zero, since
  `‖c‖ = ‖exp c - 1 - c‖ ≤ ‖c‖² e^{‖c‖}`;
* a vector-valued power series `Σ_n z^n a_n` determines its coefficients.
-/

open Filter Topology NormedSpace Metric

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FormationDust

/-! ### Uniqueness of power series coefficients -/

/-- If `Σ_n z^n a_n` and `Σ_n z^n b_n` have the same sum for all `‖z‖ < ρ`, then `a = b`. -/
theorem eq_of_hasSum_pow_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a b : ℕ → E} {f : ℂ → E} {ρ : ℝ} (hρ : 0 < ρ)
    (ha : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => z ^ n • a n) (f z))
    (hb : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => z ^ n • b n) (f z)) : a = b := by
  set r : NNReal := ⟨ρ / 2, by positivity⟩
  have hr : (r : ℝ) = ρ / 2 := rfl
  have hrρ : (r : ℝ) < ρ := by rw [hr]; linarith
  have hrnorm : ‖((r : ℝ) : ℂ)‖ = r := by simp
  let p : (ℕ → E) → FormalMultilinearSeries ℂ ℂ E := fun c n =>
    ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (c n)
  have hp : ∀ c : ℕ → E, ∀ n (y : ℂ), p c n (fun _ => y) = y ^ n • c n := fun c n y => by
    simp [p, ContinuousMultilinearMap.mkPiRing_apply]
  have hseries : ∀ c : ℕ → E, (∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => z ^ n • c n) (f z)) →
      HasFPowerSeriesAt f (p c) 0 := fun c hc => by
    obtain ⟨M, hM⟩ := ((hc _ (hrnorm.symm ▸ hrρ)).summable.tendsto_atTop_zero.norm).bddAbove_range
    refine ⟨r, ⟨(p c).le_radius_of_bound M fun n => ?_,
      ENNReal.coe_pos.2 (NNReal.coe_pos.1 (by rw [hr]; positivity)), fun {y} hy => ?_⟩⟩
    · have := hM ⟨n, rfl⟩
      simp only [norm_smul, norm_pow, hrnorm] at this
      simpa [p, ContinuousMultilinearMap.norm_mkPiRing, mul_comm] using this
    · rw [zero_add]
      have hy' : ‖y‖ < ρ := by
        have : ‖y‖ < r := by simpa [edist_zero_right, enorm_eq_nnnorm] using hy
        linarith
      simpa only [hp] using hc y hy'
  have h := (hseries a ha).eq_formalMultilinearSeries (hseries b hb)
  funext n
  have := congrArg (fun q : FormalMultilinearSeries ℂ ℂ E => q n fun _ => (1 : ℂ)) h
  simpa only [hp, one_pow, one_smul] using this

variable {𝔸 : Type*} [NormedCommRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

attribute [local instance] ratAlgebra

/-! ### Local injectivity of the exponential -/

/-- An element with `exp c = 1` and `‖c‖ e^{‖c‖} < 1` is zero. -/
theorem eq_zero_of_exp_eq_one {c : 𝔸} (h : exp c = 1) (hc : ‖c‖ * Real.exp ‖c‖ < 1) : c = 0 := by
  have h1 := norm_exp_sub_one_sub_le c
  rw [h, sub_self, zero_sub, norm_neg] at h1
  by_contra hne
  have hpos : 0 < ‖c‖ := norm_pos_iff.2 hne
  nlinarith

/-! ### The logarithm series -/

/-- The coefficients `(-1)^r/(r+1)` of `log(1 + x) = Σ_r (-1)^r x^{r+1}/(r+1)`. -/
def logCoeff (r : ℕ) : ℂ := (-1) ^ r / (r + 1)

theorem norm_logCoeff_le (r : ℕ) : ‖logCoeff r‖ ≤ 1 := by
  have h : ((r : ℂ) + 1) = ((r + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [logCoeff, norm_div, norm_pow, norm_neg, norm_one, one_pow, h, Complex.norm_natCast]
  exact div_le_one_of_le₀ (by exact_mod_cast Nat.succ_pos r) (by positivity)

theorem logCoeff_zero : logCoeff 0 = 1 := by simp [logCoeff]

/-- `log(1 + x) = Σ_r (-1)^r x^{r+1}/(r+1)`. -/
def logSeries (x : 𝔸) : 𝔸 := ∑' r : ℕ, logCoeff r • x ^ (r + 1)

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
theorem norm_logSeries_term_le (x : 𝔸) (r : ℕ) :
    ‖logCoeff r • x ^ (r + 1)‖ ≤ ‖x‖ ^ (r + 1) := by
  rw [norm_smul]
  exact (mul_le_mul (norm_logCoeff_le r) (norm_pow_le' x (Nat.succ_pos r)) (norm_nonneg _)
    zero_le_one).trans_eq (one_mul _)

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
theorem summable_norm_logSeries {x : 𝔸} (hx : ‖x‖ < 1) :
    Summable fun r => ‖logCoeff r • x ^ (r + 1)‖ := by
  have hg : Summable fun r : ℕ => ‖x‖ ^ (r + 1) := by
    simpa only [pow_succ'] using (summable_geometric_of_lt_one (norm_nonneg x) hx).mul_left ‖x‖
  exact Summable.of_nonneg_of_le (fun r => norm_nonneg _) (norm_logSeries_term_le x) hg

omit [CompleteSpace 𝔸] [NormOneClass 𝔸] in
theorem norm_logSeries_le {x : 𝔸} (hx : ‖x‖ < 1) : ‖logSeries x‖ ≤ ‖x‖ / (1 - ‖x‖) := by
  have hs : Summable fun r => ‖logCoeff r • x ^ (r + 1)‖ := summable_norm_logSeries hx
  have h := norm_tsum_le_tsum_norm (E := 𝔸) (f := fun r => logCoeff r • x ^ (r + 1)) hs
  rw [logSeries]
  refine h.trans ?_
  calc ∑' r, ‖logCoeff r • x ^ (r + 1)‖ ≤ ∑' r : ℕ, ‖x‖ * ‖x‖ ^ r :=
        hs.tsum_le_tsum (fun r => (norm_logSeries_term_le x r).trans_eq
          (pow_succ' ‖x‖ r)) ((summable_geometric_of_lt_one (norm_nonneg x) hx).mul_left ‖x‖)
    _ = ‖x‖ / (1 - ‖x‖) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (norm_nonneg x) hx, div_eq_mul_inv]

/-! ### `exp(log(1 + x)) = 1 + x` -/

omit [NormOneClass 𝔸] in
/-- The termwise derivative of `t ↦ log(1 + tx)` is `x Σ_k (-tx)^k`. -/
theorem hasDerivAt_logSeries_smul {x : 𝔸} {ρ : ℝ} (hρ : ρ * ‖x‖ < 1) {t : ℂ}
    (ht : t ∈ ball (0 : ℂ) ρ) :
    HasDerivAt (fun s : ℂ => logSeries (s • x)) (x * ∑' k : ℕ, (-t • x) ^ k) t := by
  have hρ0 : 0 < ρ := lt_of_le_of_lt (norm_nonneg t) (mem_ball_zero_iff.1 ht)
  have hρx : 0 ≤ ρ * ‖x‖ := by positivity
  set g : ℕ → ℂ → 𝔸 := fun r s => (logCoeff r * s ^ (r + 1)) • x ^ (r + 1)
  set g' : ℕ → ℂ → 𝔸 := fun r s => ((-1) ^ r * s ^ r) • x ^ (r + 1)
  have hfun : (fun s : ℂ => logSeries (s • x)) = fun s => ∑' r, g r s := funext fun s => by
    simp only [logSeries, g, smul_pow, smul_smul, mul_comm]
  have hg : ∀ r s, s ∈ ball (0 : ℂ) ρ → HasDerivAt (g r) (g' r s) s := fun r s _ => by
    have h := ((hasDerivAt_pow (r + 1) s).const_mul (logCoeff r)).smul_const (x ^ (r + 1))
    refine h.congr_deriv ?_
    have hr : ((r : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
    show (logCoeff r * (((r + 1 : ℕ) : ℂ) * s ^ (r + 1 - 1))) • x ^ (r + 1) =
      ((-1) ^ r * s ^ r) • x ^ (r + 1)
    congr 1
    rw [Nat.add_sub_cancel, logCoeff]
    push_cast
    field_simp
  have hbound : ∀ r s, s ∈ ball (0 : ℂ) ρ → ‖g' r s‖ ≤ ‖x‖ * (ρ * ‖x‖) ^ r := fun r s hs => by
    have hs' : ‖s‖ ≤ ρ := (mem_ball_zero_iff.1 hs).le
    rw [norm_smul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
    calc ‖s‖ ^ r * ‖x ^ (r + 1)‖ ≤ ρ ^ r * ‖x‖ ^ (r + 1) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hs' r) (norm_pow_le' x (Nat.succ_pos r))
            (norm_nonneg _) (by positivity)
      _ = ‖x‖ * (ρ * ‖x‖) ^ r := by ring
  have h := hasDerivAt_tsum_of_isPreconnected
    ((summable_geometric_of_lt_one hρx hρ).mul_left ‖x‖) isOpen_ball
    (convex_ball (0 : ℂ) ρ).isPreconnected hg hbound (mem_ball_self hρ0)
    (by simp [g]) ht
  have hsum : Summable fun k : ℕ => (-t • x) ^ k := by
    refine summable_geometric_of_norm_lt_one ?_
    calc ‖-t • x‖ = ‖t‖ * ‖x‖ := by rw [norm_smul, norm_neg]
      _ ≤ ρ * ‖x‖ := mul_le_mul_of_nonneg_right (mem_ball_zero_iff.1 ht).le (norm_nonneg _)
      _ < 1 := hρ
  have heq : ∑' r, g' r t = x * ∑' k : ℕ, (-t • x) ^ k := by
    rw [← hsum.tsum_mul_left]
    refine tsum_congr fun r => ?_
    show ((-1) ^ r * t ^ r) • x ^ (r + 1) = x * (-t • x) ^ r
    rw [smul_pow, mul_smul_comm, ← pow_succ', neg_pow t r]
  rw [hfun]
  exact h.congr_deriv heq

omit [NormOneClass 𝔸] in
/-- **`exp(log(1 + x)) = 1 + x`** for `‖x‖ < 1`. -/
theorem exp_logSeries {x : 𝔸} (hx : ‖x‖ < 1) : exp (logSeries x) = 1 + x := by
  set ρ : ℝ := 2 / (1 + ‖x‖)
  have hx0 := norm_nonneg x
  have hρ1 : 1 < ρ := by rw [lt_div_iff₀ (by positivity)]; linarith
  have hρ : ρ * ‖x‖ < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one (by positivity)]; linarith
  set L : ℂ → 𝔸 := fun s => logSeries (s • x)
  set P : ℂ → 𝔸 := fun s => exp (-L s) * (1 + s • x)
  have hderiv : ∀ t ∈ ball (0 : ℂ) ρ, HasDerivAt P 0 t := fun t ht => by
    have hL := hasDerivAt_logSeries_smul hρ ht
    have hE : HasDerivAt (fun s => exp (-L s)) (exp (-L t) * -(x * ∑' k : ℕ, (-t • x) ^ k)) t := by
      have h1 := (hasFDerivAt_exp (𝕂 := ℂ) (x := -L t)).comp_hasDerivAt t hL.neg
      have h2 : (exp (-L t) • (1 : 𝔸 →L[ℂ] 𝔸)) (-(x * ∑' k : ℕ, (-t • x) ^ k)) =
          exp (-L t) * -(x * ∑' k : ℕ, (-t • x) ^ k) := by simp
      exact h1.congr_deriv h2
    have hD : HasDerivAt (fun s : ℂ => 1 + s • x) x t := by
      simpa using ((hasDerivAt_id t).smul_const x).const_add 1
    have hgeom : (∑' k : ℕ, (-t • x) ^ k) * (1 + t • x) = 1 := by
      have hn : ‖-t • x‖ < 1 := by
        calc ‖-t • x‖ = ‖t‖ * ‖x‖ := by rw [norm_smul, norm_neg]
          _ ≤ ρ * ‖x‖ := mul_le_mul_of_nonneg_right (mem_ball_zero_iff.1 ht).le (norm_nonneg _)
          _ < 1 := hρ
      have := geom_series_mul_neg (-t • x) hn
      have e : (1 : 𝔸) - -t • x = 1 + t • x := by rw [neg_smul, sub_neg_eq_add]
      rwa [e] at this
    have hval : exp (-L t) * -(x * ∑' k : ℕ, (-t • x) ^ k) * (1 + t • x) + exp (-L t) * x =
        0 := by
      calc exp (-L t) * -(x * ∑' k : ℕ, (-t • x) ^ k) * (1 + t • x) + exp (-L t) * x
          = exp (-L t) * (x - x * ((∑' k : ℕ, (-t • x) ^ k) * (1 + t • x))) := by ring
        _ = 0 := by rw [hgeom, mul_one, sub_self, mul_zero]
    exact (hE.mul hD).congr_deriv hval
  have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) ρ).isPreconnected
    (fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hderiv t ht).deriv) (x := (1 : ℂ)) (y := 0)
    (by simpa using hρ1) (mem_ball_self (by linarith))
  have hL0 : L 0 = 0 := by simp [L, logSeries]
  have hL1 : L 1 = logSeries x := by simp [L]
  simp only [P, hL0, hL1, neg_zero, exp_zero, zero_smul, add_zero, mul_one, one_smul] at hconst
  calc exp (logSeries x) = exp (logSeries x) * (exp (-logSeries x) * (1 + x)) := by
        rw [hconst, mul_one]
    _ = exp (logSeries x + -logSeries x) * (1 + x) := by rw [exp_add, mul_assoc]
    _ = 1 + x := by rw [add_neg_cancel, exp_zero, one_mul]

end GaloisForLFunctions.HTGeometry.FormationDust
