import GaloisForLFunctions.RHTower.IntegerBeurlingPerturbation
import GaloisForLFunctions.RHTower.ZetaConvexityBound
import GaloisForLFunctions.HTGeometry.LogQuotientDerivativeCeiling
import GaloisForLFunctions.HTGeometry.ZetaTailBound
import GaloisForLFunctions.RHTower.ZetaStripPolynomialBound

/-!
# The continued `L(e)` is logarithmic when the integer count is regular

Let an integer-supported Beurling system have integer masses `a` and generator von Mangoldt
function `Λ - e` (`IntegerBeurlingPerturbation`).  Suppose `Σ_{n ≤ x} a n = A x + O(x^θ)` and the
perturbation's Chebyshev function is `Σ_ρ c_ρ x^ρ + O(x^η)` over finitely many exponents of bounded
height.  Then for every `σ > max θ η` the continuation `s(Σ c_ρ/(s-ρ) + ∫_1^∞ R(t) t^{-(s+1)} dt)`
of `L(e)` is `O(log t)` on `Re s = σ` (`exists_norm_pertLogDeriv_le_log`).

The logarithmic derivative of `L(a)/ζ` is `L(e)`.  On discs at height `t`, a primitive `g` of the
continued `L(e)` satisfies `exp g · (s-1)ζ(s) = (s-1)L(a)(s)` (`exists_log_ratio_on_ball`).  Both
sides are polynomially bounded; the logarithmic-derivative ceiling for zero-free quotients
(`GaloisForLFunctions.HTGeometry.norm_deriv_le_of_exp_mul_eq`) needs no lower bound for zeta away
from `Re s = 3`.  For a set `Q` of deleted primes, `a = 1_S` and `e = Λ_Q`.
-/

open Filter Topology Complex Asymptotics MeasureTheory Set Metric ArithmeticFunction

namespace RHTower

noncomputable section

namespace IntegerBeurling

/-- A Mellin integral of a function bounded by `C t^r` on `[1, ∞)` is at most `C/(Re s - r)`. -/
theorem norm_integral_mul_cpow_le {G : ℝ → ℂ} {C r : ℝ}
    (hG : ∀ t : ℝ, 1 ≤ t → ‖G t‖ ≤ C * t ^ r) {s : ℂ} (hs : r < s.re) :
    ‖∫ t in Ioi (1:ℝ), G t * (t : ℂ) ^ (-(s + 1))‖ ≤ C / (s.re - r) := by
  have hexp : r - s.re - 1 < -1 := by linarith
  have hmaj : IntegrableOn (fun t : ℝ => C * t ^ (r - s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt hexp one_pos).const_mul C
  have hbound : ∀ t ∈ Ioi (1:ℝ), ‖G t * (t : ℂ) ^ (-(s + 1))‖ ≤ C * t ^ (r - s.re - 1) := by
    intro t ht
    have ht0 : (0:ℝ) < t := zero_lt_one.trans ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-(s + 1)).re = -s.re - 1 := by simp; ring
    rw [hre]
    calc ‖G t‖ * t ^ (-s.re - 1) ≤ C * t ^ r * t ^ (-s.re - 1) :=
          mul_le_mul_of_nonneg_right (hG t (le_of_lt ht)) (Real.rpow_nonneg ht0.le _)
      _ = C * t ^ (r - s.re - 1) := by
          rw [mul_assoc, ← Real.rpow_add ht0]; ring_nf
  calc ‖∫ t in Ioi (1:ℝ), G t * (t : ℂ) ^ (-(s + 1))‖
      ≤ ∫ t in Ioi (1:ℝ), C * t ^ (r - s.re - 1) :=
        norm_integral_le_of_norm_le hmaj ((ae_restrict_iff' measurableSet_Ioi).mpr
          (Eventually.of_forall hbound))
    _ = C / (s.re - r) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt hexp one_pos, Real.one_rpow]
        have : r - s.re - 1 + 1 = -(s.re - r) := by ring
        rw [this]
        field_simp

/-- A Dirichlet series with coefficients of modulus at most one differs from its first coefficient
by at most `4 · 2^{-Re s}` on `Re s ≥ 2`. -/
theorem norm_LSeries_sub_apply_one_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {s : ℂ}
    (hs : 2 ≤ s.re) : ‖LSeries f s - f 1‖ ≤ 4 * (2 : ℝ) ^ (-s.re) := by
  have hs1 : 1 < s.re := by linarith
  have hsum : Summable (LSeries.term f s) := by
    refine LSeriesSummable_of_le_const_mul_rpow (x := 1) hs1 ⟨1, fun n _ => ?_⟩
    simpa using hf n
  have hsplit : LSeries f s - f 1 = ∑' k : ℕ, f (k + 2) / ((k : ℂ) + 2) ^ s := by
    rw [LSeries, hsum.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hsum).tsum_eq_zero_add]
    · simp only [LSeries.term_zero, zero_add]
      rw [LSeries.term_of_ne_zero (by norm_num)]
      simp only [Nat.cast_one, Complex.one_cpow, div_one, add_sub_cancel_left]
      refine tsum_congr fun k => ?_
      rw [LSeries.term_of_ne_zero (by omega)]
      push_cast
      ring_nf
  rw [hsplit]
  have hbound : ∀ k : ℕ, ‖f (k + 2) / ((k : ℂ) + 2) ^ s‖ ≤ ‖(1 : ℂ) / ((k : ℂ) + 2) ^ s‖ := by
    intro k
    rw [norm_div, norm_div, norm_one]
    exact div_le_div_of_nonneg_right (hf _) (norm_nonneg _)
  have hsumt := GaloisForLFunctions.HTGeometry.summable_norm_tail hs
  have hsumf : Summable fun k : ℕ => ‖f (k + 2) / ((k : ℂ) + 2) ^ s‖ :=
    hsumt.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  have hbound2 : ∀ k : ℕ, ‖(1 : ℂ) / ((k : ℂ) + 2) ^ s‖
      ≤ 4 * (2 : ℝ) ^ (-s.re) * ((1 : ℝ) / ((k : ℝ) + 2) ^ 2) := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hcast : (((k : ℝ) + 2 : ℝ) : ℂ) = (k : ℂ) + 2 := by push_cast; ring
    rw [norm_div, norm_one, ← hcast, Complex.norm_cpow_eq_rpow_re_of_pos hk]
    exact GaloisForLFunctions.HTGeometry.inv_rpow_shift_le hs k
  refine (norm_tsum_le_tsum_norm hsumf).trans ?_
  refine (Summable.tsum_mono hsumf
    (GaloisForLFunctions.HTGeometry.summable_zetaTailWeight.mul_left _)
    fun k => (hbound k).trans (hbound2 k)).trans ?_
  rw [tsum_mul_left]
  have hc : (0 : ℝ) ≤ 4 * (2 : ℝ) ^ (-s.re) := by positivity
  nlinarith [GaloisForLFunctions.HTGeometry.tsum_zetaTailWeight_le, hc]

variable {a e : ℕ → ℝ}

theorem norm_countSeq_le (ha : ∀ n, |a n| ≤ 1) (n : ℕ) : ‖countSeq a n‖ ≤ 1 := by
  rw [countSeq, Complex.norm_real, Real.norm_eq_abs]
  exact ha n

theorem norm_LSeries_countSeq_sub_one_le (ha : ∀ n, |a n| ≤ 1) (ha1 : a 1 = 1) {s : ℂ}
    (hs : 3 ≤ s.re) : ‖LSeries (countSeq a) s - 1‖ ≤ 1 / 2 := by
  have h := norm_LSeries_sub_apply_one_le (norm_countSeq_le ha) (s := s) (by linarith)
  have h1 : countSeq a 1 = 1 := by simp [countSeq, ha1]
  rw [h1] at h
  have h2 : (2 : ℝ) ^ (-s.re) ≤ 2 ^ (-(3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (2 : ℝ) ^ (-(3 : ℝ)) = 1 / 8 := by
    rw [Real.rpow_neg (by norm_num)]; norm_num
  rw [h3] at h2
  calc ‖LSeries (countSeq a) s - 1‖ ≤ 4 * (2 : ℝ) ^ (-s.re) := h
    _ ≤ 4 * (1 / 8) := by gcongr
    _ = 1 / 2 := by norm_num

variable (e) in
/-- The continuation `s (Σ_ρ c_ρ/(s-ρ) + ∫_1^∞ R(t) t^{-(s+1)} dt)` of `L(e)`. -/
def pertLogDeriv (J : Finset ℂ) (c : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * (∑ ρ ∈ J, c ρ / (z - ρ) + remainderIntegral e J c z)

theorem differentiableAt_pertLogDeriv {J : Finset ℂ} {c : ℂ → ℂ} {η : ℝ}
    (hψ : (fun x : ℝ => (pertChebyshev e x : ℂ) - ∑ ρ ∈ J, c ρ * (x : ℂ) ^ ρ) =O[atTop]
      fun x : ℝ => x ^ η)
    {z : ℂ} (hz : η < z.re) (hzJ : ∀ ρ ∈ J, z ≠ ρ) :
    DifferentiableAt ℂ (pertLogDeriv e J c) z := by
  unfold pertLogDeriv
  refine differentiableAt_id.mul (DifferentiableAt.add ?_
    (differentiableAt_remainderIntegral hψ hz))
  refine DifferentiableAt.fun_sum fun ρ hρ => ?_
  exact (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _))
    (sub_ne_zero.mpr (hzJ ρ hρ))

variable (a) in
/-- `L(a)/ζ`. -/
def ratio (z : ℂ) : ℂ := LSeries (countSeq a) z / riemannZeta z

theorem ratio_ne_zero (ha : ∀ n, |a n| ≤ 1) (ha1 : a 1 = 1) {z : ℂ} (hz : 3 ≤ z.re) :
    ratio a z ≠ 0 := by
  have hL : LSeries (countSeq a) z ≠ 0 := by
    intro h
    have := norm_LSeries_countSeq_sub_one_le ha ha1 hz
    rw [h, zero_sub, norm_neg, norm_one] at this
    linarith
  have hζ : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
  exact div_ne_zero hL hζ

/-- **A logarithm of `L(1_S)/ζ` on discs.**  On a disc about `w₀` (`Re w₀ ≥ 3`) lying in
`Re s > max θ η` and avoiding the exponents, a primitive `g` of the continued `L(Λ_Q)` satisfies
`exp g · (s-1)ζ(s) = (s-1)L(1_S)(s)` (continued).  Near `w₀` this is `exp g = L(1_S)/ζ`; the identity
theorem carries it across the disc, through any common zeros of the two sides. -/
theorem exists_log_ratio_on_ball (ha : ∀ n, |a n| ≤ 1) (ha1 : a 1 = 1)
    (he : ∀ n, |e n| ≤ Real.log n)
    (hconv : LSeries.convolution (fun n => ((Λ n - e n : ℝ) : ℂ)) (countSeq a) =
      LSeries.logMul (countSeq a))
    {A θ η : ℝ} {J : Finset ℂ} {c : ℂ → ℂ} (hθ : 0 ≤ θ)
    (hN : (fun x : ℝ => count a x - A * x) =O[atTop] fun x => x ^ θ)
    (hψ : (fun x : ℝ => (pertChebyshev e x : ℂ) - ∑ ρ ∈ J, c ρ * (x : ℂ) ^ ρ) =O[atTop]
      fun x : ℝ => x ^ η)
    (hJ : ∀ ρ ∈ J, ρ.re < 2) {w₀ : ℂ} (hw₀ : 3 ≤ w₀.re) {r : ℝ} (hr : 1 ≤ r)
    (hball : ∀ z ∈ ball w₀ r, θ < z.re ∧ η < z.re ∧ ∀ ρ ∈ J, z ≠ ρ) :
    ∃ g : ℂ → ℂ, (∀ z ∈ ball w₀ r, HasDerivAt g (pertLogDeriv e J c z) z) ∧
      (∀ z ∈ ball w₀ r, Complex.exp (g z) * zetaResidueFactor z = numerator a A z) ∧
      g w₀ = Complex.log (ratio a w₀) := by
  have hd : DifferentiableOn ℂ (pertLogDeriv e J c) (ball w₀ r) := fun z hz =>
    (differentiableAt_pertLogDeriv hψ (hball z hz).2.1
      (hball z hz).2.2).differentiableWithinAt
  obtain ⟨g, hg0, hg⟩ := hd.isExactOn_ball.with_val_at w₀ (Complex.log (ratio a w₀))
  refine ⟨g, hg, ?_, hg0⟩
  -- near `w₀`: `exp g = L(1_S)/ζ`
  set V : Set ℂ := ball w₀ 1 with hV
  have hVsub : V ⊆ ball w₀ r := ball_subset_ball hr
  have hVre : ∀ z ∈ V, 2 < z.re := by
    intro z hz
    rw [hV, mem_ball, dist_eq_norm] at hz
    have := Complex.abs_re_le_norm (z - w₀)
    rw [Complex.sub_re] at this
    have := neg_abs_le (z.re - w₀.re)
    linarith
  set H : ℂ → ℂ := fun z => ratio a z * Complex.exp (-g z) with hH
  have hratio_d : ∀ z ∈ V, HasDerivAt (ratio a)
      (ratio a z * LSeries (pertSeq e) z) z := by
    intro z hz
    have hz1 : 1 < z.re := by linarith [hVre z hz]
    have hz1' : z ≠ 1 := by
      intro h; rw [h, Complex.one_re] at hz1; exact lt_irrefl _ hz1
    have habs : LSeries.abscissaOfAbsConv (countSeq a) < z.re :=
      (abscissa_countSeq_le ha).trans_lt (by exact_mod_cast hz1)
    have hdL : DifferentiableAt ℂ (LSeries (countSeq a)) z :=
      (LSeries_hasDerivAt habs).differentiableAt
    have hdζ : DifferentiableAt ℂ riemannZeta z := differentiableAt_riemannZeta hz1'
    have hζ : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_le_re hz1.le
    have hdiff : DifferentiableAt ℂ (ratio a) z := hdL.div hdζ hζ
    have h := deriv_LSeries_div_riemannZeta ha he hconv hz1
    have heq : (fun z => LSeries (countSeq a) z / riemannZeta z) = ratio a := rfl
    rw [heq] at h
    have h' : deriv (ratio a) z =
        ratio a z * LSeries (pertSeq e) z := h
    rw [← h']
    exact hdiff.hasDerivAt
  have hΛ : ∀ z ∈ V, LSeries (pertSeq e) z =
      pertLogDeriv e J c z := by
    intro z hz
    have h := LSeries_pertSeq_eq he hψ (s := z) (hVre z hz) (hball z (hVsub hz)).2.1
      (fun ρ hρ => (hJ ρ hρ).trans (hVre z hz))
    exact h
  have hHd : ∀ z ∈ V, HasDerivAt H 0 z := by
    intro z hz
    have h1 := hratio_d z hz
    have h2 := ((hg z (hVsub hz)).neg).cexp
    have h3 : HasDerivAt (fun y => ratio a y * Complex.exp (-g y))
        (ratio a z * LSeries (pertSeq e) z *
          Complex.exp (-g z) + ratio a z * (Complex.exp (-g z) *
            -pertLogDeriv e J c z)) z := h1.mul h2
    exact h3.congr_deriv (by rw [hΛ z hz]; ring)
  have hHdiff : DifferentiableOn ℂ H V := fun z hz => (hHd z hz).differentiableAt.differentiableWithinAt
  have hconst : ∀ z ∈ V, H z = H w₀ := fun z hz =>
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball w₀ 1).isPreconnected hHdiff
      (fun y hy => (hHd y hy).deriv) hz (mem_ball_self one_pos)
  have hHw₀ : H w₀ = 1 := by
    rw [hH]
    simp only
    rw [hg0, Complex.exp_neg, Complex.exp_log (ratio_ne_zero ha ha1 hw₀)]
    exact mul_inv_cancel₀ (ratio_ne_zero ha ha1 hw₀)
  have hexpV : ∀ z ∈ V, Complex.exp (g z) * zetaResidueFactor z = numerator a A z := by
    intro z hz
    have hz1 : 1 < z.re := by linarith [hVre z hz]
    have hz1' : z ≠ 1 := by
      intro h; rw [h, Complex.one_re] at hz1; exact lt_irrefl _ hz1
    have hH1 : ratio a z * Complex.exp (-g z) = 1 := (hconst z hz).trans hHw₀
    have hexp : Complex.exp (g z) = ratio a z := by
      have hne := Complex.exp_ne_zero (g z)
      rw [Complex.exp_neg] at hH1
      field_simp at hH1
      exact hH1.symm
    rw [hexp, numerator_eq ha hθ hN hz1 (hball z (hVsub hz)).1,
      zetaResidueFactor_of_ne hz1', ratio]
    have hζ : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_le_re hz1.le
    field_simp
  -- the identity theorem on the whole disc
  have hana : AnalyticOnNhd ℂ (fun z => Complex.exp (g z) * zetaResidueFactor z -
      numerator a A z) (ball w₀ r) := by
    have hdiffon : DifferentiableOn ℂ (fun z => Complex.exp (g z) * zetaResidueFactor z -
        numerator a A z) (ball w₀ r) := fun z hz =>
      ((((hg z hz).differentiableAt.cexp).mul (differentiable_zetaResidueFactor z)).sub
        (differentiableAt_numerator hθ hN (hball z hz).1)).differentiableWithinAt
    exact hdiffon.analyticOnNhd isOpen_ball
  have hev : (fun z => Complex.exp (g z) * zetaResidueFactor z - numerator a A z)
      =ᶠ[𝓝 w₀] 0 := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (one_pos : (0:ℝ) < 1))] with z hz
    rw [Pi.zero_apply, hexpV z hz, sub_self]
  have hzero := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball w₀ r).isPreconnected (mem_ball_self (by linarith)) hev
  intro z hz
  have := hzero hz
  simp only [Pi.zero_apply] at this
  exact sub_eq_zero.mp this

/-- The count defect is `O(t^θ)` uniformly on `[1, ∞)`. -/
theorem exists_forall_norm_sum_countDefectSeq_le (ha : ∀ n, |a n| ≤ 1) {A θ : ℝ} (hθ : 0 ≤ θ)
    (hN : (fun x : ℝ => count a x - A * x) =O[atTop] fun x => x ^ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, countDefectSeq a A k‖ ≤ C * t ^ θ := by
  obtain ⟨C₀, hC₀⟩ := (countDefect_isBigO hθ hN).bound
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp hC₀
  refine ⟨max (max C₀ 0) (max t₀ 1 * (1 + |A|)), le_max_of_le_left (le_max_right _ _),
    fun t ht => ?_⟩
  have htθ : 1 ≤ t ^ θ := Real.one_le_rpow ht hθ
  have hpos : 0 ≤ t ^ θ := by linarith
  rcases le_or_gt t₀ t with h | h
  · have := ht₀ t h
    rw [Real.norm_eq_abs, abs_of_nonneg hpos] at this
    calc _ ≤ C₀ * t ^ θ := this
      _ ≤ max (max C₀ 0) (max t₀ 1 * (1 + |A|)) * t ^ θ :=
          mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _)) hpos
  · have hterm : ∀ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖countDefectSeq a A k‖ ≤ 1 + |A| := by
      intro k _
      rw [countDefectSeq]
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add (norm_countSeq_le ha k) le_rfl
    have hcard : ((Finset.Icc 1 ⌊t⌋₊).card : ℝ) ≤ max t₀ 1 := by
      rw [Nat.card_Icc, Nat.add_sub_cancel]
      exact (Nat.floor_le (by linarith)).trans (le_max_of_le_left h.le)
    calc ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, countDefectSeq a A k‖
        ≤ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖countDefectSeq a A k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 + |A|) := Finset.sum_le_sum hterm
      _ = ((Finset.Icc 1 ⌊t⌋₊).card : ℝ) * (1 + |A|) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ max t₀ 1 * (1 + |A|) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ max (max C₀ 0) (max t₀ 1 * (1 + |A|)) * 1 := by rw [mul_one]; exact le_max_right _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left htθ (le_max_of_le_left (le_max_right _ _))

theorem norm_countDefectIntegral_le {A θ C : ℝ}
    (hC : ∀ t : ℝ, 1 ≤ t → ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, countDefectSeq a A k‖ ≤ C * t ^ θ)
    {z : ℂ} (hz : θ < z.re) : ‖countDefectIntegral a A z‖ ≤ C / (z.re - θ) :=
  norm_integral_mul_cpow_le hC hz

/-- `|ζ(w)| ≤ 2 + 2|Im w|/σ₀` on `σ₀ ≤ Re w`, `|Im w| ≥ 2`, `0 < σ₀`. -/
theorem norm_riemannZeta_le_of_re_ge {σ₀ : ℝ} (hσ₀ : 0 < σ₀) {w : ℂ}
    (hw : σ₀ ≤ w.re) (hwi : 2 ≤ |w.im|) :
    ‖riemannZeta w‖ ≤ 2 + 2 * |w.im| / σ₀ := by
  have h0 : 0 ≤ 2 * |w.im| / σ₀ := by positivity
  rcases le_or_gt w.re 2 with h2 | h2
  · have h := norm_riemannZeta_le_of_re_pos (lt_of_lt_of_le hσ₀ hw) h2 hwi
    rw [← Complex.re_add_im w] at h ⊢
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
      Complex.mul_im, zero_add] at h ⊢
    refine h.trans (by gcongr)
  · have h := GaloisForLFunctions.HTGeometry.norm_riemannZeta_sub_one_le_rpow (s := w) h2.le
    have h3 : (2 : ℝ) ^ (-w.re) ≤ 2 ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h4 : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by
      rw [Real.rpow_neg (by norm_num)]; norm_num
    rw [h4] at h3
    have := norm_le_norm_sub_add (riemannZeta w) 1
    rw [norm_one] at this
    linarith

theorem norm_zetaResidueFactor_le_region {σ₀ t : ℝ} (hσ₀ : 0 < σ₀) {w : ℂ} (hre0 : σ₀ ≤ w.re)
    (hre7 : w.re ≤ 7) (him2 : 2 ≤ |w.im|) (himt : |w.im| ≤ t + 4) :
    ‖zetaResidueFactor w‖ ≤ (2 + 2 / σ₀) * (t + 11) ^ 2 := by
  have hw1 : w ≠ 1 := by
    intro h; rw [h] at him2; simp at him2; norm_num at him2
  rw [zetaResidueFactor_of_ne hw1, norm_mul]
  have hz := norm_riemannZeta_le_of_re_ge hσ₀ hre0 him2
  have ht : 0 ≤ t + 2 := by linarith [abs_nonneg w.im]
  have hw1n : ‖w - 1‖ ≤ t + 10 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    have : |w.re - 1| ≤ 6 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hσinv : 0 ≤ 2 / σ₀ := by positivity
  have hzt : ‖riemannZeta w‖ ≤ (2 + 2 / σ₀) * (t + 11) := by
    refine hz.trans ?_
    have h1 : 2 * |w.im| / σ₀ = 2 / σ₀ * |w.im| := by ring
    have h2 : 2 / σ₀ * |w.im| ≤ 2 / σ₀ * (t + 11) :=
      mul_le_mul_of_nonneg_left (by linarith) hσinv
    have h3 : 2 ≤ 2 * (t + 11) := by linarith
    have h4 : (2 + 2 / σ₀) * (t + 11) = 2 * (t + 11) + 2 / σ₀ * (t + 11) := by ring
    linarith
  calc ‖w - 1‖ * ‖riemannZeta w‖ ≤ (t + 10) * ((2 + 2 / σ₀) * (t + 11)) :=
        mul_le_mul hw1n hzt (norm_nonneg _) (by linarith)
    _ ≤ (t + 11) * ((2 + 2 / σ₀) * (t + 11)) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (by positivity) (by linarith))
    _ = (2 + 2 / σ₀) * (t + 11) ^ 2 := by ring

theorem norm_numerator_le_region {A θ δ σ₀ t CN : ℝ} (hδ : 0 < δ) (hσ₀ : 0 < σ₀)
    (hσ₀θ : θ + δ ≤ σ₀) (hCN0 : 0 ≤ CN)
    (hCN : ∀ u : ℝ, 1 ≤ u → ‖∑ k ∈ Finset.Icc 1 ⌊u⌋₊, countDefectSeq a A k‖ ≤ CN * u ^ θ)
    {w : ℂ} (hre0 : σ₀ ≤ w.re) (hre7 : w.re ≤ 7) (him2 : 2 ≤ |w.im|) (himt : |w.im| ≤ t + 4) :
    ‖numerator a A w‖ ≤ ((|A| + 1) * (2 + 2 / σ₀) + CN / δ) * (t + 11) ^ 2 := by
  have hZ := norm_zetaResidueFactor_le_region hσ₀ hre0 hre7 him2 himt
  have hint := norm_countDefectIntegral_le hCN (z := w) (by linarith)
  have hint' : ‖countDefectIntegral a A w‖ ≤ CN / δ :=
    hint.trans (div_le_div_of_nonneg_left hCN0 hδ (by linarith))
  have ht : 0 ≤ t + 2 := by linarith [abs_nonneg w.im]
  have hw1n : ‖w - 1‖ ≤ t + 11 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    have : |w.re - 1| ≤ 6 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hwn : ‖w‖ ≤ t + 11 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have : |w.re| ≤ 7 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  unfold numerator
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  set X : ℝ := (2 + 2 / σ₀) * (t + 11) ^ 2 with hX
  have hX0 : 0 ≤ X := by rw [hX]; exact mul_nonneg (by positivity) (sq_nonneg _)
  have h1 : |A| * ‖zetaResidueFactor w‖ ≤ |A| * X := mul_le_mul_of_nonneg_left hZ (abs_nonneg A)
  have h2 : ‖w - 1‖ * ‖w‖ * ‖countDefectIntegral a A w‖ ≤ (t + 11) * (t + 11) * (CN / δ) :=
    mul_le_mul (mul_le_mul hw1n hwn (norm_nonneg _) (by linarith)) hint' (norm_nonneg _)
      (mul_nonneg (by linarith) (by linarith))
  have h3 : ((|A| + 1) * (2 + 2 / σ₀) + CN / δ) * (t + 11) ^ 2 =
      |A| * X + X + (t + 11) * (t + 11) * (CN / δ) := by rw [hX]; ring
  rw [h3]
  linarith

theorem log_three_lt_two : Real.log 3 < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [h2]; nlinarith

/-- At `Re w = 3` the logarithm of `L(1_S)/ζ` is bounded by `2 + π`. -/
theorem norm_log_ratio_le (ha : ∀ n, |a n| ≤ 1) (ha1 : a 1 = 1) {w : ℂ} (hw : w.re = 3) :
    ‖Complex.log (ratio a w)‖ ≤ 2 + Real.pi := by
  have hL := norm_LSeries_countSeq_sub_one_le ha ha1 (show 3 ≤ w.re by rw [hw])
  have hζu := GaloisForLFunctions.HTGeometry.norm_riemannZeta_sub_one_le_rpow
    (s := w) (by rw [hw]; norm_num)
  have h8 : (2 : ℝ) ^ (-w.re) = 1 / 8 := by
    rw [hw, Real.rpow_neg (by norm_num)]; norm_num
  rw [h8] at hζu
  have hLlo : 1 / 2 ≤ ‖LSeries (countSeq a) w‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - LSeries (countSeq a) w)
    rw [norm_one, sub_sub_cancel, norm_sub_rev] at this; linarith
  have hLhi : ‖LSeries (countSeq a) w‖ ≤ 3 / 2 := by
    have := norm_le_norm_sub_add (LSeries (countSeq a) w) 1
    rw [norm_one] at this; linarith
  have hζlo : 1 / 2 ≤ ‖riemannZeta w‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - riemannZeta w)
    rw [norm_one, sub_sub_cancel, norm_sub_rev] at this; linarith
  have hζhi : ‖riemannZeta w‖ ≤ 3 / 2 := by
    have := norm_le_norm_sub_add (riemannZeta w) 1
    rw [norm_one] at this; linarith
  have hRlo : 1 / 3 ≤ ‖ratio a w‖ := by
    rw [ratio, norm_div, le_div_iff₀ (by linarith)]; nlinarith
  have hRhi : ‖ratio a w‖ ≤ 3 := by
    rw [ratio, norm_div, div_le_iff₀ (by linarith)]; nlinarith
  have hl3 := log_three_lt_two
  have hlog : |Real.log ‖ratio a w‖| ≤ 2 := by
    rw [abs_le]
    constructor
    · have h := Real.log_le_log (by norm_num) hRlo
      rw [one_div, Real.log_inv] at h
      linarith
    · have := Real.log_le_log (by linarith) hRhi
      linarith
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.log_re, Complex.log_im]
  exact add_le_add hlog (Complex.abs_arg_le_pi _)

theorem one_le_norm_zetaResidueFactor {w : ℂ} (hw : w.re = 3) : 1 ≤ ‖zetaResidueFactor w‖ := by
  have hζu := GaloisForLFunctions.HTGeometry.norm_riemannZeta_sub_one_le_rpow
    (s := w) (by rw [hw]; norm_num)
  have h8 : (2 : ℝ) ^ (-w.re) = 1 / 8 := by
    rw [hw, Real.rpow_neg (by norm_num)]; norm_num
  rw [h8] at hζu
  have hζc : 1 / 2 ≤ ‖riemannZeta w‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - riemannZeta w)
    rw [norm_one, sub_sub_cancel, norm_sub_rev] at this; linarith
  have hw1 : w ≠ 1 := by intro h; rw [h] at hw; simp at hw
  rw [zetaResidueFactor_of_ne hw1, norm_mul]
  have h2 : 2 ≤ ‖w - 1‖ := by
    have := Complex.abs_re_le_norm (w - 1)
    rw [Complex.sub_re, hw, Complex.one_re] at this
    norm_num at this; linarith
  nlinarith

theorem region_of_mem_closedBall {t R σ₀ : ℝ} (hre : 3 - R = σ₀) (hR : R ≤ 4)
    (ht : R + 2 ≤ t) {w : ℂ} (hw : w ∈ closedBall ((3 : ℂ) + (t : ℂ) * I) R) :
    σ₀ ≤ w.re ∧ w.re ≤ 7 ∧ 2 ≤ |w.im| ∧ |w.im| ≤ t + 4 := by
  rw [mem_closedBall, dist_eq_norm] at hw
  have h1 := Complex.abs_re_le_norm (w - ((3 : ℂ) + (t : ℂ) * I))
  have h2 := Complex.abs_im_le_norm (w - ((3 : ℂ) + (t : ℂ) * I))
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.add_im, Complex.mul_im,
    mul_zero, mul_one, sub_zero, add_zero] at h1 h2
  norm_num at h1 h2
  have h1' := neg_abs_le (w.re - 3)
  have h1'' := le_abs_self (w.re - 3)
  have h2' := neg_abs_le (w.im - t)
  have h2'' := le_abs_self (w.im - t)
  have him : 2 ≤ w.im := by linarith
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · rw [abs_of_pos (by linarith)]; exact him
  · rw [abs_of_pos (by linarith)]; linarith

theorem ceiling_le_mul_log {α β A K t : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hK : 0 ≤ Real.log K)
    (hA : A ≤ Real.log K + 4 * Real.log t) (ht : 1 ≤ Real.log t) :
    α * A + β ≤ (α * Real.log K + 4 * α + β) * Real.log t := by
  have h1 := mul_le_mul_of_nonneg_left hA hα
  have h2 : β ≤ β * Real.log t := le_mul_of_one_le_right hβ ht
  have h3 : α * Real.log K ≤ α * Real.log K * Real.log t :=
    le_mul_of_one_le_right (mul_nonneg hα hK) ht
  have h4 : (α * Real.log K + 4 * α + β) * Real.log t =
      α * Real.log K * Real.log t + α * (4 * Real.log t) + β * Real.log t := by ring
  rw [h4]
  linarith

/-- **Logarithmic size of the continued `L(Λ_Q)` below the integer exponent.**  If the `Q`-free
integers have error `O(x^θ)` and the deleted Chebyshev function has error `O(x^η)` about finitely
many exponents of bounded height, then for every `σ > max θ η` the continued `L(Λ_Q)` is `O(log t)` on
`Re s = σ`.  The integer count bounds `(s-1)L(1_S)`, zeta bounds `(s-1)ζ(s)`, and the ceiling
for zero-free quotients (Poisson, Jensen, Borel--Carathéodory, Cauchy) bounds the logarithmic
derivative of their quotient `L(1_S)/ζ`. -/
theorem exists_norm_pertLogDeriv_le_log (ha : ∀ n, |a n| ≤ 1) (ha1 : a 1 = 1)
    (he : ∀ n, |e n| ≤ Real.log n)
    (hconv : LSeries.convolution (fun n => ((Λ n - e n : ℝ) : ℂ)) (countSeq a) =
      LSeries.logMul (countSeq a))
    {A θ η σ B : ℝ} {J : Finset ℂ} {c : ℂ → ℂ}
    (hθ : 0 ≤ θ) (hN : (fun x : ℝ => count a x - A * x) =O[atTop] fun x => x ^ θ)
    (hψ : (fun x : ℝ => (pertChebyshev e x : ℂ) - ∑ ρ ∈ J, c ρ * (x : ℂ) ^ ρ) =O[atTop]
      fun x : ℝ => x ^ η)
    (hJ : ∀ ρ ∈ J, ρ.re < 2 ∧ |ρ.im| ≤ B) (hσθ : θ < σ) (hση : η < σ) (hσ1 : σ ≤ 1) :
    ∃ C t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
      ‖pertLogDeriv e J c ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * Real.log t := by
  have hmσ : max θ η < σ := max_lt hσθ hση
  obtain ⟨δ, hδ0, hδdef⟩ : ∃ δ : ℝ, 0 < δ ∧ δ = (σ - max θ η) / 3 := ⟨_, by linarith, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = 3 - σ := ⟨_, rfl⟩
  have hd2 : 2 ≤ d := by rw [hd]; linarith
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : ℝ, σ₀ = max θ η + δ := ⟨_, rfl⟩
  have hσ₀θ : θ + δ ≤ σ₀ := by rw [hσ₀]; linarith [le_max_left θ η]
  have hσ₀0 : 0 < σ₀ := by linarith
  have hre : 3 - (d + 2 * δ) = σ₀ := by rw [hd, hσ₀, hδdef]; ring
  have hR4 : d + 2 * δ ≤ 4 := by rw [hd, hδdef]; linarith [le_max_left θ η]
  obtain ⟨CN, hCN0, hCN⟩ := exists_forall_norm_sum_countDefectSeq_le ha hθ hN
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = max (Real.exp 6) ((|A| + 1) * (2 + 2 / σ₀) + CN / δ) :=
    ⟨_, rfl⟩
  have hK₀pos : 0 < K₀ := by rw [hK₀]; exact lt_of_lt_of_le (Real.exp_pos 6) (le_max_left _ _)
  have hlogK₀ : 6 ≤ Real.log K₀ := by
    rw [Real.le_log_iff_exp_le hK₀pos, hK₀]; exact le_max_left _ _
  obtain ⟨α, hα⟩ : ∃ α : ℝ,
      α = 2 / δ * ((2 * (3 * (2 * d + 3 * δ) / δ) * (2 * d + δ) + (4 * d + 3 * δ)) / δ) :=
    ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = 2 / δ * (2 * (2 * d + δ) / δ) := ⟨_, rfl⟩
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  refine ⟨α * Real.log K₀ + 4 * α + β, max (d + 3 * δ + 3 + |B|) 11, fun t ht => ?_⟩
  have ht11 : 11 ≤ t := le_trans (le_max_right _ _) ht
  have htB : d + 3 * δ + 3 + |B| ≤ t := le_trans (le_max_left _ _) ht
  have htr : d + 3 * δ + 3 ≤ t := by linarith [abs_nonneg B]
  set w₀ : ℂ := (3 : ℂ) + (t : ℂ) * I with hw₀
  have hw₀re : w₀.re = 3 := by simp [hw₀]
  have hball : ∀ z ∈ ball w₀ (d + 3 * δ), θ < z.re ∧ η < z.re ∧ ∀ ρ ∈ J, z ≠ ρ := by
    intro z hz
    have hz' : z ∈ closedBall w₀ (d + 3 * δ) := ball_subset_closedBall hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 := Complex.abs_re_le_norm (z - w₀)
    have h2 := Complex.abs_im_le_norm (z - w₀)
    rw [Complex.sub_re, hw₀re] at h1
    have hw₀im : w₀.im = t := by simp [hw₀]
    rw [Complex.sub_im, hw₀im] at h2
    have h1' := neg_abs_le (z.re - 3)
    have h2' := neg_abs_le (z.im - t)
    have hm : max θ η < z.re := by
      have : 3 - (d + 3 * δ) = max θ η := by rw [hd, hδdef]; ring
      linarith
    refine ⟨lt_of_le_of_lt (le_max_left θ η) hm, lt_of_le_of_lt (le_max_right θ η) hm,
      fun ρ hρ hzρ => ?_⟩
    have hB := (hJ ρ hρ).2
    rw [← hzρ] at hB
    have := le_abs_self z.im
    linarith [le_abs_self B]
  obtain ⟨g, hg, hexp, hg0⟩ := exists_log_ratio_on_ball ha ha1 he hconv hθ hN hψ
    (fun ρ hρ => (hJ ρ hρ).1) (show 3 ≤ w₀.re by rw [hw₀re]) (by linarith) hball
  have hsub : closedBall w₀ (d + 2 * δ) ⊆ ball w₀ (d + 3 * δ) :=
    closedBall_subset_ball (by linarith)
  have hgana : AnalyticOnNhd ℂ g (closedBall w₀ (d + 2 * δ)) := by
    have hdiff : DifferentiableOn ℂ g (ball w₀ (d + 3 * δ)) :=
      fun z hz => (hg z hz).differentiableAt.differentiableWithinAt
    exact (hdiff.analyticOnNhd isOpen_ball).mono hsub
  have hNana : AnalyticOnNhd ℂ (numerator a A) (closedBall w₀ (d + 2 * δ)) := by
    have hdiff : DifferentiableOn ℂ (numerator a A) (ball w₀ (d + 3 * δ)) := fun z hz =>
      (differentiableAt_numerator hθ hN (hball z hz).1).differentiableWithinAt
    exact (hdiff.analyticOnNhd isOpen_ball).mono hsub
  have hZana : AnalyticOnNhd ℂ zetaResidueFactor (closedBall w₀ (d + 2 * δ)) :=
    (differentiable_zetaResidueFactor.differentiableOn.analyticOnNhd isOpen_univ).mono
      (subset_univ _)
  -- boundary bounds with `A = log K₀ + 2 log (t + 11)`
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = Real.log K₀ + 2 * Real.log (t + 11) := ⟨_, rfl⟩
  have hexpM : Real.exp M = K₀ * (t + 11) ^ 2 := by
    rw [hM, Real.exp_add, Real.exp_log hK₀pos, show (2 : ℝ) * Real.log (t + 11) =
      Real.log ((t + 11) ^ 2) by rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]
  have hlogt : 0 ≤ Real.log (t + 11) := Real.log_nonneg (by linarith)
  have hM0 : 0 ≤ M := by rw [hM]; linarith
  have hreg : ∀ w ∈ sphere w₀ (d + 2 * δ),
      σ₀ ≤ w.re ∧ w.re ≤ 7 ∧ 2 ≤ |w.im| ∧ |w.im| ≤ t + 4 := fun w hw =>
    region_of_mem_closedBall hre hR4 (by linarith) (sphere_subset_closedBall hw)
  have hsq : 0 ≤ (t + 11) ^ 2 := sq_nonneg _
  have hNA : ∀ w ∈ sphere w₀ (d + 2 * δ), ‖numerator a A w‖ ≤ Real.exp M := by
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hreg w hw
    rw [hexpM]
    refine (norm_numerator_le_region hδ0 hσ₀0 hσ₀θ hCN0 hCN h1 h2 h3 h4).trans ?_
    exact mul_le_mul_of_nonneg_right (by rw [hK₀]; exact le_max_right _ _) hsq
  have hZA : ∀ w ∈ sphere w₀ (d + 2 * δ), ‖zetaResidueFactor w‖ ≤ Real.exp M := by
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hreg w hw
    rw [hexpM]
    refine (norm_zetaResidueFactor_le_region hσ₀0 h1 h2 h3 h4).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hsq
    rw [hK₀]
    refine le_trans ?_ (le_max_right _ _)
    have : 0 ≤ CN / δ := by positivity
    have : 0 ≤ 2 + 2 / σ₀ := by positivity
    nlinarith [abs_nonneg A]
  -- the centre
  have hZc := one_le_norm_zetaResidueFactor hw₀re
  have hZc0 : zetaResidueFactor w₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hZc; linarith
  have hZlow : -M ≤ Real.log ‖zetaResidueFactor w₀‖ := by
    have := Real.log_nonneg hZc; linarith
  have hgc : ‖g w₀‖ ≤ M := by
    rw [hg0]
    refine (norm_log_ratio_le ha ha1 hw₀re).trans ?_
    rw [hM]; linarith [Real.pi_lt_four]
  -- apply the ceiling at `σ + it`
  have hzw : ‖((σ : ℂ) + (t : ℂ) * I) - w₀‖ ≤ d := by
    have : ((σ : ℂ) + (t : ℂ) * I) - w₀ = ((σ - 3 : ℝ) : ℂ) := by rw [hw₀]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith), hd]
    linarith
  have hceil := GaloisForLFunctions.HTGeometry.norm_deriv_le_of_exp_mul_eq (by linarith) hδ0
    hgana hNana hZana (fun w hw => hexp w (hsub hw)) hZc0 hNA hZA hM0 hZlow hgc hzw
  have hzball : ((σ : ℂ) + (t : ℂ) * I) ∈ ball w₀ (d + 3 * δ) := by
    rw [mem_ball, dist_eq_norm]; linarith
  rw [← (hg _ hzball).deriv]
  refine hceil.trans ?_
  have hceq : 2 / δ * ((2 * (3 * M * (2 * d + 3 * δ) / δ + 1) * (2 * d + δ) +
      M * (4 * d + 3 * δ)) / δ) = α * M + β := by
    rw [hα, hβ]; field_simp; ring
  rw [hceq]
  have hlt : Real.log (t + 11) ≤ 2 * Real.log t := by
    rw [← Real.log_rpow (by linarith)]
    apply Real.log_le_log (by linarith)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith
  have hlog1 : 1 ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  exact ceiling_le_mul_log hα0 hβ0 (by linarith) (by rw [hM]; linarith) hlog1

end IntegerBeurling
