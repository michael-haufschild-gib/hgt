import GaloisForLFunctions.RHTower.Suzuki.SuzukiXiSecondDefectJet
import GaloisForLFunctions.RHTower.XiEndpointSchwarzPairHeightGap
import GaloisForLFunctions.RHTower.DigammaLeLog
import GaloisForLFunctions.RHTower.XiLogDerivFactorization
import GaloisForLFunctions.HTGeometry.DigammaMittagLeffler
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The GHS inequality for Riemann's `Ξ`

Riemann's kernel `Φ(u)du` is a positive measure with Laplace transform `ξ(½ + w)/ξ(½)`. Tilting it
by the field `e^{wu}` gives a probability measure with mean ("magnetization")
`m(w) = (ξ'/ξ)(½ + w)` (`xiRealLogDeriv`). Its variance is `m'(w)` and its third cumulant is
`m''(w)`.

**Theorem** (`concaveOn_xiRealLogDeriv`). `m` is concave on `[0, ∞)`, unconditionally. In
statistical-mechanics language, the Riemann measure satisfies the Griffiths–Hurst–Sherman
inequality, a necessary condition for it to be a Griffiths–Simon limit of ferromagnetic block
spins. The corpus had the sign of `m''` at the single point `w = 1` (Suzuki's safe tilt).

**Proof.**
* *Near the centre* (`deriv2_xiRealLogDeriv_neg`, `0 < w ≤ √120`). The zero side gives
  `m''(w) = 2w(−3 Re M₁ + 4w² Re M₂)` with `M_n = Σ_ρ (w² + ρ_c²)^{−(n+1)}`. Every atom satisfies
  `4y Re s³ < 3 Re s²` (`four_mul_re_xiShiftedReciprocalSquare_cube_lt`). The proof uses the
  first-zero height gap `γ² > 9769/231` and the strip bound `|β| < ½`.
* *Beyond `17/2`* (`concaveOn_xiRealLogDeriv_Ici`). For real `s = ½ + w > 1`,
  `m = 1/s + 1/(s−1) − log π/2 + ½ψ(s/2) + ζ'/ζ(s)`. After the shift
  `ψ(s/2) = ψ(s/2 + 8) − Σ_{k<8} 1/(s/2 + k)`, the only convex term `1/(s−1)` is dominated by
  `Σ_{k=1}^{7} 1/(s + 2k)` (`concaveOn_ghsFinitePart`, `s ≥ 9`). The digamma function is concave
  (`concaveOn_re_digamma`, Mittag-Leffler series), and `ζ'/ζ = −Σ Λ(n) n^{−s}` is concave
  (`concaveOn_re_logDeriv_riemannZeta`).
* *Gluing.* Antitone derivatives on `[0, 9]` and `[9, ∞)`.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section


theorem fortyTwo_lt_re_xiSquaredNode (q : XiZeroCopy) : 42 < (xiSquaredNode q).re := by
  rw [xiSquaredNode_re]
  have hv := xiDivisorSupport_nineThousandSevenHundredSixtyNine_div_twoHundredThirtyOne_lt_im_sq q.1
  have hu := xi_divisor_support_centered_re_sq_lt_quarter q.1
  linarith

theorem im_sq_xiSquaredNode_lt (q : XiZeroCopy) :
    (xiSquaredNode q).im ^ 2 < (xiSquaredNode q).re + 1 / 4 := by
  rw [xiSquaredNode_im, xiSquaredNode_re]
  have hu := xi_divisor_support_centered_re_sq_lt_quarter q.1
  set β := (q.1 : ℂ).re - 1 / 2
  set γ := (q.1 : ℂ).im
  have h1 : 0 ≤ γ ^ 2 * (1 - 4 * β ^ 2) := mul_nonneg (sq_nonneg γ) (by linarith)
  nlinarith

/-- **Atomwise tilted skewness bound.** For `0 < y ≤ 120`, `4y Re s³ < 3 Re s²` for every shifted
reciprocal atom `s = (y + ρ_c²)⁻¹`. -/
theorem four_mul_re_xiShiftedReciprocalSquare_cube_lt
    (q : XiZeroCopy) {y : ℝ} (hy : 0 < y) (hy' : y ≤ 120) :
    4 * y * (xiShiftedReciprocalSquare y q ^ 3).re <
      3 * (xiShiftedReciprocalSquare y q ^ 2).re := by
  set A : ℝ := y + (xiSquaredNode q).re with hAdef
  set B : ℝ := (xiSquaredNode q).im with hBdef
  have hnode := fortyTwo_lt_re_xiSquaredNode q
  have hB2 := im_sq_xiSquaredNode_lt q
  have hA : y + 42 < A := by rw [hAdef]; linarith
  have hA0 : 0 < A := by linarith
  have hBA : B ^ 2 < A + 1 / 4 := by rw [hBdef, hAdef]; linarith
  have hden : 0 < A ^ 2 + B ^ 2 := by nlinarith [sq_pos_of_pos hA0, sq_nonneg B]
  have hcoord : ((y : ℝ) : ℂ) + xiSquaredNode q = (A : ℂ) + (B : ℂ) * I := by
    apply Complex.ext <;> simp [A, B]
  rw [xiShiftedReciprocalSquare_eq_inv hy.le, hcoord]
  have hnormSq : Complex.normSq ((A : ℂ) + (B : ℂ) * I) = A ^ 2 + B ^ 2 := by
    norm_num [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im]
    ring
  have hsqRe (z : ℂ) : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    rw [pow_two, Complex.mul_re]; ring
  have hcubeRe (z : ℂ) : (z ^ 3).re = z.re ^ 3 - 3 * z.re * z.im ^ 2 := by
    rw [show z ^ 3 = z * z * z by ring, Complex.mul_re, Complex.mul_re, Complex.mul_im]; ring
  have hre2 : (((A : ℂ) + (B : ℂ) * I)⁻¹ ^ 2).re = (A ^ 2 - B ^ 2) / (A ^ 2 + B ^ 2) ^ 2 := by
    rw [hsqRe, Complex.inv_re, Complex.inv_im, hnormSq]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_zero, mul_one, add_zero, zero_add]
    field_simp [hden.ne']
  have hre3 : (((A : ℂ) + (B : ℂ) * I)⁻¹ ^ 3).re =
      A * (A ^ 2 - 3 * B ^ 2) / (A ^ 2 + B ^ 2) ^ 3 := by
    rw [hcubeRe, Complex.inv_re, Complex.inv_im, hnormSq]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_zero, mul_one, add_zero, zero_add]
    field_simp [hden.ne']
  rw [hre3, hre2]
  -- the core polynomial inequality
  have h3A : 6 ≤ 3 * A - 4 * y := by linarith
  have hB4 : B ^ 2 * B ^ 2 < (A + 1 / 4) * (A + 1 / 4) := by
    have := sq_nonneg B
    nlinarith
  have hcube : 6 * A ^ 3 ≤ A ^ 3 * (3 * A - 4 * y) := by
    have : 0 ≤ A ^ 3 := by positivity
    nlinarith
  have hbig : 3 * ((A + 1 / 4) * (A + 1 / 4)) < 6 * A ^ 3 := by nlinarith
  have hcore : 4 * y * (A * (A ^ 2 - 3 * B ^ 2)) <
      3 * ((A ^ 2 - B ^ 2) * (A ^ 2 + B ^ 2)) := by
    have hyAB : 0 ≤ 12 * y * A * B ^ 2 := by positivity
    nlinarith
  rw [show (A ^ 2 + B ^ 2) ^ 3 = (A ^ 2 + B ^ 2) ^ 2 * (A ^ 2 + B ^ 2) by ring]
  rw [show 4 * y * (A * (A ^ 2 - 3 * B ^ 2) / ((A ^ 2 + B ^ 2) ^ 2 * (A ^ 2 + B ^ 2))) =
      (4 * y * (A * (A ^ 2 - 3 * B ^ 2)) / (A ^ 2 + B ^ 2)) / (A ^ 2 + B ^ 2) ^ 2 by
    field_simp]
  rw [mul_div_assoc']
  apply div_lt_div_of_pos_right _ (by positivity)
  rw [div_lt_iff₀ hden]
  linarith

/-- **Summed tilted skewness bound.** `4y Re M₂(y) < 3 Re M₁(y)` for `0 < y ≤ 120`. -/
theorem four_mul_re_xiShiftedReciprocalMoment_two_lt {y : ℝ} (hy : 0 < y) (hy' : y ≤ 120) :
    4 * y * (xiShiftedReciprocalMoment y 2).re < 3 * (xiShiftedReciprocalMoment y 1).re := by
  have hsum2C : Summable (fun q : XiZeroCopy => xiShiftedReciprocalSquare y q ^ (1 + 1)) :=
    summable_xiShiftedReciprocalSquare_pow hy.le 1
  have hsum3C : Summable (fun q : XiZeroCopy => xiShiftedReciprocalSquare y q ^ (2 + 1)) :=
    summable_xiShiftedReciprocalSquare_pow hy.le 2
  have hsum2 : Summable (fun q : XiZeroCopy => 3 * (xiShiftedReciprocalSquare y q ^ 2).re) := by
    simpa using (Complex.reCLM.summable hsum2C).mul_left 3
  have hsum3 : Summable (fun q : XiZeroCopy =>
      4 * y * (xiShiftedReciprocalSquare y q ^ 3).re) := by
    simpa using (Complex.reCLM.summable hsum3C).mul_left (4 * y)
  obtain ⟨q0⟩ := nonempty_xiZeroCopy
  have hlt := hsum3.tsum_lt_tsum (i := q0)
    (fun q => (four_mul_re_xiShiftedReciprocalSquare_cube_lt q hy hy').le)
    (four_mul_re_xiShiftedReciprocalSquare_cube_lt q0 hy hy') hsum2
  change 4 * y * (∑' q : XiZeroCopy, xiShiftedReciprocalSquare y q ^ (2 + 1)).re <
    3 * (∑' q : XiZeroCopy, xiShiftedReciprocalSquare y q ^ (1 + 1)).re
  rw [Complex.re_tsum hsum3C, Complex.re_tsum hsum2C]
  simpa only [tsum_mul_left] using hlt

/-- The derivative of the real Xi logarithmic derivative is differentiable at every positive point. -/
theorem hasDerivAt_deriv_xiRealLogDeriv {w : ℝ} (hw : 0 < w) :
    HasDerivAt (deriv xiRealLogDeriv)
      (-6 * w * (xiShiftedReciprocalMoment (w ^ 2) 1).re +
        8 * w ^ 3 * (xiShiftedReciprocalMoment (w ^ 2) 2).re) w := by
  have hy : 0 < w ^ 2 := sq_pos_of_pos hw
  have hpow : HasDerivAt (fun v : ℝ => v ^ 2) (2 * w) w := by
    simpa using hasDerivAt_pow 2 w
  have hM0 := HasDerivAt.comp (h := fun v : ℝ => v ^ 2) w
    (hasDerivAt_re_xiShiftedReciprocalMoment (y := w ^ 2) hy 0) hpow
  have hM1 := HasDerivAt.comp (h := fun v : ℝ => v ^ 2) w
    (hasDerivAt_re_xiShiftedReciprocalMoment (y := w ^ 2) hy 1) hpow
  have hterm := ((hpow.mul hM1).const_mul (2 : ℝ))
  have hformula := hM0.sub hterm
  have heq : deriv xiRealLogDeriv =ᶠ[nhds w]
      fun v : ℝ => (xiShiftedReciprocalMoment (v ^ 2) 0).re -
        2 * (v ^ 2 * (xiShiftedReciprocalMoment (v ^ 2) 1).re) := by
    filter_upwards [Ioi_mem_nhds hw] with v hv
    rw [deriv_xiRealLogDeriv_eq hv]
    ring
  have hformula' : HasDerivAt (fun v : ℝ => (xiShiftedReciprocalMoment (v ^ 2) 0).re -
      2 * (v ^ 2 * (xiShiftedReciprocalMoment (v ^ 2) 1).re)) _ w := hformula
  refine (hformula'.congr_of_eventuallyEq heq).congr_deriv ?_
  simp only [Function.comp_apply]
  norm_num
  ring

/-- The second derivative of the real Xi logarithmic derivative at every positive point. -/
theorem deriv2_xiRealLogDeriv_eq {w : ℝ} (hw : 0 < w) :
    deriv (deriv xiRealLogDeriv) w =
      -6 * w * (xiShiftedReciprocalMoment (w ^ 2) 1).re +
        8 * w ^ 3 * (xiShiftedReciprocalMoment (w ^ 2) 2).re :=
  (hasDerivAt_deriv_xiRealLogDeriv hw).deriv

/-- **The GHS inequality for Riemann's Xi near the centre.** The magnetization
`m(w) = (ξ'/ξ)(½ + w)` is strictly concave on `(0, √120]`: `m''(w) < 0`. -/
theorem deriv2_xiRealLogDeriv_neg {w : ℝ} (hw : 0 < w) (hw' : w ^ 2 ≤ 120) :
    deriv (deriv xiRealLogDeriv) w < 0 := by
  rw [deriv2_xiRealLogDeriv_eq hw]
  have h := four_mul_re_xiShiftedReciprocalMoment_two_lt (sq_pos_of_pos hw) hw'
  have : 0 < 2 * w := by linarith
  nlinarith



/-- A pointwise summable series of concave functions is concave. -/
theorem concaveOn_tsum {S : Set ℝ} (hS : Convex ℝ S) (f : ℕ → ℝ → ℝ)
    (hf : ∀ k, ConcaveOn ℝ S (f k)) (hsum : ∀ x ∈ S, Summable fun k => f k x) :
    ConcaveOn ℝ S (fun x => ∑' k, f k x) := by
  refine ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rw [← tsum_mul_left, ← tsum_mul_left, ← (hsum x hx).mul_left a |>.tsum_add ((hsum y hy).mul_left b)]
  refine ((hsum x hx).mul_left a |>.add ((hsum y hy).mul_left b)).tsum_le_tsum (fun k => ?_)
    (hsum _ (hS hx hy ha hb hab))
  have := (hf k).2 hx hy ha hb hab
  simpa only [smul_eq_mul] using this

/-- `x ↦ −1/(x + c)` is concave on `x > −c`. -/
theorem concaveOn_neg_inv_add (c : ℝ) :
    ConcaveOn ℝ (Ioi (-c)) (fun x : ℝ => -(1 / (x + c))) := by
  have h := ((convexOn_zpow (𝕜 := ℝ) (-1)).translate_right c).neg
  have hpre : (fun z : ℝ => c + z) ⁻¹' Ioi 0 = Ioi (-c) := by
    ext z; simp only [mem_preimage, mem_Ioi]; constructor <;> intro h <;> linarith
  rw [hpre] at h
  refine h.congr fun x _ => ?_
  simp only [Pi.neg_apply, Function.comp_apply, zpow_neg_one, one_div, add_comm c x]

/-- **The digamma function is concave on the positive reals.** -/
theorem concaveOn_re_digamma :
    ConcaveOn ℝ (Ioi 0) (fun y : ℝ => (Complex.digamma (y : ℂ)).re) := by
  have hterm : ∀ (y : ℝ), 0 < y → ∀ k : ℕ,
      (1 / ((k : ℂ) + 1) - 1 / ((y : ℂ) + k)).re = 1 / ((k : ℝ) + 1) - 1 / (y + k) := by
    intro y hy k
    have h1 : (1 / ((k : ℂ) + 1)) = ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
    have h2 : (1 / ((y : ℂ) + k)) = ((1 / (y + (k : ℝ)) : ℝ) : ℂ) := by push_cast; ring
    rw [h1, h2, ← Complex.ofReal_sub, Complex.ofReal_re]
  have hsumC : ∀ y : ℝ, 0 < y → Summable fun k : ℕ => (1 / ((k : ℂ) + 1) - 1 / ((y : ℂ) + k)) :=
    fun y hy => (RHTower.hasSum_digammaSeries
      (s := (y : ℂ)) (by simpa using hy)).summable
  have heq : ∀ y ∈ Ioi (0 : ℝ), (Complex.digamma (y : ℂ)).re =
      -Real.eulerMascheroniConstant + ∑' k : ℕ, (1 / ((k : ℝ) + 1) - 1 / (y + k)) := by
    intro y hy
    rw [RHTower.digamma_eq_tsum (s := (y : ℂ)) (by simpa using hy),
      Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.re_tsum (hsumC y hy)]
    congr 1
    exact tsum_congr fun k => hterm y hy k
  have hconc : ConcaveOn ℝ (Ioi (0 : ℝ)) (fun y : ℝ =>
      -Real.eulerMascheroniConstant + ∑' k : ℕ, (1 / ((k : ℝ) + 1) - 1 / (y + k))) := by
    refine (concaveOn_const _ (convex_Ioi 0)).add ?_
    refine concaveOn_tsum (convex_Ioi 0) _ (fun k => ?_) (fun y hy => ?_)
    · have h := (concaveOn_neg_inv_add (k : ℝ)).subset
        (fun y (hy : 0 < y) => show -(k : ℝ) < y by
          have := Nat.cast_nonneg (α := ℝ) k; linarith) (convex_Ioi 0)
      refine ((concaveOn_const (1 / ((k : ℝ) + 1)) (convex_Ioi 0)).add h).congr fun y _ => ?_
      simp only [Pi.add_apply]; ring
    · have := (Complex.reCLM.summable (hsumC y hy))
      refine this.congr fun k => ?_
      exact hterm y hy k
  exact hconc.congr fun y hy => (heq y hy).symm

/-- The real von Mangoldt Dirichlet term `Λ(n) n^{−x}` (zero at `n = 0`). -/
def vonMangoldtTermR (n : ℕ) (x : ℝ) : ℝ :=
  if n = 0 then 0 else (ArithmeticFunction.vonMangoldt n : ℝ) * Real.exp (-(x * Real.log n))

theorem re_term_vonMangoldt (n : ℕ) (x : ℝ) :
    (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x : ℂ) n).re =
      vonMangoldtTermR n x := by
  rw [LSeries.term_def, vonMangoldtTermR]
  split_ifs with hn
  · simp
  · have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hc : ((n : ℂ) ^ (x : ℂ)) = (((n : ℝ) ^ x : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hpos.le]; push_cast; ring_nf
    rw [hc, ← Complex.ofReal_div, Complex.ofReal_re, Real.rpow_def_of_pos hpos, div_eq_mul_inv,
      ← Real.exp_neg]
    ring_nf

theorem convexOn_vonMangoldtTermR (n : ℕ) : ConvexOn ℝ univ (vonMangoldtTermR n) := by
  by_cases hn : n = 0
  · have h0 : vonMangoldtTermR n = fun _ => 0 := by funext x; simp [vonMangoldtTermR, hn]
    rw [h0]
    exact convexOn_const 0 convex_univ
  · have h1 : vonMangoldtTermR n = fun x =>
        (ArithmeticFunction.vonMangoldt n : ℝ) * Real.exp (-(x * Real.log n)) := by
      funext x; simp [vonMangoldtTermR, hn]
    rw [h1]
    have hlin : ConvexOn ℝ univ (fun x : ℝ => Real.exp (-(x * Real.log n))) := by
      have := convexOn_exp.comp_linearMap ((-(Real.log n)) • LinearMap.id (R := ℝ) (M := ℝ))
      refine (this.subset (subset_univ _) convex_univ).congr fun x _ => ?_
      simp only [Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
      ring_nf
    exact hlin.smul ArithmeticFunction.vonMangoldt_nonneg

/-- **`ζ'/ζ` is concave on `(1, ∞)`.** -/
theorem concaveOn_re_logDeriv_riemannZeta :
    ConcaveOn ℝ (Ioi 1) (fun x : ℝ => (logDeriv riemannZeta (x : ℂ)).re) := by
  have heq : ∀ x ∈ Ioi (1 : ℝ), (logDeriv riemannZeta (x : ℂ)).re =
      ∑' n : ℕ, -vonMangoldtTermR n x := by
    intro x hx
    have hx' : 1 < (x : ℂ).re := by simpa using hx
    rw [logDeriv_apply, show deriv riemannZeta (x : ℂ) / riemannZeta (x : ℂ) =
      -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x : ℂ) by
        rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hx']; ring,
      Complex.neg_re, LSeries, Complex.re_tsum (ArithmeticFunction.LSeriesSummable_vonMangoldt hx'),
      tsum_neg]
    exact congrArg Neg.neg (tsum_congr fun n => re_term_vonMangoldt n x)
  have hconc : ConcaveOn ℝ (Ioi (1 : ℝ)) (fun x : ℝ => ∑' n : ℕ, -vonMangoldtTermR n x) := by
    refine concaveOn_tsum (convex_Ioi 1) _ (fun n => ?_) (fun x hx => ?_)
    · exact ((convexOn_vonMangoldtTermR n).neg).subset (subset_univ _) (convex_Ioi 1)
    · have hx' : 1 < (x : ℂ).re := by simpa using hx
      have := (Complex.reCLM.summable (ArithmeticFunction.LSeriesSummable_vonMangoldt hx')).neg
      exact this.congr fun n => by simp [re_term_vonMangoldt]
  exact hconc.congr fun x hx => (heq x hx).symm

theorem hasDerivAt_inv_add {c x : ℝ} (h : x + c ≠ 0) :
    HasDerivAt (fun y : ℝ => (y + c)⁻¹) (-((x + c) ^ 2)⁻¹) x := by
  have := ((hasDerivAt_id x).add_const c).inv h
  refine this.congr_deriv ?_
  simp only [id]
  ring

theorem hasDerivAt_neg_inv_sq_add {c x : ℝ} (h : x + c ≠ 0) :
    HasDerivAt (fun y : ℝ => -((y + c) ^ 2)⁻¹) (2 * ((x + c) ^ 3)⁻¹) x := by
  have h2 : (x + c) ^ 2 ≠ 0 := pow_ne_zero 2 h
  have := ((((hasDerivAt_id x).add_const c).pow 2).inv h2).neg
  refine this.congr_deriv ?_
  simp only [id, Nat.cast_ofNat, Pi.pow_apply]
  field_simp
  ring

/-- The leftover finite part `1/(x−1) − Σ_{k=1}^{7} 1/(x+2k)`. -/
def ghsFinitePart (x : ℝ) : ℝ :=
  (x + -1)⁻¹ - ∑ k ∈ Finset.Icc (1 : ℕ) 7, (x + 2 * (k : ℝ))⁻¹

theorem ghsFinitePart_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt ghsFinitePart
      (-((x + -1) ^ 2)⁻¹ - ∑ k ∈ Finset.Icc (1 : ℕ) 7, -((x + 2 * (k : ℝ)) ^ 2)⁻¹) x := by
  have h0 : x + -1 ≠ 0 := by linarith
  have hk : ∀ k ∈ Finset.Icc (1 : ℕ) 7, x + 2 * (k : ℝ) ≠ 0 := fun k _ => by
    have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hs := HasDerivAt.fun_sum (u := Finset.Icc (1 : ℕ) 7)
    (A := fun k (y : ℝ) => (y + 2 * (k : ℝ))⁻¹)
    (A' := fun k => -((x + 2 * (k : ℝ)) ^ 2)⁻¹) fun k hkmem => hasDerivAt_inv_add (hk k hkmem)
  exact (hasDerivAt_inv_add h0).sub hs

theorem ghsFinitePart_deriv2 {x : ℝ} (hx : 1 < x) :
    deriv (deriv ghsFinitePart) x =
      2 * ((x + -1) ^ 3)⁻¹ - ∑ k ∈ Finset.Icc (1 : ℕ) 7, 2 * ((x + 2 * (k : ℝ)) ^ 3)⁻¹ := by
  have heq : deriv ghsFinitePart =ᶠ[𝓝 x] fun y =>
      -((y + -1) ^ 2)⁻¹ - ∑ k ∈ Finset.Icc (1 : ℕ) 7, -((y + 2 * (k : ℝ)) ^ 2)⁻¹ := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (ghsFinitePart_hasDerivAt hy).deriv
  rw [heq.deriv_eq]
  have h0 : x + -1 ≠ 0 := by linarith
  have hk : ∀ k ∈ Finset.Icc (1 : ℕ) 7, x + 2 * (k : ℝ) ≠ 0 := fun k _ => by
    have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hs := HasDerivAt.fun_sum (u := Finset.Icc (1 : ℕ) 7)
    (A := fun k (y : ℝ) => -((y + 2 * (k : ℝ)) ^ 2)⁻¹)
    (A' := fun k => 2 * ((x + 2 * (k : ℝ)) ^ 3)⁻¹) fun k hkmem =>
      hasDerivAt_neg_inv_sq_add (hk k hkmem)
  exact ((hasDerivAt_neg_inv_sq_add h0).sub hs).deriv

theorem ghsFinitePart_deriv2_nonpos {x : ℝ} (hx : 9 ≤ x) :
    deriv (deriv ghsFinitePart) x ≤ 0 := by
  rw [ghsFinitePart_deriv2 (by linarith)]
  have hx1 : 0 < x - 1 := by linarith
  -- each term dominates a fixed fraction of the first
  have hterm : ∀ k ∈ Finset.Icc (1 : ℕ) 7,
      (8 / (9 + 2 * (k : ℝ))) ^ 3 * ((x + -1) ^ 3)⁻¹ ≤ ((x + 2 * (k : ℝ)) ^ 3)⁻¹ := by
    intro k hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hpos : 0 < x + 2 * (k : ℝ) := by linarith
    have hle : 8 * (x + 2 * (k : ℝ)) ≤ (9 + 2 * (k : ℝ)) * (x + -1) := by nlinarith
    have hratio : 8 / (9 + 2 * (k : ℝ)) ≤ (x + -1) / (x + 2 * (k : ℝ)) := by
      rw [div_le_div_iff₀ (by linarith) hpos]; linarith
    have hcube := pow_le_pow_left₀ (by positivity) hratio 3
    calc (8 / (9 + 2 * (k : ℝ))) ^ 3 * ((x + -1) ^ 3)⁻¹
        ≤ ((x + -1) / (x + 2 * (k : ℝ))) ^ 3 * ((x + -1) ^ 3)⁻¹ :=
          mul_le_mul_of_nonneg_right hcube (by positivity)
      _ = ((x + 2 * (k : ℝ)) ^ 3)⁻¹ := by
          field_simp [show (x + -1) ≠ 0 by linarith]
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul] at hsum
  have hconst : (1 : ℝ) ≤ ∑ k ∈ Finset.Icc (1 : ℕ) 7, (8 / (9 + 2 * (k : ℝ))) ^ 3 := by
    have hI : Finset.Icc (1 : ℕ) 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
    rw [hI]
    norm_num [Finset.sum_insert]
  have hinv : 0 ≤ ((x + -1) ^ 3)⁻¹ := by positivity
  have h2 : ((x + -1) ^ 3)⁻¹ ≤ ∑ k ∈ Finset.Icc (1 : ℕ) 7, ((x + 2 * (k : ℝ)) ^ 3)⁻¹ := by
    nlinarith
  rw [← Finset.mul_sum]
  linarith

/-- The finite part is concave on `[9, ∞)`. -/
theorem concaveOn_ghsFinitePart : ConcaveOn ℝ (Ici 9) ghsFinitePart := by
  have hint : interior (Ici (9 : ℝ)) = Ioi 9 := interior_Ici
  refine concaveOn_of_deriv2_nonpos (convex_Ici 9) ?_ ?_ ?_ ?_
  · intro x hx
    exact (ghsFinitePart_hasDerivAt (by simp at hx; linarith)).continuousAt.continuousWithinAt
  · rw [hint]
    intro x hx
    exact (ghsFinitePart_hasDerivAt (by simp at hx; linarith)).differentiableAt.differentiableWithinAt
  · rw [hint]
    intro x hx
    have hx1 : 1 < x := by simp at hx; linarith
    have h0 : x + -1 ≠ 0 := by linarith
    have hk : ∀ k ∈ Finset.Icc (1 : ℕ) 7, x + 2 * (k : ℝ) ≠ 0 := fun k _ => by
      have := Nat.cast_nonneg (α := ℝ) k; linarith
    have heq : deriv ghsFinitePart =ᶠ[𝓝 x] fun y =>
        -((y + -1) ^ 2)⁻¹ - ∑ k ∈ Finset.Icc (1 : ℕ) 7, -((y + 2 * (k : ℝ)) ^ 2)⁻¹ := by
      filter_upwards [Ioi_mem_nhds hx1] with y hy
      exact (ghsFinitePart_hasDerivAt hy).deriv
    have hs := HasDerivAt.fun_sum (u := Finset.Icc (1 : ℕ) 7)
      (A := fun k (y : ℝ) => -((y + 2 * (k : ℝ)) ^ 2)⁻¹)
      (A' := fun k => 2 * ((x + 2 * (k : ℝ)) ^ 3)⁻¹) fun k hkmem =>
        hasDerivAt_neg_inv_sq_add (hk k hkmem)
    exact ((((hasDerivAt_neg_inv_sq_add h0).sub hs).congr_of_eventuallyEq heq).differentiableAt
      ).differentiableWithinAt
  · rw [hint]
    intro x hx
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    exact ghsFinitePart_deriv2_nonpos (by simp at hx; linarith)

/-- The Gamma–prime form of the real Xi logarithmic derivative right of `1`. -/
def ghsGammaPrimeForm (x : ℝ) : ℝ :=
  ghsFinitePart x - Real.log Real.pi / 2 + (Complex.digamma (((x / 2 + 8 : ℝ)) : ℂ)).re / 2 +
    (logDeriv riemannZeta (x : ℂ)).re

theorem xiRealLogDeriv_eq_ghsGammaPrimeForm {w : ℝ} (hw : 1 / 2 < w) :
    xiRealLogDeriv w = ghsGammaPrimeForm (1 / 2 + w) := by
  set x : ℝ := 1 / 2 + w with hx
  have hx1 : 1 < x := by rw [hx]; linarith
  have hs : (1 / 2 + (w : ℂ)) = ((x : ℝ) : ℂ) := by rw [hx]; push_cast; ring
  have hsre : 1 < ((x : ℝ) : ℂ).re := by simpa using hx1
  rw [xiRealLogDeriv, hs, logDeriv_xi_fourFactor hsre]
  -- real parts of the four factors
  have h1 : (1 / ((x : ℝ) : ℂ)).re = 1 / x := by
    rw [show (1 / ((x : ℝ) : ℂ)) = ((1 / x : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  have h2 : (1 / (((x : ℝ) : ℂ) - 1)).re = 1 / (x - 1) := by
    rw [show (1 / (((x : ℝ) : ℂ) - 1)) = ((1 / (x - 1) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  have h3 : ((Real.log Real.pi : ℂ) / 2).re = Real.log Real.pi / 2 := by
    rw [show ((Real.log Real.pi : ℂ) / 2) = ((Real.log Real.pi / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  have hhalf : ((x : ℝ) : ℂ) / 2 = (((x / 2 : ℝ)) : ℂ) := by push_cast; ring
  have h4 : (Complex.digamma (((x : ℝ) : ℂ) / 2) / 2).re =
      (Complex.digamma (((x / 2 : ℝ)) : ℂ)).re / 2 := by
    rw [hhalf, Complex.div_re]
    simp only [Complex.normSq_ofNat, Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_div]
    ring
  rw [Complex.add_re, Complex.add_re, Complex.sub_re, Complex.add_re, h1, h2, h3, h4]
  -- shift the digamma function by eight
  have hshift := re_digamma_shift (y := x / 2) (by linarith) 8
  rw [hshift, ghsGammaPrimeForm, ghsFinitePart]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have hI : Finset.Icc (1 : ℕ) 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  rw [hI]
  norm_num [Finset.sum_insert]
  have hx0 : x ≠ 0 := by linarith
  field_simp
  ring

/-- `x ↦ g(x/2 + 8)/2` inherits concavity on `[9, ∞)` from concavity of `g` on `(0, ∞)`. -/
theorem concaveOn_half_comp_affine {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Ioi 0) g) :
    ConcaveOn ℝ (Ici 9) (fun x => g (x / 2 + 8) / 2) := by
  refine ⟨convex_Ici 9, fun x hx y hy a b ha hb hab => ?_⟩
  have hx' : x / 2 + 8 ∈ Ioi (0 : ℝ) := by simp at hx ⊢; linarith
  have hy' : y / 2 + 8 ∈ Ioi (0 : ℝ) := by simp at hy ⊢; linarith
  have h := hg.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have harg : a * (x / 2 + 8) + b * (y / 2 + 8) = (a * x + b * y) / 2 + 8 := by
    have : b = 1 - a := by linarith
    subst this; ring
  rw [harg] at h
  linarith

/-- **Concavity of the Gamma–prime form on `[9, ∞)`.** -/
theorem concaveOn_ghsGammaPrimeForm : ConcaveOn ℝ (Ici 9) ghsGammaPrimeForm := by
  have h1 := concaveOn_ghsFinitePart
  have h2 := concaveOn_const (𝕜 := ℝ) (-(Real.log Real.pi / 2)) (convex_Ici (9 : ℝ))
  have h3 := concaveOn_half_comp_affine concaveOn_re_digamma
  have h4 := concaveOn_re_logDeriv_riemannZeta.subset
    (fun x (hx : (9 : ℝ) ≤ x) => show (1 : ℝ) < x by linarith) (convex_Ici 9)
  refine (((h1.add h2).add h3).add h4).congr fun x _ => ?_
  simp only [Pi.add_apply, ghsGammaPrimeForm]
  push_cast
  ring

/-- **The magnetization is concave beyond `17/2`.** -/
theorem concaveOn_xiRealLogDeriv_Ici :
    ConcaveOn ℝ (Ici (17 / 2)) xiRealLogDeriv := by
  have hG := concaveOn_ghsGammaPrimeForm
  have hT : ConcaveOn ℝ (Ici (17 / 2)) (fun w => ghsGammaPrimeForm (1 / 2 + w)) := by
    refine ⟨convex_Ici _, fun x hx y hy a b ha hb hab => ?_⟩
    have hx' : 1 / 2 + x ∈ Ici (9 : ℝ) := by simp at hx ⊢; linarith
    have hy' : 1 / 2 + y ∈ Ici (9 : ℝ) := by simp at hy ⊢; linarith
    have h := hG.2 hx' hy' ha hb hab
    simp only [smul_eq_mul] at h ⊢
    have harg : a * (1 / 2 + x) + b * (1 / 2 + y) = 1 / 2 + (a * x + b * y) := by
      have : b = 1 - a := by linarith
      subst this; ring
    rw [harg] at h
    exact h
  refine hT.congr fun w hw => ?_
  have : 1 / 2 < w := by simp at hw; linarith
  exact (xiRealLogDeriv_eq_ghsGammaPrimeForm this).symm

/-- **The magnetization is strictly concave on `[0, 10]`.** -/
theorem concaveOn_xiRealLogDeriv_Icc : ConcaveOn ℝ (Icc 0 10) xiRealLogDeriv := by
  have hint : interior (Icc (0 : ℝ) 10) = Ioo 0 10 := interior_Icc
  refine concaveOn_of_deriv2_nonpos (convex_Icc 0 10) ?_ ?_ ?_ ?_
  · exact fun x _ => (hasDerivAt_xiRealLogDeriv x).continuousAt.continuousWithinAt
  · exact fun x _ => (hasDerivAt_xiRealLogDeriv x).differentiableAt.differentiableWithinAt
  · rw [hint]
    exact fun x hx => (hasDerivAt_deriv_xiRealLogDeriv hx.1).differentiableAt.differentiableWithinAt
  · rw [hint]
    intro x hx
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    exact (deriv2_xiRealLogDeriv_neg hx.1 (by nlinarith [hx.1, hx.2])).le

/-- **The GHS inequality for Riemann's `Ξ`.** The magnetization `m(w) = (ξ'/ξ)(½ + w)` of the
Riemann measure `Φ(u)du` under the exponential field `e^{wu}` is concave on `[0, ∞)`.
Equivalently, every rightward tilt of `Φ` has nonpositive third cumulant. No hypothesis on the
zeros is used. Near the centre the zero sum is controlled atom by atom using the first-zero height
gap. Beyond `17/2`, the Gamma–prime form `1/(s−1) + ½ψ(s/2) + ζ'/ζ(s)` is a sum of concave pieces. -/
theorem concaveOn_xiRealLogDeriv : ConcaveOn ℝ (Ici 0) xiRealLogDeriv := by
  have hdiff : ∀ x, DifferentiableAt ℝ xiRealLogDeriv x :=
    fun x => (hasDerivAt_xiRealLogDeriv x).differentiableAt
  have hA : AntitoneOn (deriv xiRealLogDeriv) (Icc 0 9) :=
    (concaveOn_xiRealLogDeriv_Icc.antitoneOn_deriv fun x _ => hdiff x).mono
      (Icc_subset_Icc le_rfl (by norm_num))
  have hB : AntitoneOn (deriv xiRealLogDeriv) (Ici 9) :=
    (concaveOn_xiRealLogDeriv_Ici.antitoneOn_deriv fun x _ => hdiff x).mono
      (Ici_subset_Ici.mpr (by norm_num))
  have hU : AntitoneOn (deriv xiRealLogDeriv) (Icc 0 9 ∪ Ici 9) :=
    hA.union_right hB ⟨⟨by norm_num, le_rfl⟩, fun x hx => hx.2⟩
      ⟨show (9 : ℝ) ∈ Ici 9 from le_refl (9 : ℝ), fun x hx => hx⟩
  have hset : Icc (0 : ℝ) 9 ∪ Ici 9 = Ici 0 := Icc_union_Ici_eq_Ici (by norm_num)
  rw [hset] at hU
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici 0)
    (fun x _ => (hdiff x).continuousAt.continuousWithinAt)
    (fun x _ => (hdiff x).differentiableWithinAt) ?_
  rw [interior_Ici]
  exact hU.mono Ioi_subset_Ici_self

end

end RHTower
