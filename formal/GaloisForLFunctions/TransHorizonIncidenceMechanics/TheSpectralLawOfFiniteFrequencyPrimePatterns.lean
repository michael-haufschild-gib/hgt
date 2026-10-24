import GaloisForLFunctions.TransHorizonIncidenceMechanics.ThePhaseLawOfOscillatingPrimePatterns

/-!
# The spectral law of finite-frequency prime patterns

Let `g(x) = c₀ + Σ_k Re(B_k e^{i t_k x})` be a real trigonometric polynomial with distinct positive
frequencies `t_k` and `|g| ≤ 1`, and let `f` be completely multiplicative with `f(p) = g(log p)`
(`spectralPattern`). The half-damped weight `f(d) d^{-1/2}` is paid if and only if

  `c₀ < 1/2`  and, for every `k`,  `Re B_k < 1`  or  `ζ(1/2 + it_k) = 0`

(`receiverBounded_spectralWeight_iff`). Each frequency is read on its own: the mean `c₀` by the
quarter law at `s = 1/2`, the amplitude `Re B_k` by a singularity `|s − (1/2 + it_k)|^{−Re B_k}` of
the pattern's Dirichlet series, which a critical zero at the same height cancels exactly. Mixing
frequencies enlarges the admissible amplitudes: with harmonics a single frequency can carry
`Re B_k > 1` while `|g| ≤ 1` (`(9/8) cos x − (1/8) cos 3x`), and the receiver still reads it through
the critical zero at its height. The exponents are capped, `Re B_k ≤ 2` and `c₀ ≤ 1`
(`spectralAmplitude_re_le_two`), since `|F(w)| ≤ ζ(Re w)`.

**Mechanism.** The Euler comparison (`abs_log_norm_spectralSeries_sub_le`) and the two-sided pole
bounds `m ≤ |ζ(v)| |v − 1| ≤ K` on boxes give the local factorization
(`exists_abs_log_norm_spectralSeries_add_le`)

  `log|F(w)| = −c₀ log|w − 1| − Σ_k (Re B_k/2)(log|w − 1 − it_k| + log|w − 1 + it_k|) + O(1)`

uniformly on `1 < Re w ≤ 2`, `|Im w| ≤ H`. Its upper half bounds the line integrand by an
integrable majorant (at most one singular height is near any point); its lower half produces the
singularity `κ/|s − s_k|` that a paid receiver forbids.
-/

open Filter Topology MeasureTheory Complex Set
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

variable {K : ℕ}

/-! ### The spectral pattern -/

/-- The finite-frequency profile `g(x) = c₀ + Σ_k Re(B_k e^{i t_k x})`. -/
def spectralProfile (c₀ : ℝ) (t : Fin K → ℝ) (B : Fin K → ℂ) (x : ℝ) : ℝ :=
  c₀ + ∑ k, (B k * Complex.exp (((t k * x : ℝ) : ℂ) * I)).re

/-- The completely multiplicative pattern with prime values `g(log p)`. -/
def spectralPattern (c₀ : ℝ) (t : Fin K → ℝ) (B : Fin K → ℂ) : ℕ →*₀ ℝ :=
  primeValueHom fun p => spectralProfile c₀ t B (Real.log p)

/-- The half-damped spectral weight `f(d) d^{-1/2}`. -/
def spectralWeight (c₀ : ℝ) (t : Fin K → ℝ) (B : Fin K → ℂ) (d : ℕ) : ℝ :=
  spectralPattern c₀ t B d * (d : ℝ) ^ (-(1 / 2 : ℝ))

/-- The Dirichlet series `F(w) = Σ f(n) n^{-w}` of the pattern. -/
def spectralSeries (c₀ : ℝ) (t : Fin K → ℝ) (B : Fin K → ℂ) (w : ℂ) : ℂ :=
  ∑' n : ℕ, (spectralPattern c₀ t B n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)

theorem spectralPattern_prime (c₀ : ℝ) (t : Fin K → ℝ) (B : Fin K → ℂ) {p : ℕ} (hp : p.Prime) :
    spectralPattern c₀ t B p = spectralProfile c₀ t B (Real.log p) :=
  primeValueHom_prime _ hp

theorem abs_spectralPattern_le {c₀ : ℝ} {t : Fin K → ℝ} {B : Fin K → ℂ}
    (hg : ∀ x, |spectralProfile c₀ t B x| ≤ 1) (n : ℕ) : |spectralPattern c₀ t B n| ≤ 1 :=
  abs_patternHom_le_one _ (fun p hp => by rw [spectralPattern_prime c₀ t B hp]; exact hg _) n

/-- `Re(B e^{iθ}) p^{-w} = (B/2) p^{-(w − it)} + (B̄/2) p^{-(w + it)}` at `θ = t log p`. -/
theorem re_mul_exp_mul_cpow_eq {p : ℕ} (hp : 0 < p) (b : ℂ) (τ : ℝ) (w : ℂ) :
    (((b * Complex.exp (((τ * Real.log p : ℝ) : ℂ) * I)).re : ℝ) : ℂ) * (p : ℂ) ^ (-w) =
      b / 2 * (p : ℂ) ^ (-(w - τ * I)) + starRingEnd ℂ b / 2 * (p : ℂ) ^ (-(w + τ * I)) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg p)]
  rw [Complex.re_eq_add_conj, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, Complex.cpow_def_of_ne_zero hp0, Complex.cpow_def_of_ne_zero hp0,
    Complex.cpow_def_of_ne_zero hp0, hlog]
  have e1 : Complex.exp (((τ * Real.log p : ℝ) : ℂ) * I) * Complex.exp (Real.log p * -w) =
      Complex.exp (Real.log p * -(w - τ * I)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have e2 : Complex.exp (((τ * Real.log p : ℝ) : ℂ) * -I) * Complex.exp (Real.log p * -w) =
      Complex.exp (Real.log p * -(w + τ * I)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [← e1, ← e2]
  ring

/-! ### The Euler comparison -/

/-- The phase datum of the Euler comparison:
`c₀ ℓ(w) + Σ_k ((B_k/2) ℓ(w − it_k) + (B̄_k/2) ℓ(w + it_k))`. -/
def spectralEulerPhase (c₀ : ℝ) (t : Fin K → ℝ) (B : Fin K → ℂ) (w : ℂ) : ℂ :=
  (c₀ : ℂ) * RHTower.zetaEulerLog w + ∑ k, (B k / 2 * RHTower.zetaEulerLog (w - t k * I) +
    starRingEnd ℂ (B k) / 2 * RHTower.zetaEulerLog (w + t k * I))

/-- **The Euler comparison.** On `Re w > 1`, `log|F(w)|` is the real part of the phase datum up to
`(1 + |c₀| + Σ_k ‖B_k‖) S`, `S = Σ_p p^{-2}`. -/
theorem abs_log_norm_spectralSeries_sub_le {c₀ : ℝ} {t : Fin K → ℝ} {B : Fin K → ℂ}
    (hg : ∀ x, |spectralProfile c₀ t B x| ≤ 1) {w : ℂ} (hw : 1 < w.re) :
    |Real.log ‖spectralSeries c₀ t B w‖ - (spectralEulerPhase c₀ t B w).re| ≤
      (1 + |c₀| + ∑ k, ‖B k‖) * primeSquareMass := by
  have hF := abs_log_norm_tsum_sub_re_le (cweightedPatternHom (spectralPattern c₀ t B) w) hw
    fun n => by
      simp only [cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_natCast]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_spectralPattern_le hg n)
  have hFn : ∑' n, cweightedPatternHom (spectralPattern c₀ t B) w n = spectralSeries c₀ t B w :=
    tsum_congr fun n => rfl
  have hs0 := summable_prime_cpow_neg hw
  have hsm : ∀ k, Summable fun p : Nat.Primes => ((p : ℕ) : ℂ) ^ (-(w - t k * I)) :=
    fun k => summable_prime_cpow_neg (by simpa using hw)
  have hsp : ∀ k, Summable fun p : Nat.Primes => ((p : ℕ) : ℂ) ^ (-(w + t k * I)) :=
    fun k => summable_prime_cpow_neg (by simpa using hw)
  set P : ℂ → ℂ := fun v => ∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-v)
  have hFp : ∑' p : Nat.Primes, cweightedPatternHom (spectralPattern c₀ t B) w p =
      (c₀ : ℂ) * P w + ∑ k, (B k / 2 * P (w - t k * I) + starRingEnd ℂ (B k) / 2 *
        P (w + t k * I)) := by
    have hterm : ∀ p : Nat.Primes, cweightedPatternHom (spectralPattern c₀ t B) w p =
        (c₀ : ℂ) * ((p : ℕ) : ℂ) ^ (-w) + ∑ k, (B k / 2 * ((p : ℕ) : ℂ) ^ (-(w - t k * I)) +
          starRingEnd ℂ (B k) / 2 * ((p : ℕ) : ℂ) ^ (-(w + t k * I))) := by
      intro p
      simp only [cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
        Complex.ofReal_natCast, spectralPattern_prime c₀ t B p.2, spectralProfile]
      push_cast
      rw [add_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      have := re_mul_exp_mul_cpow_eq p.2.pos (B k) (t k) w
      push_cast at this
      exact this
    rw [tsum_congr hterm, (hs0.mul_left _).tsum_add (summable_sum fun k _ =>
      ((hsm k).mul_left _).add ((hsp k).mul_left _)), tsum_mul_left,
      Summable.tsum_finsetSum fun k _ => ((hsm k).mul_left _).add ((hsp k).mul_left _)]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [((hsm k).mul_left _).tsum_add ((hsp k).mul_left _), tsum_mul_left, tsum_mul_left]
  rw [hFn, hFp] at hF
  have hS : ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) = primeSquareMass := rfl
  rw [hS] at hF
  have hdiff : |((c₀ : ℂ) * P w + ∑ k, (B k / 2 * P (w - t k * I) + starRingEnd ℂ (B k) / 2 *
      P (w + t k * I))).re - (spectralEulerPhase c₀ t B w).re| ≤
        (|c₀| + ∑ k, ‖B k‖) * primeSquareMass := by
    rw [← Complex.sub_re]
    refine (Complex.abs_re_le_norm _).trans ?_
    have heq : (c₀ : ℂ) * P w + ∑ k, (B k / 2 * P (w - t k * I) + starRingEnd ℂ (B k) / 2 *
        P (w + t k * I)) - spectralEulerPhase c₀ t B w =
          (c₀ : ℂ) * (P w - RHTower.zetaEulerLog w) + ∑ k, (B k / 2 *
            (P (w - t k * I) - RHTower.zetaEulerLog (w - t k * I)) + starRingEnd ℂ (B k) / 2 *
              (P (w + t k * I) - RHTower.zetaEulerLog (w + t k * I))) := by
      simp only [spectralEulerPhase, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      ring
    rw [heq]
    have hS0 : 0 ≤ primeSquareMass := tsum_nonneg fun p => by positivity
    have h0 : ‖(c₀ : ℂ) * (P w - RHTower.zetaEulerLog w)‖ ≤ |c₀| * primeSquareMass := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_tsum_prime_cpow_sub_zetaEulerLog_le hw) (abs_nonneg _)
    have hk : ∀ k, ‖B k / 2 * (P (w - t k * I) - RHTower.zetaEulerLog (w - t k * I)) +
        starRingEnd ℂ (B k) / 2 * (P (w + t k * I) - RHTower.zetaEulerLog (w + t k * I))‖ ≤
          ‖B k‖ * primeSquareMass := by
      intro k
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_div, norm_div, Complex.norm_conj, Complex.norm_two]
      have h1 := norm_tsum_prime_cpow_sub_zetaEulerLog_le (v := w - t k * I) (by simpa using hw)
      have h2 := norm_tsum_prime_cpow_sub_zetaEulerLog_le (v := w + t k * I) (by simpa using hw)
      have hb := norm_nonneg (B k)
      nlinarith [mul_le_mul_of_nonneg_left h1 hb, mul_le_mul_of_nonneg_left h2 hb]
    calc ‖(c₀ : ℂ) * (P w - RHTower.zetaEulerLog w) + ∑ k, (B k / 2 *
          (P (w - t k * I) - RHTower.zetaEulerLog (w - t k * I)) + starRingEnd ℂ (B k) / 2 *
            (P (w + t k * I) - RHTower.zetaEulerLog (w + t k * I)))‖
        ≤ |c₀| * primeSquareMass + ∑ k, ‖B k‖ * primeSquareMass :=
          (norm_add_le _ _).trans (add_le_add h0 ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun k _ => hk k)))
      _ = (|c₀| + ∑ k, ‖B k‖) * primeSquareMass := by rw [add_mul, Finset.sum_mul]
  have h3 := abs_sub_le (Real.log ‖spectralSeries c₀ t B w‖)
    ((c₀ : ℂ) * P w + ∑ k, (B k / 2 * P (w - t k * I) + starRingEnd ℂ (B k) / 2 *
      P (w + t k * I))).re (spectralEulerPhase c₀ t B w).re
  linarith

/-! ### The local factorization -/

/-- `log|ζ(v)| = −log|v − 1| + O(1)` and `Im ℓ(v) = O(1)` on a box right of the pole. -/
theorem exists_abs_log_norm_zeta_add_le (H : ℝ) :
    ∃ L C : ℝ, 0 ≤ L ∧ 0 ≤ C ∧ ∀ v : ℂ, 1 < v.re → v.re ≤ 2 → |v.im| ≤ H →
      |Real.log ‖riemannZeta v‖ + Real.log ‖v - 1‖| ≤ L ∧
        |(RHTower.zetaEulerLog v).im| ≤ C := by
  obtain ⟨m, K₀, hm, hmK⟩ := RHTower.exists_norm_zeta_mul_sub_one_bounds H
  obtain ⟨C, hC⟩ := RHTower.exists_abs_im_zetaEulerLog_le H
  refine ⟨|Real.log m| + |Real.log K₀|, |C|, by positivity, abs_nonneg _, fun v hv hv2 hvH => ?_⟩
  obtain ⟨h1, h2⟩ := hmK v hv hv2 hvH
  have hζ : 0 < ‖riemannZeta v‖ := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re hv.le)
  have hv1 : 0 < ‖v - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr fun h => by
    rw [h, Complex.one_re] at hv; exact lt_irrefl _ hv)
  have hprod : 0 < ‖riemannZeta v‖ * ‖v - 1‖ := mul_pos hζ hv1
  refine ⟨?_, ?_⟩
  · rw [← Real.log_mul hζ.ne' hv1.ne', abs_le]
    constructor
    · have := Real.log_le_log hm h1
      linarith [neg_abs_le (Real.log m), abs_nonneg (Real.log K₀)]
    · have := Real.log_le_log hprod h2
      linarith [le_abs_self (Real.log K₀), abs_nonneg (Real.log m)]
  · have hv' : v = (((1 + (v.re - 1)) : ℝ) : ℂ) + (v.im : ℂ) * I := by
      apply Complex.ext <;> simp
    have := hC (v.re - 1) v.im (by linarith) (by linarith) hvH
    rw [← hv'] at this
    exact this.trans (le_abs_self C)

/-- The logarithmic factor datum `−c₀ log|w − 1| − Σ_k (Re B_k/2)(log|w − 1 − it_k| + log|w − 1 + it_k|)`. -/
def spectralLogFactor (c₀ : ℝ) (t : Fin K → ℝ) (B : Fin K → ℂ) (w : ℂ) : ℝ :=
  -(c₀ * Real.log ‖w - 1‖) - ∑ k, (B k).re / 2 *
    (Real.log ‖w - t k * I - 1‖ + Real.log ‖w + t k * I - 1‖)

/-- **The local factorization.** For every `H` there is `C` with
`|log|F(w)| − (−c₀ log|w − 1| − Σ_k (Re B_k/2)(log|w − 1 − it_k| + log|w − 1 + it_k|))| ≤ C` on
`1 < Re w ≤ 2`, `|Im w| ≤ H`. -/
theorem exists_abs_log_norm_spectralSeries_sub_le {c₀ : ℝ} {t : Fin K → ℝ} {B : Fin K → ℂ}
    (hg : ∀ x, |spectralProfile c₀ t B x| ≤ 1) (H : ℝ) :
    ∃ C : ℝ, ∀ w : ℂ, 1 < w.re → w.re ≤ 2 → |w.im| ≤ H →
      |Real.log ‖spectralSeries c₀ t B w‖ - spectralLogFactor c₀ t B w| ≤ C := by
  set H' : ℝ := H + ∑ k, |t k|
  obtain ⟨L, C, hL, hC, hbox⟩ := exists_abs_log_norm_zeta_add_le H'
  refine ⟨(1 + |c₀| + ∑ k, ‖B k‖) * primeSquareMass + |c₀| * L + ∑ k, ‖B k‖ * (L + C),
    fun w hw hw2 hwH => ?_⟩
  have hE := abs_log_norm_spectralSeries_sub_le hg hw
  have hH' : ∀ k, |w.im| + |t k| ≤ H' := fun k => by
    have := Finset.single_le_sum (f := fun k => |t k|) (fun k _ => abs_nonneg _)
      (Finset.mem_univ k)
    simp only [H']; linarith
  have hsumt : 0 ≤ ∑ k, |t k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hbox' : ∀ v : ℂ, v.re = w.re → |v.im| ≤ H' →
      |Real.log ‖riemannZeta v‖ + Real.log ‖v - 1‖| ≤ L ∧ |(RHTower.zetaEulerLog v).im| ≤ C :=
    fun v hre him => hbox v (by rw [hre]; exact hw) (by rw [hre]; exact hw2) him
  have hw0 := hbox' w rfl (by simp only [H']; linarith)
  have hvm : ∀ k, (w - t k * I).re = w.re ∧ |(w - t k * I).im| ≤ H' := fun k => by
    refine ⟨by simp, ?_⟩
    have : (w - t k * I).im = w.im - t k := by simp
    rw [this]; exact (abs_sub _ _).trans (hH' k)
  have hvp : ∀ k, (w + t k * I).re = w.re ∧ |(w + t k * I).im| ≤ H' := fun k => by
    refine ⟨by simp, ?_⟩
    have : (w + t k * I).im = w.im + t k := by simp
    rw [this]; exact (abs_add_le _ _).trans (hH' k)
  have hgtm : ∀ k, 1 < (w - t k * I).re := fun k => by rw [(hvm k).1]; exact hw
  have hgtp : ∀ k, 1 < (w + t k * I).re := fun k => by rw [(hvp k).1]; exact hw
  have hhalf : ∀ b z : ℂ, (b / 2 * z).re = b.re / 2 * z.re - b.im / 2 * z.im := fun b z => by
    simp only [Complex.mul_re, Complex.div_ofNat_re, Complex.div_ofNat_im]
  -- the real part of the phase, term by term
  have hre : (spectralEulerPhase c₀ t B w).re = c₀ * Real.log ‖riemannZeta w‖ +
      ∑ k, ((B k).re / 2 * (Real.log ‖riemannZeta (w - t k * I)‖ +
        Real.log ‖riemannZeta (w + t k * I)‖) - (B k).im / 2 *
          ((RHTower.zetaEulerLog (w - t k * I)).im - (RHTower.zetaEulerLog (w + t k * I)).im)) := by
    simp only [spectralEulerPhase, Complex.add_re, Complex.re_sum, hhalf]
    rw [Complex.re_ofReal_mul, RHTower.re_zetaEulerLog hw]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [RHTower.re_zetaEulerLog (hgtm k), RHTower.re_zetaEulerLog (hgtp k), Complex.conj_re,
      Complex.conj_im]
    ring
  set dz : ℂ → ℝ := fun v => Real.log ‖riemannZeta v‖ + Real.log ‖v - 1‖
  set term : Fin K → ℝ := fun k => (B k).re / 2 * (dz (w - t k * I) + dz (w + t k * I)) -
    (B k).im / 2 * ((RHTower.zetaEulerLog (w - t k * I)).im - (RHTower.zetaEulerLog (w + t k * I)).im)
  have hdiff : (spectralEulerPhase c₀ t B w).re - spectralLogFactor c₀ t B w =
      c₀ * dz w + ∑ k, term k := by
    rw [hre]
    simp only [spectralLogFactor, term, dz]
    have h1 := Finset.sum_add_distrib (s := Finset.univ) (f := fun k => (B k).re / 2 *
        (Real.log ‖riemannZeta (w - t k * I)‖ + Real.log ‖riemannZeta (w + t k * I)‖) -
          (B k).im / 2 * ((RHTower.zetaEulerLog (w - t k * I)).im -
            (RHTower.zetaEulerLog (w + t k * I)).im))
      (g := fun k => (B k).re / 2 * (Real.log ‖w - t k * I - 1‖ + Real.log ‖w + t k * I - 1‖))
    have h2 : ∑ k, ((B k).re / 2 * (Real.log ‖riemannZeta (w - t k * I)‖ +
        Real.log ‖riemannZeta (w + t k * I)‖) - (B k).im / 2 *
          ((RHTower.zetaEulerLog (w - t k * I)).im - (RHTower.zetaEulerLog (w + t k * I)).im) +
        (B k).re / 2 * (Real.log ‖w - t k * I - 1‖ + Real.log ‖w + t k * I - 1‖)) =
        ∑ k, ((B k).re / 2 * (Real.log ‖riemannZeta (w - t k * I)‖ + Real.log ‖w - t k * I - 1‖ +
          (Real.log ‖riemannZeta (w + t k * I)‖ + Real.log ‖w + t k * I - 1‖)) - (B k).im / 2 *
            ((RHTower.zetaEulerLog (w - t k * I)).im - (RHTower.zetaEulerLog (w + t k * I)).im)) :=
      Finset.sum_congr rfl fun k _ => by ring
    linarith
  have hterm : ∀ k, |term k| ≤ ‖B k‖ * (L + C) := by
    intro k
    obtain ⟨hm1, hm2⟩ := hbox' _ (hvm k).1 (hvm k).2
    obtain ⟨hp1, hp2⟩ := hbox' _ (hvp k).1 (hvp k).2
    have hre_le : |(B k).re| ≤ ‖B k‖ := Complex.abs_re_le_norm _
    have him_le : |(B k).im| ≤ ‖B k‖ := Complex.abs_im_le_norm _
    simp only [term]
    calc |(B k).re / 2 * (dz (w - t k * I) + dz (w + t k * I)) - (B k).im / 2 *
          ((RHTower.zetaEulerLog (w - t k * I)).im - (RHTower.zetaEulerLog (w + t k * I)).im)|
        ≤ |(B k).re| / 2 * (|dz (w - t k * I)| + |dz (w + t k * I)|) + |(B k).im| / 2 *
            (|(RHTower.zetaEulerLog (w - t k * I)).im| +
              |(RHTower.zetaEulerLog (w + t k * I)).im|) := by
          refine (abs_sub _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul, abs_div, abs_two]
            exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
          · rw [abs_mul, abs_div, abs_two]
            exact mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity)
      _ ≤ ‖B k‖ / 2 * (L + L) + ‖B k‖ / 2 * (C + C) := by
          gcongr
      _ = ‖B k‖ * (L + C) := by ring
  have hsum : |c₀ * dz w + ∑ k, term k| ≤ |c₀| * L + ∑ k, ‖B k‖ * (L + C) := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun k _ => hterm k)))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hw0.1 (abs_nonneg _)
  rw [← hdiff] at hsum
  have h3 := abs_sub_le (Real.log ‖spectralSeries c₀ t B w‖) (spectralEulerPhase c₀ t B w).re
    (spectralLogFactor c₀ t B w)
  linarith
end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
