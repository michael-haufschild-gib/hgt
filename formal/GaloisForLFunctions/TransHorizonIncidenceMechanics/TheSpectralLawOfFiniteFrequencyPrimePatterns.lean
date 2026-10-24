import GaloisForLFunctions.TransHorizonIncidenceMechanics.ThePhaseLawOfOscillatingPrimePatterns
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheEndpointAndPhaseDiagramOfOscillatingPrimePatterns
import GaloisForLFunctions.RHTower.Sieve.ZetaRealBound

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

/-! ### The series right of the line -/

/-- `|f(n) n^{-w}| ≤ n^{-Re w}`. -/
theorem norm_cweightedPatternHom_spectral_le {c₀ : ℝ} {t : Fin K → ℝ} {B : Fin K → ℂ}
    (hg : ∀ x, |spectralProfile c₀ t B x| ≤ 1) {w : ℂ} (hw : 1 < w.re) (n : ℕ) :
    ‖cweightedPatternHom (spectralPattern c₀ t B) w n‖ ≤ (n : ℝ) ^ (-w.re) := by
  simp only [cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (show -w.re ≠ 0 by intro h; linarith)]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hn0.le _) (abs_spectralPattern_le hg n)

/-- The pattern's Dirichlet series does not vanish right of the line (Euler product). -/
theorem spectralSeries_ne_zero {c₀ : ℝ} {t : Fin K → ℝ} {B : Fin K → ℂ}
    (hg : ∀ x, |spectralProfile c₀ t B x| ≤ 1) {w : ℂ} (hw : 1 < w.re) :
    spectralSeries c₀ t B w ≠ 0 := by
  have hsum : Summable fun n => ‖cweightedPatternHom (spectralPattern c₀ t B) w n‖ :=
    (Real.summable_nat_rpow.mpr (show -w.re < -1 by linarith)).of_nonneg_of_le
      (fun _ => norm_nonneg _) (norm_cweightedPatternHom_spectral_le hg hw)
  have hFn : ∑' n, cweightedPatternHom (spectralPattern c₀ t B) w n = spectralSeries c₀ t B w :=
    tsum_congr fun n => rfl
  rw [← hFn, ← EulerProduct.exp_tsum_primes_log_eq_tsum hsum]
  exact Complex.exp_ne_zero _

/-- The trivial bound `|F(w)| ≤ Σ n^{-Re w} ≤ 1 + 1/(Re w − 1)`. -/
theorem norm_spectralSeries_le {c₀ : ℝ} {t : Fin K → ℝ} {B : Fin K → ℂ}
    (hg : ∀ x, |spectralProfile c₀ t B x| ≤ 1) {w : ℂ} (hw : 1 < w.re) :
    ‖spectralSeries c₀ t B w‖ ≤ 1 + 1 / (w.re - 1) := by
  have hle := norm_cweightedPatternHom_spectral_le hg hw
  have hs : Summable fun n : ℕ => (n : ℝ) ^ (-w.re) := Real.summable_nat_rpow.mpr (by linarith)
  have hsum := hs.of_nonneg_of_le (fun _ => norm_nonneg _) hle
  have hFn : ∑' n, cweightedPatternHom (spectralPattern c₀ t B) w n = spectralSeries c₀ t B w :=
    tsum_congr fun n => rfl
  rw [← hFn]
  exact (norm_tsum_le_tsum_norm hsum).trans ((hsum.tsum_le_tsum hle hs).trans
    (RHTower.Sieve.tsum_nat_rpow_neg_le hw))

theorem dampedClass_spectralWeight {c₀ : ℝ} {t : Fin K → ℝ} {B : Fin K → ℂ}
    (hg : ∀ x, |spectralProfile c₀ t B x| ≤ 1) : DampedClass 1 (1 / 2) (spectralWeight c₀ t B) :=
  fun d => by
    simp only [spectralWeight]
    rw [one_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _)
      (abs_spectralPattern_le hg d)

/-- The receiver reads `F` on the line shifted by `1/2`: `C(s) = F(s + 1/2)`. -/
theorem weightDirichletSeries_spectralWeight (c₀ : ℝ) (t : Fin K → ℝ) (B : Fin K → ℂ) (s : ℂ) :
    weightDirichletSeries (spectralWeight c₀ t B) s = spectralSeries c₀ t B (s + 1 / 2) :=
  weightDirichletSeries_pattern (spectralPattern c₀ t B) s

/-! ### Singular heights -/

/-- The singular heights above the real axis: `η(none) = 0`, `η(some k) = t_k`. -/
def spectralHeight (t : Fin K → ℝ) (j : Option (Fin K)) : ℝ := j.elim 0 t

/-- Their exponents: `e(none) = c₀`, `e(some k) = Re B_k / 2`. -/
def spectralExponent (c₀ : ℝ) (B : Fin K → ℂ) (j : Option (Fin K)) : ℝ :=
  j.elim c₀ fun k => (B k).re / 2

/-- The log factor over the heights `η_j ≥ 0` and the mirror heights `−t_k`. -/
theorem spectralLogFactor_eq (c₀ : ℝ) (t : Fin K → ℝ) (B : Fin K → ℂ) (w : ℂ) :
    spectralLogFactor c₀ t B w = -(∑ j, spectralExponent c₀ B j *
      Real.log ‖w - 1 - spectralHeight t j * I‖) -
        ∑ k, (B k).re / 2 * Real.log ‖w + t k * I - 1‖ := by
  have h : ∀ k, w - t k * I - 1 = w - 1 - t k * I := fun k => by ring
  simp only [spectralLogFactor, Fintype.sum_option, spectralExponent, spectralHeight,
    Option.elim, Complex.ofReal_zero, zero_mul, sub_zero, h, mul_add, Finset.sum_add_distrib]
  ring

theorem spectralHeight_mem {t : Fin K → ℝ} (ht : ∀ k, 0 < t k) (j : Option (Fin K)) :
    0 ≤ spectralHeight t j ∧ spectralHeight t j ≤ ∑ k, t k := by
  cases j with
  | none => exact ⟨le_rfl, Finset.sum_nonneg fun k _ => (ht k).le⟩
  | some k => exact ⟨(ht k).le, Finset.single_le_sum (fun i _ => (ht i).le) (Finset.mem_univ k)⟩

theorem spectralHeight_injective {t : Fin K → ℝ} (ht : ∀ k, 0 < t k)
    (hinj : Function.Injective t) : Function.Injective (spectralHeight t) := by
  intro i j h
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some l => exact absurd h.symm (ht l).ne'
  | some k =>
    cases j with
    | none => exact absurd h (ht k).ne'
    | some l => exact congrArg some (hinj h)

/-- Finitely many distinct reals are `2δ`-separated for some `0 < δ ≤ 1`. -/
theorem exists_two_mul_le_abs_sub {ι : Type*} [Fintype ι] {η : ι → ℝ}
    (hη : Function.Injective η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ i j, i ≠ j → 2 * δ ≤ |η i - η j| := by
  classical
  set S := (Finset.univ : Finset (ι × ι)).filter fun p => p.1 ≠ p.2
  rcases S.eq_empty_or_nonempty with hS | hS
  · refine ⟨1, one_pos, le_rfl, fun i j hij => ?_⟩
    have h : (i, j) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
    rw [hS] at h
    simp at h
  · obtain ⟨p, hpS, hmin⟩ := S.exists_min_image (fun p => |η p.1 - η p.2|) hS
    have hp : 0 < |η p.1 - η p.2| :=
      abs_pos.mpr (sub_ne_zero.mpr fun h => (Finset.mem_filter.mp hpS).2 (hη h))
    refine ⟨min (|η p.1 - η p.2| / 2) 1, lt_min (by positivity) one_pos, min_le_right _ _,
      fun i j hij => ?_⟩
    have h1 := hmin (i, j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)
    have h2 := min_le_left (|η p.1 - η p.2| / 2) 1
    linarith

/-! ### Two-sided bounds on the log factor -/

/-- `|log d| ≤ |log δ| + |log D|` on `[δ, D]`. -/
theorem abs_log_le_of_mem_Icc {δ D d : ℝ} (hδ : 0 < δ) (h1 : δ ≤ d) (h2 : d ≤ D) :
    |Real.log d| ≤ |Real.log δ| + |Real.log D| := by
  have hd : 0 < d := hδ.trans_le h1
  rw [abs_le]
  constructor
  · have := Real.log_le_log hδ h1
    linarith [neg_abs_le (Real.log δ), abs_nonneg (Real.log D)]
  · have := Real.log_le_log hd h2
    linarith [le_abs_self (Real.log D), abs_nonneg (Real.log δ)]

theorem abs_mul_log_le {e d δ D : ℝ} (hδ : 0 < δ) (h1 : δ ≤ d) (h2 : d ≤ D) :
    |e * Real.log d| ≤ |e| * (|Real.log δ| + |Real.log D|) := by
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_log_le_of_mem_Icc hδ h1 h2) (abs_nonneg e)

/-- `−e log d ≤ |e| log D + e⁺ max(0, −log d)` for `0 < d ≤ D`, `1 ≤ D`. -/
theorem neg_mul_log_le {e d D : ℝ} (hd : 0 < d) (hdD : d ≤ D) (hD : 1 ≤ D) :
    -(e * Real.log d) ≤ |e| * Real.log D + max e 0 * max 0 (-Real.log d) := by
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  rcases le_total 1 d with h1 | h1
  · have hl0 : 0 ≤ Real.log d := Real.log_nonneg h1
    have hlD : Real.log d ≤ Real.log D := Real.log_le_log hd hdD
    rw [max_eq_left (by linarith : -Real.log d ≤ 0), mul_zero, add_zero]
    have h := mul_nonneg (show 0 ≤ |e| + e by linarith [neg_abs_le e]) hl0
    have h' := mul_le_mul_of_nonneg_left hlD (abs_nonneg e)
    nlinarith
  · have hl0 : Real.log d ≤ 0 := Real.log_nonpos hd.le h1
    rw [max_eq_right (by linarith : 0 ≤ -Real.log d)]
    have h := mul_nonneg (sub_nonneg.mpr (le_max_left e 0)) (neg_nonneg.mpr hl0)
    have h' := mul_nonneg (abs_nonneg e) hlogD
    nlinarith

/-- **Upper bound of the log factor**: every height contributes at most `e⁺ max(0, −log d)`
beyond a constant, when the mirror distances lie in `[δ, D]`. -/
theorem spectralLogFactor_le {c₀ : ℝ} {t : Fin K → ℝ} {B : Fin K → ℂ} {w : ℂ} {δ D : ℝ}
    (hδ : 0 < δ) (hD : 1 ≤ D)
    (hd : ∀ j, 0 < ‖w - 1 - spectralHeight t j * I‖ ∧ ‖w - 1 - spectralHeight t j * I‖ ≤ D)
    (hdp : ∀ k, δ ≤ ‖w + t k * I - 1‖ ∧ ‖w + t k * I - 1‖ ≤ D) :
    spectralLogFactor c₀ t B w ≤ (∑ j, |spectralExponent c₀ B j|) * Real.log D +
      (∑ k, |(B k).re / 2|) * (|Real.log δ| + |Real.log D|) +
      ∑ j, max (spectralExponent c₀ B j) 0 *
        max 0 (-Real.log ‖w - 1 - spectralHeight t j * I‖) := by
  rw [spectralLogFactor_eq]
  have h1 : -(∑ j, spectralExponent c₀ B j * Real.log ‖w - 1 - spectralHeight t j * I‖) ≤
      ∑ j, (|spectralExponent c₀ B j| * Real.log D + max (spectralExponent c₀ B j) 0 *
        max 0 (-Real.log ‖w - 1 - spectralHeight t j * I‖)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun j _ => neg_mul_log_le (hd j).1 (hd j).2 hD
  have h2 : -(∑ k, (B k).re / 2 * Real.log ‖w + t k * I - 1‖) ≤
      ∑ k, |(B k).re / 2| * (|Real.log δ| + |Real.log D|) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun k _ =>
      (neg_le_abs _).trans (abs_mul_log_le hδ (hdp k).1 (hdp k).2)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at h1
  rw [← Finset.sum_mul] at h2
  linarith

/-- **Lower bound of the log factor** at a distinguished height `η_{j₀}`, when all other
distances lie in `[δ, D]`. -/
theorem le_spectralLogFactor {c₀ : ℝ} {t : Fin K → ℝ} {B : Fin K → ℂ} {w : ℂ} {δ D : ℝ}
    (hδ : 0 < δ) (j₀ : Option (Fin K))
    (hd : ∀ j, j ≠ j₀ → δ ≤ ‖w - 1 - spectralHeight t j * I‖ ∧
      ‖w - 1 - spectralHeight t j * I‖ ≤ D)
    (hdp : ∀ k, δ ≤ ‖w + t k * I - 1‖ ∧ ‖w + t k * I - 1‖ ≤ D) :
    -(spectralExponent c₀ B j₀ * Real.log ‖w - 1 - spectralHeight t j₀ * I‖) -
      ((∑ j, |spectralExponent c₀ B j|) + ∑ k, |(B k).re / 2|) *
        (|Real.log δ| + |Real.log D|) ≤ spectralLogFactor c₀ t B w := by
  rw [spectralLogFactor_eq, ← Finset.add_sum_erase Finset.univ
    (fun j => spectralExponent c₀ B j * Real.log ‖w - 1 - spectralHeight t j * I‖)
    (Finset.mem_univ j₀)]
  have hΛ : 0 ≤ |Real.log δ| + |Real.log D| := by positivity
  have h1 : ∑ j ∈ Finset.univ.erase j₀, spectralExponent c₀ B j *
      Real.log ‖w - 1 - spectralHeight t j * I‖ ≤
        ∑ j, |spectralExponent c₀ B j| * (|Real.log δ| + |Real.log D|) := by
    refine (Finset.sum_le_sum fun j hj => (le_abs_self _).trans
      (abs_mul_log_le hδ (hd j (Finset.ne_of_mem_erase hj)).1
        (hd j (Finset.ne_of_mem_erase hj)).2)).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      fun j _ _ => mul_nonneg (abs_nonneg _) hΛ
  have h2 : ∑ k, (B k).re / 2 * Real.log ‖w + t k * I - 1‖ ≤
      ∑ k, |(B k).re / 2| * (|Real.log δ| + |Real.log D|) :=
    Finset.sum_le_sum fun k _ => (le_abs_self _).trans (abs_mul_log_le hδ (hdp k).1 (hdp k).2)
  rw [← Finset.sum_mul] at h1 h2
  have h3 := add_mul (∑ j, |spectralExponent c₀ B j|) (∑ k, |(B k).re / 2|)
    (|Real.log δ| + |Real.log D|)
  linarith

/-- **The local lower bound.** The heights are `2δ`-separated, and within `δ` of the height
`η_{j₀}`: `log|F(w)| ≥ −e_{j₀} log|w − 1 − iη_{j₀}| − C`. -/
theorem exists_le_log_norm_spectralSeries {c₀ : ℝ} {t : Fin K → ℝ} {B : Fin K → ℂ}
    (hg : ∀ x, |spectralProfile c₀ t B x| ≤ 1) (ht : ∀ k, 0 < t k)
    (hinj : Function.Injective t) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ j₀ : Option (Fin K), ∀ w : ℂ, 1 < w.re →
      ‖w - 1 - spectralHeight t j₀ * I‖ < δ →
        -(spectralExponent c₀ B j₀ * Real.log ‖w - 1 - spectralHeight t j₀ * I‖) - C ≤
          Real.log ‖spectralSeries c₀ t B w‖ := by
  obtain ⟨δ, hδ, hδ1, hsep⟩ := exists_two_mul_le_abs_sub (spectralHeight_injective ht hinj)
  obtain ⟨St, hSt⟩ : ∃ St : ℝ, St = ∑ k, t k := ⟨_, rfl⟩
  have hSt0 : 0 ≤ St := hSt ▸ Finset.sum_nonneg fun k _ => (ht k).le
  obtain ⟨C₁, hC₁⟩ := exists_abs_log_norm_spectralSeries_sub_le hg (1 + St)
  refine ⟨δ, C₁ + ((∑ j, |spectralExponent c₀ B j|) + ∑ k, |(B k).re / 2|) *
    (|Real.log δ| + |Real.log (3 + 2 * St)|), hδ, hδ1, fun j₀ w hw hnear => ?_⟩
  have hηm := spectralHeight_mem ht
  have htk : ∀ k, t k ≤ St := fun k => hSt ▸ (hηm (some k)).2
  have htδ : ∀ k, 2 * δ ≤ t k := fun k => by
    have h := hsep (some k) none (Option.some_ne_none k)
    simp only [spectralHeight, Option.elim, sub_zero, abs_of_pos (ht k)] at h
    exact h
  have him : ∀ η : ℝ, (w - 1 - η * I).im = w.im - η := fun η => by simp
  have hre : ∀ η : ℝ, (w - 1 - η * I).re = w.re - 1 := fun η => by simp
  have hnre := Complex.abs_re_le_norm (w - 1 - spectralHeight t j₀ * I)
  have hnim := Complex.abs_im_le_norm (w - 1 - spectralHeight t j₀ * I)
  rw [hre, abs_of_pos (by linarith)] at hnre
  rw [him] at hnim
  have hw2 : w.re ≤ 2 := by linarith
  have hη₀ := hηm j₀
  have hwim : |w.im| ≤ 1 + St := by
    rw [abs_le] at hnim ⊢
    constructor <;> linarith [hSt ▸ hη₀.2]
  have hnorm : ∀ v : ℂ, v.re = w.re - 1 → |v.im| ≤ 1 + 2 * St → ‖v‖ ≤ 3 + 2 * St := by
    intro v hvre hvim
    have := Complex.norm_le_abs_re_add_abs_im v
    rw [hvre, abs_of_pos (by linarith)] at this
    linarith
  have hfar : ∀ j, j ≠ j₀ → δ ≤ ‖w - 1 - spectralHeight t j * I‖ ∧
      ‖w - 1 - spectralHeight t j * I‖ ≤ 3 + 2 * St := by
    intro j hj
    have hsj := hsep j j₀ hj
    have hηj := hηm j
    constructor
    · have h := Complex.abs_im_le_norm (w - 1 - spectralHeight t j * I)
      rw [him] at h
      have : |spectralHeight t j - spectralHeight t j₀| ≤
          |w.im - spectralHeight t j| + |w.im - spectralHeight t j₀| := by
        calc |spectralHeight t j - spectralHeight t j₀|
            = |(w.im - spectralHeight t j₀) - (w.im - spectralHeight t j)| := by ring_nf
          _ ≤ |w.im - spectralHeight t j₀| + |w.im - spectralHeight t j| := abs_sub _ _
          _ = _ := add_comm _ _
      linarith
    · refine hnorm _ (hre _) ?_
      rw [him]
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg hηj.1]
      linarith [hSt ▸ hηj.2]
  have hfarp : ∀ k, δ ≤ ‖w + t k * I - 1‖ ∧ ‖w + t k * I - 1‖ ≤ 3 + 2 * St := by
    intro k
    have hre' : (w + t k * I - 1).re = w.re - 1 := by simp
    have him' : (w + t k * I - 1).im = w.im + t k := by simp
    have hlow : spectralHeight t j₀ - δ ≤ w.im := by
      rw [abs_le] at hnim; linarith
    constructor
    · have h := Complex.abs_im_le_norm (w + t k * I - 1)
      rw [him', abs_of_pos (by linarith [htδ k, hη₀.1])] at h
      linarith [htδ k, hη₀.1]
    · refine hnorm _ hre' ?_
      rw [him']
      refine (abs_add_le _ _).trans ?_
      rw [abs_of_pos (ht k)]
      linarith [htk k]
  have hL := le_spectralLogFactor (c₀ := c₀) (B := B) hδ j₀ hfar hfarp
  have hF := (abs_le.mp (hC₁ w hw hw2 hwim)).1
  linarith

/-! ### The amplitude cap -/

/-- **The amplitude cap** `Re B_k ≤ 2`: near `1 + it_k` the series grows like
`|w − 1 − it_k|^{-Re B_k/2}`, but never faster than `ζ(Re w) ≤ 1 + 1/(Re w − 1)`. -/
theorem spectralAmplitude_re_le_two {c₀ : ℝ} {t : Fin K → ℝ} {B : Fin K → ℂ}
    (hg : ∀ x, |spectralProfile c₀ t B x| ≤ 1) (ht : ∀ k, 0 < t k)
    (hinj : Function.Injective t) (k : Fin K) : (B k).re ≤ 2 := by
  obtain ⟨δ, C, hδ, hδ1, hlow⟩ := exists_le_log_norm_spectralSeries hg ht hinj
  by_contra hB
  push Not at hB
  obtain ⟨κ, hκ_def⟩ : ∃ κ : ℝ, κ = (B k).re / 2 - 1 := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκ_def]; linarith
  obtain ⟨X, hX_def⟩ : ∃ X : ℝ, X = (|C| + Real.log 2) / κ + 1 := ⟨_, rfl⟩
  obtain ⟨u, hu_def⟩ : ∃ u : ℝ, u = δ / 2 * Real.exp (-X) := ⟨_, rfl⟩
  have hu : 0 < u := by rw [hu_def]; positivity
  have hX0 : 0 ≤ X := by rw [hX_def]; have := Real.log_pos one_lt_two; positivity
  have hexp1 : Real.exp (-X) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have huδ : u ≤ δ / 2 := by
    rw [hu_def]; exact mul_le_of_le_one_right (by positivity) hexp1
  have hu1 : u ≤ 1 := by linarith
  set w : ℂ := ((1 + u : ℝ) : ℂ) + (t k : ℂ) * I
  have hwre : w.re = 1 + u := by simp [w]
  have hd : w - 1 - spectralHeight t (some k) * I = (u : ℂ) := by
    simp only [w, spectralHeight, Option.elim]; push_cast; ring
  have hdn : ‖w - 1 - spectralHeight t (some k) * I‖ = u := by
    rw [hd, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  have h1 := hlow (some k) w (by rw [hwre]; linarith) (by rw [hdn]; linarith)
  rw [hdn] at h1
  have he : spectralExponent c₀ B (some k) = (B k).re / 2 := rfl
  rw [he] at h1
  have hw1 : 1 < w.re := by rw [hwre]; linarith
  have h2 : Real.log ‖spectralSeries c₀ t B w‖ ≤ Real.log 2 - Real.log u := by
    have hF0 := norm_pos_iff.mpr (spectralSeries_ne_zero hg hw1)
    have hle := norm_spectralSeries_le hg hw1
    rw [hwre, add_sub_cancel_left] at hle
    have hinv : 1 ≤ 1 / u := by rw [le_div_iff₀ hu]; linarith
    have h2u : 1 + 1 / u ≤ 2 / u := by
      have : 2 / u = 1 / u + 1 / u := by ring
      linarith
    calc Real.log ‖spectralSeries c₀ t B w‖ ≤ Real.log (2 / u) :=
          Real.log_le_log hF0 (hle.trans h2u)
      _ = Real.log 2 - Real.log u := Real.log_div (by norm_num) hu.ne'
  have hlogu : Real.log u = Real.log (δ / 2) - X := by
    rw [hu_def, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]; ring
  have hlogδ : Real.log (δ / 2) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
  have hκu : κ * (-Real.log u) = -((B k).re / 2 * Real.log u) + Real.log u := by
    rw [hκ_def]; ring
  have h3 : κ * (-Real.log u) ≤ C + Real.log 2 := by linarith
  have h4 : κ * X ≤ κ * (-Real.log u) := mul_le_mul_of_nonneg_left (by linarith) hκ.le
  have h5 : κ * X = |C| + Real.log 2 + κ := by rw [hX_def]; field_simp
  linarith [le_abs_self C]

/-! ### The unpaid range -/

/-- `−e log d − C ≤ log x` with `e ≥ 1/2`, `0 < d < 1` gives `x² ≥ e^{-2C}/d`. -/
theorem exp_div_le_sq_of_le_log {x d e C : ℝ} (hx : 0 < x) (hd0 : 0 < d) (hd1 : d < 1)
    (he : 1 / 2 ≤ e) (h : -(e * Real.log d) - C ≤ Real.log x) :
    Real.exp (-(2 * C)) / d ≤ x ^ 2 := by
  have hlogd : Real.log d < 0 := Real.log_neg hd0 hd1
  have h5 : (e - 1 / 2) * Real.log d ≤ 0 :=
    mul_nonpos_iff.mpr (Or.inl ⟨sub_nonneg.mpr he, hlogd.le⟩)
  have h2 : -(1 / 2 * Real.log d) - C ≤ Real.log x := by nlinarith
  have h3 : Real.exp (-(1 / 2 * Real.log d) - C) ≤ x :=
    (Real.exp_le_exp.mpr h2).trans (Real.exp_log hx).le
  have h4 : Real.exp (-(1 / 2 * Real.log d) - C) ^ 2 = Real.exp (-(2 * C)) / d := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-(1 / 2 * Real.log d) - C) =
      -(2 * C) + -Real.log d by push_cast; ring, Real.exp_add, Real.exp_neg (Real.log d),
      Real.exp_log hd0, div_eq_mul_inv]
  rw [← h4]
  exact pow_le_pow_left₀ (Real.exp_pos _).le h3 2

/-- **The mean is read at `s = 1/2`**: `c₀ ≥ 1/2` leaves the spectral weight unpaid. -/
theorem not_receiverBounded_spectralWeight_of_half_le {c₀ : ℝ} {t : Fin K → ℝ} {B : Fin K → ℂ}
    (hg : ∀ x, |spectralProfile c₀ t B x| ≤ 1) (ht : ∀ k, 0 < t k)
    (hinj : Function.Injective t) (hc₀ : 1 / 2 ≤ c₀) :
    ¬ ReceiverBounded (spectralWeight c₀ t B) := by
  obtain ⟨δ, C, hδ, hδ1, hlow⟩ := exists_le_log_norm_spectralSeries hg ht hinj
  refine not_receiverBounded_of_sq_norm_dirichletSeries_ge (dampedClass_spectralWeight hg)
    (Real.exp_pos (-(2 * C))) hδ fun s hs hsδ => ?_
  have hw : 1 < (s + 1 / 2).re := by simp; linarith
  have hd : s + 1 / 2 - 1 - spectralHeight t none * I = s - 1 / 2 := by
    simp only [spectralHeight, Option.elim, Complex.ofReal_zero, zero_mul, sub_zero]; ring
  have h1 := hlow none (s + 1 / 2) hw (by rw [hd]; exact hsδ)
  rw [hd] at h1
  have hd0 : 0 < ‖s - 1 / 2‖ := by
    have := Complex.abs_re_le_norm (s - 1 / 2)
    have hre : (s - 1 / 2).re = s.re - 1 / 2 := by simp
    rw [hre, abs_of_pos (by linarith)] at this
    linarith
  rw [weightDirichletSeries_spectralWeight]
  exact exp_div_le_sq_of_le_log (norm_pos_iff.mpr (spectralSeries_ne_zero hg hw)) hd0
    (hsδ.trans_le hδ1) hc₀ h1

/-- **An amplitude is read at its height**: `Re B_k ≥ 1` with `ζ(1/2 + it_k) ≠ 0` leaves the
spectral weight unpaid. -/
theorem not_receiverBounded_spectralWeight_of_one_le {c₀ : ℝ} {t : Fin K → ℝ} {B : Fin K → ℂ}
    (hg : ∀ x, |spectralProfile c₀ t B x| ≤ 1) (ht : ∀ k, 0 < t k)
    (hinj : Function.Injective t) {k : Fin K} (hk : 1 ≤ (B k).re)
    (hz : riemannZeta (1 / 2 + (t k : ℂ) * I) ≠ 0) :
    ¬ ReceiverBounded (spectralWeight c₀ t B) := by
  obtain ⟨δ, C, hδ, hδ1, hlow⟩ := exists_le_log_norm_spectralSeries hg ht hinj
  refine not_receiverBounded_of_sq_norm_dirichletSeries_ge_at_height
    (dampedClass_spectralWeight hg) (ht k) hz (Real.exp_pos (-(2 * C))) hδ fun s hs hsδ => ?_
  have hw : 1 < (s + 1 / 2).re := by simp; linarith
  have hd : s + 1 / 2 - 1 - spectralHeight t (some k) * I = s - (1 / 2 + (t k : ℂ) * I) := by
    simp only [spectralHeight, Option.elim]; ring
  have h1 := hlow (some k) (s + 1 / 2) hw (by rw [hd]; exact hsδ)
  rw [hd] at h1
  have hd0 : 0 < ‖s - (1 / 2 + (t k : ℂ) * I)‖ := by
    have := Complex.abs_re_le_norm (s - (1 / 2 + (t k : ℂ) * I))
    have hre : (s - (1 / 2 + (t k : ℂ) * I)).re = s.re - 1 / 2 := by simp
    rw [hre, abs_of_pos (by linarith)] at this
    linarith
  rw [weightDirichletSeries_spectralWeight]
  exact exp_div_le_sq_of_le_log (norm_pos_iff.mpr (spectralSeries_ne_zero hg hw)) hd0
    (hsδ.trans_le hδ1) (show 1 / 2 ≤ (B k).re / 2 by linarith) h1

/-! ### The paid range -/

/-- At a zero `s₀ ≠ 1` of `ζ`, on the box `1/2 ≤ σ ≤ 3/4`, `|τ| ≤ T`: `|ζ(s)| ≤ L |s − s₀|`. -/
theorem exists_norm_zeta_le_mul_of_zero {s₀ : ℂ} (hs₀ : s₀ ≠ 1) (hz : riemannZeta s₀ = 0)
    (T : ℝ) : ∃ L : ℝ, 0 ≤ L ∧ ∀ σ τ : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 4 → |τ| ≤ T →
      ‖riemannZeta ((σ : ℂ) + τ * I)‖ ≤ L * ‖(σ : ℂ) + τ * I - s₀‖ := by
  obtain ⟨r, L, hr, hL, hLip⟩ := exists_norm_zeta_sub_le hs₀
  obtain ⟨Z₀, hZ₀, hZ⟩ := exists_norm_zeta_le_on_tall_box T
  refine ⟨L + Z₀ / r, by positivity, fun σ τ hσ hσ' hτ => ?_⟩
  have hn := norm_nonneg ((σ : ℂ) + τ * I - s₀)
  rcases le_or_gt ‖(σ : ℂ) + τ * I - s₀‖ r with h | h
  · have h1 := hLip ((σ : ℂ) + τ * I) h
    rw [hz, sub_zero] at h1
    nlinarith [mul_nonneg (div_nonneg hZ₀ hr.le) hn]
  · have h1 := hZ σ τ hσ hσ' hτ
    have h2 : Z₀ ≤ Z₀ / r * ‖(σ : ℂ) + τ * I - s₀‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hr]
      exact mul_le_mul_of_nonneg_left h.le hZ₀
    nlinarith [mul_nonneg hL hn]

/-- `lam < max(0, −log d)` with `lam = −log δ`, `δ ≤ 1`, forces `d < δ`. -/
theorem lt_of_neg_log_lt_max {d δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h : -Real.log δ < max 0 (-Real.log d)) : d < δ := by
  by_contra hle
  push Not at hle
  have h1 : -Real.log d ≤ -Real.log δ := by linarith [Real.log_le_log hδ hle]
  have h2 : 0 ≤ -Real.log δ := neg_nonneg.mpr (Real.log_nonpos hδ.le hδ1)
  exact absurd h (not_lt.mpr (max_le h2 h1))

/-- **One large term.** If at most one `ℓ_j` exceeds `lam ≥ 0`, then
`exp(Σ a_j ℓ_j) ≤ exp((Σ a_j) lam) (1 + Σ exp(a_j ℓ_j))`. -/
theorem exp_sum_le_of_unique_large {ι : Type*} [Fintype ι] {a ℓ : ι → ℝ} {lam : ℝ}
    (ha : ∀ j, 0 ≤ a j) (hlam : 0 ≤ lam) (huniq : ∀ i j, lam < ℓ i → lam < ℓ j → i = j) :
    Real.exp (∑ j, a j * ℓ j) ≤
      Real.exp ((∑ j, a j) * lam) * (1 + ∑ j, Real.exp (a j * ℓ j)) := by
  classical
  have hS : 0 ≤ ∑ j, Real.exp (a j * ℓ j) := Finset.sum_nonneg fun j _ => (Real.exp_pos _).le
  have hE := (Real.exp_pos ((∑ j, a j) * lam)).le
  by_cases h : ∃ i, lam < ℓ i
  · obtain ⟨i, hi⟩ := h
    have hrest : ∀ j ∈ Finset.univ.erase i, a j * ℓ j ≤ a j * lam := fun j hj =>
      mul_le_mul_of_nonneg_left
        (not_lt.mp fun hj' => Finset.ne_of_mem_erase hj (huniq j i hj' hi)) (ha j)
    have hsum : ∑ j, a j * ℓ j ≤ (∑ j, a j) * lam + a i * ℓ i := by
      rw [← Finset.add_sum_erase Finset.univ (fun j => a j * ℓ j) (Finset.mem_univ i),
        Finset.sum_mul,
        ← Finset.add_sum_erase Finset.univ (fun j => a j * lam) (Finset.mem_univ i)]
      have h1 := Finset.sum_le_sum hrest
      have h2 := mul_nonneg (ha i) hlam
      linarith
    have hi1 : Real.exp (a i * ℓ i) ≤ 1 + ∑ j, Real.exp (a j * ℓ j) := by
      have := Finset.single_le_sum (f := fun j => Real.exp (a j * ℓ j))
        (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)
      linarith
    calc Real.exp (∑ j, a j * ℓ j) ≤ Real.exp ((∑ j, a j) * lam + a i * ℓ i) :=
          Real.exp_le_exp.mpr hsum
      _ = Real.exp ((∑ j, a j) * lam) * Real.exp (a i * ℓ i) := Real.exp_add _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hi1 hE
  · push Not at h
    have hsum : ∑ j, a j * ℓ j ≤ (∑ j, a j) * lam := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (ha j)
    calc Real.exp (∑ j, a j * ℓ j) ≤ Real.exp ((∑ j, a j) * lam) := Real.exp_le_exp.mpr hsum
      _ = Real.exp ((∑ j, a j) * lam) * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hE

/-- Near a cancelling zero: `d² exp(a max(0, −log d))² ≤ D²` for `a ≤ 1`, `0 < d ≤ D`, `1 ≤ D`. -/
theorem sq_mul_exp_sq_le {a d D : ℝ} (ha : a ≤ 1) (hd : 0 < d) (hdD : d ≤ D) (hD : 1 ≤ D) :
    d ^ 2 * Real.exp (a * max 0 (-Real.log d)) ^ 2 ≤ D ^ 2 := by
  rcases le_total 1 d with h1 | h1
  · rw [max_eq_left (by linarith [Real.log_nonneg h1] : -Real.log d ≤ 0), mul_zero,
      Real.exp_zero, one_pow, mul_one]
    exact pow_le_pow_left₀ hd.le hdD 2
  · have hl : Real.log d ≤ 0 := Real.log_nonpos hd.le h1
    rw [max_eq_right (by linarith : 0 ≤ -Real.log d)]
    have hd2 : Real.exp (2 * Real.log d) = d ^ 2 := by
      rw [show (2 : ℝ) * Real.log d = ((2 : ℕ) : ℝ) * Real.log d by norm_num, Real.exp_nat_mul,
        Real.exp_log hd]
    have he : Real.exp (a * -Real.log d) ^ 2 = Real.exp (2 * (a * -Real.log d)) := by
      rw [← Real.exp_nat_mul]; norm_num
    calc d ^ 2 * Real.exp (a * -Real.log d) ^ 2
        = Real.exp (2 * Real.log d) * Real.exp (2 * (a * -Real.log d)) := by rw [hd2, he]
      _ = Real.exp (2 * ((1 - a) * Real.log d)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr
          (by nlinarith [mul_nonneg (sub_nonneg.mpr ha) (neg_nonneg.mpr hl)])
      _ = 1 := Real.exp_zero
      _ ≤ D ^ 2 := one_le_pow₀ hD

/-- Away from cancellation: `exp(a max(0, −log d))² ≤ 1 + x^{-2a}` for `a ≥ 0`, `0 < x ≤ d`. -/
theorem exp_mul_sq_le {a d x : ℝ} (ha : 0 ≤ a) (hx : 0 < x) (hxd : x ≤ d) :
    Real.exp (a * max 0 (-Real.log d)) ^ 2 ≤ 1 + x ^ (-(2 * a)) := by
  have hd : 0 < d := hx.trans_le hxd
  have hx0 : 0 ≤ x ^ (-(2 * a)) := Real.rpow_nonneg hx.le _
  rcases le_total 1 d with h1 | h1
  · rw [max_eq_left (by linarith [Real.log_nonneg h1] : -Real.log d ≤ 0), mul_zero,
      Real.exp_zero, one_pow]
    linarith
  · rw [max_eq_right (by linarith [Real.log_nonpos hd.le h1] : 0 ≤ -Real.log d)]
    have h : Real.exp (a * -Real.log d) ^ 2 = d ^ (-(2 * a)) := by
      rw [← Real.exp_nat_mul, Real.rpow_def_of_pos hd]; congr 1; push_cast; ring
    rw [h]
    have := Real.rpow_le_rpow_of_nonpos hx hxd (by linarith : -(2 * a) ≤ 0)
    linarith

/-- **An integrable local majorant off a countable set of heights pays the line energy.** -/
theorem exists_lineEnergy_le_of_majorant_off_countable {c : ℕ → ℝ} {P T B₁ : ℝ} {S : Set ℝ}
    {g : ℝ → ℝ} (hS : S.Countable) (hT : 2 ≤ T) (hg : IntegrableOn g (Ioc 0 T))
    (hsmall : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 → 0 < t → t ≤ T → t ∉ S →
      lineIntegrand c P σ t ≤ g t)
    (hlarge : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 → T < t →
      ‖weightDirichletSeries c ((σ : ℂ) + t * I) - (P : ℂ)‖ ≤ B₁ * t ^ (1 / 4 : ℝ)) :
    ∃ M : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ < 3 / 4 → ∫ t : ℝ, lineIntegrand c P σ t ≤ M := by
  obtain ⟨M₂, hM₂⟩ := exists_integral_zeta_sq_rpow_le
  set Λ : ℝ := B₁ ^ 2
  have hΛ : 0 ≤ Λ := sq_nonneg _
  refine ⟨2 * ((∫ t in Ioc 0 T, g t) + Λ * M₂), fun σ hσ hσ' => ?_⟩
  set Φ : ℝ → ℝ := lineIntegrand c P σ with hΦ
  change ∫ t : ℝ, Φ t ≤ _
  obtain ⟨hint2, hbound2⟩ := hM₂ σ hσ.le (by linarith)
  have hΦform : ∀ t, Φ t = ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 *
      ‖weightDirichletSeries c ((σ : ℂ) + t * I) - (P : ℂ)‖ ^ 2 / ‖(σ : ℂ) + t * I‖ ^ 2 :=
    fun t => by simp only [hΦ, lineIntegrand, norm_div, norm_mul, div_pow, mul_pow]
  -- beyond `T`
  have hlarge' : ∀ u : ℝ, T < u →
      Φ u ≤ Λ * (‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ))) := by
    intro u hu
    have hu0 : 0 < u := by linarith
    have hsn : u ≤ ‖(σ : ℂ) + u * I‖ := by
      have := Complex.abs_im_le_norm ((σ : ℂ) + u * I)
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add] at this
      rwa [abs_of_pos hu0] at this
    rw [hΦform u, div_le_iff₀ (pow_pos (lt_of_lt_of_le hu0 hsn) 2)]
    have hX := pow_le_pow_left₀ (norm_nonneg _) (hlarge σ u hσ hσ' hu) 2
    have hq2 : (u ^ (1 / 4 : ℝ)) ^ 2 = u ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; norm_num
    have hpow : u ^ (-(3 / 2 : ℝ)) * u ^ 2 = u ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hu0]; norm_num
    have hs2 : u ^ 2 ≤ ‖(σ : ℂ) + u * I‖ ^ 2 := pow_le_pow_left₀ hu0.le hsn 2
    calc ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 *
          ‖weightDirichletSeries c ((σ : ℂ) + u * I) - (P : ℂ)‖ ^ 2
        ≤ ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * (Λ * u ^ (1 / 2 : ℝ)) := by
          refine mul_le_mul_of_nonneg_left (hX.trans (le_of_eq ?_)) (sq_nonneg _)
          rw [mul_pow, hq2]
      _ = Λ * (‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ))) * u ^ 2 := by
          rw [← hpow]; ring
      _ ≤ Λ * (‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ))) *
            ‖(σ : ℂ) + u * I‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hs2 (by positivity)
  -- the majorant on the half-line
  set G : ℝ → ℝ := fun u => if u ≤ T then g u
    else Λ * (‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ)))
  have hint2T : IntegrableOn
      (fun u : ℝ => ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ))) (Ioi T) :=
    hint2.mono_set (Ioi_subset_Ioi hT)
  have hsplit : Ioi (0 : ℝ) = Ioc 0 T ∪ Ioi T := (Ioc_union_Ioi_eq_Ioi (by linarith)).symm
  have hGint : IntegrableOn G (Ioi 0) := by
    rw [hsplit]
    refine IntegrableOn.union ?_ ?_
    · exact hg.congr_fun (fun u hu => by simp only [G, if_pos hu.2]) measurableSet_Ioc
    · refine IntegrableOn.congr_fun (hint2T.const_mul Λ) (fun u hu => ?_) measurableSet_Ioi
      have : ¬ u ≤ T := not_le.mpr hu
      simp only [G, if_neg this]
  have hΦ0 : ∀ u, 0 ≤ Φ u := fun u => by simp only [hΦ, lineIntegrand]; positivity
  have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ∉ S := compl_mem_ae_iff.mpr (hS.measure_zero volume)
  have hΦle : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), Φ u ≤ G u := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (hne.mono fun u hu hpos => ?_)
    by_cases h2 : u ≤ T
    · simp only [G, if_pos h2]; exact hsmall σ u hσ hσ' hpos h2 hu
    · simp only [G, if_neg h2]; exact hlarge' u (not_le.mp h2)
  have hhalf : ∫ u in Ioi (0 : ℝ), Φ u ≤ ∫ u in Ioi (0 : ℝ), G u :=
    integral_mono_of_nonneg (Eventually.of_forall hΦ0) hGint hΦle
  have hG1 : ∫ u in Ioc 0 T, G u = ∫ u in Ioc 0 T, g u :=
    setIntegral_congr_fun measurableSet_Ioc (fun u hu => by simp only [G, if_pos hu.2])
  have hG2 : ∫ u in Ioi T, G u =
      Λ * ∫ u in Ioi T, ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ)) := by
    rw [setIntegral_congr_fun
        (g := fun u : ℝ => Λ * (‖riemannZeta ((σ : ℂ) + (u : ℂ) * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ))))
        measurableSet_Ioi (fun u hu => by
          have : ¬ u ≤ T := not_le.mpr hu
          simp only [G, if_neg this]), integral_const_mul]
  have hGval : ∫ u in Ioi (0 : ℝ), G u = (∫ u in Ioc 0 T, g u) +
      Λ * ∫ u in Ioi T, ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ)) := by
    rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hGint.mono_set (by rw [hsplit]; exact subset_union_left))
      (hGint.mono_set (by rw [hsplit]; exact subset_union_right)), hG1, hG2]
  have htail : ∫ u in Ioi T, ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ)) ≤ M₂ := by
    refine le_trans (setIntegral_mono_set hint2 ?_ (Ioi_subset_Ioi hT).eventuallyLE) hbound2
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith [mem_Ioi.mp hu]) _)
  have heven : ∫ t : ℝ, Φ t = 2 * ∫ u in Ioi (0 : ℝ), Φ u := by
    rw [← integral_comp_abs]
    congr 1
    funext t
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, hΦ, lineIntegrand_neg]
  rw [heven]
  have := mul_le_mul_of_nonneg_left htail hΛ
  linarith

/-- **The large-height bound**: `|F(w)| ≤ B₁ (Im w)^{1/4}` for `Im w > 2 Σ_k t_k + 18`. -/
theorem exists_norm_spectralSeries_le_large {c₀ : ℝ} {t : Fin K → ℝ} {B : Fin K → ℂ}
    (hg : ∀ x, |spectralProfile c₀ t B x| ≤ 1) (ht : ∀ k, 0 < t k) :
    ∃ B₁ : ℝ, ∀ w : ℂ, 1 < w.re → w.re ≤ 2 → 2 * (∑ k, t k) + 18 < w.im →
      ‖spectralSeries c₀ t B w‖ ≤ B₁ * w.im ^ (1 / 4 : ℝ) := by
  obtain ⟨CL, hCL⟩ := RHTower.exists_norm_zetaEulerLog_le_large
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = |c₀| + ∑ k, ‖B k‖ := ⟨_, rfl⟩
  obtain ⟨M, hM_def⟩ : ∃ M : ℕ, M = ⌈9 * N⌉₊ := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (1 + |c₀| + ∑ k, ‖B k‖) * primeSquareMass := ⟨_, rfl⟩
  refine ⟨Real.exp (E + N * |CL|) * 2 ^ M * (4 * ((M : ℝ) + 1)) ^ M, fun w hw hw2 hy => ?_⟩
  have hSt : 0 ≤ ∑ k, t k := Finset.sum_nonneg fun k _ => (ht k).le
  have htk : ∀ k, t k ≤ ∑ k, t k := fun k =>
    Finset.single_le_sum (fun i _ => (ht i).le) (Finset.mem_univ k)
  have hy18 : 18 < w.im := by linarith
  have hlog2 := Real.log_two_gt_d9
  have hlogy : Real.log 2 ≤ Real.log w.im := Real.log_le_log (by norm_num) (by linarith)
  have hX : 0 ≤ Real.log (2 * Real.log w.im) := Real.log_nonneg (by linarith)
  -- `‖ℓ(Re w + iτ)‖ ≤ 9 log(2 log y) + |CL|` for `9 ≤ τ ≤ 2y`
  have hℓ : ∀ τ : ℝ, 9 ≤ τ → τ ≤ 2 * w.im →
      ‖RHTower.zetaEulerLog ((w.re : ℂ) + τ * I)‖ ≤
        9 * Real.log (2 * Real.log w.im) + |CL| := by
    intro τ hτ hτy
    have h := hCL w.re τ hw hw2 (by rw [abs_of_pos (by linarith)]; exact hτ)
    rw [abs_of_pos (by linarith)] at h
    have hlogτ : 0 < Real.log τ := Real.log_pos (by linarith)
    have h2 : Real.log τ ≤ 2 * Real.log w.im := by
      rw [← Real.log_rpow (by linarith), Real.rpow_two]
      exact Real.log_le_log (by linarith) (by nlinarith)
    have h3 : Real.log (Real.log τ) ≤ Real.log (2 * Real.log w.im) := Real.log_le_log hlogτ h2
    linarith [le_abs_self CL]
  have hb0 : ‖RHTower.zetaEulerLog w‖ ≤ 9 * Real.log (2 * Real.log w.im) + |CL| := by
    have := hℓ w.im (by linarith) (by linarith)
    rwa [Complex.re_add_im] at this
  have hk : ∀ k, ‖B k / 2 * RHTower.zetaEulerLog (w - t k * I) +
      starRingEnd ℂ (B k) / 2 * RHTower.zetaEulerLog (w + t k * I)‖ ≤
        ‖B k‖ * (9 * Real.log (2 * Real.log w.im) + |CL|) := by
    intro k
    have hm : ‖RHTower.zetaEulerLog (w - t k * I)‖ ≤ 9 * Real.log (2 * Real.log w.im) + |CL| := by
      have := hℓ (w.im - t k) (by linarith [htk k]) (by linarith [ht k])
      rwa [show (w.re : ℂ) + ((w.im - t k : ℝ) : ℂ) * I = w - t k * I by
        apply Complex.ext <;> simp] at this
    have hp : ‖RHTower.zetaEulerLog (w + t k * I)‖ ≤ 9 * Real.log (2 * Real.log w.im) + |CL| := by
      have := hℓ (w.im + t k) (by linarith [ht k]) (by linarith [htk k])
      rwa [show (w.re : ℂ) + ((w.im + t k : ℝ) : ℂ) * I = w + t k * I by
        apply Complex.ext <;> simp] at this
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_div, norm_div, Complex.norm_conj, Complex.norm_two]
    have hb := norm_nonneg (B k)
    nlinarith [mul_le_mul_of_nonneg_left hm hb, mul_le_mul_of_nonneg_left hp hb]
  have hph : (spectralEulerPhase c₀ t B w).re ≤ N * (9 * Real.log (2 * Real.log w.im) + |CL|) := by
    have h0 : ‖(c₀ : ℂ) * RHTower.zetaEulerLog w‖ ≤
        |c₀| * (9 * Real.log (2 * Real.log w.im) + |CL|) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hb0 (abs_nonneg _)
    unfold spectralEulerPhase
    refine (Complex.re_le_norm _).trans ((norm_add_le _ _).trans ?_)
    calc _ ≤ |c₀| * (9 * Real.log (2 * Real.log w.im) + |CL|) +
          ∑ k, ‖B k‖ * (9 * Real.log (2 * Real.log w.im) + |CL|) :=
          add_le_add h0 ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hk k))
      _ = N * (9 * Real.log (2 * Real.log w.im) + |CL|) := by rw [hN, add_mul, Finset.sum_mul]
  have hEc := (abs_le.mp (abs_log_norm_spectralSeries_sub_le hg hw)).2
  rw [← hE] at hEc
  have hF0 := norm_pos_iff.mpr (spectralSeries_ne_zero hg hw)
  have hM9 : 9 * N ≤ M := by rw [hM_def]; exact Nat.le_ceil _
  have hlog : Real.log ‖spectralSeries c₀ t B w‖ ≤
      E + N * |CL| + M * Real.log (2 * Real.log w.im) := by
    have h9 : 9 * N * Real.log (2 * Real.log w.im) ≤ M * Real.log (2 * Real.log w.im) :=
      mul_le_mul_of_nonneg_right hM9 hX
    have h10 : N * (9 * Real.log (2 * Real.log w.im) + |CL|) =
        9 * N * Real.log (2 * Real.log w.im) + N * |CL| := by ring
    linarith
  have hq := log_pow_le_rpow_quarter (show 1 ≤ w.im by linarith) M
  calc ‖spectralSeries c₀ t B w‖ = Real.exp (Real.log ‖spectralSeries c₀ t B w‖) :=
        (Real.exp_log hF0).symm
    _ ≤ Real.exp (E + N * |CL| + M * Real.log (2 * Real.log w.im)) := Real.exp_le_exp.mpr hlog
    _ = Real.exp (E + N * |CL|) * (2 * Real.log w.im) ^ M := by
        rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by linarith)]
    _ = Real.exp (E + N * |CL|) * 2 ^ M * Real.log w.im ^ M := by ring
    _ ≤ Real.exp (E + N * |CL|) * 2 ^ M * ((4 * ((M : ℝ) + 1)) ^ M * w.im ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := by ring

/-- The heights whose singularity no critical zero cancels: the mean height `0`, and every `t_k`
with `ζ(1/2 + it_k) ≠ 0`. -/
noncomputable def spectralUncancelled (t : Fin K → ℝ) : Finset (Option (Fin K)) := by
  classical
  exact Finset.univ.filter fun j =>
    ¬ (j.elim False fun k => riemannZeta (1 / 2 + (t k : ℂ) * I) = 0)

/-- **The upper factorization on the box.** On `1 < Re w ≤ 2`, `0 < Im w ≤ T` the distances to
the heights are at most `D` and `|F(w)|² ≤ R (1 + Σ_j Y_j²)`,
`Y_j = exp(e_j⁺ max(0, −log|w − 1 − iη_j|))`: at most one height is near `w`. -/
theorem exists_sq_norm_spectralSeries_le {c₀ : ℝ} {t : Fin K → ℝ} {B : Fin K → ℂ}
    (hg : ∀ x, |spectralProfile c₀ t B x| ≤ 1) (ht : ∀ k, 0 < t k)
    (hinj : Function.Injective t) (T : ℝ) :
    ∃ R D : ℝ, 0 ≤ R ∧ 1 ≤ D ∧ ∀ w : ℂ, 1 < w.re → w.re ≤ 2 → 0 < w.im → w.im ≤ T →
      (∀ j, ‖w - 1 - spectralHeight t j * I‖ ≤ D) ∧
      ‖spectralSeries c₀ t B w‖ ^ 2 ≤ R * (1 + ∑ j, Real.exp (max (spectralExponent c₀ B j) 0 *
        max 0 (-Real.log ‖w - 1 - spectralHeight t j * I‖)) ^ 2) := by
  obtain ⟨δ, hδ, hδ1, hsep⟩ := exists_two_mul_le_abs_sub (spectralHeight_injective ht hinj)
  have hηm := spectralHeight_mem ht
  obtain ⟨St, hSt⟩ : ∃ St : ℝ, St = ∑ k, t k := ⟨_, rfl⟩
  have hSt0 : 0 ≤ St := by rw [hSt]; exact Finset.sum_nonneg fun k _ => (ht k).le
  have hηSt : ∀ j, spectralHeight t j ≤ St := fun j => by rw [hSt]; exact (hηm j).2
  have htδ : ∀ k, 2 * δ ≤ t k := fun k => by
    have h := hsep (some k) none (Option.some_ne_none k)
    simp only [spectralHeight, Option.elim, sub_zero, abs_of_pos (ht k)] at h
    exact h
  obtain ⟨D, hD_def⟩ : ∃ D : ℝ, D = 2 + |T| + St := ⟨_, rfl⟩
  have hD1 : 1 ≤ D := by rw [hD_def]; linarith [abs_nonneg T]
  obtain ⟨C₁, hC₁⟩ := exists_abs_log_norm_spectralSeries_sub_le hg T
  obtain ⟨lam, hlam_def⟩ : ∃ lam : ℝ, lam = -Real.log δ := ⟨_, rfl⟩
  have hlam : 0 ≤ lam := by rw [hlam_def]; exact neg_nonneg.mpr (Real.log_nonpos hδ.le hδ1)
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = (∑ j, |spectralExponent c₀ B j|) * Real.log D +
      (∑ k, |(B k).re / 2|) * (|Real.log δ| + |Real.log D|) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ,
      Q = Real.exp (C₁ + C₂ + (∑ j, max (spectralExponent c₀ B j) 0) * lam) := ⟨_, rfl⟩
  refine ⟨Q ^ 2 * (2 * ((K : ℝ) + 1)), D, by positivity, hD1,
    fun w hw1 hw2 hτ hτT => ?_⟩
  have hwT : |w.im| ≤ T := by rw [abs_of_pos hτ]; exact hτT
  have hdre : ∀ η : ℝ, (w - 1 - (η : ℂ) * I).re = w.re - 1 := fun η => by simp
  have hdim : ∀ η : ℝ, (w - 1 - (η : ℂ) * I).im = w.im - η := fun η => by simp
  have hd0 : ∀ j, 0 < ‖w - 1 - spectralHeight t j * I‖ := fun j => by
    have := Complex.abs_re_le_norm (w - 1 - spectralHeight t j * I)
    rw [hdre, abs_of_pos (by linarith)] at this
    linarith
  have hdτ : ∀ j, |w.im - spectralHeight t j| ≤ ‖w - 1 - spectralHeight t j * I‖ := fun j => by
    have := Complex.abs_im_le_norm (w - 1 - spectralHeight t j * I)
    rwa [hdim] at this
  have hdD : ∀ j, ‖w - 1 - spectralHeight t j * I‖ ≤ D := fun j => by
    have h := Complex.norm_le_abs_re_add_abs_im (w - 1 - spectralHeight t j * I)
    rw [hdre, hdim, abs_of_pos (by linarith)] at h
    have h' : |w.im - spectralHeight t j| ≤ |T| + St := (abs_sub _ _).trans (by
      rw [abs_of_pos hτ, abs_of_nonneg (hηm j).1]
      linarith [hηSt j, le_abs_self T])
    rw [hD_def]
    linarith
  have hdp : ∀ k, δ ≤ ‖w + t k * I - 1‖ ∧ ‖w + t k * I - 1‖ ≤ D := fun k => by
    have hre' : (w + t k * I - 1).re = w.re - 1 := by simp
    have him' : (w + t k * I - 1).im = w.im + t k := by simp
    constructor
    · have h := Complex.abs_im_le_norm (w + t k * I - 1)
      rw [him', abs_of_pos (by linarith [ht k])] at h
      linarith [htδ k]
    · have h := Complex.norm_le_abs_re_add_abs_im (w + t k * I - 1)
      rw [hre', him', abs_of_pos (by linarith), abs_of_pos (by linarith [ht k])] at h
      rw [hD_def]
      linarith [hηSt (some k), le_abs_self T]
  refine ⟨hdD, ?_⟩
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = ∑ j, max (spectralExponent c₀ B j) 0 *
      max 0 (-Real.log ‖w - 1 - spectralHeight t j * I‖) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Option (Fin K) → ℝ, Y = fun j => Real.exp
      (max (spectralExponent c₀ B j) 0 * max 0 (-Real.log ‖w - 1 - spectralHeight t j * I‖)) :=
    ⟨_, rfl⟩
  have hYsum2 : ∑ j, Real.exp (max (spectralExponent c₀ B j) 0 *
      max 0 (-Real.log ‖w - 1 - spectralHeight t j * I‖)) ^ 2 = ∑ j, Y j ^ 2 := by rw [hY]
  rw [hYsum2]
  have hFac := spectralLogFactor_le (c₀ := c₀) (B := B) hδ hD1 (fun j => ⟨hd0 j, hdD j⟩) hdp
  rw [← hC₂, ← hΛ] at hFac
  have hloc := (abs_le.mp (hC₁ w hw1 hw2 hwT)).2
  -- at most one height is within `δ`
  have huniq : ∀ i j, lam < max 0 (-Real.log ‖w - 1 - spectralHeight t i * I‖) →
      lam < max 0 (-Real.log ‖w - 1 - spectralHeight t j * I‖) → i = j := by
    intro i j hi hj
    rw [hlam_def] at hi hj
    have hi' := lt_of_neg_log_lt_max hδ hδ1 hi
    have hj' := lt_of_neg_log_lt_max hδ hδ1 hj
    by_contra hij
    have h := hsep i j hij
    have h1 := hdτ i
    have h2 := hdτ j
    have h3 : |spectralHeight t i - spectralHeight t j| ≤
        |w.im - spectralHeight t i| + |w.im - spectralHeight t j| := by
      calc |spectralHeight t i - spectralHeight t j|
          = |(w.im - spectralHeight t j) - (w.im - spectralHeight t i)| := by ring_nf
        _ ≤ |w.im - spectralHeight t j| + |w.im - spectralHeight t i| := abs_sub _ _
        _ = _ := add_comm _ _
    linarith
  have hexp := exp_sum_le_of_unique_large (a := fun j => max (spectralExponent c₀ B j) 0)
    (ℓ := fun j => max 0 (-Real.log ‖w - 1 - spectralHeight t j * I‖))
    (fun j => le_max_right _ _) hlam huniq
  beta_reduce at hexp
  have hYsum : ∑ j, Real.exp (max (spectralExponent c₀ B j) 0 *
      max 0 (-Real.log ‖w - 1 - spectralHeight t j * I‖)) = ∑ j, Y j := by rw [hY]
  rw [← hΛ, hYsum] at hexp
  have hF0 := norm_pos_iff.mpr (spectralSeries_ne_zero hg hw1)
  have hFle : ‖spectralSeries c₀ t B w‖ ≤ Q * (1 + ∑ j, Y j) := by
    have hlog : Real.log ‖spectralSeries c₀ t B w‖ ≤ C₁ + C₂ + Λ := by linarith
    calc ‖spectralSeries c₀ t B w‖ = Real.exp (Real.log ‖spectralSeries c₀ t B w‖) :=
          (Real.exp_log hF0).symm
      _ ≤ Real.exp (C₁ + C₂ + Λ) := Real.exp_le_exp.mpr hlog
      _ = Real.exp (C₁ + C₂) * Real.exp Λ := Real.exp_add _ _
      _ ≤ Real.exp (C₁ + C₂) * (Real.exp ((∑ j, max (spectralExponent c₀ B j) 0) * lam) *
            (1 + ∑ j, Y j)) := mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
      _ = Q * (1 + ∑ j, Y j) := by rw [hQ, Real.exp_add (C₁ + C₂)]; ring
  -- Cauchy–Schwarz over the `K + 1` heights
  have hY0 : ∀ j, 0 ≤ Y j := fun j => by rw [hY]; exact (Real.exp_pos _).le
  have hCS : (∑ j, Y j) ^ 2 ≤ ((K : ℝ) + 1) * ∑ j, Y j ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Option (Fin K)))) (f := Y)
    rwa [Finset.card_univ, Fintype.card_option, Fintype.card_fin, Nat.cast_add,
      Nat.cast_one] at h
  have hS0 : 0 ≤ ∑ j, Y j := Finset.sum_nonneg fun j _ => hY0 j
  have hY2 : 0 ≤ ∑ j, Y j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h2 : (1 + ∑ j, Y j) ^ 2 ≤ 2 * ((K : ℝ) + 1) * (1 + ∑ j, Y j ^ 2) := by
    have e1 : 2 * ((K : ℝ) + 1) * (1 + ∑ j, Y j ^ 2) =
        2 * ((K : ℝ) + 1) + 2 * (((K : ℝ) + 1) * ∑ j, Y j ^ 2) := by ring
    linarith [sq_nonneg (1 - ∑ j, Y j)]
  calc ‖spectralSeries c₀ t B w‖ ^ 2 ≤ (Q * (1 + ∑ j, Y j)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hFle 2
    _ = Q ^ 2 * (1 + ∑ j, Y j) ^ 2 := by ring
    _ ≤ Q ^ 2 * (2 * ((K : ℝ) + 1) * (1 + ∑ j, Y j ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = _ := by ring

/-- **The pointwise majorant.** On `1/2 < σ < 3/4`, `0 < τ ≤ T`, `τ` off the heights: each
uncancelled height contributes `|τ − η_j|^{-2e_j⁺}`, each height at a critical zero is cancelled by
`|ζ(s)| ≤ L|s − s_k|` (using `Re B_k ≤ 2`). -/
theorem lineIntegrand_spectralWeight_le {c₀ : ℝ} {t : Fin K → ℝ} {B : Fin K → ℂ}
    (hg : ∀ x, |spectralProfile c₀ t B x| ≤ 1) (ht : ∀ k, 0 < t k)
    (hinj : Function.Injective t) {T R D Z₀ : ℝ} {L : Fin K → ℝ} (hR0 : 0 ≤ R) (hD1 : 1 ≤ D)
    (hbox : ∀ w : ℂ, 1 < w.re → w.re ≤ 2 → 0 < w.im → w.im ≤ T →
      (∀ j, ‖w - 1 - spectralHeight t j * I‖ ≤ D) ∧
      ‖spectralSeries c₀ t B w‖ ^ 2 ≤ R * (1 + ∑ j, Real.exp (max (spectralExponent c₀ B j) 0 *
        max 0 (-Real.log ‖w - 1 - spectralHeight t j * I‖)) ^ 2))
    (hZ : ∀ σ τ : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 4 → |τ| ≤ T → ‖riemannZeta ((σ : ℂ) + τ * I)‖ ≤ Z₀)
    (hL0 : ∀ k, 0 ≤ L k)
    (hL : ∀ k, riemannZeta (1 / 2 + (t k : ℂ) * I) = 0 → ∀ σ τ : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 4 →
      |τ| ≤ T → ‖riemannZeta ((σ : ℂ) + τ * I)‖ ≤
        L k * ‖(σ : ℂ) + τ * I - (1 / 2 + (t k : ℂ) * I)‖)
    {P σ τ : ℝ} (hσ : 1 / 2 < σ) (hσ' : σ < 3 / 4) (hτ : 0 < τ) (hτT : τ ≤ T)
    (hτS : τ ∉ Set.range (spectralHeight t)) :
    lineIntegrand (spectralWeight c₀ t B) P σ τ ≤
      4 * (2 * (R * (Z₀ ^ 2 + (Z₀ ^ 2 + (∑ k, L k) ^ 2 * D ^ 2) * ((K : ℝ) + 1))) +
        2 * (Z₀ ^ 2 * P ^ 2)) + 4 * (2 * (R * (Z₀ ^ 2 + (∑ k, L k) ^ 2 * D ^ 2))) *
          ∑ j ∈ spectralUncancelled t,
            |τ - spectralHeight t j| ^ (-(2 * max (spectralExponent c₀ B j) 0)) := by
  classical
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℝ, M₀ = Z₀ ^ 2 + (∑ k, L k) ^ 2 * D ^ 2 := ⟨_, rfl⟩
  rw [← hM₀]
  have hM₀Z : Z₀ ^ 2 ≤ M₀ := by
    have := mul_nonneg (sq_nonneg (∑ k, L k)) (sq_nonneg D)
    rw [hM₀]; linarith
  obtain ⟨w, hw_def⟩ : ∃ w : ℂ, w = (σ : ℂ) + τ * I + 1 / 2 := ⟨_, rfl⟩
  have hwre : w.re = σ + 1 / 2 := by rw [hw_def]; simp
  have hwim : w.im = τ := by rw [hw_def]; simp
  obtain ⟨hdD, hF2⟩ := hbox w (by rw [hwre]; linarith) (by rw [hwre]; linarith)
    (by rw [hwim]; exact hτ) (by rw [hwim]; exact hτT)
  obtain ⟨Y, hY⟩ : ∃ Y : Option (Fin K) → ℝ, Y = fun j => Real.exp
      (max (spectralExponent c₀ B j) 0 * max 0 (-Real.log ‖w - 1 - spectralHeight t j * I‖)) :=
    ⟨_, rfl⟩
  have hYsum2 : ∑ j, Real.exp (max (spectralExponent c₀ B j) 0 *
      max 0 (-Real.log ‖w - 1 - spectralHeight t j * I‖)) ^ 2 = ∑ j, Y j ^ 2 := by rw [hY]
  rw [hYsum2] at hF2
  have hd0 : ∀ j, 0 < ‖w - 1 - spectralHeight t j * I‖ := fun j => by
    have := Complex.abs_re_le_norm (w - 1 - spectralHeight t j * I)
    have hre : (w - 1 - spectralHeight t j * I).re = σ - 1 / 2 := by
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, hwre]
      ring
    rw [hre, abs_of_pos (by linarith)] at this
    linarith
  have hdτ : ∀ j, |τ - spectralHeight t j| ≤ ‖w - 1 - spectralHeight t j * I‖ := fun j => by
    have := Complex.abs_im_le_norm (w - 1 - spectralHeight t j * I)
    have him : (w - 1 - spectralHeight t j * I).im = τ - spectralHeight t j := by
      simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, hwim]
      ring
    rwa [him] at this
  have hζ0 : ‖riemannZeta ((σ : ℂ) + τ * I)‖ ≤ Z₀ :=
    hZ σ τ hσ.le hσ'.le (by rw [abs_of_pos hτ]; exact hτT)
  have hz2 : ‖riemannZeta ((σ : ℂ) + τ * I)‖ ^ 2 ≤ Z₀ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hζ0 2
  -- each height: integrable, or cancelled by a critical zero
  have hj : ∀ j, ‖riemannZeta ((σ : ℂ) + τ * I)‖ ^ 2 * Y j ^ 2 ≤
      M₀ * (1 + if j ∈ spectralUncancelled t then
        |τ - spectralHeight t j| ^ (-(2 * max (spectralExponent c₀ B j) 0)) else 0) := by
    intro j
    by_cases hjb : j ∈ spectralUncancelled t
    · rw [if_pos hjb]
      have hx : 0 < |τ - spectralHeight t j| :=
        abs_pos.mpr (sub_ne_zero.mpr fun h => hτS ⟨j, h.symm⟩)
      have hx0 := Real.rpow_nonneg (abs_nonneg (τ - spectralHeight t j))
        (-(2 * max (spectralExponent c₀ B j) 0))
      have hYj : Y j ^ 2 ≤ 1 + |τ - spectralHeight t j| ^
          (-(2 * max (spectralExponent c₀ B j) 0)) := by
        rw [hY]; exact exp_mul_sq_le (le_max_right _ _) hx (hdτ j)
      calc _ ≤ Z₀ ^ 2 * (1 + |τ - spectralHeight t j| ^
            (-(2 * max (spectralExponent c₀ B j) 0))) :=
            mul_le_mul hz2 hYj (sq_nonneg _) (sq_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_right hM₀Z (by linarith)
    · rw [if_neg hjb, add_zero, mul_one]
      have hgood : (j.elim False fun k => riemannZeta (1 / 2 + (t k : ℂ) * I) = 0) := by
        by_contra h
        exact hjb (by
          unfold spectralUncancelled
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      cases j with
      | none => exact (hgood : False).elim
      | some k =>
        have hz : riemannZeta (1 / 2 + (t k : ℂ) * I) = 0 := hgood
        have hcap : max (spectralExponent c₀ B (some k)) 0 ≤ 1 :=
          max_le (by
            show (B k).re / 2 ≤ 1
            linarith [spectralAmplitude_re_le_two hg ht hinj k]) zero_le_one
        have hζk := hL k hz σ τ hσ.le hσ'.le (by rw [abs_of_pos hτ]; exact hτT)
        have hds : (σ : ℂ) + τ * I - (1 / 2 + (t k : ℂ) * I) =
            w - 1 - spectralHeight t (some k) * I := by
          rw [hw_def]; simp only [spectralHeight, Option.elim]; ring
        rw [hds] at hζk
        have hLk : L k ≤ ∑ i, L i := Finset.single_le_sum (fun i _ => hL0 i) (Finset.mem_univ k)
        have hYk : ‖w - 1 - spectralHeight t (some k) * I‖ ^ 2 * Y (some k) ^ 2 ≤ D ^ 2 := by
          rw [hY]; exact sq_mul_exp_sq_le hcap (hd0 (some k)) (hdD (some k)) hD1
        have hzk : ‖riemannZeta ((σ : ℂ) + τ * I)‖ ^ 2 ≤
            L k ^ 2 * ‖w - 1 - spectralHeight t (some k) * I‖ ^ 2 := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hζk 2
        have hL2 : L k ^ 2 ≤ (∑ i, L i) ^ 2 := pow_le_pow_left₀ (hL0 k) hLk 2
        calc ‖riemannZeta ((σ : ℂ) + τ * I)‖ ^ 2 * Y (some k) ^ 2
            ≤ L k ^ 2 * ‖w - 1 - spectralHeight t (some k) * I‖ ^ 2 * Y (some k) ^ 2 :=
              mul_le_mul_of_nonneg_right hzk (sq_nonneg _)
          _ = L k ^ 2 * (‖w - 1 - spectralHeight t (some k) * I‖ ^ 2 * Y (some k) ^ 2) := by
              ring
          _ ≤ L k ^ 2 * D ^ 2 := mul_le_mul_of_nonneg_left hYk (sq_nonneg _)
          _ ≤ (∑ i, L i) ^ 2 * D ^ 2 := mul_le_mul_of_nonneg_right hL2 (sq_nonneg _)
          _ ≤ M₀ := by rw [hM₀]; linarith [sq_nonneg Z₀]
  have hsumj : ∑ j, ‖riemannZeta ((σ : ℂ) + τ * I)‖ ^ 2 * Y j ^ 2 ≤
      M₀ * ((K : ℝ) + 1) + M₀ * ∑ j ∈ spectralUncancelled t,
        |τ - spectralHeight t j| ^ (-(2 * max (spectralExponent c₀ B j) 0)) := by
    refine (Finset.sum_le_sum fun j _ => hj j).trans (le_of_eq ?_)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_option, Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_mem,
      Finset.univ_inter]
    push_cast
    ring
  -- assemble
  have hCP : ‖spectralSeries c₀ t B w - (P : ℂ)‖ ^ 2 ≤
      2 * ‖spectralSeries c₀ t B w‖ ^ 2 + 2 * P ^ 2 := by
    have h := norm_sub_le (spectralSeries c₀ t B w) (P : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at h
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    linarith [sq_abs P, sq_nonneg (‖spectralSeries c₀ t B w‖ - |P|)]
  have hZs := sq_nonneg ‖riemannZeta ((σ : ℂ) + τ * I)‖
  have h1 : ‖riemannZeta ((σ : ℂ) + τ * I)‖ ^ 2 * ‖spectralSeries c₀ t B w‖ ^ 2 ≤
      R * (Z₀ ^ 2 + (M₀ * ((K : ℝ) + 1) + M₀ * ∑ j ∈ spectralUncancelled t,
        |τ - spectralHeight t j| ^ (-(2 * max (spectralExponent c₀ B j) 0)))) := by
    calc _ ≤ ‖riemannZeta ((σ : ℂ) + τ * I)‖ ^ 2 * (R * (1 + ∑ j, Y j ^ 2)) :=
          mul_le_mul_of_nonneg_left hF2 hZs
      _ = R * (‖riemannZeta ((σ : ℂ) + τ * I)‖ ^ 2 +
            ∑ j, ‖riemannZeta ((σ : ℂ) + τ * I)‖ ^ 2 * Y j ^ 2) := by
          rw [Finset.mul_sum]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hz2 hsumj) hR0
  have h2 : ‖riemannZeta ((σ : ℂ) + τ * I)‖ ^ 2 * P ^ 2 ≤ Z₀ ^ 2 * P ^ 2 :=
    mul_le_mul_of_nonneg_right hz2 (sq_nonneg _)
  have h3 := mul_le_mul_of_nonneg_left hCP hZs
  have hs2 : (1 / 2 : ℝ) ^ 2 ≤ ‖(σ : ℂ) + τ * I‖ ^ 2 := by
    have hsn : σ ≤ ‖(σ : ℂ) + τ * I‖ := by
      have := Complex.abs_re_le_norm ((σ : ℂ) + τ * I)
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero] at this
      linarith [le_abs_self σ]
    exact pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have hden : 0 < ‖(σ : ℂ) + τ * I‖ ^ 2 := lt_of_lt_of_le (by norm_num) hs2
  simp only [lineIntegrand, norm_div, norm_mul, div_pow, mul_pow]
  rw [weightDirichletSeries_spectralWeight, ← hw_def, div_le_iff₀ hden]
  have hmain : ‖riemannZeta ((σ : ℂ) + τ * I)‖ ^ 2 *
      ‖spectralSeries c₀ t B w - (P : ℂ)‖ ^ 2 * 4 ≤
        4 * (2 * (R * (Z₀ ^ 2 + M₀ * ((K : ℝ) + 1))) + 2 * (Z₀ ^ 2 * P ^ 2)) +
          4 * (2 * (R * M₀)) * ∑ j ∈ spectralUncancelled t,
            |τ - spectralHeight t j| ^ (-(2 * max (spectralExponent c₀ B j) 0)) := by
    linarith
  have hG0 := mul_nonneg (mul_nonneg hZs (sq_nonneg ‖spectralSeries c₀ t B w - (P : ℂ)‖))
    (show (0 : ℝ) ≤ 4 by norm_num)
  nlinarith

/-- **The paid range.** If `c₀ < 1/2` and at every frequency `Re B_k < 1` or
`ζ(1/2 + it_k) = 0`, the half-damped spectral weight is paid. -/
theorem receiverBounded_spectralWeight_of {c₀ : ℝ} {t : Fin K → ℝ} {B : Fin K → ℂ}
    (hg : ∀ x, |spectralProfile c₀ t B x| ≤ 1) (ht : ∀ k, 0 < t k)
    (hinj : Function.Injective t) (hc₀ : c₀ < 1 / 2)
    (hB : ∀ k, (B k).re < 1 ∨ riemannZeta (1 / 2 + (t k : ℂ) * I) = 0) :
    ReceiverBounded (spectralWeight c₀ t B) := by
  obtain ⟨St, hSt⟩ : ∃ St : ℝ, St = ∑ k, t k := ⟨_, rfl⟩
  have hSt0 : 0 ≤ St := by rw [hSt]; exact Finset.sum_nonneg fun k _ => (ht k).le
  obtain ⟨T, hT_def⟩ : ∃ T : ℝ, T = 2 * St + 18 := ⟨_, rfl⟩
  have hT : 2 ≤ T := by rw [hT_def]; linarith
  obtain ⟨R, D, hR0, hD1, hbox⟩ := exists_sq_norm_spectralSeries_le hg ht hinj T
  -- Lipschitz constants at the critical zeros
  have hLip : ∀ k, ∃ L : ℝ, 0 ≤ L ∧ (riemannZeta (1 / 2 + (t k : ℂ) * I) = 0 →
      ∀ σ τ : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 4 → |τ| ≤ T →
        ‖riemannZeta ((σ : ℂ) + τ * I)‖ ≤
          L * ‖(σ : ℂ) + τ * I - (1 / 2 + (t k : ℂ) * I)‖) := by
    intro k
    by_cases hz : riemannZeta (1 / 2 + (t k : ℂ) * I) = 0
    · obtain ⟨L, hL0, hL⟩ := exists_norm_zeta_le_mul_of_zero (s₀ := 1 / 2 + (t k : ℂ) * I)
        (by intro h; have := congrArg Complex.re h; norm_num at this) hz T
      exact ⟨L, hL0, fun _ => hL⟩
    · exact ⟨0, le_rfl, fun h => absurd h hz⟩
  choose L hL0 hL using hLip
  obtain ⟨Z₀, -, hZ⟩ := exists_norm_zeta_le_on_tall_box T
  set P : ℝ := ∑' d : ℕ, spectralWeight c₀ t B d / d
  have hbad : ∀ j ∈ spectralUncancelled t, 2 * max (spectralExponent c₀ B j) 0 < 1 := by
    intro j hj
    unfold spectralUncancelled at hj
    have hj' := (Finset.mem_filter.mp hj).2
    cases j with
    | none =>
      show 2 * max c₀ 0 < 1
      have := max_lt hc₀ (by norm_num : (0 : ℝ) < 1 / 2)
      linarith
    | some k =>
      have hz : riemannZeta (1 / 2 + (t k : ℂ) * I) ≠ 0 := hj'
      have hk := (hB k).resolve_right hz
      show 2 * max ((B k).re / 2) 0 < 1
      have := max_lt (by linarith : (B k).re / 2 < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
      linarith
  obtain ⟨A₁, hA₁⟩ : ∃ A₁ : ℝ, A₁ = 4 * (2 * (R * (Z₀ ^ 2 + (Z₀ ^ 2 + (∑ k, L k) ^ 2 * D ^ 2) *
      ((K : ℝ) + 1))) + 2 * (Z₀ ^ 2 * P ^ 2)) := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A₂ : ℝ, A₂ = 4 * (2 * (R * (Z₀ ^ 2 + (∑ k, L k) ^ 2 * D ^ 2))) :=
    ⟨_, rfl⟩
  have hGi : IntegrableOn (fun τ => A₁ + A₂ * ∑ j ∈ spectralUncancelled t,
      |τ - spectralHeight t j| ^ (-(2 * max (spectralExponent c₀ B j) 0))) (Ioc 0 T) := by
    have hc : IntegrableOn (fun _ : ℝ => A₁) (Ioc 0 T) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp intervalIntegrable_const
    have hs : IntegrableOn (fun τ : ℝ => ∑ j ∈ spectralUncancelled t,
        |τ - spectralHeight t j| ^ (-(2 * max (spectralExponent c₀ B j) 0))) (Ioc 0 T) :=
      integrable_finsetSum _ fun j hj =>
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
          (intervalIntegrable_abs_sub_rpow (by linarith [hbad j hj]) _ 0 T)
    exact hc.add (hs.const_mul A₂)
  have hsmall : ∀ σ τ : ℝ, 1 / 2 < σ → σ < 3 / 4 → 0 < τ → τ ≤ T →
      τ ∉ Set.range (spectralHeight t) → lineIntegrand (spectralWeight c₀ t B) P σ τ ≤
        A₁ + A₂ * ∑ j ∈ spectralUncancelled t,
          |τ - spectralHeight t j| ^ (-(2 * max (spectralExponent c₀ B j) 0)) :=
    fun σ τ hσ hσ' hτ hτT hτS => by
      rw [hA₁, hA₂]
      exact lineIntegrand_spectralWeight_le hg ht hinj hR0 hD1 hbox hZ hL0 hL hσ hσ' hτ hτT hτS
  -- large heights
  obtain ⟨B₁, hB₁⟩ := exists_norm_spectralSeries_le_large hg ht
  have hlarge : ∀ σ τ : ℝ, 1 / 2 < σ → σ < 3 / 4 → T < τ →
      ‖weightDirichletSeries (spectralWeight c₀ t B) ((σ : ℂ) + τ * I) - (P : ℂ)‖ ≤
        (|B₁| + |P|) * τ ^ (1 / 4 : ℝ) := by
    intro σ τ hσ hσ' hτ
    have hwre : ((σ : ℂ) + τ * I + 1 / 2).re = σ + 1 / 2 := by simp
    have hwim : ((σ : ℂ) + τ * I + 1 / 2).im = τ := by simp
    have hF := hB₁ ((σ : ℂ) + τ * I + 1 / 2) (by rw [hwre]; linarith) (by rw [hwre]; linarith)
      (by rw [hwim, ← hSt, ← hT_def]; exact hτ)
    rw [hwim] at hF
    rw [weightDirichletSeries_spectralWeight]
    refine (norm_sub_le _ _).trans ?_
    have h1 : 1 ≤ τ ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    rw [Complex.norm_real, Real.norm_eq_abs]
    nlinarith [le_abs_self B₁, abs_nonneg P, abs_nonneg B₁,
      mul_le_mul_of_nonneg_right (le_abs_self B₁) (by positivity : (0 : ℝ) ≤ τ ^ (1 / 4 : ℝ))]
  obtain ⟨M, hM⟩ := exists_lineEnergy_le_of_majorant_off_countable
    (Set.finite_range (spectralHeight t)).countable hT hGi hsmall hlarge
  exact ⟨3 * M / (4 * Real.pi), weightPronicEnergy_le_of_lineEnergy_le
    (dampedClass_spectralWeight hg) hM⟩

/-! ### The spectral law -/

/-- **The spectral law of finite-frequency prime patterns.** For `g(x) = c₀ + Σ_k Re(B_k e^{it_k x})`
with distinct `t_k > 0` and `|g| ≤ 1`, the half-damped weight of `f(p) = g(log p)` is paid iff
`c₀ < 1/2` and, at every frequency, `Re B_k < 1` or `ζ(1/2 + it_k) = 0`. -/
theorem receiverBounded_spectralWeight_iff {c₀ : ℝ} {t : Fin K → ℝ} {B : Fin K → ℂ}
    (hg : ∀ x, |spectralProfile c₀ t B x| ≤ 1) (ht : ∀ k, 0 < t k)
    (hinj : Function.Injective t) :
    ReceiverBounded (spectralWeight c₀ t B) ↔
      c₀ < 1 / 2 ∧ ∀ k, (B k).re < 1 ∨ riemannZeta (1 / 2 + (t k : ℂ) * I) = 0 := by
  constructor
  · intro hR
    refine ⟨?_, fun k => ?_⟩
    · by_contra h
      push Not at h
      exact not_receiverBounded_spectralWeight_of_half_le hg ht hinj h hR
    · by_contra h
      push Not at h
      exact not_receiverBounded_spectralWeight_of_one_le hg ht hinj h.1 h.2 hR
  · rintro ⟨hc₀, hB⟩
    exact receiverBounded_spectralWeight_of hg ht hinj hc₀ hB

/-- **An amplitude above one.** `g(x) = (9/8) cos x − (1/8) cos 3x = (3 cos x − cos³ x)/2` has
`|g| ≤ 1` and amplitude `9/8` at the base frequency; for `t₀ > 0` the pattern
`f(p) = g(t₀ log p)` is paid at half damping iff `ζ(1/2 + it₀) = 0`. -/
theorem receiverBounded_cubicPattern_iff {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ReceiverBounded (spectralWeight 0 ![t₀, 3 * t₀] ![9 / 8, -(1 / 8)]) ↔
      riemannZeta (1 / 2 + (t₀ : ℂ) * I) = 0 := by
  have hg : ∀ x, |spectralProfile 0 ![t₀, 3 * t₀] ![9 / 8, -(1 / 8)] x| ≤ 1 := by
    intro x
    have hre : ∀ (b : ℝ) (θ : ℝ), ((b : ℂ) * Complex.exp ((θ : ℂ) * I)).re = b * Real.cos θ :=
      fun b θ => by rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    have e1 : ((9 / 8 : ℂ) * Complex.exp (((t₀ * x : ℝ) : ℂ) * I)).re =
        9 / 8 * Real.cos (t₀ * x) := by
      have := hre (9 / 8) (t₀ * x); push_cast at this ⊢; exact this
    have e2 : ((-(1 / 8) : ℂ) * Complex.exp (((3 * t₀ * x : ℝ) : ℂ) * I)).re =
        -(1 / 8) * Real.cos (3 * (t₀ * x)) := by
      have := hre (-(1 / 8)) (3 * (t₀ * x)); push_cast at this ⊢
      rw [show (3 : ℂ) * (t₀ * x) = 3 * t₀ * x by ring] at this; exact this
    simp only [spectralProfile, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      zero_add]
    rw [e1, e2, Real.cos_three_mul]
    have hc := Real.abs_cos_le_one (t₀ * x)
    rw [abs_le] at hc ⊢
    obtain ⟨hc1, hc2⟩ := hc
    constructor <;> nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hc2) (sub_nonneg.mpr hc2))
      (by linarith : (0 : ℝ) ≤ Real.cos (t₀ * x) + 2),
      mul_nonneg (mul_nonneg (neg_le_iff_add_nonneg.mp hc1) (neg_le_iff_add_nonneg.mp hc1))
      (by linarith : (0 : ℝ) ≤ 2 - Real.cos (t₀ * x))]
  have ht : ∀ k, 0 < (![t₀, 3 * t₀] : Fin 2 → ℝ) k := by
    intro k; fin_cases k <;> simp <;> linarith
  have hinj : Function.Injective (![t₀, 3 * t₀] : Fin 2 → ℝ) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> linarith
  rw [receiverBounded_spectralWeight_iff hg ht hinj, Fin.forall_fin_two]
  norm_num
end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
