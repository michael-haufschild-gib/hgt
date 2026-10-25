import GaloisForLFunctions.TransHorizonIncidenceMechanics.ThePhaseLawOfOscillatingPrimePatterns

/-!
# The Dini law of completely monotone amplitude defects

Fix `t₀ > 0`, weights `w_k ≥ 0` with `W = Σ w_k < ∞`, exponents `0 < s_k ≤ 1/2`, and `c ≥ 0` with
`cW ≤ 2`. The completely monotone defect `g(x) = Σ_k w_k x^{-s_k}` (`cmDefect`) lowers the amplitude
of the boundary pattern `cos(t₀ log p)`:

`f(p) = (1 − c g(p)) cos(t₀ log p)`  (`defectPattern`).

Since `g(p) p^{-w} = Σ_k w_k p^{-(w + s_k)}`, the Euler product sees `ζ` at the heights `±t₀` and at
the shifted points `w + s_k ± it₀`:

`log|F(w)| = ½(log|ζ(w − it₀)| + log|ζ(w + it₀)|) − (c/2) Σ_k w_k (log|ζ(w + s_k − it₀)| +
  log|ζ(w + s_k + it₀)|) + O(1)`  (`abs_log_norm_defectSeries_sub_le`).

Near the height `t₀`, with `w = 1 + u + i(t₀ + τ)` and `ρ = u + |τ|`, this is
`|F(w)|² ≍ e^{−cΛ(ρ)}/ρ`, where `Λ(ρ) = Σ_k w_k log(1/(s_k + ρ))` is the defect profile
(`defectProfile`).
-/

open Filter Topology MeasureTheory Complex Set
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The defect data and the pattern -/

/-- Admissible defect data: weights `w_k ≥ 0` with `Σ w_k < ∞` and exponents `0 < s_k ≤ 1/2`. -/
structure AdmissibleDefect (w s : ℕ → ℝ) : Prop where
  nonneg : ∀ k, 0 ≤ w k
  summable : Summable w
  pos : ∀ k, 0 < s k
  le_half : ∀ k, s k ≤ 1 / 2

/-- The completely monotone amplitude defect `g(x) = Σ_k w_k x^{-s_k}`. -/
def cmDefect (w s : ℕ → ℝ) (x : ℝ) : ℝ := ∑' k, w k * x ^ (-s k)

/-- The defect profile `Λ(ρ) = Σ_k w_k log(1/(s_k + ρ))`. -/
def defectProfile (w s : ℕ → ℝ) (ρ : ℝ) : ℝ := ∑' k, w k * Real.log (s k + ρ)⁻¹

/-- The boundary pattern with amplitude defect: `f(p) = (1 − c g(p)) cos(t₀ log p)`. -/
def defectPattern (c t₀ : ℝ) (w s : ℕ → ℝ) : ℕ →*₀ ℝ :=
  primeValueHom fun p => (1 - c * cmDefect w s p) * Real.cos (t₀ * Real.log p)

/-- The half-damped weight `f(d) d^{-1/2}` of the defect pattern. -/
def defectWeight (c t₀ : ℝ) (w s : ℕ → ℝ) (d : ℕ) : ℝ :=
  defectPattern c t₀ w s d * (d : ℝ) ^ (-(1 / 2 : ℝ))

variable {w s : ℕ → ℝ}

theorem AdmissibleDefect.summable_mul_rpow (hd : AdmissibleDefect w s) {x : ℝ} (hx : 1 ≤ x) :
    Summable fun k => w k * x ^ (-s k) :=
  hd.summable.of_nonneg_of_le
    (fun k => mul_nonneg (hd.nonneg k) (Real.rpow_nonneg (by linarith) _))
    fun k => mul_le_of_le_one_right (hd.nonneg k)
      (Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith [hd.pos k]))

theorem cmDefect_nonneg (hd : AdmissibleDefect w s) {x : ℝ} (hx : 1 ≤ x) : 0 ≤ cmDefect w s x :=
  tsum_nonneg fun k => mul_nonneg (hd.nonneg k) (Real.rpow_nonneg (by linarith) _)

theorem cmDefect_le (hd : AdmissibleDefect w s) {x : ℝ} (hx : 1 ≤ x) :
    cmDefect w s x ≤ ∑' k, w k :=
  (hd.summable_mul_rpow hx).tsum_le_tsum (fun k => mul_le_of_le_one_right (hd.nonneg k)
    (Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith [hd.pos k]))) hd.summable

theorem defectPattern_prime (c t₀ : ℝ) {p : ℕ} (hp : p.Prime) :
    defectPattern c t₀ w s p = (1 - c * cmDefect w s p) * Real.cos (t₀ * Real.log p) :=
  primeValueHom_prime _ hp

/-- The amplitude `1 − c g(p)` lies in `[−1, 1]`. -/
theorem abs_one_sub_mul_cmDefect_le (hd : AdmissibleDefect w s) {c : ℝ} (hc : 0 ≤ c)
    (hcW : c * ∑' k, w k ≤ 2) {x : ℝ} (hx : 1 ≤ x) : |1 - c * cmDefect w s x| ≤ 1 := by
  have h0 := mul_nonneg hc (cmDefect_nonneg hd hx)
  have h1 := mul_le_mul_of_nonneg_left (cmDefect_le hd hx) hc
  rw [abs_le]; constructor <;> linarith

theorem abs_defectPattern_le (hd : AdmissibleDefect w s) {c : ℝ} (hc : 0 ≤ c)
    (hcW : c * ∑' k, w k ≤ 2) (t₀ : ℝ) (n : ℕ) : |defectPattern c t₀ w s n| ≤ 1 :=
  abs_patternHom_le_one _ (fun p hp => by
    rw [defectPattern_prime c t₀ hp, abs_mul]
    exact mul_le_one₀ (abs_one_sub_mul_cmDefect_le hd hc hcW (by exact_mod_cast hp.one_lt.le))
      (abs_nonneg _) (Real.abs_cos_le_one _)) n

theorem dampedClass_defectWeight (hd : AdmissibleDefect w s) {c : ℝ} (hc : 0 ≤ c)
    (hcW : c * ∑' k, w k ≤ 2) (t₀ : ℝ) : DampedClass 1 (1 / 2) (defectWeight c t₀ w s) :=
  fun d => by
    simp only [defectWeight]
    rw [one_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _)
      (abs_defectPattern_le hd hc hcW t₀ d)

/-! ### The Euler comparison -/

/-- The cosine prime series `Σ_p cos(t₀ log p) p^{-v}`. -/
def cosPrimeSeries (t₀ : ℝ) (v : ℂ) : ℂ :=
  ∑' p : Nat.Primes, ((Real.cos (t₀ * Real.log (p : ℕ)) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-v)

theorem norm_cos_mul_prime_cpow_le (t₀ : ℝ) {v : ℂ} (p : Nat.Primes) :
    ‖((Real.cos (t₀ * Real.log (p : ℕ)) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-v)‖ ≤
      ((p : ℕ) : ℝ) ^ (-v.re) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast p.2.pos), Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.abs_cos_le_one _)

theorem summable_cos_mul_prime_cpow (t₀ : ℝ) {v : ℂ} (hv : 1 < v.re) :
    Summable fun p : Nat.Primes =>
      ((Real.cos (t₀ * Real.log (p : ℕ)) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-v) :=
  (Nat.Primes.summable_rpow.mpr (show -v.re < -1 by linarith)).of_norm_bounded
    fun p => norm_cos_mul_prime_cpow_le t₀ p

/-- `‖Σ_p cos(t₀ log p) p^{-v}‖ ≤ Σ_p p^{-σ}` whenever `1 < σ ≤ Re v`. -/
theorem norm_cosPrimeSeries_le (t₀ : ℝ) {v : ℂ} {σ : ℝ} (hσ : 1 < σ) (hv : σ ≤ v.re) :
    ‖cosPrimeSeries t₀ v‖ ≤ ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ) := by
  have hsσ : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-σ) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  refine (norm_tsum_le_tsum_norm (summable_cos_mul_prime_cpow t₀ (by linarith)).norm).trans
    ((summable_cos_mul_prime_cpow t₀ (by linarith)).norm.tsum_le_tsum (fun p => ?_) hsσ)
  refine (norm_cos_mul_prime_cpow_le t₀ p).trans ?_
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_lt.le) (by linarith)

/-- `Re Σ_p cos(t₀ log p) p^{-v}` is `½(log|ζ(v − it₀)| + log|ζ(v + it₀)|)` up to `S`. -/
theorem abs_re_cosPrimeSeries_sub_le (t₀ : ℝ) {v : ℂ} (hv : 1 < v.re) :
    |(cosPrimeSeries t₀ v).re -
      (Real.log ‖riemannZeta (v - t₀ * I)‖ + Real.log ‖riemannZeta (v + t₀ * I)‖) / 2| ≤
        primeSquareMass := by
  have hvm : 1 < (v - t₀ * I).re := by simpa using hv
  have hvp : 1 < (v + t₀ * I).re := by simpa using hv
  have hsm := summable_prime_cpow_neg hvm
  have hsp := summable_prime_cpow_neg hvp
  have hQ : cosPrimeSeries t₀ v = (∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-(v - t₀ * I)) +
      ∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-(v + t₀ * I))) / 2 := by
    rw [← hsm.tsum_add hsp, ← tsum_div_const]
    exact tsum_congr fun p => cos_mul_cpow_eq p.2.pos t₀ v
  have hζm := abs_log_norm_riemannZeta_sub_re_le hvm
  have hζp := abs_log_norm_riemannZeta_sub_re_le hvp
  rw [hQ, Complex.div_ofNat_re, Complex.add_re]
  set Rm := (∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-(v - t₀ * I))).re
  set Rp := (∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-(v + t₀ * I))).re
  rw [abs_le] at hζm hζp ⊢
  constructor <;> linarith [hζm.1, hζm.2, hζp.1, hζp.2]

/-- **The prime sum of the defect pattern.** On `Re v > 1`,
`Σ_p f(p) p^{-v} = Q(v) − c Σ_k w_k Q(v + s_k)`, `Q(v) = Σ_p cos(t₀ log p) p^{-v}`. -/
theorem tsum_defectPattern_primes (hd : AdmissibleDefect w s) (c t₀ : ℝ) {v : ℂ}
    (hv : 1 < v.re) :
    ∑' p : Nat.Primes, cweightedPatternHom (defectPattern c t₀ w s) v p =
      cosPrimeSeries t₀ v - c * ∑' k, (w k : ℂ) * cosPrimeSeries t₀ (v + s k) := by
  set q : ℂ → Nat.Primes → ℂ := fun v' p =>
    ((Real.cos (t₀ * Real.log (p : ℕ)) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-v')
  have hre : ∀ k, (v + s k).re = v.re + s k := fun k => by simp
  have hsσ : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-v.re) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  have hqk : ∀ (k : ℕ) (p : Nat.Primes), ‖(w k : ℂ) * q (v + s k) p‖ ≤
      ((p : ℕ) : ℝ) ^ (-v.re) * w k := fun k p => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd.nonneg k), mul_comm]
    refine mul_le_mul_of_nonneg_right ((norm_cos_mul_prime_cpow_le t₀ p).trans ?_) (hd.nonneg k)
    rw [hre]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_lt.le)
      (by linarith [hd.pos k])
  have hprod : Summable (Function.uncurry fun (p : Nat.Primes) (k : ℕ) =>
      (w k : ℂ) * q (v + s k) p) := by
    refine (hsσ.mul_of_nonneg hd.summable (fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      hd.nonneg).of_norm_bounded fun x => hqk x.2 x.1
  -- the pointwise identity at each prime
  have hpt : ∀ p : Nat.Primes, cweightedPatternHom (defectPattern c t₀ w s) v p =
      q v p - c * ∑' k, (w k : ℂ) * q (v + s k) p := fun p => by
    have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    have hp0' : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
    have hg : ((cmDefect w s (p : ℕ) : ℝ) : ℂ) * q v p = ∑' k, (w k : ℂ) * q (v + s k) p := by
      rw [cmDefect, Complex.ofReal_tsum, ← tsum_mul_right]
      refine tsum_congr fun k => ?_
      simp only [q]
      rw [Complex.ofReal_mul, Complex.ofReal_cpow hp0'.le, Complex.ofReal_natCast,
        Complex.ofReal_neg]
      have hc : ((p : ℕ) : ℂ) ^ (-(v + (s k : ℂ))) =
          ((p : ℕ) : ℂ) ^ (-(s k : ℂ)) * ((p : ℕ) : ℂ) ^ (-v) := by
        rw [← Complex.cpow_add _ _ hp0]; ring_nf
      rw [hc]; ring
    simp only [cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      Complex.ofReal_natCast, defectPattern_prime c t₀ p.2]
    rw [← hg]
    simp only [q]
    push_cast
    ring
  have hsumk : Summable fun p : Nat.Primes => ∑' k, (w k : ℂ) * q (v + s k) p := hprod.prod
  have hswap : ∑' p : Nat.Primes, ∑' k, (w k : ℂ) * q (v + s k) p =
      ∑' k, (w k : ℂ) * cosPrimeSeries t₀ (v + s k) := by
    rw [← hprod.tsum_comm]
    exact tsum_congr fun k => tsum_mul_left
  rw [tsum_congr hpt, (summable_cos_mul_prime_cpow t₀ hv).tsum_sub (hsumk.mul_left (c : ℂ)),
    tsum_mul_left, hswap]
  rfl

/-- The Euler model of `log|F|`: with `Z = log|ζ|`,
`D(v) = ½(Z(v − it₀) + Z(v + it₀)) − (c/2) Σ_k w_k (Z(v + s_k − it₀) + Z(v + s_k + it₀))`. -/
def defectLogModel (c t₀ : ℝ) (w s : ℕ → ℝ) (v : ℂ) : ℝ :=
  (Real.log ‖riemannZeta (v - t₀ * I)‖ + Real.log ‖riemannZeta (v + t₀ * I)‖) / 2 -
    c / 2 * ∑' k, w k * (Real.log ‖riemannZeta (v + s k - t₀ * I)‖ +
      Real.log ‖riemannZeta (v + s k + t₀ * I)‖)

/-- Weighted sums of uniformly close bounded sequences are close:
`|Σ w_k a_k − Σ w_k b_k| ≤ W C` when `|b_k| ≤ B` and `|a_k − b_k| ≤ C`. -/
theorem abs_tsum_mul_sub_tsum_mul_le (hd : AdmissibleDefect w s) {a b : ℕ → ℝ} {B C : ℝ}
    (hb : ∀ k, |b k| ≤ B) (hab : ∀ k, |a k - b k| ≤ C) :
    |∑' k, w k * a k - ∑' k, w k * b k| ≤ (∑' k, w k) * C := by
  have hwb : ∀ k, ‖w k * b k‖ ≤ w k * B := fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hd.nonneg k)]
    exact mul_le_mul_of_nonneg_left (hb k) (hd.nonneg k)
  have hwa : ∀ k, ‖w k * a k‖ ≤ w k * (B + C) := fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hd.nonneg k)]
    refine mul_le_mul_of_nonneg_left ?_ (hd.nonneg k)
    have h1 := hb k; have h2 := hab k
    rw [abs_le] at h1 h2 ⊢; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hsb := (hd.summable.mul_right B).of_norm_bounded hwb
  have hsa := (hd.summable.mul_right (B + C)).of_norm_bounded hwa
  rw [← hsa.tsum_sub hsb, ← tsum_mul_right]
  refine (norm_tsum_le_tsum_norm (hsa.sub hsb).norm).trans
    ((hsa.sub hsb).norm.tsum_le_tsum (fun k => ?_) (hd.summable.mul_right C))
  rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (hd.nonneg k)]
  exact mul_le_mul_of_nonneg_left (hab k) (hd.nonneg k)

/-- **The Euler comparison for the defect pattern.** On `Re v > 1`,
`|log|F(v)| − D(v)| ≤ (2 + cW) S` with `S = Σ_p p^{-2}`. -/
theorem abs_log_norm_defectSeries_sub_le (hd : AdmissibleDefect w s) {c : ℝ} (hc : 0 ≤ c)
    (hcW : c * ∑' k, w k ≤ 2) (t₀ : ℝ) {v : ℂ} (hv : 1 < v.re) :
    |Real.log ‖∑' n : ℕ, (defectPattern c t₀ w s n : ℂ) * ((n : ℝ) : ℂ) ^ (-v)‖ -
      defectLogModel c t₀ w s v| ≤ (2 + c * ∑' k, w k) * primeSquareMass := by
  have hF := abs_log_norm_tsum_sub_re_le (cweightedPatternHom (defectPattern c t₀ w s) v) hv
    fun n => by
      simp only [cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_natCast]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_defectPattern_le hd hc hcW t₀ n)
  have hFn : ∑' n, cweightedPatternHom (defectPattern c t₀ w s) v n =
      ∑' n : ℕ, (defectPattern c t₀ w s n : ℂ) * ((n : ℝ) : ℂ) ^ (-v) := tsum_congr fun n => rfl
  rw [hFn, tsum_defectPattern_primes hd c t₀ hv] at hF
  set Q : ℕ → ℂ := fun k => cosPrimeSeries t₀ (v + s k)
  set M := ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-v.re)
  have hvk : ∀ k, 1 < (v + s k).re := fun k => by simp; linarith [hd.pos k]
  have hQb : ∀ k, ‖Q k‖ ≤ M := fun k =>
    norm_cosPrimeSeries_le t₀ hv (by simp; linarith [hd.pos k])
  have hQs : Summable fun k => (w k : ℂ) * Q k :=
    (hd.summable.mul_right M).of_norm_bounded fun k => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd.nonneg k)]
      exact mul_le_mul_of_nonneg_left (hQb k) (hd.nonneg k)
  have hre : (c * ∑' k, (w k : ℂ) * Q k).re = c * ∑' k, w k * (Q k).re := by
    rw [Complex.re_ofReal_mul, Complex.re_tsum hQs]
    simp only [Complex.re_ofReal_mul]
  rw [Complex.sub_re, hre, ← primeSquareMass] at hF
  set Zk : ℕ → ℝ := fun k => Real.log ‖riemannZeta (v + s k - t₀ * I)‖ +
    Real.log ‖riemannZeta (v + s k + t₀ * I)‖
  have hQZ : ∀ k, |(Q k).re - Zk k / 2| ≤ primeSquareMass := fun k =>
    abs_re_cosPrimeSeries_sub_le t₀ (hvk k)
  have hQre : ∀ k, |(Q k).re| ≤ M := fun k => (Complex.abs_re_le_norm _).trans (hQb k)
  have hsum := abs_tsum_mul_sub_tsum_mul_le hd (a := fun k => Zk k / 2)
    (b := fun k => (Q k).re) hQre (fun k => by rw [abs_sub_comm]; exact hQZ k)
  have hhalf : ∑' k, w k * (Zk k / 2) = (∑' k, w k * Zk k) / 2 := by
    rw [← tsum_div_const]; exact tsum_congr fun k => by ring
  rw [hhalf] at hsum
  have h0 := abs_re_cosPrimeSeries_sub_le t₀ hv
  have hcs := mul_le_mul_of_nonneg_left hsum hc
  rw [← abs_of_nonneg hc, ← abs_mul, abs_of_nonneg hc] at hcs
  have hS : 0 ≤ primeSquareMass := tsum_nonneg fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _
  simp only [defectLogModel]
  set Lf := Real.log ‖∑' n : ℕ, (defectPattern c t₀ w s n : ℂ) * ((n : ℝ) : ℂ) ^ (-v)‖
  set A := ∑' k, w k * (Q k).re
  set Bz := ∑' k, w k * Zk k
  rw [abs_le] at hF h0 hcs ⊢
  constructor <;> nlinarith [hF.1, hF.2, h0.1, h0.2, hcs.1, hcs.2]

/-! ### The defect profile -/

/-- `|log x| ≤ |log a| + |log b|` on `0 < a ≤ x ≤ b`. -/
theorem abs_log_le_of_mem {a b x : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    |Real.log x| ≤ |Real.log a| + |Real.log b| := by
  have h1 := Real.log_le_log ha hax
  have h2 := Real.log_le_log (by linarith) hxb
  rw [abs_le]; constructor <;> linarith [le_abs_self (Real.log a), neg_abs_le (Real.log a),
    le_abs_self (Real.log b), neg_abs_le (Real.log b)]

theorem abs_log_inv_shift_le (hd : AdmissibleDefect w s) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    |Real.log (s k + ρ)⁻¹| ≤ |Real.log ρ| + |Real.log (1 + ρ)| := by
  rw [Real.log_inv, abs_neg]
  exact abs_log_le_of_mem hρ (by linarith [hd.pos k]) (by linarith [hd.le_half k])

theorem summable_defectProfile (hd : AdmissibleDefect w s) {ρ : ℝ} (hρ : 0 < ρ) :
    Summable fun k => w k * Real.log (s k + ρ)⁻¹ :=
  (hd.summable.mul_right (|Real.log ρ| + |Real.log (1 + ρ)|)).of_norm_bounded fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hd.nonneg k)]
    exact mul_le_mul_of_nonneg_left (abs_log_inv_shift_le hd hρ k) (hd.nonneg k)

/-- `Λ ≥ 0` on `(0, 1/2]`. -/
theorem defectProfile_nonneg (hd : AdmissibleDefect w s) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ2 : ρ ≤ 1 / 2) : 0 ≤ defectProfile w s ρ :=
  tsum_nonneg fun k => mul_nonneg (hd.nonneg k) (by
    rw [Real.log_inv, neg_nonneg]
    exact Real.log_nonpos (by linarith [hd.pos k]) (by linarith [hd.le_half k]))

/-- `Λ` is antitone on `(0, ∞)`. -/
theorem defectProfile_antitone (hd : AdmissibleDefect w s) {ρ ρ' : ℝ} (hρ : 0 < ρ)
    (hρρ' : ρ ≤ ρ') : defectProfile w s ρ' ≤ defectProfile w s ρ :=
  (summable_defectProfile hd (by linarith)).tsum_le_tsum (fun k => by
    refine mul_le_mul_of_nonneg_left ?_ (hd.nonneg k)
    rw [Real.log_inv, Real.log_inv, neg_le_neg_iff]
    exact Real.log_le_log (by linarith [hd.pos k]) (by linarith)) (summable_defectProfile hd hρ)

/-- Doubling costs at most `W log 2`: `Λ(ρ) − W log 2 ≤ Λ(2ρ)`. -/
theorem defectProfile_sub_le_two_mul (hd : AdmissibleDefect w s) {ρ : ℝ} (hρ : 0 < ρ) :
    defectProfile w s ρ - (∑' k, w k) * Real.log 2 ≤ defectProfile w s (2 * ρ) := by
  rw [defectProfile, defectProfile, ← tsum_mul_right,
    ← (summable_defectProfile hd hρ).tsum_sub (hd.summable.mul_right _)]
  refine (((summable_defectProfile hd hρ).sub (hd.summable.mul_right _))).tsum_le_tsum
    (fun k => ?_) (summable_defectProfile hd (by linarith))
  have hk := hd.pos k
  rw [← mul_sub]
  refine mul_le_mul_of_nonneg_left ?_ (hd.nonneg k)
  rw [Real.log_inv, Real.log_inv]
  have : Real.log (s k + 2 * ρ) ≤ Real.log (s k + ρ) + Real.log 2 := by
    rw [← Real.log_mul (by linarith) (by norm_num)]
    exact Real.log_le_log (by linarith) (by linarith)
  linarith

/-- `−Λ(ρ) ≤ W log(1 + R)` on `(0, R]`. -/
theorem neg_defectProfile_le (hd : AdmissibleDefect w s) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    -defectProfile w s ρ ≤ (∑' k, w k) * Real.log (1 + R) := by
  rw [defectProfile, ← tsum_neg, ← tsum_mul_right]
  refine (summable_defectProfile hd hρ).neg.tsum_le_tsum (fun k => ?_)
    (hd.summable.mul_right _)
  rw [Real.log_inv, mul_neg, neg_neg]
  exact mul_le_mul_of_nonneg_left
    (Real.log_le_log (by linarith [hd.pos k]) (by linarith [hd.le_half k])) (hd.nonneg k)

/-! ### `ζ` on boxes right of the pole -/

/-- `log|ζ(v)| = −log|v − 1| + O(1)` on `1 < Re v ≤ 2`, `|Im v| ≤ H`. -/
theorem exists_abs_log_norm_zeta_add_log_le (H : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ v : ℂ, 1 < v.re → v.re ≤ 2 → |v.im| ≤ H →
      |Real.log ‖riemannZeta v‖ + Real.log ‖v - 1‖| ≤ L := by
  obtain ⟨m, K, hm, hb⟩ := RHTower.exists_norm_zeta_mul_sub_one_bounds H
  refine ⟨|Real.log m| + |Real.log K|, by positivity, fun v hv hv2 hvH => ?_⟩
  obtain ⟨h1, h2⟩ := hb v hv hv2 hvH
  have hv1 : v - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hζ : riemannZeta v ≠ 0 := riemannZeta_ne_zero_of_one_le_re hv.le
  have hpos : 0 < ‖riemannZeta v‖ * ‖v - 1‖ :=
    mul_pos (norm_pos_iff.mpr hζ) (norm_pos_iff.mpr hv1)
  rw [← Real.log_mul (norm_ne_zero_iff.mpr hζ) (norm_ne_zero_iff.mpr hv1)]
  have hl1 := Real.log_le_log hm h1
  have hl2 := Real.log_le_log hpos h2
  rw [abs_le]; constructor <;> linarith [le_abs_self (Real.log m), neg_abs_le (Real.log m),
    le_abs_self (Real.log K), neg_abs_le (Real.log K)]

/-- Two consequences on the box: near the pole `|log|ζ(v)| − log(1/a)| ≤ L + log 2` when
`a/2 ≤ |v − 1| ≤ a`; away from it `|log|ζ(v)|| ≤ L + |log a| + |log b|` when `a ≤ |v − 1| ≤ b`. -/
theorem abs_log_norm_zeta_sub_log_inv_le {L H : ℝ}
    (hL : ∀ v : ℂ, 1 < v.re → v.re ≤ 2 → |v.im| ≤ H →
      |Real.log ‖riemannZeta v‖ + Real.log ‖v - 1‖| ≤ L)
    {v : ℂ} (hv : 1 < v.re) (hv2 : v.re ≤ 2) (hvH : |v.im| ≤ H) {a : ℝ}
    (ha1 : a / 2 ≤ ‖v - 1‖) (ha2 : ‖v - 1‖ ≤ a) :
    |Real.log ‖riemannZeta v‖ - Real.log a⁻¹| ≤ L + Real.log 2 := by
  have h := hL v hv hv2 hvH
  have hv1 : 0 < ‖v - 1‖ := by
    refine lt_of_lt_of_le ?_ (Complex.abs_re_le_norm (v - 1))
    rw [Complex.sub_re, Complex.one_re, abs_of_pos (by linarith)]; linarith
  have ha : 0 < a := by linarith
  have l1 := Real.log_le_log (by linarith) ha1
  have l2 := Real.log_le_log hv1 ha2
  rw [Real.log_div ha.ne' two_ne_zero] at l1
  rw [Real.log_inv]
  rw [abs_le] at h ⊢; constructor <;> linarith [h.1, h.2]

theorem abs_log_norm_zeta_le_of_mem {L H : ℝ}
    (hL : ∀ v : ℂ, 1 < v.re → v.re ≤ 2 → |v.im| ≤ H →
      |Real.log ‖riemannZeta v‖ + Real.log ‖v - 1‖| ≤ L)
    {v : ℂ} (hv : 1 < v.re) (hv2 : v.re ≤ 2) (hvH : |v.im| ≤ H) {a b : ℝ} (ha : 0 < a)
    (ha1 : a ≤ ‖v - 1‖) (hb : ‖v - 1‖ ≤ b) :
    |Real.log ‖riemannZeta v‖| ≤ L + (|Real.log a| + |Real.log b|) := by
  have h := hL v hv hv2 hvH
  have hl := abs_log_le_of_mem ha ha1 hb
  have := abs_add_le (Real.log ‖riemannZeta v‖ + Real.log ‖v - 1‖) (-Real.log ‖v - 1‖)
  rw [abs_neg, add_neg_cancel_right] at this
  linarith

/-- `ρ/2 ≤ |x + iy| ≤ ρ` for `ρ = |x| + |y|`. -/
theorem norm_bounds_abs_add_abs (z : ℂ) :
    (|z.re| + |z.im|) / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ |z.re| + |z.im| :=
  ⟨by linarith [Complex.abs_re_le_norm z, Complex.abs_im_le_norm z],
    Complex.norm_le_abs_re_add_abs_im z⟩

/-- **The box estimate.** For `t₀ > 0` and `T ≥ 0` there is `B` with
`|log|F(v)| − (½ log(1/ρ) − (c/2) Λ(ρ))| ≤ B`, `ρ = (Re v − 1) + |Im v − t₀|`, on
`1 < Re v ≤ 3/2`, `0 ≤ Im v ≤ T`. -/
theorem exists_abs_log_norm_defectSeries_sub_profile_le (hd : AdmissibleDefect w s) {c t₀ T : ℝ}
    (hc : 0 ≤ c) (hcW : c * ∑' k, w k ≤ 2) (ht₀ : 0 < t₀) (hT : 0 ≤ T) :
    ∃ B : ℝ, ∀ v : ℂ, 1 < v.re → v.re ≤ 3 / 2 → 0 ≤ v.im → v.im ≤ T →
      |Real.log ‖∑' n : ℕ, (defectPattern c t₀ w s n : ℂ) * ((n : ℝ) : ℂ) ^ (-v)‖ -
        (1 / 2 * Real.log (v.re - 1 + |v.im - t₀|)⁻¹ -
          c / 2 * defectProfile w s (v.re - 1 + |v.im - t₀|))| ≤ B := by
  obtain ⟨L, hL0, hL⟩ := exists_abs_log_norm_zeta_add_log_le (T + t₀)
  set W := ∑' k, w k
  have hW : 0 ≤ W := tsum_nonneg hd.nonneg
  set L₂ : ℝ := L + (|Real.log t₀| + |Real.log (T + t₀ + 2)|)
  refine ⟨(L + Real.log 2 + L₂) / 2 + c / 2 * (W * (L + Real.log 2 + L₂)) +
    (2 + c * W) * primeSquareMass, fun v hv hv2 hv0 hvT => ?_⟩
  have hE := abs_log_norm_defectSeries_sub_le hd hc hcW t₀ hv
  set u := v.re - 1
  set τ := v.im - t₀
  set ρ := u + |τ|
  have hu : 0 < u := by simp only [u]; linarith
  have hρ : 0 < ρ := by simp only [ρ]; positivity
  have hτH : |τ| ≤ T + t₀ := by simp only [τ]; rw [abs_le]; constructor <;> linarith
  have hpH : |v.im + t₀| ≤ T + t₀ := by rw [abs_of_nonneg (by linarith)]; linarith
  -- the four kinds of `ζ` values
  have hZm : |Real.log ‖riemannZeta (v - t₀ * I)‖ - Real.log ρ⁻¹| ≤ L + Real.log 2 := by
    have hn := norm_bounds_abs_add_abs (v - t₀ * I - 1)
    have hre : (v - t₀ * I - 1).re = u := by simp [u]
    have him : (v - t₀ * I - 1).im = τ := by simp [τ]
    rw [hre, him, abs_of_pos hu] at hn
    exact abs_log_norm_zeta_sub_log_inv_le hL (by simpa using hv) (by simp; linarith)
      (by simpa [τ] using hτH) hn.1 hn.2
  have hZp : |Real.log ‖riemannZeta (v + t₀ * I)‖| ≤ L₂ := by
    have hre : (v + t₀ * I - 1).re = u := by simp [u]
    have him : (v + t₀ * I - 1).im = v.im + t₀ := by simp
    have hn := norm_bounds_abs_add_abs (v + t₀ * I - 1)
    rw [hre, him, abs_of_pos hu, abs_of_nonneg (by linarith)] at hn
    refine abs_log_norm_zeta_le_of_mem hL (by simpa using hv) (by simp; linarith)
      (by simpa using hpH) ht₀ ?_ ?_
    · have := Complex.abs_im_le_norm (v + t₀ * I - 1)
      rw [him, abs_of_nonneg (by linarith)] at this; linarith
    · linarith
  have hZmk : ∀ k, |Real.log ‖riemannZeta (v + s k - t₀ * I)‖ - Real.log (s k + ρ)⁻¹| ≤
      L + Real.log 2 := fun k => by
    have hk := hd.pos k
    have hk2 := hd.le_half k
    have hre : (v + s k - t₀ * I - 1).re = u + s k := by simp [u]; ring
    have him : (v + s k - t₀ * I - 1).im = τ := by simp [τ]
    have hn := norm_bounds_abs_add_abs (v + s k - t₀ * I - 1)
    rw [hre, him, abs_of_pos (by linarith)] at hn
    refine abs_log_norm_zeta_sub_log_inv_le hL (by simp; linarith) (by simp; linarith)
      (by simpa [τ] using hτH) ?_ ?_
    · simp only [ρ]; linarith [hn.1]
    · simp only [ρ]; linarith [hn.2]
  have hZpk : ∀ k, |Real.log ‖riemannZeta (v + s k + t₀ * I)‖| ≤ L₂ := fun k => by
    have hk := hd.pos k
    have hk2 := hd.le_half k
    have hre : (v + s k + t₀ * I - 1).re = u + s k := by simp [u]; ring
    have him : (v + s k + t₀ * I - 1).im = v.im + t₀ := by simp
    have hn := norm_bounds_abs_add_abs (v + s k + t₀ * I - 1)
    rw [hre, him, abs_of_pos (by linarith), abs_of_nonneg (by linarith)] at hn
    refine abs_log_norm_zeta_le_of_mem hL (by simp; linarith) (by simp; linarith)
      (by simpa using hpH) ht₀ ?_ ?_
    · have := Complex.abs_im_le_norm (v + s k + t₀ * I - 1)
      rw [him, abs_of_nonneg (by linarith)] at this; linarith
    · linarith
  -- the weighted sum of the shifted values against the profile
  have hsum := abs_tsum_mul_sub_tsum_mul_le hd
    (a := fun k => Real.log ‖riemannZeta (v + s k - t₀ * I)‖ +
      Real.log ‖riemannZeta (v + s k + t₀ * I)‖)
    (b := fun k => Real.log (s k + ρ)⁻¹) (abs_log_inv_shift_le hd hρ)
    (C := L + Real.log 2 + L₂) fun k => by
      have h1 := hZmk k; have h2 := hZpk k
      rw [abs_le] at h1 h2 ⊢; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  change |_ - defectProfile w s ρ| ≤ _ at hsum
  have hcs := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ c / 2)
  rw [← abs_of_nonneg (by positivity : (0 : ℝ) ≤ c / 2), ← abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ c / 2)] at hcs
  simp only [defectLogModel] at hE
  set Lf := Real.log ‖∑' n : ℕ, (defectPattern c t₀ w s n : ℂ) * ((n : ℝ) : ℂ) ^ (-v)‖
  rw [abs_le] at hE hcs hZm hZp ⊢
  constructor <;> nlinarith [hE.1, hE.2, hcs.1, hcs.2, hZm.1, hZm.2, hZp.1, hZp.2]

/-! ### The Dini density -/

/-- The Dini density `h(ρ) = e^{−cΛ(ρ)}/ρ`. -/
def diniDensity (c : ℝ) (w s : ℕ → ℝ) (ρ : ℝ) : ℝ := Real.exp (-(c * defectProfile w s ρ)) / ρ

theorem diniDensity_nonneg (c : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ diniDensity c w s ρ :=
  div_nonneg (Real.exp_pos _).le hρ

/-- `h(ρ) ≤ 1/ρ` on `(0, 1/2]`, where `Λ ≥ 0`. -/
theorem diniDensity_le_inv (hd : AdmissibleDefect w s) {c : ℝ} (hc : 0 ≤ c) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ2 : ρ ≤ 1 / 2) : diniDensity c w s ρ ≤ ρ⁻¹ := by
  rw [diniDensity, div_eq_mul_inv]
  refine mul_le_of_le_one_left (inv_nonneg.mpr hρ.le) (Real.exp_le_one_iff.mpr ?_)
  have := mul_nonneg hc (defectProfile_nonneg hd hρ hρ2)
  linarith

/-- `h` is almost decreasing: `h(ρ) ≤ 4 h(x)` for `x ≤ ρ ≤ 2x`. -/
theorem diniDensity_le_four_mul (hd : AdmissibleDefect w s) {c : ℝ} (hc : 0 ≤ c)
    (hcW : c * ∑' k, w k ≤ 2) {x ρ : ℝ} (hx : 0 < x) (hxρ : x ≤ ρ) (hρx : ρ ≤ 2 * x) :
    diniDensity c w s ρ ≤ 4 * diniDensity c w s x := by
  have h1 := defectProfile_antitone hd (by linarith : 0 < ρ) hρx
  have h2 := defectProfile_sub_le_two_mul hd hx
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hcw : c * (∑' k, w k) * Real.log 2 ≤ 2 * Real.log 2 :=
    mul_le_mul_of_nonneg_right hcW hlog2
  have hexp : Real.exp (-(c * defectProfile w s ρ)) ≤
      4 * Real.exp (-(c * defectProfile w s x)) := by
    have hineq : -(c * defectProfile w s ρ) ≤ 2 * Real.log 2 + -(c * defectProfile w s x) := by
      have := mul_le_mul_of_nonneg_left (h2.trans h1) hc
      rw [mul_sub] at this
      nlinarith
    calc Real.exp (-(c * defectProfile w s ρ))
        ≤ Real.exp (2 * Real.log 2 + -(c * defectProfile w s x)) := Real.exp_le_exp.mpr hineq
      _ = 4 * Real.exp (-(c * defectProfile w s x)) := by
        rw [Real.exp_add, show 2 * Real.log 2 = Real.log 4 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring,
          Real.exp_log (by norm_num)]
  rw [diniDensity, diniDensity, mul_div_assoc']
  calc _ ≤ 4 * Real.exp (-(c * defectProfile w s x)) / ρ :=
        div_le_div_of_nonneg_right hexp (by linarith)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hx hxρ

/-- `h(ρ) ≤ (1 + R)²/a` on `[a, R]`. -/
theorem diniDensity_le_of_mem (hd : AdmissibleDefect w s) {c : ℝ} (hc : 0 ≤ c)
    (hcW : c * ∑' k, w k ≤ 2) {a R ρ : ℝ} (ha : 0 < a) (haρ : a ≤ ρ) (hρR : ρ ≤ R) :
    diniDensity c w s ρ ≤ (1 + R) ^ 2 / a := by
  have hρ : 0 < ρ := by linarith
  have h := neg_defectProfile_le hd hρ hρR
  have hlog : 0 ≤ Real.log (1 + R) := Real.log_nonneg (by linarith)
  have hexp : Real.exp (-(c * defectProfile w s ρ)) ≤ (1 + R) ^ 2 := by
    have h' : -(c * defectProfile w s ρ) ≤ 2 * Real.log (1 + R) := by
      have h3 := mul_le_mul_of_nonneg_left h hc
      have h4 := mul_le_mul_of_nonneg_right hcW hlog
      rw [mul_neg, ← mul_assoc] at h3
      linarith
    calc _ ≤ Real.exp (2 * Real.log (1 + R)) := Real.exp_le_exp.mpr h'
      _ = (1 + R) ^ 2 := by
        rw [show 2 * Real.log (1 + R) = Real.log ((1 + R) ^ 2) by rw [Real.log_pow]; push_cast; ring,
          Real.exp_log (pow_pos (by linarith) 2)]
  rw [diniDensity]
  calc _ ≤ (1 + R) ^ 2 / ρ := div_le_div_of_nonneg_right hexp hρ.le
    _ ≤ (1 + R) ^ 2 / a := div_le_div_of_nonneg_left (by positivity) ha haρ

theorem aemeasurable_diniDensity (hd : AdmissibleDefect w s) {c : ℝ} (hc : 0 ≤ c) :
    AEMeasurable (diniDensity c w s) (volume.restrict (Ioi 0)) := by
  have hmono : MonotoneOn (fun ρ => Real.exp (-(c * defectProfile w s ρ))) (Ioi 0) := by
    intro x hx y _ hxy
    refine Real.exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_left (defectProfile_antitone hd hx hxy) hc
    linarith
  exact (aemeasurable_restrict_of_monotoneOn measurableSet_Ioi hmono).div aemeasurable_id

theorem integrableOn_diniDensity_Ioc (hd : AdmissibleDefect w s) {c : ℝ} (hc : 0 ≤ c)
    (hcW : c * ∑' k, w k ≤ 2) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (diniDensity c w s) (Ioc a b) := by
  have hm : AEStronglyMeasurable (diniDensity c w s) (volume.restrict (Ioc a b)) :=
    ((aemeasurable_diniDensity hd hc).mono_measure (Measure.restrict_mono
      (fun x hx => (show (0 : ℝ) < x from lt_trans ha hx.1)) le_rfl)).aestronglyMeasurable
  refine Integrable.mono' (g := fun _ => (1 + max b a) ^ 2 / a)
    (integrableOn_const (C := (1 + max b a) ^ 2 / a) measure_Ioc_lt_top.ne) hm ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (diniDensity_nonneg c (by linarith [hx.1]))]
  exact diniDensity_le_of_mem hd hc hcW ha hx.1.le (hx.2.trans (le_max_left _ _))

theorem integrableOn_diniDensity_of_one (hd : AdmissibleDefect w s) {c : ℝ} (hc : 0 ≤ c)
    (hcW : c * ∑' k, w k ≤ 2) (hI : IntegrableOn (diniDensity c w s) (Ioc 0 1)) {R : ℝ}
    (hR : 1 ≤ R) : IntegrableOn (diniDensity c w s) (Ioc 0 R) := by
  rw [← Ioc_union_Ioc_eq_Ioc zero_le_one hR]
  exact hI.union (integrableOn_diniDensity_Ioc hd hc hcW one_pos)

/-- The reflected and translated density `y ↦ h(|y − t₀|)` is locally integrable. -/
theorem intervalIntegrable_diniDensity_abs_sub (hd : AdmissibleDefect w s) {c : ℝ} (hc : 0 ≤ c)
    (hcW : c * ∑' k, w k ≤ 2) (hI : IntegrableOn (diniDensity c w s) (Ioc 0 1)) (t₀ a b : ℝ) :
    IntervalIntegrable (fun y => diniDensity c w s |y - t₀|) volume a b := by
  have h0 : ∀ R : ℝ, 0 ≤ R →
      IntervalIntegrable (fun x => diniDensity c w s |x|) volume 0 R := by
    intro R hR
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR]
    exact ((integrableOn_diniDensity_of_one hd hc hcW hI (le_max_right R 1)).mono_set
      (Ioc_subset_Ioc_right (le_max_left R 1))).congr_fun
        (fun x hx => by simp only [abs_of_pos hx.1]) measurableSet_Ioc
  have habs : ∀ R : ℝ, IntervalIntegrable (fun x => diniDensity c w s |x|) volume 0 R := by
    intro R
    rcases le_total 0 R with hR | hR
    · exact h0 R hR
    · have h := (IntervalIntegrable.iff_comp_neg (f := fun x : ℝ => diniDensity c w s |x|)).mp
        (h0 (-R) (by linarith)).symm
      simpa only [abs_neg, neg_neg, neg_zero] using h.symm
  have hall : IntervalIntegrable (fun x => diniDensity c w s |x|) volume (a - t₀) (b - t₀) :=
    (habs (a - t₀)).symm.trans (habs (b - t₀))
  simpa only [sub_add_cancel] using hall.comp_sub_right t₀

/-- `log F ≤ ½ log(1/ρ) − (c/2)Λ(ρ) + B` gives `F² ≤ e^{2B} h(ρ)`. -/
theorem sq_le_exp_mul_diniDensity {c F ρ B : ℝ} (hF : 0 < F) (hρ : 0 < ρ)
    (h : Real.log F - (1 / 2 * Real.log ρ⁻¹ - c / 2 * defectProfile w s ρ) ≤ B) :
    F ^ 2 ≤ Real.exp (2 * B) * diniDensity c w s ρ := by
  have hF2 : F ^ 2 = Real.exp (2 * Real.log F) := by
    rw [show 2 * Real.log F = Real.log F + Real.log F by ring, Real.exp_add, Real.exp_log hF, sq]
  have he : Real.exp (2 * B) * diniDensity c w s ρ =
      Real.exp (Real.log ρ⁻¹ + -(c * defectProfile w s ρ) + 2 * B) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log (inv_pos.mpr hρ), diniDensity, div_eq_mul_inv]
    ring
  rw [hF2, he]
  exact Real.exp_le_exp.mpr (by linarith)

/-- `log F ≥ ½ log(1/ρ) − (c/2)Λ(ρ) − B` gives `e^{−2B} h(ρ) ≤ F²`. -/
theorem exp_mul_diniDensity_le_sq {c F ρ B : ℝ} (hF : 0 < F) (hρ : 0 < ρ)
    (h : -B ≤ Real.log F - (1 / 2 * Real.log ρ⁻¹ - c / 2 * defectProfile w s ρ)) :
    Real.exp (-(2 * B)) * diniDensity c w s ρ ≤ F ^ 2 := by
  have hF2 : F ^ 2 = Real.exp (2 * Real.log F) := by
    rw [show 2 * Real.log F = Real.log F + Real.log F by ring, Real.exp_add, Real.exp_log hF, sq]
  have he : Real.exp (-(2 * B)) * diniDensity c w s ρ =
      Real.exp (Real.log ρ⁻¹ + -(c * defectProfile w s ρ) + -(2 * B)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log (inv_pos.mpr hρ), diniDensity, div_eq_mul_inv]
    ring
  rw [hF2, he]
  exact Real.exp_le_exp.mpr (by linarith)

/-! ### The series and the line energy -/

theorem weightDirichletSeries_defectWeight (c t₀ : ℝ) (w s : ℕ → ℝ) (z : ℂ) :
    weightDirichletSeries (defectWeight c t₀ w s) z =
      ∑' n : ℕ, (defectPattern c t₀ w s n : ℂ) * ((n : ℝ) : ℂ) ^ (-(z + 1 / 2)) :=
  weightDirichletSeries_pattern _ z

/-- The defect series does not vanish on `Re v > 1` (an Euler product). -/
theorem defectSeries_ne_zero (hd : AdmissibleDefect w s) {c : ℝ} (hc : 0 ≤ c)
    (hcW : c * ∑' k, w k ≤ 2) (t₀ : ℝ) {v : ℂ} (hv : 1 < v.re) :
    ∑' n : ℕ, (defectPattern c t₀ w s n : ℂ) * ((n : ℝ) : ℂ) ^ (-v) ≠ 0 := by
  set g := cweightedPatternHom (defectPattern c t₀ w s) v
  have hsum : Summable (fun n => ‖g n‖) := by
    refine (Real.summable_nat_rpow.mpr (show -v.re < -1 by linarith)).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun n => ?_
    simp only [g, cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul,
      Complex.norm_real, Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Real.zero_rpow (show -v.re ≠ 0 by intro h; linarith)]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re]
      exact mul_le_of_le_one_left (Real.rpow_nonneg hn0.le _) (abs_defectPattern_le hd hc hcW t₀ n)
  have hE := EulerProduct.exp_tsum_primes_log_eq_tsum hsum
  have hFn : ∑' n, g n = ∑' n : ℕ, (defectPattern c t₀ w s n : ℂ) * ((n : ℝ) : ℂ) ^ (-v) :=
    tsum_congr fun n => rfl
  rw [← hFn, ← hE]
  exact Complex.exp_ne_zero _

/-- **A line-energy criterion with a family of majorants.** If on `1/2 < σ < 3/4` the line
integrand is dominated on `(0, T]` by `g σ`, integrable with `∫_{(0,T]} g σ ≤ G` uniformly, and
`|C(s) − P| ≤ B₁ t^{1/4}` above `T ≥ 2`, the line energies are uniformly bounded. -/
theorem exists_lineEnergy_le_of_majorant_family {c : ℕ → ℝ} {P T B₁ G : ℝ} {g : ℝ → ℝ → ℝ}
    (hT : 2 ≤ T) (hg : ∀ σ : ℝ, 1 / 2 < σ → σ < 3 / 4 → IntegrableOn (g σ) (Ioc 0 T))
    (hgG : ∀ σ : ℝ, 1 / 2 < σ → σ < 3 / 4 → ∫ t in Ioc 0 T, g σ t ≤ G)
    (hsmall : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 → 0 < t → t ≤ T →
      lineIntegrand c P σ t ≤ g σ t)
    (hlarge : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 → T < t →
      ‖weightDirichletSeries c ((σ : ℂ) + t * I) - (P : ℂ)‖ ≤ B₁ * t ^ (1 / 4 : ℝ)) :
    ∃ M : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ < 3 / 4 → ∫ t : ℝ, lineIntegrand c P σ t ≤ M := by
  obtain ⟨M₂, hM₂⟩ := exists_integral_zeta_sq_rpow_le
  set Λ : ℝ := B₁ ^ 2
  refine ⟨2 * (G + Λ * M₂), fun σ hσ hσ' => ?_⟩
  set Φ : ℝ → ℝ := lineIntegrand c P σ with hΦ
  change ∫ t : ℝ, Φ t ≤ _
  obtain ⟨hint2, hbound2⟩ := hM₂ σ hσ.le (by linarith)
  have hΦform : ∀ t, Φ t = ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 *
      ‖weightDirichletSeries c ((σ : ℂ) + t * I) - (P : ℂ)‖ ^ 2 / ‖(σ : ℂ) + t * I‖ ^ 2 :=
    fun t => by simp only [hΦ, lineIntegrand, norm_div, norm_mul, div_pow, mul_pow]
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
  set Gf : ℝ → ℝ := fun u => if u ≤ T then g σ u
    else Λ * (‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ)))
  have hint2T : IntegrableOn
      (fun u : ℝ => ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ))) (Ioi T) :=
    hint2.mono_set (Ioi_subset_Ioi hT)
  have hsplit : Ioi (0 : ℝ) = Ioc 0 T ∪ Ioi T := (Ioc_union_Ioi_eq_Ioi (by linarith)).symm
  have hGint : IntegrableOn Gf (Ioi 0) := by
    rw [hsplit]
    refine IntegrableOn.union ?_ ?_
    · exact (hg σ hσ hσ').congr_fun (fun u hu => by simp only [Gf, if_pos hu.2]) measurableSet_Ioc
    · refine IntegrableOn.congr_fun (hint2T.const_mul Λ) (fun u hu => ?_) measurableSet_Ioi
      have : ¬ u ≤ T := not_le.mpr hu
      simp only [Gf, if_neg this]
  have hΦ0 : ∀ u, 0 ≤ Φ u := fun u => by simp only [hΦ, lineIntegrand]; positivity
  have hΦle : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), Φ u ≤ Gf u := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hpos => ?_)
    simp only [Gf]
    split_ifs with huT
    · exact hsmall σ u hσ hσ' hpos huT
    · exact hlarge' u (not_le.mp huT)
  have hhalf : ∫ u in Ioi (0 : ℝ), Φ u ≤ ∫ u in Ioi (0 : ℝ), Gf u :=
    integral_mono_of_nonneg (Eventually.of_forall hΦ0) hGint hΦle
  have hG1 : ∫ u in Ioc 0 T, Gf u = ∫ u in Ioc 0 T, g σ u :=
    setIntegral_congr_fun measurableSet_Ioc (fun u hu => by simp only [Gf, if_pos hu.2])
  have hG2 : ∫ u in Ioi T, Gf u =
      Λ * ∫ u in Ioi T, ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ)) := by
    rw [setIntegral_congr_fun
        (g := fun u : ℝ => Λ * (‖riemannZeta ((σ : ℂ) + (u : ℂ) * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ))))
        measurableSet_Ioi (fun u hu => by
          have : ¬ u ≤ T := not_le.mpr hu
          simp only [Gf, if_neg this]), integral_const_mul]
  have hGval : ∫ u in Ioi (0 : ℝ), Gf u = (∫ u in Ioc 0 T, g σ u) +
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
  have := mul_le_mul_of_nonneg_left htail (sq_nonneg B₁)
  have hG := hgG σ hσ hσ'
  linarith

/-! ### Large heights -/

/-- `(log 2y)^{27} ≤ 2 · 108^{27} y^{1/4}` for `y ≥ 1`. -/
theorem log_two_mul_pow_le {y : ℝ} (hy : 1 ≤ y) :
    Real.log (2 * y) ^ 27 ≤ 2 * 108 ^ 27 * y ^ (1 / 4 : ℝ) := by
  have h2y : 0 < 2 * y := by linarith
  have hl0 : 0 ≤ Real.log (2 * y) := Real.log_nonneg (by linarith)
  have hl' : Real.log (2 * y) ≤ 108 * (2 * y) ^ (1 / 108 : ℝ) :=
    (Real.log_le_rpow_div h2y.le (show (0 : ℝ) < 1 / 108 by norm_num)).trans (le_of_eq (by ring))
  have h24 : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
    calc (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have hy4 : 0 ≤ y ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by linarith) _
  calc Real.log (2 * y) ^ 27 ≤ (108 * (2 * y) ^ (1 / 108 : ℝ)) ^ 27 :=
        pow_le_pow_left₀ hl0 hl' 27
    _ = 108 ^ 27 * (2 ^ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ)) := by
        rw [mul_pow, ← Real.rpow_natCast ((2 * y) ^ (1 / 108 : ℝ)), ← Real.rpow_mul h2y.le,
          ← Real.mul_rpow (by norm_num) (by linarith)]
        norm_num
    _ ≤ 2 * 108 ^ 27 * y ^ (1 / 4 : ℝ) := by nlinarith

/-- **The large-height bound.** `|F(v)| ≤ C (Im v)^{1/4}` on `1 < Re v ≤ 3/2`, `Im v ≥ t₀ + 9`. -/
theorem exists_norm_defectSeries_le_large (hd : AdmissibleDefect w s) {c t₀ : ℝ} (hc : 0 ≤ c)
    (hcW : c * ∑' k, w k ≤ 2) (ht₀ : 0 < t₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℂ, 1 < v.re → v.re ≤ 3 / 2 → t₀ + 9 ≤ v.im →
      ‖∑' n : ℕ, (defectPattern c t₀ w s n : ℂ) * ((n : ℝ) : ℂ) ^ (-v)‖ ≤
        C * v.im ^ (1 / 4 : ℝ) := by
  obtain ⟨C₀, hC₀⟩ := RHTower.exists_norm_zetaEulerLog_le_large
  set W := ∑' k, w k
  have hW : 0 ≤ W := tsum_nonneg hd.nonneg
  set K : ℝ := Real.exp (3 * |C₀| + 4 * primeSquareMass)
  refine ⟨K * (2 * 108 ^ 27), by positivity, fun v hv hv2 hvy => ?_⟩
  set y := v.im
  have hy : 9 ≤ y := by linarith
  have hlog2y : 1 < Real.log (2 * y) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hΛ0 : 0 ≤ Real.log (Real.log (2 * y)) := Real.log_nonneg hlog2y.le
  set Λy : ℝ := 9 * Real.log (Real.log (2 * y)) + |C₀|
  have hΛy : 0 ≤ Λy := by positivity
  -- every `ζ` value in the model is bounded by `Λy`
  have hZ : ∀ v' : ℂ, 1 < v'.re → v'.re ≤ 2 → 9 ≤ v'.im → v'.im ≤ 2 * y →
      |Real.log ‖riemannZeta v'‖| ≤ Λy := by
    intro v' h1 h2 h9 h2y
    have hb := hC₀ v'.re v'.im h1 h2 (by rw [abs_of_pos (by linarith)]; exact h9)
    rw [Complex.re_add_im, abs_of_pos (by linarith)] at hb
    rw [← RHTower.re_zetaEulerLog h1]
    refine (Complex.abs_re_le_norm _).trans (hb.trans ?_)
    have hll : Real.log (Real.log v'.im) ≤ Real.log (Real.log (2 * y)) :=
      Real.log_le_log (Real.log_pos (by linarith)) (Real.log_le_log (by linarith) h2y)
    linarith [le_abs_self C₀]
  have hZm := hZ (v - t₀ * I) (by simpa using hv) (by simp; linarith) (by simp; linarith)
    (by simp; linarith)
  have hZp := hZ (v + t₀ * I) (by simpa using hv) (by simp; linarith) (by simp; linarith)
    (by simp; linarith)
  have hZk : ∀ k, |Real.log ‖riemannZeta (v + s k - t₀ * I)‖ +
      Real.log ‖riemannZeta (v + s k + t₀ * I)‖ - 0| ≤ 2 * Λy := fun k => by
    have hk := hd.pos k; have hk2 := hd.le_half k
    have h1 := hZ (v + s k - t₀ * I) (by simp; linarith) (by simp; linarith) (by simp; linarith)
      (by simp; linarith)
    have h2 := hZ (v + s k + t₀ * I) (by simp; linarith) (by simp; linarith) (by simp; linarith)
      (by simp; linarith)
    rw [sub_zero]
    exact (abs_add_le _ _).trans (by linarith)
  have hsum := abs_tsum_mul_sub_tsum_mul_le hd (b := fun _ => (0 : ℝ)) (B := 0)
    (fun _ => by simp) hZk
  simp only [mul_zero, tsum_zero, sub_zero] at hsum
  have hE := abs_log_norm_defectSeries_sub_le hd hc hcW t₀ hv
  have hS : 0 ≤ primeSquareMass := tsum_nonneg fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _
  set F := ‖∑' n : ℕ, (defectPattern c t₀ w s n : ℂ) * ((n : ℝ) : ℂ) ^ (-v)‖
  have hF0 : 0 < F := norm_pos_iff.mpr (defectSeries_ne_zero hd hc hcW t₀ hv)
  -- `log F ≤ (1 + cW) Λy + (2 + cW) S ≤ 3 Λy + 4 S`
  have hlogF : Real.log F ≤ 27 * Real.log (Real.log (2 * y)) + (3 * |C₀| + 4 * primeSquareMass) := by
    simp only [defectLogModel] at hE
    have hcs := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ c / 2)
    rw [← abs_of_nonneg (by positivity : (0 : ℝ) ≤ c / 2), ← abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ c / 2)] at hcs
    have hcW' : c / 2 * (W * (2 * Λy)) ≤ 2 * Λy := by
      have := mul_le_mul_of_nonneg_right hcW (by positivity : (0 : ℝ) ≤ Λy)
      nlinarith
    have hcS : c * W * primeSquareMass ≤ 2 * primeSquareMass := mul_le_mul_of_nonneg_right hcW hS
    rw [abs_le] at hE hcs hZm hZp
    nlinarith [hE.1, hE.2, hcs.1, hcs.2, hZm.1, hZm.2, hZp.1, hZp.2]
  have hpow : Real.exp (27 * Real.log (Real.log (2 * y))) = Real.log (2 * y) ^ 27 := by
    rw [show (27 : ℝ) * Real.log (Real.log (2 * y)) = Real.log (Real.log (2 * y) ^ 27) by
      rw [Real.log_pow]; push_cast; ring, Real.exp_log (pow_pos (by linarith) 27)]
  calc F = Real.exp (Real.log F) := (Real.exp_log hF0).symm
    _ ≤ Real.exp (27 * Real.log (Real.log (2 * y)) + (3 * |C₀| + 4 * primeSquareMass)) :=
        Real.exp_le_exp.mpr hlogF
    _ = K * Real.log (2 * y) ^ 27 := by rw [Real.exp_add, hpow, mul_comm]
    _ ≤ K * (2 * 108 ^ 27 * y ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (log_two_mul_pow_le (by linarith)) (Real.exp_pos _).le
    _ = K * (2 * 108 ^ 27) * y ^ (1 / 4 : ℝ) := by ring

/-! ### Payment -/

/-- **An integrable Dini density pays the receiver.** -/
theorem receiverBounded_defectWeight_of_integrableOn (hd : AdmissibleDefect w s) {c t₀ : ℝ}
    (hc : 0 ≤ c) (hcW : c * ∑' k, w k ≤ 2) (ht₀ : 0 < t₀)
    (hI : IntegrableOn (diniDensity c w s) (Ioc 0 1)) :
    ReceiverBounded (defectWeight c t₀ w s) := by
  set T : ℝ := t₀ + 11
  have hT : 2 ≤ T := by simp only [T]; linarith
  obtain ⟨B, hB⟩ := exists_abs_log_norm_defectSeries_sub_profile_le hd hc hcW ht₀
    (show 0 ≤ T by linarith)
  obtain ⟨Cl, hCl0, hCl⟩ := exists_norm_defectSeries_le_large hd hc hcW ht₀
  obtain ⟨Z₀, hZ₀, hZ⟩ := exists_norm_zeta_le_on_tall_box T
  set cw := defectWeight c t₀ w s
  set P : ℝ := ∑' d : ℕ, cw d / d
  set A : ℝ := 32 * Z₀ ^ 2 * Real.exp (2 * B)
  set A' : ℝ := 8 * Z₀ ^ 2 * P ^ 2
  have hA : 0 ≤ A := by positivity
  have hA' : 0 ≤ A' := by positivity
  set H : ℝ → ℝ := fun y => diniDensity c w s |y - t₀|
  have hH0 : ∀ y, 0 ≤ H y := fun y => diniDensity_nonneg c (abs_nonneg _)
  have hH : IntegrableOn H (Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
      (intervalIntegrable_diniDensity_abs_sub hd hc hcW hI t₀ 0 T)
  set ind : ℝ → ℝ → ℝ := fun σ =>
    (Ioo (t₀ - (σ - 1 / 2)) (t₀ + (σ - 1 / 2))).indicator (fun _ => (σ - 1 / 2)⁻¹)
  have hind0 : ∀ σ y : ℝ, 1 / 2 < σ → 0 ≤ ind σ y := fun σ y hσ =>
    indicator_nonneg (fun _ _ => inv_nonneg.mpr (by linarith)) y
  set g : ℝ → ℝ → ℝ := fun σ y => A * (ind σ y + H y) + A'
  have hwre : ∀ σ y : ℝ, ((σ : ℂ) + y * I + 1 / 2).re = σ + 1 / 2 := fun σ y => by simp
  have hwim : ∀ σ y : ℝ, ((σ : ℂ) + y * I + 1 / 2).im = y := fun σ y => by simp
  -- `|F(v)|² ≤ e^{2B} h(ρ)` on the box
  have hFsq : ∀ σ y : ℝ, 1 / 2 < σ → σ < 3 / 4 → 0 < y → y ≤ T →
      ‖∑' n : ℕ, (defectPattern c t₀ w s n : ℂ) * ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + y * I + 1 / 2))‖ ^ 2
        ≤ Real.exp (2 * B) * diniDensity c w s (σ - 1 / 2 + |y - t₀|) := by
    intro σ y hσ hσ' hy hyT
    have hb := hB ((σ : ℂ) + y * I + 1 / 2) (by rw [hwre]; linarith) (by rw [hwre]; linarith)
      (by rw [hwim]; linarith) (by rw [hwim]; exact hyT)
    rw [hwre, hwim, show σ + 1 / 2 - 1 = σ - 1 / 2 by ring] at hb
    exact sq_le_exp_mul_diniDensity
      (norm_pos_iff.mpr (defectSeries_ne_zero hd hc hcW t₀ (by rw [hwre]; linarith)))
      (by positivity) (abs_le.mp hb).2
  -- `h(ρ) ≤ 4 (ind + H)`
  have hdens : ∀ σ y : ℝ, 1 / 2 < σ → σ < 3 / 4 →
      diniDensity c w s (σ - 1 / 2 + |y - t₀|) ≤ 4 * (ind σ y + H y) := by
    intro σ y hσ hσ'
    have hu : 0 < σ - 1 / 2 := by linarith
    have hH0y := hH0 y
    rcases lt_or_ge |y - t₀| (σ - 1 / 2) with hlt | hge
    · have hmem : y ∈ Ioo (t₀ - (σ - 1 / 2)) (t₀ + (σ - 1 / 2)) := by
        rw [abs_lt] at hlt; constructor <;> linarith
      have hind : ind σ y = (σ - 1 / 2)⁻¹ := indicator_of_mem hmem _
      have h1 := diniDensity_le_inv hd hc (show 0 < σ - 1 / 2 + |y - t₀| by positivity)
        (by linarith [abs_nonneg (y - t₀)]) (w := w) (s := s)
      have h2 : (σ - 1 / 2 + |y - t₀|)⁻¹ ≤ (σ - 1 / 2)⁻¹ :=
        inv_anti₀ hu (by linarith [abs_nonneg (y - t₀)])
      have h3 : 0 ≤ (σ - 1 / 2)⁻¹ := inv_nonneg.mpr hu.le
      rw [hind]; linarith
    · have hx : 0 < |y - t₀| := lt_of_lt_of_le hu hge
      have h1 := diniDensity_le_four_mul hd hc hcW hx (ρ := σ - 1 / 2 + |y - t₀|) (by linarith)
        (by linarith) (w := w) (s := s)
      have h0 := hind0 σ y hσ
      simp only [H]; linarith
  have hsmall : ∀ σ y : ℝ, 1 / 2 < σ → σ < 3 / 4 → 0 < y → y ≤ T →
      lineIntegrand cw P σ y ≤ g σ y := by
    intro σ y hσ hσ' hy hyT
    have hF := (hFsq σ y hσ hσ' hy hyT).trans
      (mul_le_mul_of_nonneg_left (hdens σ y hσ hσ') (Real.exp_pos _).le)
    set Fn := ‖∑' n : ℕ, (defectPattern c t₀ w s n : ℂ) *
      ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + y * I + 1 / 2))‖
    have hC : ‖weightDirichletSeries cw ((σ : ℂ) + y * I) - (P : ℂ)‖ ≤ Fn + |P| := by
      rw [weightDirichletSeries_defectWeight]
      exact (norm_sub_le _ _).trans (by rw [Complex.norm_real, Real.norm_eq_abs])
    have hsq : ‖weightDirichletSeries cw ((σ : ℂ) + y * I) - (P : ℂ)‖ ^ 2 ≤
        2 * Fn ^ 2 + 2 * P ^ 2 := by
      have h := pow_le_pow_left₀ (norm_nonneg _) hC 2
      nlinarith [sq_nonneg (Fn - |P|), sq_abs P, norm_nonneg (∑' n : ℕ,
        (defectPattern c t₀ w s n : ℂ) * ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + y * I + 1 / 2)))]
    have hζ2 : ‖riemannZeta ((σ : ℂ) + y * I)‖ ^ 2 ≤ Z₀ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hZ σ y hσ.le hσ'.le (by rw [abs_of_pos hy]; exact hyT)) 2
    have hsn : σ ≤ ‖(σ : ℂ) + y * I‖ := by
      have := Complex.abs_re_le_norm ((σ : ℂ) + y * I)
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero] at this
      linarith [le_abs_self σ]
    have hs2 : (1 / 2 : ℝ) ^ 2 ≤ ‖(σ : ℂ) + y * I‖ ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have hden : 0 < ‖(σ : ℂ) + y * I‖ ^ 2 := lt_of_lt_of_le (by norm_num) hs2
    have hg0 : 0 ≤ g σ y := add_nonneg (mul_nonneg hA (add_nonneg (hind0 σ y hσ) (hH0 y))) hA'
    have hZF := mul_le_mul_of_nonneg_left hF (sq_nonneg Z₀)
    simp only [lineIntegrand, norm_div, norm_mul, div_pow, mul_pow]
    rw [div_le_iff₀ hden]
    calc ‖riemannZeta ((σ : ℂ) + y * I)‖ ^ 2 *
          ‖weightDirichletSeries cw ((σ : ℂ) + y * I) - (P : ℂ)‖ ^ 2
        ≤ Z₀ ^ 2 * (2 * Fn ^ 2 + 2 * P ^ 2) := mul_le_mul hζ2 hsq (sq_nonneg _) (by positivity)
      _ ≤ g σ y * (1 / 2) ^ 2 := by simp only [g, A, A']; nlinarith [hZF]
      _ ≤ g σ y * ‖(σ : ℂ) + y * I‖ ^ 2 := mul_le_mul_of_nonneg_left hs2 hg0
  have hindI : ∀ σ : ℝ, 1 / 2 < σ → IntegrableOn (ind σ) (Ioc 0 T) := fun σ _ =>
    (integrableOn_const (C := (σ - 1 / 2)⁻¹) measure_Ioc_lt_top.ne).indicator measurableSet_Ioo
  have hgI : ∀ σ : ℝ, 1 / 2 < σ → σ < 3 / 4 → IntegrableOn (g σ) (Ioc 0 T) := fun σ hσ _ =>
    (((hindI σ hσ).add hH).const_mul A).add
      (integrableOn_const (C := A') measure_Ioc_lt_top.ne)
  have hind2 : ∀ σ : ℝ, 1 / 2 < σ → ∫ y in Ioc 0 T, ind σ y ≤ 2 := by
    intro σ hσ
    have hu : 0 < σ - 1 / 2 := by linarith
    simp only [ind]
    rw [setIntegral_indicator measurableSet_Ioo, setIntegral_const, smul_eq_mul]
    have hm : volume.real (Ioc 0 T ∩ Ioo (t₀ - (σ - 1 / 2)) (t₀ + (σ - 1 / 2))) ≤
        2 * (σ - 1 / 2) := by
      refine (measureReal_mono inter_subset_right measure_Ioo_lt_top.ne).trans (le_of_eq ?_)
      rw [Real.volume_real_Ioo_of_le (by linarith)]; ring
    calc _ ≤ 2 * (σ - 1 / 2) * (σ - 1 / 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hm (inv_nonneg.mpr hu.le)
      _ = 2 := by rw [mul_assoc, mul_inv_cancel₀ hu.ne', mul_one]
  set G : ℝ := A * (2 + ∫ y in Ioc 0 T, H y) + A' * T
  have hgG : ∀ σ : ℝ, 1 / 2 < σ → σ < 3 / 4 → ∫ y in Ioc 0 T, g σ y ≤ G := by
    intro σ hσ _
    have hI1 : IntegrableOn (fun y => A * (ind σ y + H y)) (Ioc 0 T) :=
      ((hindI σ hσ).add hH).const_mul A
    have hI2 : IntegrableOn (fun _ : ℝ => A') (Ioc 0 T) :=
      integrableOn_const (C := A') measure_Ioc_lt_top.ne
    have hval : ∫ y in Ioc 0 T, g σ y =
        A * ((∫ y in Ioc 0 T, ind σ y) + ∫ y in Ioc 0 T, H y) + A' * T := by
      simp only [g]
      rw [integral_add hI1 hI2, integral_const_mul A (fun y => ind σ y + H y),
        integral_add (hindI σ hσ) hH, setIntegral_const, smul_eq_mul,
        Real.volume_real_Ioc_of_le (by linarith)]
      ring
    rw [hval]
    have := mul_le_mul_of_nonneg_left (hind2 σ hσ) hA
    simp only [G]; nlinarith
  have hlarge : ∀ σ y : ℝ, 1 / 2 < σ → σ < 3 / 4 → T < y →
      ‖weightDirichletSeries cw ((σ : ℂ) + y * I) - (P : ℂ)‖ ≤ (Cl + |P|) * y ^ (1 / 4 : ℝ) := by
    intro σ y hσ hσ' hy
    rw [weightDirichletSeries_defectWeight]
    refine (norm_sub_le _ _).trans ?_
    have h := hCl ((σ : ℂ) + y * I + 1 / 2) (by rw [hwre]; linarith) (by rw [hwre]; linarith)
      (by rw [hwim]; simp only [T] at hy; linarith)
    rw [hwim] at h
    have h1 : 1 ≤ y ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    rw [Complex.norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg P]
  obtain ⟨M, hM⟩ := exists_lineEnergy_le_of_majorant_family hT hgI hgG hsmall hlarge
  exact ⟨3 * M / (4 * Real.pi),
    weightPronicEnergy_le_of_lineEnergy_le (dampedClass_defectWeight hd hc hcW t₀) hM⟩

/-- **A critical zero pays the receiver**, whatever the defect. -/
theorem receiverBounded_defectWeight_of_zero (hd : AdmissibleDefect w s) {c t₀ : ℝ}
    (hc : 0 ≤ c) (hcW : c * ∑' k, w k ≤ 2) (ht₀ : 0 < t₀)
    (hz : riemannZeta (1 / 2 + t₀ * I) = 0) :
    ReceiverBounded (defectWeight c t₀ w s) := by
  have hs₀1 : (1 / 2 + t₀ * I : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; norm_num at this
  obtain ⟨rL, L, hrL, hL, hLip⟩ := exists_norm_zeta_sub_le hs₀1
  set T : ℝ := t₀ + 11
  have hT : 2 ≤ T := by simp only [T]; linarith
  obtain ⟨B, hB⟩ := exists_abs_log_norm_defectSeries_sub_profile_le hd hc hcW ht₀
    (show 0 ≤ T by linarith)
  obtain ⟨Cl, hCl0, hCl⟩ := exists_norm_defectSeries_le_large hd hc hcW ht₀
  obtain ⟨Z₀, hZ₀, hZ⟩ := exists_norm_zeta_le_on_tall_box T
  set cw := defectWeight c t₀ w s
  set P : ℝ := ∑' d : ℕ, cw d / d
  set r' : ℝ := min rL (1 / 2)
  have hr' : 0 < r' := lt_min hrL (by norm_num)
  set R : ℝ := 1 / 4 + T + t₀
  set E2 : ℝ := Real.exp (2 * B)
  set K₁ : ℝ := max (L ^ 2 * E2) (Z₀ ^ 2 * (E2 * ((1 + R) ^ 2 / r')))
  have hK₁ : 0 ≤ K₁ := le_max_of_le_left (by positivity)
  set A : ℝ := 4 * (2 * K₁ + 2 * Z₀ ^ 2 * P ^ 2)
  have hA : 0 ≤ A := by positivity
  have hwre : ∀ σ y : ℝ, ((σ : ℂ) + y * I + 1 / 2).re = σ + 1 / 2 := fun σ y => by simp
  have hwim : ∀ σ y : ℝ, ((σ : ℂ) + y * I + 1 / 2).im = y := fun σ y => by simp
  have hsmall : ∀ σ y : ℝ, 1 / 2 < σ → σ < 3 / 4 → 0 < y → y ≤ T → y ≠ t₀ →
      lineIntegrand cw P σ y ≤ (fun _ : ℝ => A) y := by
    intro σ y hσ hσ' hy hyT _
    set ρ : ℝ := σ - 1 / 2 + |y - t₀|
    have hρ : 0 < ρ := by simp only [ρ]; have : 0 < σ - 1 / 2 := by linarith
                          positivity
    have hρR : ρ ≤ R := by
      simp only [ρ, R]
      have : |y - t₀| ≤ T + t₀ := by rw [abs_le]; constructor <;> linarith
      linarith
    have hb := hB ((σ : ℂ) + y * I + 1 / 2) (by rw [hwre]; linarith) (by rw [hwre]; linarith)
      (by rw [hwim]; linarith) (by rw [hwim]; exact hyT)
    rw [hwre, hwim, show σ + 1 / 2 - 1 = σ - 1 / 2 by ring] at hb
    set Fn := ‖∑' n : ℕ, (defectPattern c t₀ w s n : ℂ) *
      ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + y * I + 1 / 2))‖
    have hF : Fn ^ 2 ≤ E2 * diniDensity c w s ρ :=
      sq_le_exp_mul_diniDensity
        (norm_pos_iff.mpr (defectSeries_ne_zero hd hc hcW t₀ (by rw [hwre]; linarith)))
        hρ (abs_le.mp hb).2
    have hζZ : ‖riemannZeta ((σ : ℂ) + y * I)‖ ≤ Z₀ :=
      hZ σ y hσ.le hσ'.le (by rw [abs_of_pos hy]; exact hyT)
    -- `|ζ(s)|² |F|² ≤ K₁`
    have hkey : ‖riemannZeta ((σ : ℂ) + y * I)‖ ^ 2 * Fn ^ 2 ≤ K₁ := by
      rcases le_or_gt ρ r' with hρr | hρr
      · have hd' : ‖(σ : ℂ) + y * I - (1 / 2 + t₀ * I)‖ ≤ ρ := by
          have := Complex.norm_le_abs_re_add_abs_im ((σ : ℂ) + y * I - (1 / 2 + t₀ * I))
          have hre : ((σ : ℂ) + y * I - (1 / 2 + t₀ * I)).re = σ - 1 / 2 := by simp
          have him : ((σ : ℂ) + y * I - (1 / 2 + t₀ * I)).im = y - t₀ := by simp
          rw [hre, him, abs_of_pos (by linarith)] at this
          exact this
        have hζ : ‖riemannZeta ((σ : ℂ) + y * I)‖ ≤ L * ρ := by
          have := hLip ((σ : ℂ) + y * I) (hd'.trans (hρr.trans (min_le_left _ _)))
          rw [hz, sub_zero] at this
          exact this.trans (mul_le_mul_of_nonneg_left hd' hL)
        have hh := diniDensity_le_inv hd hc hρ (hρr.trans (min_le_right _ _)) (w := w) (s := s)
        have hζ2 : ‖riemannZeta ((σ : ℂ) + y * I)‖ ^ 2 ≤ L ^ 2 * ρ ^ 2 := by
          have := pow_le_pow_left₀ (norm_nonneg _) hζ 2; rwa [mul_pow] at this
        have hF' : Fn ^ 2 ≤ E2 * ρ⁻¹ := hF.trans (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le)
        calc _ ≤ L ^ 2 * ρ ^ 2 * (E2 * ρ⁻¹) := mul_le_mul hζ2 hF' (sq_nonneg _) (by positivity)
          _ = L ^ 2 * E2 * ρ := by field_simp
          _ ≤ L ^ 2 * E2 * 1 := mul_le_mul_of_nonneg_left (by
                linarith [min_le_right rL (1 / 2 : ℝ)]) (by positivity)
          _ ≤ K₁ := by rw [mul_one]; exact le_max_left _ _
      · have hh := diniDensity_le_of_mem hd hc hcW hr' hρr.le hρR (w := w) (s := s)
        have hζ2 : ‖riemannZeta ((σ : ℂ) + y * I)‖ ^ 2 ≤ Z₀ ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hζZ 2
        calc _ ≤ Z₀ ^ 2 * (E2 * ((1 + R) ^ 2 / r')) :=
              mul_le_mul hζ2 (hF.trans (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le))
                (sq_nonneg _) (sq_nonneg _)
          _ ≤ K₁ := le_max_right _ _
    have hC : ‖weightDirichletSeries cw ((σ : ℂ) + y * I) - (P : ℂ)‖ ≤ Fn + |P| := by
      rw [weightDirichletSeries_defectWeight]
      exact (norm_sub_le _ _).trans (by rw [Complex.norm_real, Real.norm_eq_abs])
    have hsq : ‖weightDirichletSeries cw ((σ : ℂ) + y * I) - (P : ℂ)‖ ^ 2 ≤
        2 * Fn ^ 2 + 2 * P ^ 2 := by
      have h := pow_le_pow_left₀ (norm_nonneg _) hC 2
      nlinarith [sq_nonneg (Fn - |P|), sq_abs P, norm_nonneg (∑' n : ℕ,
        (defectPattern c t₀ w s n : ℂ) * ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + y * I + 1 / 2)))]
    have hsn : σ ≤ ‖(σ : ℂ) + y * I‖ := by
      have := Complex.abs_re_le_norm ((σ : ℂ) + y * I)
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero] at this
      linarith [le_abs_self σ]
    have hs2 : (1 / 2 : ℝ) ^ 2 ≤ ‖(σ : ℂ) + y * I‖ ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have hden : 0 < ‖(σ : ℂ) + y * I‖ ^ 2 := lt_of_lt_of_le (by norm_num) hs2
    have hζ2 : ‖riemannZeta ((σ : ℂ) + y * I)‖ ^ 2 ≤ Z₀ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hζZ 2
    show lineIntegrand cw P σ y ≤ A
    simp only [lineIntegrand, norm_div, norm_mul, div_pow, mul_pow]
    rw [div_le_iff₀ hden]
    have hP2 := mul_le_mul_of_nonneg_right hζ2 (sq_nonneg P)
    calc ‖riemannZeta ((σ : ℂ) + y * I)‖ ^ 2 *
          ‖weightDirichletSeries cw ((σ : ℂ) + y * I) - (P : ℂ)‖ ^ 2
        ≤ ‖riemannZeta ((σ : ℂ) + y * I)‖ ^ 2 * (2 * Fn ^ 2 + 2 * P ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ ≤ A * (1 / 2) ^ 2 := by simp only [A]; nlinarith [hkey, hP2]
      _ ≤ A * ‖(σ : ℂ) + y * I‖ ^ 2 := mul_le_mul_of_nonneg_left hs2 hA
  have hlarge : ∀ σ y : ℝ, 1 / 2 < σ → σ < 3 / 4 → T < y →
      ‖weightDirichletSeries cw ((σ : ℂ) + y * I) - (P : ℂ)‖ ≤ (Cl + |P|) * y ^ (1 / 4 : ℝ) := by
    intro σ y hσ hσ' hy
    rw [weightDirichletSeries_defectWeight]
    refine (norm_sub_le _ _).trans ?_
    have h := hCl ((σ : ℂ) + y * I + 1 / 2) (by rw [hwre]; linarith) (by rw [hwre]; linarith)
      (by rw [hwim]; simp only [T] at hy; linarith)
    rw [hwim] at h
    have h1 : 1 ≤ y ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    rw [Complex.norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg P]
  have hg : IntegrableOn (fun _ : ℝ => A) (Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp intervalIntegrable_const
  obtain ⟨M, hM⟩ := exists_lineEnergy_le_of_majorant (g := fun _ : ℝ => A) hT hg hsmall hlarge
  exact ⟨3 * M / (4 * Real.pi),
    weightPronicEnergy_le_of_lineEnergy_le (dampedClass_defectWeight hd hc hcW t₀) hM⟩

/-! ### The obstruction -/

/-- **A paid receiver forces an integrable Dini density** when `ζ(1/2 + it₀) ≠ 0`: on the segment
`t₀ ≤ t ≤ t₀ + r` the line integrand at `σ = 1/2 + u` is `≥ κ h(u + τ) − C'`, so the line energy
`≤ 4πE` bounds `∫_u^r h` uniformly in `u`. -/
theorem integrableOn_diniDensity_of_receiverBounded (hd : AdmissibleDefect w s) {c t₀ : ℝ}
    (hc : 0 ≤ c) (hcW : c * ∑' k, w k ≤ 2) (ht₀ : 0 < t₀)
    (hz : riemannZeta (1 / 2 + t₀ * I) ≠ 0) (hR : ReceiverBounded (defectWeight c t₀ w s)) :
    IntegrableOn (diniDensity c w s) (Ioc 0 1) := by
  obtain ⟨E, hE⟩ := hR
  set cw := defectWeight c t₀ w s
  have hcd : DampedClass 1 (1 / 2) cw := dampedClass_defectWeight hd hc hcW t₀
  set m : ℝ := ∑' d : ℕ, cw d / d
  have hs₀1 : (1 / 2 + (t₀ : ℂ) * I : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; norm_num at this
  obtain ⟨r₀, hr₀, hζ0⟩ := exists_norm_zeta_gt_near hs₀1 hz
  obtain ⟨B, hB⟩ := exists_abs_log_norm_defectSeries_sub_profile_le hd hc hcW ht₀ (T := t₀ + 1)
    (by linarith)
  have hc₀ : 0 < ‖riemannZeta (1 / 2 + (t₀ : ℂ) * I)‖ := norm_pos_iff.mpr hz
  set r : ℝ := min (r₀ / 4) (1 / 4)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hr4 : r ≤ 1 / 4 := min_le_right _ _
  have hrr₀ : 2 * r < r₀ := by have := min_le_left (r₀ / 4) (1 / 4); linarith
  set A₀ : ℝ :=
    ((‖riemannZeta (1 / 2 + (t₀ : ℂ) * I)‖ / 2) / (‖(1 / 2 + (t₀ : ℂ) * I : ℂ)‖ + 1)) ^ 2
  have hA₀ : 0 < A₀ := by positivity
  set κ : ℝ := A₀ * Real.exp (-(2 * B)) / 2
  have hκ : 0 < κ := by positivity
  set C' : ℝ := A₀ * m ^ 2
  -- the pointwise lower bound on the segment
  have hpt : ∀ u τ : ℝ, 0 < u → u ≤ r → 0 ≤ τ → τ ≤ r →
      κ * diniDensity c w s (u + τ) - C' ≤ lineIntegrand cw m (1 / 2 + u) (t₀ + τ) := by
    intro u τ hu hur hτ hτr
    set s' : ℂ := ((1 / 2 + u : ℝ) : ℂ) + ((t₀ + τ : ℝ) : ℂ) * I
    have hss₀ : s' - (1 / 2 + (t₀ : ℂ) * I) = (u : ℂ) + (τ : ℂ) * I := by
      simp only [s']; push_cast; ring
    have hnorm_ut : ‖(u : ℂ) + (τ : ℂ) * I‖ ≤ u + τ := by
      have := Complex.norm_le_abs_re_add_abs_im ((u : ℂ) + (τ : ℂ) * I)
      simpa [abs_of_pos hu, abs_of_nonneg hτ] using this
    have hut : 0 < u + τ := by linarith
    have hζs := hζ0 s' (by rw [hss₀]; linarith)
    have hs1 : ‖s'‖ ≤ ‖(1 / 2 + (t₀ : ℂ) * I : ℂ)‖ + 1 := by
      have h : ‖s'‖ ≤ ‖(1 / 2 + (t₀ : ℂ) * I : ℂ)‖ + ‖s' - (1 / 2 + (t₀ : ℂ) * I)‖ := by
        calc ‖s'‖ = ‖(1 / 2 + (t₀ : ℂ) * I : ℂ) + (s' - (1 / 2 + (t₀ : ℂ) * I))‖ := by
              congr 1; ring
          _ ≤ _ := norm_add_le _ _
      rw [hss₀] at h; linarith
    have hsre : s'.re = 1 / 2 + u := by simp [s']
    have hs0 : 0 < ‖s'‖ := by
      have := Complex.abs_re_le_norm s'
      rw [hsre, abs_of_pos (by linarith)] at this; linarith
    set v : ℂ := ((1 + u : ℝ) : ℂ) + ((t₀ + τ : ℝ) : ℂ) * I
    have hw_eq : s' + 1 / 2 = v := by simp only [s', v]; push_cast; ring
    have hvre : v.re = 1 + u := by simp [v]
    have hvim : v.im = t₀ + τ := by simp [v]
    have hb := hB v (by rw [hvre]; linarith) (by rw [hvre]; linarith) (by rw [hvim]; linarith)
      (by rw [hvim]; linarith)
    have hρ : v.re - 1 + |v.im - t₀| = u + τ := by
      rw [hvre, hvim, show t₀ + τ - t₀ = τ by ring, abs_of_nonneg hτ]; ring
    rw [hρ] at hb
    set Pn := ‖∑' n : ℕ, (defectPattern c t₀ w s n : ℂ) * ((n : ℝ) : ℂ) ^ (-v)‖
    have hPn0 : 0 < Pn :=
      norm_pos_iff.mpr (defectSeries_ne_zero hd hc hcW t₀ (by rw [hvre]; linarith))
    have hP2 : Real.exp (-(2 * B)) * diniDensity c w s (u + τ) ≤ Pn ^ 2 :=
      exp_mul_diniDensity_le_sq hPn0 hut (abs_le.mp hb).1
    set Y := ‖weightDirichletSeries cw s' - (m : ℂ)‖
    have hPY : Pn ≤ Y + |m| := by
      have h := norm_sub_norm_le (weightDirichletSeries cw s') (m : ℂ)
      have hW : ‖weightDirichletSeries cw s'‖ = Pn := by
        rw [weightDirichletSeries_defectWeight, hw_eq]
      rw [hW, Complex.norm_real, Real.norm_eq_abs] at h
      linarith
    have hY0 : 0 ≤ Y := norm_nonneg _
    have hYP : Pn ^ 2 / 2 - m ^ 2 ≤ Y ^ 2 := by
      have h := pow_le_pow_left₀ hPn0.le hPY 2
      nlinarith [sq_nonneg (Y - |m|), sq_abs m]
    have hint : lineIntegrand cw m (1 / 2 + u) (t₀ + τ) = (‖riemannZeta s'‖ * Y / ‖s'‖) ^ 2 := by
      simp only [lineIntegrand, norm_div, norm_mul]; rfl
    rw [hint]
    have hbound := sq_div_ge_of_bounds (by positivity) hζs.le hs0 hs1 hY0 hYP hP2
    refine le_trans (le_of_eq ?_) hbound
    simp only [κ, C', A₀]
    ring
  have hE0 : 0 ≤ E := by simpa [weightPronicEnergy] using hE 0
  -- a paid receiver caps every line energy by `4πE`
  have hup : ∀ u : ℝ, 0 < u → u ≤ r →
      ∫ t, lineIntegrand cw m (1 / 2 + u) t ≤ 4 * Real.pi * E := by
    intro u hu hur
    have hσ : 1 / 2 < 1 / 2 + u := by linarith
    have hσ1 : 1 / 2 + u < 1 := by linarith
    have hid := sum_sq_mul_mellinCell_eq_lineEnergy hcd hσ hσ1
    have hcap := tsum_sq_mul_mellinCell_le_of_energy (weightCenteredPrefix_zero cw m) hσ.le hE
    have h : (1 / 2 + u) / Real.pi * ∫ t, lineIntegrand cw m (1 / 2 + u) t ≤
        4 * (1 / 2 + u) * E := hid.symm.le.trans hcap
    have hpi := Real.pi_pos
    rw [div_mul_eq_mul_div, div_le_iff₀ hpi] at h
    nlinarith
  -- the segment carries `κ ∫_u^r h − C' r`
  have hlow : ∀ u : ℝ, 0 < u → u ≤ r →
      κ * (∫ x in Ioc u r, diniDensity c w s x) - C' * r ≤
        ∫ t, lineIntegrand cw m (1 / 2 + u) t := by
    intro u hu hur
    have hσ : 1 / 2 < 1 / 2 + u := by linarith
    have hσ1 : 1 / 2 + u < 1 := by linarith
    have hfi : Integrable (lineIntegrand cw m (1 / 2 + u)) := integrable_lineEnergy hcd hσ hσ1
    have hf0 : 0 ≤ᵐ[volume] lineIntegrand cw m (1 / 2 + u) :=
      Eventually.of_forall fun t => by simp only [Pi.zero_apply, lineIntegrand]; positivity
    have hhi : IntervalIntegrable (diniDensity c w s) volume u (u + r) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
        (integrableOn_diniDensity_Ioc hd hc hcW hu)
    have hsh : IntervalIntegrable (fun τ => diniDensity c w s (u + τ)) volume 0 r := by
      simpa using hhi.comp_add_left u
    have hg : IntervalIntegrable (fun τ : ℝ => κ * diniDensity c w s (u + τ) - C') volume 0 r :=
      (hsh.const_mul κ).sub intervalIntegrable_const
    have hval : ∫ τ in (0 : ℝ)..r, (κ * diniDensity c w s (u + τ) - C') =
        κ * (∫ x in u..u + r, diniDensity c w s x) - C' * r := by
      rw [intervalIntegral.integral_sub (hsh.const_mul κ) intervalIntegrable_const,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_add_left (fun x => diniDensity c w s x) u, add_zero,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    have hmono : ∫ x in Ioc u r, diniDensity c w s x ≤ ∫ x in u..u + r, diniDensity c w s x := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      refine setIntegral_mono_set (integrableOn_diniDensity_Ioc hd hc hcW hu) ?_
        (Ioc_subset_Ioc_right (by linarith)).eventuallyLE
      exact (ae_restrict_iff' measurableSet_Ioc).mpr
        (Eventually.of_forall fun x hx => diniDensity_nonneg c (by linarith [hx.1]))
    have hfs : IntervalIntegrable (fun τ => lineIntegrand cw m (1 / 2 + u) (t₀ + τ)) volume 0 r :=
      (hfi.comp_add_left t₀).intervalIntegrable
    have hshift : ∫ τ in (0 : ℝ)..r, lineIntegrand cw m (1 / 2 + u) (t₀ + τ) =
        ∫ t in t₀..t₀ + r, lineIntegrand cw m (1 / 2 + u) t := by
      rw [intervalIntegral.integral_comp_add_left (fun t => lineIntegrand cw m (1 / 2 + u) t) t₀,
        add_zero]
    calc κ * (∫ x in Ioc u r, diniDensity c w s x) - C' * r
        ≤ κ * (∫ x in u..u + r, diniDensity c w s x) - C' * r := by
          have := mul_le_mul_of_nonneg_left hmono hκ.le; linarith
      _ = ∫ τ in (0 : ℝ)..r, (κ * diniDensity c w s (u + τ) - C') := hval.symm
      _ ≤ ∫ τ in (0 : ℝ)..r, lineIntegrand cw m (1 / 2 + u) (t₀ + τ) :=
          intervalIntegral.integral_mono_on hr.le hg hfs fun τ hτ =>
            hpt u τ hu hur hτ.1 hτ.2
      _ = ∫ t in t₀..t₀ + r, lineIntegrand cw m (1 / 2 + u) t := hshift
      _ = ∫ t in Ioc t₀ (t₀ + r), lineIntegrand cw m (1 / 2 + u) t :=
          intervalIntegral.integral_of_le (by linarith)
      _ ≤ ∫ t, lineIntegrand cw m (1 / 2 + u) t := setIntegral_le_integral hfi hf0
  -- uniform bound on `∫_u^r h`
  set Ib : ℝ := (4 * Real.pi * E + C' * r) / κ
  have hbd : ∀ u : ℝ, 0 < u → u ≤ r → ∫ x in Ioc u r, diniDensity c w s x ≤ Ib := by
    intro u hu hur
    have h1 := hlow u hu hur
    have h2 := hup u hu hur
    rw [le_div_iff₀ hκ]
    linarith
  set a : ℕ → ℝ := fun n => r * (1 / ((n : ℝ) + 1))
  have ha0 : ∀ n, 0 < a n := fun n => by simp only [a]; positivity
  have har : ∀ n, a n ≤ r := fun n => by
    simp only [a]
    refine mul_le_of_le_one_right hr.le ?_
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hat : Tendsto a atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul r
    rwa [mul_zero] at this
  have hIr : IntegrableOn (diniDensity c w s) (Ioc 0 r) := by
    refine integrableOn_Ioc_of_intervalIntegral_norm_bounded_left (I := Ib)
      (fun n => integrableOn_diniDensity_Ioc hd hc hcW (ha0 n)) hat
      (Eventually.of_forall fun n => ?_)
    rw [setIntegral_congr_fun measurableSet_Ioc (g := diniDensity c w s) fun x hx =>
      Real.norm_of_nonneg (diniDensity_nonneg c (by linarith [hx.1, ha0 n]))]
    exact hbd (a n) (ha0 n) (har n)
  rw [← Ioc_union_Ioc_eq_Ioc hr.le (by linarith : r ≤ 1)]
  exact hIr.union (integrableOn_diniDensity_Ioc hd hc hcW hr)

/-! ### The phase diagram -/

/-- **The Dini law of completely monotone amplitude defects.** For admissible defect data,
`c ≥ 0` with `cW ≤ 2` and `t₀ > 0`, the half-damped weight of
`f(p) = (1 − c Σ_k w_k p^{-s_k}) cos(t₀ log p)` has bounded receiver if and only if the Dini density
`e^{−cΛ(ρ)}/ρ` is integrable on `(0, 1]` or `ζ(1/2 + it₀) = 0`. -/
theorem receiverBounded_defectWeight_iff (hd : AdmissibleDefect w s) {c t₀ : ℝ} (hc : 0 ≤ c)
    (hcW : c * ∑' k, w k ≤ 2) (ht₀ : 0 < t₀) :
    ReceiverBounded (defectWeight c t₀ w s) ↔
      IntegrableOn (diniDensity c w s) (Ioc 0 1) ∨ riemannZeta (1 / 2 + t₀ * I) = 0 := by
  refine ⟨fun h => ?_, fun h => h.elim (receiverBounded_defectWeight_of_integrableOn hd hc hcW ht₀)
    (receiverBounded_defectWeight_of_zero hd hc hcW ht₀)⟩
  by_cases hz : riemannZeta (1 / 2 + t₀ * I) = 0
  · exact Or.inr hz
  · exact Or.inl (integrableOn_diniDensity_of_receiverBounded hd hc hcW ht₀ hz h)

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
