import GaloisForLFunctions.HTGeometry.CanonicalEulerLog
import GaloisForLFunctions.RHTower.EulerTiltCovariance

/-!
# The Euler logarithm of zeta as a prime cosine sum

On the abscissa `σ > 1` the logarithmic modulus of the zeta function is the prime cosine sum

```text
log |ζ(σ + iτ)| = ∑_p p^{-σ} cos(τ log p) + O(1),
```

with the error carried entirely by the absolutely convergent prime-power correction: the local
logarithm `-log(1 - z)` differs from `z` by at most `‖z‖²/(1-‖z‖)/2`, which at a prime is bounded
by `p^{-2}`.
-/

open Filter Topology Complex

namespace RHTower

noncomputable section

/-- The point `σ + iτ` on a vertical line. -/
def zetaLinePoint (σ τ : ℝ) : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I

@[simp]
theorem zetaLinePoint_re (σ τ : ℝ) : (zetaLinePoint σ τ).re = σ := by
  rw [zetaLinePoint]
  simp

/-- On `Re s > 1` the logarithmic modulus of zeta is the real part of its canonical Euler
logarithm. -/
theorem log_norm_riemannZeta_eq_re_eulerLog {s : ℂ} (hs : 1 < s.re) :
    Real.log ‖riemannZeta s‖ = (canonicalEulerLogZeta s).re := by
  rw [← exp_canonicalEulerLogZeta_eq_riemannZeta hs, Complex.norm_exp, Real.log_exp]

/-- The prime cosine sum `∑_p p^{-σ} cos(τ log p)`. -/
def primeCosTsum (σ τ : ℝ) : ℝ :=
  ∑' p : Nat.Primes, (p : ℝ) ^ (-σ) * Real.cos (τ * Real.log p)

theorem natCast_cpow_neg_zetaLinePoint {p : ℕ} (hp : 0 < p) (σ τ : ℝ) :
    ((p : ℂ) ^ (-(zetaLinePoint σ τ)))
      = ((p : ℝ) ^ (-σ) : ℝ) * Complex.exp ((-(τ * Real.log p) : ℝ) * Complex.I) := by
  have hp0 : ((p : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    simpa using (by exact_mod_cast hp.ne' : (p : ℂ) ≠ 0)
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [Complex.cpow_def_of_ne_zero hp0, ← Complex.natCast_log, zetaLinePoint]
  have hval : (↑(Real.log p) : ℂ) * -((σ : ℂ) + (τ : ℂ) * Complex.I)
      = ((-σ * Real.log p : ℝ) : ℂ) + ((-(τ * Real.log p) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hval, Complex.exp_add]
  congr 1
  rw [Real.rpow_def_of_pos hpR]
  rw [← Complex.ofReal_exp]
  congr 1
  ring

theorem re_natCast_cpow_neg_zetaLinePoint {p : ℕ} (hp : 0 < p) (σ τ : ℝ) :
    ((p : ℂ) ^ (-(zetaLinePoint σ τ))).re = (p : ℝ) ^ (-σ) * Real.cos (τ * Real.log p) := by
  rw [natCast_cpow_neg_zetaLinePoint hp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hcos : Real.cos (-(τ * Real.log p)) = Real.cos (τ * Real.log p) := Real.cos_neg _
  rw [hcos]
  ring

theorem norm_natCast_cpow_neg_zetaLinePoint {p : ℕ} (hp : 0 < p) (σ τ : ℝ) :
    ‖(p : ℂ) ^ (-(zetaLinePoint σ τ))‖ = (p : ℝ) ^ (-σ) := by
  rw [natCast_cpow_neg_zetaLinePoint hp, norm_mul, Complex.norm_real, Complex.norm_exp]
  have hre : ((-(τ * Real.log p) : ℝ) * Complex.I).re = 0 := by
    rw [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hre, Real.exp_zero, mul_one]
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  exact Real.norm_of_nonneg (Real.rpow_nonneg hpR.le _)

theorem summable_primeRpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-σ)) :=
  Nat.Primes.summable_rpow.mpr (by linarith)

theorem summable_primeCos {σ τ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-σ) * Real.cos (τ * Real.log p)) := by
  refine Summable.of_norm_bounded (summable_primeRpow hσ) fun p => ?_
  have hpR : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.pos
  have hnn : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg hpR.le _
  rw [norm_mul, Real.norm_of_nonneg hnn]
  have hcos : ‖Real.cos (τ * Real.log p)‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  nlinarith [hcos, hnn]

theorem norm_primeRpow_le_half {σ : ℝ} (hσ : 1 ≤ σ) (p : Nat.Primes) :
    ((p : ℕ) : ℝ) ^ (-σ) ≤ 1 / 2 := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
  have hstep : ((p : ℕ) : ℝ) ^ (-σ) ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hinv : ((p : ℕ) : ℝ) ^ (-1 : ℝ) = (((p : ℕ) : ℝ))⁻¹ := Real.rpow_neg_one _
  rw [hinv] at hstep
  have hle : (((p : ℕ) : ℝ))⁻¹ ≤ 1 / 2 := by
    rw [one_div, inv_le_inv₀ (by linarith) (by norm_num)]
    exact hp2
  linarith

/-! ## The local logarithm bound -/

theorem norm_log_one_sub_sub_self_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.log (1 - z) + z‖ ≤ ‖z‖ ^ 2 := by
  have hlt : ‖-z‖ < 1 := by
    rw [norm_neg]
    linarith
  have hbound := Complex.norm_log_one_add_sub_self_le hlt
  rw [norm_neg] at hbound
  have hsub : (1 : ℂ) + -z = 1 - z := by ring
  rw [hsub] at hbound
  have hval : Complex.log (1 - z) - -z = Complex.log (1 - z) + z := by ring
  rw [hval] at hbound
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hznn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  nlinarith [hbound, hinv, hznn, sq_nonneg ‖z‖]

theorem norm_log_one_sub_le_two_mul {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.log (1 - z)‖ ≤ 2 * ‖z‖ := by
  have h := norm_log_one_sub_sub_self_le hz
  have htri : ‖Complex.log (1 - z)‖ ≤ ‖Complex.log (1 - z) + z‖ + ‖z‖ := by
    have := norm_sub_le (Complex.log (1 - z) + z) z
    have hval : Complex.log (1 - z) + z - z = Complex.log (1 - z) := by ring
    rw [hval] at this
    exact this
  have hznn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  nlinarith [h, htri, hznn]

theorem abs_re_neg_log_one_sub_sub_re_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    |(-Complex.log (1 - z)).re - z.re| ≤ ‖z‖ ^ 2 := by
  have h := norm_log_one_sub_sub_self_le hz
  have hval : (-Complex.log (1 - z)).re - z.re = -((Complex.log (1 - z) + z).re) := by
    simp [Complex.add_re, Complex.neg_re]
  rw [hval, abs_neg]
  exact le_trans (Complex.abs_re_le_norm _) h

/-! ## The prime sum -/

theorem summable_primeEulerLog {σ τ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes =>
      -Complex.log (1 - (p : ℂ) ^ (-(zetaLinePoint σ τ)))) := by
  have hmajor : Summable (fun p : Nat.Primes => 2 * (((p : ℕ) : ℝ) ^ (-σ))) :=
    (summable_primeRpow hσ).mul_left 2
  refine Summable.of_norm_bounded hmajor fun p => ?_
  have hp0 : 0 < (p : ℕ) := p.prop.pos
  have hz : ‖(p : ℂ) ^ (-(zetaLinePoint σ τ))‖ = ((p : ℕ) : ℝ) ^ (-σ) :=
    norm_natCast_cpow_neg_zetaLinePoint hp0 σ τ
  have hhalf : ‖(p : ℂ) ^ (-(zetaLinePoint σ τ))‖ ≤ 1 / 2 := by
    rw [hz]
    exact norm_primeRpow_le_half (le_of_lt hσ) p
  rw [norm_neg]
  have := norm_log_one_sub_le_two_mul hhalf
  rwa [hz] at this

theorem primeRpow_sq_le_invSq {σ : ℝ} (hσ : 1 ≤ σ) (p : Nat.Primes) :
    (((p : ℕ) : ℝ) ^ (-σ)) ^ 2 ≤ 1 / ((p : ℕ) : ℝ) ^ (2 : ℝ) := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have hstep : ((p : ℕ) : ℝ) ^ (-σ) ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hnn : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg hp0.le _
  have hinvnn : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) := Real.rpow_nonneg hp0.le _
  have hsq : (((p : ℕ) : ℝ) ^ (-σ)) ^ 2 ≤ (((p : ℕ) : ℝ) ^ (-1 : ℝ)) ^ 2 := by
    nlinarith [hstep, hnn, hinvnn]
  have hval : (((p : ℕ) : ℝ) ^ (-1 : ℝ)) ^ 2 = 1 / ((p : ℕ) : ℝ) ^ (2 : ℝ) := by
    rw [← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-1 : ℝ)) 2, ← Real.rpow_mul hp0.le]
    rw [show (-1 : ℝ) * ((2 : ℕ) : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hp0.le, one_div]
  rw [hval] at hsq
  exact hsq

/-- **The Euler logarithm is the prime cosine sum up to an absolutely convergent correction.** -/
theorem abs_re_eulerLog_sub_primeCosTsum_le {σ τ : ℝ} (hσ : 1 < σ) :
    |(canonicalEulerLogZeta (zetaLinePoint σ τ)).re - primeCosTsum σ τ|
      ≤ invSquareTailConst := by
  have hre : 1 < (zetaLinePoint σ τ).re := by
    rw [zetaLinePoint_re]
    exact hσ
  have heq := canonicalEulerLogZeta_eq_primeLog hre
  have hsummable := summable_primeEulerLog (σ := σ) (τ := τ) hσ
  have hcos := summable_primeCos (σ := σ) (τ := τ) hσ
  have hresum : (canonicalEulerLogZeta (zetaLinePoint σ τ)).re
      = ∑' p : Nat.Primes, (-Complex.log (1 - (p : ℂ) ^ (-(zetaLinePoint σ τ)))).re := by
    rw [heq]
    exact Complex.re_tsum hsummable
  have hresumdiff : Summable (fun p : Nat.Primes =>
      (-Complex.log (1 - (p : ℂ) ^ (-(zetaLinePoint σ τ)))).re) :=
    hsummable.re
  have hcosre : primeCosTsum σ τ
      = ∑' p : Nat.Primes, ((p : ℂ) ^ (-(zetaLinePoint σ τ))).re := by
    rw [primeCosTsum]
    exact tsum_congr fun p => (re_natCast_cpow_neg_zetaLinePoint p.prop.pos σ τ).symm
  have hcosre_summable : Summable (fun p : Nat.Primes =>
      ((p : ℂ) ^ (-(zetaLinePoint σ τ))).re) := by
    refine hcos.congr fun p => ?_
    exact (re_natCast_cpow_neg_zetaLinePoint p.prop.pos σ τ).symm
  rw [hresum, hcosre, ← hresumdiff.tsum_sub hcosre_summable]
  have hbound : ∀ p : Nat.Primes,
      |(-Complex.log (1 - (p : ℂ) ^ (-(zetaLinePoint σ τ)))).re
        - ((p : ℂ) ^ (-(zetaLinePoint σ τ))).re| ≤ 1 / ((p : ℕ) : ℝ) ^ (2 : ℝ) := by
    intro p
    have hp0 : 0 < (p : ℕ) := p.prop.pos
    have hz : ‖(p : ℂ) ^ (-(zetaLinePoint σ τ))‖ = ((p : ℕ) : ℝ) ^ (-σ) :=
      norm_natCast_cpow_neg_zetaLinePoint hp0 σ τ
    have hhalf : ‖(p : ℂ) ^ (-(zetaLinePoint σ τ))‖ ≤ 1 / 2 := by
      rw [hz]
      exact norm_primeRpow_le_half (le_of_lt hσ) p
    have h := abs_re_neg_log_one_sub_sub_re_le hhalf
    rw [hz] at h
    exact le_trans h (primeRpow_sq_le_invSq (le_of_lt hσ) p)
  have hinvsum : Summable (fun p : Nat.Primes => 1 / ((p : ℕ) : ℝ) ^ (2 : ℝ)) := by
    have h := Nat.Primes.summable_rpow (r := (-2 : ℝ)).mpr (by norm_num)
    refine h.congr fun p => ?_
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.pos
    rw [Real.rpow_neg hp0.le, one_div]
  have hdiffsum : Summable (fun p : Nat.Primes =>
      (-Complex.log (1 - (p : ℂ) ^ (-(zetaLinePoint σ τ)))).re
        - ((p : ℂ) ^ (-(zetaLinePoint σ τ))).re) := hresumdiff.sub hcosre_summable
  have hnormle : |∑' p : Nat.Primes,
      ((-Complex.log (1 - (p : ℂ) ^ (-(zetaLinePoint σ τ)))).re
        - ((p : ℂ) ^ (-(zetaLinePoint σ τ))).re)|
      ≤ ∑' p : Nat.Primes, 1 / ((p : ℕ) : ℝ) ^ (2 : ℝ) := by
    have h := hdiffsum.norm_tsum_le_tsum_norm ?_
    · refine le_trans ?_ (h.trans ?_)
      · exact le_of_eq (Real.norm_eq_abs _).symm
      · refine Summable.tsum_le_tsum ?_ ?_ hinvsum
        · intro p
          rw [Real.norm_eq_abs]
          exact hbound p
        · refine Summable.of_norm_bounded hinvsum fun p => ?_
          rw [Real.norm_eq_abs, abs_abs]
          exact hbound p
    · refine Summable.of_norm_bounded hinvsum fun p => ?_
      rw [Real.norm_eq_abs, abs_abs]
      exact hbound p
  refine le_trans hnormle ?_
  rw [invSquareTailConst]
  refine Summable.tsum_le_tsum_of_inj (fun p : Nat.Primes => (p : ℕ)) ?_ ?_ ?_ hinvsum
    invSquareTail_summable
  · intro p q hpq
    exact Subtype.ext hpq
  · intro n _
    exact invSquareTail_nonneg n
  · intro p
    exact le_rfl

end

end RHTower
