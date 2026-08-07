import GaloisForLFunctions.RHTower.Sieve.MultiplicativeEulerBound
import GaloisForLFunctions.RHTower.Sieve.ZetaLogPrimeSum
import GaloisForLFunctions.HTGeometry.ZetaGammaFieldHypertranscendence
import Mathlib.Analysis.SumIntegralComparisons

/-!
# The trivial size of the prime sum at an abscissa

The Euler bound for a bounded multiplicative Dirichlet series is `exp(P(σ) − D²)` with
`P(σ) = ∑_p p^{-σ}`, so it is only as good as an upper bound for `P`.  The Euler product of `ζ`
supplies one: the Euler logarithms differ from the prime sum by at most the prime inverse squares, so

`P(σ) ≤ log ζ(σ) + 49/100`,

and `ζ(σ) ≤ 1 + 1/(σ−1)` by the integral test.  Hence `P(σ) ≤ log(1 + 1/(σ−1)) + 1`, which at
`σ = 1 + 1/log x` is `log log x + O(1)`: logarithmic, not `1/(σ−1)`.  Bounding `P` by the whole
`ζ`-sum instead of by `log ζ` would lose exactly that logarithm and make the Euler bound vacuous.
-/

namespace RHTower.Sieve

open Complex Filter MeasureTheory Set Topology
open GaloisForLFunctions.HTGeometry

/-! ## The `p`-series value bound -/

theorem antitoneOn_rpow_neg_Ici {σ : ℝ} (hσ : 0 < σ) :
    AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Ici (1 : ℝ)) := by
  intro x hx y hy hxy
  have hx1 : (1 : ℝ) ≤ x := hx
  have hy1 : (1 : ℝ) ≤ y := hy
  simp only
  rw [Real.rpow_neg (by linarith), Real.rpow_neg (by linarith)]
  have hxpow : (0 : ℝ) < x ^ σ := Real.rpow_pos_of_pos (by linarith) _
  have hle : x ^ σ ≤ y ^ σ := Real.rpow_le_rpow (by linarith) hxy hσ.le
  simpa [one_div] using one_div_le_one_div_of_le hxpow hle

theorem tsum_shift_rpow_neg_le {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, (((n + 1 + 1 : ℕ) : ℝ)) ^ (-σ) ≤ 1 / (σ - 1) := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Ici ((1 : ℕ) : ℝ)) := by
    simpa using antitoneOn_rpow_neg_Ici (by linarith : (0 : ℝ) < σ)
  have hint : IntegrableOn (fun x : ℝ => x ^ (-σ)) (Set.Ioi ((1 : ℕ) : ℝ)) := by
    simpa using integrableOn_Ioi_rpow_of_lt (by linarith : -σ < -1) (by norm_num : (0:ℝ) < 1)
  have hnn : ∀ t ∈ Set.Ioi ((1 : ℕ) : ℝ), (0 : ℝ) ≤ t ^ (-σ) := by
    intro t ht
    have : (0 : ℝ) < t := by
      have : ((1 : ℕ) : ℝ) < t := ht
      simpa using lt_trans (by norm_num : (0:ℝ) < 1) (by simpa using this)
    exact Real.rpow_nonneg this.le _
  have hval : ∫ x in Set.Ioi ((1 : ℕ) : ℝ), x ^ (-σ) = 1 / (σ - 1) := by
    have h := integral_Ioi_rpow_of_lt (a := -σ) (by linarith : -σ < -1)
      (by norm_num : (0:ℝ) < 1)
    rw [show (((1 : ℕ) : ℝ)) = (1 : ℝ) by norm_num, h, Real.one_rpow]
    rw [show (-σ + 1) = -(σ - 1) by ring, neg_div, div_neg, neg_neg]
  have hmain := AntitoneOn.tsum_comp_add_le_integral 1 hanti hint hnn
  rw [hval] at hmain
  exact hmain

/-! ## The `ζ`-sum bound -/

theorem zetaHalfPlaneBound_le {σ : ℝ} (hσ : 1 < σ) :
    GaloisForLFunctions.zetaHalfPlaneBound σ ≤ 1 + 1 / (σ - 1) := by
  have hterm : ∀ i : ℕ, (1 : ℝ) / (((i : ℝ) + 1)) ^ σ = (((i + 1 : ℕ) : ℝ)) ^ (-σ) := by
    intro i
    rw [Real.rpow_neg (by positivity), one_div]
    congr 2
    push_cast
    ring
  have hsummable : Summable (fun i : ℕ => (((i + 1 : ℕ) : ℝ)) ^ (-σ)) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-σ)) := summable_nat_rpow_neg hσ
    exact (summable_nat_add_iff 1).2 hbase
  have hsplit : ∑' i : ℕ, (((i + 1 : ℕ) : ℝ)) ^ (-σ)
      = (((0 + 1 : ℕ) : ℝ)) ^ (-σ) + ∑' i : ℕ, (((i + 1 + 1 : ℕ) : ℝ)) ^ (-σ) :=
    hsummable.tsum_eq_zero_add
  have h1 : (((0 + 1 : ℕ) : ℝ)) ^ (-σ) = 1 := by
    rw [show (((0 + 1 : ℕ) : ℝ)) = (1 : ℝ) by norm_num, Real.one_rpow]
  rw [GaloisForLFunctions.zetaHalfPlaneBound, tsum_congr hterm, hsplit, h1]
  have := tsum_shift_rpow_neg_le hσ
  linarith

theorem norm_riemannZeta_real_le {σ : ℝ} (hσ : 1 < σ) :
    ‖riemannZeta ((σ : ℝ) : ℂ)‖ ≤ 1 + 1 / (σ - 1) := by
  refine le_trans (GaloisForLFunctions.norm_riemannZeta_le_halfPlane hσ ?_)
    (zetaHalfPlaneBound_le hσ)
  simp

/-! ## The prime sum at a real abscissa -/

theorem primeAbscissaSum_eq_tsum_re {σ : ℝ} :
    primeAbscissaSum σ =
      ∑' p : Nat.Primes, ((((p : ℕ) : ℂ)) ^ (-((σ : ℝ) : ℂ))).re := by
  rw [primeAbscissaSum]
  refine tsum_congr fun p => ?_
  have hcast : ((((p : ℕ) : ℝ)) ^ (-σ) : ℝ) = ((((p : ℕ) : ℂ)) ^ (-((σ : ℝ) : ℂ))) := by
    have h := Complex.ofReal_cpow (x := (((p : ℕ) : ℝ))) (Nat.cast_nonneg _) (-σ)
    rw [h, Complex.ofReal_natCast]
    congr 1
    push_cast
    ring
  rw [← Complex.ofReal_re ((((p : ℕ) : ℝ)) ^ (-σ)), hcast]

theorem tsum_primes_norm_cpow_sq_le {σ : ℝ} (hσ : 1 < σ) :
    ∑' p : Nat.Primes, ‖(((p : ℕ) : ℂ)) ^ (-((σ : ℝ) : ℂ))‖ ^ 2 ≤ 49 / 100 := by
  have hterm : ∀ p : Nat.Primes,
      ‖(((p : ℕ) : ℂ)) ^ (-((σ : ℝ) : ℂ))‖ ^ 2 = ((((p : ℕ)) : ℝ)) ^ (-(2 * σ)) := by
    intro p
    have hnorm : ‖(((p : ℕ) : ℂ)) ^ (-((σ : ℝ) : ℂ))‖ = ((((p : ℕ)) : ℝ)) ^ (-σ) := by
      rw [Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re, Complex.ofReal_re]
    rw [hnorm, ← Real.rpow_natCast (((((p : ℕ)) : ℝ)) ^ (-σ)) 2,
      ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    push_cast
    ring
  rw [tsum_congr hterm]
  exact tsum_primes_rpow_two_le (le_of_lt hσ)

/-- **The trivial size of the prime sum is logarithmic.**  `P(σ) ≤ log(1 + 1/(σ−1)) + 1`, so at
`σ = 1 + 1/log x` it is `log log x + O(1)`. -/
theorem primeAbscissaSum_le {σ : ℝ} (hσ : 1 < σ) :
    primeAbscissaSum σ ≤ Real.log (1 + 1 / (σ - 1)) + 1 := by
  have hs : (1 : ℝ) < (((σ : ℝ) : ℂ)).re := by simpa using hσ
  have hzne : riemannZeta ((σ : ℝ) : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hzpos : 0 < ‖riemannZeta ((σ : ℝ) : ℂ)‖ := norm_pos_iff.mpr hzne
  have hlog := abs_log_norm_riemannZeta_sub_tsum_re_le hs
  have hsq := tsum_primes_norm_cpow_sq_le hσ
  have hbound := norm_riemannZeta_real_le hσ
  have hlogle : Real.log ‖riemannZeta ((σ : ℝ) : ℂ)‖ ≤ Real.log (1 + 1 / (σ - 1)) :=
    Real.log_le_log hzpos hbound
  have habs := abs_le.mp hlog
  rw [primeAbscissaSum_eq_tsum_re]
  linarith [habs.1, habs.2]

/-! ## The Euler bound with the trivial size made explicit -/

section

variable {f : ℕ → ℂ} {s : ℂ}

/-- **The Halász input.**  For `Re s > 1` a bounded multiplicative Dirichlet series is at most its
trivial size `1 + 1/(Re s − 1)` times `e^{−D²}`, where `D²` is its distance from the character at
`s`.  At `Re s = 1 + 1/log x` the trivial size is `1 + log x`, so a distance exceeding
`log log x` is what produces decay. -/
theorem norm_tsum_twistedSummand_le_mul_exp_neg_dist
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) (hs : 1 < s.re) :
    ‖∑' n : ℕ, twistedSummand f s n‖ ≤
      (1 + 1 / (s.re - 1)) * Real.exp (7 / 2 - mulDistSqTsum f s) := by
  have hpos : 0 < 1 + 1 / (s.re - 1) := by
    have h1 : 0 < s.re - 1 := by linarith
    positivity
  have hP := primeAbscissaSum_le hs
  have hlog : Real.exp (Real.log (1 + 1 / (s.re - 1)) + 1 - mulDistSqTsum f s + 5 / 2)
      = (1 + 1 / (s.re - 1)) * Real.exp (7 / 2 - mulDistSqTsum f s) := by
    rw [show Real.log (1 + 1 / (s.re - 1)) + 1 - mulDistSqTsum f s + 5 / 2
        = Real.log (1 + 1 / (s.re - 1)) + (7 / 2 - mulDistSqTsum f s) by ring,
      Real.exp_add, Real.exp_log hpos]
  calc ‖∑' n : ℕ, twistedSummand f s n‖
      ≤ Real.exp (primeAbscissaSum s.re - mulDistSqTsum f s + 5 / 2) :=
        norm_tsum_twistedSummand_le_exp_sub_dist hf1 hmul hbdd hs
    _ ≤ Real.exp (Real.log (1 + 1 / (s.re - 1)) + 1 - mulDistSqTsum f s + 5 / 2) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = (1 + 1 / (s.re - 1)) * Real.exp (7 / 2 - mulDistSqTsum f s) := hlog

end

end RHTower.Sieve
