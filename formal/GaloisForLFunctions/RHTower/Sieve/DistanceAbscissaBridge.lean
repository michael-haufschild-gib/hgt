import GaloisForLFunctions.RHTower.Sieve.PrimeAbscissaSumBound
import GaloisForLFunctions.RHTower.Sieve.PrimeSigmaShift
import GaloisForLFunctions.RHTower.Sieve.DistanceTriangle

/-!
# From the abscissa-weighted distance to the harmonic one

The Euler bound damps a Dirichlet series by `exp(−D²)` with `D²` weighted by `p^{-σ}` over all primes,
while every distance lower bound in the corpus is weighted by `1/p` over the primes up to `z`.  The two
differ by the abscissa shift, which costs `(σ−1)(log z + log 4)` per unit weight and is therefore free
at `σ = 1 + 1/log z`:

`mulDistSqPair f (charFn t) (primesLE z) ≤ mulDistSqTsum f s + 2(σ−1)(log z + log 4)`.

The proof is the polar split `p^{-s} = p^{-σ} · conj(charFn t p)`, which turns each term of the
abscissa-weighted distance into `p^{-σ}` times the harmonic defect, followed by the corpus's summed
shift estimate applied to the defects halved.

Consequently the damping bound can be stated with the harmonic distance, which is what the zero-free
strip and Mertens-level estimates actually supply.
-/

namespace RHTower.Sieve

open Complex Finset

/-! ## The local defect -/

/-- The local defect `1 − Re(f(p) p^{-it})` of the harmonic distance. -/
noncomputable def distDefect (f : ℕ → ℂ) (t : ℝ) (p : ℕ) : ℝ :=
  1 - (f p * (starRingEnd ℂ) (charFn t p)).re

theorem mulDistSqPair_charFn_eq_sum (f : ℕ → ℂ) (t : ℝ) (P : Finset ℕ) :
    mulDistSqPair f (charFn t) P = ∑ p ∈ P, distDefect f t p / (p : ℝ) := rfl

section

variable {f : ℕ → ℂ} {s : ℂ}

theorem norm_mul_conj_charFn_le (hbdd : ∀ n, ‖f n‖ ≤ 1) (t : ℝ) (p : ℕ) :
    ‖f p * (starRingEnd ℂ) (charFn t p)‖ ≤ 1 := by
  rw [norm_mul, RCLike.norm_conj, norm_charFn, mul_one]
  exact hbdd p

theorem distDefect_nonneg (hbdd : ∀ n, ‖f n‖ ≤ 1) (t : ℝ) (p : ℕ) :
    0 ≤ distDefect f t p :=
  one_sub_re_nonneg (norm_mul_conj_charFn_le hbdd t p)

theorem distDefect_le_two (hbdd : ∀ n, ‖f n‖ ≤ 1) (t : ℝ) (p : ℕ) :
    distDefect f t p ≤ 2 := by
  have h1 : -(1 : ℝ) ≤ (f p * (starRingEnd ℂ) (charFn t p)).re := by
    have habs : |(f p * (starRingEnd ℂ) (charFn t p)).re| ≤ 1 :=
      le_trans (Complex.abs_re_le_norm _) (norm_mul_conj_charFn_le hbdd t p)
    linarith [(abs_le.mp habs).1]
  rw [distDefect]
  linarith

/-! ## The polar split -/

theorem natCast_cpow_neg_eq_mul (s : ℂ) {p : ℕ} (hp : 0 < p) :
    ((p : ℕ) : ℂ) ^ (-s) =
      ((((((p : ℕ)) : ℝ)) ^ (-s.re) : ℝ) : ℂ) * (starRingEnd ℂ) (charFn s.im p) := by
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp
  have hsplit : (-s : ℂ) = -((s.re : ℝ) : ℂ) + -((s.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hreal : ((p : ℕ) : ℂ) ^ (-((s.re : ℝ) : ℂ)) =
      ((((((p : ℕ)) : ℝ)) ^ (-s.re) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (le_of_lt hppos) (-s.re), Complex.ofReal_natCast]
    congr 1
    push_cast
    ring
  have himag : ((p : ℕ) : ℂ) ^ (-((s.im : ℝ) : ℂ) * Complex.I) =
      (starRingEnd ℂ) (charFn s.im p) := by
    rw [Complex.cpow_def_of_ne_zero hp0, charFn, ← Complex.exp_conj]
    congr 1
    rw [← Complex.ofReal_natCast (p : ℕ), ← Complex.ofReal_log hppos.le]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  rw [hsplit, Complex.cpow_add _ _ hp0, hreal, himag]

/-- **The abscissa-weighted term is the harmonic defect scaled by `p^{-σ}`.** -/
theorem rpow_sub_re_twistedSummand (hp0 : 0 < p) :
    ((((p : ℕ)) : ℝ)) ^ (-s.re) - (twistedSummand f s (p : ℕ)).re =
      ((((p : ℕ)) : ℝ)) ^ (-s.re) * distDefect f s.im p := by
  have hsplit := natCast_cpow_neg_eq_mul s hp0
  have hre : (twistedSummand f s (p : ℕ)).re =
      ((((p : ℕ)) : ℝ)) ^ (-s.re) * (f p * (starRingEnd ℂ) (charFn s.im p)).re := by
    rw [twistedSummand, hsplit, show f p * (((((((p : ℕ)) : ℝ)) ^ (-s.re) : ℝ) : ℂ) *
        (starRingEnd ℂ) (charFn s.im p)) =
        ((((((p : ℕ)) : ℝ)) ^ (-s.re) : ℝ) : ℂ) *
          (f p * (starRingEnd ℂ) (charFn s.im p)) by ring]
    exact re_ofReal_mul _ _
  rw [hre, distDefect]
  ring

end

/-! ## The bridge -/

section

variable {f : ℕ → ℂ} {s : ℂ}

theorem sum_primesLE_le_mulDistSqTsum (hbdd : ∀ n, ‖f n‖ ≤ 1) (hs : 1 < s.re) (z : ℕ) :
    ∑ p ∈ Nat.primesLE z, ((((p : ℕ)) : ℝ)) ^ (-s.re) * distDefect f s.im p ≤
      mulDistSqTsum f s := by
  have hsummable := summable_mulDistSqTsum hbdd hs
  have hsumT : ∑ q ∈ (Nat.primesLE z).subtype Nat.Prime,
        ((((q : ℕ)) : ℝ)) ^ (-s.re) * distDefect f s.im (q : ℕ) =
      ∑ p ∈ Nat.primesLE z, ((((p : ℕ)) : ℝ)) ^ (-s.re) * distDefect f s.im p := by
    rw [Finset.sum_subtype_eq_sum_filter
        (fun n : ℕ => ((n : ℝ)) ^ (-s.re) * distDefect f s.im n),
      Finset.filter_true_of_mem fun p hp => Nat.prime_of_mem_primesLE hp]
  have hterm : ∀ q ∈ (Nat.primesLE z).subtype Nat.Prime,
      ((((q : ℕ)) : ℝ)) ^ (-s.re) * distDefect f s.im (q : ℕ) =
        ((((q : ℕ)) : ℝ)) ^ (-s.re) - (twistedSummand f s ((q : ℕ))).re := by
    intro q _
    exact (rpow_sub_re_twistedSummand q.2.pos).symm
  rw [← hsumT, Finset.sum_congr rfl hterm, mulDistSqTsum]
  exact hsummable.sum_le_tsum ((Nat.primesLE z).subtype Nat.Prime)
    (fun q _ => mulDistSqTsum_term_nonneg hbdd q)

/-- **The bridge.**  The harmonic distance over the primes up to `z` exceeds the abscissa-weighted
distance over all primes by at most the shift cost. -/
theorem mulDistSqPair_le_mulDistSqTsum_add (hbdd : ∀ n, ‖f n‖ ≤ 1) (hs : 1 < s.re)
    {z : ℕ} (hz : 1 ≤ z) :
    mulDistSqPair f (charFn s.im) (Nat.primesLE z) ≤
      mulDistSqTsum f s + 2 * (s.re - 1) * (Real.log z + Real.log 4) := by
  have hshift := abs_sum_weight_shift_le hz (le_of_lt hs)
    (w := fun p => distDefect f s.im p / 2)
    (fun p => by
      rw [abs_div, abs_of_nonneg (distDefect_nonneg hbdd s.im p), abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      have := distDefect_le_two hbdd s.im p
      rw [div_le_one (by norm_num : (0:ℝ) < 2)]
      linarith)
  have habs := abs_le.mp hshift
  have hsplit : ∑ p ∈ Nat.primesLE z, distDefect f s.im p / (p : ℝ) =
      ∑ p ∈ Nat.primesLE z, ((((p : ℕ)) : ℝ)) ^ (-s.re) * distDefect f s.im p +
        2 * ∑ p ∈ Nat.primesLE z,
          (distDefect f s.im p / 2) * (1 / (p : ℝ) - ((p : ℝ)) ^ (-s.re)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    field_simp
    ring
  have hmain := sum_primesLE_le_mulDistSqTsum hbdd hs z
  rw [mulDistSqPair_charFn_eq_sum, hsplit]
  linarith [habs.1, habs.2]

/-- **The damping bound with the harmonic distance.**  This is the form the corpus's distance lower
bounds can be substituted into directly. -/
theorem norm_tsum_twistedSummand_le_of_mulDistSqPair
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) (hs : 1 < s.re) {z : ℕ} (hz : 1 ≤ z) :
    ‖∑' n : ℕ, twistedSummand f s n‖ ≤
      (1 + 1 / (s.re - 1)) *
        Real.exp (7 / 2 + 2 * (s.re - 1) * (Real.log z + Real.log 4)
          - mulDistSqPair f (charFn s.im) (Nat.primesLE z)) := by
  have hbase := norm_tsum_twistedSummand_le_mul_exp_neg_dist hf1 hmul hbdd hs
  have hbridge := mulDistSqPair_le_mulDistSqTsum_add hbdd hs hz
  have hpos : 0 < 1 + 1 / (s.re - 1) := by
    have h1 : 0 < s.re - 1 := by linarith
    positivity
  refine le_trans hbase (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hpos.le)
  linarith

end

end RHTower.Sieve
