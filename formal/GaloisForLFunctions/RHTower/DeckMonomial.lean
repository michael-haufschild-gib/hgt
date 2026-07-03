/-
The monomial dictionary for the deck cocycle (MWM lane, A3 chunk 2; task #113).

Explicit 2^k-th-root branches of the monomial (z−a)^m on the two standard slit charts
around the puncture a, and the computation of their deck class:

  w_n((z−a)^m) = exp(2πi·m/n).

Together with `deckClass_root_indep` and `deckClass_mul_global` (below), this gives the
zero-counting meaning of the cocycle with NO argument principle: any local roots of a
peeled function (z−a)^m·h have deck class exp(2πi·m/n) — the enclosed order mod n,
realized as the q62 dyadic multiplier when n = 2^k.
-/
import GaloisForLFunctions.RHTower.DeckCocycle

namespace RHTower

open Complex

/-- Multiplying both local roots by one global nonvanishing factor does not change the
deck class. -/
theorem deckClass_mul_global {g₁ g₂ r : ℂ → ℂ} {pP pM : ℂ}
    (hrP : r pP ≠ 0) (hrM : r pM ≠ 0) :
    deckClass (fun z => g₁ z * r z) (fun z => g₂ z * r z) pP pM =
      deckClass g₁ g₂ pP pM := by
  simp only [deckClass]
  rw [mul_div_mul_right _ _ hrP, mul_div_mul_right _ _ hrM]

/-- The chart-1 branch of the `n`-th root of `(z−a)^m`: defined via `log (z−a)` on the
right-slit chart `{z | z − a ∈ slitPlane}`. -/
noncomputable def monoRoot₁ (a : ℂ) (m n : ℕ) : ℂ → ℂ :=
  fun z => exp ((m / n : ℂ) * log (z - a))

/-- The chart-2 branch: via `log (a−z)` on the opposite chart `{z | a − z ∈ slitPlane}`,
with the constant `exp((m/n)πi)` correcting the sign `(a−z)^m = (−1)^m (z−a)^m`. -/
noncomputable def monoRoot₂ (a : ℂ) (m n : ℕ) : ℂ → ℂ :=
  fun z => exp ((m / n : ℂ) * log (a - z) + (m / n : ℂ) * (Real.pi : ℂ) * I)

theorem monoRoot₁_pow {a : ℂ} {m n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : z - a ∈ slitPlane) :
    monoRoot₁ a m n z ^ n = (z - a) ^ m := by
  have hz0 : z - a ≠ 0 := slitPlane_ne_zero hz
  rw [monoRoot₁, ← exp_nat_mul]
  have harg : (n : ℂ) * ((m / n : ℂ) * log (z - a)) = (m : ℂ) * log (z - a) := by
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp
  rw [harg, exp_nat_mul, exp_log hz0]

theorem monoRoot₂_pow {a : ℂ} {m n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : a - z ∈ slitPlane) :
    monoRoot₂ a m n z ^ n = (z - a) ^ m := by
  have hz0 : a - z ≠ 0 := slitPlane_ne_zero hz
  rw [monoRoot₂, ← exp_nat_mul]
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have harg : (n : ℂ) * ((m / n : ℂ) * log (a - z) + (m / n : ℂ) * (Real.pi : ℂ) * I) =
      (m : ℂ) * log (a - z) + (m : ℂ) * ((Real.pi : ℂ) * I) := by
    field_simp
  rw [harg, exp_add, exp_nat_mul, exp_nat_mul, exp_log hz0, exp_pi_mul_I]
  rw [← mul_pow]
  congr 1
  ring

theorem monoRoot₁_analyticOnNhd (a : ℂ) (m n : ℕ) :
    AnalyticOnNhd ℂ (monoRoot₁ a m n) {z | z - a ∈ slitPlane} := by
  intro z hz
  have hsub : AnalyticAt ℂ (fun z : ℂ => z - a) z := analyticAt_id.sub analyticAt_const
  have hlog : AnalyticAt ℂ (fun z : ℂ => log (z - a)) z := hsub.clog hz
  have hconst : AnalyticAt ℂ (fun _ : ℂ => (m / n : ℂ)) z := analyticAt_const
  exact (hconst.mul hlog).cexp

theorem monoRoot₂_analyticOnNhd (a : ℂ) (m n : ℕ) :
    AnalyticOnNhd ℂ (monoRoot₂ a m n) {z | a - z ∈ slitPlane} := by
  intro z hz
  have hsub : AnalyticAt ℂ (fun z : ℂ => a - z) z := analyticAt_const.sub analyticAt_id
  have hlog : AnalyticAt ℂ (fun z : ℂ => log (a - z)) z := hsub.clog hz
  have hconst : AnalyticAt ℂ (fun _ : ℂ => (m / n : ℂ)) z := analyticAt_const
  have hconst2 : AnalyticAt ℂ (fun _ : ℂ => (m / n : ℂ) * (Real.pi : ℂ) * I) z :=
    analyticAt_const
  exact ((hconst.mul hlog).add hconst2).cexp

/-- **The monomial dictionary**: the deck class of the standard branches of the `n`-th
root of `(z−a)^m`, read at the overlap basepoints `a ± i`, is `exp(2πi·m/n)` — the
enclosed order `m`, reduced mod `n`, realized as a root of unity. For `n = 2^k` this is
the q62 dyadic multiplier `dyadicRoot k ^ m`. No argument principle enters. -/
theorem deckClass_monomial (a : ℂ) (m n : ℕ) :
    deckClass (monoRoot₁ a m n) (monoRoot₂ a m n) (a + I) (a - I) =
      exp (2 * (Real.pi : ℂ) * I * m / n) := by
  have e₁ : a + I - a = I := by ring
  have e₂ : a - (a + I) = -I := by ring
  have e₃ : a - I - a = -I := by ring
  have e₄ : a - (a - I) = I := by ring
  simp only [deckClass, monoRoot₁, monoRoot₂]
  rw [e₁, e₂, e₃, e₄, log_I, log_neg_I, ← exp_sub, ← exp_sub, ← exp_sub]
  congr 1
  ring

end RHTower
