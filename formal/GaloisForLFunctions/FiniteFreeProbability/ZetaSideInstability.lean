import GaloisForLFunctions.FiniteFreeProbability.PoleSideInstability
import GaloisForLFunctions.RHTower.ZetaFisherVariance
import GaloisForLFunctions.RHTower.GammaShiftZetaJetFlag

/-!
# The zeta side has no Hermite–Biehler normalization

For `σ > 1` the Taylor series at `w = 0` of `w ↦ ζ(σ + iw)` has coefficients
`i^k ζ^{(k)}(σ)/k! = Σ_n n^{−σ} (−i log n)^k / k!`: it is the nonnegative exponential mixture
`Σ_n n^{−σ} e^{−iw log n}`, whose frequencies `log n` are unbounded. Hence for every translation `c`
the reversed Jensen polynomials of `e^{icw} ζ(σ + iw)` have a root in the open upper half-plane at
all large odd degrees. The Dirichlet-series side of `ζ` admits no stabilizing phase, whereas each
Möbius-side Euler factor `1 − p^{−σ−iw}` is stabilized exactly by the phase `(log p)/2`.
-/

open Polynomial Filter Topology Complex

namespace FiniteFreeProbability

noncomputable section

/-- The Taylor series at `0` of `w ↦ ζ(σ + iw)`. -/
def zetaTaylor (σ : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk fun k => I ^ k * iteratedDeriv k riemannZeta (σ : ℂ) / (k.factorial : ℂ)

theorem summable_rpow_neg_mul_sub_log_pow {σ : ℝ} (hσ : 1 < σ) (c : ℝ) (i : ℕ) :
    Summable fun n : ℕ => (n : ℝ) ^ (-σ) * (c - Real.log n) ^ i := by
  have h : Summable fun n : ℕ => ∑ m ∈ Finset.range (i + 1),
      (c ^ m * (i.choose m : ℝ) * (-1) ^ (i - m)) * (Real.log n ^ (i - m) * (n : ℝ) ^ (-σ)) :=
    summable_sum fun m _ => (RHTower.summable_log_natCast_pow_mul_rpow_neg (i - m) hσ).mul_left _
  refine h.congr fun n => ?_
  rw [sub_eq_add_neg, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [neg_pow]; ring

/-- The Taylor series of `ζ(σ + iw)` is the mixture `Σ_n n^{−σ} e^{−iw log n}`. -/
theorem zetaTaylor_eq {σ : ℝ} (hσ : 1 < σ) :
    zetaTaylor σ = seriesMixture (fun n => (n : ℝ) ^ (-σ)) (fun n => Real.log n) 0 := by
  ext k
  rw [zetaTaylor, seriesMixture, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
    ← GaloisForLFunctions.LSeries_zetaJetFullCoeff_eq_iteratedDeriv k (by simpa using hσ), LSeries,
    mul_div_right_comm, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [LSeries.term_def, coeff_expSeries]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow (by linarith : -σ ≠ 0)]
  rw [if_neg hn, GaloisForLFunctions.zetaJetFullCoeff, if_neg hn,
    Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, Complex.ofReal_neg,
    Complex.cpow_neg]
  have hns : (n : ℂ) ^ (σ : ℂ) ≠ 0 :=
    (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by exact_mod_cast (by linarith : σ ≠ 0))).2
      (by exact_mod_cast hn)
  rw [mul_pow]
  push_cast
  field_simp
  ring

/-- **No phase stabilizes the zeta side.** For `σ > 1` and every translation `c`, the reversed Jensen
polynomials of the Taylor series of `e^{icw} ζ(σ + iw)` have a root in the open upper half-plane for
all large odd degrees. -/
theorem eventually_exists_upper_root_zetaTaylor {σ : ℝ} (hσ : 1 < σ) (c : ℝ) :
    ∀ᶠ d : ℕ in atTop, Odd d →
      ∃ x : ℂ, (jensenRev d (expSeries (I * c) * zetaTaylor σ)).IsRoot x ∧ 0 < x.im := by
  rw [zetaTaylor_eq hσ, expSeries_mul_seriesMixture (summable_rpow_neg_mul_sub_log_pow hσ 0),
    zero_add]
  set K := ⌈Real.exp (2 * c)⌉₊ + 1
  have hK0 : (0 : ℝ) < K := by positivity
  have hlog : 2 * c < Real.log K := by
    rw [Real.lt_log_iff_exp_lt hK0]
    have := Nat.le_ceil (Real.exp (2 * c))
    simp only [K]; push_cast; linarith
  exact eventually_exists_upper_root_seriesMixture (m := 0) (K := K)
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) (fun n => Real.log_natCast_nonneg n)
    (summable_rpow_neg_mul_sub_log_pow hσ c) (Real.rpow_pos_of_pos hK0 _) (by simpa using hlog)

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.eventually_exists_upper_root_zetaTaylor
