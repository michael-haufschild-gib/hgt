import GaloisForLFunctions.FiniteFreeProbability.JensenDictionary
import GaloisForLFunctions.HTGeometry.LaguerreShiftSplits

/-!
# Dirichlet pieces are never real-rooted

The reversed Jensen polynomials of a power series form a derivative ladder,
`(R_{d+1} f)' = (d+1) R_d f`, so by Rolle real-rootedness descends in the degree and every
real-rooted `R_d f` (`d ≥ 2`) forces the degree-two Turán inequality `2 f₀ f₂ ≤ f₁²`.

A Dirichlet polynomial `Σ_n a_n n^{−σ−w}` with nonnegative coefficients, expanded in the real
direction `w`, is the exponential mixture `Σ_n w_n e^{−λ_n w}` with `w_n = a_n n^{−σ} ≥ 0` and
`λ_n = log n`; its reversed Jensen polynomials are the Appell polynomials `Σ_n w_n (X − λ_n)^d` of
the law `(w_n)` on the points `λ_n`. For such a mixture
`2 f₀ f₂ − f₁² = (Σ w)(Σ w λ²) − (Σ w λ)²`, a positive multiple of the variance. So as soon as two
distinct frequencies occur, no reversed Jensen polynomial of degree `≥ 2` is real-rooted: Euler and
Dirichlet data never supply real-rooted finite free pieces in the real direction.
-/

open Polynomial Finset

namespace FiniteFreeProbability

noncomputable section

section General

variable {K : Type*} [Field K]

theorem diffOp_X (p : K[X]) : diffOp X p = derivative p := by
  simp [diffOp]

theorem diffOp_C_mul (h : K[X]) (a : K) (p : K[X]) :
    diffOp h (C a * p) = C a * diffOp h p := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul]; exact map_smul _ _ _

/-- **The Jensen ladder.** `(R_{d+1} f)' = (d + 1) R_d f`. -/
theorem derivative_jensenRev (d : ℕ) (f : PowerSeries K) :
    derivative (jensenRev (d + 1) f) = C ((d : K) + 1) * jensenRev d f := by
  rw [jensenRev, ← diffOp_X, diffOp_comm, diffOp_X, derivative_X_pow, Nat.add_sub_cancel,
    diffOp_C_mul, jensenRev]
  push_cast
  congr 1
  refine diffOp_congr (natDegree_X_pow_le d) fun i hi => ?_
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_pos (by omega), if_pos (by omega)]

end General

/-- The exponential power series `e^{cw} = Σ c^k w^k / k!`. -/
def expSeries {K : Type*} [Field K] (c : K) : PowerSeries K :=
  PowerSeries.mk fun k => c ^ k / (k.factorial : K)

/-- Real-rootedness descends along the Jensen ladder. -/
theorem splits_jensenRev_of_splits_succ {d : ℕ} {f : PowerSeries ℝ}
    (h : (jensenRev (d + 1) f).Splits) : (jensenRev d f).Splits := by
  have hder : (derivative (jensenRev (d + 1) f)).Splits := by
    have := GaloisForLFunctions.HTGeometry.splits_laguerreShift h 0
    simpa [GaloisForLFunctions.HTGeometry.laguerreShift] using this
  rw [derivative_jensenRev] at hder
  exact (splits_mul_iff_right (C_ne_zero.2 (by positivity)) (Polynomial.Splits.C _)).1 hder

theorem splits_jensenRev_of_le {d k : ℕ} (hk : k ≤ d) {f : PowerSeries ℝ}
    (h : (jensenRev d f).Splits) : (jensenRev k f).Splits := by
  induction d, hk using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact ih (splits_jensenRev_of_splits_succ h)

/-- `R_2 f = f₀ X² + 2 f₁ X + 2 f₂`. -/
theorem jensenRev_two (f : PowerSeries ℝ) :
    jensenRev 2 f = C (PowerSeries.coeff 0 f) * X ^ 2 + C (2 * PowerSeries.coeff 1 f) * X +
      C (2 * PowerSeries.coeff 2 f) := by
  rw [jensenRev_eq_sum]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.descFactorial, PowerSeries.coeff_zero_eq_constantCoeff]
  simp only [Nat.cast_one, map_mul, mul_one]
  rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) from rfl]
  simp only [map_ofNat]
  ring

/-- **Turán obstruction.** A real-rooted reversed Jensen polynomial of degree `d ≥ 2` forces
`2 f₀ f₂ ≤ f₁²`. -/
theorem turan_of_splits_jensenRev {d : ℕ} (hd : 2 ≤ d) {f : PowerSeries ℝ}
    (h : (jensenRev d f).Splits) :
    2 * PowerSeries.coeff 0 f * PowerSeries.coeff 2 f ≤ PowerSeries.coeff 1 f ^ 2 := by
  have h2 := splits_jensenRev_of_le hd h
  set a := PowerSeries.coeff 0 f
  set b := PowerSeries.coeff 1 f
  set c := PowerSeries.coeff 2 f
  by_cases ha : a = 0
  · rw [ha]; nlinarith [sq_nonneg b]
  have hdeg : (jensenRev 2 f).degree ≠ 0 := by
    rw [jensenRev_two, degree_quadratic ha]; decide
  obtain ⟨x, hx⟩ := h2.exists_eval_eq_zero hdeg
  rw [jensenRev_two] at hx
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at hx
  have hq : a * (x * x) + 2 * b * x + 2 * c = 0 := by linear_combination hx
  have hdisc := discrim_eq_sq_of_quadratic_eq_zero hq
  rw [discrim] at hdisc
  nlinarith [sq_nonneg (2 * a * x + 2 * b)]

/-- The Taylor coefficients of an exponential mixture `Σ w_i e^{−λ_i w}`. -/
theorem coeff_expMixture {ι : Type*} (S : Finset ι) (w lam : ι → ℝ) (k : ℕ) :
    PowerSeries.coeff k (∑ i ∈ S, PowerSeries.C (w i) * expSeries (-lam i)) =
      ∑ i ∈ S, w i * (-lam i) ^ k / (k.factorial : ℝ) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PowerSeries.coeff_C_mul, expSeries, PowerSeries.coeff_mk]
  ring

/-- Lagrange's identity for a weighted variance. -/
theorem variance_identity {ι : Type*} (S : Finset ι) (w lam : ι → ℝ) :
    2 * ((∑ i ∈ S, w i) * (∑ i ∈ S, w i * lam i ^ 2) - (∑ i ∈ S, w i * lam i) ^ 2) =
      ∑ i ∈ S, ∑ j ∈ S, w i * w j * (lam i - lam j) ^ 2 := by
  have e : ∀ i j, w i * w j * (lam i - lam j) ^ 2 =
      w i * (w j * lam j ^ 2) + w j * (w i * lam i ^ 2) - 2 * ((w i * lam i) * (w j * lam j)) := by
    intro i j; ring
  simp_rw [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    ← Finset.mul_sum]
  ring

/-- **Dirichlet pieces are never real-rooted.** A positive exponential mixture `Σ_{i ∈ S} w_i e^{−λ_i w}`
with two distinct frequencies has no real-rooted reversed Jensen polynomial of degree `≥ 2`. -/
theorem not_splits_jensenRev_expMixture {ι : Type*} (S : Finset ι) (w lam : ι → ℝ)
    (hw : ∀ i ∈ S, 0 < w i) (hlam : ∃ i ∈ S, ∃ j ∈ S, lam i ≠ lam j) {d : ℕ} (hd : 2 ≤ d) :
    ¬ (jensenRev d (∑ i ∈ S, PowerSeries.C (w i) * expSeries (-lam i))).Splits := by
  intro h
  have ht := turan_of_splits_jensenRev hd h
  have c0 : PowerSeries.coeff 0 (∑ i ∈ S, PowerSeries.C (w i) * expSeries (-lam i)) =
      ∑ i ∈ S, w i := by
    rw [coeff_expMixture]; simp
  have c1 : PowerSeries.coeff 1 (∑ i ∈ S, PowerSeries.C (w i) * expSeries (-lam i)) =
      -∑ i ∈ S, w i * lam i := by
    rw [coeff_expMixture, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_; simp
  have c2 : PowerSeries.coeff 2 (∑ i ∈ S, PowerSeries.C (w i) * expSeries (-lam i)) =
      (∑ i ∈ S, w i * lam i ^ 2) / 2 := by
    rw [coeff_expMixture, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_; simp [Nat.factorial]
  rw [c0, c1, c2] at ht
  have hpos : 0 < ∑ i ∈ S, ∑ j ∈ S, w i * w j * (lam i - lam j) ^ 2 := by
    obtain ⟨i, hi, j, hj, hij⟩ := hlam
    have hnn : ∀ a ∈ S, ∀ b ∈ S, 0 ≤ w a * w b * (lam a - lam b) ^ 2 := fun a ha b hb =>
      mul_nonneg (mul_nonneg (hw a ha).le (hw b hb).le) (sq_nonneg _)
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun a ha =>
      Finset.sum_nonneg (hnn a ha)) hi)
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (hnn i hi) hj)
    have hsq : 0 < (lam i - lam j) ^ 2 := by positivity [sub_ne_zero.2 hij]
    exact mul_pos (mul_pos (hw i hi) (hw j hj)) hsq
  rw [← variance_identity] at hpos
  nlinarith

end

end FiniteFreeProbability
