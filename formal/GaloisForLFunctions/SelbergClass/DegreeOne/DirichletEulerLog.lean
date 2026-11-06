import GaloisForLFunctions.HTGeometry.CanonicalEulerLog
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# The Euler logarithm of a shifted Dirichlet L-function

For a Dirichlet character `χ` and real `θ`, the series `L(s + iθ, χ)` has coefficients
`a(n) = χ(n) n^{−iθ}` and Euler logarithm `b(n) = a(n) Λ(n)/log n`, supported on prime powers.  On
`Re s > 1`, `exp L(b, s) = L(s + iθ, χ)` (`exp_lSeries_dirichletLogCoeff`).
-/

noncomputable section

set_option autoImplicit false

open Complex RHTower

namespace GaloisForLFunctions.SelbergClass.DegreeOne

variable {N : ℕ} (χ : DirichletCharacter ℂ N) (θ : ℝ)

/-- The coefficients of `L(s + iθ, χ)`. -/
def dirichletCoeff : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else χ n * (n : ℂ) ^ (-(I * (θ : ℂ))), by simp⟩

theorem dirichletCoeff_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    dirichletCoeff χ θ n = χ n * (n : ℂ) ^ (-(I * (θ : ℂ))) := if_neg hn

theorem norm_natCast_cpow_shift {n : ℕ} (hn : n ≠ 0) : ‖(n : ℂ) ^ (-(I * (θ : ℂ)))‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp

theorem norm_dirichletCoeff_le (n : ℕ) : ‖dirichletCoeff χ θ n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [dirichletCoeff]
  rw [dirichletCoeff_of_ne_zero χ θ hn, norm_mul, norm_natCast_cpow_shift θ hn, mul_one]
  exact DirichletCharacter.norm_le_one χ _

/-- A Dirichlet coefficient of `L(s + iθ, χ)` is the term of `L(·, χ)` at `s + iθ`. -/
theorem term_dirichletCoeff (s : ℂ) (n : ℕ) :
    LSeries.term (dirichletCoeff χ θ) s n =
      LSeries.term (fun n => χ n) (s + I * (θ : ℂ)) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, dirichletCoeff_of_ne_zero χ θ hn,
    Complex.cpow_add _ _ hnc, Complex.cpow_neg]
  have h1 : (n : ℂ) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hnc]
    exact Complex.exp_ne_zero _
  have h2 : (n : ℂ) ^ (I * (θ : ℂ)) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hnc]
    exact Complex.exp_ne_zero _
  field_simp

theorem re_add_shift (s : ℂ) : (s + I * (θ : ℂ)).re = s.re := by simp

theorem lSeriesSummable_dirichletCoeff {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (dirichletCoeff χ θ) s := by
  have h := DirichletCharacter.LSeriesSummable_of_one_lt_re χ (s := s + I * (θ : ℂ))
    (by rwa [re_add_shift])
  unfold LSeriesSummable at h ⊢
  convert h using 1
  funext n
  exact term_dirichletCoeff χ θ s n

theorem lSeries_dirichletCoeff [NeZero N] {s : ℂ} (hs : 1 < s.re) :
    LSeries (dirichletCoeff χ θ) s = DirichletCharacter.LFunction χ (s + I * (θ : ℂ)) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ (by rwa [re_add_shift]), LSeries, LSeries]
  exact tsum_congr fun n => term_dirichletCoeff χ θ s n

/-- The Euler logarithm `a(n) Λ(n)/log n`. -/
def dirichletLogCoeff : ArithmeticFunction ℂ :=
  ⟨fun n => dirichletCoeff χ θ n * eulerLogDirichletCoeff n, by simp [dirichletCoeff]⟩

theorem dirichletLogCoeff_apply (n : ℕ) :
    dirichletLogCoeff χ θ n = dirichletCoeff χ θ n * eulerLogDirichletCoeff n := rfl

theorem norm_dirichletLogCoeff_le (n : ℕ) : ‖dirichletLogCoeff χ θ n‖ ≤ 1 := by
  rw [dirichletLogCoeff_apply, norm_mul]
  exact mul_le_one₀ (norm_dirichletCoeff_le χ θ n) (norm_nonneg _)
    (norm_eulerLogDirichletCoeff_le_one n)

theorem isPrimePow_of_dirichletLogCoeff_ne_zero {n : ℕ} (hn : dirichletLogCoeff χ θ n ≠ 0) :
    IsPrimePow n := by
  by_contra h
  apply hn
  rw [dirichletLogCoeff_apply, eulerLogDirichletCoeff_eq_zero_of_not_primePower h, mul_zero]

theorem lSeriesSummable_dirichletLogCoeff {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (dirichletLogCoeff χ θ) s := by
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have h1n : Summable fun n => ‖LSeries.term (1 : ℕ → ℂ) s n‖ := summable_norm_iff.mpr h1
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) h1n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_div]
    simp only [Pi.one_apply, norm_one, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (norm_dirichletLogCoeff_le χ θ n)
      (inv_nonneg.mpr (norm_nonneg ((n : ℂ) ^ s)))

/-- The term of the Euler logarithm at `p^{k+1}` is the Taylor term of `−log(1 − x)`. -/
theorem term_dirichletLogCoeff_prime_pow {p : ℕ} (hp : p.Prime) (s : ℂ) (k : ℕ) :
    LSeries.term (dirichletLogCoeff χ θ) s (p ^ (k + 1)) =
      (χ p * (p : ℂ) ^ (-(s + I * (θ : ℂ)))) ^ (k + 1) / ((k + 1 : ℕ) : ℂ) := by
  have hne : p ^ (k + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [LSeries.term_of_ne_zero hne, dirichletLogCoeff_apply, dirichletCoeff_of_ne_zero χ θ hne,
    eulerLogDirichletCoeff_prime_pow_succ p k hp]
  have hcast : ((p ^ (k + 1) : ℕ) : ℂ) = (p : ℂ) ^ (k + 1) := by push_cast; rfl
  have hχ : χ ((p ^ (k + 1) : ℕ) : ZMod N) = χ (p : ZMod N) ^ (k + 1) := by
    push_cast
    exact map_pow χ _ _
  rw [hχ, hcast]
  have hpow : ∀ w : ℂ, ((p : ℂ) ^ (k + 1)) ^ w = (p : ℂ) ^ (((k + 1 : ℕ) : ℂ) * w) := by
    intro w
    rw [← Complex.natCast_cpow_natCast_mul]
    norm_cast
  have hmulpow : ∀ w : ℂ, ((p : ℂ) ^ w) ^ (k + 1) = (p : ℂ) ^ (((k + 1 : ℕ) : ℂ) * w) := by
    intro w
    rw [← Complex.cpow_nat_mul]
  rw [hpow, hpow, mul_pow, hmulpow]
  have hsplit : ((k + 1 : ℕ) : ℂ) * (-(s + I * (θ : ℂ))) =
      ((k + 1 : ℕ) : ℂ) * (-(I * (θ : ℂ))) + (-(((k + 1 : ℕ) : ℂ) * s)) := by ring
  rw [hsplit, Complex.cpow_add _ _ hpc, Complex.cpow_neg]
  push_cast
  ring

/-- The Dirichlet series of the Euler logarithm is the prime sum of `−log(1 − χ(p) p^{−(s+iθ)})`. -/
theorem lSeries_dirichletLogCoeff_eq_primeLog {s : ℂ} (hs : 1 < s.re) :
    LSeries (dirichletLogCoeff χ θ) s =
      ∑' p : Nat.Primes, -Complex.log (1 - χ p * (p : ℂ) ^ (-(s + I * (θ : ℂ)))) := by
  rw [LSeries]
  have hsum : Summable (LSeries.term (dirichletLogCoeff χ θ) s) :=
    lSeriesSummable_dirichletLogCoeff χ θ hs
  rw [tsum_eq_tsum_primes_of_support_subset_prime_powers hsum]
  · apply tsum_congr
    intro p
    have hnorm : ‖χ p * (p : ℂ) ^ (-(s + I * (θ : ℂ)))‖ < 1 := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by exact_mod_cast p.prop.pos), Complex.neg_re,
        re_add_shift]
      have hp1 : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
      have hlt : (p : ℝ) ^ (-s.re) < 1 := by
        calc (p : ℝ) ^ (-s.re) < (p : ℝ) ^ (0 : ℝ) :=
              Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
          _ = 1 := Real.rpow_zero _
      calc _ ≤ 1 * (p : ℝ) ^ (-s.re) :=
            mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (by positivity)
        _ < 1 := by linarith
    have hseries := Complex.hasSum_taylorSeries_neg_log hnorm
    rw [← hseries.tsum_eq, hseries.summable.tsum_eq_zero_add]
    simp only [Nat.cast_zero, div_zero, zero_add]
    apply tsum_congr
    intro k
    exact term_dirichletLogCoeff_prime_pow χ θ p.prop s k
  · intro n hn
    by_contra hpp
    apply hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn0, dirichletLogCoeff_apply,
        eulerLogDirichletCoeff_eq_zero_of_not_primePower hpp]
      simp

/-- **The Euler product of `L(s + iθ, χ)`.** -/
theorem exp_lSeries_dirichletLogCoeff [NeZero N] {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (LSeries (dirichletLogCoeff χ θ) s) =
      DirichletCharacter.LFunction χ (s + I * (θ : ℂ)) := by
  rw [lSeries_dirichletLogCoeff_eq_primeLog χ θ hs,
    DirichletCharacter.LFunction_eq_LSeries χ (by rwa [re_add_shift])]
  exact DirichletCharacter.LSeries_eulerProduct_exp_log χ (by rwa [re_add_shift])

end GaloisForLFunctions.SelbergClass.DegreeOne
