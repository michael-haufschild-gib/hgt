import GaloisForLFunctions.HTGeometry.PolynomialVanishingOrderBound

/-!
# The forced power series solving `u² P' = -Λ P`

A balanced gamma monomial `M` satisfies `M' = L·M` with `L(s) = -∑_{m≥1} D_m s^{-(m+1)}`.  In the
variable `u = 1/s` the ansatz `M = P(u)` turns this into `-u² P'(u) = Λ(u) P(u)` with
`Λ(u) = -∑_m D_m u^{m+1}`, so the residual `Λ P + u² P'` must vanish to all orders.

Exactly as for the Stirling ladder, one new coefficient per step is forced: adding `c_N u^{N+1}` to
`P` changes the degree-`(N+2)` coefficient of the residual by `(N+1) c_N`, and nothing lower.  The
divisor `N+1` never vanishes, so the ladder never stalls.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- The truncated logarithmic-derivative series in the variable `u = 1/s`. -/
def lamPoly (D : ℕ → ℂ) (N : ℕ) : ℂ[X] :=
  -∑ m ∈ Finset.range (N + 1), C (D m) * X ^ (m + 1)

/-- The forced next coefficient. -/
def expLadderCoeffOf (D : ℕ → ℂ) (P : ℂ[X]) (N : ℕ) : ℂ :=
  (D (N + 1) - (lamPoly D N * P + X ^ 2 * derivative P).coeff (N + 2)) / ((N : ℂ) + 1)

/-- The forced truncation of the exponential series. -/
def inverseSeriesLadderExpPoly (D : ℕ → ℂ) : ℕ → ℂ[X]
  | 0 => 1
  | (N + 1) => inverseSeriesLadderExpPoly D N + C (expLadderCoeffOf D (inverseSeriesLadderExpPoly D N) N) * X ^ (N + 1)

/-- The residual of the differential equation at truncation order `N`. -/
def resPoly (D : ℕ → ℂ) (N : ℕ) : ℂ[X] :=
  lamPoly D N * inverseSeriesLadderExpPoly D N + X ^ 2 * derivative (inverseSeriesLadderExpPoly D N)

theorem lamPoly_succ (D : ℕ → ℂ) (N : ℕ) :
    lamPoly D (N + 1) = lamPoly D N - C (D (N + 1)) * X ^ (N + 2) := by
  rw [lamPoly, lamPoly, Finset.sum_range_succ]
  ring

theorem X_dvd_lamPoly (D : ℕ → ℂ) (N : ℕ) : X ∣ lamPoly D N := by
  rw [lamPoly]
  refine dvd_neg.mpr (Finset.dvd_sum fun m _ => ?_)
  exact Dvd.dvd.mul_left (dvd_pow_self X (Nat.succ_ne_zero m)) _

theorem coeff_one_lamPoly (D : ℕ → ℂ) (N : ℕ) : (lamPoly D N).coeff 1 = -D 0 := by
  rw [lamPoly, Polynomial.coeff_neg, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro m _ hm
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp [hm]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos N)) h

theorem coeff_zero_expPoly (D : ℕ → ℂ) (N : ℕ) : (inverseSeriesLadderExpPoly D N).coeff 0 = 1 := by
  induction N with
  | zero => simp [inverseSeriesLadderExpPoly]
  | succ n ih =>
      rw [inverseSeriesLadderExpPoly, Polynomial.coeff_add, ih, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp

theorem resPoly_succ (D : ℕ → ℂ) (N : ℕ) :
    resPoly D (N + 1)
      = resPoly D N
        + C (expLadderCoeffOf D (inverseSeriesLadderExpPoly D N) N) * X ^ (N + 1) * lamPoly D N
        - C (D (N + 1)) * X ^ (N + 2) * inverseSeriesLadderExpPoly D (N + 1)
        + C (expLadderCoeffOf D (inverseSeriesLadderExpPoly D N) N) * C (((N + 1 : ℕ) : ℂ)) * X ^ (N + 2) := by
  have hexp : inverseSeriesLadderExpPoly D (N + 1)
      = inverseSeriesLadderExpPoly D N + C (expLadderCoeffOf D (inverseSeriesLadderExpPoly D N) N) * X ^ (N + 1) := rfl
  have hder : derivative (inverseSeriesLadderExpPoly D (N + 1))
      = derivative (inverseSeriesLadderExpPoly D N)
        + C (expLadderCoeffOf D (inverseSeriesLadderExpPoly D N) N) * (C (((N + 1 : ℕ) : ℂ)) * X ^ N) := by
    rw [hexp, derivative_add, derivative_C_mul, derivative_X_pow]
    simp
  rw [resPoly, resPoly, lamPoly_succ, hder, hexp]
  ring

/-- **The residual vanishes to order `N+2`.**  One coefficient per step, forced, with divisor
`N+1`. -/
theorem X_pow_dvd_resPoly (D : ℕ → ℂ) (hD0 : D 0 = 0) (N : ℕ) :
    X ^ (N + 2) ∣ resPoly D N := by
  induction N with
  | zero =>
      have h : lamPoly D 0 = 0 := by
        rw [lamPoly]
        simp [hD0]
      have hexp : inverseSeriesLadderExpPoly D 0 = 1 := rfl
      rw [resPoly, h, hexp]
      simp
  | succ n ih =>
      have hstep := resPoly_succ D n
      set c := expLadderCoeffOf D (inverseSeriesLadderExpPoly D n) n with hc
      have hdvd : X ^ (n + 2) ∣ resPoly D (n + 1) := by
        rw [hstep]
        obtain ⟨q, hq⟩ := X_dvd_lamPoly D n
        refine dvd_add (dvd_sub (dvd_add ih ?_) ?_) ?_
        · refine ⟨C c * q, ?_⟩
          rw [hq]
          ring
        · exact ⟨C (D (n + 1)) * inverseSeriesLadderExpPoly D (n + 1), by ring⟩
        · exact ⟨C c * C (((n + 1 : ℕ) : ℂ)), by ring⟩
      have hcoeff : (resPoly D (n + 1)).coeff (n + 2) = 0 := by
        have h2 : (C c * X ^ (n + 1) * lamPoly D n).coeff (n + 2) = 0 := by
          have hrw : C c * X ^ (n + 1) * lamPoly D n = C c * (X ^ (n + 1) * lamPoly D n) := by ring
          have hx := Polynomial.coeff_X_pow_mul (lamPoly D n) (n + 1) 1
          rw [show 1 + (n + 1) = n + 2 from by omega] at hx
          rw [hrw, Polynomial.coeff_C_mul, hx, coeff_one_lamPoly, hD0]
          ring
        have h3 : (C (D (n + 1)) * X ^ (n + 2) * inverseSeriesLadderExpPoly D (n + 1)).coeff (n + 2)
            = D (n + 1) := by
          have hrw : C (D (n + 1)) * X ^ (n + 2) * inverseSeriesLadderExpPoly D (n + 1)
              = C (D (n + 1)) * (X ^ (n + 2) * inverseSeriesLadderExpPoly D (n + 1)) := by ring
          have hx := Polynomial.coeff_X_pow_mul (inverseSeriesLadderExpPoly D (n + 1)) (n + 2) 0
          rw [zero_add] at hx
          rw [hrw, Polynomial.coeff_C_mul, hx, coeff_zero_expPoly]
          ring
        have h4 : (C c * C (((n + 1 : ℕ) : ℂ)) * X ^ (n + 2)).coeff (n + 2)
            = c * (((n + 1 : ℕ) : ℂ)) := by
          rw [← C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
        have hne : ((n : ℂ) + 1) ≠ 0 := by
          intro hcon
          have hre : ((n : ℂ) + 1).re = (n : ℝ) + 1 := by simp
          rw [hcon] at hre
          simp only [Complex.zero_re] at hre
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        have hcval : c * (((n + 1 : ℕ) : ℂ)) = D (n + 1) - (resPoly D n).coeff (n + 2) := by
          rw [hc, expLadderCoeffOf]
          have hres : (lamPoly D n * inverseSeriesLadderExpPoly D n + X ^ 2 * derivative (inverseSeriesLadderExpPoly D n)).coeff (n + 2)
              = (resPoly D n).coeff (n + 2) := rfl
          rw [hres]
          push_cast
          field_simp
        rw [hstep, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_add, h2, h3, h4,
          hcval]
        ring
      rw [Polynomial.X_pow_dvd_iff]
      intro d hd
      rcases (by omega : d < n + 2 ∨ d = n + 2) with h | h
      · exact (Polynomial.X_pow_dvd_iff.mp hdvd) d h
      · rw [h]; exact hcoeff

end

end GaloisForLFunctions.HTGeometry
