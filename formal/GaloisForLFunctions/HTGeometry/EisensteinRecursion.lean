import GaloisForLFunctions.HTGeometry.HenselDefectRoot

/-!
# The coefficient recursion of an algebraic power series

If `y` is a root of a polynomial `F` over a power-series ring and the derivative `F′(y)` vanishes
to order `r`, then beyond degree `r` every coefficient of `y` is *determined* by the earlier ones:

`(F′(y))_r · y_n = − (F(y_{<n}))_{n+r}`   for `n > r`,

where `y_{<n}` is the truncation of `y` below degree `n`.  The right-hand side involves only
`y_0, …, y_{n-1}`, so this is a genuine recursion, and it is the engine of Eisenstein's theorem on
algebraic power series: the denominator of `y_n` is controlled by one fixed element, `(F′(y))_r`,
together with the denominators already accumulated.

The proof is the second-order Taylor expansion at the truncation.  Writing `y = y_{<n} + η` with
`η` divisible by `Xⁿ`, the quadratic remainder is divisible by `X^{2n}` and so invisible in degree
`n + r` as soon as `n > r`; the linear term contributes `∑_{j≥n} (F′(y_{<n}))_{n+r-j} · y_j`, and
`F′(y_{<n})` agrees with `F′(y)` below degree `n`, whose coefficients below `r` vanish — leaving the
single term `j = n`.

Nothing here needs `F` monic, a field, or a domain.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial PowerSeries

variable {S : Type*} [CommRing S]

/-- The truncation of a power series below a given degree, again as a power series. -/
noncomputable def truncPS (n : ℕ) (y : PowerSeries S) : PowerSeries S :=
  PowerSeries.mk fun j => if j < n then PowerSeries.coeff j y else 0

@[simp]
theorem coeff_truncPS (n j : ℕ) (y : PowerSeries S) :
    PowerSeries.coeff j (truncPS n y) = if j < n then PowerSeries.coeff j y else 0 :=
  PowerSeries.coeff_mk _ _

theorem X_pow_dvd_sub_truncPS (n : ℕ) (y : PowerSeries S) :
    (PowerSeries.X : PowerSeries S) ^ n ∣ (y - truncPS n y) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  rw [map_sub, coeff_truncPS, if_pos hm, sub_self]

/-- **The Eisenstein recursion.**  Beyond the order of vanishing of the derivative, each
coefficient of a root is determined by the earlier ones, with the single denominator `(F′(y))_r`. -/
theorem coeff_deriv_mul_coeff_eq {F : (PowerSeries S)[X]} {y : PowerSeries S}
    (hroot : F.eval y = 0) {r n : ℕ} (hrn : r < n)
    (hu : ∀ j < r, PowerSeries.coeff j ((Polynomial.derivative F).eval y) = 0) :
    PowerSeries.coeff r ((Polynomial.derivative F).eval y) * PowerSeries.coeff n y
      = - PowerSeries.coeff (n + r) (F.eval (truncPS n y)) := by
  classical
  have hηdvd : (PowerSeries.X : PowerSeries S) ^ n ∣ (y - truncPS n y) :=
    X_pow_dvd_sub_truncPS n y
  have hyw : truncPS n y + (y - truncPS n y) = y := by ring
  obtain ⟨B, hB⟩ := exists_eval_add_eq F (truncPS n y) (y - truncPS n y)
  rw [hyw, hroot] at hB
  have hcoeff := congrArg (PowerSeries.coeff (n + r)) hB.symm
  rw [map_zero, map_add, map_add] at hcoeff
  -- the quadratic remainder is invisible
  have hquad : PowerSeries.coeff (n + r) ((y - truncPS n y) ^ 2 * B) = 0 := by
    have hdvd : (PowerSeries.X : PowerSeries S) ^ (n + n) ∣ (y - truncPS n y) ^ 2 * B := by
      refine Dvd.dvd.mul_right ?_ B
      rw [pow_add, sq]
      exact mul_dvd_mul hηdvd hηdvd
    rw [PowerSeries.X_pow_dvd_iff] at hdvd
    exact hdvd (n + r) (by omega)
  -- the derivative at the truncation agrees with the derivative at the root below degree `n`
  have hagree : ∀ i, i < n → PowerSeries.coeff i ((Polynomial.derivative F).eval (truncPS n y))
      = PowerSeries.coeff i ((Polynomial.derivative F).eval y) := by
    intro i hi
    have hwy : (PowerSeries.X : PowerSeries S) ^ n ∣ (truncPS n y - y) := by
      have hrw : truncPS n y - y = -(y - truncPS n y) := by ring
      rw [hrw]
      exact dvd_neg.2 hηdvd
    have hdvd : (PowerSeries.X : PowerSeries S) ^ n ∣
        ((Polynomial.derivative F).eval (truncPS n y) - (Polynomial.derivative F).eval y) :=
      dvd_trans hwy (Polynomial.sub_dvd_eval_sub _ _ (Polynomial.derivative F))
    rw [PowerSeries.X_pow_dvd_iff] at hdvd
    have hzero := hdvd i hi
    rw [map_sub, sub_eq_zero] at hzero
    exact hzero
  -- only one term of the linear part survives
  have hlin : PowerSeries.coeff (n + r)
      ((Polynomial.derivative F).eval (truncPS n y) * (y - truncPS n y))
      = PowerSeries.coeff r ((Polynomial.derivative F).eval y) * PowerSeries.coeff n y := by
    rw [PowerSeries.coeff_mul, Finset.sum_eq_single (r, n)]
    · rw [hagree r (by omega), map_sub, coeff_truncPS, if_neg (by omega), sub_zero]
    · rintro ⟨i, j⟩ hmem hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hmem
      rcases Nat.lt_or_ge j n with hjn | hjn
      · have hzero : PowerSeries.coeff j (y - truncPS n y) = 0 := by
          rw [map_sub, coeff_truncPS, if_pos hjn, sub_self]
        rw [hzero, mul_zero]
      · rcases Nat.eq_or_lt_of_le hjn with hje | hjl
        · exact absurd (Prod.ext (by omega) hje.symm) hne
        · have hir : i < r := by omega
          rw [hagree i (by omega), hu i hir, zero_mul]
    · intro hcon
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by omega)) hcon
  rw [hquad, hlin, add_zero] at hcoeff
  linear_combination hcoeff

end GaloisForLFunctions.HTGeometry
