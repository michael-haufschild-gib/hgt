import GaloisForLFunctions.RHTower.PrimeWinningFaceSeries

/-!
# The face function carries exactly the zeta divisor

On the Euler half-plane the winner-face Dirichlet series equals `ζ · U_{F,m}`, and the right-hand
side continues to the strict critical half-plane, where the face unit is holomorphic and
nonvanishing.  The continued face function therefore has the same analytic order as `ζ` at every
point of that half-plane, its jets below the zeta multiplicity vanish, and its leading jet is the
zeta jet times the face unit.  Adjoining a prime multiplies the leading jet by that prime's
transition factor alone.
-/

open Complex

noncomputable section

namespace RHTower

/-- The continued face function `ζ(s) U_{F,m}(s)`. -/
def faceFunction (F : Finset Nat.Primes) (m : ℕ) (s : ℂ) : ℂ :=
  riemannZeta s * faceUnit F m s

theorem faceFunction_eq_faceSeries {F : Finset Nat.Primes} {m : ℕ} {s : ℂ} (hs : 1 < s.re) :
    faceFunction F m s = faceSeries F m s :=
  (faceSeries_eq_zeta_mul_faceUnit hs).symm

theorem faceFunction_ne_zero_of_riemannZeta_ne_zero {F : Finset Nat.Primes} {m : ℕ} (hm : 1 ≤ m)
    {s : ℂ} (hs : 1 / 2 < s.re) (hζ : riemannZeta s ≠ 0) : faceFunction F m s ≠ 0 :=
  mul_ne_zero hζ (faceUnit_ne_zero hm hs F)

/-! ## Analyticity -/

theorem analyticAt_faceUnit {F : Finset Nat.Primes} {m : ℕ} (hm : 1 ≤ m) {s : ℂ}
    (hs : 1 / 2 < s.re) : AnalyticAt ℂ (faceUnit F m) s := by
  rw [analyticAt_iff_eventually_differentiableAt]
  have hopen : IsOpen {z : ℂ | 1 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.eventually_mem hs] with z hz
  exact differentiableAt_faceUnit hm hz F

theorem analyticAt_faceFunction {F : Finset Nat.Primes} {m : ℕ} (hm : 1 ≤ m) {s : ℂ}
    (hs : 1 / 2 < s.re) (hne : s ≠ 1) : AnalyticAt ℂ (faceFunction F m) s :=
  (analyticOn_riemannZeta s (by simpa using hne)).mul (analyticAt_faceUnit hm hs)

/-! ## The face divisor -/

/-- **Every face carries exactly the zeta divisor.**  On the strict critical half-plane the
continued face function and `ζ` have the same analytic order, with multiplicity. -/
theorem analyticOrderAt_faceFunction {F : Finset Nat.Primes} {m : ℕ} (hm : 1 ≤ m) {s : ℂ}
    (hs : 1 / 2 < s.re) (hne : s ≠ 1) :
    analyticOrderAt (faceFunction F m) s = analyticOrderAt riemannZeta s := by
  have hZ : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s (by simpa using hne)
  have hU : AnalyticAt ℂ (faceUnit F m) s := analyticAt_faceUnit hm hs
  have hmul : faceFunction F m = riemannZeta * faceUnit F m := rfl
  rw [hmul, analyticOrderAt_mul hZ hU,
    hU.analyticOrderAt_eq_zero.mpr (faceUnit_ne_zero hm hs F), add_zero]

/-! ## Jets at a zeta zero -/

theorem iteratedDeriv_faceFunction_eq_zero {F : Finset Nat.Primes} {m : ℕ} (hm : 1 ≤ m) {s : ℂ}
    (hs : 1 / 2 < s.re) (hne : s ≠ 1) {d : ℕ}
    (hvanish : ∀ j < d, iteratedDeriv j riemannZeta s = 0) {j : ℕ} (hj : j < d) :
    iteratedDeriv j (faceFunction F m) s = 0 := by
  have hZ : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s (by simpa using hne)
  have hU : AnalyticAt ℂ (faceUnit F m) s := analyticAt_faceUnit hm hs
  have hmul : faceFunction F m = riemannZeta * faceUnit F m := rfl
  rw [hmul, iteratedDeriv_mul hZ.contDiffAt hU.contDiffAt]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [hvanish i (by omega), mul_zero, zero_mul]

/-- **The leading face jet.**  At a zeta zero of order `d` the `d`-th face jet is the zeta jet
times the face unit. -/
theorem iteratedDeriv_faceFunction {F : Finset Nat.Primes} {m : ℕ} (hm : 1 ≤ m) {s : ℂ}
    (hs : 1 / 2 < s.re) (hne : s ≠ 1) {d : ℕ}
    (hvanish : ∀ j < d, iteratedDeriv j riemannZeta s = 0) :
    iteratedDeriv d (faceFunction F m) s = iteratedDeriv d riemannZeta s * faceUnit F m s := by
  have hZ : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s (by simpa using hne)
  have hU : AnalyticAt ℂ (faceUnit F m) s := analyticAt_faceUnit hm hs
  have hmul : faceFunction F m = riemannZeta * faceUnit F m := rfl
  rw [hmul, iteratedDeriv_mul hZ.contDiffAt hU.contDiffAt, Finset.sum_eq_single d]
  · rw [Nat.choose_self, Nat.sub_self, iteratedDeriv_zero, Nat.cast_one, one_mul]
  · intro i hi hid
    rw [Finset.mem_range] at hi
    rw [hvanish i (by omega), mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.self_mem_range_succ d) h

theorem iteratedDeriv_faceFunction_ne_zero {F : Finset Nat.Primes} {m : ℕ} (hm : 1 ≤ m) {s : ℂ}
    (hs : 1 / 2 < s.re) (hne : s ≠ 1) {d : ℕ}
    (hvanish : ∀ j < d, iteratedDeriv j riemannZeta s = 0)
    (hlead : iteratedDeriv d riemannZeta s ≠ 0) :
    iteratedDeriv d (faceFunction F m) s ≠ 0 := by
  rw [iteratedDeriv_faceFunction hm hs hne hvanish]
  exact mul_ne_zero hlead (faceUnit_ne_zero hm hs F)

/-! ## The principal conormal transition -/

/-- **Flat transition of the leading jet.**  Adjoining a prime to a face multiplies the leading
face jet by that prime's transition factor. -/
theorem iteratedDeriv_faceFunction_insert {F : Finset Nat.Primes} {p : Nat.Primes} (hp : p ∉ F)
    {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs : 1 / 2 < s.re) (hne : s ≠ 1) {d : ℕ}
    (hvanish : ∀ j < d, iteratedDeriv j riemannZeta s = 0) :
    iteratedDeriv d (faceFunction (insert p F) m) s =
      faceTransitionUnit p m s * iteratedDeriv d (faceFunction F m) s := by
  rw [iteratedDeriv_faceFunction hm hs hne hvanish, iteratedDeriv_faceFunction hm hs hne hvanish,
    faceUnit_insert hp]
  ring

/-- **The principal conormal transition chart.**  At a zeta zero of order `d` the ratio of leading
face jets across a one-prime enlargement is exactly the transition factor. -/
theorem iteratedDeriv_faceFunction_ratio {F : Finset Nat.Primes} {p : Nat.Primes} (hp : p ∉ F)
    {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs : 1 / 2 < s.re) (hne : s ≠ 1) {d : ℕ}
    (hvanish : ∀ j < d, iteratedDeriv j riemannZeta s = 0)
    (hlead : iteratedDeriv d riemannZeta s ≠ 0) :
    iteratedDeriv d (faceFunction (insert p F) m) s / iteratedDeriv d (faceFunction F m) s =
      faceTransitionUnit p m s := by
  rw [iteratedDeriv_faceFunction_insert hp hm hs hne hvanish]
  exact mul_div_cancel_right₀ _ (iteratedDeriv_faceFunction_ne_zero hm hs hne hvanish hlead)

end RHTower
