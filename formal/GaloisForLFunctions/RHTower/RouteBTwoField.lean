/-
The two-field architecture of the mollified carrier (doc 86 §§1–2).

Every support element factors uniquely as m = u·r (u z-smooth, r z-rough).
This module proves the exact arithmetic skeleton of the factorization
P = Σ_u u^{-1/2} X_u · W_u:

* `coprime_rough_of_le` / `smooth_dvd_of_window` — an admissible window
  divisor e ≤ z is coprime to the rough factor, hence divides the smooth
  factor: the window collapses to the smooth coordinate.
* `two_field_filter_eq` / `two_field_coeff` — the coefficient identity
  b_{u·r} = Σ_{e | u, e ≤ z, ur ≤ Ne} λ_e.
* `window_filter_empty_of_rough_gt` / `coeff_eq_zero_of_rough_gt` — on the
  support the rough factor never exceeds N (e | u ⟹ e ≤ u ⟹ r ≤ N): the
  one-line structural supersession of the two-large-primes argument in
  `RouteBSupport.boundary_coeff_eq_zero`.
* `rough_eq_one_or_prime` — at N ≤ z² the rough support ≤ N is {1} ∪ primes:
  the u = 1 row is W_1 = 1 + S exactly.
* `inner_coeff_complete` / `divisors_filter_le_of_le` — for u·p ≤ N the
  window is complete: b_{up} = Σ_{e|u, e≤z} λ_e, and for u ≤ z the full
  divisor sum.
* `inner_row_vanishes_sharp` — sharp design (λ = μ): rows 2 ≤ u ≤ z carry NO
  inner mass (Legendre identity); the boundary band is exactly their
  p > N/u tails.  Machine-checks doc 86 §2's "pure boundary rows".
-/
import Mathlib
import GaloisForLFunctions.RHTower.RouteBSupport

namespace RHTower

/-- An admissible window divisor (`e ≤ z`, `e > 0`) is coprime to any z-rough
number: a common prime would be ≤ e ≤ z and > z at once. -/
theorem coprime_rough_of_le {z e r : ℕ} (he : 0 < e) (hez : e ≤ z)
    (hrough : ∀ p, p.Prime → p ∣ r → z < p) : Nat.Coprime e r := by
  by_contra hnc
  have hg : 0 < Nat.gcd e r := Nat.gcd_pos_of_pos_left r he
  have hg1 : Nat.gcd e r ≠ 1 := hnc
  have hq : (Nat.gcd e r).minFac.Prime := Nat.minFac_prime hg1
  have hqe : (Nat.gcd e r).minFac ∣ e :=
    dvd_trans (Nat.minFac_dvd _) (Nat.gcd_dvd_left e r)
  have hqr : (Nat.gcd e r).minFac ∣ r :=
    dvd_trans (Nat.minFac_dvd _) (Nat.gcd_dvd_right e r)
  have hle : (Nat.gcd e r).minFac ≤ e := Nat.le_of_dvd he hqe
  have hgt : z < (Nat.gcd e r).minFac := hrough _ hq hqr
  omega

/-- The window collapses to the smooth factor: `e ≤ z` and `e ∣ u·r` with `r`
z-rough force `e ∣ u`. -/
theorem smooth_dvd_of_window {z u r e : ℕ} (he : 0 < e) (hez : e ≤ z)
    (hrough : ∀ p, p.Prime → p ∣ r → z < p) (hdvd : e ∣ u * r) : e ∣ u :=
  (coprime_rough_of_le he hez hrough).dvd_of_dvd_mul_right hdvd

/-- **The two-field filter identity.**  The divisor window of `u·r` equals the
divisor window of `u` (same predicate): the rough factor is invisible to the
window except through the size constraint. -/
theorem two_field_filter_eq {N z u r : ℕ} (hu : 0 < u) (hr : 0 < r)
    (hrough : ∀ p, p.Prime → p ∣ r → z < p) :
    (u * r).divisors.filter (fun e => e ≤ z ∧ u * r ≤ N * e)
      = u.divisors.filter (fun e => e ≤ z ∧ u * r ≤ N * e) := by
  ext e
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdvd, _⟩, hez, hwin⟩
    have hepos : 0 < e := Nat.pos_of_dvd_of_pos hdvd (Nat.mul_pos hu hr)
    exact ⟨⟨smooth_dvd_of_window hepos hez hrough hdvd, hu.ne'⟩, hez, hwin⟩
  · rintro ⟨⟨hdvd, _⟩, hez, hwin⟩
    exact ⟨⟨hdvd.mul_right r, (Nat.mul_pos hu hr).ne'⟩, hez, hwin⟩

/-- **The two-field coefficient identity (doc 86 §1(a)).**
`b_{u·r} = Σ_{e | u, e ≤ z, ur ≤ Ne} λ_e` for any weights. -/
theorem two_field_coeff (lam : ℕ → ℝ) {N z u r : ℕ} (hu : 0 < u) (hr : 0 < r)
    (hrough : ∀ p, p.Prime → p ∣ r → z < p) :
    ∑ e ∈ (u * r).divisors.filter (fun e => e ≤ z ∧ u * r ≤ N * e), lam e
      = ∑ e ∈ u.divisors.filter (fun e => e ≤ z ∧ u * r ≤ N * e), lam e := by
  rw [two_field_filter_eq hu hr hrough]

/-- **The rough factor never exceeds `N` on the support (doc 86 §1(b)).**
Any admissible divisor of `u·r` divides `u`, hence is ≤ u, forcing `r ≤ N`.
One line — the structural supersession of the two-large-primes argument. -/
theorem window_filter_empty_of_rough_gt {N z u r : ℕ} (hu : 0 < u) (hr : 0 < r)
    (hrough : ∀ p, p.Prime → p ∣ r → z < p) (hrN : N < r) :
    (u * r).divisors.filter (fun e => e ≤ z ∧ u * r ≤ N * e) = ∅ := by
  rw [two_field_filter_eq hu hr hrough, Finset.filter_eq_empty_iff]
  rintro e hmem ⟨_, hwin⟩
  have hdvd : e ∣ u := (Nat.mem_divisors.mp hmem).1
  have heu : e ≤ u := Nat.le_of_dvd hu hdvd
  have h1 : u * r ≤ N * u := le_trans hwin (Nat.mul_le_mul_left N heu)
  have h2 : u * r ≤ u * N := by rwa [Nat.mul_comm N u] at h1
  have h3 : r ≤ N := Nat.le_of_mul_le_mul_left h2 hu
  omega

/-- Coefficient form: `b_{u·r} = 0` whenever the rough factor exceeds `N`. -/
theorem coeff_eq_zero_of_rough_gt (lam : ℕ → ℝ) {N z u r : ℕ} (hu : 0 < u)
    (hr : 0 < r) (hrough : ∀ p, p.Prime → p ∣ r → z < p) (hrN : N < r) :
    ∑ e ∈ (u * r).divisors.filter (fun e => e ≤ z ∧ u * r ≤ N * e), lam e
      = 0 := by
  rw [window_filter_empty_of_rough_gt hu hr hrough hrN]
  exact Finset.sum_empty

/-- **The rough support up to `N` is `{1} ∪ primes` (doc 86 §1(c)).**  At
`N ≤ z²` a composite z-rough number exceeds `minFac² > z² ≥ N`. -/
theorem rough_eq_one_or_prime {z N r : ℕ} (hr : 0 < r) (hrN : r ≤ N)
    (hNz : N ≤ z * z) (hrough : ∀ p, p.Prime → p ∣ r → z < p) :
    r = 1 ∨ r.Prime := by
  rcases eq_or_ne r 1 with h1 | h1
  · exact Or.inl h1
  · right
    obtain ⟨m, hm⟩ := Nat.minFac_dvd r
    have hq : r.minFac.Prime := Nat.minFac_prime h1
    have hqz : z < r.minFac := hrough _ hq (Nat.minFac_dvd r)
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m
      · omega
      · rw [Nat.mul_one] at hm
        rw [hm]
        exact hq
    · exfalso
      have hmdvd : m ∣ r := ⟨r.minFac, by rw [Nat.mul_comm]; exact hm⟩
      have hmq : m.minFac.Prime := Nat.minFac_prime (by omega)
      have hmqz : z < m.minFac :=
        hrough _ hmq (dvd_trans (Nat.minFac_dvd m) hmdvd)
      have hzm : z < m := lt_of_lt_of_le hmqz (Nat.minFac_le (by omega))
      have hbig : z * z < r.minFac * m :=
        Nat.mul_lt_mul_of_lt_of_le hqz (le_of_lt hzm) (by omega)
      rw [← hm] at hbig
      omega

/-- For `u ≤ z` every divisor of `u` is admissible: the `e ≤ z` filter is
the full divisor set. -/
theorem divisors_filter_le_of_le {z u : ℕ} (huz : u ≤ z) :
    u.divisors.filter (fun e => e ≤ z) = u.divisors := by
  rw [Finset.filter_eq_self]
  intro e he
  have : e ∣ u := (Nat.mem_divisors.mp he).1
  have hu : u ≠ 0 := (Nat.mem_divisors.mp he).2
  exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hu) this) huz

/-- **Inner window completeness (doc 86 §2).**  For `u·p ≤ N` (p prime above
z) the size constraint is vacuous: `b_{up} = Σ_{e|u, e≤z} λ_e`. -/
theorem inner_coeff_complete (lam : ℕ → ℝ) {N z u p : ℕ} (hu : 0 < u)
    (hp : p.Prime) (hpz : z < p) (hupN : u * p ≤ N) :
    ∑ e ∈ (u * p).divisors.filter (fun e => e ≤ z ∧ u * p ≤ N * e), lam e
      = ∑ e ∈ u.divisors.filter (fun e => e ≤ z), lam e := by
  have hrough : ∀ q, q.Prime → q ∣ p → z < q := by
    intro q hq hqp
    have : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
    omega
  rw [two_field_coeff lam hu hp.pos hrough]
  congr 1
  apply Finset.filter_congr
  intro e he
  have hepos : 0 < e := Nat.pos_of_mem_divisors he
  have hwin : u * p ≤ N * e := le_trans hupN (Nat.le_mul_of_pos_right N hepos)
  simp [hwin]

/-- **Sharp-design rows `2 ≤ u ≤ z` carry no inner mass.**  With λ = μ the
complete window sum is the Legendre identity `Σ_{e|u} μ(e) = 0`: the row is
supported entirely on the boundary `p > N/u`.  Machine-checks doc 86 §2. -/
theorem inner_row_vanishes_sharp {N z u p : ℕ} (hu2 : 2 ≤ u) (huz : u ≤ z)
    (hp : p.Prime) (hpz : z < p) (hupN : u * p ≤ N) :
    ∑ e ∈ (u * p).divisors.filter (fun e => e ≤ z ∧ u * p ≤ N * e),
        ((ArithmeticFunction.moebius e : ℤ) : ℝ) = 0 := by
  rw [inner_coeff_complete _ (by omega) hp hpz hupN, divisors_filter_le_of_le huz]
  have hmu : ∑ e ∈ u.divisors, ArithmeticFunction.moebius e = 0 := by
    have h := DFunLike.congr_fun ArithmeticFunction.moebius_mul_coe_zeta u
    rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
    rw [h, if_neg (by omega)]
  calc ∑ e ∈ u.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℝ)
      = ((∑ e ∈ u.divisors, ArithmeticFunction.moebius e : ℤ) : ℝ) := by
        push_cast
        rfl
    _ = 0 := by rw [hmu]; norm_num

end RHTower
