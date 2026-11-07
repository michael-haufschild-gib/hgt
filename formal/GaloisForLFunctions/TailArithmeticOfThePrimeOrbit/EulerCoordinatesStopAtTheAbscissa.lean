import Mathlib

/-!
# Euler coordinates stop at the abscissa

Prime torus theory certifies `S = E(s)/(s + 3)`, `E = ζ(2s − 1)/ζ(2s)`, on `Re s > 2` by a product decomposition in
coordinates `z_p = (s + 3)^{−α_p} E_p(s)` that do not return, with `E_p(s) = (1 − p^{−2s})/(1 − p^{1−2s})`. Product
decompositions need `Σ_p |1 − z_p| < ∞`. Which certificates in non-returning coordinates survive past `Re s = 1`?

* **The abscissa is a wall for Euler coordinates** (`summable_one_sub_scatteringFactor_iff`). On `Re s > ½`,
  `Σ_p |1 − E_p(s)| < ∞` exactly when `Re s > 1`: `|E_p(s) − 1| ≥ p^{1−2σ}/4` (`le_norm_scatteringFactor_sub_one`), and
  `Σ_p p^{1−2σ}` diverges at `σ ≤ 1` with `Σ 1/p`.
* **No perturbation helps** (`not_summable_of_summable_sub`). Coordinates within summable distance of the Euler factors,
  such as `(s + 3)^{−α_p} E_p` with `Σ α_p < ∞`, have `Σ_p |1 − z_p| = ∞` at every point of `½ < Re s ≤ 1`. Prime-by-prime
  product certificates do not cross the abscissa, whatever share of the Gamma factor each prime receives.
* **What survives: head and tail** (`certificate_of_factorization`, `headTail_certificate`). Every finite factorization
  `S = z_0 ⋯ z_{n−1}` is a decomposition `1 − S(x)S̄(y) = Σ_i (1 − z_i(x)z̄_i(y)) K_i(x, y)` with rank-one kernels
  `K_i = w_i(x) w̄_i(y)`, `w_i = z_0 ⋯ z_{i−1}`. Take the Euler coordinates of the primes up to `y` and one tail
  coordinate `S/(z_0 ⋯ z_{n−1})`. The certificate exists wherever every coordinate is Schur, and the tail coordinate is
  Schur exactly where `|S| ≤ |z_0 ⋯ z_{n−1}|` (`norm_tailCoordinate_le_one_iff`).

So past the abscissa the certificate question in non-returning coordinates is the size of the tail: a certificate exists
at the heights where the tail of `S` past the head is at most the head. This is a tail-good condition in the sense of
the Euler tail law, which holds at typical heights and fails at the rare heights where a return to a zero would sit.
-/

open Complex Finset

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

noncomputable section

local notation "conj" => starRingEnd ℂ

/-- The Euler factor `E_p(s) = (1 − p^{−2s})/(1 − p^{1−2s})` of `ζ(2s − 1)/ζ(2s)`. -/
def scatteringFactor (p : ℕ) (s : ℂ) : ℂ := (1 - (p : ℂ) ^ (-(2 * s))) / (1 - (p : ℂ) ^ (1 - 2 * s))

theorem norm_cpow_eq {p : ℕ} (hp : 0 < p) (w : ℂ) : ‖(p : ℂ) ^ w‖ = (p : ℝ) ^ w.re :=
  Complex.norm_natCast_cpow_of_pos hp w

theorem cpow_one_sub_two_mul {p : ℕ} (hp : 0 < p) (s : ℂ) :
    (p : ℂ) ^ (1 - 2 * s) = (p : ℂ) * (p : ℂ) ^ (-(2 * s)) := by
  rw [sub_eq_add_neg, Complex.cpow_add _ _ (by exact_mod_cast hp.ne'), Complex.cpow_one]

theorem scatteringFactor_sub_one {p : ℕ} (hp : 0 < p) {s : ℂ} (hden : 1 - (p : ℂ) ^ (1 - 2 * s) ≠ 0) :
    scatteringFactor p s - 1 = (p : ℂ) ^ (-(2 * s)) * ((p : ℂ) - 1) / (1 - (p : ℂ) ^ (1 - 2 * s)) := by
  unfold scatteringFactor
  rw [div_sub_one hden, cpow_one_sub_two_mul hp]
  congr 1
  ring

theorem norm_cpow_one_sub_lt {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖(p : ℂ) ^ (1 - 2 * s)‖ < 1 := by
  rw [norm_cpow_eq (by omega)]
  have hre : (1 - 2 * s).re = 1 - 2 * s.re := by simp
  rw [hre]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < p)) (by linarith)

theorem den_ne_zero {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 1 / 2 < s.re) : 1 - (p : ℂ) ^ (1 - 2 * s) ≠ 0 := by
  intro h
  have h1 := norm_cpow_one_sub_lt hp hs
  rw [← sub_eq_zero.mp h, norm_one] at h1
  exact lt_irrefl _ h1

theorem norm_num_eq {p : ℕ} (hp : 2 ≤ p) (s : ℂ) :
    ‖(p : ℂ) ^ (-(2 * s)) * ((p : ℂ) - 1)‖ = (p : ℝ) ^ (-2 * s.re) * ((p : ℝ) - 1) := by
  rw [norm_mul, norm_cpow_eq (by omega)]
  have hre : (-(2 * s)).re = -2 * s.re := by simp
  rw [hre]
  congr 1
  have : ((p : ℂ) - 1) = (((p : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith)]

theorem rpow_mul_sub_one {p : ℕ} (hp : 0 < p) (σ : ℝ) :
    (p : ℝ) ^ (-2 * σ) * (p : ℝ) = (p : ℝ) ^ (1 - 2 * σ) := by
  rw [show 1 - 2 * σ = -2 * σ + 1 by ring, Real.rpow_add (by exact_mod_cast hp), Real.rpow_one]

/-- **The Euler factor stays away from `1`.** `|E_p(s) − 1| ≥ p^{1−2σ}/4` on `Re s > ½`. -/
theorem le_norm_scatteringFactor_sub_one {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 1 / 2 < s.re) :
    (p : ℝ) ^ (1 - 2 * s.re) / 4 ≤ ‖scatteringFactor p s - 1‖ := by
  have hp0 : 0 < p := by omega
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  rw [scatteringFactor_sub_one hp0 (den_ne_zero hp hs), norm_div, norm_num_eq hp]
  have hden : ‖1 - (p : ℂ) ^ (1 - 2 * s)‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one]
    linarith [norm_cpow_one_sub_lt hp hs]
  have hden0 : 0 < ‖1 - (p : ℂ) ^ (1 - 2 * s)‖ := norm_pos_iff.mpr (den_ne_zero hp hs)
  have hrp : 0 < (p : ℝ) ^ (-2 * s.re) := Real.rpow_pos_of_pos (by linarith) _
  have hnum : (p : ℝ) ^ (1 - 2 * s.re) / 2 ≤ (p : ℝ) ^ (-2 * s.re) * ((p : ℝ) - 1) := by
    rw [← rpow_mul_sub_one hp0]
    nlinarith
  rw [le_div_iff₀ hden0]
  have h0 : 0 ≤ (p : ℝ) ^ (1 - 2 * s.re) := by positivity
  nlinarith

/-- `|E_p(s) − 1| ≤ p^{1−2σ}/(1 − 2^{1−2σ})` on `Re s > ½`. -/
theorem norm_scatteringFactor_sub_one_le {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖scatteringFactor p s - 1‖ ≤ (p : ℝ) ^ (1 - 2 * s.re) / (1 - (2 : ℝ) ^ (1 - 2 * s.re)) := by
  have hp0 : 0 < p := by omega
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h2 : (2 : ℝ) ^ (1 - 2 * s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hle : (p : ℝ) ^ (1 - 2 * s.re) ≤ (2 : ℝ) ^ (1 - 2 * s.re) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hpR (by linarith)
  rw [scatteringFactor_sub_one hp0 (den_ne_zero hp hs), norm_div, norm_num_eq hp]
  have hden : 1 - (2 : ℝ) ^ (1 - 2 * s.re) ≤ ‖1 - (p : ℂ) ^ (1 - 2 * s)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (1 - 2 * s))
    rw [norm_one, norm_cpow_eq hp0] at h
    have hre : (1 - 2 * s).re = 1 - 2 * s.re := by simp
    rw [hre] at h
    linarith
  have hnum : (p : ℝ) ^ (-2 * s.re) * ((p : ℝ) - 1) ≤ (p : ℝ) ^ (1 - 2 * s.re) := by
    rw [← rpow_mul_sub_one hp0]
    have : 0 < (p : ℝ) ^ (-2 * s.re) := Real.rpow_pos_of_pos (by linarith) _
    nlinarith
  calc (p : ℝ) ^ (-2 * s.re) * ((p : ℝ) - 1) / ‖1 - (p : ℂ) ^ (1 - 2 * s)‖
      ≤ (p : ℝ) ^ (1 - 2 * s.re) / ‖1 - (p : ℂ) ^ (1 - 2 * s)‖ :=
        div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ (p : ℝ) ^ (1 - 2 * s.re) / (1 - (2 : ℝ) ^ (1 - 2 * s.re)) :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) hden

/-- **The abscissa is a wall for Euler coordinates.** -/
theorem summable_one_sub_scatteringFactor_iff {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun p : Nat.Primes => ‖1 - scatteringFactor p s‖) ↔ 1 < s.re := by
  constructor
  · intro h
    by_contra hle
    push Not at hle
    refine Nat.Primes.not_summable_one_div ((h.mul_left 4).of_nonneg_of_le (fun _ => by positivity) fun p => ?_)
    have hp2 := p.2.two_le
    have hpR : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ (p : ℕ))
    have h1 := le_norm_scatteringFactor_sub_one hp2 hs
    have h2 : ((p : ℕ) : ℝ) ^ (-1 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (1 - 2 * s.re) :=
      Real.rpow_le_rpow_of_exponent_le hpR (by linarith)
    rw [Real.rpow_neg_one] at h2
    rw [norm_sub_rev, one_div]
    linarith
  · intro h1
    have hsum : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (1 - 2 * s.re)) :=
      Nat.Primes.summable_rpow.mpr (by linarith)
    refine (hsum.div_const (1 - (2 : ℝ) ^ (1 - 2 * s.re))).of_nonneg_of_le (fun _ => norm_nonneg _) fun p => ?_
    rw [norm_sub_rev]
    exact norm_scatteringFactor_sub_one_le p.2.two_le hs

/-- **No perturbation helps.** Coordinates within summable distance of the Euler factors are not summably close to `1`
at any point of `½ < Re s ≤ 1`. -/
theorem not_summable_of_summable_sub {s : ℂ} (hs1 : 1 / 2 < s.re) (hs2 : s.re ≤ 1) (z : Nat.Primes → ℂ)
    (hz : Summable fun p : Nat.Primes => ‖z p - scatteringFactor p s‖) :
    ¬ Summable fun p : Nat.Primes => ‖1 - z p‖ := by
  intro h
  have hE : Summable fun p : Nat.Primes => ‖1 - scatteringFactor p s‖ :=
    (h.add hz).of_nonneg_of_le (fun _ => norm_nonneg _) fun p => by
      calc ‖1 - scatteringFactor p s‖ = ‖(1 - z p) + (z p - scatteringFactor p s)‖ := by
            congr 1
            ring
        _ ≤ _ := norm_add_le _ _
  exact absurd ((summable_one_sub_scatteringFactor_iff hs1).mp hE) (not_lt.mpr hs2)

/-! ## What survives: head and tail -/

/-- `1 − Π a_i = Σ_i (1 − a_i) Π_{m<i} a_m`. -/
theorem one_sub_prod_eq_sum (a : ℕ → ℂ) (n : ℕ) :
    1 - ∏ i ∈ range n, a i = ∑ i ∈ range n, (1 - a i) * ∏ m ∈ range i, a m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, sum_range_succ, ← ih]
    ring

/-- **A factorization is a certificate.** The kernels `(Π_{m<i} z_m(x)) conj(Π_{m<i} z_m(y))` have rank one. -/
theorem certificate_of_factorization {X : Type*} (z : ℕ → X → ℂ) (n : ℕ) (x y : X) :
    1 - (∏ i ∈ range n, z i x) * conj (∏ i ∈ range n, z i y) =
      ∑ i ∈ range n, (1 - z i x * conj (z i y)) * ((∏ m ∈ range i, z m x) * conj (∏ m ∈ range i, z m y)) := by
  have h := one_sub_prod_eq_sum (fun i => z i x * conj (z i y)) n
  simp only [prod_mul_distrib] at h
  simp only [map_prod]
  exact h

/-- The tail coordinate `S/(z_0 ⋯ z_{n−1})`. -/
def tailCoordinate {X : Type*} (S : X → ℂ) (z : ℕ → X → ℂ) (n : ℕ) (x : X) : ℂ := S x / ∏ i ∈ range n, z i x

/-- The head coordinates followed by the tail coordinate. -/
def headTailCoordinates {X : Type*} (S : X → ℂ) (z : ℕ → X → ℂ) (n : ℕ) (i : ℕ) : X → ℂ :=
  if i < n then z i else tailCoordinate S z n

/-- The tail coordinate is Schur exactly where `S` is at most the head. -/
theorem norm_tailCoordinate_le_one_iff {X : Type*} (S : X → ℂ) (z : ℕ → X → ℂ) (n : ℕ) {x : X}
    (hne : ∏ i ∈ range n, z i x ≠ 0) :
    ‖tailCoordinate S z n x‖ ≤ 1 ↔ ‖S x‖ ≤ ‖∏ i ∈ range n, z i x‖ := by
  rw [tailCoordinate, norm_div, div_le_one (norm_pos_iff.mpr hne)]

theorem prod_headTailCoordinates {X : Type*} (S : X → ℂ) (z : ℕ → X → ℂ) (n : ℕ) {x : X}
    (hne : ∏ i ∈ range n, z i x ≠ 0) : ∏ i ∈ range (n + 1), headTailCoordinates S z n i x = S x := by
  rw [prod_range_succ]
  have hhead : ∏ i ∈ range n, headTailCoordinates S z n i x = ∏ i ∈ range n, z i x :=
    prod_congr rfl fun i hi => by
      rw [headTailCoordinates, if_pos (mem_range.mp hi)]
  rw [hhead, headTailCoordinates, if_neg (lt_irrefl n), tailCoordinate]
  field_simp

/-- **The head–tail certificate.** Wherever the head does not vanish, `S` has the rank-one decomposition with the head
coordinates and the tail coordinate. -/
theorem headTail_certificate {X : Type*} (S : X → ℂ) (z : ℕ → X → ℂ) (n : ℕ) {x y : X}
    (hx : ∏ i ∈ range n, z i x ≠ 0) (hy : ∏ i ∈ range n, z i y ≠ 0) :
    1 - S x * conj (S y) =
      ∑ i ∈ range (n + 1), (1 - headTailCoordinates S z n i x * conj (headTailCoordinates S z n i y)) *
        ((∏ m ∈ range i, headTailCoordinates S z n m x) * conj (∏ m ∈ range i, headTailCoordinates S z n m y)) := by
  rw [← certificate_of_factorization, prod_headTailCoordinates S z n hx, prod_headTailCoordinates S z n hy]

end

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
