import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Nat.Dist

/-!
# The adjunction formula on resonators: the Kronecker law

A lattice test `Σ_a c_a g(· − log a)` is a combination of Hecke cycles `Γ_a`; on narrow bumps the
prime part of the local intersection `Γ_a · Γ_b` is the **Hecke incidence**
`ratioIncidence a b + ratioIncidence b a`: the atom `Λ(m)/√m` when `b = am` or `a = bm`. On a resonator — a
`{p, q}`-smooth box `{p^i q^j : i < M, j < N}`, the support of the bi-lattice train — this
incidence is computed exactly (`heckeIncidence_box`):

    Γ_{p^i q^j} · Γ_{p^{i'} q^{j'}} = [j = j'] τ_p(|i − i'|) + [i = i'] τ_q(|j − j'|),
    τ_p(k) = Λ(p^k)/p^{k/2} = log p · p^{−k/2}.

Two Hecke cycles of a resonator interact through the primes only when they differ in **one**
exponent. The prime part of the self-intersection of the box is therefore the **Kronecker sum**
`T_p ⊗ 1 + 1 ⊗ T_q` of the two single-prime tower forms (`heckeForm_box_eq`): there is no
cross-prime prime coupling at all. The cross-prime aggregate `Σ_{p ≠ q} w_p w_q A(log(q/p))` of the
comb-energy reduction is not an intersection number of the surface; it is produced by the
Cauchy–Schwarz step. On resonators the towers couple only through the archimedean collar and the
pole.

The tower form is bounded by the **Euler envelope** `2 log p/(√p − 1)` in absolute value
(`abs_towerForm_le`, a Schur test), and the constant vector — the resonant train — attains it in
the limit: `towerForm(1) = 2 Σ_{1 ≤ k < M} (M − k) τ_p(k)` (`towerForm_one`). Hence on the box the
two envelopes **add** exactly: the prime part is at most `(E_p + E_q) Σ c²` and the bi-lattice
train realises `N·towerForm_p(1) + M·towerForm_q(1)` (`heckeForm_box_one`).
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- The prime atom `Λ(n)/√n` on `n ≥ 2` (the `vonMangoldtAtom` of `RHTower`). -/
def primeAtom (n : ℕ) : ℝ :=
  if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0

theorem primeAtom_nonneg (n : ℕ) : 0 ≤ primeAtom n := by
  unfold primeAtom
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact le_rfl

/-- The ratio atom `Λ(b/a)/√(b/a)` of the same-side pair `(log a, log b)` when `a ∣ b` (the
`ratioAtom` of `ArithmeticIncidencePositivity`). -/
def ratioIncidence (a b : ℕ) : ℝ := if a ∣ b then primeAtom (b / a) else 0

/-- The **Hecke incidence** of two integers: the ratio atom in whichever direction divides. -/
def heckeIncidence (a b : ℕ) : ℝ := ratioIncidence a b + ratioIncidence b a

/-- The tower weight `τ_p(k) = Λ(p^k)/p^{k/2}`. -/
def towerWeight (p k : ℕ) : ℝ := primeAtom (p ^ k)

theorem towerWeight_zero (p : ℕ) : towerWeight p 0 = 0 := by
  simp [towerWeight, primeAtom]

theorem towerWeight_eq {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    towerWeight p k = Real.log p / Real.sqrt ((p : ℝ) ^ k) := by
  have h2 : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  rw [towerWeight, primeAtom, if_pos h2,
    ArithmeticFunction.vonMangoldt_apply_pow (by omega), ArithmeticFunction.vonMangoldt_apply_prime hp]
  push_cast; rfl

theorem towerWeight_nonneg (p k : ℕ) : 0 ≤ towerWeight p k := primeAtom_nonneg _

/-- `τ_p(k) = log p · z^k` with `z = p^{−1/2}`. -/
theorem towerWeight_eq_geom {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    towerWeight p k = Real.log p * (1 / Real.sqrt p) ^ k := by
  have hs : Real.sqrt ((p : ℝ) ^ k) = Real.sqrt p ^ k := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by have := hp.pos; positivity), ← mul_pow,
      Real.mul_self_sqrt (Nat.cast_nonneg p)]
  rw [towerWeight_eq hp hk, hs, div_pow, one_pow, ← div_eq_mul_one_div]

section Box

variable {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
include hp hq hpq

theorem coprime_pow_pow (i j : ℕ) : Nat.Coprime (p ^ i) (q ^ j) :=
  Nat.Coprime.pow i j ((Nat.coprime_primes hp hq).mpr hpq)

/-- Divisibility in a `{p, q}`-box is the product order on exponents. -/
theorem pow_mul_pow_dvd_iff {i j i' j' : ℕ} :
    p ^ i * q ^ j ∣ p ^ i' * q ^ j' ↔ i ≤ i' ∧ j ≤ j' := by
  constructor
  · intro h
    have h1 : p ^ i ∣ p ^ i' := (coprime_pow_pow hp hq hpq i j').dvd_of_dvd_mul_right
      (dvd_trans (Dvd.intro _ rfl) h)
    have h2 : q ^ j ∣ q ^ j' := (coprime_pow_pow hp hq hpq i' j).symm.dvd_of_dvd_mul_left
      (dvd_trans (Dvd.intro_left _ rfl) h)
    exact ⟨(Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h1,
      (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact mul_dvd_mul (Nat.pow_dvd_pow p h1) (Nat.pow_dvd_pow q h2)

/-- A number divisible by two distinct primes is not a prime power. -/
theorem vonMangoldt_pow_mul_pow_eq_zero {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ArithmeticFunction.vonMangoldt (p ^ a * q ^ b) = 0 := by
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
  rintro ⟨r, k, hr, hk, hrk⟩
  have hr' := hr.nat_prime
  have hp' : p ∣ r ^ k := by rw [hrk]; exact dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
  have hq' : q ∣ r ^ k := by rw [hrk]; exact dvd_mul_of_dvd_right (dvd_pow_self q (by omega)) _
  have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr').mp (hp.dvd_of_dvd_pow hp')
  have hqr : q = r := (Nat.prime_dvd_prime_iff_eq hq hr').mp (hq.dvd_of_dvd_pow hq')
  exact hpq (hpr.trans hqr.symm)

/-- The atom of a box element: only the pure powers carry one. -/
theorem vonMangoldtAtom_box (a b : ℕ) :
    primeAtom (p ^ a * q ^ b)
      = (if b = 0 then towerWeight p a else 0) + (if a = 0 then towerWeight q b else 0) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha <;> rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [towerWeight_zero, primeAtom]
  · simp [towerWeight, hb.ne']
  · simp [towerWeight, ha.ne']
  · rw [if_neg hb.ne', if_neg ha.ne', add_zero, primeAtom,
      vonMangoldt_pow_mul_pow_eq_zero hp hq hpq ha hb]
    simp

theorem ratioIncidence_box (i j i' j' : ℕ) :
    ratioIncidence (p ^ i * q ^ j) (p ^ i' * q ^ j')
      = (if j = j' ∧ i ≤ i' then towerWeight p (i' - i) else 0)
        + (if i = i' ∧ j ≤ j' then towerWeight q (j' - j) else 0) := by
  unfold ratioIncidence
  by_cases h : i ≤ i' ∧ j ≤ j'
  · rw [if_pos ((pow_mul_pow_dvd_iff hp hq hpq).mpr h)]
    have hdiv : p ^ i' * q ^ j' / (p ^ i * q ^ j) = p ^ (i' - i) * q ^ (j' - j) := by
      rw [Nat.div_eq_of_eq_mul_left (Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _))]
      rw [mul_mul_mul_comm, ← pow_add, ← pow_add, Nat.sub_add_cancel h.1, Nat.sub_add_cancel h.2]
    rw [hdiv, vonMangoldtAtom_box hp hq hpq]
    have e1 : (j' - j = 0) ↔ (j = j' ∧ i ≤ i') := ⟨fun h0 => ⟨by omega, h.1⟩, fun h0 => by omega⟩
    have e2 : (i' - i = 0) ↔ (i = i' ∧ j ≤ j') := ⟨fun h0 => ⟨by omega, h.2⟩, fun h0 => by omega⟩
    simp only [e1, e2]
  · rw [if_neg (fun hd => h ((pow_mul_pow_dvd_iff hp hq hpq).mp hd))]
    push Not at h
    rw [if_neg (fun hh => by have := h hh.2; omega), if_neg (fun hh => by have := h hh.1.le; omega),
      add_zero]

/-- **The Kronecker law of a resonator.** Two Hecke cycles of a `{p, q}`-box meet through the
primes only when they differ in one exponent, with the tower weight of the difference. -/
theorem heckeIncidence_box (i j i' j' : ℕ) :
    heckeIncidence (p ^ i * q ^ j) (p ^ i' * q ^ j')
      = (if j = j' then towerWeight p (Nat.dist i i') else 0)
        + (if i = i' then towerWeight q (Nat.dist j j') else 0) := by
  rw [heckeIncidence, ratioIncidence_box hp hq hpq, ratioIncidence_box hp hq hpq]
  by_cases hj : j = j' <;> by_cases hi : i = i'
  · subst hj; subst hi; simp [towerWeight_zero]
  · subst hj
    rcases lt_or_gt_of_ne hi with h | h
    · simp [hi, Ne.symm hi, h.le, not_le.mpr h, Nat.dist_eq_sub_of_le h.le]
    · simp [hi, Ne.symm hi, h.le, not_le.mpr h, Nat.dist_comm i i', Nat.dist_eq_sub_of_le h.le]
  · subst hi
    rcases lt_or_gt_of_ne hj with h | h
    · simp [hj, Ne.symm hj, h.le, not_le.mpr h, Nat.dist_eq_sub_of_le h.le]
    · simp [hj, Ne.symm hj, h.le, not_le.mpr h, Nat.dist_comm j j', Nat.dist_eq_sub_of_le h.le]
  · simp [hj, hi, Ne.symm hj, Ne.symm hi]

end Box

/-- The single-prime tower form `Σ_{i, i' < M} x_i x_{i'} τ_p(|i − i'|)`. -/
def towerForm (p M : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range M, ∑ i' ∈ range M, x i * x i' * towerWeight p (Nat.dist i i')

/-- The Hecke quadratic form of a box `{p^i q^j : i < M, j < N}` with coefficients `c`. -/
def heckeForm (p q M N : ℕ) (c : ℕ × ℕ → ℝ) : ℝ :=
  ∑ x ∈ range M ×ˢ range N, ∑ y ∈ range M ×ˢ range N,
    c x * c y * heckeIncidence (p ^ x.1 * q ^ x.2) (p ^ y.1 * q ^ y.2)

/-- **The prime self-intersection of a resonator is a Kronecker sum** of tower forms: one tower
form in the `p`-direction for each `q`-level, and one in the `q`-direction for each `p`-level. -/
theorem heckeForm_box_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (M N : ℕ)
    (c : ℕ × ℕ → ℝ) :
    heckeForm p q M N c = ∑ j ∈ range N, towerForm p M (fun i => c (i, j))
      + ∑ i ∈ range M, towerForm q N (fun j => c (i, j)) := by
  have hexp : ∀ f : ℕ × ℕ → ℕ × ℕ → ℝ,
      (∑ x ∈ range M ×ˢ range N, ∑ y ∈ range M ×ˢ range N, f x y)
        = ∑ i ∈ range M, ∑ j ∈ range N, ∑ i' ∈ range M, ∑ j' ∈ range N, f (i, j) (i', j') := by
    intro f
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_product]
  unfold heckeForm towerForm
  rw [hexp]
  simp only [heckeIncidence_box hp hq hpq, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.sum_ite_eq, if_pos hj]
  · refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Finset.sum_ite_eq, if_pos hi]

/-- Geometric partial sums of the tower weights stay below the Euler envelope
`log p/(√p − 1)`. -/
theorem sum_towerWeight_le {p : ℕ} (hp : p.Prime) (K : ℕ) :
    ∑ k ∈ range K, towerWeight p (k + 1) ≤ Real.log p / (Real.sqrt p - 1) := by
  have hs : 1 < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by exact_mod_cast hp.one_lt)
  set z := 1 / Real.sqrt p
  have hz0 : 0 ≤ z := by positivity
  have hz1 : z < 1 := by rw [div_lt_one (by linarith)]; exact hs
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hterm : ∀ k ∈ range K, towerWeight p (k + 1) = Real.log p * z * z ^ k := fun k _ => by
    rw [towerWeight_eq_geom hp (by omega), pow_succ]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hgeom : ∑ k ∈ range K, z ^ k ≤ 1 / (1 - z) := by
    have h1 : (1 - z) * ∑ k ∈ range K, z ^ k = 1 - z ^ K := mul_neg_geom_sum z K
    rw [le_div_iff₀ (by linarith), mul_comm, h1]
    linarith [pow_nonneg hz0 K]
  have henv : Real.log p * z * (1 / (1 - z)) = Real.log p / (Real.sqrt p - 1) := by
    simp only [z]
    field_simp
  calc Real.log p * z * ∑ k ∈ range K, z ^ k ≤ Real.log p * z * (1 / (1 - z)) :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = _ := henv

/-- A row of the tower matrix is bounded by twice the envelope (Schur test). -/
theorem sum_towerWeight_dist_le {p : ℕ} (hp : p.Prime) (M i : ℕ) :
    ∑ i' ∈ range M, towerWeight p (Nat.dist i i') ≤ 2 * (Real.log p / (Real.sqrt p - 1)) := by
  have hsplit : ∑ i' ∈ range M, towerWeight p (Nat.dist i i')
      ≤ ∑ k ∈ range (M + i), towerWeight p (k + 1) + ∑ k ∈ range (M + i), towerWeight p (k + 1) := by
    -- each value `d ≥ 1` of `|i − i'|` is taken at most twice, and `d = 0` carries no weight
    have hle : ∀ i' ∈ range M, towerWeight p (Nat.dist i i')
        ≤ (if i' < i then towerWeight p (i - i') else 0)
          + (if i < i' then towerWeight p (i' - i) else 0) := by
      intro i' _
      rcases lt_trichotomy i' i with h | rfl | h
      · rw [if_pos h, if_neg (by omega), add_zero, Nat.dist_comm, Nat.dist_eq_sub_of_le h.le]
      · simp [Nat.dist_self, towerWeight_zero]
      · rw [if_neg (by omega), if_pos h, zero_add, Nat.dist_eq_sub_of_le h.le]
    have hA : ∑ i' ∈ range M, (if i' < i then towerWeight p (i - i') else 0)
        ≤ ∑ k ∈ range (M + i), towerWeight p (k + 1) := by
      rw [← Finset.sum_filter]
      calc ∑ i' ∈ (range M).filter (· < i), towerWeight p (i - i')
          = ∑ k ∈ ((range M).filter (· < i)).image (fun i' => i - i' - 1),
              towerWeight p (k + 1) := by
            rw [Finset.sum_image]
            · refine Finset.sum_congr rfl fun i' hi' => ?_
              have := (Finset.mem_filter.mp hi').2
              congr 1; omega
            · intro a ha b hb hab
              have := (Finset.mem_filter.mp ha).2
              have := (Finset.mem_filter.mp hb).2
              simp only at hab; omega
        _ ≤ ∑ k ∈ range (M + i), towerWeight p (k + 1) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => towerWeight_nonneg _ _)
            intro k hk
            obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hk
            have h1 := Finset.mem_range.mp (Finset.mem_filter.mp hi').1
            have h2 := (Finset.mem_filter.mp hi').2
            exact Finset.mem_range.mpr (by omega)
    have hB : ∑ i' ∈ range M, (if i < i' then towerWeight p (i' - i) else 0)
        ≤ ∑ k ∈ range (M + i), towerWeight p (k + 1) := by
      rw [← Finset.sum_filter]
      calc ∑ i' ∈ (range M).filter (i < ·), towerWeight p (i' - i)
          = ∑ k ∈ ((range M).filter (i < ·)).image (fun i' => i' - i - 1),
              towerWeight p (k + 1) := by
            rw [Finset.sum_image]
            · refine Finset.sum_congr rfl fun i' hi' => ?_
              have := (Finset.mem_filter.mp hi').2
              congr 1; omega
            · intro a ha b hb hab
              have := (Finset.mem_filter.mp ha).2
              have := (Finset.mem_filter.mp hb).2
              simp only at hab; omega
        _ ≤ ∑ k ∈ range (M + i), towerWeight p (k + 1) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => towerWeight_nonneg _ _)
            intro k hk
            obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hk
            have h1 := Finset.mem_range.mp (Finset.mem_filter.mp hi').1
            exact Finset.mem_range.mpr (by omega)
    refine (Finset.sum_le_sum hle).trans ?_
    rw [Finset.sum_add_distrib]
    exact add_le_add hA hB
  have := sum_towerWeight_le hp (M + i)
  linarith

/-- **The Euler envelope bounds every tower form**: `|towerForm| ≤ (2 log p/(√p − 1)) Σ x²`. -/
theorem abs_towerForm_le {p : ℕ} (hp : p.Prime) (M : ℕ) (x : ℕ → ℝ) :
    |towerForm p M x| ≤ 2 * (Real.log p / (Real.sqrt p - 1)) * ∑ i ∈ range M, x i ^ 2 := by
  have hterm : ∀ i ∈ range M, ∀ i' ∈ range M,
      |x i * x i' * towerWeight p (Nat.dist i i')|
        ≤ (x i ^ 2 / 2 + x i' ^ 2 / 2) * towerWeight p (Nat.dist i i') := by
    intro i _ i' _
    rw [abs_mul, abs_of_nonneg (towerWeight_nonneg _ _), abs_mul]
    have hab : abs (x i) * abs (x i') ≤ x i ^ 2 / 2 + x i' ^ 2 / 2 := by
      nlinarith [sq_nonneg (abs (x i) - abs (x i')), sq_abs (x i), sq_abs (x i')]
    exact mul_le_mul_of_nonneg_right hab (towerWeight_nonneg _ _)
  have hsym : ∑ i ∈ range M, ∑ i' ∈ range M,
      (x i ^ 2 / 2 + x i' ^ 2 / 2) * towerWeight p (Nat.dist i i')
        = ∑ i ∈ range M, x i ^ 2 * ∑ i' ∈ range M, towerWeight p (Nat.dist i i') := by
    simp only [add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i i' => x i' ^ 2 / 2 * towerWeight p (Nat.dist i i'))]
    simp_rw [Nat.dist_comm _ _]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Nat.dist_comm]; ring
  calc |towerForm p M x| ≤ ∑ i ∈ range M, ∑ i' ∈ range M, |x i * x i' * towerWeight p (Nat.dist i i')| := by
        unfold towerForm
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
          Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i ∈ range M, ∑ i' ∈ range M, (x i ^ 2 / 2 + x i' ^ 2 / 2) * towerWeight p (Nat.dist i i') :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun i' hi' => hterm i hi i' hi'
    _ = ∑ i ∈ range M, x i ^ 2 * ∑ i' ∈ range M, towerWeight p (Nat.dist i i') := hsym
    _ ≤ ∑ i ∈ range M, x i ^ 2 * (2 * (Real.log p / (Real.sqrt p - 1))) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (sum_towerWeight_dist_le hp M i)
          (sq_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- **The envelopes add on a resonator**: the prime self-intersection of a `{p, q}`-box is at most
`(E_p + E_q) Σ c²` in absolute value, `E_p = 2 log p/(√p − 1)`. -/
theorem abs_heckeForm_box_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (M N : ℕ)
    (c : ℕ × ℕ → ℝ) :
    |heckeForm p q M N c| ≤ (2 * (Real.log p / (Real.sqrt p - 1)) + 2 * (Real.log q / (Real.sqrt q - 1)))
      * ∑ x ∈ range M ×ˢ range N, c x ^ 2 := by
  rw [heckeForm_box_eq hp hq hpq, add_mul]
  have h1 : |∑ j ∈ range N, towerForm p M (fun i => c (i, j))|
      ≤ 2 * (Real.log p / (Real.sqrt p - 1)) * ∑ x ∈ range M ×ˢ range N, c x ^ 2 := by
    rw [Finset.sum_product, Finset.sum_comm, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => abs_towerForm_le hp M _)
  have h2 : |∑ i ∈ range M, towerForm q N (fun j => c (i, j))|
      ≤ 2 * (Real.log q / (Real.sqrt q - 1)) * ∑ x ∈ range M ×ˢ range N, c x ^ 2 := by
    rw [Finset.sum_product, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => abs_towerForm_le hq N _)
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- A row of distances: `Σ_{i < M} f(|i − M|) = Σ_{k < M} f(k + 1)`. -/
theorem sum_range_dist_right (f : ℕ → ℝ) (M : ℕ) :
    ∑ i ∈ range M, f (Nat.dist i M) = ∑ k ∈ range M, f (k + 1) := by
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have := Finset.mem_range.mp hk
  rw [Nat.dist_eq_sub_of_le (by omega)]
  congr 1; omega

/-- **Distance counting on a window**: `Σ_{i, i' < M} f(|i − i'|) = M f(0) + 2 Σ_{k < M} (M − 1 − k) f(k + 1)`. -/
theorem sum_range_sum_range_dist (f : ℕ → ℝ) (M : ℕ) :
    ∑ i ∈ range M, ∑ i' ∈ range M, f (Nat.dist i i')
      = M * f 0 + 2 * ∑ k ∈ range M, ((M - 1 - k : ℕ) : ℝ) * f (k + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
    rw [ih, sum_range_dist_right]
    have hcol : ∑ i' ∈ range M, f (Nat.dist M i') = ∑ k ∈ range M, f (k + 1) := by
      simp_rw [Nat.dist_comm M]; exact sum_range_dist_right f M
    rw [hcol, Nat.dist_self]
    have hshift : ∑ k ∈ range M, ((M + 1 - 1 - k : ℕ) : ℝ) * f (k + 1)
        = ∑ k ∈ range M, ((M - 1 - k : ℕ) : ℝ) * f (k + 1) + ∑ k ∈ range M, f (k + 1) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      have := Finset.mem_range.mp hk
      rw [show M + 1 - 1 - k = (M - 1 - k) + 1 by omega]
      push_cast; ring
    rw [hshift, show M + 1 - 1 - M = 0 by omega]
    push_cast; ring

/-- **The resonant train**: on the constant vector the tower form is
`2 Σ_{k < M} (M − 1 − k) τ_p(k + 1)`; divided by `M` it tends to the envelope. -/
theorem towerForm_one (p M : ℕ) :
    towerForm p M (fun _ => 1) = 2 * ∑ k ∈ range M, ((M - 1 - k : ℕ) : ℝ) * towerWeight p (k + 1) := by
  unfold towerForm
  simp only [one_mul]
  rw [sum_range_sum_range_dist, towerWeight_zero, mul_zero, zero_add]

/-- On the constant coefficient vector of a box (the bi-lattice train) the Kronecker law reads
`heckeForm(1) = N·towerForm_p(1) + M·towerForm_q(1)`. -/
theorem heckeForm_box_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (M N : ℕ) :
    heckeForm p q M N (fun _ => 1)
      = N * towerForm p M (fun _ => 1) + M * towerForm q N (fun _ => 1) := by
  rw [heckeForm_box_eq hp hq hpq]
  simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Successor orthogonality.** Consecutive Hecke cycles `Γ_k, Γ_{k+1}` (`k ≥ 2`) have no prime
intersection: neither divides the other. The successor structure of `ℕ` reaches the surface only
through the archimedean collar at the lag `log(1 + 1/k)`. -/
theorem heckeIncidence_succ {k : ℕ} (hk : 2 ≤ k) : heckeIncidence k (k + 1) = 0 := by
  have h1 : ¬ k ∣ k + 1 := by
    intro h
    have := (Nat.dvd_add_right (dvd_refl k)).mp h
    have := Nat.le_of_dvd one_pos this
    omega
  have h2 : ¬ k + 1 ∣ k := fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega
  simp [heckeIncidence, ratioIncidence, h1, h2]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
