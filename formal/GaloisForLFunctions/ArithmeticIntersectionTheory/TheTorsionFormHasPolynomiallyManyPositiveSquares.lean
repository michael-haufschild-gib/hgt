import GaloisForLFunctions.ArithmeticIntersectionTheory.TheHeckeCocycleOfRenormalization
import GaloisForLFunctions.RHTower.Sieve.PrimeWindow

/-!
# The torsion form has polynomially many positive squares

The renormalized torsion form `R(x) = −Σ x_m x_n P(m, n) − Σ x_n² c(n)` (`renormalizedTorsionForm`)
has at most two positive squares on each `p`-ladder: the self-intersection beats the tower above the
second level (`TheSelfIntersectionDominatesTheTower`). On the box `[1, N]` the ladders of different
primes share their bases, and the index grows like a power of `N`.

* **Anti-poles at a prime base.** For a prime `q` and the primes `p` of a window `A` above it, the
  vector `v_q = δ_q − Σ_{p ∈ A} δ_{qp}/(2√p)` pairs its base against the first rung of every
  `p`-ladder through `q`:
  `R(v_q) = Σ_{p ∈ A} log p/p − c(q) − Σ_{p ∈ A} c(qp)/(4p) ≥ ½ Σ_{p ∈ A} log p/p − log q`
  (`renormalizedTorsionForm_armVector`, using `c(n) ≤ log n` and `log(qp) ≤ 2 log p`).
* **Disjoint windows decouple.** For bases in `(M, Q₀M]` and arms in `(Q₀M, N/(Q₀M)]` the vectors
  are `R`-orthogonal: two distinct anti-poles share no Hecke edge (`torsionBilinear_armVector_ne`).
* **The index** (`renormalizedTorsionForm_pos_on_span`): for `M ≥ 3` and `N ≥ (Q₀M)⁵`, `R` is positive
  definite on a subspace of `ℝ^{[1, N]}` of dimension at least `M/log M`, by Mertens' theorem for the
  arm window and Chebyshev's bound for the base window. So the positive index on `[1, N]` is at
  least `c N^{1/5}/log N`.

No finite-rank counterterm renormalizes the torsion pairing on all boxes: positive squares are
created where ladders of different primes meet, at their bases.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ArithmeticIntersectionTheory

open ArithmeticEffectivityTheory ArithmeticFunction RHTower.Sieve

/-! ### 1. The bilinear torsion form -/

/-- The symmetric bilinear form of `renormalizedTorsionForm`. -/
def torsionBilinear (S : Finset ℕ) (x y : ℕ → ℝ) : ℝ :=
  -(∑ m ∈ S, ∑ n ∈ S, x m * y n * weilPrimeKernel m n) - ∑ n ∈ S, x n * y n * selfIntersection n

theorem renormalizedTorsionForm_eq_bilinear (S : Finset ℕ) (x : ℕ → ℝ) :
    renormalizedTorsionForm S x = torsionBilinear S x x := by
  unfold renormalizedTorsionForm torsionBilinear
  congr 1
  exact sum_congr rfl fun n _ => by ring

theorem weilPrimeKernel_symm (m n : ℕ) : weilPrimeKernel m n = weilPrimeKernel n m := by
  unfold weilPrimeKernel
  by_cases h1 : m ∣ n ∧ m ≠ n
  · have h2 : ¬ (n ∣ m ∧ n ≠ m) := fun h => h1.2 (Nat.dvd_antisymm h1.1 h.1)
    rw [if_pos h1, if_neg h2, if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : n ∣ m ∧ n ≠ m
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, if_neg h1]

/-- Linearity in the first slot. -/
theorem torsionBilinear_sum_left (S C : Finset ℕ) (a : ℕ → ℝ) (e : ℕ → ℕ → ℝ) (y : ℕ → ℝ) :
    torsionBilinear S (fun n => ∑ q ∈ C, a q * e q n) y =
      ∑ q ∈ C, a q * torsionBilinear S (e q) y := by
  unfold torsionBilinear
  have h1 : ∑ m ∈ S, ∑ n ∈ S, (∑ q ∈ C, a q * e q m) * y n * weilPrimeKernel m n =
      ∑ q ∈ C, a q * ∑ m ∈ S, ∑ n ∈ S, e q m * y n * weilPrimeKernel m n := by
    have hl : ∑ m ∈ S, ∑ n ∈ S, (∑ q ∈ C, a q * e q m) * y n * weilPrimeKernel m n =
        ∑ m ∈ S, ∑ n ∈ S, ∑ q ∈ C, a q * (e q m * y n * weilPrimeKernel m n) :=
      sum_congr rfl fun m _ => sum_congr rfl fun n _ => by
        rw [sum_mul, sum_mul]; exact sum_congr rfl fun q _ => by ring
    have hr : ∑ q ∈ C, a q * ∑ m ∈ S, ∑ n ∈ S, e q m * y n * weilPrimeKernel m n =
        ∑ q ∈ C, ∑ m ∈ S, ∑ n ∈ S, a q * (e q m * y n * weilPrimeKernel m n) :=
      sum_congr rfl fun q _ => by rw [mul_sum]; exact sum_congr rfl fun m _ => by rw [mul_sum]
    rw [hl, hr]
    calc _ = ∑ m ∈ S, ∑ q ∈ C, ∑ n ∈ S, a q * (e q m * y n * weilPrimeKernel m n) :=
          sum_congr rfl fun m _ => sum_comm
      _ = _ := sum_comm
  have h2 : ∑ n ∈ S, (∑ q ∈ C, a q * e q n) * y n * selfIntersection n =
      ∑ q ∈ C, a q * ∑ n ∈ S, e q n * y n * selfIntersection n := by
    have hl : ∑ n ∈ S, (∑ q ∈ C, a q * e q n) * y n * selfIntersection n =
        ∑ n ∈ S, ∑ q ∈ C, a q * (e q n * y n * selfIntersection n) :=
      sum_congr rfl fun n _ => by
        rw [sum_mul, sum_mul]; exact sum_congr rfl fun q _ => by ring
    have hr : ∑ q ∈ C, a q * ∑ n ∈ S, e q n * y n * selfIntersection n =
        ∑ q ∈ C, ∑ n ∈ S, a q * (e q n * y n * selfIntersection n) :=
      sum_congr rfl fun q _ => by rw [mul_sum]
    rw [hl, hr, sum_comm]
  rw [h1, h2, ← sum_neg_distrib, ← sum_sub_distrib]
  exact sum_congr rfl fun q _ => by ring

theorem torsionBilinear_comm (S : Finset ℕ) (x y : ℕ → ℝ) :
    torsionBilinear S x y = torsionBilinear S y x := by
  unfold torsionBilinear
  congr 1
  · congr 1
    rw [sum_comm]
    exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by
      rw [weilPrimeKernel_symm]; ring
  · exact sum_congr rfl fun n _ => by ring

/-! ### 2. Anti-poles at a prime base -/

/-- The arm weight `1/(2√p)`. -/
def armWeight (p : ℕ) : ℝ := 1 / (2 * Real.sqrt p)

/-- The **anti-pole** at the base `q` with arms `A`: `v_q = δ_q − Σ_{p ∈ A} δ_{qp}/(2√p)`. -/
def armVector (A : Finset ℕ) (q n : ℕ) : ℝ :=
  (if n = q then 1 else 0) - ∑ p ∈ A, (if n = q * p then armWeight p else 0)

/-- Pairing an anti-pole with a function: `Σ_n v_q(n) F(n) = F(q) − Σ_p F(qp)/(2√p)`. -/
theorem sum_armVector_mul {S A : Finset ℕ} {q : ℕ} (hq : q ∈ S) (hqp : ∀ p ∈ A, q * p ∈ S)
    (F : ℕ → ℝ) :
    ∑ n ∈ S, armVector A q n * F n = F q - ∑ p ∈ A, armWeight p * F (q * p) := by
  unfold armVector
  simp only [sub_mul, sum_mul, ite_mul, one_mul, zero_mul]
  rw [sum_sub_distrib, sum_ite_eq' S q F, if_pos hq, sum_comm]
  congr 1
  refine sum_congr rfl fun p hp => ?_
  rw [sum_ite_eq' S (q * p) (fun n => armWeight p * F n), if_pos (hqp p hp)]

/-! ### 3. Divisibility across disjoint windows -/

theorem weilPrimeKernel_eq_zero_of_not_dvd {m n : ℕ} (h1 : ¬ m ∣ n) (h2 : ¬ n ∣ m) :
    weilPrimeKernel m n = 0 := by
  simp [weilPrimeKernel, h1, h2]

theorem weilPrimeKernel_self_eq (n : ℕ) : weilPrimeKernel n n = 0 := by
  simp [weilPrimeKernel]

theorem weilPrimeKernel_base_arm {q p : ℕ} (hq : 0 < q) (hp : p.Prime) :
    weilPrimeKernel q (q * p) = Real.log p / Real.sqrt p := by
  have hne : q ≠ q * p := by
    intro h
    have : q * 1 = q * p := by rw [mul_one]; exact h
    have := Nat.eq_of_mul_eq_mul_left hq this
    exact hp.one_lt.ne this
  rw [weilPrimeKernel, if_pos ⟨dvd_mul_right q p, hne⟩, Nat.mul_div_cancel_left p hq,
    vonMangoldt_apply_prime hp]

/-- The window hypotheses: bases are primes `≤ B`, arms are primes `> B`. -/
structure Windows (C A : Finset ℕ) (B : ℕ) : Prop where
  base_prime : ∀ q ∈ C, q.Prime
  base_le : ∀ q ∈ C, q ≤ B
  arm_prime : ∀ p ∈ A, p.Prime
  arm_gt : ∀ p ∈ A, B < p

variable {C A : Finset ℕ} {B : ℕ}

theorem Windows.not_dvd_base_arm (hW : Windows C A B) {q q' p' : ℕ} (hq : q ∈ C) (hq' : q' ∈ C)
    (hp' : p' ∈ A) (hne : q ≠ q') : ¬ q ∣ q' * p' := by
  intro h
  rcases (hW.base_prime q hq).dvd_mul.mp h with h1 | h1
  · exact hne ((Nat.prime_dvd_prime_iff_eq (hW.base_prime q hq) (hW.base_prime q' hq')).mp h1)
  · have := (Nat.prime_dvd_prime_iff_eq (hW.base_prime q hq) (hW.arm_prime p' hp')).mp h1
    have := hW.base_le q hq; have := hW.arm_gt p' hp'; omega

theorem Windows.not_arm_dvd_base (hW : Windows C A B) {q q' p' : ℕ} (hq : q ∈ C) (hq' : q' ∈ C)
    (hp' : p' ∈ A) : ¬ q' * p' ∣ q := by
  intro h
  have hq0 := (hW.base_prime q hq).pos
  have hle := Nat.le_of_dvd hq0 h
  have h1 := (hW.base_prime q' hq').two_le
  have := hW.base_le q hq; have := hW.arm_gt p' hp'
  nlinarith

theorem Windows.not_arm_dvd_arm (hW : Windows C A B) {q q' p p' : ℕ} (hq : q ∈ C) (hq' : q' ∈ C)
    (hp : p ∈ A) (hp' : p' ∈ A) (hne : q ≠ q' ∨ p ≠ p') : ¬ q * p ∣ q' * p' := by
  intro h
  have hqq : q = q' := by
    by_contra hqq
    exact hW.not_dvd_base_arm hq hq' hp' hqq (dvd_trans (dvd_mul_right q p) h)
  subst hqq
  have hpp : p ∣ p' := (Nat.mul_dvd_mul_iff_left (hW.base_prime q hq).pos).mp h
  have := (Nat.prime_dvd_prime_iff_eq (hW.arm_prime p hp) (hW.arm_prime p' hp')).mp hpp
  rcases hne with h' | h'
  · exact h' rfl
  · exact h' this

theorem Windows.base_ne_arm (hW : Windows C A B) {q q' p' : ℕ} (hq : q ∈ C) (hq' : q' ∈ C)
    (hp' : p' ∈ A) : q ≠ q' * p' := by
  intro h
  exact hW.not_arm_dvd_base hq hq' hp' (h ▸ dvd_refl _)

/-- **Distinct anti-poles share no Hecke edge.** -/
theorem torsionBilinear_armVector_ne (hW : Windows C A B) {S : Finset ℕ} {q q' : ℕ} (hq : q ∈ C)
    (hq' : q' ∈ C) (hne : q ≠ q') (hS : ∀ q ∈ C, q ∈ S ∧ ∀ p ∈ A, q * p ∈ S) :
    torsionBilinear S (armVector A q) (armVector A q') = 0 := by
  unfold torsionBilinear
  -- the prime kernel between the two supports vanishes
  have hP : ∑ m ∈ S, ∑ n ∈ S, armVector A q m * armVector A q' n * weilPrimeKernel m n = 0 := by
    have hrow : ∀ m, ∑ n ∈ S, armVector A q m * armVector A q' n * weilPrimeKernel m n =
        armVector A q m * (weilPrimeKernel m q' -
          ∑ p' ∈ A, armWeight p' * weilPrimeKernel m (q' * p')) := by
      intro m
      rw [← sum_armVector_mul (hS q' hq').1 (hS q' hq').2, mul_sum]
      exact sum_congr rfl fun n _ => by ring
    rw [sum_congr rfl fun m _ => hrow m, sum_armVector_mul (hS q hq).1 (hS q hq).2]
    have hqq' : weilPrimeKernel q q' = 0 := weilPrimeKernel_eq_zero_of_not_dvd
      (fun h => hne ((Nat.prime_dvd_prime_iff_eq (hW.base_prime q hq) (hW.base_prime q' hq')).mp h))
      (fun h => hne ((Nat.prime_dvd_prime_iff_eq (hW.base_prime q' hq')
        (hW.base_prime q hq)).mp h).symm)
    have hqa : ∀ p' ∈ A, weilPrimeKernel q (q' * p') = 0 := fun p' hp' =>
      weilPrimeKernel_eq_zero_of_not_dvd (hW.not_dvd_base_arm hq hq' hp' hne)
        (hW.not_arm_dvd_base hq hq' hp')
    have haq : ∀ p ∈ A, weilPrimeKernel (q * p) q' = 0 := fun p hp =>
      weilPrimeKernel_eq_zero_of_not_dvd (hW.not_arm_dvd_base hq' hq hp)
        (hW.not_dvd_base_arm hq' hq hp (Ne.symm hne))
    have haa : ∀ p ∈ A, ∀ p' ∈ A, weilPrimeKernel (q * p) (q' * p') = 0 := fun p hp p' hp' =>
      weilPrimeKernel_eq_zero_of_not_dvd (hW.not_arm_dvd_arm hq hq' hp hp' (Or.inl hne))
        (hW.not_arm_dvd_arm hq' hq hp' hp (Or.inl (Ne.symm hne)))
    rw [hqq', sum_congr rfl fun p' hp' => by rw [hqa p' hp', mul_zero]]
    simp only [sum_const_zero, sub_zero, zero_sub]
    rw [sum_congr rfl fun p hp => by
      rw [haq p hp, sum_congr rfl fun p' hp' => by rw [haa p hp p' hp', mul_zero]]]
    simp
  -- the diagonal parts have disjoint supports
  have hD : ∑ n ∈ S, armVector A q n * armVector A q' n * selfIntersection n = 0 := by
    have : ∑ n ∈ S, armVector A q n * armVector A q' n * selfIntersection n =
        ∑ n ∈ S, armVector A q n * (armVector A q' n * selfIntersection n) :=
      sum_congr rfl fun n _ => by ring
    rw [this, sum_armVector_mul (hS q hq).1 (hS q hq).2]
    have h1 : armVector A q' q = 0 := by
      unfold armVector
      rw [if_neg hne, sum_eq_zero fun p' hp' => if_neg (hW.base_ne_arm hq hq' hp')]
      ring
    have h2 : ∀ p ∈ A, armVector A q' (q * p) = 0 := by
      intro p hp
      unfold armVector
      rw [if_neg (fun h => hW.base_ne_arm hq' hq hp h.symm),
        sum_eq_zero fun p' hp' => if_neg (fun h => hW.not_arm_dvd_arm hq hq' hp hp'
          (Or.inl hne) (dvd_of_eq h))]
      ring
    rw [h1, zero_mul, sum_congr rfl fun p hp => by rw [h2 p hp, zero_mul, mul_zero]]
    simp
  rw [hP, hD]; ring

/-- `c(n) ≤ log n`. -/
theorem selfIntersection_le_log {n : ℕ} (hn : 0 < n) : selfIntersection n ≤ Real.log n := by
  rw [selfIntersection_eq hn]
  have : 0 ≤ tameDifferent n := sum_nonneg fun p hp => by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    exact div_nonneg (Real.log_nonneg hp1.le) (by linarith)
  linarith

/-- **The anti-pole is positive**: `R(v_q) ≥ ½ Σ_{p ∈ A} log p/p − log q`. -/
theorem torsionBilinear_armVector_self_ge (hW : Windows C A B) {S : Finset ℕ} {q : ℕ} (hq : q ∈ C)
    (hS : ∀ q ∈ C, q ∈ S ∧ ∀ p ∈ A, q * p ∈ S) :
    (1 / 2) * ∑ p ∈ A, Real.log p / p - Real.log q ≤
      torsionBilinear S (armVector A q) (armVector A q) := by
  have hqP := hW.base_prime q hq
  have hq0 := hqP.pos
  unfold torsionBilinear
  -- the prime part: `−2 Σ_p (1/(2√p)) (log p/√p) = −Σ log p/p`
  have hrow : ∀ m, ∑ n ∈ S, armVector A q m * armVector A q n * weilPrimeKernel m n =
      armVector A q m * (weilPrimeKernel m q -
        ∑ p ∈ A, armWeight p * weilPrimeKernel m (q * p)) := by
    intro m
    rw [← sum_armVector_mul (hS q hq).1 (hS q hq).2, mul_sum]
    exact sum_congr rfl fun n _ => by ring
  have hP : ∑ m ∈ S, ∑ n ∈ S, armVector A q m * armVector A q n * weilPrimeKernel m n =
      -∑ p ∈ A, Real.log p / p := by
    rw [sum_congr rfl fun m _ => hrow m, sum_armVector_mul (hS q hq).1 (hS q hq).2]
    have hba : ∀ p ∈ A, weilPrimeKernel q (q * p) = Real.log p / Real.sqrt p := fun p hp =>
      weilPrimeKernel_base_arm hq0 (hW.arm_prime p hp)
    have hab : ∀ p ∈ A, weilPrimeKernel (q * p) q = Real.log p / Real.sqrt p := fun p hp => by
      rw [weilPrimeKernel_symm]; exact hba p hp
    have haa : ∀ p ∈ A, ∀ p' ∈ A, weilPrimeKernel (q * p) (q * p') = 0 := by
      intro p hp p' hp'
      by_cases hpp : p = p'
      · subst hpp; exact weilPrimeKernel_self_eq _
      · exact weilPrimeKernel_eq_zero_of_not_dvd (hW.not_arm_dvd_arm hq hq hp hp' (Or.inr hpp))
          (hW.not_arm_dvd_arm hq hq hp' hp (Or.inr (Ne.symm hpp)))
    have hs1 : ∑ p ∈ A, armWeight p * weilPrimeKernel q (q * p) =
        ∑ p ∈ A, Real.log p / p / 2 := sum_congr rfl fun p hp => by
      rw [hba p hp]
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (hW.arm_prime p hp).pos
      have hs : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
      unfold armWeight
      rw [div_mul_div_comm, one_mul, mul_assoc, hs]
      ring
    have hs2 : ∑ p ∈ A, armWeight p * (weilPrimeKernel (q * p) q -
        ∑ p' ∈ A, armWeight p' * weilPrimeKernel (q * p) (q * p')) =
        ∑ p ∈ A, Real.log p / p / 2 := sum_congr rfl fun p hp => by
      rw [hab p hp, sum_eq_zero fun p' hp' => by rw [haa p hp p' hp', mul_zero], sub_zero]
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (hW.arm_prime p hp).pos
      have hs : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
      unfold armWeight
      rw [div_mul_div_comm, one_mul, mul_assoc, hs]
      ring
    rw [weilPrimeKernel_self_eq, hs1, hs2, ← sum_div]
    ring
  -- the diagonal part: `c(q) + Σ_p c(qp)/(4p)`
  have hdiag : ∑ n ∈ S, armVector A q n * armVector A q n * selfIntersection n =
      selfIntersection q + ∑ p ∈ A, armWeight p ^ 2 * selfIntersection (q * p) := by
    have : ∑ n ∈ S, armVector A q n * armVector A q n * selfIntersection n =
        ∑ n ∈ S, armVector A q n * (armVector A q n * selfIntersection n) :=
      sum_congr rfl fun n _ => by ring
    rw [this, sum_armVector_mul (hS q hq).1 (hS q hq).2]
    have h1 : armVector A q q = 1 := by
      unfold armVector
      rw [if_pos rfl, sum_eq_zero fun p hp => if_neg (hW.base_ne_arm hq hq hp)]
      ring
    have h2 : ∀ p ∈ A, armVector A q (q * p) = -armWeight p := by
      intro p hp
      unfold armVector
      rw [if_neg (fun h => hW.base_ne_arm hq hq hp h.symm)]
      rw [sum_eq_single p (fun p' hp' hne => if_neg (fun h => hW.not_arm_dvd_arm hq hq hp hp'
          (Or.inr (Ne.symm hne)) (dvd_of_eq h))) (fun h => absurd hp h), if_pos rfl]
      ring
    rw [h1, one_mul, sum_congr rfl fun p hp => by rw [h2 p hp]]
    rw [sub_eq_add_neg, ← sum_neg_distrib]
    congr 1
    exact sum_congr rfl fun p _ => by ring
  rw [hP, hdiag]
  -- bounds: `c(q) ≤ log q`, `c(qp) ≤ log(qp) ≤ 2 log p`
  have hcq := selfIntersection_le_log hq0
  have harm : ∑ p ∈ A, armWeight p ^ 2 * selfIntersection (q * p) ≤
      ∑ p ∈ A, (1 / 2) * (Real.log p / p) := by
    refine sum_le_sum fun p hp => ?_
    have hpP := hW.arm_prime p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpP.pos
    have hqp : 0 < q * p := Nat.mul_pos hq0 hpP.pos
    have hc := selfIntersection_le_log hqp
    have hqlt : (q : ℝ) ≤ p := by
      have := hW.base_le q hq; have := hW.arm_gt p hp
      exact_mod_cast (show q ≤ p by omega)
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq0
    have hlog : Real.log ((q * p : ℕ) : ℝ) ≤ 2 * Real.log p := by
      rw [Nat.cast_mul, Real.log_mul (by positivity) hp0.ne']
      have := Real.log_le_log (by positivity) hqlt
      linarith
    have hw : armWeight p ^ 2 = 1 / (4 * p) := by
      unfold armWeight
      rw [div_pow, mul_pow, Real.sq_sqrt hp0.le]; ring
    rw [hw]
    have hc0 : selfIntersection (q * p) ≤ 2 * Real.log p := hc.trans hlog
    calc 1 / (4 * (p : ℝ)) * selfIntersection (q * p) ≤ 1 / (4 * (p : ℝ)) * (2 * Real.log p) :=
          mul_le_mul_of_nonneg_left hc0 (by positivity)
      _ = 1 / 2 * (Real.log p / p) := by field_simp; ring
  rw [← mul_sum] at harm
  linarith

/-! ### 4. The index on a box -/

/-- The window ratio `Q₀ = ⌈e^{2c₁ + 1}⌉`, `c₁` the constant of Mertens' first theorem. -/
def windowRatio : ℕ := ⌈Real.exp (2 * mertensFirstConst + 1)⌉₊

theorem log_windowRatio_ge : 2 * mertensFirstConst + 1 ≤ Real.log windowRatio := by
  have h : Real.exp (2 * mertensFirstConst + 1) ≤ windowRatio := Nat.le_ceil _
  calc 2 * mertensFirstConst + 1 = Real.log (Real.exp (2 * mertensFirstConst + 1)) :=
        (Real.log_exp _).symm
    _ ≤ Real.log windowRatio := Real.log_le_log (Real.exp_pos _) h

theorem one_le_windowRatio : 1 ≤ windowRatio :=
  Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (Real.exp_pos _)).ne'

/-- **The renormalized torsion form has at least `M/log M` positive squares on `[1, N]`** as soon
as `N ≥ (Q₀M)⁵`: it is positive definite on the span of the anti-poles at the primes of
`(M, Q₀M]` with arms at the primes of `(Q₀M, N/(Q₀M)]`. -/
theorem renormalizedTorsionForm_pos_on_span {M N : ℕ} (hM : 3 ≤ M)
    (hN : (windowRatio * M) ^ 5 ≤ N) :
    ∃ (C A : Finset ℕ), (M : ℝ) / Real.log M ≤ C.card ∧
      (∀ q ∈ C, ∀ n, armVector A q n ≠ 0 → n ∈ Icc 1 N) ∧
      ∀ a : ℕ → ℝ, (∃ q ∈ C, a q ≠ 0) →
        0 < renormalizedTorsionForm (Icc 1 N) (fun n => ∑ q ∈ C, a q * armVector A q n) := by
  set Q := windowRatio
  set B := Q * M
  have hQ1 := one_le_windowRatio
  have hB3 : 3 ≤ B := le_trans hM (Nat.le_mul_of_pos_left M (by omega))
  set A := bigPrimeSet B (N / B)
  have hBN : B ≤ N / B := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    calc B * B ≤ B ^ 5 := by nlinarith [pow_le_pow_right₀ (by omega : 1 ≤ B) (show 2 ≤ 5 by norm_num)]
      _ ≤ N := hN
  have hW : Windows (bigPrimeSet M B) A B := by
    refine ⟨fun q hq => (mem_filter.mp hq).2, fun q hq => (mem_Icc.mp (mem_filter.mp hq).1).2,
      fun p hp => (mem_filter.mp hp).2, fun p hp => ?_⟩
    have := (mem_Icc.mp (mem_filter.mp hp).1).1; omega
  have hS : ∀ q ∈ bigPrimeSet M B, q ∈ Icc 1 N ∧ ∀ p ∈ A, q * p ∈ Icc 1 N := by
    intro q hq
    have hq1 := (mem_Icc.mp (mem_filter.mp hq).1)
    have hqB := hq1.2
    have hBle : B ≤ N := le_trans hBN (Nat.div_le_self N B)
    refine ⟨mem_Icc.mpr ⟨by omega, by omega⟩, fun p hp => ?_⟩
    have hp1 := (mem_Icc.mp (mem_filter.mp hp).1)
    refine mem_Icc.mpr ⟨Nat.mul_pos (by omega) (by omega), ?_⟩
    calc q * p ≤ B * (N / B) := Nat.mul_le_mul hqB hp1.2
      _ ≤ N := Nat.mul_div_le N B
  -- each anti-pole is positive: Mertens on the arm window `(B, N/B]`
  have hpos : ∀ q ∈ bigPrimeSet M B, 0 < torsionBilinear (Icc 1 N) (armVector A q) (armVector A q) := by
    intro q hq
    have hself := torsionBilinear_armVector_self_ge hW hq hS
    have hq1 := (mem_Icc.mp (mem_filter.mp hq).1)
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    have hlogq : Real.log q ≤ Real.log B := Real.log_le_log hqpos (by exact_mod_cast hq1.2)
    have hwin := sum_logDiv_bigPrimeSet B (N / B) hBN
    have hNB1 : 1 ≤ N / B := le_trans (by omega) hBN
    have hupB := (abs_le.mp (abs_mertensA_sub_log_le (show 1 ≤ B by omega))).2
    have hlowNB := (abs_le.mp (abs_mertensA_sub_log_le hNB1)).1
    -- `N/B ≥ B⁴`, so `log(N/B) ≥ 4 log B`
    have hB4 : B ^ 4 ≤ N / B := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      calc B ^ 4 * B = B ^ 5 := by ring
        _ ≤ N := hN
    have hlog4 : 4 * Real.log B ≤ Real.log ((N / B : ℕ) : ℝ) := by
      have := Real.log_le_log (by positivity) (show ((B ^ 4 : ℕ) : ℝ) ≤ ((N / B : ℕ) : ℝ) by
        exact_mod_cast hB4)
      rw [Nat.cast_pow, Real.log_pow] at this; push_cast at this; linarith
    -- `log B ≥ log Q₀ ≥ 2c₁ + 1`
    have hlogB : 2 * mertensFirstConst + 1 ≤ Real.log B := by
      have hQB : (Q : ℝ) ≤ B := by exact_mod_cast Nat.le_mul_of_pos_right Q (by omega)
      exact log_windowRatio_ge.trans (Real.log_le_log (by exact_mod_cast hQ1) hQB)
    have hc1 := mertensFirstConst_nonneg
    rw [hwin] at hself
    linarith
  refine ⟨bigPrimeSet M B, A, ?_, ?_, ?_⟩
  · -- Chebyshev for the base window
    have h := card_bigPrimeSet_ratio_ge hM hQ1
    have hlogM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
    have hQ := log_windowRatio_ge
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    calc (M : ℝ) / Real.log M ≤ (Real.log Q - 2 * mertensFirstConst) * (M : ℝ) / Real.log M := by
          rw [div_le_div_iff_of_pos_right hlogM]; nlinarith
      _ ≤ _ := h
  · -- the anti-poles live in `[1, N]`
    intro q hq n hn
    have hqC := hS q hq
    by_contra hnS
    apply hn
    unfold armVector
    rw [if_neg (fun (h : n = q) => hnS (by rw [h]; exact hqC.1)),
      sum_eq_zero fun p hp => if_neg (fun (h : n = q * p) => hnS (by rw [h]; exact hqC.2 p hp))]
    ring
  · intro a ha
    rw [renormalizedTorsionForm_eq_bilinear, torsionBilinear_sum_left]
    -- the anti-poles are orthogonal, so the form is diagonal on their span
    have hdiag : ∀ q ∈ bigPrimeSet M B, torsionBilinear (Icc 1 N) (armVector A q)
        (fun n => ∑ q' ∈ bigPrimeSet M B, a q' * armVector A q' n) =
        a q * torsionBilinear (Icc 1 N) (armVector A q) (armVector A q) := by
      intro q hq
      rw [torsionBilinear_comm, torsionBilinear_sum_left,
        sum_eq_single q (fun q' hq' hne => by
          rw [torsionBilinear_comm, torsionBilinear_armVector_ne hW hq hq' (Ne.symm hne) hS,
            mul_zero]) (fun h => absurd hq h), torsionBilinear_comm]
    rw [sum_congr rfl fun q hq => by rw [hdiag q hq]]
    obtain ⟨q₀, hq₀, ha₀⟩ := ha
    refine sum_pos' (fun q hq => ?_) ⟨q₀, hq₀, ?_⟩
    · have := hpos q hq
      nlinarith [sq_nonneg (a q)]
    · have := hpos q₀ hq₀
      have : 0 < a q₀ ^ 2 := by positivity
      nlinarith

end GaloisForLFunctions.ArithmeticIntersectionTheory
