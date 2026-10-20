import GaloisForLFunctions.RHTower.WeilMarkovPrimitiveHyperplane

/-!
# Prime-power incidence: the ratio atom dominates the product atom

In an odd gauge the zero form is a jump form whose prime conductance between two points `x, y`
is `M(x) M(y) Λ(n) n^{-1/2}` when `|x − y| = log n`. On the logarithmic lattice `{± log a : a ≥ 1}`
with an even profile, the same unordered pair of integers `{a, b}` is coupled twice:

* **same side**, `(log a, log b)` with `b = a m`: the *ratio atom* `Λ(m)/√m`, conductance factor
  `M(log a) M(log b) > 0`;
* **across the origin**, `(−log a, log b)` with `ab = n`: the *product atom* `Λ(n)/√n`, conductance
  factor `M(−log a) M(log b) = −M(log a) M(log b) < 0`.

Both couplings carry the same gauge factor `|M(log a) M(log b)|` and the same profile difference
`(u(log a) − u(log b))²`. The net prime conductance of the pair is therefore
`|M(log a) M(log b)| (ratioAtom a b − productAtom a b)`.

**Dominance law.** If `ab` is a prime power then `a` and `b` are powers of the same prime, the ratio
`b/a` is a prime power too, `Λ(ab) = Λ(b/a) = log p`, and `√(ab) ≥ √(b/a)`. Hence for `1 ≤ a < b`

    productAtom a b ≤ ratioAtom a b,

with equality exactly when `a = 1` (then the two atoms coincide) or when neither atom is present.
The negative prime atoms of the jump form never win on a lattice pair: the prime obstruction to
positivity lives strictly between lattice points, not on them. Profiles constant along each
prime-power tower `{p^i}` see no product atom at all.
-/

open ArithmeticFunction RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-- Same-side prime atom of the lattice pair `(log a, log b)`: `Λ(b/a)/√(b/a)` when `a ∣ b`,
and `0` when the pair is not a dilation pair. -/
def ratioAtom (a b : ℕ) : ℝ := if a ∣ b then vonMangoldtAtom (b / a) else 0

/-- Crossing prime atom of the lattice pair `(−log a, log b)`: `Λ(ab)/√(ab)`. -/
def productAtom (a b : ℕ) : ℝ := vonMangoldtAtom (a * b)

/-- Net prime conductance of the unordered lattice pair `{a, b}` per unit `|M(log a) M(log b)|`. -/
def netAtom (a b : ℕ) : ℝ := ratioAtom a b - productAtom a b

theorem ratioAtom_nonneg (a b : ℕ) : 0 ≤ ratioAtom a b := by
  unfold ratioAtom
  split_ifs
  · exact vonMangoldtAtom_nonneg _
  · exact le_rfl

theorem productAtom_nonneg (a b : ℕ) : 0 ≤ productAtom a b := vonMangoldtAtom_nonneg _

theorem productAtom_comm (a b : ℕ) : productAtom a b = productAtom b a := by
  unfold productAtom; rw [mul_comm]

/-- The product atom vanishes unless `ab` is a prime power. -/
theorem productAtom_eq_zero_of_not_isPrimePow {a b : ℕ} (h : ¬ IsPrimePow (a * b)) :
    productAtom a b = 0 := by
  unfold productAtom vonMangoldtAtom
  split_ifs
  · rw [vonMangoldt_eq_zero_iff.mpr h, zero_div]
  · rfl

/-- **Tower lemma.** If `ab` is a prime power then `a` and `b` are powers of one prime. -/
theorem exists_prime_pow_of_isPrimePow_mul {a b : ℕ} (h : IsPrimePow (a * b)) :
    ∃ p i j : ℕ, p.Prime ∧ a = p ^ i ∧ b = p ^ j ∧ 0 < i + j := by
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff _).mp h
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro b hpk)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro_left a hpk)
  refine ⟨p, i, j, hp, hi, hj, ?_⟩
  by_contra hij
  have hi0 : i = 0 := by omega
  have hj0 : j = 0 := by omega
  subst hi0 hj0
  simp only [pow_zero, mul_one] at hpk
  have : p ^ k = 1 := hpk.symm ▸ rfl
  exact (pow_eq_one_iff hk.ne').mp this ▸ hp |>.one_lt.ne' rfl

/-- `Λ(p^i p^j) = log p` for a prime `p` and `0 < i + j`. -/
theorem vonMangoldt_pow_mul_pow {p i j : ℕ} (hp : p.Prime) (hij : 0 < i + j) :
    vonMangoldt (p ^ i * p ^ j) = Real.log p := by
  rw [← pow_add, vonMangoldt_apply_pow hij.ne', vonMangoldt_apply_prime hp]

/-- On a prime-power tower the product atom is `log p / √(p^{i+j})`. -/
theorem productAtom_pow_pow {p i j : ℕ} (hp : p.Prime) (hij : 0 < i + j) :
    productAtom (p ^ i) (p ^ j) = Real.log p / Real.sqrt ((p : ℝ) ^ (i + j)) := by
  unfold productAtom vonMangoldtAtom
  have h2 : 2 ≤ p ^ i * p ^ j := by
    rw [← pow_add]
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (i + j) := Nat.pow_le_pow_right hp.pos hij
  rw [if_pos h2, vonMangoldt_pow_mul_pow hp hij]
  push_cast
  rw [← pow_add]

/-- On a prime-power tower with `i < j` the ratio atom is `log p / √(p^{j−i})`. -/
theorem ratioAtom_pow_pow {p i j : ℕ} (hp : p.Prime) (hij : i < j) :
    ratioAtom (p ^ i) (p ^ j) = Real.log p / Real.sqrt ((p : ℝ) ^ (j - i)) := by
  unfold ratioAtom vonMangoldtAtom
  have hdvd : p ^ i ∣ p ^ j := Nat.pow_dvd_pow p hij.le
  have hdiv : p ^ j / p ^ i = p ^ (j - i) := by
    rw [Nat.pow_div hij.le hp.pos]
  have h2 : 2 ≤ p ^ (j - i) := by
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (j - i) := Nat.pow_le_pow_right hp.pos (by omega)
  rw [if_pos hdvd, hdiv, if_pos h2, vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
  push_cast
  rfl

/-- **Dominance law.** For `1 ≤ a < b` the crossing atom never exceeds the same-side atom. -/
theorem productAtom_le_ratioAtom {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    productAtom a b ≤ ratioAtom a b := by
  by_cases h : IsPrimePow (a * b)
  · obtain ⟨p, i, j, hp, rfl, rfl, hij⟩ := exists_prime_pow_of_isPrimePow_mul h
    have hlt : i < j := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hab
    rw [productAtom_pow_pow hp hij, ratioAtom_pow_pow hp hlt]
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hpow : (p : ℝ) ^ (j - i) ≤ (p : ℝ) ^ (i + j) :=
      pow_le_pow_right₀ hp1 (by omega)
    have hpos : 0 < Real.sqrt ((p : ℝ) ^ (j - i)) :=
      Real.sqrt_pos.mpr (pow_pos (by linarith) _)
    exact div_le_div_of_nonneg_left hlogp hpos (Real.sqrt_le_sqrt hpow)
  · rw [productAtom_eq_zero_of_not_isPrimePow h]
    exact ratioAtom_nonneg a b

/-- **Strict dominance.** For `2 ≤ a < b` with `ab` a prime power the same-side atom is strictly
larger: the gauge factor cancels and `√(ab) > √(b/a)` since `a > 1`. -/
theorem productAtom_lt_ratioAtom {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) (h : IsPrimePow (a * b)) :
    productAtom a b < ratioAtom a b := by
  obtain ⟨p, i, j, hp, rfl, rfl, hij⟩ := exists_prime_pow_of_isPrimePow_mul h
  have hlt : i < j := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hab
  have hi : 0 < i := by
    by_contra hi0
    have : i = 0 := by omega
    subst this
    simp at ha
  rw [productAtom_pow_pow hp hij, ratioAtom_pow_pow hp hlt]
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpow : (p : ℝ) ^ (j - i) < (p : ℝ) ^ (i + j) :=
    pow_lt_pow_right₀ hp1 (by omega)
  have hpos : 0 < Real.sqrt ((p : ℝ) ^ (j - i)) :=
    Real.sqrt_pos.mpr (pow_pos (by linarith) _)
  exact div_lt_div_of_pos_left hlogp hpos (Real.sqrt_lt_sqrt (by positivity) hpow)

/-- At `a = 1` the two atoms coincide: the pair `{1, b}` is prime-neutral. -/
theorem productAtom_one_left (b : ℕ) : productAtom 1 b = ratioAtom 1 b := by
  unfold productAtom ratioAtom
  simp

theorem netAtom_nonneg {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) : 0 ≤ netAtom a b :=
  sub_nonneg.mpr (productAtom_le_ratioAtom ha hab)

theorem netAtom_pos {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) (h : IsPrimePow (a * b)) :
    0 < netAtom a b :=
  sub_pos.mpr (productAtom_lt_ratioAtom ha hab h)

theorem netAtom_one_left (b : ℕ) : netAtom 1 b = 0 := by
  unfold netAtom; rw [productAtom_one_left, sub_self]

/-! ### The lattice skeleton as a nonnegative graph Laplacian -/

/-- The product (crossing) energy of a lattice profile `c` on a finite support `S`:
`Σ_{a<b} Λ(ab)/√(ab) (c a − c b)²`, the part of the jump form with negative gauge factor. -/
def productEnergy (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ a ∈ S, ∑ b ∈ S, if a < b then productAtom a b * (c a - c b) ^ 2 else 0

/-- The ratio (same-side) energy `Σ_{a<b} Λ(b/a)/√(b/a) (c a − c b)²`. -/
def ratioEnergy (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ a ∈ S, ∑ b ∈ S, if a < b then ratioAtom a b * (c a - c b) ^ 2 else 0

/-- The net prime skeleton energy `Σ_{a<b} (ratioAtom − productAtom)(c a − c b)²`. -/
def skeletonEnergy (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ a ∈ S, ∑ b ∈ S, if a < b then netAtom a b * (c a - c b) ^ 2 else 0

theorem skeletonEnergy_eq_sub (S : Finset ℕ) (c : ℕ → ℝ) :
    skeletonEnergy S c = ratioEnergy S c - productEnergy S c := by
  unfold skeletonEnergy ratioEnergy productEnergy
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs
  · unfold netAtom; ring
  · ring

/-- **The prime skeleton is a nonnegative Laplacian.** On supports of positive integers the
crossing energy is paid pair by pair by the same-side energy. -/
theorem productEnergy_le_ratioEnergy {S : Finset ℕ} (hS : ∀ a ∈ S, 1 ≤ a) (c : ℕ → ℝ) :
    productEnergy S c ≤ ratioEnergy S c := by
  unfold productEnergy ratioEnergy
  refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b _ => ?_
  split_ifs with hab
  · exact mul_le_mul_of_nonneg_right (productAtom_le_ratioAtom (hS a ha) hab) (sq_nonneg _)
  · exact le_rfl

theorem skeletonEnergy_nonneg {S : Finset ℕ} (hS : ∀ a ∈ S, 1 ≤ a) (c : ℕ → ℝ) :
    0 ≤ skeletonEnergy S c := by
  rw [skeletonEnergy_eq_sub]
  exact sub_nonneg.mpr (productEnergy_le_ratioEnergy hS c)

/-- A profile constant along every prime-power tower has no crossing energy: every product atom
sits on a pair `{p^i, p^j}` inside one tower. -/
theorem productEnergy_eq_zero_of_tower_constant {S : Finset ℕ} (c : ℕ → ℝ)
    (hc : ∀ p i j : ℕ, p.Prime → c (p ^ i) = c (p ^ j)) :
    productEnergy S c = 0 := by
  unfold productEnergy
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  split_ifs with hab
  · by_cases h : IsPrimePow (a * b)
    · obtain ⟨p, i, j, hp, rfl, rfl, -⟩ := exists_prime_pow_of_isPrimePow_mul h
      rw [hc p i j hp, sub_self, sq, mul_zero, mul_zero]
    · rw [productAtom_eq_zero_of_not_isPrimePow h, zero_mul]
  · rfl

end GaloisForLFunctions.ArithmeticIncidencePositivity
