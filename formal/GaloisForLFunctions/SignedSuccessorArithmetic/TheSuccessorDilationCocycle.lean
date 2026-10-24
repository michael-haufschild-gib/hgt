import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.Order.Units
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Liouville

/-!
# The successor dilation cocycle

A completely multiplicative sign `f` on the positive integers is read along the successor through
its successor sign `σ_f(n) = f(n) f(n+1)`, which is `+1` when the sign is kept across the step
`n → n+1` and `-1` when it flips. Dilation by `m` carries the step `n → n+1` onto the block
`mn, mn+1, …, mn+m`, and telescoping the successor signs over that block gives the
**dilation cocycle**

  `∏_{j<m} σ_f(mn + j) = σ_f(n)`.

This is the interaction of `×` and `+1` in one identity. It characterizes complete
multiplicativity: a sign sequence is the successor sign of a completely multiplicative sign iff it
satisfies the cocycle at every prime dilation (`exists_cmSign_iff_primeCocycle`), and the sign is
recovered from its successor signs as `f(n) = ∏_{1 ≤ k < n} σ_f(k)` (`eq_signOfSucc_succSign`).
The prime values `f(p)` cancel out of the cocycle (`f(m)² = 1`), so the constraints are the same
for every completely multiplicative sign; the values are carried by the initial segments of `σ_f`.

Completely multiplicative signs form a group under pointwise product, generated freely by their
prime values (`CMSign.ofPrimes`), and the successor sign is a group homomorphism (`succSign_mul`).
-/

namespace GaloisForLFunctions.SignedSuccessorArithmetic

open Finset

/-- A completely multiplicative sign on the positive integers. The value at `0` plays no role. -/
structure CMSign where
  /-- The sign function. -/
  toFun : ℕ → ℤˣ
  map_one' : toFun 1 = 1
  map_mul' : ∀ {m n : ℕ}, 0 < m → 0 < n → toFun (m * n) = toFun m * toFun n

instance : CoeFun CMSign (fun _ => ℕ → ℤˣ) := ⟨CMSign.toFun⟩

namespace CMSign

@[simp] theorem map_one (f : CMSign) : f 1 = 1 := f.map_one'

theorem map_mul (f : CMSign) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) : f (m * n) = f m * f n :=
  f.map_mul' hm hn

/-- Pointwise product of completely multiplicative signs. -/
instance : Mul CMSign where
  mul f g :=
    { toFun := fun n => f n * g n
      map_one' := by simp
      map_mul' := fun hm hn => by
        simp only [f.map_mul hm hn, g.map_mul hm hn]
        exact mul_mul_mul_comm _ _ _ _ }

@[simp] theorem mul_apply (f g : CMSign) (n : ℕ) : (f * g) n = f n * g n := rfl

/-- The trivial sign. -/
instance : One CMSign := ⟨{ toFun := fun _ => 1, map_one' := rfl, map_mul' := fun _ _ => by simp }⟩

@[simp] theorem one_apply (n : ℕ) : (1 : CMSign) n = 1 := rfl

/-- The Liouville function `λ(n) = (-1)^{Ω(n)}` as a completely multiplicative sign. -/
def liouville : CMSign where
  toFun n := if h : n = 0 then 1 else
    ⟨ArithmeticFunction.liouville n, ArithmeticFunction.liouville n, by
      rw [ArithmeticFunction.liouville_apply h, ← pow_add, ← two_mul, pow_mul]; simp, by
      rw [ArithmeticFunction.liouville_apply h, ← pow_add, ← two_mul, pow_mul]; simp⟩
  map_one' := by
    ext; simp [ArithmeticFunction.liouville_apply_one]
  map_mul' := fun {m n} hm hn => by
    ext
    simp [hm.ne', hn.ne', ArithmeticFunction.liouville_apply_mul]

theorem liouville_val {n : ℕ} (hn : n ≠ 0) :
    ((liouville n : ℤˣ) : ℤ) = ArithmeticFunction.liouville n := by
  simp [liouville, hn]

/-- The completely multiplicative sign with prescribed values `ε p` at the primes:
`f(n) = ∏_p ε(p)^{v_p(n)}`. -/
def ofPrimes (ε : ℕ → ℤˣ) : CMSign where
  toFun n := n.factorization.prod fun p k => ε p ^ k
  map_one' := by simp
  map_mul' := fun {m n} hm hn => by
    rw [Nat.factorization_mul hm.ne' hn.ne', Finsupp.prod_add_index']
    · intro _; simp
    · intro _ _ _; exact pow_add _ _ _

theorem ofPrimes_prime (ε : ℕ → ℤˣ) {p : ℕ} (hp : p.Prime) : ofPrimes ε p = ε p := by
  change p.factorization.prod (fun q k => ε q ^ k) = ε p
  rw [hp.factorization, Finsupp.prod_single_index (by simp), pow_one]

/-- Two completely multiplicative signs agreeing at every prime agree on the positive integers. -/
theorem eq_of_prime (f g : CMSign) (h : ∀ p, p.Prime → f p = g p) {n : ℕ} (hn : 0 < n) :
    f n = g n := by
  induction n using induction_on_primes with
  | zero => exact absurd hn (lt_irrefl 0)
  | one => simp
  | prime_mul p a hp ih =>
    have ha : 0 < a := Nat.pos_of_mul_pos_left hn
    rw [f.map_mul hp.pos ha, g.map_mul hp.pos ha, h p hp, ih ha]

/-- Every completely multiplicative sign is determined by its prime values. -/
theorem eq_ofPrimes (f : CMSign) {n : ℕ} (hn : 0 < n) : f n = ofPrimes (fun p => f p) n :=
  eq_of_prime f _ (fun _ hp => (ofPrimes_prime _ hp).symm) hn

end CMSign

/-! ## Successor signs and telescoping -/

/-- The successor sign `σ_f(n) = f(n) f(n+1)`. -/
def succSign (f : ℕ → ℤˣ) (n : ℕ) : ℤˣ := f n * f (n + 1)

/-- The successor sign of a product is the product of the successor signs. -/
theorem succSign_mul (f g : CMSign) (n : ℕ) :
    succSign (f * g) n = succSign f n * succSign g n := by
  simp only [succSign]
  exact mul_mul_mul_comm _ _ _ _

/-- Telescoping: the successor signs along `a, a+1, …, a+m-1` multiply to `f(a) f(a+m)`. -/
theorem prod_succSign_range (f : ℕ → ℤˣ) (a m : ℕ) :
    ∏ j ∈ range m, succSign f (a + j) = f a * f (a + m) := by
  induction m with
  | zero => simp [Int.units_mul_self]
  | succ m ih =>
    rw [prod_range_succ, ih, succSign, ← add_assoc]
    calc f a * f (a + m) * (f (a + m) * f (a + m + 1))
        = f a * (f (a + m) * f (a + m)) * f (a + m + 1) := by simp only [mul_assoc]
      _ = f a * f (a + m + 1) := by rw [Int.units_mul_self, mul_one]

/-- **The dilation cocycle.** For a completely multiplicative sign, the successor signs on the
dilated block `mn, …, mn+m-1` multiply to the successor sign at `n`. -/
theorem dilation_cocycle (f : CMSign) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ∏ j ∈ range m, succSign f (m * n + j) = succSign f n := by
  rw [prod_succSign_range, show m * n + m = m * (n + 1) by ring, f.map_mul hm hn,
    f.map_mul hm n.succ_pos, mul_mul_mul_comm, Int.units_mul_self, one_mul, succSign]

/-- The dilation cocycle condition at one dilation factor `m`, on positive indices. -/
def IsDilationCocycleAt (σ : ℕ → ℤˣ) (m : ℕ) : Prop :=
  ∀ n, 0 < n → ∏ j ∈ range m, σ (m * n + j) = σ n

/-- The full dilation cocycle condition. -/
def IsDilationCocycle (σ : ℕ → ℤˣ) : Prop := ∀ m, 0 < m → IsDilationCocycleAt σ m

theorem isDilationCocycle_succSign (f : CMSign) : IsDilationCocycle (succSign f) :=
  fun _ hm _ hn => dilation_cocycle f hm hn

/-! ## Reconstruction of a sign from its successor signs -/

/-- The sign recovered from a successor-sign sequence: `∏_{1 ≤ k < n} σ(k)`. -/
def signOfSucc (σ : ℕ → ℤˣ) (n : ℕ) : ℤˣ := ∏ k ∈ Ico 1 n, σ k

@[simp] theorem signOfSucc_one (σ : ℕ → ℤˣ) : signOfSucc σ 1 = 1 := by simp [signOfSucc]

theorem signOfSucc_add (σ : ℕ → ℤˣ) {a : ℕ} (ha : 0 < a) (m : ℕ) :
    signOfSucc σ (a + m) = signOfSucc σ a * ∏ j ∈ range m, σ (a + j) := by
  rw [signOfSucc, signOfSucc, ← prod_Ico_consecutive σ ha (Nat.le_add_right a m)]
  congr 1
  rw [prod_Ico_eq_prod_range, Nat.add_sub_cancel_left]

theorem signOfSucc_succ (σ : ℕ → ℤˣ) {n : ℕ} (hn : 0 < n) :
    signOfSucc σ (n + 1) = signOfSucc σ n * σ n := by
  rw [signOfSucc_add σ hn 1, prod_range_one, add_zero]

/-- The reconstructed sign has successor signs `σ` on the positive integers. -/
theorem succSign_signOfSucc (σ : ℕ → ℤˣ) {n : ℕ} (hn : 0 < n) :
    succSign (signOfSucc σ) n = σ n := by
  rw [succSign, signOfSucc_succ σ hn, ← mul_assoc, Int.units_mul_self, one_mul]

/-- Every sign with `f(1) = 1` is the product of its successor signs below `n`. -/
theorem eq_signOfSucc_succSign (f : ℕ → ℤˣ) (h1 : f 1 = 1) {n : ℕ} (hn : 0 < n) :
    f n = signOfSucc (succSign f) n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 1 + m := ⟨n - 1, by omega⟩
  rw [signOfSucc_add _ Nat.one_pos, signOfSucc_one, one_mul, prod_succSign_range, h1, one_mul]

/-- A completely multiplicative sign is determined by its successor signs. -/
theorem CMSign.eq_of_succSign (f g : CMSign) (h : ∀ n, 0 < n → succSign f n = succSign g n)
    {n : ℕ} (hn : 0 < n) : f n = g n := by
  rw [eq_signOfSucc_succSign f f.map_one hn, eq_signOfSucc_succSign g g.map_one hn]
  exact prod_congr rfl fun k hk => h k (by simp at hk; omega)

/-- The cocycle at `m` makes the reconstructed sign multiplicative under dilation by `m`. -/
theorem signOfSucc_mul_of_cocycleAt {σ : ℕ → ℤˣ} {m : ℕ} (hm : 0 < m)
    (hσ : IsDilationCocycleAt σ m) {n : ℕ} (hn : 0 < n) :
    signOfSucc σ (m * n) = signOfSucc σ m * signOfSucc σ n := by
  induction n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · simp
    rw [show m * (n + 1) = m * n + m by ring, signOfSucc_add σ (Nat.mul_pos hm hn') m,
      hσ n hn', ih hn', signOfSucc_succ σ hn', mul_assoc]

/-- The cocycle at every prime makes the reconstructed sign completely multiplicative. -/
theorem signOfSucc_mul_of_primeCocycle {σ : ℕ → ℤˣ}
    (hσ : ∀ p, p.Prime → IsDilationCocycleAt σ p) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    signOfSucc σ (m * n) = signOfSucc σ m * signOfSucc σ n := by
  induction m using induction_on_primes generalizing n with
  | zero => exact absurd hm (lt_irrefl 0)
  | one => simp
  | prime_mul p a hp ih =>
    have ha : 0 < a := Nat.pos_of_mul_pos_left hm
    rw [mul_assoc, signOfSucc_mul_of_cocycleAt hp.pos (hσ p hp) (Nat.mul_pos ha hn), ih ha hn,
      signOfSucc_mul_of_cocycleAt hp.pos (hσ p hp) ha, mul_assoc]

/-- The completely multiplicative sign reconstructed from a prime-cocycle. -/
def CMSign.ofCocycle (σ : ℕ → ℤˣ) (hσ : ∀ p, p.Prime → IsDilationCocycleAt σ p) : CMSign where
  toFun := signOfSucc σ
  map_one' := signOfSucc_one σ
  map_mul' := fun hm hn => signOfSucc_mul_of_primeCocycle hσ hm hn

/-- **Characterization.** A sign sequence is the successor sign of a completely multiplicative
sign iff it satisfies the dilation cocycle at every prime. -/
theorem exists_cmSign_iff_primeCocycle (σ : ℕ → ℤˣ) :
    (∃ f : CMSign, ∀ n, 0 < n → succSign f n = σ n) ↔
      ∀ p, p.Prime → IsDilationCocycleAt σ p := by
  constructor
  · rintro ⟨f, hf⟩ p hp n hn
    rw [← hf n hn, ← dilation_cocycle f hp.pos hn]
    exact prod_congr rfl fun j _ => (hf _ (by have := Nat.mul_pos hp.pos hn; omega)).symm
  · intro hσ
    exact ⟨CMSign.ofCocycle σ hσ, fun n hn => succSign_signOfSucc σ hn⟩

/-- The prime cocycle implies the full cocycle. -/
theorem isDilationCocycle_of_prime {σ : ℕ → ℤˣ} (hσ : ∀ p, p.Prime → IsDilationCocycleAt σ p) :
    IsDilationCocycle σ := by
  obtain ⟨f, hf⟩ := (exists_cmSign_iff_primeCocycle σ).2 hσ
  intro m hm n hn
  rw [← hf n hn, ← dilation_cocycle f hm hn]
  exact prod_congr rfl fun j _ => (hf _ (by have := Nat.mul_pos hm hn; omega)).symm

/-! ## Multiplicative (not completely) functions: the pronic law -/

/-- **Pronic law.** Since consecutive integers are coprime, a multiplicative function satisfies
`g(n) g(n+1) = g(n(n+1))`: the successor correlation is a sum over pronic numbers. -/
theorem pronic_law {R : Type*} [CommMonoidWithZero R] {g : ArithmeticFunction R}
    (hg : g.IsMultiplicative) (n : ℕ) : g n * g (n + 1) = g (n * (n + 1)) :=
  (hg.map_mul_of_coprime (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right n))).symm

end GaloisForLFunctions.SignedSuccessorArithmetic
