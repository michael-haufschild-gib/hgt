import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheFrobeniusGraphsMeetInThePrimes
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheTeichmullerPointsAndTheLatticeOfSections

/-!
# The arithmetic square is cofree

A ring `A` has **Frobenius lifts** (`FrobeniusLifts A`) if it carries ring endomorphisms `ψ_n`,
`n ≥ 1`, with `ψ_1 = id`, `ψ_m ψ_n = ψ_{mn}` and `ψ_p(a) ≡ a^p (mod pA)` for every prime `p`: a
descent datum to `𝔽₁` in Λ-geometry.

* **Cofreeness** (`ghostLift`, `ghostLift_frobenius`, `ghostLift_unique`). For every such ring and
  every `ℤ`-point `f : A → ℤ`, the sequence `(f(ψ_n a))_n` satisfies the Dwork congruences, and
  `a ↦ (f(ψ_n a))_n` is the unique equivariant ring homomorphism `A → 𝒢` over `f`. So
  `𝒢 = W(ℤ)` is `Spec ℤ ×_{𝔽₁} Spec ℤ`: every geometry with Frobenius lifts in which `Spec ℤ` has a
  point maps to it. The proof is the lifting lemma `a ≡ b (mod p^k) ⇒ a^p ≡ b^p (mod p^{k+1})`
  (`prime_pow_succ_dvd_pow_sub_pow`).
* **The square has Frobenius lifts** (`ghostFrobeniusLifts`): `F_p x = x^p + p · δ_p x` with
  `δ_p x = ((x_{pn} − x_n^p)/p)_n` again in `𝒢` (`delta`, `frobenius_eq_pow_add_delta`).
* **Every Frobenius lift fixes its prime** (`span_fixed_le_graphIdeal`,
  `prime_dvd_sub_frobeniusLift`). On every ring with Frobenius lifts and every `ℤ`-point, the fixed
  scheme of `ψ_n` contains `Γ_1 ∩ Γ_n`; in particular `p ∣ f(a) − f(ψ_{p^k} a)`. The cofree ring is
  the one in which nothing else is fixed.
-/

open Finset

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- **The lifting lemma.** `x ≡ y (mod p^k)`, `k ≥ 1`, gives `x^p ≡ y^p (mod p^{k+1})`. -/
theorem prime_pow_succ_dvd_pow_sub_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) {x y : ℤ}
    (h : (p : ℤ) ^ k ∣ x - y) : (p : ℤ) ^ (k + 1) ∣ x ^ p - y ^ p := by
  haveI := Fact.mk hp
  have hp1 : (p : ℤ) ∣ x - y := (dvd_pow_self _ hk).trans h
  -- modulo `p` the geometric sum is `p y^{p-1}`
  have hsum : (p : ℤ) ∣ ∑ i ∈ range p, x ^ i * y ^ (p - 1 - i) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hxy : ((x : ℤ) : ZMod p) = y := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (x - y) p).mpr hp1
      push_cast at this
      exact sub_eq_zero.mp this
    push_cast
    rw [hxy]
    have hterm : ∀ i ∈ range p, ((y : ℤ) : ZMod p) ^ i * ((y : ℤ) : ZMod p) ^ (p - 1 - i) =
        ((y : ℤ) : ZMod p) ^ (p - 1) := by
      intro i hi
      rw [← pow_add]
      congr 1
      have := mem_range.mp hi
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_range, nsmul_eq_mul, ZMod.natCast_self,
      zero_mul]
  have hfac : x ^ p - y ^ p = (x - y) * ∑ i ∈ range p, x ^ i * y ^ (p - 1 - i) := by
    rw [mul_comm]; exact (geom_sum₂_mul x y p).symm
  rw [hfac, pow_succ]
  exact mul_dvd_mul h hsum

/-! ### Rings with Frobenius lifts -/

/-- **Commuting Frobenius lifts**: ring endomorphisms `ψ_n`, multiplicative in `n`, with
`ψ_p(a) ≡ a^p (mod p)` at every prime. -/
structure FrobeniusLifts (A : Type*) [CommRing A] where
  /-- The Frobenius of degree `n`. -/
  ψ : ℕ+ →* (A →+* A)
  /-- `ψ_p` lifts the `p`-th power map. -/
  lift : ∀ p : ℕ+, p.Prime → ∀ a : A, ∃ b : A, ψ p a = a ^ (p : ℕ) + ((p : ℕ) : A) * b

variable {A : Type*} [CommRing A]

theorem FrobeniusLifts.ψ_mul_apply (L : FrobeniusLifts A) (m n : ℕ+) (a : A) :
    L.ψ (m * n) a = L.ψ m (L.ψ n a) := by
  rw [map_mul]; rfl

@[simp] theorem FrobeniusLifts.ψ_one_apply (L : FrobeniusLifts A) (a : A) : L.ψ 1 a = a := by
  rw [map_one]; rfl

/-- Along the powers of `p`: `f(ψ_{p^{r+1}} c) ≡ f(ψ_{p^r} c) (mod p^{r+1})`. -/
theorem FrobeniusLifts.pow_succ_dvd (L : FrobeniusLifts A) (f : A →+* ℤ) {p : ℕ+} (hp : p.Prime)
    (r : ℕ) (c : A) :
    ((p : ℕ) : ℤ) ^ (r + 1) ∣ f (L.ψ (p ^ (r + 1)) c) - f (L.ψ (p ^ r) c) := by
  have hp' : (p : ℕ).Prime := hp
  induction r generalizing c with
  | zero =>
    obtain ⟨b, hb⟩ := L.lift p hp c
    rw [zero_add, pow_one, pow_one, pow_zero, L.ψ_one_apply, hb, map_add, map_pow, map_mul,
      map_natCast]
    have h : f c ^ (p : ℕ) + ((p : ℕ) : ℤ) * f b - f c =
        (f c ^ (p : ℕ) - f c) + ((p : ℕ) : ℤ) * f b := by ring
    rw [h]
    exact dvd_add (prime_dvd_pow_sub_self hp' (f c)) (dvd_mul_right _ _)
  | succ r ih =>
    obtain ⟨b, hb⟩ := L.lift p hp c
    -- `ψ_{p^{s+1}} c = (ψ_{p^s} c)^p + p ψ_{p^s} b`
    have step : ∀ s : ℕ, f (L.ψ (p ^ (s + 1)) c) =
        f (L.ψ (p ^ s) c) ^ (p : ℕ) + ((p : ℕ) : ℤ) * f (L.ψ (p ^ s) b) := by
      intro s
      rw [pow_succ, L.ψ_mul_apply, hb, map_add, map_pow, map_mul, map_natCast, map_add, map_pow,
        map_mul, map_natCast]
    have key : f (L.ψ (p ^ (r + 1 + 1)) c) - f (L.ψ (p ^ (r + 1)) c) =
        (f (L.ψ (p ^ (r + 1)) c) ^ (p : ℕ) - f (L.ψ (p ^ r) c) ^ (p : ℕ)) +
          ((p : ℕ) : ℤ) * (f (L.ψ (p ^ (r + 1)) b) - f (L.ψ (p ^ r) b)) := by
      have f1 := step (r + 1)
      have f2 := step r
      linear_combination f1 - f2
    rw [key]
    refine dvd_add (prime_pow_succ_dvd_pow_sub_pow hp' (Nat.succ_ne_zero r) (ih c)) ?_
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih b)

/-- **The trace sequence of a ring with Frobenius lifts satisfies the Dwork congruences.** -/
theorem FrobeniusLifts.isGhost (L : FrobeniusLifts A) (f : A →+* ℤ) (a : A) :
    IsGhost fun n : ℕ+ => f (L.ψ n a) := by
  intro p hp n
  obtain ⟨m, hm⟩ : p ^ ((n : ℕ).factorization p) ∣ n :=
    PNat.dvd_iff.mpr (by rw [PNat.pow_coe]; exact Nat.ordProj_dvd _ _)
  have h := L.pow_succ_dvd f hp ((n : ℕ).factorization p) (L.ψ m a)
  have e : p ^ ((n : ℕ).factorization p + 1) * m = p * n := by
    rw [pow_succ', mul_assoc, ← hm]
  rw [← L.ψ_mul_apply, ← L.ψ_mul_apply, e, ← hm] at h
  exact h

/-- **The canonical lift** of a `ℤ`-point to the arithmetic square: `a ↦ (f(ψ_n a))_n`. -/
def ghostLift (L : FrobeniusLifts A) (f : A →+* ℤ) : A →+* ghostRing where
  toFun a := ⟨fun n => f (L.ψ n a), L.isGhost f a⟩
  map_one' := Subtype.ext (funext fun n => by simp)
  map_mul' a b := Subtype.ext (funext fun n => by simp)
  map_zero' := Subtype.ext (funext fun n => by simp)
  map_add' a b := Subtype.ext (funext fun n => by simp)

@[simp] theorem ghostComponent_ghostLift (L : FrobeniusLifts A) (f : A →+* ℤ) (n : ℕ+) (a : A) :
    ghostComponent n (ghostLift L f a) = f (L.ψ n a) := rfl

/-- The lift lies over `f`: its diagonal component is `f`. -/
theorem ghostComponent_one_ghostLift (L : FrobeniusLifts A) (f : A →+* ℤ) (a : A) :
    ghostComponent 1 (ghostLift L f a) = f a := by
  rw [ghostComponent_ghostLift, L.ψ_one_apply]

/-- The lift is equivariant: `ψ_k` goes to the Witt Frobenius `F_k`. -/
theorem ghostLift_frobenius (L : FrobeniusLifts A) (f : A →+* ℤ) (k : ℕ+) (a : A) :
    ghostLift L f (L.ψ k a) = frobenius k (ghostLift L f a) :=
  Subtype.ext (funext fun n => by
    change f (L.ψ n (L.ψ k a)) = f (L.ψ (k * n) a)
    rw [← L.ψ_mul_apply, mul_comm])

/-- **Cofreeness.** The canonical lift is the only equivariant ring homomorphism over `f`. -/
theorem ghostLift_unique (L : FrobeniusLifts A) (f : A →+* ℤ) (h : A →+* ghostRing)
    (h1 : ∀ a, ghostComponent 1 (h a) = f a)
    (hF : ∀ (k : ℕ+) (a : A), h (L.ψ k a) = frobenius k (h a)) : h = ghostLift L f := by
  refine RingHom.ext fun a => ghostRing_ext fun n => ?_
  have := h1 (L.ψ n a)
  rw [hF, ghostComponent_frobenius, mul_one] at this
  rw [this, ghostComponent_ghostLift]

/-! ### The `p`-derivations of the square -/

/-- The `p`-derivation on sequences: `(δ_p x)_n = (x_{pn} − x_n^p)/p`. -/
def deltaFun (p : ℕ+) (x : ℕ+ → ℤ) : ℕ+ → ℤ := fun n => (x (p * n) - x n ^ (p : ℕ)) / ((p : ℕ) : ℤ)

theorem IsGhost.prime_dvd_sub_pow {x : ℕ+ → ℤ} (hx : IsGhost x) {p : ℕ+} (hp : p.Prime) (n : ℕ+) :
    ((p : ℕ) : ℤ) ∣ x (p * n) - x n ^ (p : ℕ) := by
  have h : x (p * n) - x n ^ (p : ℕ) = (x (p * n) - x n) - (x n ^ (p : ℕ) - x n) := by ring
  rw [h]
  exact dvd_sub ((dvd_pow_self _ (Nat.succ_ne_zero _)).trans (hx p hp n))
    (prime_dvd_pow_sub_self hp (x n))

theorem mul_deltaFun_eq {x : ℕ+ → ℤ} (hx : IsGhost x) {p : ℕ+} (hp : p.Prime) (n : ℕ+) :
    ((p : ℕ) : ℤ) * deltaFun p x n = x (p * n) - x n ^ (p : ℕ) :=
  Int.mul_ediv_cancel' (hx.prime_dvd_sub_pow hp n)

/-- **`δ_p` preserves the arithmetic square.** -/
theorem isGhost_deltaFun {x : ℕ+ → ℤ} (hx : IsGhost x) {p : ℕ+} (hp : p.Prime) :
    IsGhost (deltaFun p x) := by
  intro q hq n
  have hp' : (p : ℕ).Prime := hp
  have hq' : (q : ℕ).Prime := hq
  have hp0 : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hp'.ne_zero
  -- `p (δ_p x_{qn} − δ_p x_n) = (x_{q(pn)} − x_{pn}) − (x_{qn}^p − x_n^p)`
  have hZ : ((p : ℕ) : ℤ) * (deltaFun p x (q * n) - deltaFun p x n) =
      (x (q * (p * n)) - x (p * n)) - (x (q * n) ^ (p : ℕ) - x n ^ (p : ℕ)) := by
    rw [mul_sub, mul_deltaFun_eq hx hp, mul_deltaFun_eq hx hp, mul_left_comm p q n]
    ring
  by_cases hqp : q = p
  · subst hqp
    -- both differences are divisible by `p^{v+2}`
    have h1 : ((q : ℕ) : ℤ) ^ ((n : ℕ).factorization q + 1 + 1) ∣ x (q * (q * n)) - x (q * n) := by
      have := hx q hq (q * n)
      rwa [PNat.mul_coe, Nat.factorization_mul q.ne_zero n.ne_zero, Finsupp.add_apply,
        hq'.factorization, Finsupp.single_eq_same, add_comm 1] at this
    have h2 : ((q : ℕ) : ℤ) ^ ((n : ℕ).factorization q + 1 + 1) ∣
        x (q * n) ^ (q : ℕ) - x n ^ (q : ℕ) :=
      prime_pow_succ_dvd_pow_sub_pow hq' (Nat.succ_ne_zero _) (hx q hq n)
    have h3 := dvd_sub h1 h2
    rw [← hZ, pow_succ' _ ((n : ℕ).factorization q + 1)] at h3
    exact (mul_dvd_mul_iff_left hp0).mp h3
  · have hne : (q : ℕ) ≠ (p : ℕ) := fun h => hqp (PNat.eq h)
    have h1 : ((q : ℕ) : ℤ) ^ ((n : ℕ).factorization q + 1) ∣ x (q * (p * n)) - x (p * n) := by
      refine (pow_dvd_pow _ (Nat.succ_le_succ ?_)).trans (hx q hq (p * n))
      rw [PNat.mul_coe, Nat.factorization_mul p.ne_zero n.ne_zero, Finsupp.add_apply]
      exact Nat.le_add_left _ _
    have h2 : ((q : ℕ) : ℤ) ^ ((n : ℕ).factorization q + 1) ∣
        x (q * n) ^ (p : ℕ) - x n ^ (p : ℕ) :=
      (hx q hq n).trans (sub_dvd_pow_sub_pow _ _ _)
    have h3 := dvd_sub h1 h2
    rw [← hZ] at h3
    have hcop : IsCoprime (((q : ℕ) : ℤ) ^ ((n : ℕ).factorization q + 1)) ((p : ℕ) : ℤ) :=
      (Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hq' hp').mpr hne)).pow_left
    exact hcop.dvd_of_dvd_mul_left h3

/-- The `p`-derivation `δ_p` of the arithmetic square. -/
def delta (p : ℕ+) (hp : p.Prime) (x : ghostRing) : ghostRing := ⟨deltaFun p x.1, isGhost_deltaFun x.2 hp⟩

/-- **`F_p x = x^p + p δ_p x`**: the Witt Frobenius at `p` lifts the `p`-th power map. -/
theorem frobenius_eq_pow_add_delta (p : ℕ+) (hp : p.Prime) (x : ghostRing) :
    frobenius p x = x ^ (p : ℕ) + ((p : ℕ) : ghostRing) * delta p hp x := by
  refine Subtype.ext (funext fun n => ?_)
  change x.1 (p * n) = x.1 n ^ (p : ℕ) + ((p : ℕ) : ℤ) * deltaFun p x.1 n
  rw [mul_deltaFun_eq x.2 hp]
  ring

/-- **The arithmetic square has Frobenius lifts**: the Witt Frobenii. -/
def ghostFrobeniusLifts : FrobeniusLifts ghostRing where
  ψ :=
    { toFun := frobenius
      map_one' := RingHom.ext frobenius_one
      map_mul' := fun k l => RingHom.ext fun x => by
        rw [RingHom.mul_def, RingHom.comp_apply, frobenius_frobenius, mul_comm] }
  lift := fun p hp x => ⟨delta p hp x, frobenius_eq_pow_add_delta p hp x⟩

/-! ### Every Frobenius lift fixes its prime -/

/-- **The fixed scheme of `ψ_n` contains `Γ_1 ∩ Γ_n`.** On every ring with Frobenius lifts and every
`ℤ`-point the differences `f(a) − f(ψ_n a)` lie in the graph ideal of the arithmetic square. -/
theorem span_fixed_le_graphIdeal (L : FrobeniusLifts A) (f : A →+* ℤ) (n : ℕ+) :
    Ideal.span (Set.range fun a : A => f a - f (L.ψ n a)) ≤ graphIdeal 1 n := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨a, rfl⟩
  refine Ideal.subset_span ⟨ghostLift L f a, ?_⟩
  change ghostComponent 1 (ghostLift L f a) - ghostComponent n (ghostLift L f a) = _
  rw [ghostComponent_one_ghostLift, ghostComponent_ghostLift]

/-- On the arithmetic square itself the fixed scheme of `F_n` on the diagonal is `Γ_1 ∩ Γ_n`. -/
theorem span_fixed_ghostRing (n : ℕ+) :
    Ideal.span (Set.range fun x : ghostRing =>
      ghostComponent 1 x - ghostComponent 1 (ghostFrobeniusLifts.ψ n x)) = graphIdeal 1 n := by
  refine congrArg Ideal.span (congrArg Set.range (funext fun x => ?_))
  change x.1 1 - x.1 (n * 1) = x.1 1 - x.1 n
  rw [mul_one]

/-- **Every Frobenius lift fixes its prime**: `p ∣ f(a) − f(ψ_{p^k} a)` on every ring with Frobenius
lifts and every `ℤ`-point. -/
theorem prime_dvd_sub_frobeniusLift (L : FrobeniusLifts A) (f : A →+* ℤ) {p : ℕ+} (hp : p.Prime)
    {k : ℕ} (hk : k ≠ 0) (a : A) : ((p : ℕ) : ℤ) ∣ f a - f (L.ψ (p ^ k) a) := by
  have h := span_fixed_le_graphIdeal L f (p ^ k) (Ideal.subset_span ⟨a, rfl⟩)
  rw [graphIdeal_one_prime_pow hp hk] at h
  exact Ideal.mem_span_singleton.mp h

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
