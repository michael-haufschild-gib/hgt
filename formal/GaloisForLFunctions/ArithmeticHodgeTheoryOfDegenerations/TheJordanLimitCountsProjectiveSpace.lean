import GaloisForLFunctions.ArithmeticDegenerationTheory.TheLimitingMixedStructure
import GaloisForLFunctions.ArithmeticDegenerationTheory.TheRescaledLimitTensorizesOverThePrimes

/-!
# The Jordan limit counts points of projective space

The rescaled limit of the complete Weil family is the Jordan form `J(m) = J(1) J₈(m)/φ(m)` (ADT).
Its graded polarization is a cardinality: `J_k(m)` counts the primitive vectors of `(ℤ/m)^k` (those
whose entries generate the unit ideal), the units of `ℤ/m` act freely on them, and the orbits are
the points of `ℙ^{k−1}(ℤ/m)`. Hence

* **Count law** (`natCard_projPoints_mul_totient`, `jordanCoefficient_eq_projPoints`):
  `#ℙ^{k−1}(ℤ/m) · φ(m) = J_k(m)`, and `J(m) = J(1) · #ℙ⁷(ℤ/m)`.
* **Weight strings are Hensel towers** (`projPoints_prime_mul`, `projPoints_prime_pow_succ`):
  `#ℙ^{k−1}(𝔽_p)(p − 1) = p^k − 1` at the bottom of a `p`-tower and
  `#ℙ^{k−1}(ℤ/p^{a+1}) = p^{k−1} #ℙ^{k−1}(ℤ/p^a)` along it; the tensor law is the Chinese remainder
  theorem `ℙ(ℤ/ab) = ℙ(ℤ/a) × ℙ(ℤ/b)`.

The limiting polarization of the degeneration is positive because it is the point count of a smooth
projective scheme over `ℤ`: the first-order structure of the field is a count, as Weil's
intersection numbers are. The sign question lives entirely in the second-order term.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open ArithmeticDegenerationTheory

/-- A vector is primitive when its entries generate the unit ideal. -/
def IsPrimitiveVec {R : Type*} [CommRing R] {k : ℕ} (v : Fin k → R) : Prop :=
  ∃ l : Fin k → R, ∑ i, l i * v i = 1

/-- The primitive vectors of `(ℤ/m)^k`. -/
abbrev PrimVec (k m : ℕ) := {v : Fin k → ZMod m // IsPrimitiveVec v}

/-! ### Primitivity under ring isomorphisms and products -/

theorem isPrimitiveVec_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) {k : ℕ}
    (v : Fin k → R) : IsPrimitiveVec (fun i => e (v i)) ↔ IsPrimitiveVec v := by
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨fun i => e.symm (l i), e.injective ?_⟩
    simp only [map_sum, map_mul, RingEquiv.apply_symm_apply, map_one]
    exact hl
  · rintro ⟨l, hl⟩
    refine ⟨fun i => e (l i), ?_⟩
    simp only [← map_mul, ← map_sum, hl, map_one]

theorem isPrimitiveVec_prod_iff {R S : Type*} [CommRing R] [CommRing S] {k : ℕ}
    (v : Fin k → R × S) :
    IsPrimitiveVec v ↔ IsPrimitiveVec (fun i => (v i).1) ∧ IsPrimitiveVec (fun i => (v i).2) := by
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨⟨fun i => (l i).1, ?_⟩, ⟨fun i => (l i).2, ?_⟩⟩
    · have := congrArg Prod.fst hl
      simpa only [Prod.fst_sum, Prod.fst_mul, Prod.fst_one] using this
    · have := congrArg Prod.snd hl
      simpa only [Prod.snd_sum, Prod.snd_mul, Prod.snd_one] using this
  · rintro ⟨⟨l₁, h₁⟩, ⟨l₂, h₂⟩⟩
    refine ⟨fun i => (l₁ i, l₂ i), Prod.ext ?_ ?_⟩
    · simpa only [Prod.fst_sum, Prod.fst_mul, Prod.fst_one] using h₁
    · simpa only [Prod.snd_sum, Prod.snd_mul, Prod.snd_one] using h₂

/-- **Chinese remainder theorem for primitive vectors.** -/
def primVecCRT {k m n : ℕ} (h : m.Coprime n) : PrimVec k (m * n) ≃ PrimVec k m × PrimVec k n :=
  let e := ZMod.chineseRemainder h
  let F : (Fin k → ZMod (m * n)) ≃ (Fin k → ZMod m) × (Fin k → ZMod n) :=
    (Equiv.piCongrRight fun _ => e.toEquiv).trans (Equiv.arrowProdEquivProdArrow _ _ _)
  (F.subtypeEquiv fun v => by
      rw [← isPrimitiveVec_ringEquiv e v, isPrimitiveVec_prod_iff]
      rfl).trans
    (Equiv.subtypeProdEquivProd (p := IsPrimitiveVec) (q := IsPrimitiveVec))

theorem natCard_primVec_mul {k m n : ℕ} (h : m.Coprime n) :
    Nat.card (PrimVec k (m * n)) = Nat.card (PrimVec k m) * Nat.card (PrimVec k n) := by
  rw [Nat.card_congr (primVecCRT h), Nat.card_prod]

theorem natCard_primVec_one (k : ℕ) : Nat.card (PrimVec k 1) = 1 := by
  have : ∀ v : Fin k → ZMod 1, IsPrimitiveVec v := fun v => ⟨0, Subsingleton.elim _ _⟩
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv this)]
  exact Nat.card_unique

/-! ### Prime powers -/

section PrimePower

variable {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
include hp ha

/-- In `ℤ/p^a` an element is a unit exactly when its reduction mod `p` is nonzero. -/
theorem isUnit_iff_castHom_ne_zero (x : ZMod (p ^ a)) :
    IsUnit x ↔ ZMod.castHom (dvd_pow_self p (by omega : a ≠ 0)) (ZMod p) x ≠ 0 := by
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hL : IsUnit x ↔ ¬p ∣ x.val := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x]
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm,
      hp.coprime_iff_not_dvd]
  rw [hL, ZMod.castHom_apply, ZMod.cast_eq_val, Ne, ZMod.natCast_eq_zero_iff]

theorem isPrimitiveVec_iff_exists_isUnit {k : ℕ} (v : Fin k → ZMod (p ^ a)) :
    IsPrimitiveVec v ↔ ∃ i, IsUnit (v i) := by
  haveI := Fact.mk hp
  constructor
  · rintro ⟨l, hl⟩
    by_contra hno
    simp only [not_exists] at hno
    set π := ZMod.castHom (dvd_pow_self p (by omega : a ≠ 0)) (ZMod p)
    have h0 : ∀ i, π (v i) = 0 := fun i => by
      by_contra hne
      exact hno i ((isUnit_iff_castHom_ne_zero hp ha (v i)).mpr hne)
    have := congrArg π hl
    simp only [map_sum, map_mul, h0, mul_zero, sum_const_zero, map_one] at this
    exact zero_ne_one this
  · rintro ⟨i, hi⟩
    refine ⟨Pi.single i (↑hi.unit⁻¹ : ZMod (p ^ a)), ?_⟩
    rw [Fintype.sum_eq_single i fun j hj => by simp [hj]]
    simp only [Pi.single_eq_same]
    exact hi.val_inv_mul

/-- The units of a monoid as an `IsUnit` subtype. -/
def unitsEquivIsUnit (M : Type*) [Monoid M] : Mˣ ≃ {x : M // IsUnit x} where
  toFun u := ⟨u, u.isUnit⟩
  invFun x := x.2.unit
  left_inv _ := Units.ext rfl
  right_inv _ := Subtype.ext rfl

/-- `ℤ/p^a` has `p^{a−1}` non-units. -/
theorem natCard_nonunits : Nat.card {x : ZMod (p ^ a) // ¬IsUnit x} = p ^ (a - 1) := by
  classical
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ZMod.card,
    ← Fintype.card_congr (unitsEquivIsUnit (ZMod (p ^ a))), ZMod.card_units_eq_totient,
    Nat.totient_prime_pow hp (by omega)]
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  rw [Nat.mul_sub, mul_one, Nat.sub_sub_self (Nat.le_mul_of_pos_right _ hp.pos)]

/-- **Primitive vectors mod a prime power**: `(p^a)^k − (p^{a−1})^k`. -/
theorem natCard_primVec_prime_pow (k : ℕ) :
    Nat.card (PrimVec k (p ^ a)) = (p ^ a) ^ k - (p ^ (a - 1)) ^ k := by
  classical
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have e1 : PrimVec k (p ^ a) ≃ {v : Fin k → ZMod (p ^ a) // ¬∀ i, ¬IsUnit (v i)} :=
    Equiv.subtypeEquivRight fun v => by
      rw [isPrimitiveVec_iff_exists_isUnit hp ha]; simp only [not_forall, not_not]
  have e2 : {v : Fin k → ZMod (p ^ a) // ∀ i, ¬IsUnit (v i)} ≃
      (Fin k → {x : ZMod (p ^ a) // ¬IsUnit x}) :=
    Equiv.subtypePiEquivPi (p := fun _ x => ¬IsUnit x)
  have hcompl : Nat.card {v : Fin k → ZMod (p ^ a) // ¬∀ i, ¬IsUnit (v i)} =
      Nat.card (Fin k → ZMod (p ^ a)) - Nat.card {v : Fin k → ZMod (p ^ a) // ∀ i, ¬IsUnit (v i)} := by
    simp only [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_compl _
  rw [Nat.card_congr e1, hcompl, Nat.card_congr e2, Nat.card_fun, Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin, natCard_nonunits hp ha]

end PrimePower

/-! ### The count law -/

theorem jordanTotient_natCast (k m : ℕ) :
    jordanTotient k m = ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℝ) * (d : ℝ) ^ k := by
  simp only [jordanTotient, Real.rpow_natCast]

/-- `J_k(p^a) = p^{k(a−1)}(p^k − 1)` with natural exponents. -/
theorem jordanTotient_prime_pow_nat {p : ℕ} (hp : p.Prime) (k : ℕ) {a : ℕ} (ha : 1 ≤ a) :
    jordanTotient k (p ^ a) = (p : ℝ) ^ (k * (a - 1)) * ((p : ℝ) ^ k - 1) := by
  rw [jordanTotient_prime_pow hp k ha,
    show ((k : ℕ) : ℝ) * ((a - 1 : ℕ) : ℝ) = ((k * (a - 1) : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, Real.rpow_natCast]

/-- **Primitive vectors are counted by Jordan's totient**: `#{v ∈ (ℤ/m)^k primitive} = J_k(m)`. -/
theorem natCard_primVec_eq_jordanTotient {k : ℕ} (hk : 0 < k) :
    ∀ m : ℕ, 1 ≤ m → (Nat.card (PrimVec k m) : ℝ) = jordanTotient k m := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p a hp ha =>
    intro _
    have hp' : p.Prime := hp
    rw [natCard_primVec_prime_pow hp' ha k, jordanTotient_prime_pow_nat hp' k ha,
      Nat.cast_sub (Nat.pow_le_pow_left (Nat.pow_le_pow_right hp'.pos (by omega)) k)]
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  | zero => intro h; omega
  | one => intro _; rw [natCard_primVec_one, jordanTotient_one]; simp
  | coprime a b ha hb hab iha ihb =>
    intro _
    rw [natCard_primVec_mul hab, Nat.cast_mul, iha (by omega), ihb (by omega),
      ← jordanTotient_mul_of_coprime hk hab]

/-! ### Projective points -/

/-- Units of `ℤ/m` act on primitive vectors by scaling. -/
instance primVecMulAction (k m : ℕ) : MulAction (ZMod m)ˣ (PrimVec k m) where
  smul u v := ⟨fun i => (u : ZMod m) * v.1 i, by
    obtain ⟨l, hl⟩ := v.2
    refine ⟨fun i => (↑u⁻¹ : ZMod m) * l i, ?_⟩
    calc ∑ i, (↑u⁻¹ : ZMod m) * l i * ((u : ZMod m) * v.1 i)
        = ((↑u⁻¹ : ZMod m) * u) * ∑ i, l i * v.1 i := by
          rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
      _ = 1 := by rw [hl, Units.inv_mul, one_mul]⟩
  one_smul v := Subtype.ext (funext fun i => by
    change ((1 : (ZMod m)ˣ) : ZMod m) * v.1 i = v.1 i
    rw [Units.val_one, one_mul])
  mul_smul u w v := Subtype.ext (funext fun i => by
    change ((u * w : (ZMod m)ˣ) : ZMod m) * v.1 i = (u : ZMod m) * ((w : ZMod m) * v.1 i)
    rw [Units.val_mul, mul_assoc])

theorem primVec_smul_val {k m : ℕ} (u : (ZMod m)ˣ) (v : PrimVec k m) (i : Fin k) :
    (u • v).1 i = (u : ZMod m) * v.1 i := rfl

/-- The action of the units on primitive vectors is free. -/
theorem eq_one_of_smul_eq {k m : ℕ} {u : (ZMod m)ˣ} {v : PrimVec k m} (h : u • v = v) : u = 1 := by
  obtain ⟨l, hl⟩ := v.2
  have hv : ∀ i, (u : ZMod m) * v.1 i = v.1 i := fun i => congrFun (congrArg Subtype.val h) i
  apply Units.ext
  calc (u : ZMod m) = (u : ZMod m) * ∑ i, l i * v.1 i := by rw [hl, mul_one]
    _ = ∑ i, l i * ((u : ZMod m) * v.1 i) := by
      rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
    _ = 1 := by simp only [hv, hl]
    _ = ((1 : (ZMod m)ˣ) : ZMod m) := Units.val_one.symm

/-- The points of `ℙ^{k−1}(ℤ/m)`: primitive vectors modulo units. -/
abbrev ProjPoints (k m : ℕ) := MulAction.orbitRel.Quotient (ZMod m)ˣ (PrimVec k m)

/-- **Orbit count**: `#PrimVec = #ℙ^{k−1}(ℤ/m) · φ(m)`. -/
theorem natCard_primVec_eq (k m : ℕ) [NeZero m] :
    Nat.card (PrimVec k m) = Nat.card (ProjPoints k m) * m.totient := by
  classical
  have horb : ∀ x : PrimVec k m,
      Nat.card (MulAction.orbit (ZMod m)ˣ x) = Nat.card (ZMod m)ˣ := fun x => by
    refine (Nat.card_congr (Equiv.ofBijective (fun g : (ZMod m)ˣ =>
      (⟨g • x, MulAction.mem_orbit x g⟩ : MulAction.orbit (ZMod m)ˣ x)) ⟨?_, ?_⟩)).symm
    · intro g h hgh
      have h1 : g • x = h • x := congrArg Subtype.val hgh
      have h2 : (h⁻¹ * g) • x = x := by rw [mul_smul, h1, ← mul_smul, inv_mul_cancel, one_smul]
      have := eq_one_of_smul_eq h2
      rw [inv_mul_eq_one] at this
      exact this.symm
    · rintro ⟨y, g, rfl⟩
      exact ⟨g, rfl⟩
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits (ZMod m)ˣ (PrimVec k m)),
    Nat.card_sigma]
  simp only [horb, sum_const, card_univ, smul_eq_mul]
  rw [Nat.card_eq_fintype_card (α := (ZMod m)ˣ), ZMod.card_units_eq_totient,
    Nat.card_eq_fintype_card (α := ProjPoints k m)]

/-- **Count law**: `#ℙ^{k−1}(ℤ/m) · φ(m) = J_k(m)`. -/
theorem natCard_projPoints_mul_totient {k : ℕ} (hk : 0 < k) {m : ℕ} (hm : 1 ≤ m) :
    (Nat.card (ProjPoints k m) : ℝ) * m.totient = jordanTotient k m := by
  haveI : NeZero m := ⟨by omega⟩
  rw [← natCard_primVec_eq_jordanTotient hk m hm, natCard_primVec_eq, Nat.cast_mul]

/-- **The Jordan limit counts `ℙ⁷`**: `J(m) = J(1) · #ℙ⁷(ℤ/m)`. -/
theorem jordanCoefficient_eq_projPoints {m : ℕ} (hm : 1 ≤ m) :
    jordanCoefficient m = jordanCoefficient 1 * Nat.card (ProjPoints 8 m) := by
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hc0 := natCard_projPoints_mul_totient (k := 8) (by norm_num) hm
  have hc : (Nat.card (ProjPoints 8 m) : ℝ) * m.totient = jordanTotient 8 m := by
    simpa using hc0
  have hJ : (Nat.card (ProjPoints 8 m) : ℝ) = jordanTotient 8 m / m.totient := by
    rw [← hc, mul_div_cancel_right₀ _ hφ.ne']
  rw [hJ]
  simp only [jordanCoefficient, jordanTotient_one, Nat.totient_one, Nat.cast_one, div_one,
    mul_one]
  ring

/-! ### Weight strings as Hensel towers -/

/-- Bottom of a tower: `#ℙ^{k−1}(𝔽_p) (p − 1) = p^k − 1`. -/
theorem projPoints_prime_mul {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 0 < k) :
    (Nat.card (ProjPoints k p) : ℝ) * (p - 1) = (p : ℝ) ^ k - 1 := by
  have h := natCard_projPoints_mul_totient hk (m := p) hp.one_lt.le
  have hJ := jordanTotient_prime_pow hp k (a := 1) le_rfl
  rw [pow_one] at hJ
  rw [Nat.totient_prime hp, hJ] at h
  rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one] at h
  simpa [Real.rpow_natCast] using h

/-- Along a tower: `#ℙ^{k−1}(ℤ/p^{a+1}) = p^{k−1} #ℙ^{k−1}(ℤ/p^a)` for `a ≥ 1`. -/
theorem projPoints_prime_pow_succ {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 0 < k) {a : ℕ}
    (ha : 1 ≤ a) :
    (Nat.card (ProjPoints k (p ^ (a + 1))) : ℝ) =
      (p : ℝ) ^ (k - 1) * Nat.card (ProjPoints k (p ^ a)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (0 : ℝ) < p - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  have h1 := natCard_projPoints_mul_totient hk (m := p ^ (a + 1)) (Nat.one_le_pow _ _ hp.pos)
  have h2 := natCard_projPoints_mul_totient hk (m := p ^ a) (Nat.one_le_pow _ _ hp.pos)
  rw [jordanTotient_prime_pow_nat hp k (by omega), Nat.totient_prime_pow hp (by omega)] at h1
  rw [jordanTotient_prime_pow_nat hp k ha, Nat.totient_prime_pow hp (by omega)] at h2
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1 h2 ⊢
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_lt.le, Nat.cast_one] at h1 h2
  have hden : (p : ℝ) ^ (b + 1) * (p - 1) ≠ 0 := (mul_pos (pow_pos hp0 _) hp1).ne'
  apply mul_right_cancel₀ hden
  rw [h1, show (p : ℝ) ^ j * (Nat.card (ProjPoints (j + 1) (p ^ (b + 1))) : ℝ) *
      ((p : ℝ) ^ (b + 1) * (p - 1)) = (p : ℝ) ^ j * p *
      ((Nat.card (ProjPoints (j + 1) (p ^ (b + 1))) : ℝ) * ((p : ℝ) ^ b * (p - 1))) by ring, h2]
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
