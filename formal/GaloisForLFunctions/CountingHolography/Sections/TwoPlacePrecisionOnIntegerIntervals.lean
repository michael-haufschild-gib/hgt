import GaloisForLFunctions.CountingHolography.Sections.SmallSectionsOfARationalLattice
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Log

/-!
# Precision at two places on integer intervals

Index each interval by the distance from its left endpoint. If two coprime
input moduli fit jointly inside the interval and each corresponding output
modulus is at least the length of the narrow output interval, Chinese
remaindering forces that output coordinate to be constant.
-/

namespace GaloisForLFunctions.CountingHolography.Sections

/-- A small section is indexed by its displacement from the left endpoint.
Differences in this index are differences of the integer coordinates. -/
noncomputable def sectionOrdinal (d A : ℝ) :
    ↥(smallSections d A) ≃ Fin (smallSections d A).card := by
  let r := ⌊Real.exp A / d⌋₊
  have hc : (smallSections d A).card = 2*r+1 := card_smallSections _ _
  have hm (z : ℤ) : z ∈ smallSections d A ↔ -(r : ℤ) ≤ z ∧ z ≤ r := Finset.mem_Icc
  refine
    { toFun := fun z => ⟨(z.val + r).toNat, ?_⟩
      invFun := fun i => ⟨(i.val : ℤ) - r, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hz := (hm _).mp z.property
    omega
  · apply (hm _).mpr
    have hi := i.isLt
    omega
  · intro z
    have hz := (hm _).mp z.property
    apply Subtype.ext
    dsimp only
    omega
  · intro i
    apply Fin.ext
    dsimp only
    omega

/-- Precision of a map into a rectangle. Congruence of both input indices
modulo P forces congruence of the narrow output index modulo u. -/
def preservesSecondMod {n L s : ℕ} (f : Fin n × Fin n → Fin L × Fin s) (P u : ℕ) : Prop :=
  ∀ x y, x.1.val ≡ y.1.val [MOD P] → x.2.val ≡ y.2.val [MOD P] →
    (f x).2.val ≡ (f y).2.val [MOD u]

/-- A loss of i digits at p allows the input to be known to r+i digits
when only r output digits are requested. -/
def secondPrecisionLoss {n L s : ℕ} (f : Fin n × Fin n → Fin L × Fin s) (p i : ℕ) : Prop :=
  ∀ r : ℕ, preservesSecondMod f (p^(r+i)) (p^r)

theorem sectionOrdinal_sub {d A : ℝ} (x y : ↥(smallSections d A)) :
    (((sectionOrdinal d A x).val : ℤ) - (sectionOrdinal d A y).val) = x.val - y.val := by
  let r := ⌊Real.exp A / d⌋₊
  change (((x.val + r).toNat : ℤ) - (y.val + r).toNat) = _
  have hx : -(r : ℤ) ≤ x.val := (Finset.mem_Icc.mp x.property).1
  have hy : -(r : ℤ) ≤ y.val := (Finset.mem_Icc.mp y.property).1
  omega

/-- Independent residue assignments at two places make the narrow
coordinate constant as soon as the source meets every joint residue. -/
theorem second_constant_of_coprime {n L s P Q u v : ℕ} (f : Fin n × Fin n → Fin L × Fin s)
    (hc : P.Coprime Q) (hP : P ≠ 0) (hQ : Q ≠ 0) (hn : P*Q ≤ n)
    (hu : s ≤ u) (hv : s ≤ v) (hfP : preservesSecondMod f P u) (hfQ : preservesSecondMod f Q v) :
    ∀ x y, (f x).2 = (f y).2 := by
  let w (a b : Fin n) : Fin n :=
    ⟨(Nat.chineseRemainder hc a.val b.val).val,
      (Nat.chineseRemainder_lt_mul hc _ _ hP hQ).trans_le hn⟩
  intro x y
  let z := (w x.1 y.1, w x.2 y.2)
  have hzx := hfP z x (Nat.chineseRemainder hc _ _).property.1 (Nat.chineseRemainder hc _ _).property.1
  have hzy := hfQ z y (Nat.chineseRemainder hc _ _).property.2 (Nat.chineseRemainder hc _ _).property.2
  apply Fin.ext
  exact (hzx.eq_of_lt_of_lt ((f z).2.isLt.trans_le hu) ((f x).2.isLt.trans_le hu)).symm.trans
    (hzy.eq_of_lt_of_lt ((f z).2.isLt.trans_le hv) ((f y).2.isLt.trans_le hv))

/-- If the wide output alone cannot hold the input square, the product
of the two required input moduli must exceed the input length. -/
theorem input_lt_precision_product {n L s P Q u v : ℕ} (e : (Fin n × Fin n) ↪ (Fin L × Fin s))
    (hc : P.Coprime Q) (hP : P ≠ 0) (hQ : Q ≠ 0) (hL : L < n*n)
    (hu : s ≤ u) (hv : s ≤ v) (hfP : preservesSecondMod e P u) (hfQ : preservesSecondMod e Q v) :
    n < P*Q := by
  by_contra! hn
  have he := second_constant_of_coprime e hc hP hQ hn hu hv hfP hfQ
  let e₁ : (Fin n × Fin n) ↪ Fin L :=
    ⟨fun x => (e x).1, fun x y hxy => e.injective (Prod.ext hxy (he x y))⟩
  have hh := Fintype.card_le_of_embedding e₁
  exact hL.not_ge (by simpa only [Fintype.card_prod, Fintype.card_fin] using hh)

/-- Quantitative precision loss for any embedding and any two coprime bases.
The moduli may be chosen separately for each embedding. -/
theorem two_place_precision_loss {n L s p q i j : ℕ} (e : (Fin n × Fin n) ↪ (Fin L × Fin s))
    (hp : 1 < p) (hq : 1 < q) (hc : p.Coprime q) (hs : 0 < s) (hL : L < n*n)
    (hi : secondPrecisionLoss e p i) (hj : secondPrecisionLoss e q j) :
    n < (p*q*s^2) * (p^i*q^j) := by
  let r := Nat.log p s + 1
  let t := Nat.log q s + 1
  have hsmall (b : ℕ) : b^(Nat.log b s+1) ≤ s*b := by
    rw [pow_succ]
    exact Nat.mul_le_mul_right b (Nat.pow_log_le_self b hs.ne')
  have hh := input_lt_precision_product e ((hc.pow_left (r+i)).pow_right (t+j))
    (pow_ne_zero _ (by omega)) (pow_ne_zero _ (by omega)) hL
    (Nat.lt_pow_succ_log_self hp s).le (Nat.lt_pow_succ_log_self hq s).le (hi r) (hj t)
  refine hh.trans_le ?_
  rw [pow_add p r i, pow_add q t j]
  calc p^r*p^i*(q^t*q^j) ≤ (s*p*p^i)*(s*q*q^j) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (hsmall p)) (Nat.mul_le_mul_right _ (hsmall q))
    _ = _ := by ring

/-- Both output coordinates preserve congruences at every power of the base. -/
def preservesPlace {n L s : ℕ} (f : Fin n × Fin n → Fin L × Fin s) (p : ℕ) : Prop :=
  ∀ (t : ℕ) x y, x.1.val ≡ y.1.val [MOD p^t] → x.2.val ≡ y.2.val [MOD p^t] →
    (f x).1.val ≡ (f y).1.val [MOD p^t] ∧ (f x).2.val ≡ (f y).2.val [MOD p^t]

private theorem remainder_preserves_place (p r t : ℕ) {a b : ℕ} (h : a ≡ b [MOD p^t]) :
    a % p^r ≡ b % p^r [MOD p^t] := by
  rcases le_total t r with htr | hrt
  · change a % p^r % p^t = b % p^r % p^t
    rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow p htr), Nat.mod_mod_of_dvd _ (pow_dvd_pow p htr)]
    exact h
  · have he : a % p^r = b % p^r := h.of_dvd (pow_dvd_pow p hrt)
    rw [he]

/-- Split a base-p digit block from the first input and put the remaining
digits above the second input. The resulting embedding respects every
power of p in both output coordinates. -/
theorem exists_embedding_preserving_place_of_blocks {n L s p r H : ℕ} (hp : 0 < p)
    (hn : n ≤ H*p^r) (hs : p^r ≤ s) (hL : H*(H*p^r) ≤ L) :
    ∃ e : (Fin n × Fin n) ↪ (Fin L × Fin s), preservesPlace e p := by
  let P := p^r
  let W := H*P
  have hP : 0 < P := pow_pos hp _
  let f (x : Fin n × Fin n) : Fin L × Fin s :=
    (⟨x.2.val + W*(x.1.val/P), by
      have hq : x.1.val/P < H := (Nat.div_lt_iff_lt_mul hP).mpr (x.1.isLt.trans_le hn)
      calc x.2.val + W*(x.1.val/P) < W + W*(x.1.val/P) :=
              Nat.add_lt_add_right (x.2.isLt.trans_le hn) _
        _ = (x.1.val/P+1)*W := by ring
        _ ≤ H*W := Nat.mul_le_mul_right W hq
        _ ≤ _ := hL⟩, ⟨x.1.val % P, (Nat.mod_lt _ hP).trans_le hs⟩)
  have hi : Function.Injective f := by
    intro x y he
    have hxy : x.2.val + W*(x.1.val/P) = y.2.val + W*(y.1.val/P) :=
      congrArg (fun z : Fin L × Fin s => z.1.val) he
    have hr : x.1.val % P = y.1.val % P := congrArg (fun z : Fin L × Fin s => z.2.val) he
    have hy : x.2.val = y.2.val := by
      have hxW : x.2.val < W := x.2.isLt.trans_le hn
      have hyW : y.2.val < W := y.2.isLt.trans_le hn
      have hmod := congrArg (fun a : ℕ => a % W) hxy
      change (_ + W*(x.1.val/P)) % W = (_ + W*(y.1.val/P)) % W at hmod
      rwa [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hxW,
        Nat.mod_eq_of_lt hyW] at hmod
    have hq : x.1.val/P = y.1.val/P := by
      rw [hy] at hxy
      exact mul_left_cancel₀ (Nat.ne_of_gt ((Nat.zero_le _).trans_lt (x.2.isLt.trans_le hn)))
        (Nat.add_left_cancel hxy)
    apply Prod.ext _ (Fin.ext hy)
    apply Fin.ext
    calc x.1.val = x.1.val % P + P*(x.1.val/P) := (Nat.mod_add_div _ _).symm
      _ = y.1.val % P + P*(y.1.val/P) := by rw [hr,hq]
      _ = y.1.val := Nat.mod_add_div _ _
  refine ⟨⟨f,hi⟩,?_⟩
  intro t x y hx hy
  have hr : x.1.val % P ≡ y.1.val % P [MOD p^t] := remainder_preserves_place p r t hx
  have hb : P*(x.1.val/P) ≡ P*(y.1.val/P) [MOD p^t] := hr.add_left_cancel (by
    rw [Nat.mod_add_div, Nat.mod_add_div]; exact hx)
  refine ⟨?_,hr⟩
  change (x.2.val + W*(x.1.val/P)) ≡ (y.2.val + W*(y.1.val/P)) [MOD p^t]
  simpa only [W,Nat.mul_assoc] using hy.add (hb.mul_left H)

/-- A fixed multiplicative surplus in the area accommodates rounding
the narrow output length down to a power of any prescribed base. -/
theorem exists_embedding_preserving_one_place {n L s p : ℕ}
    (hp : 1 < p) (hs : 0 < s) (hsn : s ≤ n) (harea : 4*p*n^2 ≤ L*s) :
    ∃ e : (Fin n × Fin n) ↪ (Fin L × Fin s), preservesPlace e p := by
  let r := Nat.log p s
  let P := p^r
  let H := n/P+1
  have hp' : 0 < p := by omega
  have hP : 0 < P := pow_pos hp' _
  have hPs : P ≤ s := Nat.pow_log_le_self _ hs.ne'
  have hsP : s ≤ P*p := by
    have h := (Nat.lt_pow_succ_log_self hp s).le
    rwa [pow_succ] at h
  have hW : n ≤ H*P ∧ H*P ≤ 2*n := by
    have he : H*P = P*(n/P)+P := by dsimp only [H]; ring
    have hmod := Nat.mod_add_div n P
    have hm := Nat.mod_lt n hP
    omega
  apply exists_embedding_preserving_place_of_blocks hp' hW.1 hPs
  apply (mul_le_mul_iff_left₀ hp').mp
  apply (mul_le_mul_iff_left₀ hP).mp
  calc H*(H*P)*p*P = p*(H*P)^2 := by ring
    _ ≤ p*(2*n)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hW.2 _)
    _ = 4*p*n^2 := by ring
    _ ≤ L*s := harea
    _ ≤ L*(P*p) := Nat.mul_le_mul_left _ hsP
    _ = L*p*P := by ring

#print axioms exists_embedding_preserving_one_place
#print axioms second_constant_of_coprime
#print axioms two_place_precision_loss

end GaloisForLFunctions.CountingHolography.Sections
