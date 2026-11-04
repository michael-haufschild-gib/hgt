import GaloisForLFunctions.KodairaParshinAbc.TheIndexOfGammaZeroAtAPrime
import GaloisForLFunctions.HTGeometry.FreeCyclicOrbits
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# The genus of `X₀(23)`

The discriminant inequality uses the genus-two curve `X₀(23)` and its `j`-map of degree
`[SL(2, ℤ) : Γ₀(23)] = 24`.  The covering `X₀(p) → X(1)` has monodromy the action of
`SL(2, ℤ) = ⟨S, T⟩` on the cosets `SL(2, ℤ)/Γ₀(p) ≃ P¹(F_p)` (`gamma0QuotientEquiv`), where
`S` and `T` act by the Möbius maps

  `S : t ↦ -1/t`,  `T : t ↦ t + 1`,  `ST : t ↦ -1/(t + 1)`

(`firstColumnPoint_S_mul`, `firstColumnPoint_T_mul`).  For `p ≡ 11 (mod 12)`:

* `S` has no fixed point, since `t² = -1` has no solution (`p ≡ 3 mod 4`), and `ST` has none,
  since a root of `t² + t + 1` would have order `3` in `F_p^×` (`p ≡ 2 mod 3`); so both act
  freely, of orders `2` and `3` — there are no elliptic points;
* `T` has the two orbits `{∞}` and `F_p` — two cusps.

The Euler characteristic of the monodromy triple `(S, ST, T)` is therefore
`(p+1)/2 + (p+1)/3 + 2 - (p+1) = 2 - 2 (p+1)/12`, i.e. `X₀(p)` has genus `(p+1)/12`, and
`X₀(23)` has genus `2` (`eulerChar_monodromy_twentyThree`).
-/

noncomputable section

open Equiv Equiv.Perm Matrix CongruenceSubgroup
open scoped MatrixGroups

namespace GaloisForLFunctions.KodairaParshinAbc

open HTGeometry

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## The Möbius permutations of `P¹(F_p)` -/

/-- `S : t ↦ -1/t` on `P¹(F_p) = F_p ∪ {∞}`. -/
def sMap : Option (ZMod p) → Option (ZMod p)
  | none => some 0
  | some t => if t = 0 then none else some (-t⁻¹)

theorem sMap_involutive : Function.Involutive (sMap (p := p)) := by
  intro x
  rcases x with _ | t
  · simp [sMap]
  · by_cases ht : t = 0
    · simp [sMap, ht]
    · have h' : -t⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero ht)
      simp [sMap, ht, h']

/-- The permutation `S`. -/
def sPerm : Perm (Option (ZMod p)) := Function.Involutive.toPerm _ sMap_involutive

/-- The permutation `T : t ↦ t + 1`, fixing `∞`. -/
def tPerm : Perm (Option (ZMod p)) := Equiv.optionCongr (Equiv.addRight 1)

/-- The permutation `ST : t ↦ -1/(t + 1)`. -/
def stPerm : Perm (Option (ZMod p)) := sPerm * tPerm

@[simp] theorem sPerm_apply (x : Option (ZMod p)) : sPerm x = sMap x := rfl
@[simp] theorem tPerm_none : tPerm (p := p) none = none := rfl
@[simp] theorem tPerm_some (t : ZMod p) : tPerm (some t) = some (t + 1) := rfl

theorem stPerm_none : stPerm (p := p) none = some 0 := rfl

theorem stPerm_some_of_eq {t : ZMod p} (h : t + 1 = 0) : stPerm (some t) = none := by
  simp [stPerm, sMap, h]

theorem stPerm_some_of_ne {t : ZMod p} (h : t + 1 ≠ 0) :
    stPerm (some t) = some (-(t + 1)⁻¹) := by
  simp [stPerm, sMap, h]

/-- `S · ST = T`: the three monodromies multiply to the cusp monodromy. -/
theorem sPerm_mul_stPerm : sPerm (p := p) * stPerm = tPerm := by
  ext x : 1
  simp [stPerm, sMap_involutive _]

/-! ## No elliptic points for `p ≡ 11 (mod 12)` -/

theorem sq_ne_neg_one (hp4 : p % 4 = 3) (t : ZMod p) : t ^ 2 ≠ -1 := by
  intro h
  exact (ZMod.exists_sq_eq_neg_one_iff.mp ⟨t, by rw [← h, sq]⟩) hp4

theorem sq_add_self_add_one_ne_zero (hp3 : p % 3 = 2) (t : ZMod p) : t ^ 2 + t + 1 ≠ 0 := by
  intro h
  have h3 : t ^ 3 = 1 := by linear_combination (t - 1) * h
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at h
  have ht1 : t ≠ 1 := by
    rintro rfl
    have h3' : ((3 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination h
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at h3'
    have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp h3'
    omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf t = 3 := orderOf_eq_prime h3 ht1
  have hdvd := ZMod.orderOf_dvd_card_sub_one ht0
  rw [hord] at hdvd
  omega

theorem sPerm_apply_ne (hp4 : p % 4 = 3) (x : Option (ZMod p)) : sPerm x ≠ x := by
  rcases x with _ | t
  · simp [sMap]
  · by_cases ht : t = 0
    · simp [sMap, ht]
    · simp only [sPerm_apply, sMap, ht, if_false, ne_eq, Option.some.injEq]
      intro h
      apply sq_ne_neg_one hp4 t
      have : t * (-t⁻¹) = t * t := by rw [h]
      rw [mul_neg, mul_inv_cancel₀ ht] at this
      rw [sq]
      exact this.symm

/-- **`S` acts freely of order two** on `P¹(F_p)` for `p ≡ 3 (mod 4)`. -/
theorem sPerm_isFreeOfOrder (hp4 : p % 4 = 3) : IsFreeOfOrder (sPerm (p := p)) 2 where
  pow_eq_one := by
    ext x : 1
    simp [pow_two, sMap_involutive _]
  free := by
    intro k hk0 hk2 x
    interval_cases k
    simpa using sPerm_apply_ne hp4 x

theorem stPerm_apply_ne (hp3 : p % 3 = 2) (x : Option (ZMod p)) : stPerm x ≠ x := by
  rcases x with _ | t
  · simp [stPerm_none]
  · by_cases ht : t + 1 = 0
    · simp [stPerm_some_of_eq ht]
    · rw [stPerm_some_of_ne ht, ne_eq, Option.some.injEq]
      intro h
      apply sq_add_self_add_one_ne_zero hp3 t
      have : (t + 1) * (-(t + 1)⁻¹) = (t + 1) * t := by rw [h]
      rw [mul_neg, mul_inv_cancel₀ ht] at this
      linear_combination -this

theorem stPerm_cube : (stPerm (p := p)) ^ 3 = 1 := by
  have h10 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have hm1 : (-1 : ZMod p) + 1 = 0 := by ring
  have h01 : (0 : ZMod p) + 1 ≠ 0 := by rw [zero_add]; exact h10
  ext x : 1
  simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply]
  rcases x with _ | t
  · rw [stPerm_none, stPerm_some_of_ne h01, zero_add, inv_one, stPerm_some_of_eq hm1]
  · by_cases ht : t + 1 = 0
    · have hneg : -(0 + 1 : ZMod p)⁻¹ = t := by
        rw [zero_add, inv_one]
        linear_combination -ht
      rw [stPerm_some_of_eq ht, stPerm_none, stPerm_some_of_ne h01, hneg]
    · by_cases ht0 : t = 0
      · subst ht0
        rw [stPerm_some_of_ne h01, zero_add, inv_one, stPerm_some_of_eq hm1, stPerm_none]
      · have hu : -(t + 1)⁻¹ + 1 ≠ 0 := by
          intro h
          apply ht0
          have : (t + 1) * (-(t + 1)⁻¹ + 1) = 0 := by rw [h, mul_zero]
          rw [mul_add, mul_neg, mul_inv_cancel₀ ht] at this
          linear_combination this
        have e1 : -(t + 1)⁻¹ + 1 = t / (t + 1) := by
          field_simp
          ring
        have e : -(-(t + 1)⁻¹ + 1)⁻¹ + 1 = -t⁻¹ := by
          rw [e1, inv_div]
          field_simp
          ring
        have hv : -(-(t + 1)⁻¹ + 1)⁻¹ + 1 ≠ 0 := by
          rw [e]
          exact neg_ne_zero.mpr (inv_ne_zero ht0)
        rw [stPerm_some_of_ne ht, stPerm_some_of_ne hu, stPerm_some_of_ne hv, Option.some.injEq,
          e, inv_neg, inv_inv, neg_neg]

/-- **`ST` acts freely of order three** on `P¹(F_p)` for `p ≡ 2 (mod 3)`. -/
theorem stPerm_isFreeOfOrder (hp3 : p % 3 = 2) : IsFreeOfOrder (stPerm (p := p)) 3 where
  pow_eq_one := stPerm_cube
  free := by
    intro k hk0 hk3 x
    interval_cases k
    · simpa using stPerm_apply_ne hp3 x
    · intro h
      apply stPerm_apply_ne hp3 x
      have h3 := congrArg (fun φ : Perm (Option (ZMod p)) => φ x) (stPerm_cube (p := p))
      simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply] at h3 h
      calc stPerm x = stPerm (stPerm (stPerm x)) := by rw [h]
        _ = x := h3

/-! ## The cusps -/

theorem tPerm_pow_some (a : ZMod p) (n : ℕ) : (tPerm ^ n) (some a) = some (a + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, tPerm_some]
    push_cast
    ring_nf

theorem tPerm_support : (tPerm (p := p)).support = Finset.univ.erase none := by
  ext x
  rcases x with _ | t
  · simp
  · simp [Perm.mem_support]

/-- **`T` is a single `p`-cycle on `F_p`**, fixing `∞`. -/
theorem tPerm_isCycle : (tPerm (p := p)).IsCycle := by
  refine ⟨some 0, by simp, fun y hy => ?_⟩
  rcases y with _ | s
  · exact absurd rfl hy
  · refine ⟨(s.val : ℤ), ?_⟩
    rw [zpow_natCast, tPerm_pow_some, zero_add, ZMod.natCast_zmod_val]

/-- The number of `⟨σ⟩`-orbits: the nontrivial cycles together with the fixed points. -/
def orbitCount {X : Type*} [Fintype X] [DecidableEq X] (σ : Perm X) : ℕ :=
  σ.cycleType.card + (Fintype.card X - σ.support.card)

theorem card_projectiveLine : Fintype.card (Option (ZMod p)) = p + 1 := by
  rw [Fintype.card_option, ZMod.card]

/-- **Two cusps**: `T` has exactly two orbits on `P¹(F_p)`. -/
theorem orbitCount_tPerm : orbitCount (tPerm (p := p)) = 2 := by
  have hsupp : (tPerm (p := p)).support.card = p := by
    rw [tPerm_support, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      card_projectiveLine]
    rfl
  rw [orbitCount, tPerm_isCycle.cycleType, hsupp, card_projectiveLine]
  simp

theorem orbitCount_of_isFreeOfOrder {X : Type*} [Fintype X] [DecidableEq X] {σ : Perm X} {a : ℕ}
    (h : IsFreeOfOrder σ a) (ha : 2 ≤ a) : a * orbitCount σ = Fintype.card X := by
  rw [orbitCount, h.support_eq_univ (by omega), Finset.card_univ, Nat.sub_self, add_zero,
    h.card_eq_mul_cycleType_card ha]

/-! ## The genus -/

/-- The Euler characteristic `#⟨S⟩-orbits + #⟨ST⟩-orbits + #⟨T⟩-orbits - [SL(2,ℤ) : Γ₀(p)]` of the
monodromy triple of `X₀(p) → X(1)`. -/
def monodromyEulerChar (p : ℕ) [Fact p.Prime] : ℤ :=
  orbitCount (sPerm (p := p)) + orbitCount (stPerm (p := p)) + orbitCount (tPerm (p := p)) -
    (p + 1 : ℕ)

/-- **`X₀(p)` has genus `(p+1)/12` for `p ≡ 11 (mod 12)`**: `χ = 2 - 2 (p+1)/12`. -/
theorem monodromyEulerChar_eq (hp12 : p % 12 = 11) :
    monodromyEulerChar p = 2 - 2 * (((p + 1) / 12 : ℕ) : ℤ) := by
  have hS := orbitCount_of_isFreeOfOrder (sPerm_isFreeOfOrder (p := p) (by omega)) le_rfl
  have hST := orbitCount_of_isFreeOfOrder (stPerm_isFreeOfOrder (p := p) (by omega))
    (by norm_num)
  rw [card_projectiveLine] at hS hST
  rw [monodromyEulerChar, orbitCount_tPerm]
  omega

/-- **`X₀(23)` has genus two**: `χ = -2`. -/
theorem eulerChar_monodromy_twentyThree :
    haveI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    monodromyEulerChar 23 = -2 := by
  haveI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  rw [monodromyEulerChar_eq (by norm_num)]
  norm_num

/-! ## The monodromy is the coset action -/

/-- Left multiplication by `S` acts on the first column as `t ↦ -1/t`. -/
theorem firstColumnPoint_S_mul (γ : SL(2, ℤ)) :
    firstColumnPoint (p := p) (ModularGroup.S * γ) = sMap (firstColumnPoint γ) := by
  have hcol := firstColumn_ne_zero (p := p) γ
  have h00 : ((ModularGroup.S * γ : SL(2, ℤ)) 0 0 : ℤ) = -γ 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h10 : ((ModularGroup.S * γ : SL(2, ℤ)) 1 0 : ℤ) = γ 0 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  unfold firstColumnPoint
  rw [h00, h10]
  push_cast
  by_cases hc : ((γ 1 0 : ℤ) : ZMod p) = 0
  · have ha : ((γ 0 0 : ℤ) : ZMod p) ≠ 0 := fun ha => hcol ⟨ha, hc⟩
    simp [hc, ha, sMap]
  · by_cases ha : ((γ 0 0 : ℤ) : ZMod p) = 0
    · simp [hc, ha, sMap]
    · simp only [hc, ha, if_false, sMap, div_eq_zero_iff, or_self, inv_div]
      rw [neg_div]

/-- Left multiplication by `T` acts on the first column as `t ↦ t + 1`. -/
theorem firstColumnPoint_T_mul (γ : SL(2, ℤ)) :
    firstColumnPoint (p := p) (ModularGroup.T * γ) = tPerm (firstColumnPoint γ) := by
  have h00 : ((ModularGroup.T * γ : SL(2, ℤ)) 0 0 : ℤ) = γ 0 0 + γ 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h10 : ((ModularGroup.T * γ : SL(2, ℤ)) 1 0 : ℤ) = γ 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  unfold firstColumnPoint
  rw [h00, h10]
  push_cast
  by_cases hc : ((γ 1 0 : ℤ) : ZMod p) = 0
  · simp [hc]
  · simp only [hc, if_false, tPerm_some, Option.some.injEq]
    field_simp

end GaloisForLFunctions.KodairaParshinAbc
