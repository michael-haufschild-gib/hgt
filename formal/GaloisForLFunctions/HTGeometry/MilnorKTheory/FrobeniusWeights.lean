import GaloisForLFunctions.HTGeometry.MilnorKDegFunctoriality
import GaloisForLFunctions.HTGeometry.MilnorKSlotGeneration
import Mathlib.Algebra.CharP.Frobenius

/-!
# Frobenius weights on Milnor symbols

Multilinearity gives weight `n` to a symbol of length `n`: raising every entry to the
`d`th power multiplies its class by `d^n`. In characteristic `p`, this identifies the
actual map induced by Frobenius, including every iterate, on the whole Milnor group.
This is the Milnor-symbol counterpart of the Frobenius distribution mechanism for
polylogarithms in Kupers--Rudenko--Sierra, §4.4.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F]

/-- Raising one entry to a natural power multiplies its symbol class by that power. -/
theorem milnorClassDeg_pow_slot {n : ℕ} (a : Fˣ) (l₁ l₂ : List Fˣ) (d : ℕ)
    (h : (l₁ ++ l₂).length + 1 = n) :
    milnorClassDeg F n ⟨l₁ ++ a ^ d :: l₂, (length_middle F _ _ _).trans h⟩ =
      d • milnorClassDeg F n ⟨l₁ ++ a :: l₂, (length_middle F _ _ _).trans h⟩ := by
  induction d with
  | zero =>
      simpa only [pow_zero, zero_nsmul] using
        milnorClassDeg_one_of_eq l₁ l₂ rfl ((length_middle F _ _ _).trans h)
  | succ d ih =>
      rw [pow_succ, milnorClassDeg_mul_of_eq F (a ^ d) a l₁ l₂ rfl rfl rfl
        ((length_middle F _ _ _).trans h) ((length_middle F _ _ _).trans h)
        ((length_middle F _ _ _).trans h),
        ih, succ_nsmul]

/-- Multilinearity in all entries, with a fixed prefix left unchanged. -/
theorem milnorClassDeg_map_pow_suffix {n : ℕ} (d : ℕ) (l l₁ : List Fˣ)
    (h : (l₁ ++ l).length = n) :
    milnorClassDeg F n ⟨l₁ ++ l.map (fun a => a ^ d), by simpa only
      [List.length_append, List.length_map] using h⟩ =
      d ^ l.length • milnorClassDeg F n ⟨l₁ ++ l, h⟩ := by
  induction l generalizing l₁ with
  | nil => simp only [List.map_nil, List.length_nil, pow_zero, one_nsmul]
  | cons a l ih =>
      have hlen : (l₁ ++ l.map (fun a => a ^ d)).length + 1 = n := by
        simpa only [List.length_append, List.length_map, List.length_cons,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
      have htail := ih (l₁ ++ [a]) (by simpa only
        [List.append_assoc, List.singleton_append] using h)
      simp only [List.append_assoc, List.singleton_append] at htail
      simp only [List.map_cons, List.length_cons]
      rw [milnorClassDeg_pow_slot a l₁ (l.map (fun a => a ^ d)) d hlen,
        htail, smul_smul, pow_succ, Nat.mul_comm d]

/-- The simultaneous power operation has degree `n` on degree-`n` symbols. -/
theorem milnorClassDeg_map_pow (d n : ℕ) (s : MilnorSymbolDeg F n) :
    milnorClassDeg F n ⟨s.val.map (fun a => a ^ d), by
      rw [List.length_map, s.property]⟩ = d ^ n • milnorClassDeg F n s := by
  rcases s with ⟨l, hl⟩
  simpa only [List.nil_append, hl] using milnorClassDeg_map_pow_suffix d l [] hl

variable (p : ℕ) [Fact p.Prime] [CharP F p]

/-- Frobenius scales the entire degree-`n` Milnor group by `p^n`. -/
theorem milnorKDegMap_frobenius (n : ℕ) (x : MilnorKDeg F n) :
    milnorKDegMap (frobenius F p) n x = p ^ n • x := by
  have hhom : milnorKDegMap (frobenius F p) n =
      p ^ n • AddMonoidHom.id (MilnorKDeg F n) := by
    apply milnorKDeg_hom_ext F
    intro s
    rw [milnorKDegMap_class]
    have hunit : milnorUnitMap (frobenius F p) = fun a : Fˣ => a ^ p := by
      funext a
      apply Units.ext
      rfl
    simpa only [milnorSymbolDegMap, hunit, AddMonoidHom.nsmul_apply,
      AddMonoidHom.id_apply] using milnorClassDeg_map_pow p n s
  exact DFunLike.congr_fun hhom x

/-- The `r`th Frobenius iterate acts with weight `p^(r*n)`. -/
theorem milnorKDegMap_iterateFrobenius (r n : ℕ) (x : MilnorKDeg F n) :
    milnorKDegMap (iterateFrobenius F p r) n x = p ^ (r * n) • x := by
  have hhom : milnorKDegMap (iterateFrobenius F p r) n =
      p ^ (r * n) • AddMonoidHom.id (MilnorKDeg F n) := by
    apply milnorKDeg_hom_ext F
    intro s
    rw [milnorKDegMap_class]
    have hunit : milnorUnitMap (iterateFrobenius F p r) =
        fun a : Fˣ => a ^ (p ^ r) := by
      funext a
      apply Units.ext
      rfl
    simpa only [milnorSymbolDegMap, hunit, AddMonoidHom.nsmul_apply,
      AddMonoidHom.id_apply, ← pow_mul] using milnorClassDeg_map_pow (p ^ r) n s
  exact DFunLike.congr_fun hhom x

end GaloisForLFunctions.HTGeometry
