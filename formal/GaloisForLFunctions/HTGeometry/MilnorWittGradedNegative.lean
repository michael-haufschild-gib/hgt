import GaloisForLFunctions.HTGeometry.MilnorWittGradedIso

/-!
# Negative degrees of graded Milnor--Witt `K`-theory

In a negative degree every word `η^k[a_1]⋯[a_m]` has `k = m - n > 0`, so over a quadratically
closed field every word with a symbol vanishes and only the powers of `η` survive.  The hyperbolic
relation makes twice such a power zero, and the parity of the word — one for the empty word, zero
otherwise — is a well-defined invariant taking the value one on it.  Hence

  `K_n^{MW}(F) ≅ ℤ/2` for `n < 0`.

* `mwRankMod2` : the parity invariant, defined in every degree.
* `mwEtaPow` : the power of `η` generating a negative degree.
* `mwNegDegreeEquiv` : the isomorphism with `ℤ/2`.
-/

namespace GaloisForLFunctions.HTGeometry

section MilnorWittGradedNegative

variable {F : Type*} [Field F]

/-- The parity of a word: one for a pure power of `η`, zero as soon as a symbol occurs. -/
def mwRankMod2Word (n : ℤ) : MWWordDeg F n → ZMod 2
  | ⟨(_, []), _⟩ => 1
  | ⟨(_, _ :: _), _⟩ => 0

/-- The parity on formal sums of words. -/
def mwRankMod2Lift (n : ℤ) : FreeAbelianGroup (MWWordDeg F n) →+ ZMod 2 :=
  FreeAbelianGroup.lift (mwRankMod2Word n)

@[simp]
theorem mwRankMod2Lift_of (n : ℤ) (w : MWWordDeg F n) :
    mwRankMod2Lift n (FreeAbelianGroup.of w) = mwRankMod2Word n w :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **The parity descends.**  Every word occurring in a Steinberg or twisted relation carries a
symbol, and the two `η`-powers of the hyperbolic relation cancel modulo two. -/
theorem mwRankMod2Lift_ker (n : ℤ) : mwRelDeg F n ≤ (mwRankMod2Lift (F := F) n).ker := by
  have htwo : ∀ x : ZMod 2, x + x = 0 := by decide
  rw [mwRelDeg, AddSubgroup.closure_le]
  rintro x ((⟨k, a, ha, l₁, l₂, hp, rfl⟩ | ⟨k, a, b, l₁, l₂, hab, hpa, hpb, hpe, rfl⟩) |
    ⟨k, l₁, l₂, h1, h2, rfl⟩)
  · show mwRankMod2Lift n _ = 0
    rw [mwRankMod2Lift_of]
    cases l₁ <;> rfl
  · show mwRankMod2Lift n _ = 0
    rw [map_sub, map_sub, map_sub, mwRankMod2Lift_of, mwRankMod2Lift_of, mwRankMod2Lift_of,
      mwRankMod2Lift_of]
    cases l₁ <;> · show (0 : ZMod 2) - 0 - 0 - 0 = 0; decide
  · show mwRankMod2Lift n _ = 0
    rw [map_add, map_add, mwRankMod2Lift_of, mwRankMod2Lift_of]
    have hfirst : mwRankMod2Word (F := F) n ⟨(k + 2, l₁ ++ (-1 : Fˣ) :: l₂), h1⟩ = 0 := by
      cases l₁ <;> rfl
    rw [hfirst, zero_add]
    exact htwo _

/-- **The parity invariant** of a Milnor--Witt class. -/
def mwRankMod2 (n : ℤ) : MilnorWittKDeg F n →+ ZMod 2 :=
  QuotientAddGroup.lift _ (mwRankMod2Lift n) (mwRankMod2Lift_ker n)

@[simp]
theorem mwRankMod2_class (n : ℤ) (w : MWWordDeg F n) :
    mwRankMod2 n (mwClassDeg F n w) = mwRankMod2Word n w := by
  show mwRankMod2Lift n (FreeAbelianGroup.of w) = _
  rw [mwRankMod2Lift_of]

/-- The power of `η` sitting in a negative degree. -/
def mwEtaPow {n : ℤ} (hn : n ≤ -1) : MilnorWittKDeg F n :=
  mwClassDeg F n ⟨((-n).toNat, []), by
    simp only [List.length_nil]
    omega⟩

@[simp]
theorem mwRankMod2_etaPow {n : ℤ} (hn : n ≤ -1) :
    mwRankMod2 (F := F) n (mwEtaPow hn) = 1 := by
  rw [mwEtaPow, mwRankMod2_class]
  rfl

/-- **Twice a power of `η` vanishes**, by the hyperbolic relation. -/
theorem mwEtaPow_add_self (hsq : ∀ x : F, ∃ y : F, x = y * y) {n : ℤ} (hn : n ≤ -1) :
    (mwEtaPow hn : MilnorWittKDeg F n) + mwEtaPow hn = 0 := by
  have hk : (-n).toNat = ((-n).toNat - 1) + 1 := by omega
  have p1 : (((([(-1 : Fˣ)] : List Fˣ).length : ℤ))) - (((-n).toNat - 1 : ℕ) + 2) = n := by
    simp only [List.length_cons, List.length_nil]
    omega
  have p2 : ((([] : List Fˣ).length : ℤ)) - (((-n).toNat - 1 : ℕ) + 1) = n := by
    simp only [List.length_nil]
    omega
  have hhyp := mwClassDeg_hyperbolic (F := F) ((-n).toNat - 1) [] []
    (show ([(-1 : Fˣ)] : List Fˣ) = [] ++ (-1 : Fˣ) :: [] from rfl)
    (show ([] : List Fˣ) = [] ++ [] from rfl) p1 p2
  have hzero : mwClassDeg F n ⟨(((-n).toNat - 1 : ℕ) + 2, [(-1 : Fˣ)]), p1⟩ = 0 :=
    mwClassDeg_eq_zero_of_eta hsq _ (-1) [] p1
  rw [hzero, zero_add] at hhyp
  have hgen : mwClassDeg F n ⟨(((-n).toNat - 1 : ℕ) + 1, ([] : List Fˣ)), p2⟩ =
      mwEtaPow (F := F) hn := by
    rw [mwEtaPow]
    congr 1
    exact Subtype.ext (by
      show ((((-n).toNat - 1 : ℕ) + 1), ([] : List Fˣ)) = ((-n).toNat, [])
      congr 1
      omega)
  rw [hgen] at hhyp
  exact hhyp

/-- **Every class in a negative degree is a multiple of the `η`-power.** -/
theorem exists_zsmul_eq_mwEtaPow (hsq : ∀ x : F, ∃ y : F, x = y * y) {n : ℤ} (hn : n ≤ -1)
    (y : MilnorWittKDeg F n) : ∃ m : ℤ, y = m • mwEtaPow hn := by
  refine QuotientAddGroup.induction_on y fun v => ?_
  induction v using FreeAbelianGroup.induction_on with
  | zero => exact ⟨0, by rw [zero_smul]; rfl⟩
  | of w =>
    obtain ⟨⟨k, l⟩, p⟩ := w
    cases l with
    | nil =>
      refine ⟨1, ?_⟩
      rw [one_zsmul, mwEtaPow]
      show mwClassDeg F n ⟨(k, ([] : List Fˣ)), p⟩ = _
      congr 1
      exact Subtype.ext (by
        show ((k, ([] : List Fˣ))) = ((-n).toNat, [])
        simp only [List.length_nil] at p
        congr 1
        omega)
    | cons u t =>
      refine ⟨0, ?_⟩
      rw [zero_smul]
      show mwClassDeg F n ⟨(k, u :: t), p⟩ = 0
      cases k with
      | zero =>
        exfalso
        simp only [List.length_cons] at p
        push_cast at p
        omega
      | succ j => exact mwClassDeg_eq_zero_of_eta hsq j u t p
  | neg w ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨-m, ?_⟩
    have hmk : (QuotientAddGroup.mk (s := mwRelDeg F n) (-FreeAbelianGroup.of w)) =
        -(QuotientAddGroup.mk (s := mwRelDeg F n) (FreeAbelianGroup.of w)) := rfl
    rw [hmk, hm, neg_zsmul]
    rfl
  | add u v hu hv =>
    obtain ⟨m₁, h₁⟩ := hu
    obtain ⟨m₂, h₂⟩ := hv
    refine ⟨m₁ + m₂, ?_⟩
    have hmk : (QuotientAddGroup.mk (s := mwRelDeg F n) (u + v)) =
        QuotientAddGroup.mk (s := mwRelDeg F n) u +
          QuotientAddGroup.mk (s := mwRelDeg F n) v := rfl
    rw [hmk, h₁, h₂, add_zsmul]
    rfl

theorem mwRankMod2_injective (hsq : ∀ x : F, ∃ y : F, x = y * y) {n : ℤ} (hn : n ≤ -1) :
    Function.Injective (mwRankMod2 (F := F) n) := by
  intro x y hxy
  obtain ⟨m, rfl⟩ := exists_zsmul_eq_mwEtaPow hsq hn x
  obtain ⟨j, rfl⟩ := exists_zsmul_eq_mwEtaPow hsq hn y
  rw [map_zsmul, map_zsmul, mwRankMod2_etaPow] at hxy
  have hdvd : (2 : ℤ) ∣ (m - j) := by
    have hmj : ((m : ℤ) : ZMod 2) = ((j : ℤ) : ZMod 2) := by
      simpa [zsmul_eq_mul] using hxy
    have h : ((m - j : ℤ) : ZMod 2) = 0 := by
      push_cast
      rw [hmj, sub_self]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 h
  obtain ⟨c, hc⟩ := hdvd
  have h2 : (2 : ℤ) • (mwEtaPow (F := F) hn) = 0 := by
    rw [two_zsmul]
    exact mwEtaPow_add_self hsq hn
  have hzero2 : (m - j) • (mwEtaPow (F := F) hn) = 0 := by
    rw [hc, mul_comm, mul_zsmul, h2, smul_zero]
  rw [← sub_eq_zero]
  calc m • (mwEtaPow (F := F) hn) - j • mwEtaPow hn = (m - j) • mwEtaPow hn := by
        rw [sub_zsmul]
        abel
    _ = 0 := hzero2

theorem mwRankMod2_surjective {n : ℤ} (hn : n ≤ -1) :
    Function.Surjective (mwRankMod2 (F := F) n) := by
  intro z
  refine ⟨(z.val : ℤ) • mwEtaPow hn, ?_⟩
  rw [map_zsmul, mwRankMod2_etaPow, zsmul_eq_mul, mul_one]
  push_cast
  exact ZMod.natCast_rightInverse z

/-- **`K_n^{MW}(F) ≅ ℤ/2` in every negative degree** over a quadratically closed field: only the
powers of `η` survive, and the hyperbolic relation makes twice such a power zero. -/
noncomputable def mwNegDegreeEquiv (hsq : ∀ x : F, ∃ y : F, x = y * y) {n : ℤ} (hn : n ≤ -1) :
    MilnorWittKDeg F n ≃+ ZMod 2 :=
  AddEquiv.ofBijective (mwRankMod2 n) ⟨mwRankMod2_injective hsq hn, mwRankMod2_surjective hn⟩

end MilnorWittGradedNegative

end GaloisForLFunctions.HTGeometry
