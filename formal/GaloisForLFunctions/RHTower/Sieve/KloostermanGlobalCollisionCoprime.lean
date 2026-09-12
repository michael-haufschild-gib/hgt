import GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalFrequencyParseval

open scoped BigOperators
open Finset

/-!
# Constant global-frequency collision multiplicity for coprime clocks

For positive stored indices whose clocks `q + 1` are pairwise coprime, Chinese
remainder coordinates recover the unordered pair of endpoints of every signed
two-clock frequency. Fixed orientation is injective, so every global-frequency
fibre has at most the two orientations of one endpoint pair.

Applied to the existing signed Kloosterman global coefficient, this removes the
growing `#Q + 1` collision loss. The final theorem bounds its collision energy
by twice an explicit weighted sum of source residue-collision energy products.
It does not estimate those source residue energies.
-/

namespace RHTower.Sieve

noncomputable section

abbrev KloostermanStoredIndex (Q : Finset ℕ) := {q : ℕ // q ∈ Q}

abbrev kloostermanStoredClock (Q : Finset ℕ) (q : KloostermanStoredIndex Q) : ℕ := q.1 + 1

instance kloostermanStoredClockNeZero (Q : Finset ℕ) (q : KloostermanStoredIndex Q) : NeZero (kloostermanStoredClock Q q) :=
  ⟨by unfold kloostermanStoredClock; omega⟩

theorem kloostermanStoredIndex_pairwise_coprime
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1))) :
    Pairwise (Function.onFun Nat.Coprime (kloostermanStoredClock Q)) := by
  intro q r hqr
  exact hpair q.property r.property (fun h => hqr (Subtype.ext h))

theorem kloostermanProduct_div_storedClock
    (Q : Finset ℕ) (q : KloostermanStoredIndex Q) :
    (∏ i : KloostermanStoredIndex Q, kloostermanStoredClock Q i) / kloostermanStoredClock Q q =
      ∏ i : {i : KloostermanStoredIndex Q // i ≠ q}, kloostermanStoredClock Q i.1 := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne (kloostermanStoredClock Q) q]
  rw [Nat.mul_comm]
  unfold kloostermanStoredClock
  exact Nat.mul_div_left _ (Nat.succ_pos q.1)

theorem kloostermanProduct_div_storedClock_coprime
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1)))
    (q : KloostermanStoredIndex Q) :
    Nat.Coprime ((∏ i : KloostermanStoredIndex Q, kloostermanStoredClock Q i) / kloostermanStoredClock Q q) (kloostermanStoredClock Q q) := by
  rw [kloostermanProduct_div_storedClock]
  rw [Nat.coprime_fintype_prod_left_iff]
  intro i
  exact kloostermanStoredIndex_pairwise_coprime Q hpair (by simpa using i.2)

noncomputable def kloostermanStoredCRT
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1))) :
    ZMod (∏ i : KloostermanStoredIndex Q, kloostermanStoredClock Q i) ≃+* (∀ i : KloostermanStoredIndex Q, ZMod (kloostermanStoredClock Q i)) :=
  ZMod.prodEquivPi (kloostermanStoredClock Q) (kloostermanStoredIndex_pairwise_coprime Q hpair)

def kloostermanProductCrossFrequency
    (Q : Finset ℕ) (q r : KloostermanStoredIndex Q)
    (x : (ZMod (kloostermanStoredClock Q q))ˣ) (y : (ZMod (kloostermanStoredClock Q r))ˣ) :
    ZMod (∏ i : KloostermanStoredIndex Q, kloostermanStoredClock Q i) :=
  (((((∏ i : KloostermanStoredIndex Q, kloostermanStoredClock Q i) / kloostermanStoredClock Q r : ℕ) : ℤ) *
        ((y : ZMod (kloostermanStoredClock Q r)).val : ℤ) -
      (((∏ i : KloostermanStoredIndex Q, kloostermanStoredClock Q i) / kloostermanStoredClock Q q : ℕ) : ℤ) *
        ((x : ZMod (kloostermanStoredClock Q q)).val : ℤ) : ℤ) :
    ZMod (∏ i : KloostermanStoredIndex Q, kloostermanStoredClock Q i))

theorem kloostermanStoredCRT_crossFrequency_apply
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1)))
    (q r i : KloostermanStoredIndex Q)
    (x : (ZMod (kloostermanStoredClock Q q))ˣ) (y : (ZMod (kloostermanStoredClock Q r))ˣ) :
    kloostermanStoredCRT Q hpair (kloostermanProductCrossFrequency Q q r x y) i =
      (((∏ j : KloostermanStoredIndex Q, kloostermanStoredClock Q j) / kloostermanStoredClock Q r : ℕ) : ZMod (kloostermanStoredClock Q i)) *
          ((y : ZMod (kloostermanStoredClock Q r)).val : ZMod (kloostermanStoredClock Q i)) -
      (((∏ j : KloostermanStoredIndex Q, kloostermanStoredClock Q j) / kloostermanStoredClock Q q : ℕ) : ZMod (kloostermanStoredClock Q i)) *
          ((x : ZMod (kloostermanStoredClock Q q)).val : ZMod (kloostermanStoredClock Q i)) := by
  have hiDvd : kloostermanStoredClock Q i ∣ ∏ j : KloostermanStoredIndex Q, kloostermanStoredClock Q j :=
    Finset.dvd_prod_of_mem (kloostermanStoredClock Q) (Finset.mem_univ i)
  unfold kloostermanStoredCRT kloostermanProductCrossFrequency
  rw [ZMod.prodEquivPi_apply]
  rw [ZMod.castHom_apply, ZMod.cast_intCast hiDvd]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast]

theorem kloostermanStoredClock_dvd_product_div_storedClock_of_ne
    (Q : Finset ℕ) (i r : KloostermanStoredIndex Q) (hir : i ≠ r) :
    kloostermanStoredClock Q i ∣ (∏ j : KloostermanStoredIndex Q, kloostermanStoredClock Q j) / kloostermanStoredClock Q r := by
  rw [kloostermanProduct_div_storedClock Q r]
  exact Finset.dvd_prod_of_mem
    (fun j : {j : KloostermanStoredIndex Q // j ≠ r} => kloostermanStoredClock Q j.1)
    (Finset.mem_univ ⟨i, hir⟩)

theorem kloostermanStoredCRT_crossFrequency_apply_eq_zero_of_ne
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1)))
    (q r i : KloostermanStoredIndex Q) (hiq : i ≠ q) (hir : i ≠ r)
    (x : (ZMod (kloostermanStoredClock Q q))ˣ) (y : (ZMod (kloostermanStoredClock Q r))ˣ) :
    kloostermanStoredCRT Q hpair (kloostermanProductCrossFrequency Q q r x y) i = 0 := by
  rw [kloostermanStoredCRT_crossFrequency_apply]
  have hrzero :
      (((∏ j : KloostermanStoredIndex Q, kloostermanStoredClock Q j) / kloostermanStoredClock Q r : ℕ) : ZMod (kloostermanStoredClock Q i)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2
      (kloostermanStoredClock_dvd_product_div_storedClock_of_ne Q i r hir)
  have hqzero :
      (((∏ j : KloostermanStoredIndex Q, kloostermanStoredClock Q j) / kloostermanStoredClock Q q : ℕ) : ZMod (kloostermanStoredClock Q i)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2
      (kloostermanStoredClock_dvd_product_div_storedClock_of_ne Q i q hiq)
  rw [hrzero, hqzero]
  ring

theorem kloostermanStoredCRT_crossFrequency_apply_left_ne_zero
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1)))
    (q r : KloostermanStoredIndex Q) (hqpos : 0 < q.1) (hqr : q ≠ r)
    (x : (ZMod (kloostermanStoredClock Q q))ˣ) (y : (ZMod (kloostermanStoredClock Q r))ˣ) :
    kloostermanStoredCRT Q hpair (kloostermanProductCrossFrequency Q q r x y) q ≠ 0 := by
  letI : NeZero (kloostermanStoredClock Q q) := ⟨by unfold kloostermanStoredClock; omega⟩
  letI : Nontrivial (ZMod (kloostermanStoredClock Q q)) :=
    ZMod.nontrivial_iff.mpr (by unfold kloostermanStoredClock; omega)
  rw [kloostermanStoredCRT_crossFrequency_apply]
  have hrzero :
      (((∏ j : KloostermanStoredIndex Q, kloostermanStoredClock Q j) / kloostermanStoredClock Q r : ℕ) : ZMod (kloostermanStoredClock Q q)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2
      (kloostermanStoredClock_dvd_product_div_storedClock_of_ne Q q r hqr)
  rw [hrzero, zero_mul, zero_sub]
  apply neg_ne_zero.mpr
  have hcoeffUnit : IsUnit
      (((∏ j : KloostermanStoredIndex Q, kloostermanStoredClock Q j) / kloostermanStoredClock Q q : ℕ) : ZMod (kloostermanStoredClock Q q)) :=
    (ZMod.isUnit_iff_coprime _ _).2 (kloostermanProduct_div_storedClock_coprime Q hpair q)
  have hxUnit : IsUnit
      (((x : ZMod (kloostermanStoredClock Q q)).val : ℕ) : ZMod (kloostermanStoredClock Q q)) := by
    rw [ZMod.natCast_zmod_val]
    exact x.isUnit
  exact (hcoeffUnit.mul hxUnit).ne_zero

theorem kloostermanStoredCRT_crossFrequency_apply_right_ne_zero
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1)))
    (q r : KloostermanStoredIndex Q) (hrpos : 0 < r.1) (hqr : q ≠ r)
    (x : (ZMod (kloostermanStoredClock Q q))ˣ) (y : (ZMod (kloostermanStoredClock Q r))ˣ) :
    kloostermanStoredCRT Q hpair (kloostermanProductCrossFrequency Q q r x y) r ≠ 0 := by
  letI : NeZero (kloostermanStoredClock Q r) := ⟨by unfold kloostermanStoredClock; omega⟩
  letI : Nontrivial (ZMod (kloostermanStoredClock Q r)) :=
    ZMod.nontrivial_iff.mpr (by unfold kloostermanStoredClock; omega)
  rw [kloostermanStoredCRT_crossFrequency_apply]
  have hqzero :
      (((∏ j : KloostermanStoredIndex Q, kloostermanStoredClock Q j) / kloostermanStoredClock Q q : ℕ) : ZMod (kloostermanStoredClock Q r)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2
      (kloostermanStoredClock_dvd_product_div_storedClock_of_ne Q r q (Ne.symm hqr))
  rw [hqzero, zero_mul, sub_zero]
  have hcoeffUnit : IsUnit
      (((∏ j : KloostermanStoredIndex Q, kloostermanStoredClock Q j) / kloostermanStoredClock Q r : ℕ) : ZMod (kloostermanStoredClock Q r)) :=
    (ZMod.isUnit_iff_coprime _ _).2 (kloostermanProduct_div_storedClock_coprime Q hpair r)
  have hyUnit : IsUnit
      (((y : ZMod (kloostermanStoredClock Q r)).val : ℕ) : ZMod (kloostermanStoredClock Q r)) := by
    rw [ZMod.natCast_zmod_val]
    exact y.isUnit
  exact (hcoeffUnit.mul hyUnit).ne_zero

theorem kloostermanProductCrossFrequency_eq_imp_endpoint_pairs
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1)))
    (hpos : ∀ i : KloostermanStoredIndex Q, 0 < i.1)
    (q r q' r' : KloostermanStoredIndex Q) (hqr : q ≠ r)
    (x : (ZMod (kloostermanStoredClock Q q))ˣ) (y : (ZMod (kloostermanStoredClock Q r))ˣ)
    (x' : (ZMod (kloostermanStoredClock Q q'))ˣ) (y' : (ZMod (kloostermanStoredClock Q r'))ˣ)
    (hfreq : kloostermanProductCrossFrequency Q q r x y = kloostermanProductCrossFrequency Q q' r' x' y') :
    (q' = q ∧ r' = r) ∨ (q' = r ∧ r' = q) := by
  have hq : q = q' ∨ q = r' := by
    by_contra h
    push Not at h
    have hleft := kloostermanStoredCRT_crossFrequency_apply_left_ne_zero
      Q hpair q r (hpos q) hqr x y
    have hright := kloostermanStoredCRT_crossFrequency_apply_eq_zero_of_ne
      Q hpair q' r' q h.1 h.2 x' y'
    exact hleft ((congrArg (fun z => kloostermanStoredCRT Q hpair z q) hfreq).trans hright)
  have hr : r = q' ∨ r = r' := by
    by_contra h
    push Not at h
    have hleft := kloostermanStoredCRT_crossFrequency_apply_right_ne_zero
      Q hpair q r (hpos r) hqr x y
    have hright := kloostermanStoredCRT_crossFrequency_apply_eq_zero_of_ne
      Q hpair q' r' r h.1 h.2 x' y'
    exact hleft ((congrArg (fun z => kloostermanStoredCRT Q hpair z r) hfreq).trans hright)
  rcases hq with hqq' | hqr'Eq
  · rcases hr with hrq' | hrr'
    · exact False.elim (hqr (hqq'.trans hrq'.symm))
    · exact Or.inl ⟨hqq'.symm, hrr'.symm⟩
  · rcases hr with hrq' | hrr'
    · exact Or.inr ⟨hrq'.symm, hqr'Eq.symm⟩
    · exact False.elim (hqr (hqr'Eq.trans hrr'.symm))

theorem kloostermanGlobalPeriod_eq_productStoredClock
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1))) :
    RHTower.Sieve.kloostermanGlobalPeriod Q = ∏ i : KloostermanStoredIndex Q, kloostermanStoredClock Q i := by
  calc
    RHTower.Sieve.kloostermanGlobalPeriod Q = ∏ q ∈ Q, (q + 1) := by
      exact Finset.lcm_eq_prod hpair
    _ = ∏ i : KloostermanStoredIndex Q, kloostermanStoredClock Q i := by
      exact (Finset.prod_coe_sort Q (fun q => q + 1)).symm

theorem kloostermanGlobalFrequency_transport_eq_productCrossFrequency
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1)))
    (q r : ℕ) (hq : q ∈ Q) (hr : r ∈ Q)
    (x : (ZMod (q + 1))ˣ) (y : (ZMod (r + 1))ˣ) :
    ZMod.ringEquivCongr (kloostermanGlobalPeriod_eq_productStoredClock Q hpair)
        (RHTower.Sieve.kloostermanGlobalCrossPhaseFrequency Q q r x y) =
      kloostermanProductCrossFrequency Q ⟨q, hq⟩ ⟨r, hr⟩ x y := by
  unfold RHTower.Sieve.kloostermanGlobalCrossPhaseFrequency kloostermanProductCrossFrequency kloostermanStoredClock
  rw [map_intCast]
  rw [kloostermanGlobalPeriod_eq_productStoredClock Q hpair]

theorem kloostermanGlobalCrossFrequency_eq_imp_endpoint_pairs
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1)))
    (hpos : ∀ q ∈ Q, 0 < q)
    (q r q' r' : ℕ) (hq : q ∈ Q) (hr : r ∈ Q)
    (hq' : q' ∈ Q) (hr' : r' ∈ Q) (hqr : q ≠ r)
    (x : (ZMod (q + 1))ˣ) (y : (ZMod (r + 1))ˣ)
    (x' : (ZMod (q' + 1))ˣ) (y' : (ZMod (r' + 1))ˣ)
    (hfreq : RHTower.Sieve.kloostermanGlobalCrossPhaseFrequency Q q r x y =
      RHTower.Sieve.kloostermanGlobalCrossPhaseFrequency Q q' r' x' y') :
    (q' = q ∧ r' = r) ∨ (q' = r ∧ r' = q) := by
  have ht := congrArg (ZMod.ringEquivCongr (kloostermanGlobalPeriod_eq_productStoredClock Q hpair)) hfreq
  rw [kloostermanGlobalFrequency_transport_eq_productCrossFrequency Q hpair q r hq hr x y,
    kloostermanGlobalFrequency_transport_eq_productCrossFrequency Q hpair q' r' hq' hr' x' y'] at ht
  have hend := kloostermanProductCrossFrequency_eq_imp_endpoint_pairs Q hpair
    (fun i => hpos i.1 i.2) ⟨q, hq⟩ ⟨r, hr⟩ ⟨q', hq'⟩ ⟨r', hr'⟩
      (fun h => hqr (congrArg Subtype.val h)) x y x' y' ht
  simpa only [Subtype.mk.injEq] using hend

theorem kloostermanProductCrossFrequency_fixed_injective
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1)))
    (q r : KloostermanStoredIndex Q) (hqr : q ≠ r) :
    Function.Injective (fun p :
        (ZMod (kloostermanStoredClock Q q))ˣ × (ZMod (kloostermanStoredClock Q r))ˣ =>
      kloostermanProductCrossFrequency Q q r p.1 p.2) := by
  letI : NeZero (kloostermanStoredClock Q q) := ⟨by unfold kloostermanStoredClock; omega⟩
  letI : NeZero (kloostermanStoredClock Q r) := ⟨by unfold kloostermanStoredClock; omega⟩
  intro p p' hfreq
  have hqcoord := congrArg (fun z => kloostermanStoredCRT Q hpair z q) hfreq
  rw [kloostermanStoredCRT_crossFrequency_apply, kloostermanStoredCRT_crossFrequency_apply] at hqcoord
  have hrzero :
      (((∏ j : KloostermanStoredIndex Q, kloostermanStoredClock Q j) / kloostermanStoredClock Q r : ℕ) : ZMod (kloostermanStoredClock Q q)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2
      (kloostermanStoredClock_dvd_product_div_storedClock_of_ne Q q r hqr)
  rw [hrzero, zero_mul, zero_sub, zero_mul, zero_sub] at hqcoord
  have hcoeffQ : IsUnit
      (((∏ j : KloostermanStoredIndex Q, kloostermanStoredClock Q j) / kloostermanStoredClock Q q : ℕ) : ZMod (kloostermanStoredClock Q q)) :=
    (ZMod.isUnit_iff_coprime _ _).2 (kloostermanProduct_div_storedClock_coprime Q hpair q)
  have hxCast :
      (((p.1 : ZMod (kloostermanStoredClock Q q)).val : ℕ) : ZMod (kloostermanStoredClock Q q)) =
        (((p'.1 : ZMod (kloostermanStoredClock Q q)).val : ℕ) : ZMod (kloostermanStoredClock Q q)) :=
    hcoeffQ.mul_left_cancel (neg_inj.mp hqcoord)
  have hx : p.1 = p'.1 := by
    apply Units.ext
    simpa only [ZMod.natCast_zmod_val] using hxCast
  have hrcoord := congrArg (fun z => kloostermanStoredCRT Q hpair z r) hfreq
  rw [kloostermanStoredCRT_crossFrequency_apply, kloostermanStoredCRT_crossFrequency_apply] at hrcoord
  have hqzero :
      (((∏ j : KloostermanStoredIndex Q, kloostermanStoredClock Q j) / kloostermanStoredClock Q q : ℕ) : ZMod (kloostermanStoredClock Q r)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2
      (kloostermanStoredClock_dvd_product_div_storedClock_of_ne Q r q (Ne.symm hqr))
  rw [hqzero, zero_mul, sub_zero, zero_mul, sub_zero] at hrcoord
  have hcoeffR : IsUnit
      (((∏ j : KloostermanStoredIndex Q, kloostermanStoredClock Q j) / kloostermanStoredClock Q r : ℕ) : ZMod (kloostermanStoredClock Q r)) :=
    (ZMod.isUnit_iff_coprime _ _).2 (kloostermanProduct_div_storedClock_coprime Q hpair r)
  have hyCast :
      (((p.2 : ZMod (kloostermanStoredClock Q r)).val : ℕ) : ZMod (kloostermanStoredClock Q r)) =
        (((p'.2 : ZMod (kloostermanStoredClock Q r)).val : ℕ) : ZMod (kloostermanStoredClock Q r)) :=
    hcoeffR.mul_left_cancel hrcoord
  have hy : p.2 = p'.2 := by
    apply Units.ext
    simpa only [ZMod.natCast_zmod_val] using hyCast
  exact Prod.ext hx hy

abbrev KloostermanGlobalCrossTuple (Q : Finset ℕ) :=
  Σ q : KloostermanStoredIndex Q, Σ r : KloostermanStoredIndex Q,
    {_xy : (ZMod (kloostermanStoredClock Q q))ˣ × (ZMod (kloostermanStoredClock Q r))ˣ // q ≠ r}

instance kloostermanProductStoredClockNeZero (Q : Finset ℕ) :
    NeZero (∏ i : KloostermanStoredIndex Q, kloostermanStoredClock Q i) := by
  refine ⟨Finset.prod_ne_zero_iff.mpr ?_⟩
  intro i hi
  unfold kloostermanStoredClock
  omega

def kloostermanProductCrossTupleFrequency (Q : Finset ℕ) (p : KloostermanGlobalCrossTuple Q) :
    ZMod (∏ i : KloostermanStoredIndex Q, kloostermanStoredClock Q i) :=
  kloostermanProductCrossFrequency Q p.1 p.2.1 p.2.2.1.1 p.2.2.1.2

theorem kloostermanGlobalCrossTuple_eq_of_endpoints_eq
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1)))
    (a b : KloostermanGlobalCrossTuple Q)
    (hq : b.1 = a.1) (hr : b.2.1 = a.2.1)
    (hfreq : kloostermanProductCrossTupleFrequency Q b = kloostermanProductCrossTupleFrequency Q a) :
    b = a := by
  rcases a with ⟨q, r, ⟨⟨x, y⟩, hqr⟩⟩
  rcases b with ⟨q', r', ⟨⟨x', y'⟩, hqr'⟩⟩
  dsimp only at hq hr hfreq ⊢
  subst q'
  subst r'
  change kloostermanProductCrossFrequency Q q r x' y' = kloostermanProductCrossFrequency Q q r x y at hfreq
  have hxy : (x', y') = (x, y) :=
    kloostermanProductCrossFrequency_fixed_injective Q hpair q r hqr hfreq
  cases hxy
  rfl

theorem card_filter_kloostermanProductCrossTupleFrequency_le_two
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1)))
    (hpos : ∀ i : KloostermanStoredIndex Q, 0 < i.1)
    (p : KloostermanGlobalCrossTuple Q) :
    ((Finset.univ.filter fun u : KloostermanGlobalCrossTuple Q =>
      kloostermanProductCrossTupleFrequency Q p = kloostermanProductCrossTupleFrequency Q u).card : ℕ) ≤ 2 := by
  classical
  let S := Finset.univ.filter fun u : KloostermanGlobalCrossTuple Q =>
    kloostermanProductCrossTupleFrequency Q p = kloostermanProductCrossTupleFrequency Q u
  let orientation : {u // u ∈ S} → Bool := fun u => decide (u.1.1 = p.1)
  have hinj : Function.Injective orientation := by
    intro u v huv
    have huFreq : kloostermanProductCrossTupleFrequency Q p = kloostermanProductCrossTupleFrequency Q u.1 :=
      (Finset.mem_filter.mp u.2).2
    have hvFreq : kloostermanProductCrossTupleFrequency Q p = kloostermanProductCrossTupleFrequency Q v.1 :=
      (Finset.mem_filter.mp v.2).2
    have huEnds := kloostermanProductCrossFrequency_eq_imp_endpoint_pairs Q hpair hpos
      p.1 p.2.1 u.1.1 u.1.2.1 p.2.2.2
      p.2.2.1.1 p.2.2.1.2 u.1.2.2.1.1 u.1.2.2.1.2 huFreq
    have hvEnds := kloostermanProductCrossFrequency_eq_imp_endpoint_pairs Q hpair hpos
      p.1 p.2.1 v.1.1 v.1.2.1 p.2.2.2
      p.2.2.1.1 p.2.2.1.2 v.1.2.2.1.1 v.1.2.2.1.2 hvFreq
    apply Subtype.ext
    rcases huEnds with huSame | huRev <;> rcases hvEnds with hvSame | hvRev
    · exact kloostermanGlobalCrossTuple_eq_of_endpoints_eq Q hpair v.1 u.1
        (huSame.1.trans hvSame.1.symm) (huSame.2.trans hvSame.2.symm)
        (huFreq.symm.trans hvFreq)
    · exfalso
      have hpne : p.1 ≠ p.2.1 := p.2.2.2
      simp [orientation, huSame.1, hvRev.1] at huv
      exact hpne huv.symm
    · exfalso
      have hpne : p.1 ≠ p.2.1 := p.2.2.2
      simp [orientation, huRev.1, hvSame.1] at huv
      exact hpne huv.symm
    · exact kloostermanGlobalCrossTuple_eq_of_endpoints_eq Q hpair v.1 u.1
        (huRev.1.trans hvRev.1.symm) (huRev.2.trans hvRev.2.symm)
        (huFreq.symm.trans hvFreq)
  have hcard := Fintype.card_le_of_injective orientation hinj
  simpa only [S, Fintype.card_coe, Fintype.card_bool] using hcard

private theorem normSq_finset_sum_le_card_mul_sum_normSq
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ι → ℂ) :
    Complex.normSq (∑ i ∈ S, a i) ≤
      (S.card : ℝ) * ∑ i ∈ S, Complex.normSq (a i) := by
  rw [← Complex.sq_norm]
  have htri : ‖∑ i ∈ S, a i‖ ≤ ∑ i ∈ S, ‖a i‖ := norm_sum_le _ _
  have hsum0 : 0 ≤ ∑ i ∈ S, ‖a i‖ := by positivity
  calc
    ‖∑ i ∈ S, a i‖ ^ 2 ≤ (∑ i ∈ S, ‖a i‖) ^ 2 := by
      nlinarith [norm_nonneg (∑ i ∈ S, a i)]
    _ ≤ (S.card : ℝ) * ∑ i ∈ S, Complex.normSq (a i) := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq S
        (fun _ => (1 : ℝ)) (fun i => ‖a i‖)
      simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul,
        Complex.sq_norm, Nat.cast_ofNat, mul_one] using h

theorem finiteFrequencyCollisionEnergy_le_of_fiber_card
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ν : α → β) (a : α → ℂ) {N : ℝ}
    (hN : ∀ p : α,
      (((Finset.univ.filter fun q : α => ν p = ν q).card : ℕ) : ℝ) ≤ N) :
    (∑ z : β, Complex.normSq (∑ p : α, if ν p = z then a p else 0)) ≤
      N * ∑ p : α, Complex.normSq (a p) := by
  classical
  have hpoint : ∀ z : β,
      Complex.normSq (∑ p : α, if ν p = z then a p else 0) ≤
        N * ∑ p : α, if ν p = z then Complex.normSq (a p) else 0 := by
    intro z
    let S := Finset.univ.filter fun p : α => ν p = z
    by_cases hS : S.Nonempty
    · obtain ⟨p, hp⟩ := hS
      have hpz : ν p = z := (Finset.mem_filter.mp hp).2
      have hfilter : (Finset.univ.filter fun q : α => ν p = ν q) = S := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
        rw [hpz]
        exact eq_comm
      have hcard : (S.card : ℝ) ≤ N := by
        rw [← hfilter]
        exact hN p
      rw [← Finset.sum_filter, ← Finset.sum_filter]
      have hbase := normSq_finset_sum_le_card_mul_sum_normSq S a
      exact hbase.trans (mul_le_mul_of_nonneg_right hcard
        (Finset.sum_nonneg fun i hi => Complex.normSq_nonneg _))
    · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      rw [← Finset.sum_filter, ← Finset.sum_filter, show
        (Finset.univ.filter fun p : α => ν p = z) = S by rfl, hEmpty]
      simp
  calc
    (∑ z : β, Complex.normSq (∑ p : α, if ν p = z then a p else 0)) ≤
        ∑ z : β, N * ∑ p : α,
          if ν p = z then Complex.normSq (a p) else 0 :=
      Finset.sum_le_sum fun z _ => hpoint z
    _ = N * ∑ p : α, Complex.normSq (a p) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      apply congrArg (fun x : ℝ => N * x)
      apply Fintype.sum_congr
      intro p
      simp

theorem kloostermanProductCrossTupleCollisionEnergy_le_two
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1)))
    (hpos : ∀ i : KloostermanStoredIndex Q, 0 < i.1)
    (a : KloostermanGlobalCrossTuple Q → ℂ) :
    (∑ z : ZMod (∏ i : KloostermanStoredIndex Q, kloostermanStoredClock Q i),
      Complex.normSq
        (∑ p : KloostermanGlobalCrossTuple Q, if kloostermanProductCrossTupleFrequency Q p = z then a p else 0)) ≤
      2 * ∑ p : KloostermanGlobalCrossTuple Q, Complex.normSq (a p) := by
  apply finiteFrequencyCollisionEnergy_le_of_fiber_card (kloostermanProductCrossTupleFrequency Q) a
  intro p
  exact_mod_cast card_filter_kloostermanProductCrossTupleFrequency_le_two Q hpair hpos p

def kloostermanLiteralCrossTupleFrequency (Q : Finset ℕ) (p : KloostermanGlobalCrossTuple Q) :
    ZMod (RHTower.Sieve.kloostermanGlobalPeriod Q) :=
  RHTower.Sieve.kloostermanGlobalCrossPhaseFrequency Q p.1.1 p.2.1.1
    p.2.2.1.1 p.2.2.1.2

theorem kloostermanLiteralCrossTupleFrequency_eq_iff
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1)))
    (p u : KloostermanGlobalCrossTuple Q) :
    kloostermanLiteralCrossTupleFrequency Q p = kloostermanLiteralCrossTupleFrequency Q u ↔
      kloostermanProductCrossTupleFrequency Q p = kloostermanProductCrossTupleFrequency Q u := by
  let e := ZMod.ringEquivCongr (kloostermanGlobalPeriod_eq_productStoredClock Q hpair)
  have hp : e (kloostermanLiteralCrossTupleFrequency Q p) = kloostermanProductCrossTupleFrequency Q p := by
    exact kloostermanGlobalFrequency_transport_eq_productCrossFrequency Q hpair p.1.1 p.2.1.1
      p.1.2 p.2.1.2 p.2.2.1.1 p.2.2.1.2
  have hu : e (kloostermanLiteralCrossTupleFrequency Q u) = kloostermanProductCrossTupleFrequency Q u := by
    exact kloostermanGlobalFrequency_transport_eq_productCrossFrequency Q hpair u.1.1 u.2.1.1
      u.1.2 u.2.1.2 u.2.2.1.1 u.2.2.1.2
  constructor
  · intro h
    rw [← hp, ← hu]
    exact congrArg e h
  · intro h
    apply e.injective
    rw [hp, hu]
    exact h

theorem card_filter_kloostermanLiteralCrossTupleFrequency_le_two
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1)))
    (hpos : ∀ i : KloostermanStoredIndex Q, 0 < i.1)
    (p : KloostermanGlobalCrossTuple Q) :
    ((Finset.univ.filter fun u : KloostermanGlobalCrossTuple Q =>
      kloostermanLiteralCrossTupleFrequency Q p = kloostermanLiteralCrossTupleFrequency Q u).card : ℕ) ≤ 2 := by
  have hfilter :
      (Finset.univ.filter fun u : KloostermanGlobalCrossTuple Q =>
        kloostermanLiteralCrossTupleFrequency Q p = kloostermanLiteralCrossTupleFrequency Q u) =
      Finset.univ.filter fun u : KloostermanGlobalCrossTuple Q =>
        kloostermanProductCrossTupleFrequency Q p = kloostermanProductCrossTupleFrequency Q u := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact kloostermanLiteralCrossTupleFrequency_eq_iff Q hpair p u
  rw [hfilter]
  exact card_filter_kloostermanProductCrossTupleFrequency_le_two Q hpair hpos p

theorem kloostermanLiteralCrossTupleCollisionEnergy_le_two
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1)))
    (hpos : ∀ i : KloostermanStoredIndex Q, 0 < i.1)
    (a : KloostermanGlobalCrossTuple Q → ℂ) :
    (∑ z : ZMod (RHTower.Sieve.kloostermanGlobalPeriod Q),
      Complex.normSq
        (∑ p : KloostermanGlobalCrossTuple Q,
          if kloostermanLiteralCrossTupleFrequency Q p = z then a p else 0)) ≤
      2 * ∑ p : KloostermanGlobalCrossTuple Q, Complex.normSq (a p) := by
  apply finiteFrequencyCollisionEnergy_le_of_fiber_card (kloostermanLiteralCrossTupleFrequency Q) a
  intro p
  exact_mod_cast card_filter_kloostermanLiteralCrossTupleFrequency_le_two Q hpair hpos p

def kloostermanGlobalCrossTupleCoefficient
    (Q : Finset ℕ) (w : ℕ → ℂ) (B : Finset ℕ) (b : ℕ → ℂ)
    (p : KloostermanGlobalCrossTuple Q) : ℂ :=
  star (w p.1.1) * w p.2.1.1 *
    (star (RHTower.Sieve.kloostermanSourceFourier
      (kloostermanStoredClock Q p.1) B b p.2.2.1.1) *
      RHTower.Sieve.kloostermanSourceFourier
        (kloostermanStoredClock Q p.2.1) B b p.2.2.1.2)

private theorem sum_proof_subtype_eq_if
    {α : Type*} [Fintype α] [DecidableEq α]
    {R : Type*} [AddCommMonoid R]
    {P : Prop} [Decidable P]
    (F : {_x : α // P} → R) (G : α → R)
    (hFG : ∀ _x h, F ⟨_x, h⟩ = G _x) :
    (∑ u : {_x : α // P}, F u) = if P then ∑ _x : α, G _x else 0 := by
  classical
  by_cases hP : P
  · rw [if_pos hP]
    calc
      (∑ u : {x : α // P}, F u) = ∑ u : {x : α // P}, G u.1 := by
        apply Fintype.sum_congr
        intro u
        exact hFG u.1 u.2
      _ = ∑ x : α, G x := by
        exact (Finset.sum_subtype (p := fun _ : α => P) Finset.univ
          (fun _ => by simp [hP]) G).symm
  · rw [if_neg hP]
    haveI : IsEmpty {x : α // P} := ⟨fun u => hP u.2⟩
    simp

private theorem sum_kloostermanStoredIndex_if_ne_eq_sum_erase
    {R : Type*} [AddCommMonoid R]
    (Q : Finset ℕ) (q : KloostermanStoredIndex Q) (f : ℕ → R) :
    (∑ r : KloostermanStoredIndex Q, if q.1 ≠ r.1 then f r.1 else 0) =
      ∑ r ∈ Q.erase q.1, f r := by
  calc
    (∑ r : KloostermanStoredIndex Q, if q.1 ≠ r.1 then f r.1 else 0) =
        ∑ r ∈ Q, if q.1 ≠ r then f r else 0 := by
      exact (Finset.sum_subtype Q (fun _ => Iff.rfl)
        (fun r => if q.1 ≠ r then f r else 0)).symm
    _ = ∑ r ∈ Q.erase q.1, f r := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext r
        simp [eq_comm, and_comm]
      · intro r hr
        rfl

theorem kloostermanGlobalFrequencyCoefficient_eq_crossTupleSum
    (Q : Finset ℕ) (w : ℕ → ℂ) (B : Finset ℕ) (b : ℕ → ℂ)
    (z : ZMod (RHTower.Sieve.kloostermanGlobalPeriod Q)) :
    RHTower.Sieve.kloostermanGlobalFrequencyCoefficient Q w B b z =
      ∑ p : KloostermanGlobalCrossTuple Q,
        if kloostermanLiteralCrossTupleFrequency Q p = z then
          kloostermanGlobalCrossTupleCoefficient Q w B b p else 0 := by
  classical
  unfold RHTower.Sieve.kloostermanGlobalFrequencyCoefficient
    RHTower.Sieve.kloostermanGlobalPairFrequencyCoefficient
  symm
  simp only [Fintype.sum_sigma]
  calc
    (∑ q : KloostermanStoredIndex Q, ∑ r : KloostermanStoredIndex Q,
        ∑ u : {xy : (ZMod (kloostermanStoredClock Q q))ˣ × (ZMod (kloostermanStoredClock Q r))ˣ // q ≠ r},
          if kloostermanLiteralCrossTupleFrequency Q ⟨q, r, u⟩ = z then
            kloostermanGlobalCrossTupleCoefficient Q w B b ⟨q, r, u⟩ else 0) =
      ∑ q : KloostermanStoredIndex Q, ∑ r : KloostermanStoredIndex Q,
        if q.1 ≠ r.1 then
          ∑ x : (ZMod (kloostermanStoredClock Q q))ˣ, ∑ y : (ZMod (kloostermanStoredClock Q r))ˣ,
            if RHTower.Sieve.kloostermanGlobalCrossPhaseFrequency
                Q q.1 r.1 x y = z then
              star (w q.1) * w r.1 *
                (star (RHTower.Sieve.kloostermanSourceFourier
                  (kloostermanStoredClock Q q) B b x) *
                  RHTower.Sieve.kloostermanSourceFourier
                    (kloostermanStoredClock Q r) B b y)
            else 0
        else 0 := by
      apply Fintype.sum_congr
      intro q
      apply Fintype.sum_congr
      intro r
      calc
        (∑ u : {xy : (ZMod (kloostermanStoredClock Q q))ˣ × (ZMod (kloostermanStoredClock Q r))ˣ // q ≠ r},
            if kloostermanLiteralCrossTupleFrequency Q ⟨q, r, u⟩ = z then
              kloostermanGlobalCrossTupleCoefficient Q w B b ⟨q, r, u⟩ else 0) =
            if q ≠ r then
              ∑ xy : (ZMod (kloostermanStoredClock Q q))ˣ × (ZMod (kloostermanStoredClock Q r))ˣ,
                if RHTower.Sieve.kloostermanGlobalCrossPhaseFrequency
                    Q q.1 r.1 xy.1 xy.2 = z then
                  star (w q.1) * w r.1 *
                    (star (RHTower.Sieve.kloostermanSourceFourier
                      (kloostermanStoredClock Q q) B b xy.1) *
                      RHTower.Sieve.kloostermanSourceFourier
                        (kloostermanStoredClock Q r) B b xy.2)
                else 0
            else 0 := by
          exact sum_proof_subtype_eq_if
            (fun u =>
              if kloostermanLiteralCrossTupleFrequency Q ⟨q, r, u⟩ = z then
                kloostermanGlobalCrossTupleCoefficient Q w B b ⟨q, r, u⟩ else 0)
            (fun xy =>
              if RHTower.Sieve.kloostermanGlobalCrossPhaseFrequency
                  Q q.1 r.1 xy.1 xy.2 = z then
                star (w q.1) * w r.1 *
                  (star (RHTower.Sieve.kloostermanSourceFourier
                    (kloostermanStoredClock Q q) B b xy.1) *
                    RHTower.Sieve.kloostermanSourceFourier
                      (kloostermanStoredClock Q r) B b xy.2)
              else 0)
            (by intro xy hqr; rfl)
        _ = if q.1 ≠ r.1 then
              ∑ x : (ZMod (kloostermanStoredClock Q q))ˣ, ∑ y : (ZMod (kloostermanStoredClock Q r))ˣ,
                if RHTower.Sieve.kloostermanGlobalCrossPhaseFrequency
                    Q q.1 r.1 x y = z then
                  star (w q.1) * w r.1 *
                    (star (RHTower.Sieve.kloostermanSourceFourier
                      (kloostermanStoredClock Q q) B b x) *
                      RHTower.Sieve.kloostermanSourceFourier
                        (kloostermanStoredClock Q r) B b y)
                else 0
            else 0 := by
          by_cases hqr : q = r
          · subst r
            simp
          · have hval : q.1 ≠ r.1 := fun h => hqr (Subtype.ext h)
            simp only [if_pos hqr, if_pos hval]
            exact Fintype.sum_prod_type _
    _ = ∑ q : KloostermanStoredIndex Q, ∑ r ∈ Q.erase q.1,
          ∑ x : (ZMod (q.1 + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
            if RHTower.Sieve.kloostermanGlobalCrossPhaseFrequency
                Q q.1 r x y = z then
              star (w q.1) * w r *
                (star (RHTower.Sieve.kloostermanSourceFourier
                  (q.1 + 1) B b x) *
                  RHTower.Sieve.kloostermanSourceFourier (r + 1) B b y)
            else 0 := by
      apply Fintype.sum_congr
      intro q
      let f : ℕ → ℂ := fun r =>
        ∑ x : (ZMod (q.1 + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
          if RHTower.Sieve.kloostermanGlobalCrossPhaseFrequency
              Q q.1 r x y = z then
            star (w q.1) * w r *
              (star (RHTower.Sieve.kloostermanSourceFourier
                (q.1 + 1) B b x) *
                RHTower.Sieve.kloostermanSourceFourier (r + 1) B b y)
          else 0
      change (∑ r : KloostermanStoredIndex Q, if q.1 ≠ r.1 then f r.1 else 0) =
        ∑ r ∈ Q.erase q.1, f r
      exact sum_kloostermanStoredIndex_if_ne_eq_sum_erase Q q f
    _ = ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
            if RHTower.Sieve.kloostermanGlobalCrossPhaseFrequency Q q r x y = z then
              star (w q) * w r *
                (star (RHTower.Sieve.kloostermanSourceFourier (q + 1) B b x) *
                  RHTower.Sieve.kloostermanSourceFourier (r + 1) B b y)
            else 0 := by
      exact (Finset.sum_subtype Q (fun _ => Iff.rfl) (fun q =>
        ∑ r ∈ Q.erase q,
          ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
            if RHTower.Sieve.kloostermanGlobalCrossPhaseFrequency Q q r x y = z then
              star (w q) * w r *
                (star (RHTower.Sieve.kloostermanSourceFourier (q + 1) B b x) *
                  RHTower.Sieve.kloostermanSourceFourier (r + 1) B b y)
            else 0)).symm

theorem kloostermanGlobalFrequencyCollisionEnergy_le_two_crossTuple
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1)))
    (hpos : ∀ q ∈ Q, 0 < q)
    (w : ℕ → ℂ) (B : Finset ℕ) (b : ℕ → ℂ) :
    RHTower.Sieve.kloostermanGlobalFrequencyCollisionEnergy Q w B b ≤
      2 * ∑ p : KloostermanGlobalCrossTuple Q,
        Complex.normSq (kloostermanGlobalCrossTupleCoefficient Q w B b p) := by
  unfold RHTower.Sieve.kloostermanGlobalFrequencyCollisionEnergy
  simp_rw [kloostermanGlobalFrequencyCoefficient_eq_crossTupleSum]
  have h := kloostermanLiteralCrossTupleCollisionEnergy_le_two Q hpair
    (fun q => hpos q.1 q.2) (kloostermanGlobalCrossTupleCoefficient Q w B b)
  simpa only [Complex.sq_norm] using h

private theorem sum_kloostermanGlobalCrossTuple_eq_nested
    (Q : Finset ℕ)
    (F : ∀ q r : ℕ, (ZMod (q + 1))ˣ → (ZMod (r + 1))ˣ → ℝ) :
    (∑ p : KloostermanGlobalCrossTuple Q,
      F p.1.1 p.2.1.1 p.2.2.1.1 p.2.2.1.2) =
      ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ, F q r x y := by
  classical
  simp only [Fintype.sum_sigma]
  calc
    (∑ q : KloostermanStoredIndex Q, ∑ r : KloostermanStoredIndex Q,
        ∑ u : {xy : (ZMod (kloostermanStoredClock Q q))ˣ × (ZMod (kloostermanStoredClock Q r))ˣ // q ≠ r},
          F q.1 r.1 u.1.1 u.1.2) =
      ∑ q : KloostermanStoredIndex Q, ∑ r : KloostermanStoredIndex Q,
        if q.1 ≠ r.1 then
          ∑ x : (ZMod (kloostermanStoredClock Q q))ˣ,
            ∑ y : (ZMod (kloostermanStoredClock Q r))ˣ, F q.1 r.1 x y
        else 0 := by
      apply Fintype.sum_congr
      intro q
      apply Fintype.sum_congr
      intro r
      calc
        (∑ u : {xy : (ZMod (kloostermanStoredClock Q q))ˣ × (ZMod (kloostermanStoredClock Q r))ˣ // q ≠ r},
            F q.1 r.1 u.1.1 u.1.2) =
          if q ≠ r then
            ∑ xy : (ZMod (kloostermanStoredClock Q q))ˣ × (ZMod (kloostermanStoredClock Q r))ˣ,
              F q.1 r.1 xy.1 xy.2
          else 0 := by
            exact sum_proof_subtype_eq_if
              (fun u : {xy : (ZMod (kloostermanStoredClock Q q))ˣ ×
                  (ZMod (kloostermanStoredClock Q r))ˣ // q ≠ r} =>
                F q.1 r.1 u.1.1 u.1.2)
              (fun xy : (ZMod (kloostermanStoredClock Q q))ˣ × (ZMod (kloostermanStoredClock Q r))ˣ =>
                F q.1 r.1 xy.1 xy.2)
              (by intro xy hqr; rfl)
        _ = if q.1 ≠ r.1 then
            ∑ x : (ZMod (kloostermanStoredClock Q q))ˣ,
              ∑ y : (ZMod (kloostermanStoredClock Q r))ˣ, F q.1 r.1 x y
          else 0 := by
            by_cases hqr : q = r
            · subst r
              simp
            · have hval : q.1 ≠ r.1 := fun h => hqr (Subtype.ext h)
              simp only [if_pos hqr, if_pos hval]
              exact Fintype.sum_prod_type _
    _ = ∑ q : KloostermanStoredIndex Q, ∑ r ∈ Q.erase q.1,
          ∑ x : (ZMod (q.1 + 1))ˣ,
            ∑ y : (ZMod (r + 1))ˣ, F q.1 r x y := by
      apply Fintype.sum_congr
      intro q
      let f : ℕ → ℝ := fun r =>
        ∑ x : (ZMod (q.1 + 1))ˣ,
          ∑ y : (ZMod (r + 1))ˣ, F q.1 r x y
      change (∑ r : KloostermanStoredIndex Q, if q.1 ≠ r.1 then f r.1 else 0) =
        ∑ r ∈ Q.erase q.1, f r
      exact sum_kloostermanStoredIndex_if_ne_eq_sum_erase Q q f
    _ = ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          ∑ x : (ZMod (q + 1))ˣ,
            ∑ y : (ZMod (r + 1))ˣ, F q r x y := by
      exact (Finset.sum_subtype Q (fun _ => Iff.rfl) (fun q =>
        ∑ r ∈ Q.erase q, ∑ x : (ZMod (q + 1))ˣ,
          ∑ y : (ZMod (r + 1))ˣ, F q r x y)).symm

theorem sum_normSq_kloostermanGlobalCrossTupleCoefficient_eq
    (Q : Finset ℕ) (w : ℕ → ℂ) (B : Finset ℕ) (b : ℕ → ℂ) :
    (∑ p : KloostermanGlobalCrossTuple Q,
      Complex.normSq (kloostermanGlobalCrossTupleCoefficient Q w B b p)) =
      ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        (Complex.normSq (w q) * Complex.normSq (w r)) *
          (∑ x : (ZMod (q + 1))ˣ,
            Complex.normSq (RHTower.Sieve.kloostermanSourceFourier
              (q + 1) B b x)) *
          ∑ y : (ZMod (r + 1))ˣ,
            Complex.normSq (RHTower.Sieve.kloostermanSourceFourier
              (r + 1) B b y) := by
  calc
    (∑ p : KloostermanGlobalCrossTuple Q,
        Complex.normSq (kloostermanGlobalCrossTupleCoefficient Q w B b p)) =
      ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
          Complex.normSq
            (star (w q) * w r *
              (star (RHTower.Sieve.kloostermanSourceFourier
                (q + 1) B b x) *
                RHTower.Sieve.kloostermanSourceFourier (r + 1) B b y)) := by
      exact sum_kloostermanGlobalCrossTuple_eq_nested Q (fun q r x y =>
        Complex.normSq
          (star (w q) * w r *
            (star (RHTower.Sieve.kloostermanSourceFourier
              (q + 1) B b x) *
              RHTower.Sieve.kloostermanSourceFourier (r + 1) B b y)))
    _ = ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        (Complex.normSq (w q) * Complex.normSq (w r)) *
          (∑ x : (ZMod (q + 1))ˣ,
            Complex.normSq (RHTower.Sieve.kloostermanSourceFourier
              (q + 1) B b x)) *
          ∑ y : (ZMod (r + 1))ˣ,
            Complex.normSq (RHTower.Sieve.kloostermanSourceFourier
              (r + 1) B b y) := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj]
      rw [mul_assoc, Fintype.sum_mul_sum, Finset.mul_sum]
      apply Fintype.sum_congr
      intro x
      rw [Finset.mul_sum]

/-- Pairwise-coprime positive clocks force constant signed global-frequency
collision multiplicity, followed by exact source residue-energy control. -/
theorem kloostermanGlobalFrequencyCollisionEnergy_le_two_residueEnergy_of_pairwise_coprime
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1)))
    (hpos : ∀ q ∈ Q, 0 < q)
    (w : ℕ → ℂ) (B : Finset ℕ) (b : ℕ → ℂ) :
    RHTower.Sieve.kloostermanGlobalFrequencyCollisionEnergy Q w B b ≤
      2 * ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        (Complex.normSq (w q) * Complex.normSq (w r)) *
          ((q + 1 : ℕ) : ℝ) *
          (∑ z : ZMod (q + 1),
            Complex.normSq
              (RHTower.Sieve.kloostermanSourceResidue (q + 1) B b z)) *
          (((r + 1 : ℕ) : ℝ) *
            ∑ z : ZMod (r + 1),
              Complex.normSq
                (RHTower.Sieve.kloostermanSourceResidue (r + 1) B b z)) := by
  calc
    RHTower.Sieve.kloostermanGlobalFrequencyCollisionEnergy Q w B b ≤
        2 * ∑ p : KloostermanGlobalCrossTuple Q,
          Complex.normSq (kloostermanGlobalCrossTupleCoefficient Q w B b p) :=
      kloostermanGlobalFrequencyCollisionEnergy_le_two_crossTuple Q hpair hpos w B b
    _ = 2 * ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        (Complex.normSq (w q) * Complex.normSq (w r)) *
          (∑ x : (ZMod (q + 1))ˣ,
            Complex.normSq (RHTower.Sieve.kloostermanSourceFourier
              (q + 1) B b x)) *
          ∑ y : (ZMod (r + 1))ˣ,
            Complex.normSq (RHTower.Sieve.kloostermanSourceFourier
              (r + 1) B b y) := by
      rw [sum_normSq_kloostermanGlobalCrossTupleCoefficient_eq]
    _ ≤ 2 * ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        (Complex.normSq (w q) * Complex.normSq (w r)) *
          ((q + 1 : ℕ) : ℝ) *
          (∑ z : ZMod (q + 1),
            Complex.normSq
              (RHTower.Sieve.kloostermanSourceResidue (q + 1) B b z)) *
          (((r + 1 : ℕ) : ℝ) *
            ∑ z : ZMod (r + 1),
              Complex.normSq
                (RHTower.Sieve.kloostermanSourceResidue (r + 1) B b z)) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro q hq
        apply Finset.sum_le_sum
        intro r hr
        letI : NeZero (q + 1) := ⟨by omega⟩
        letI : NeZero (r + 1) := ⟨by omega⟩
        have hqE :=
          RHTower.Sieve.sum_normSq_kloostermanSourceFourier_le_residueEnergy
            (q + 1) B b
        have hrE :=
          RHTower.Sieve.sum_normSq_kloostermanSourceFourier_le_residueEnergy
            (r + 1) B b
        have hA : 0 ≤ Complex.normSq (w q) * Complex.normSq (w r) :=
          mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
        have hY : 0 ≤ ∑ y : (ZMod (r + 1))ˣ,
            Complex.normSq (RHTower.Sieve.kloostermanSourceFourier
              (r + 1) B b y) :=
          Finset.sum_nonneg fun y hy => Complex.normSq_nonneg _
        have hX' : 0 ≤ ((q + 1 : ℕ) : ℝ) *
            ∑ z : ZMod (q + 1),
              Complex.normSq
                (RHTower.Sieve.kloostermanSourceResidue (q + 1) B b z) :=
          mul_nonneg (Nat.cast_nonneg _) <|
            Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _
        have hXY := mul_le_mul hqE hrE hY hX'
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hXY hA
      · norm_num


def kloostermanPrimeIndexSet (P : Finset ℕ) : Finset ℕ :=
  P.image Nat.pred

theorem image_succ_kloostermanPrimeIndexSet_eq
    (P : Finset ℕ) (hPprime : ∀ p ∈ P, p.Prime) :
    (kloostermanPrimeIndexSet P).image (fun q => q + 1) = P := by
  classical
  ext n
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨q, hq, hqn⟩
    rcases Finset.mem_image.mp hq with ⟨p, hp, hpq⟩
    have hpSucc : p.pred + 1 = p := Nat.succ_pred_eq_of_pos (hPprime p hp).pos
    rw [← hqn, ← hpq, hpSucc]
    exact hp
  · intro hn
    apply Finset.mem_image.mpr
    refine ⟨n.pred, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
    · exact Nat.succ_pred_eq_of_pos (hPprime n hn).pos

theorem kloostermanPrimeIndexSet_pos
    (P : Finset ℕ) (hPprime : ∀ p ∈ P, p.Prime) :
    ∀ q ∈ kloostermanPrimeIndexSet P, 0 < q := by
  intro q hq
  rcases Finset.mem_image.mp hq with ⟨p, hp, hpq⟩
  rw [← hpq]
  exact (hPprime p hp).pred_pos

theorem kloostermanPrimeIndexSet_pairwise_coprime
    (P : Finset ℕ) (hPprime : ∀ p ∈ P, p.Prime) :
    ((kloostermanPrimeIndexSet P : Finset ℕ) : Set ℕ).Pairwise
      (Function.onFun Nat.Coprime (fun q => q + 1)) := by
  intro q hq r hr hqr
  rcases Finset.mem_image.mp hq with ⟨p, hp, hpq⟩
  rcases Finset.mem_image.mp hr with ⟨s, hs, hsr⟩
  have hpSucc : p.pred + 1 = p := Nat.succ_pred_eq_of_pos (hPprime p hp).pos
  have hsSucc : s.pred + 1 = s := Nat.succ_pred_eq_of_pos (hPprime s hs).pos
  rw [← hpq, ← hsr]
  change Nat.Coprime (p.pred + 1) (s.pred + 1)
  rw [hpSucc, hsSucc]
  apply (Nat.coprime_primes (hPprime p hp) (hPprime s hs)).2
  intro hps
  apply hqr
  rw [← hpq, ← hsr, hps]

theorem kloostermanPrimeIndexSet_globalFrequencyCollisionEnergy_le_two_residueEnergy
    (P : Finset ℕ) (hPprime : ∀ p ∈ P, p.Prime)
    (w : ℕ → ℂ) (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalFrequencyCollisionEnergy (kloostermanPrimeIndexSet P) w B b ≤
      2 * ∑ q ∈ kloostermanPrimeIndexSet P,
        ∑ r ∈ (kloostermanPrimeIndexSet P).erase q,
          (Complex.normSq (w q) * Complex.normSq (w r)) *
            ((q + 1 : ℕ) : ℝ) *
            (∑ z : ZMod (q + 1),
              Complex.normSq (kloostermanSourceResidue (q + 1) B b z)) *
            (((r + 1 : ℕ) : ℝ) *
              ∑ z : ZMod (r + 1),
                Complex.normSq (kloostermanSourceResidue (r + 1) B b z)) := by
  exact kloostermanGlobalFrequencyCollisionEnergy_le_two_residueEnergy_of_pairwise_coprime
    (kloostermanPrimeIndexSet P)
    (kloostermanPrimeIndexSet_pairwise_coprime P hPprime)
    (kloostermanPrimeIndexSet_pos P hPprime) w B b

end

end RHTower.Sieve
