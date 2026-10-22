/-
Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Lemma 4.3 (`t3`).

The multiplicative group of a field, divided by its roots of unity, is a torsion-free group; over
an algebraically closed field it is moreover divisible and therefore a `ℚ`-vector space.  This file
builds that vector space as the divisible hull of `k^× / μ(k)`, together with

* the criterion turning a multiplicatively independent family of units (independent modulo roots of
  unity) into a rationally independent family of classes,
* the bijectivity of `k^× / μ(k) → (k^× / μ(k)) ⊗ ℚ` for algebraically closed `k`,
* the two cardinality estimates `rank_ℚ ((k^× / μ(k)) ⊗ ℚ) ≤ #k` and `#C ≤ #(C^× / μ(C))`.

`μ(k)` is realised as `CommGroup.torsion kˣ`: a unit of a field has finite order exactly when it is
a root of unity.
-/
import Mathlib.GroupTheory.DivisibleHull
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace RHTower

open Cardinal

section Hull

variable {M : Type*} [AddCommGroup M] [IsAddTorsionFree M]

theorem deningerDivisibleHull_coe_surjective
    (hdiv : ∀ n : ℕ, n ≠ 0 → ∀ m : M, ∃ m', n • m' = m) :
    Function.Surjective (DivisibleHull.coe : M → DivisibleHull M) := by
  intro x
  induction x with
  | mk m s =>
    obtain ⟨m', hm'⟩ := hdiv s.val s.ne_zero m
    refine ⟨m', ?_⟩
    show DivisibleHull.mk m' 1 = DivisibleHull.mk m s
    rw [DivisibleHull.mk_eq_mk_iff_smul_eq_smul]
    simpa using hm'

theorem deningerLinearIndependent_coe {ι : Type*} (u : ι → M)
    (h : ∀ (s : Finset ι) (n : ι → ℤ), ∑ i ∈ s, n i • u i = 0 → ∀ i ∈ s, n i = 0) :
    LinearIndependent ℚ (fun i => (DivisibleHull.coe (u i) : DivisibleHull M)) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  set d : ℕ := ∏ j ∈ s, (g j).den with hd
  have hd0 : (d : ℚ) ≠ 0 := by
    rw [hd]
    push_cast
    exact Finset.prod_ne_zero_iff.2 fun j _ => by
      exact_mod_cast (Rat.den_ne_zero (g j))
  set n : ι → ℤ := fun j => ((d : ℚ) * g j).num with hn
  have hnval : ∀ j ∈ s, ((n j : ℤ) : ℚ) = (d : ℚ) * g j := by
    intro j hj
    have key : ∃ m : ℤ, (d : ℚ) * g j = (m : ℚ) := by
      obtain ⟨e, he⟩ : ((g j).den : ℕ) ∣ d := Finset.dvd_prod_of_mem (fun j => (g j).den) hj
      refine ⟨(e : ℤ) * (g j).num, ?_⟩
      have hden : ((g j).den : ℚ) * g j = ((g j).num : ℚ) := Rat.den_mul_eq_num (g j)
      calc (d : ℚ) * g j = (e : ℚ) * (((g j).den : ℚ) * g j) := by
            rw [he]; push_cast; ring
        _ = (e : ℚ) * ((g j).num : ℚ) := by rw [hden]
        _ = (((e : ℤ) * (g j).num : ℤ) : ℚ) := by push_cast; ring
    obtain ⟨m, hm⟩ := key
    show ((((d : ℚ) * g j).num : ℤ) : ℚ) = (d : ℚ) * g j
    rw [hm, Rat.num_intCast]
  have hsum : ∑ j ∈ s, n j • u j = 0 := by
    apply DivisibleHull.coe_injective
    have hmap : (DivisibleHull.coeAddMonoidHom M) (∑ j ∈ s, n j • u j)
        = ∑ j ∈ s, n j • (DivisibleHull.coe (u j) : DivisibleHull M) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => map_zsmul _ _ _
    have hzero : ∑ j ∈ s, n j • (DivisibleHull.coe (u j) : DivisibleHull M) = 0 := by
      have step : ∀ j ∈ s, (n j) • (DivisibleHull.coe (u j) : DivisibleHull M)
          = ((d : ℚ) * g j) • (DivisibleHull.coe (u j) : DivisibleHull M) := by
        intro j hj
        rw [← Int.cast_smul_eq_zsmul ℚ, hnval j hj]
      calc ∑ j ∈ s, n j • (DivisibleHull.coe (u j) : DivisibleHull M)
          = ∑ j ∈ s, ((d : ℚ) * g j) • (DivisibleHull.coe (u j) : DivisibleHull M) :=
            Finset.sum_congr rfl step
        _ = (d : ℚ) • ∑ j ∈ s, g j • (DivisibleHull.coe (u j) : DivisibleHull M) := by
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun j _ => (smul_smul _ _ _).symm
        _ = 0 := by rw [hg, smul_zero]
    have hz : (DivisibleHull.coeAddMonoidHom M) (∑ j ∈ s, n j • u j) = 0 := by
      rw [hmap, hzero]
    have h2 : (DivisibleHull.coe (∑ j ∈ s, n j • u j) : DivisibleHull M) = 0 := hz
    rw [h2]
    simp
  have hni := h s n hsum i hi
  have := hnval i hi
  rw [hni] at this
  simp only [Int.cast_zero] at this
  exact (mul_eq_zero.1 this.symm).resolve_left hd0

theorem deningerRank_le_mk (R : Type*) (M : Type*) [DivisionRing R] [AddCommGroup M]
    [Module R M] : Module.rank R M ≤ #M := by
  rw [Module.Free.rank_eq_card_chooseBasisIndex R M]
  exact Cardinal.mk_le_of_injective (Module.Free.chooseBasis R M).linearIndependent.injective

end Hull

/-! ### The unit class group of a field -/

/-- The additive group `k^× / μ(k)`. -/
abbrev DeningerUnitClass (k : Type*) [Field k] : Type _ :=
  Additive (kˣ ⧸ CommGroup.torsion kˣ)

/-- The rational vector space attached to `k^× / μ(k)`. -/
abbrev DeningerUnitSpace (k : Type*) [Field k] : Type _ :=
  DivisibleHull (DeningerUnitClass k)

variable {k : Type*} [Field k]

/-- The class of a unit in `k^× / μ(k)`, written additively. -/
def deningerUnitCls (x : kˣ) : DeningerUnitClass k :=
  Additive.ofMul (QuotientGroup.mk' (CommGroup.torsion kˣ) x)

/-- The class of a unit in the rational vector space `(k^× / μ(k)) ⊗ ℚ`. -/
def deningerUnitVec (x : kˣ) : DeningerUnitSpace k :=
  DivisibleHull.coe (deningerUnitCls x)

theorem deningerUnitCls_eq_zero_iff (x : kˣ) :
    deningerUnitCls x = 0 ↔ x ∈ CommGroup.torsion kˣ := by
  constructor
  · intro h
    exact (QuotientGroup.eq_one_iff x).1 (congrArg Additive.toMul h)
  · intro h
    exact congrArg Additive.ofMul ((QuotientGroup.eq_one_iff x).2 h)

theorem deningerOfMul_prod_zpow {G : Type*} [CommGroup G] {ι : Type*} (s : Finset ι) (u : ι → G)
    (n : ι → ℤ) :
    ∑ i ∈ s, n i • (Additive.ofMul (u i)) = Additive.ofMul (∏ i ∈ s, u i ^ n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, ih]
      rfl

theorem deningerUnitCls_prod_zpow {ι : Type*} (s : Finset ι) (u : ι → kˣ) (n : ι → ℤ) :
    ∑ i ∈ s, n i • deningerUnitCls (u i) = deningerUnitCls (∏ i ∈ s, u i ^ n i) := by
  simp only [deningerUnitCls]
  rw [deningerOfMul_prod_zpow s (fun i => QuotientGroup.mk' (CommGroup.torsion kˣ) (u i)) n]
  congr 1
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => (map_zpow _ _ _).symm

/-- **The independence criterion.**  A family of units whose only multiplicative relations modulo
roots of unity are trivial gives a rationally independent family of classes. -/
theorem deningerUnitVec_linearIndependent {ι : Type*} (u : ι → kˣ)
    (h : ∀ (s : Finset ι) (n : ι → ℤ), (∏ i ∈ s, u i ^ n i) ∈ CommGroup.torsion kˣ →
      ∀ i ∈ s, n i = 0) :
    LinearIndependent ℚ (fun i => deningerUnitVec (u i)) := by
  apply deningerLinearIndependent_coe (M := DeningerUnitClass k) (fun i => deningerUnitCls (u i))
  intro s n hn i hi
  refine h s n ?_ i hi
  rw [deningerUnitCls_prod_zpow] at hn
  exact (deningerUnitCls_eq_zero_iff _).1 hn

/-! ### The algebraically closed case -/

/-- Over an algebraically closed field every unit is an `n`-th power. -/
theorem deningerUnits_exists_pow {C : Type*} [Field C] [IsAlgClosed C] {n : ℕ} (hn : n ≠ 0)
    (x : Cˣ) : ∃ y : Cˣ, y ^ n = x := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : C) (Nat.pos_of_ne_zero hn)
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow hn] at hz
    exact x.ne_zero hz.symm
  refine ⟨Units.mk0 z hz0, Units.ext ?_⟩
  simpa using hz

/-- `C^× / μ(C)` is divisible when `C` is algebraically closed. -/
theorem deningerUnitClass_divisible {C : Type*} [Field C] [IsAlgClosed C] {n : ℕ} (hn : n ≠ 0)
    (m : DeningerUnitClass C) : ∃ m' : DeningerUnitClass C, n • m' = m := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (CommGroup.torsion Cˣ) (Additive.toMul m)
  obtain ⟨y, hy⟩ := deningerUnits_exists_pow hn x
  refine ⟨deningerUnitCls y, ?_⟩
  have : (n : ℤ) • deningerUnitCls y = deningerUnitCls (y ^ (n : ℤ)) := by
    have := deningerUnitCls_prod_zpow (ι := Unit) {()} (fun _ => y) (fun _ => (n : ℤ))
    simpa using this
  have hz : (n : ℤ) • deningerUnitCls y = deningerUnitCls x := by
    rw [this, zpow_natCast, hy]
  have hnat : (n : ℕ) • deningerUnitCls y = (n : ℤ) • deningerUnitCls y := by
    rw [natCast_zsmul]
  rw [hnat, hz]
  show Additive.ofMul ((QuotientGroup.mk' (CommGroup.torsion Cˣ)) x) = m
  rw [hx]
  rfl

/-- Over an algebraically closed field the class map into the rational vector space is a
bijection. -/
theorem deningerUnitSpace_coe_bijective (C : Type*) [Field C] [IsAlgClosed C] :
    Function.Bijective (DivisibleHull.coe : DeningerUnitClass C → DeningerUnitSpace C) :=
  ⟨DivisibleHull.coe_injective,
    deningerDivisibleHull_coe_surjective fun _ hn m => deningerUnitClass_divisible hn m⟩

theorem deningerMk_unitSpace (C : Type*) [Field C] [IsAlgClosed C] :
    #(DeningerUnitSpace C) = #(DeningerUnitClass C) :=
  (Cardinal.mk_congr (Equiv.ofBijective _ (deningerUnitSpace_coe_bijective C))).symm

/-- The rank of `(k^× / μ(k)) ⊗ ℚ` is at most the cardinality of `k`, for `k` algebraically
closed. -/
theorem deningerRank_unitSpace_le (k : Type*) [Field k] [IsAlgClosed k] :
    Module.rank ℚ (DeningerUnitSpace k) ≤ #k := by
  refine (deningerRank_le_mk ℚ (DeningerUnitSpace k)).trans ?_
  rw [deningerMk_unitSpace k]
  refine (Cardinal.mk_le_of_injective (f := fun m : DeningerUnitClass k =>
      Additive.toMul m) (fun a b h => h)).trans ?_
  refine (Cardinal.mk_le_of_surjective
      (f := fun x : kˣ => (QuotientGroup.mk' (CommGroup.torsion kˣ) x))
      (QuotientGroup.mk'_surjective _)).trans ?_
  exact Cardinal.mk_le_of_injective (f := fun x : kˣ => (x : k)) fun _ _ h => Units.ext h

/-! ### Counting -/

/-- The roots of unity of a field form a countable group. -/
theorem deningerTorsion_countable (C : Type*) [Field C] : Countable (CommGroup.torsion Cˣ) := by
  have hsub : ((CommGroup.torsion Cˣ : Subgroup Cˣ) : Set Cˣ) ⊆
      ⋃ n : ℕ, ((rootsOfUnity (n + 1) C : Subgroup Cˣ) : Set Cˣ) := by
    intro x hx
    obtain ⟨m, hm, hxm⟩ :=
      isOfFinOrder_iff_pow_eq_one.1 ((CommGroup.mem_torsion _ ).1 hx)
    refine Set.mem_iUnion.2 ⟨m - 1, ?_⟩
    have hm1 : m - 1 + 1 = m := by omega
    have : x ∈ rootsOfUnity m C := (mem_rootsOfUnity m x).2 hxm
    rw [hm1]
    exact this
  have hcount : (⋃ n : ℕ, ((rootsOfUnity (n + 1) C : Subgroup Cˣ) : Set Cˣ)).Countable :=
    Set.countable_iUnion fun n => Set.Finite.countable (by
      haveI : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
      haveI : Finite ((rootsOfUnity (n + 1) C : Subgroup Cˣ) : Set Cˣ) :=
        inferInstanceAs (Finite (rootsOfUnity (n + 1) C))
      exact Set.toFinite _)
  exact (hcount.mono hsub).to_subtype

theorem deningerMk_torsion_le (C : Type*) [Field C] :
    #(CommGroup.torsion Cˣ) ≤ ℵ₀ :=
  haveI := deningerTorsion_countable C
  Cardinal.mk_le_aleph0

/-- The cardinality of a field is at most that of its unit class group, as soon as the latter is
infinite. -/
theorem deningerMk_le_unitClass (C : Type*) [Field C]
    (h : ℵ₀ ≤ #(DeningerUnitClass C)) : #C ≤ #(DeningerUnitClass C) := by
  classical
  have hqsurj : Function.Surjective (QuotientGroup.mk' (CommGroup.torsion Cˣ)) :=
    QuotientGroup.mk'_surjective _
  set σ := Function.surjInv hqsurj with hσdef
  have hσ : ∀ y, (QuotientGroup.mk' (CommGroup.torsion Cˣ)) (σ y) = y :=
    Function.surjInv_eq hqsurj
  have hmem : ∀ x : Cˣ,
      x * (σ ((QuotientGroup.mk' (CommGroup.torsion Cˣ)) x))⁻¹ ∈ CommGroup.torsion Cˣ := by
    intro x
    have hq : (QuotientGroup.mk' (CommGroup.torsion Cˣ))
        (x * (σ ((QuotientGroup.mk' (CommGroup.torsion Cˣ)) x))⁻¹) = 1 := by
      rw [map_mul, map_inv, hσ, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff _).1 hq
  have hinj : Function.Injective
      (fun x : Cˣ => ((⟨x * (σ ((QuotientGroup.mk' (CommGroup.torsion Cˣ)) x))⁻¹, hmem x⟩ :
          CommGroup.torsion Cˣ), (QuotientGroup.mk' (CommGroup.torsion Cˣ)) x)) := by
    intro x y hxy
    have h1 : (QuotientGroup.mk' (CommGroup.torsion Cˣ)) x
        = (QuotientGroup.mk' (CommGroup.torsion Cˣ)) y := congrArg Prod.snd hxy
    have h2 : x * (σ ((QuotientGroup.mk' (CommGroup.torsion Cˣ)) x))⁻¹
        = y * (σ ((QuotientGroup.mk' (CommGroup.torsion Cˣ)) y))⁻¹ :=
      congrArg (fun p => (p.1 : Cˣ)) hxy
    rw [h1] at h2
    exact mul_right_cancel h2
  have hunits : #(Cˣ) ≤ #(CommGroup.torsion Cˣ) * #(DeningerUnitClass C) := by
    have := Cardinal.mk_le_of_injective hinj
    simpa using this
  have hcast : #C ≤ #(Cˣ) + 1 := by
    have hinj2 : Function.Injective
        (fun x : C => if h : x = 0 then (none : Option Cˣ) else some (Units.mk0 x h)) := by
      intro a b hab
      by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
        simp [ha, hb] at hab ⊢
      · exact hab
    have := Cardinal.mk_le_of_injective hinj2
    simpa using this
  calc #C ≤ #(Cˣ) + 1 := hcast
    _ ≤ #(CommGroup.torsion Cˣ) * #(DeningerUnitClass C) + 1 := by gcongr
    _ ≤ ℵ₀ * #(DeningerUnitClass C) + 1 := by
        gcongr
        exact deningerMk_torsion_le C
    _ = #(DeningerUnitClass C) + 1 := by
        rw [Cardinal.mul_eq_max le_rfl h, max_eq_right h]
    _ = #(DeningerUnitClass C) := Cardinal.add_one_eq h

end RHTower
