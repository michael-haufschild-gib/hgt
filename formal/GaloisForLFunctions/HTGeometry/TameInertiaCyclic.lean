import GaloisForLFunctions.HTGeometry.TameInertiaRigidity
import Mathlib.RingTheory.IntegralDomain

/-!
# Tame inertia is cyclic

Reading the cofactor of a uniformizer in the residue field turns a tame action into a character.
For a group acting on a discrete valuation ring by ring automorphisms, each `g` multiplies a
uniformizer `π` by a unique unit `ratioElt π g`, and

```text
ratioElt π (g * h) = ratioElt π g * g • ratioElt π h
```

so if the action is trivial on the residue field the residue of the cofactor is multiplicative:

```text
residueRatioHom : Γ →* ResidueField W
```

`TameInertiaRigidity` makes this character faithful in residue characteristic zero — a trivial
ratio forces `π² ∣ gπ − π`, hence `gπ = π`, hence `g = 1` — and a finite group embedding in the
multiplicative monoid of a field is cyclic:

```text
isCyclic_of_tame
    ** a finite group acting faithfully on a discrete valuation ring by ring automorphisms,
       trivially on a residue field of characteristic zero, is cyclic **
```

This is the classical structure of tame inertia, which mathlib does not carry: its
`RamificationGroup` file stops at the inertia subgroup and leaves the higher filtration open.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDiscreteValuationRing

variable {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
variable {Γ : Type*} [Group Γ] [MulSemiringAction Γ W]

/-- The cofactor by which an automorphism multiplies a uniformizer. -/
noncomputable def ratioElt (π : W) (g : Γ) : W := (dvd_smul_self π g).choose

theorem smul_eq_mul_ratioElt (π : W) (g : Γ) : g • π = π * ratioElt π g :=
  (dvd_smul_self π g).choose_spec

theorem ratioElt_unique {π : W} (hπ : Irreducible π) {g : Γ} {c : W} (h : g • π = π * c) :
    c = ratioElt π g := by
  apply mul_left_cancel₀ hπ.ne_zero
  rw [← h, smul_eq_mul_ratioElt]

theorem isUnit_ratioElt {π : W} (hπ : Irreducible π) (g : Γ) : IsUnit (ratioElt π g) := by
  have hg : Irreducible (g • π) := hπ.map (MulSemiringAction.toRingEquiv Γ W g)
  rcases hg.isUnit_or_isUnit (smul_eq_mul_ratioElt π g) with h | h
  · exact absurd h hπ.not_isUnit
  · exact h

theorem ratioElt_one {π : W} (hπ : Irreducible π) : ratioElt π (1 : Γ) = 1 :=
  (ratioElt_unique hπ (by rw [one_smul, mul_one])).symm

theorem ratioElt_mul {π : W} (hπ : Irreducible π) (g h : Γ) :
    ratioElt π (g * h) = ratioElt π g * (g • ratioElt π h) := by
  refine (ratioElt_unique hπ ?_).symm
  rw [mul_smul, smul_eq_mul_ratioElt π h, smul_mul', smul_eq_mul_ratioElt π g]
  ring

theorem residue_smul_eq
    (hres : ∀ (h : Γ) (x : W), h • x - x ∈ IsLocalRing.maximalIdeal W) (g : Γ) (y : W) :
    IsLocalRing.residue W (g • y) = IsLocalRing.residue W y := by
  rw [← sub_eq_zero, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hres g y)

/-- **The ratio character of a tame action.**  Reading the cofactor of a uniformizer in the residue
field is a group homomorphism. -/
noncomputable def residueRatioHom {π : W} (hπ : Irreducible π)
    (hres : ∀ (h : Γ) (x : W), h • x - x ∈ IsLocalRing.maximalIdeal W) :
    Γ →* IsLocalRing.ResidueField W where
  toFun g := IsLocalRing.residue W (ratioElt π g)
  map_one' := by rw [ratioElt_one hπ, map_one]
  map_mul' g h := by
    rw [ratioElt_mul hπ, map_mul, residue_smul_eq hres]

theorem residueRatioHom_apply {π : W} (hπ : Irreducible π)
    (hres : ∀ (h : Γ) (x : W), h • x - x ∈ IsLocalRing.maximalIdeal W) (g : Γ) :
    residueRatioHom hπ hres g = IsLocalRing.residue W (ratioElt π g) := rfl

/-- **The ratio character is faithful at an invertible group order.**  If the group order is
nonzero in the residue field, the ratio character separates every element. -/
theorem residueRatioHom_injective_of_natCard_ne_zero [Finite Γ]
    [FaithfulSMul Γ W] {π : W} (hπ : Irreducible π)
    (hcardRes : ((Nat.card Γ : ℕ) : IsLocalRing.ResidueField W) ≠ 0)
    (hres : ∀ (h : Γ) (x : W), h • x - x ∈ IsLocalRing.maximalIdeal W) :
    Function.Injective (residueRatioHom hπ hres) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : IsLocalRing.residue W (ratioElt π g - 1) = 0 := by
    rw [map_sub, map_one, ← residueRatioHom_apply hπ hres, hg, sub_self]
  have hmem : ratioElt π g - 1 ∈ IsLocalRing.maximalIdeal W :=
    Ideal.Quotient.eq_zero_iff_mem.mp h1
  obtain ⟨c, hc⟩ := dvd_of_mem_maximalIdeal hπ hmem
  have h2 : π ^ 2 ∣ g • π - π := by
    refine ⟨c, ?_⟩
    rw [smul_eq_mul_ratioElt, show π * ratioElt π g - π = π * (ratioElt π g - 1) by ring, hc]
    ring
  have hfix : g • π = π :=
    smul_uniformizer_eq_self_of_sq_dvd_of_natCast_ne_zero
      hres pow_card_eq_one' hcardRes hπ h2
  refine FaithfulSMul.eq_of_smul_eq_smul (α := W) (fun x => ?_)
  rw [smul_eq_self_of_smul_uniformizer_eq_self_of_natCast_ne_zero
    hres pow_card_eq_one' hcardRes hπ hfix x, one_smul]

/-- Residue-characteristic-zero specialization of ratio-character faithfulness. -/
theorem residueRatioHom_injective [CharZero (IsLocalRing.ResidueField W)] [Finite Γ]
    [FaithfulSMul Γ W] {π : W} (hπ : Irreducible π)
    (hres : ∀ (h : Γ) (x : W), h • x - x ∈ IsLocalRing.maximalIdeal W) :
    Function.Injective (residueRatioHom hπ hres) :=
  residueRatioHom_injective_of_natCard_ne_zero hπ
    (Nat.cast_ne_zero.mpr (Nat.card_pos.ne')) hres

/-- **Tame inertia is cyclic at an invertible group order.** -/
theorem isCyclic_of_tame_of_natCard_ne_zero [Finite Γ] [FaithfulSMul Γ W]
    {π : W} (hπ : Irreducible π)
    (hcardRes : ((Nat.card Γ : ℕ) : IsLocalRing.ResidueField W) ≠ 0)
    (hres : ∀ (h : Γ) (x : W), h • x - x ∈ IsLocalRing.maximalIdeal W) :
    IsCyclic Γ :=
  isCyclic_of_injective_ringHom (residueRatioHom hπ hres)
    (residueRatioHom_injective_of_natCard_ne_zero hπ hcardRes hres)

/-- **Tame inertia is cyclic.**  A finite group acting faithfully on a discrete valuation ring by
ring automorphisms, trivially on a residue field of characteristic zero, is cyclic. -/
theorem isCyclic_of_tame [CharZero (IsLocalRing.ResidueField W)] [Finite Γ] [FaithfulSMul Γ W]
    {π : W} (hπ : Irreducible π)
    (hres : ∀ (h : Γ) (x : W), h • x - x ∈ IsLocalRing.maximalIdeal W) :
    IsCyclic Γ :=
  isCyclic_of_injective_ringHom (residueRatioHom hπ hres) (residueRatioHom_injective hπ hres)

end GaloisForLFunctions.HTGeometry
