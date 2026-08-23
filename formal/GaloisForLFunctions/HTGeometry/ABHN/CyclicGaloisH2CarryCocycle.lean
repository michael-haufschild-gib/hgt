/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisRestrictionOrientation

/-!
# Explicit cyclic Galois H² carry cocycles

The periodic cyclic resolution presents `H²` as fixed units modulo norms but hides its comparison
with inhomogeneous bar cocycles.  This file constructs the classical carry cocycle explicitly.
For a chosen cyclic generator, its value is the embedded base unit exactly when adding standard
exponent representatives wraps around the group order.

Restriction through a cyclic Galois tower is computed on these cocycles.  The restricted lower
carry differs from the upper carry with parameter multiplied by
`orientation * [M : L]` by the coboundary of an explicit floor-function cochain.  Hence genuine
group-cohomological inflation obeys the corrected formula on explicit carry classes.

Finally, the difference between the abstract periodic-resolution base projection and this explicit
bar class is packaged as an additive comparison defect.  An unconditional identity shows that the
remaining gap between genuine inflation and the oriented norm-quotient transition is exactly the
naturality mismatch of this one comparison defect.
-/

open CategoryTheory Representation

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- Carry of the standard representatives of two residue classes. -/
def cyclicCarry (n : ℕ) (a b : ZMod n) : ℕ := (a.val + b.val) / n

/-- Addition of standard representatives splits into a carry and the new representative. -/
theorem zmod_val_add_split {n : ℕ} [NeZero n] (a b : ZMod n) :
    a.val + b.val = n * cyclicCarry n a b + (a + b).val := by
  rw [cyclicCarry, ZMod.val_add]
  exact (Nat.div_add_mod _ _).symm

/-- Carry satisfies the inhomogeneous two-cocycle identity. -/
theorem cyclicCarry_cocycle (n : ℕ) [NeZero n] (a b c : ZMod n) :
    cyclicCarry n b c + cyclicCarry n a (b + c) =
      cyclicCarry n (a + b) c + cyclicCarry n a b := by
  have hn : n ≠ 0 := NeZero.ne n
  have h1 := zmod_val_add_split a b
  have h2 := zmod_val_add_split (a + b) c
  have h3 := zmod_val_add_split b c
  have h4 := zmod_val_add_split a (b + c)
  rw [add_assoc] at h2
  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn) ?_
  rw [Nat.mul_add, Nat.mul_add]
  omega

/-- Reduce a standard upper representative modulo `n` after scaling by `q`. -/
def cyclicScaledResidue (n q : ℕ) {N : ℕ} (i : ZMod N) : ZMod n :=
  (q * i.val : ZMod n)

/-- Floor cochain correcting scaled carry under a cyclic quotient. -/
def cyclicCarryTransfer (n q : ℕ) {N : ℕ} (i : ZMod N) : ℕ :=
  (q * i.val) / n

/-- Scaled residue is additive when the lower modulus divides the upper modulus. -/
theorem cyclicScaledResidue_add
    (n d N q : ℕ) [NeZero n] [NeZero N] (hN : n * d = N) (i j : ZMod N) :
    cyclicScaledResidue n q (i + j) =
      cyclicScaledResidue n q i + cyclicScaledResidue n q j := by
  have htop := zmod_val_add_split i j
  have hNcast : (N : ZMod n) = 0 := by
    rw [← hN]
    simp
  have hval : ((i + j).val : ZMod n) = (i.val : ZMod n) + (j.val : ZMod n) := by
    have h := congrArg (fun t : ℕ => (t : ZMod n)) htop
    simp only [Nat.cast_add, Nat.cast_mul, hNcast, zero_mul, zero_add] at h
    exact h.symm
  simp only [cyclicScaledResidue]
  rw [hval, mul_add]

/-- Scaled lower carry and upper carry differ by the coboundary of `cyclicCarryTransfer`. -/
theorem cyclicScaledResidue_carry_transfer
    (n d N q : ℕ) [NeZero n] [NeZero N] (hN : n * d = N) (i j : ZMod N) :
    cyclicCarryTransfer n q i + cyclicCarryTransfer n q j +
        cyclicCarry n (cyclicScaledResidue n q i) (cyclicScaledResidue n q j) =
      cyclicCarryTransfer n q (i + j) +
        q * d * cyclicCarry N i j := by
  have hi := (Nat.div_add_mod (q * i.val) n).symm
  have hj := (Nat.div_add_mod (q * j.val) n).symm
  have hij := (Nat.div_add_mod (q * (i + j).val) n).symm
  have htop := zmod_val_add_split i j
  have hres := zmod_val_add_split
    (cyclicScaledResidue n q i) (cyclicScaledResidue n q j)
  rw [← cyclicScaledResidue_add n d N q hN i j] at hres
  simp only [cyclicCarryTransfer] at hi hj hij ⊢
  simp only [cyclicScaledResidue, ← Nat.cast_mul, ZMod.val_natCast] at hres
  simp only [cyclicScaledResidue, ← Nat.cast_mul] at ⊢
  have htopq := congrArg (fun x : ℕ => q * x) htop
  have hcomm :
      q * (N * cyclicCarry N i j) =
        n * (q * (d * cyclicCarry N i j)) := by
    calc
      q * (N * cyclicCarry N i j) =
          q * ((n * d) * cyclicCarry N i j) := by rw [hN]
      _ = n * (q * (d * cyclicCarry N i j)) := by ac_rfl
  simp only [mul_add] at htopq
  rw [hcomm] at htopq
  have hassoc :
      n * (q * (d * cyclicCarry N i j)) =
        n * q * d * cyclicCarry N i j := by
    ac_rfl
  rw [hassoc] at htopq
  ring_nf at hi hj hij htopq hres ⊢
  apply Nat.eq_of_mul_eq_mul_left (NeZero.pos n)
  ring_nf
  have hswap :
      n * q * d * cyclicCarry N i j =
        q * n * d * cyclicCarry N i j := by
    ac_rfl
  omega

/-- Coordinate of a Galois automorphism relative to the chosen cyclic generator. -/
def cyclicGaloisExponent
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (sigma : Gal(L/K)) : ZMod (Module.finrank K L) :=
  Multiplicative.toAdd
    ((zmodMulEquivOfGenerator
      (cyclicGaloisGenerator_spec K L)
      (IsGalois.card_aut_eq_finrank K L)).symm sigma)

/-- Galois exponent coordinates turn composition into addition. -/
@[simp] theorem cyclicGaloisExponent_mul
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (sigma tau : Gal(L/K)) :
    cyclicGaloisExponent K L (sigma * tau) =
      cyclicGaloisExponent K L sigma + cyclicGaloisExponent K L tau := by
  simp [cyclicGaloisExponent]

/-- Identity automorphism has exponent zero. -/
@[simp] theorem cyclicGaloisExponent_one
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] :
    cyclicGaloisExponent K L 1 = 0 := by
  simp [cyclicGaloisExponent]

/-- Restriction scales exponent coordinates by the generator orientation. -/
theorem cyclicGaloisExponent_restrict
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] (sigma : Gal(M/K)) :
    cyclicGaloisExponent K L
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L sigma) =
      cyclicGaloisRestrictionOrientation K L M *
        ZMod.castHom (cyclicGaloisFinrank_dvd K L M) (ZMod (Module.finrank K L))
          (cyclicGaloisExponent K M sigma) := by
  letI : NeZero (Module.finrank K L) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  letI : NeZero (Module.finrank K M) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := M))⟩
  let eL := zmodMulEquivOfGenerator
    (cyclicGaloisGenerator_spec K L) (IsGalois.card_aut_eq_finrank K L)
  let eM := zmodMulEquivOfGenerator
    (cyclicGaloisGenerator_spec K M) (IsGalois.card_aut_eq_finrank K M)
  apply Multiplicative.ofAdd.injective
  apply eL.injective
  rw [show eL (Multiplicative.ofAdd (cyclicGaloisExponent K L
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L sigma))) =
      AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L sigma by
    exact eL.apply_symm_apply _]
  nth_rewrite 1 [← show eM (Multiplicative.ofAdd (cyclicGaloisExponent K M sigma)) = sigma by
    exact eM.apply_symm_apply _]
  have hcast :
      ZMod.castHom (cyclicGaloisFinrank_dvd K L M) (ZMod (Module.finrank K L))
          (cyclicGaloisExponent K M sigma) =
        ((cyclicGaloisExponent K M sigma).val : ZMod (Module.finrank K L)) := by
    calc
      _ = ZMod.castHom (cyclicGaloisFinrank_dvd K L M)
            (ZMod (Module.finrank K L))
            ((cyclicGaloisExponent K M sigma).val : ZMod (Module.finrank K M)) := by
          rw [ZMod.natCast_zmod_val]
      _ = _ := by rw [map_natCast]
  rw [hcast]
  rw [← ZMod.natCast_zmod_val (cyclicGaloisRestrictionOrientation K L M)]
  rw [← Nat.cast_mul]
  change AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L
      (eM (Multiplicative.ofAdd (cyclicGaloisExponent K M sigma))) =
    eL (Multiplicative.ofAdd
      (((cyclicGaloisRestrictionOrientation K L M).val *
        (cyclicGaloisExponent K M sigma).val : ℕ) : ZMod _))
  rw [show eM (Multiplicative.ofAdd (cyclicGaloisExponent K M sigma)) =
      cyclicGaloisGenerator K M ^ (cyclicGaloisExponent K M sigma).val by
    calc
      eM (Multiplicative.ofAdd (cyclicGaloisExponent K M sigma)) =
          eM (Multiplicative.ofAdd
            ((cyclicGaloisExponent K M sigma).val : ZMod _)) := by
            rw [ZMod.natCast_zmod_val]
      _ = eM (Multiplicative.ofAdd
            (((cyclicGaloisExponent K M sigma).val : ℤ) : ZMod _)) := by
            rw [Int.cast_natCast]
      _ = _ := by
        rw [zmodMulEquivOfGenerator_apply_ofAdd_intCast, zpow_natCast]]
  rw [map_pow, cyclicGaloisRestrictionOrientation_spec, ← pow_mul]
  rw [← Int.cast_natCast]
  rw [zmodMulEquivOfGenerator_apply_ofAdd_intCast, zpow_natCast]

/-- Restriction coordinates are the scaled residues used by the carry-transfer identity. -/
theorem cyclicGaloisExponent_restrict_eq_scaledResidue
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] (sigma : Gal(M/K)) :
    cyclicGaloisExponent K L
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L sigma) =
      cyclicScaledResidue (Module.finrank K L)
        (cyclicGaloisRestrictionOrientation K L M).val
        (cyclicGaloisExponent K M sigma) := by
  letI : NeZero (Module.finrank K L) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  letI : NeZero (Module.finrank K M) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := M))⟩
  rw [cyclicGaloisExponent_restrict]
  have hcast :
      ZMod.castHom (cyclicGaloisFinrank_dvd K L M) (ZMod (Module.finrank K L))
          (cyclicGaloisExponent K M sigma) =
        ((cyclicGaloisExponent K M sigma).val : ZMod (Module.finrank K L)) := by
    calc
      _ = ZMod.castHom (cyclicGaloisFinrank_dvd K L M)
            (ZMod (Module.finrank K L))
            ((cyclicGaloisExponent K M sigma).val : ZMod (Module.finrank K M)) := by
          rw [ZMod.natCast_zmod_val]
      _ = _ := by rw [map_natCast]
  rw [hcast]
  simp only [cyclicScaledResidue]
  rw [ZMod.natCast_zmod_val]

/-- Every embedded base-field unit is fixed by every Galois automorphism. -/
theorem cyclicGaloisBaseUnitsMap_fixed
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (sigma : Gal(L/K)) (a : Additive Kˣ) :
    (Rep.ofAlgebraAutOnUnits K L).ρ sigma
        (cyclicGaloisBaseUnitsMap (K := K) (L := L) a) =
      cyclicGaloisBaseUnitsMap (K := K) (L := L) a := by
  change Additive.ofMul (Units.map sigma.toMonoidHom
      (Units.map (algebraMap K L) a.toMul)) =
    Additive.ofMul (Units.map (algebraMap K L) a.toMul)
  apply Additive.toMul.injective
  apply Units.ext
  exact sigma.commutes _

/-- Explicit additive factor set: the embedded base unit multiplied by the exponent carry. -/
def cyclicGaloisCarryFactor
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (a : Additive Kˣ) : Gal(L/K) × Gal(L/K) → (Rep.ofAlgebraAutOnUnits K L) :=
  fun gh => cyclicCarry (Module.finrank K L)
      (cyclicGaloisExponent K L gh.1) (cyclicGaloisExponent K L gh.2) •
    cyclicGaloisBaseUnitsMap (K := K) (L := L) a

/-- The explicit cyclic Galois carry factor is a bar-resolution two-cocycle. -/
theorem cyclicGaloisCarryFactor_isCocycle
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (a : Additive Kˣ) :
    cyclicGaloisCarryFactor K L a ∈
      groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K L) := by
  letI : NeZero (Module.finrank K L) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  rw [groupCohomology.mem_cocycles₂_iff]
  intro g h j
  let x : (Rep.ofAlgebraAutOnUnits K L) :=
    cyclicGaloisBaseUnitsMap (K := K) (L := L) a
  change cyclicCarry _ (cyclicGaloisExponent K L (g * h)) (cyclicGaloisExponent K L j) • x +
      cyclicCarry _ (cyclicGaloisExponent K L g) (cyclicGaloisExponent K L h) • x =
    (Rep.ofAlgebraAutOnUnits K L).ρ g
        (cyclicCarry _ (cyclicGaloisExponent K L h) (cyclicGaloisExponent K L j) • x) +
      cyclicCarry _ (cyclicGaloisExponent K L g) (cyclicGaloisExponent K L (h * j)) • x
  rw [cyclicGaloisExponent_mul, cyclicGaloisExponent_mul]
  rw [map_nsmul, cyclicGaloisBaseUnitsMap_fixed]
  rw [← add_nsmul, ← add_nsmul]
  exact congrArg (fun m : ℕ => m • x)
    (cyclicCarry_cocycle (Module.finrank K L)
      (cyclicGaloisExponent K L g) (cyclicGaloisExponent K L h)
      (cyclicGaloisExponent K L j)).symm

/-- The explicit carry factor as an element of mathlib's degree-two cocycles. -/
noncomputable def cyclicGaloisCarryCocycle
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (a : Additive Kˣ) :
    groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K L) :=
  ⟨cyclicGaloisCarryFactor K L a, cyclicGaloisCarryFactor_isCocycle K L a⟩

/-- Degree-two Galois cohomology class of the explicit carry cocycle. -/
noncomputable def cyclicGaloisCarryH2Class
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (a : Additive Kˣ) : cyclicGaloisH2 K L :=
  groupCohomology.H2π _ (cyclicGaloisCarryCocycle K L a)

/-- Floor-function one-cochain witnessing carry compatibility through a Galois tower. -/
def cyclicGaloisCarryTransferCochain
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    (a : Additive Kˣ) (sigma : Gal(M/K)) : (Rep.ofAlgebraAutOnUnits K M) :=
  cyclicCarryTransfer (Module.finrank K L)
      (cyclicGaloisRestrictionOrientation K L M).val
      (cyclicGaloisExponent K M sigma) •
    cyclicGaloisBaseUnitsMap (K := K) (L := M) a

/-- Values of the transfer cochain lie in embedded base units and are Galois-fixed. -/
theorem cyclicGaloisCarryTransferCochain_fixed
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    (a : Additive Kˣ) (sigma tau : Gal(M/K)) :
    (Rep.ofAlgebraAutOnUnits K M).ρ sigma
        (cyclicGaloisCarryTransferCochain K L M a tau) =
      cyclicGaloisCarryTransferCochain K L M a tau := by
  let x : (Rep.ofAlgebraAutOnUnits K M) :=
    cyclicGaloisBaseUnitsMap (K := K) (L := M) a
  have hx : (Rep.ofAlgebraAutOnUnits K M).ρ sigma x = x :=
    cyclicGaloisBaseUnitsMap_fixed K M sigma a
  let c := cyclicCarryTransfer (Module.finrank K L)
    (cyclicGaloisRestrictionOrientation K L M).val
    (cyclicGaloisExponent K M tau)
  change (Rep.ofAlgebraAutOnUnits K M).ρ sigma
      (c • x) = c • x
  calc
    _ = c • ((Rep.ofAlgebraAutOnUnits K M).ρ sigma x) :=
      map_nsmul ((Rep.ofAlgebraAutOnUnits K M).ρ sigma) c x
    _ = c • x := by rw [hx]

/-- Literal pullback of the lower carry cocycle is scaled lower carry in upper coordinates. -/
theorem cyclicGaloisCarry_mapCocycles_apply
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    (a : Additive Kˣ) (sigma tau : Gal(M/K)) :
    groupCohomology.mapCocycles₂
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
        (galoisTowerUnitsRepresentationHom K L M)
        (cyclicGaloisCarryCocycle K L a) (sigma, tau) =
      cyclicCarry (Module.finrank K L)
          (cyclicScaledResidue (Module.finrank K L)
            (cyclicGaloisRestrictionOrientation K L M).val
            (cyclicGaloisExponent K M sigma))
          (cyclicScaledResidue (Module.finrank K L)
            (cyclicGaloisRestrictionOrientation K L M).val
            (cyclicGaloisExponent K M tau)) •
        cyclicGaloisBaseUnitsMap (K := K) (L := M) a := by
  rw [groupCohomology.coe_mapCocycles₂]
  change Additive.ofMul (Units.map (algebraMap L M).toMonoidHom
      (Additive.toMul
        (cyclicGaloisCarryFactor K L a
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L sigma,
            AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L tau)))) = _
  simp only [cyclicGaloisCarryFactor, cyclicGaloisExponent_restrict_eq_scaledResidue]
  change (Units.map (algebraMap L M).toMonoidHom).toAdditive
      (_ • cyclicGaloisBaseUnitsMap (K := K) (L := L) a) =
    _ • cyclicGaloisBaseUnitsMap (K := K) (L := M) a
  rw [map_nsmul]
  congr 1
  change Additive.ofMul (Units.map (algebraMap L M).toMonoidHom
      (Units.map (algebraMap K L).toMonoidHom a.toMul)) =
    Additive.ofMul (Units.map (algebraMap K M).toMonoidHom a.toMul)
  apply Additive.toMul.injective
  apply Units.ext
  exact (IsScalarTower.algebraMap_apply K L M (a.toMul : K)).symm

/-- The pulled-back lower carry cocycle and corrected upper carry cocycle define the same `H²`
class; `cyclicGaloisCarryTransferCochain` is the explicit coboundary witness. -/
theorem cyclicGaloisCarryCocycle_inflation_eq
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] (a : Additive Kˣ) :
    groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K M)
        (cyclicGaloisCarryCocycle K M
          (((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M) • a)) =
      groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K M)
        (groupCohomology.mapCocycles₂
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
          (galoisTowerUnitsRepresentationHom K L M)
          (cyclicGaloisCarryCocycle K L a)) := by
  letI : NeZero (Module.finrank K L) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  letI : NeZero (Module.finrank K M) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := M))⟩
  apply (groupCohomology.H2π_eq_iff _ _).2
  change (⇑(cyclicGaloisCarryCocycle K M
      (((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M) • a)) -
    ⇑(groupCohomology.mapCocycles₂
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
      (galoisTowerUnitsRepresentationHom K L M)
      (cyclicGaloisCarryCocycle K L a))) ∈
        groupCohomology.coboundaries₂ (Rep.ofAlgebraAutOnUnits K M)
  refine ⟨cyclicGaloisCarryTransferCochain K L M a, ?_⟩
  funext gh
  rcases gh with ⟨sigma, tau⟩
  change (Rep.ofAlgebraAutOnUnits K M).ρ sigma
        (cyclicGaloisCarryTransferCochain K L M a tau) -
      cyclicGaloisCarryTransferCochain K L M a (sigma * tau) +
      cyclicGaloisCarryTransferCochain K L M a sigma =
    cyclicGaloisCarryFactor K M
        (((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M) • a)
        (sigma, tau) -
      groupCohomology.mapCocycles₂
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
        (galoisTowerUnitsRepresentationHom K L M)
        (cyclicGaloisCarryCocycle K L a) (sigma, tau)
  rw [cyclicGaloisCarry_mapCocycles_apply]
  rw [cyclicGaloisCarryTransferCochain_fixed]
  simp only [cyclicGaloisCarryFactor, cyclicGaloisCarryTransferCochain,
    cyclicGaloisExponent_mul]
  rw [map_nsmul]
  rw [smul_smul]
  let x : (Rep.ofAlgebraAutOnUnits K M) :=
    cyclicGaloisBaseUnitsMap (K := K) (L := M) a
  change cyclicCarryTransfer (Module.finrank K L)
          (cyclicGaloisRestrictionOrientation K L M).val
          (cyclicGaloisExponent K M tau) • x -
        cyclicCarryTransfer (Module.finrank K L)
          (cyclicGaloisRestrictionOrientation K L M).val
          (cyclicGaloisExponent K M sigma + cyclicGaloisExponent K M tau) • x +
      cyclicCarryTransfer (Module.finrank K L)
          (cyclicGaloisRestrictionOrientation K L M).val
          (cyclicGaloisExponent K M sigma) • x =
    (cyclicCarry (Module.finrank K M)
          (cyclicGaloisExponent K M sigma) (cyclicGaloisExponent K M tau) *
        ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M)) • x -
      cyclicCarry (Module.finrank K L)
          (cyclicScaledResidue (Module.finrank K L)
            (cyclicGaloisRestrictionOrientation K L M).val
            (cyclicGaloisExponent K M sigma))
          (cyclicScaledResidue (Module.finrank K L)
            (cyclicGaloisRestrictionOrientation K L M).val
            (cyclicGaloisExponent K M tau)) • x
  have hcarry := cyclicScaledResidue_carry_transfer
    (Module.finrank K L) (Module.finrank L M) (Module.finrank K M)
    (cyclicGaloisRestrictionOrientation K L M).val
    (Module.finrank_mul_finrank K L M)
    (cyclicGaloisExponent K M sigma) (cyclicGaloisExponent K M tau)
  have hx := congrArg (fun m : ℕ => m • x) hcarry
  simp only [add_nsmul] at hx
  rw [show cyclicCarry (Module.finrank K M)
        (cyclicGaloisExponent K M sigma) (cyclicGaloisExponent K M tau) *
          ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M) =
      (cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M *
        cyclicCarry (Module.finrank K M)
          (cyclicGaloisExponent K M sigma) (cyclicGaloisExponent K M tau) by ac_rfl]
  let Fi : (Rep.ofAlgebraAutOnUnits K M) :=
    cyclicCarryTransfer (Module.finrank K L)
      (cyclicGaloisRestrictionOrientation K L M).val
      (cyclicGaloisExponent K M sigma) • x
  let Fj : (Rep.ofAlgebraAutOnUnits K M) :=
    cyclicCarryTransfer (Module.finrank K L)
      (cyclicGaloisRestrictionOrientation K L M).val
      (cyclicGaloisExponent K M tau) • x
  let Fs : (Rep.ofAlgebraAutOnUnits K M) :=
    cyclicCarryTransfer (Module.finrank K L)
      (cyclicGaloisRestrictionOrientation K L M).val
      (cyclicGaloisExponent K M sigma + cyclicGaloisExponent K M tau) • x
  let Cn : (Rep.ofAlgebraAutOnUnits K M) :=
    cyclicCarry (Module.finrank K L)
      (cyclicScaledResidue (Module.finrank K L)
        (cyclicGaloisRestrictionOrientation K L M).val
        (cyclicGaloisExponent K M sigma))
      (cyclicScaledResidue (Module.finrank K L)
        (cyclicGaloisRestrictionOrientation K L M).val
        (cyclicGaloisExponent K M tau)) • x
  let Q : (Rep.ofAlgebraAutOnUnits K M) :=
    ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M *
      cyclicCarry (Module.finrank K M)
        (cyclicGaloisExponent K M sigma) (cyclicGaloisExponent K M tau)) • x
  have hx' : Fi + Fj + Cn = Fs + Q := by
    exact hx
  change Fj - Fs + Fi = Q - Cn
  rw [eq_sub_iff_add_eq]
  rw [show Fj - Fs + Fi + Cn = (Fi + Fj + Cn) - Fs by abel]
  rw [sub_eq_iff_eq_add]
  exact hx'.trans (add_comm Fs Q)

/-- Genuine group-cohomological inflation sends an explicit carry class to the corrected upper
carry class with parameter multiplied by `orientation * [M : L]`. -/
theorem cyclicGaloisCarryH2Class_inflation
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] (a : Additive Kˣ) :
    (groupCohomology.map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
        (galoisTowerUnitsRepresentationHom K L M) 2).hom
        (cyclicGaloisCarryH2Class K L a) =
      cyclicGaloisCarryH2Class K M
        (((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M) • a) := by
  rw [cyclicGaloisCarryH2Class, cyclicGaloisCarryH2Class]
  rw [groupCohomology.H2π_comp_map_apply]
  exact (cyclicGaloisCarryCocycle_inflation_eq K L M a).symm

/-- Zero base parameter produces the zero carry cocycle. -/
theorem cyclicGaloisCarryCocycle_zero
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] :
    cyclicGaloisCarryCocycle K L 0 = 0 := by
  ext sigma tau
  change cyclicGaloisCarryFactor K L 0 (sigma, tau) = 0
  simp [cyclicGaloisCarryFactor]
  rfl

/-- Carry cocycles are additive in their base parameter. -/
theorem cyclicGaloisCarryCocycle_add
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (a b : Additive Kˣ) :
    cyclicGaloisCarryCocycle K L (a + b) =
      cyclicGaloisCarryCocycle K L a + cyclicGaloisCarryCocycle K L b := by
  ext sigma tau
  change cyclicGaloisCarryFactor K L (a + b) (sigma, tau) =
    cyclicGaloisCarryFactor K L a (sigma, tau) +
      cyclicGaloisCarryFactor K L b (sigma, tau)
  simp [cyclicGaloisCarryFactor, nsmul_add]
  rfl

/-- Zero base parameter produces the zero carry class. -/
theorem cyclicGaloisCarryH2Class_zero
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] :
    cyclicGaloisCarryH2Class K L 0 = 0 := by
  rw [cyclicGaloisCarryH2Class, cyclicGaloisCarryCocycle_zero]
  exact map_zero _

/-- Carry `H²` classes are additive in their base parameter. -/
theorem cyclicGaloisCarryH2Class_add
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (a b : Additive Kˣ) :
    cyclicGaloisCarryH2Class K L (a + b) =
      cyclicGaloisCarryH2Class K L a + cyclicGaloisCarryH2Class K L b := by
  rw [cyclicGaloisCarryH2Class, cyclicGaloisCarryCocycle_add]
  exact map_add _ _ _

/-- Additive base-unit map represented by the explicit cyclic carry cocycle. -/
noncomputable def cyclicGaloisCarryH2ClassHom
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] :
    Additive Kˣ →+ cyclicGaloisH2 K L where
  toFun := cyclicGaloisCarryH2Class K L
  map_zero' := cyclicGaloisCarryH2Class_zero K L
  map_add' := cyclicGaloisCarryH2Class_add K L

/-- Difference between the periodic-resolution base projection and the explicit carry-class map. -/
noncomputable def cyclicGaloisH2CarryComparisonDefect
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] :
    Additive Kˣ →+ cyclicGaloisH2 K L :=
  cyclicGaloisH2BaseProjection K L - cyclicGaloisCarryH2ClassHom K L

/-- Pointwise formula for the periodic-to-carry comparison defect. -/
theorem cyclicGaloisH2CarryComparisonDefect_apply
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (a : Additive Kˣ) :
    cyclicGaloisH2CarryComparisonDefect K L a =
      cyclicGaloisH2BaseProjection K L a - cyclicGaloisCarryH2Class K L a := rfl

/-- Actual inflation defect of the periodic base projection is exactly failure of the
periodic-to-carry comparison defect to commute with the explicit carry transition. -/
theorem cyclicGaloisH2Inflation_baseProjection_defect_eq_carryComparison
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] (a : Additive Kˣ) :
    (groupCohomology.map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
        (galoisTowerUnitsRepresentationHom K L M) 2).hom
          (cyclicGaloisH2BaseProjection K L a) -
        cyclicGaloisH2BaseProjection K M
          (((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M) • a) =
      (groupCohomology.map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
        (galoisTowerUnitsRepresentationHom K L M) 2).hom
          (cyclicGaloisH2CarryComparisonDefect K L a) -
        cyclicGaloisH2CarryComparisonDefect K M
          (((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M) • a) := by
  rw [cyclicGaloisH2CarryComparisonDefect_apply,
    cyclicGaloisH2CarryComparisonDefect_apply, map_sub,
    cyclicGaloisCarryH2Class_inflation]
  abel

/-- The gap between actual cohomological inflation and the oriented norm-quotient transition,
evaluated on every base parameter, is precisely the periodic-to-carry comparison mismatch. -/
theorem cyclicGaloisH2Inflation_orientedTransition_defect_eq_carryComparison
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] (a : Additive Kˣ) :
    (groupCohomology.map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
        (galoisTowerUnitsRepresentationHom K L M) 2).hom
          (cyclicGaloisH2BaseProjection K L a) -
        cyclicGaloisH2OrientedNormQuotientTransition K L M
          (cyclicGaloisH2BaseProjection K L a) =
      (groupCohomology.map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
        (galoisTowerUnitsRepresentationHom K L M) 2).hom
          (cyclicGaloisH2CarryComparisonDefect K L a) -
        cyclicGaloisH2CarryComparisonDefect K M
          (((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M) • a) := by
  rw [cyclicGaloisH2OrientedNormQuotientTransition_baseProjection]
  exact cyclicGaloisH2Inflation_baseProjection_defect_eq_carryComparison K L M a

end
end GaloisForLFunctions.HTGeometry.ABHN
