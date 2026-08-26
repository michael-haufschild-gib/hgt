import GaloisForLFunctions.HTGeometry.AffineExponentialInvariantKaehler

/-!
# Point-group law for mixed invariant Kähler pullback

For a fixed mixed invariant differential, point pullback is a homomorphism from the mixed point
group to the additive Kähler module.  This packages the multiplication, identity, inverse, and
generated-subgroup consequences used by translated-locus arguments.
-/

namespace GaloisForLFunctions.HTGeometry
namespace AffineExponentialInvariantKaehler

open AffineExponentialGroup AffineExponentialPointEvaluation

noncomputable section

theorem pointKaehlerMap_mixedInvariantKaehlerVector_mul
    {k L : Type*} [Field k] [Field L] [Algebra k L]
    {n : ℕ} (p q : Point L n) (tor add : Fin n → k) :
    pointKaehlerMap k (p * q) (mixedInvariantKaehlerVector k tor add) =
      pointKaehlerMap k p (mixedInvariantKaehlerVector k tor add) +
        pointKaehlerMap k q (mixedInvariantKaehlerVector k tor add) := by
  classical
  rw [pointKaehlerMap_mixedInvariantKaehlerVector,
    pointKaehlerMap_mixedInvariantKaehlerVector,
    pointKaehlerMap_mixedInvariantKaehlerVector]
  have hpos (r : Point L n) (i : Fin n) :
      (AlgebraicTorusCharacter.character
        (torusPart r) (Finsupp.single i 1) : L) = (torusPart r i : L) := by
    rw [AlgebraicTorusCharacter.character_single, zpow_one]
  have hneg (r : Point L n) (i : Fin n) :
      (AlgebraicTorusCharacter.character
        (torusPart r) (-(Finsupp.single i 1)) : L) = (torusPart r i : L)⁻¹ := by
    rw [AlgebraicTorusCharacter.character_neg, Units.val_inv_eq_inv_val, hpos]
  simp_rw [hpos, hneg, additivePart_mul, torusPart_mul]
  rw [add_add_add_comm]
  congr 1
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change ((algebraMap k L) (tor i) *
        ((torusPart p i : L) * (torusPart q i : L))⁻¹) •
          KaehlerDifferential.D k L
            ((torusPart p i : L) * (torusPart q i : L)) = _
    rw [Derivation.leibniz, smul_add, smul_smul, smul_smul]
    have hp : (torusPart p i : L) ≠ 0 := Units.ne_zero _
    have hq : (torusPart q i : L) ≠ 0 := Units.ne_zero _
    field_simp
    module
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change (algebraMap k L) (add i) • KaehlerDifferential.D k L
      (additivePart p i + additivePart q i) = _
    rw [map_add, smul_add]

theorem pointKaehlerMap_mixedInvariantKaehlerVector_one
    {k L : Type*} [Field k] [Field L] [Algebra k L]
    {n : ℕ} (tor add : Fin n → k) :
    pointKaehlerMap k (1 : Point L n) (mixedInvariantKaehlerVector k tor add) = 0 := by
  have h := pointKaehlerMap_mixedInvariantKaehlerVector_mul
    (k := k) (1 : Point L n) 1 tor add
  simp only [one_mul] at h
  have hsub := congrArg
    (fun z : Ω[L⁄k] => z - pointKaehlerMap k (1 : Point L n)
      (mixedInvariantKaehlerVector k tor add)) h
  simpa only [sub_self, add_sub_cancel_left] using hsub.symm

/-- Point pullback of a fixed mixed invariant differential is a group homomorphism to the
additive Kähler module. -/
noncomputable def mixedInvariantPointPullbackHom
    {k L : Type*} [Field k] [Field L] [Algebra k L]
    {n : ℕ} (tor add : Fin n → k) :
    Point L n →* Multiplicative Ω[L⁄k] where
  toFun p := Multiplicative.ofAdd
    (pointKaehlerMap k p (mixedInvariantKaehlerVector k tor add))
  map_one' := by
    change Multiplicative.ofAdd
      (pointKaehlerMap k (1 : Point L n)
        (mixedInvariantKaehlerVector k tor add)) = Multiplicative.ofAdd 0
    rw [pointKaehlerMap_mixedInvariantKaehlerVector_one]
  map_mul' p q := by
    change Multiplicative.ofAdd
      (pointKaehlerMap k (p * q) (mixedInvariantKaehlerVector k tor add)) =
        Multiplicative.ofAdd
          (pointKaehlerMap k p (mixedInvariantKaehlerVector k tor add) +
            pointKaehlerMap k q (mixedInvariantKaehlerVector k tor add))
    rw [pointKaehlerMap_mixedInvariantKaehlerVector_mul]

@[simp] theorem mixedInvariantPointPullbackHom_apply
    {k L : Type*} [Field k] [Field L] [Algebra k L]
    {n : ℕ} (tor add : Fin n → k) (p : Point L n) :
    mixedInvariantPointPullbackHom tor add p = Multiplicative.ofAdd
      (pointKaehlerMap k p (mixedInvariantKaehlerVector k tor add)) := rfl

theorem pointKaehlerMap_mixedInvariantKaehlerVector_mul_inv_eq_zero
    {k L : Type*} [Field k] [Field L] [Algebra k L]
    {n : ℕ} (p q : Point L n) (tor add : Fin n → k)
    (hp : pointKaehlerMap k p (mixedInvariantKaehlerVector k tor add) = 0)
    (hq : pointKaehlerMap k q (mixedInvariantKaehlerVector k tor add) = 0) :
    pointKaehlerMap k (p * q⁻¹) (mixedInvariantKaehlerVector k tor add) = 0 := by
  let Φ : Point L n →* Multiplicative Ω[L⁄k] :=
    mixedInvariantPointPullbackHom tor add
  have hp' : Φ p = 1 := by
    change Multiplicative.ofAdd
      (pointKaehlerMap k p (mixedInvariantKaehlerVector k tor add)) =
        Multiplicative.ofAdd 0
    rw [hp]
  have hq' : Φ q = 1 := by
    change Multiplicative.ofAdd
      (pointKaehlerMap k q (mixedInvariantKaehlerVector k tor add)) =
        Multiplicative.ofAdd 0
    rw [hq]
  have hprod : Φ (p * q⁻¹) = 1 := by
    rw [map_mul, map_inv, hp', hq', inv_one, mul_one]
  change Multiplicative.ofAdd
    (pointKaehlerMap k (p * q⁻¹) (mixedInvariantKaehlerVector k tor add)) =
      Multiplicative.ofAdd 0 at hprod
  exact congrArg Multiplicative.toAdd hprod

/-- A point set on which an invariant pullback vanishes generates a point subgroup contained in
the kernel of the pullback homomorphism. -/
theorem closure_le_ker_mixedInvariantPointPullbackHom
    {k L : Type*} [Field k] [Field L] [Algebra k L]
    {n : ℕ} (S : Set (Point L n)) (tor add : Fin n → k)
    (hS : ∀ p ∈ S,
      pointKaehlerMap k p (mixedInvariantKaehlerVector k tor add) = 0) :
    Subgroup.closure S ≤ (mixedInvariantPointPullbackHom tor add).ker := by
  rw [Subgroup.closure_le]
  intro p hp
  change Multiplicative.ofAdd
    (pointKaehlerMap k p (mixedInvariantKaehlerVector k tor add)) =
      Multiplicative.ofAdd 0
  rw [hS p hp]

end

end AffineExponentialInvariantKaehler
end GaloisForLFunctions.HTGeometry
