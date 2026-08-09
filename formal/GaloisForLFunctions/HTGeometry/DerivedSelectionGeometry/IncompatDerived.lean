import Mathlib
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.QuotientDerived
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.SourceOrientation
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.IdentityWall

/-!
# The derived dual and derived fibre of the incompatibility modules

The two-leg incompatibility module `Q = U ⧸ B_min` and the source orientation line
`Q_src = U ⧸ B_src` are quotients of free modules by a regular scalar, so their derived invariants
are computed by the presentation `R^n --(q-1)--> R^n`:

* `extOneIncompatIso` — `Ext¹(Q, R) ≅ Q`;
* `torOneIncompatIso` — `Tor₁(Q, R ⧸ I) ≅ (R ⧸ I)²`;
* `extOneSrcIso` — `Ext¹(Q_src, R) ≅ R ⧸ I`;
* `torOneSrcIso` — `Tor₁(Q_src, R ⧸ I) ≅ R ⧸ I`;
* `isZero_extIncompat_add_two`, `isZero_torIncompat_add_two`, and their source analogues — all
  higher derived groups vanish.

Over the universal monodromy line the identity fibre is the ground field, so the derived fibre of
`Q` is a two-dimensional and that of `Q_src` a one-dimensional `k`-vector space.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection

open CategoryTheory Limits Opposite TensorProduct

universe u v

section Regularity

variable {R : Type u} [CommRing R]

theorem isSMulRegular_prod {t : R} (h : IsSMulRegular R t) : IsSMulRegular (R × R) t := by
  intro a b hab
  exact Prod.ext (h (congrArg Prod.fst hab)) (h (congrArg Prod.snd hab))

theorem quotient_smul_eq_zero (t : R) (y : R ⧸ (Ideal.span {t} : Ideal R)) : t • y = 0 := by
  obtain ⟨x, rfl⟩ := (Ideal.span {t} : Ideal R).mkQ_surjective y
  have h : t • (Ideal.span {t} : Ideal R).mkQ x = (Ideal.span {t} : Ideal R).mkQ (t • x) := rfl
  rw [h, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
    Ideal.mem_span_singleton]
  exact ⟨x, rfl⟩

end Regularity

section HomIdentifications

variable (R : Type u) [CommRing R]

/-- `Hom_R(R, R) ≅ R`. -/
noncomputable def homSelfEquiv : (ModuleCat.of R R ⟶ ModuleCat.of R R) ≃ₗ[R] R :=
  (ModuleCat.homLinearEquiv (S := R)).trans (LinearMap.ringLmapEquivSelf R R R)

/-- `Hom_R(R², R) ≅ R²`. -/
noncomputable def homProdEquiv : (ModuleCat.of R (R × R) ⟶ ModuleCat.of R R) ≃ₗ[R] R × R :=
  (ModuleCat.homLinearEquiv (S := R)).trans
    (((LinearMap.coprodEquiv R).symm).trans
      ((LinearMap.ringLmapEquivSelf R R R).prodCongr (LinearMap.ringLmapEquivSelf R R R)))

end HomIdentifications

section TwoLeg

variable {R : Type u} [CommRing R] {q c : R}

theorem range_smul_id_eq_minStableBoundary (hc : IsUnit c) :
    LinearMap.range ((q - 1) • LinearMap.id : (R × R) →ₗ[R] (R × R)) = minStableBoundary q c :=
  range_wallSmul_eq_minStableBoundary q c hc

variable (hc : IsUnit c) (hreg : IsSMulRegular R (q - 1))
include hc hreg

/-- **Theorem 4.1 (4.2), `Ext` half.**  The derived dual of the two-leg incompatibility module is
the module itself: `Ext¹_R(Q, R) ≅ Q`. -/
noncomputable def extOneIncompatIso :
    ((Ext R (ModuleCat.{u} R) 1).obj (op (ModuleCat.of R (incompatModule q c)))).obj
        (ModuleCat.of R R)
      ≅ ModuleCat.of R (incompatModule q c) :=
  extOneSmulIso (range_smul_id_eq_minStableBoundary hc) (isSMulRegular_prod hreg)
      (ModuleCat.of R R) ≪≫
    (quotSmulRangeEquiv (q - 1) (homProdEquiv R)).toModuleIso ≪≫
    (Submodule.quotEquivOfEq _ _ (range_smul_id_eq_minStableBoundary hc)).toModuleIso

/-- **Theorem 4.1, higher `Ext` vanishing** for the two-leg module. -/
theorem isZero_extIncompat_add_two (Y : ModuleCat.{u} R) (n : ℕ) :
    IsZero (((Ext R (ModuleCat.{u} R) (n + 2)).obj
      (op (ModuleCat.of R (incompatModule q c)))).obj Y) :=
  isZero_extSmul_add_two (range_smul_id_eq_minStableBoundary hc) (isSMulRegular_prod hreg) Y n

/-- **Theorem 4.1 (4.2), `Tor` half.**  The derived identity fibre of the two-leg incompatibility
module has two legs: `Tor₁^R(Q, R ⧸ I) ≅ (R ⧸ I)²`. -/
noncomputable def torOneIncompatIso :
    (((Tor' (ModuleCat.{u} R) 1).obj (ModuleCat.of R (incompatModule q c))).obj
        (ModuleCat.of R (R ⧸ (Ideal.span {q - 1} : Ideal R))))
      ≅ ModuleCat.of R ((R ⧸ (Ideal.span {q - 1} : Ideal R)) ×
          (R ⧸ (Ideal.span {q - 1} : Ideal R))) :=
  torOneSmulIso (range_smul_id_eq_minStableBoundary hc) (isSMulRegular_prod hreg) _ ≪≫
    (LinearEquiv.ofEq _ ⊤ (ker_smul_id_eq_top (quotient_smul_eq_zero (q - 1)))).toModuleIso ≪≫
    (Submodule.topEquiv).toModuleIso ≪≫
    (TensorProduct.prodLeft R R R R (R ⧸ (Ideal.span {q - 1} : Ideal R))).toModuleIso ≪≫
    ((TensorProduct.lid R _).prodCongr (TensorProduct.lid R _)).toModuleIso

/-- **Theorem 4.1, higher `Tor` vanishing** for the two-leg module. -/
theorem isZero_torIncompat_add_two (Y : ModuleCat.{u} R) (n : ℕ) :
    IsZero ((((Tor' (ModuleCat.{u} R) (n + 2)).obj
      (ModuleCat.of R (incompatModule q c))).obj Y)) :=
  isZero_torSmul_add_two (range_smul_id_eq_minStableBoundary hc) (isSMulRegular_prod hreg) Y n

end TwoLeg

section Source

variable {R : Type u} [CommRing R] {S : Type u} [AddCommGroup S] [Module R S]
  {tauS : S →ₗ[R] S} {eps : S →ₗ[R] R} {q c : R}
  (hinv : ∀ x, eps (tauS x) = eps x) (heps : Function.Surjective eps)
  (hq : IsUnit q) (hc : IsUnit c) (hreg : IsSMulRegular R (q - 1))

include hinv heps hq hc hreg

/-- **Theorem 4A.1 (4A.9), `Ext` half.**  `Ext¹_R(Q_src, R) ≅ R ⧸ I`. -/
noncomputable def extOneSrcIso :
    ((Ext R (ModuleCat.{u} R) 1).obj
        (op (ModuleCat.of R (srcIncompatModule tauS eps q c)))).obj (ModuleCat.of R R)
      ≅ ModuleCat.of R (R ⧸ (Ideal.span {q - 1} : Ideal R)) :=
  extCongrLeft (srcIncompatEquiv hinv heps hq hc).toModuleIso 1 (ModuleCat.of R R) ≪≫
    extOneSmulIso (range_smul_id_eq_span (q - 1)) hreg (ModuleCat.of R R) ≪≫
    (quotSmulRangeEquiv (q - 1) (homSelfEquiv R)).toModuleIso ≪≫
    (Submodule.quotEquivOfEq _ _ (range_smul_id_eq_span (q - 1))).toModuleIso

/-- **Theorem 4A.1, higher `Ext` vanishing** for the source orientation line. -/
theorem isZero_extSrc_add_two (Y : ModuleCat.{u} R) (n : ℕ) :
    IsZero (((Ext R (ModuleCat.{u} R) (n + 2)).obj
      (op (ModuleCat.of R (srcIncompatModule tauS eps q c)))).obj Y) :=
  IsZero.of_iso
    (isZero_extSmul_add_two (range_smul_id_eq_span (q - 1)) hreg Y n)
    (extCongrLeft (srcIncompatEquiv hinv heps hq hc).toModuleIso (n + 2) Y)

/-- **Theorem 4A.1 (4A.9), `Tor` half.**  `Tor₁^R(Q_src, R ⧸ I) ≅ R ⧸ I`: the literal cyclic
source has a single derived orientation port. -/
noncomputable def torOneSrcIso :
    (((Tor' (ModuleCat.{u} R) 1).obj
        (ModuleCat.of R (srcIncompatModule tauS eps q c))).obj
        (ModuleCat.of R (R ⧸ (Ideal.span {q - 1} : Ideal R))))
      ≅ ModuleCat.of R (R ⧸ (Ideal.span {q - 1} : Ideal R)) :=
  torCongrLeft (srcIncompatEquiv hinv heps hq hc).toModuleIso 1 _ ≪≫
    torOneSmulIso (range_smul_id_eq_span (q - 1)) hreg _ ≪≫
    (LinearEquiv.ofEq _ ⊤ (ker_smul_id_eq_top (quotient_smul_eq_zero (q - 1)))).toModuleIso ≪≫
    (Submodule.topEquiv).toModuleIso ≪≫
    (TensorProduct.lid R (R ⧸ (Ideal.span {q - 1} : Ideal R))).toModuleIso

/-- **Theorem 4A.1, higher `Tor` vanishing** for the source orientation line. -/
theorem isZero_torSrc_add_two (Y : ModuleCat.{u} R) (n : ℕ) :
    IsZero ((((Tor' (ModuleCat.{u} R) (n + 2)).obj
      (ModuleCat.of R (srcIncompatModule tauS eps q c))).obj Y)) :=
  IsZero.of_iso
    (isZero_torSmul_add_two (range_smul_id_eq_span (q - 1)) hreg Y n)
    (torCongrLeft (srcIncompatEquiv hinv heps hq hc).toModuleIso (n + 2) Y)

end Source

section Monodromy

open LaurentPolynomial

variable (k : Type u) [Field k]

theorem monodromy_isSMulRegular :
    IsSMulRegular (MonodromyRing k) (monodromyParam k - 1) := by
  intro a b hab
  have h : (monodromyParam k - 1) * a = (monodromyParam k - 1) * b := hab
  exact mul_left_cancel₀ wallEquation_ne_zero h

/-- The identity fibre of the two-leg derived reader is a two-dimensional `k`-vector space. -/
noncomputable def identityFibreSqKEquiv :
    ((MonodromyRing k ⧸ identityIdeal k) × (MonodromyRing k ⧸ identityIdeal k)) ≃ₗ[k] k × k :=
  (identityFibreEquiv k).toLinearEquiv.prodCongr (identityFibreEquiv k).toLinearEquiv

/-- The identity fibre of the source derived reader is a one-dimensional `k`-vector space. -/
noncomputable def identityFibreKEquiv :
    (MonodromyRing k ⧸ identityIdeal k) ≃ₗ[k] k :=
  (identityFibreEquiv k).toLinearEquiv

end Monodromy

end GaloisForLFunctions.HTGeometry.DerivedSelection
