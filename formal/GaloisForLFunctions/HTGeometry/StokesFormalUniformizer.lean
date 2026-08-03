import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Exact formal uniformizers for ramified Stokes coordinates

For every positive ramification index `E` and normalized unit `u ∈ ℂ⟦X⟧`, this module
constructs the canonical binomial root `u^(1/E)` and the tangent coordinate
`s = X u^(1/E)`.  It proves `s^E = X^E u`, constructs mutually inverse substitutions
on formal power series, and extends them across `X`-localization to a genuine
`ℂ`-algebra automorphism of Laurent series.  Thus any normalized order-`E` coordinate
of the displayed form is not merely order-equivalent to `X^E`: it is exactly the image
of `X^E` under an invertible formal reparametrization.
-/

open scoped PowerSeries

namespace GaloisForLFunctions.IrregularStokes.FormalUniformizer

noncomputable section

theorem binomialSeries_pow (r : ℚ) : ∀ n : ℕ,
    (PowerSeries.binomialSeries ℂ r) ^ n =
      PowerSeries.binomialSeries ℂ ((n : ℚ) * r)
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ, binomialSeries_pow]
      rw [← PowerSeries.binomialSeries_add]
      congr 2
      push_cast
      ring

def unitNthRoot (E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1) : PowerSeries ℂ :=
  let hsub : PowerSeries.HasSubst (u - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hu])
  PowerSeries.substAlgHom hsub
    (PowerSeries.binomialSeries ℂ (1 / (E : ℚ)))

theorem unitNthRoot_pow {E : ℕ} (hE : 0 < E) (u : PowerSeries ℂ)
    (hu : u.constantCoeff = 1) : (unitNthRoot E u hu) ^ E = u := by
  let hsub : PowerSeries.HasSubst (u - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hu])
  change (PowerSeries.substAlgHom hsub
    (PowerSeries.binomialSeries ℂ (1 / (E : ℚ)))) ^ E = u
  rw [← map_pow, binomialSeries_pow]
  have hrat : (E : ℚ) * (1 / (E : ℚ)) = 1 := by
    field_simp
  rw [hrat]
  rw [show PowerSeries.binomialSeries ℂ (1 : ℚ) =
      (1 + PowerSeries.X : PowerSeries ℂ) by
    simpa using PowerSeries.binomialSeries_nat (A := ℂ) (R := ℚ) 1]
  simp [PowerSeries.substAlgHom_X]

theorem unitNthRoot_constantCoeff (E : ℕ) (u : PowerSeries ℂ)
    (hu : u.constantCoeff = 1) : (unitNthRoot E u hu).constantCoeff = 1 := by
  let hsub : PowerSeries.HasSubst (u - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hu])
  change (PowerSeries.substAlgHom hsub
    (PowerSeries.binomialSeries ℂ (1 / (E : ℚ)))).constantCoeff = 1
  let b : PowerSeries ℂ := PowerSeries.binomialSeries ℂ (1 / (E : ℚ))
  have hb : b.constantCoeff = 1 := by simp [b]
  have hb0 : (b - 1).constantCoeff = 0 := by simp [hb]
  have ha0 : (u - 1).constantCoeff = 0 := by simp [hu]
  have hz := PowerSeries.constantCoeff_subst_eq_zero ha0 (b - 1) hb0
  have hz' : MvPowerSeries.constantCoeff
      (PowerSeries.substAlgHom hsub (b - 1)) = 0 := by
    rw [PowerSeries.coe_substAlgHom]
    exact hz
  have hdecomp : b = 1 + (b - 1) := by ring
  rw [show PowerSeries.binomialSeries ℂ (1 / (E : ℚ)) = b by rfl, hdecomp, map_add, map_one]
  rw [map_add, map_one, hz', add_zero]

def tangentUniformizer (E : ℕ) (u : PowerSeries ℂ)
    (hu : u.constantCoeff = 1) : PowerSeries ℂ :=
  PowerSeries.X * unitNthRoot E u hu

theorem tangentUniformizer_constantCoeff (E : ℕ) (u : PowerSeries ℂ)
    (hu : u.constantCoeff = 1) :
    (tangentUniformizer E u hu).constantCoeff = 0 := by
  simp [tangentUniformizer]

theorem tangentUniformizer_coeff_one (E : ℕ) (u : PowerSeries ℂ)
    (hu : u.constantCoeff = 1) :
    PowerSeries.coeff 1 (tangentUniformizer E u hu) = 1 := by
  simp [tangentUniformizer, unitNthRoot_constantCoeff]

theorem tangentUniformizer_pow {E : ℕ} (hE : 0 < E) (u : PowerSeries ℂ)
    (hu : u.constantCoeff = 1) :
    (tangentUniformizer E u hu) ^ E = PowerSeries.X ^ E * u := by
  rw [tangentUniformizer, mul_pow, unitNthRoot_pow hE u hu]

def tangentSubstitution (E : ℕ) (u : PowerSeries ℂ)
    (hu : u.constantCoeff = 1) : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ :=
  PowerSeries.substAlgHom
    (PowerSeries.HasSubst.of_constantCoeff_zero'
      (tangentUniformizer_constantCoeff E u hu))

def inverseTangentSeries (E : ℕ) (u : PowerSeries ℂ)
    (hu : u.constantCoeff = 1) : PowerSeries ℂ :=
  (tangentUniformizer E u hu).substInvOfIsUnit
    (by rw [tangentUniformizer_coeff_one E u hu]; exact isUnit_one)

theorem inverseTangentSeries_constantCoeff (E : ℕ) (u : PowerSeries ℂ)
    (hu : u.constantCoeff = 1) :
    (inverseTangentSeries E u hu).constantCoeff = 0 := by
  simp [inverseTangentSeries]

def inverseTangentSubstitution (E : ℕ) (u : PowerSeries ℂ)
    (hu : u.constantCoeff = 1) : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ :=
  PowerSeries.substAlgHom
    (PowerSeries.HasSubst.of_constantCoeff_zero'
      (inverseTangentSeries_constantCoeff E u hu))

theorem tangentSubstitution_inverseTangentSubstitution
    (E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1) :
    (tangentSubstitution E u hu).comp (inverseTangentSubstitution E u hu) =
      AlgHom.id ℂ (PowerSeries ℂ) := by
  apply AlgHom.ext
  intro f
  simp only [AlgHom.comp_apply, AlgHom.id_apply, tangentSubstitution,
    inverseTangentSubstitution]
  rw [PowerSeries.coe_substAlgHom, PowerSeries.coe_substAlgHom]
  rw [PowerSeries.subst_comp_subst_apply]
  · rw [show (inverseTangentSeries E u hu).subst (tangentUniformizer E u hu) =
        PowerSeries.X by
      exact PowerSeries.subst_substInvOfIsUnit_left
        (tangentUniformizer E u hu)
        (tangentUniformizer_constantCoeff E u hu)
        (by rw [tangentUniformizer_coeff_one E u hu]; exact isUnit_one)]
    exact PowerSeries.X_subst f
  · exact PowerSeries.HasSubst.of_constantCoeff_zero'
      (inverseTangentSeries_constantCoeff E u hu)
  · exact PowerSeries.HasSubst.of_constantCoeff_zero'
      (tangentUniformizer_constantCoeff E u hu)

theorem inverseTangentSubstitution_tangentSubstitution
    (E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1) :
    (inverseTangentSubstitution E u hu).comp (tangentSubstitution E u hu) =
      AlgHom.id ℂ (PowerSeries ℂ) := by
  apply AlgHom.ext
  intro f
  simp only [AlgHom.comp_apply, AlgHom.id_apply, tangentSubstitution,
    inverseTangentSubstitution]
  rw [PowerSeries.coe_substAlgHom, PowerSeries.coe_substAlgHom]
  rw [PowerSeries.subst_comp_subst_apply]
  · rw [show (tangentUniformizer E u hu).subst (inverseTangentSeries E u hu) =
        PowerSeries.X by
      exact PowerSeries.subst_substInvOfIsUnit_right
        (tangentUniformizer E u hu)
        (tangentUniformizer_constantCoeff E u hu)
        (by rw [tangentUniformizer_coeff_one E u hu]; exact isUnit_one)]
    exact PowerSeries.X_subst f
  · exact PowerSeries.HasSubst.of_constantCoeff_zero'
      (tangentUniformizer_constantCoeff E u hu)
  · exact PowerSeries.HasSubst.of_constantCoeff_zero'
      (inverseTangentSeries_constantCoeff E u hu)

def tangentReparametrization (E : ℕ) (u : PowerSeries ℂ)
    (hu : u.constantCoeff = 1) : PowerSeries ℂ ≃ₐ[ℂ] PowerSeries ℂ :=
  AlgEquiv.ofAlgHom (tangentSubstitution E u hu)
    (inverseTangentSubstitution E u hu)
    (tangentSubstitution_inverseTangentSubstitution E u hu)
    (inverseTangentSubstitution_tangentSubstitution E u hu)

@[simp] theorem tangentReparametrization_X (E : ℕ) (u : PowerSeries ℂ)
    (hu : u.constantCoeff = 1) :
    tangentReparametrization E u hu PowerSeries.X =
      tangentUniformizer E u hu := by
  change tangentSubstitution E u hu PowerSeries.X = tangentUniformizer E u hu
  exact PowerSeries.substAlgHom_X
    (PowerSeries.HasSubst.of_constantCoeff_zero'
      (tangentUniformizer_constantCoeff E u hu))

theorem powerSeries_X_associated_tangentUniformizer
    (E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1) :
    Associated PowerSeries.X (tangentUniformizer E u hu) := by
  let root := unitNthRoot E u hu
  have hrootUnit : IsUnit root := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    rw [show root.constantCoeff = 1 by
      exact unitNthRoot_constantCoeff E u hu]
    exact isUnit_one
  change Associated PowerSeries.X (PowerSeries.X * root)
  exact associated_mul_unit_right PowerSeries.X root hrootUnit

noncomputable instance tangentUniformizerAway
    (E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1) :
    IsLocalization.Away (tangentUniformizer E u hu) (LaurentSeries ℂ) :=
  IsLocalization.Away.of_associated
    (powerSeries_X_associated_tangentUniformizer E u hu)

theorem tangentReparametrization_powers
    (E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1) :
    Submonoid.map (tangentReparametrization E u hu).toRingEquiv.toMonoidHom
        (Submonoid.powers PowerSeries.X) =
      Submonoid.powers (tangentUniformizer E u hu) := by
  rw [Submonoid.map_powers]
  change Submonoid.powers
      (tangentReparametrization E u hu PowerSeries.X) =
    Submonoid.powers (tangentUniformizer E u hu)
  rw [tangentReparametrization_X]

def laurentReparametrization (E : ℕ) (u : PowerSeries ℂ)
    (hu : u.constantCoeff = 1) : LaurentSeries ℂ ≃+* LaurentSeries ℂ := by
  let e := tangentReparametrization E u hu
  have hmap : Submonoid.map e.toRingEquiv.toMonoidHom
      (Submonoid.powers PowerSeries.X) =
      Submonoid.powers (tangentUniformizer E u hu) :=
    tangentReparametrization_powers E u hu
  exact IsLocalization.ringEquivOfRingEquiv
    (LaurentSeries ℂ) (LaurentSeries ℂ) e.toRingEquiv hmap

theorem laurentReparametrization_coe (E : ℕ) (u : PowerSeries ℂ)
    (hu : u.constantCoeff = 1) (f : PowerSeries ℂ) :
    laurentReparametrization E u hu (f : LaurentSeries ℂ) =
      ((tangentReparametrization E u hu f : PowerSeries ℂ) : LaurentSeries ℂ) := by
  change laurentReparametrization E u hu
      (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) f) =
    algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)
      (tangentReparametrization E u hu f)
  unfold laurentReparametrization
  rw [IsLocalization.ringEquivOfRingEquiv_eq]
  rfl

theorem laurentReparametrization_X (E : ℕ) (u : PowerSeries ℂ)
    (hu : u.constantCoeff = 1) :
    laurentReparametrization E u hu
        ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ) =
      (tangentUniformizer E u hu : LaurentSeries ℂ) := by
  rw [laurentReparametrization_coe, tangentReparametrization_X]

theorem powerSeries_C_coe (c : ℂ) :
    ((PowerSeries.C c : PowerSeries ℂ) : LaurentSeries ℂ) =
      algebraMap ℂ (LaurentSeries ℂ) c := by
  rw [HahnSeries.algebraMap_apply']
  rfl

theorem laurentReparametrization_commutes
    (E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1) (c : ℂ) :
    laurentReparametrization E u hu (algebraMap ℂ (LaurentSeries ℂ) c) =
      algebraMap ℂ (LaurentSeries ℂ) c := by
  rw [← powerSeries_C_coe, laurentReparametrization_coe]
  have hc := (tangentReparametrization E u hu).commutes c
  simpa [PowerSeries.algebraMap_apply] using congrArg
    (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)) hc

def laurentAlgReparametrization (E : ℕ) (u : PowerSeries ℂ)
    (hu : u.constantCoeff = 1) : LaurentSeries ℂ ≃ₐ[ℂ] LaurentSeries ℂ :=
  { laurentReparametrization E u hu with
    commutes' := laurentReparametrization_commutes E u hu }

@[simp] theorem laurentAlgReparametrization_coe
    (E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1)
    (f : PowerSeries ℂ) :
    laurentAlgReparametrization E u hu (f : LaurentSeries ℂ) =
      ((tangentReparametrization E u hu f : PowerSeries ℂ) : LaurentSeries ℂ) :=
  laurentReparametrization_coe E u hu f

theorem laurentAlgReparametrization_X_pow
    {E : ℕ} (hE : 0 < E) (u : PowerSeries ℂ)
    (hu : u.constantCoeff = 1) :
    laurentAlgReparametrization E u hu
        ((PowerSeries.X ^ E : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((PowerSeries.X ^ E * u : PowerSeries ℂ) : LaurentSeries ℂ) := by
  rw [laurentAlgReparametrization_coe]
  change ((tangentReparametrization E u hu
      (PowerSeries.X ^ E) : PowerSeries ℂ) : LaurentSeries ℂ) = _
  rw [map_pow, tangentReparametrization_X,
    tangentUniformizer_pow hE u hu]

end
end GaloisForLFunctions.IrregularStokes.FormalUniformizer
