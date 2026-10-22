import Mathlib

/-!
# Weil--Arakelov mapping fiber for Deninger arithmetic cohomology

Flach--Morin's exact bridge identifies Weil--Arakelov cohomology at weight `n` with the
homotopy fiber of `Theta - n` on Deninger's dynamical cochain complex.  For a three-term
leafwise complex, that fiber is the four-term complex formalized here.

This module proves only the forced homological algebra.  It assumes neither a zeta-zero
description nor positivity nor the Riemann hypothesis.
-/

namespace RHTower

section WeilArakelovFiber

variable {R A0 A1 A2 : Type*}
variable [CommRing R]
variable [AddCommGroup A0] [Module R A0]
variable [AddCommGroup A1] [Module R A1]
variable [AddCommGroup A2] [Module R A2]

/-- Degree-zero differential of the mapping fiber of a chain endomorphism. -/
def deningerWeilArakelovD0
    (d0 : A0 →ₗ[R] A1) (vertical0 : A0 →ₗ[R] A0) :
    A0 →ₗ[R] A1 × A0 :=
  d0.prod vertical0

/-- Degree-one differential of the mapping fiber of a chain endomorphism. -/
def deningerWeilArakelovD1
    (d0 : A0 →ₗ[R] A1)
    (d1 : A1 →ₗ[R] A2)
    (vertical1 : A1 →ₗ[R] A1) :
    A1 × A0 →ₗ[R] A2 × A1 where
  toFun x := (d1 x.1, vertical1 x.1 - d0 x.2)
  map_add' x y := by
    apply Prod.ext
    · simp
    · simp only [Prod.fst_add, Prod.snd_add, map_add]
      abel
  map_smul' c x := by
    ext
    · simp
    · simp only [Prod.smul_fst, Prod.smul_snd, map_smul]
      exact (smul_sub c (vertical1 x.1) (d0 x.2)).symm

/-- Degree-two differential of the mapping fiber of a chain endomorphism. -/
def deningerWeilArakelovD2
    (d1 : A1 →ₗ[R] A2) (vertical2 : A2 →ₗ[R] A2) :
    A2 × A1 →ₗ[R] A2 where
  toFun x := vertical2 x.1 - d1 x.2
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul]
    exact (smul_sub c (vertical2 x.1) (d1 x.2)).symm

@[simp]
theorem deningerWeilArakelovD0_apply
    (d0 : A0 →ₗ[R] A1) (vertical0 : A0 →ₗ[R] A0) (x : A0) :
    deningerWeilArakelovD0 d0 vertical0 x = (d0 x, vertical0 x) :=
  rfl

@[simp]
theorem deningerWeilArakelovD1_apply
    (d0 : A0 →ₗ[R] A1)
    (d1 : A1 →ₗ[R] A2)
    (vertical1 : A1 →ₗ[R] A1)
    (x : A1 × A0) :
    deningerWeilArakelovD1 d0 d1 vertical1 x =
      (d1 x.1, vertical1 x.1 - d0 x.2) :=
  rfl

@[simp]
theorem deningerWeilArakelovD2_apply
    (d1 : A1 →ₗ[R] A2) (vertical2 : A2 →ₗ[R] A2)
    (x : A2 × A1) :
    deningerWeilArakelovD2 d1 vertical2 x =
      vertical2 x.1 - d1 x.2 :=
  rfl

/--
The first two mapping-fiber differentials compose to zero when the horizontal maps form a
complex and the vertical endomorphism commutes with the first horizontal differential.
-/
theorem deningerWeilArakelovD1_comp_D0
    (d0 : A0 →ₗ[R] A1)
    (d1 : A1 →ₗ[R] A2)
    (vertical0 : A0 →ₗ[R] A0)
    (vertical1 : A1 →ₗ[R] A1)
    (hcomplex : d1.comp d0 = 0)
    (hcomm0 : vertical1.comp d0 = d0.comp vertical0) :
    (deningerWeilArakelovD1 d0 d1 vertical1).comp
        (deningerWeilArakelovD0 d0 vertical0) = 0 := by
  apply LinearMap.ext
  intro x
  have hdx := LinearMap.congr_fun hcomplex x
  have hcommx := LinearMap.congr_fun hcomm0 x
  ext
  · exact hdx
  · change vertical1 (d0 x) - d0 (vertical0 x) = 0
    exact sub_eq_zero.mpr hcommx

/--
The last two mapping-fiber differentials compose to zero when the horizontal maps form a
complex and the vertical endomorphism commutes with the second horizontal differential.
-/
theorem deningerWeilArakelovD2_comp_D1
    (d0 : A0 →ₗ[R] A1)
    (d1 : A1 →ₗ[R] A2)
    (vertical1 : A1 →ₗ[R] A1)
    (vertical2 : A2 →ₗ[R] A2)
    (hcomplex : d1.comp d0 = 0)
    (hcomm1 : vertical2.comp d1 = d1.comp vertical1) :
    (deningerWeilArakelovD2 d1 vertical2).comp
        (deningerWeilArakelovD1 d0 d1 vertical1) = 0 := by
  apply LinearMap.ext
  intro x
  have hdx := LinearMap.congr_fun hcomplex x.2
  have hcommx := LinearMap.congr_fun hcomm1 x.1
  have hdx' : d1 (d0 x.2) = 0 := by
    simpa using hdx
  have hcommx' : vertical2 (d1 x.1) = d1 (vertical1 x.1) := by
    simpa using hcommx
  change vertical2 (d1 x.1) - d1 (vertical1 x.1 - d0 x.2) = 0
  rw [map_sub, hcommx', hdx', sub_zero, sub_self]

/-- Bottom cocycles are simultaneous horizontal cocycles and vertical invariants. -/
theorem deningerWeilArakelov_ker_D0
    (d0 : A0 →ₗ[R] A1) (vertical0 : A0 →ₗ[R] A0) :
    LinearMap.ker (deningerWeilArakelovD0 d0 vertical0) =
      LinearMap.ker d0 ⊓ LinearMap.ker vertical0 := by
  ext x
  simp [deningerWeilArakelovD0]

/-- Degree-one cocycles satisfy the horizontal cocycle and transgression equations. -/
theorem deningerWeilArakelov_mem_ker_D1
    (d0 : A0 →ₗ[R] A1)
    (d1 : A1 →ₗ[R] A2)
    (vertical1 : A1 →ₗ[R] A1)
    (x : A1 × A0) :
    x ∈ LinearMap.ker (deningerWeilArakelovD1 d0 d1 vertical1) ↔
      d1 x.1 = 0 ∧ vertical1 x.1 = d0 x.2 := by
  simp [deningerWeilArakelovD1, sub_eq_zero]

/-- Degree-two cocycles satisfy the final transgression equation. -/
theorem deningerWeilArakelov_mem_ker_D2
    (d1 : A1 →ₗ[R] A2) (vertical2 : A2 →ₗ[R] A2)
    (x : A2 × A1) :
    x ∈ LinearMap.ker (deningerWeilArakelovD2 d1 vertical2) ↔
      vertical2 x.1 = d1 x.2 := by
  simp [deningerWeilArakelovD2, sub_eq_zero]

/-- Top coboundaries are the sum of the vertical and final horizontal images. -/
theorem deningerWeilArakelov_range_D2
    (d1 : A1 →ₗ[R] A2) (vertical2 : A2 →ₗ[R] A2) :
    LinearMap.range (deningerWeilArakelovD2 d1 vertical2) =
      LinearMap.range vertical2 ⊔ LinearMap.range d1 := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [Submodule.mem_sup]
    refine ⟨vertical2 x.1, ⟨x.1, rfl⟩,
      -d1 x.2, ⟨-x.2, by simp⟩, ?_⟩
    rw [deningerWeilArakelovD2_apply]
    exact (sub_eq_add_neg _ _).symm
  · rw [Submodule.mem_sup]
    rintro ⟨u, ⟨z, rfl⟩, v, ⟨y, rfl⟩, huv⟩
    refine ⟨(z, -y), ?_⟩
    simp only [deningerWeilArakelovD2_apply, map_neg, sub_neg_eq_add]
    exact huv

end WeilArakelovFiber

end RHTower
