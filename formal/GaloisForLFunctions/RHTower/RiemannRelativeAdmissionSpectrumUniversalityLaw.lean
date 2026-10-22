import GaloisForLFunctions.HTGeometry.L2RelativeAdmissionSpectrum
import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittRelativeBoundaryTransgression
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmEulerReflectionAdmissionFracture

/-!
# Relative admission spectra across three Riemann-source routes

The abstract relative primitive obstruction becomes a parameter spectrum by recording where its
class vanishes.  This module instantiates that one construction in three independent carriers:

* the all-prime Calderón--Witt incidence complex;
* the Hedenmalm Borel reflection family in the fixed source `L²` space;
* the polarized Euler/Hardy reflection family in the same fixed `L²` presentation after absorbing
  its tail weight into the profile.

The Hedenmalm spectrum contains the centered open half-strip, while the Euler/Hardy spectrum is
the singleton zero.  Consequently no linear transport preserving the admitted `L²` sector can
intertwine these families on that strip.  This is an unconditional cross-route no-go; it does not
assert source-derived landing of Xi fibres in the sharp Euler/Hardy carrier.
-/

open Complex MeasureTheory Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Common admitted raw-profile sector used to compare the two analytic reflection sources. -/
def riemannProfileL2AdmissionSubmodule : Submodule ℂ (ℝ → ℂ) :=
  memLpTwoSubmodule (volume.restrict (Ioi (0 : ℝ)))

/-- Hedenmalm Borel reflection as an exact relative admission spectrum of the identity complex. -/
def hedenmalmBorelRelativeAdmissionSpectrum (x : ℝ) : Set ℝ :=
  relativeAdmissionSpectrum riemannProfileL2AdmissionSubmodule
    (LinearMap.id : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ)) LinearMap.id
    (fun a => hedenmalmBorelReflectionOddFun a x)

/-- Polarized Euler/Hardy reflection as the same relative admission construction. -/
def eulerPrimitiveRelativeAdmissionSpectrum : Set ℝ :=
  relativeAdmissionSpectrum riemannProfileL2AdmissionSubmodule
    (LinearMap.id : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ)) LinearMap.id
    eulerPrimitiveWeightedReflectionOddFun

theorem hedenmalmBorelRelativeAdmissionSpectrum_eq (x : ℝ) :
    hedenmalmBorelRelativeAdmissionSpectrum x =
      hedenmalmBorelReflectionAdmissionSpectrum x := by
  rw [hedenmalmBorelRelativeAdmissionSpectrum,
    riemannProfileL2AdmissionSubmodule,
    relativeAdmissionSpectrum_id_eq_memLp]
  rfl

theorem eulerPrimitiveRelativeAdmissionSpectrum_eq_singleton :
    eulerPrimitiveRelativeAdmissionSpectrum = {0} := by
  rw [eulerPrimitiveRelativeAdmissionSpectrum,
    riemannProfileL2AdmissionSubmodule,
    relativeAdmissionSpectrum_id_eq_memLp]
  ext a
  exact memLp_eulerPrimitiveWeightedReflectionOddFun_iff a

/-- The two analytic routes are inequivalent already as relative admission spectra. -/
theorem hedenmalmBorelRelativeAdmissionSpectrum_ne_eulerPrimitive (x : ℝ) :
    hedenmalmBorelRelativeAdmissionSpectrum x ≠
      eulerPrimitiveRelativeAdmissionSpectrum := by
  rw [hedenmalmBorelRelativeAdmissionSpectrum_eq,
    eulerPrimitiveRelativeAdmissionSpectrum_eq_singleton,
    ← eulerPrimitiveReflectionAdmissionSpectrum_eq_singleton]
  exact hedenmalmBorelReflectionAdmissionSpectrum_ne_eulerPrimitive x

/-- The all-prime Calderón--Witt source is the nontrivial-complex instance of the same spectrum. -/
def deningerCalderonWittGlobalRelativeAdmissionSpectrum
    {P : Type*}
    (S : Submodule ℂ deningerCalderonWittGlobalMilnorIncidence)
    (w : P → ⋀[ℂ]^(2 : ℕ) DeningerCalderonWittAlgebraicGlobalDegreeOne) : Set P :=
  relativeAdmissionSpectrum
    (R := ℂ)
    (A0 := deningerCalderonWittGlobalMilnorIncidence)
    (A1 := ⋀[ℂ]^(2 : ℕ) DeningerCalderonWittAlgebraicGlobalDegreeOne)
    S
    deningerCalderonWittGlobalMilnorIncidence.subtype
    deningerCalderonWittGlobalMilnorGreenRetraction w

/-- In the Deninger route, spectrum membership is exactly landing of the canonical Green
primitive in the admitted incidence sector. -/
theorem mem_deningerCalderonWittGlobalRelativeAdmissionSpectrum_iff
    {P : Type*}
    (S : Submodule ℂ deningerCalderonWittGlobalMilnorIncidence)
    (w : P → ⋀[ℂ]^(2 : ℕ) DeningerCalderonWittAlgebraicGlobalDegreeOne)
    (hcocycle : ∀ p, deningerCalderonWittAlgebraicGlobalExteriorCup (w p) = 0)
    (p : P) :
    p ∈ deningerCalderonWittGlobalRelativeAdmissionSpectrum S w ↔
      deningerCalderonWittGlobalMilnorGreenRetraction (w p) ∈ S := by
  simpa [deningerCalderonWittGlobalRelativeAdmissionSpectrum,
    relativeAdmissionSpectrum,
    deningerCalderonWittGlobalRelativeBoundaryClass] using
    deningerCalderonWittGlobalRelativeBoundaryClass_eq_zero_iff S (w p) (hcocycle p)

/-- **Cross-route singularity theorem.**  No linear operator preserving the common admitted
`L²` sector can carry the Hedenmalm reflection family to the sharp weighted Euler/Hardy family on
the centered open half-strip.  A bridge must be domain-singular or fail to intertwine the modular
profiles. -/
theorem no_l2AdmissionSectorTransport_hedenmalm_to_euler (x : ℝ) :
    ¬ ∃ T : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ),
      riemannProfileL2AdmissionSubmodule.map T ≤
          riemannProfileL2AdmissionSubmodule ∧
        ∀ a ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2),
          T (hedenmalmBorelReflectionOddFun a x) =
            eulerPrimitiveWeightedReflectionOddFun a := by
  rintro ⟨T, hsector, hintertwine⟩
  let a : ℝ := 1 / 4
  have ha : a ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    dsimp only [a]
    norm_num
  have hH : hedenmalmBorelReflectionOddFun a x ∈
      riemannProfileL2AdmissionSubmodule := by
    exact memLp_hedenmalmBorelReflectionOddFun (abs_lt.mpr ha) x
  have hmap : T (hedenmalmBorelReflectionOddFun a x) ∈
      riemannProfileL2AdmissionSubmodule :=
    hsector (Submodule.mem_map_of_mem hH)
  change MemLp (T (hedenmalmBorelReflectionOddFun a x)) 2
    (volume.restrict (Ioi (0 : ℝ))) at hmap
  rw [hintertwine a ha] at hmap
  have ha0 := (memLp_eulerPrimitiveWeightedReflectionOddFun_iff a).mp hmap
  norm_num [a] at ha0

end

end RHTower
