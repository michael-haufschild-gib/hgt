import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.PELLevels.LatticeLevelCRT
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! Projectivity and rank of a PEL lattice over the ring of integers of its coefficient field. -/

noncomputable section

open NumberField TensorProduct

namespace GlobalTheory.UPel.HT.EtLev

variable {p : ℕ} [Fact p.Prime]

/-- A finite integral PEL lattice is projective over the coefficient ring. -/
theorem projective_La_int (D : Datum p) :
    letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
    Module.Projective (𝓞 D.F) D.La := by
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  haveI := D.freeLa
  haveI := D.finLa
  have htor : Submodule.torsion (𝓞 D.F) D.La = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    have ha0 : (a : 𝓞 D.F) ≠ 0 := nonZeroDivisors.ne_zero a.2
    have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) ha0 (Ideal.mem_span_singleton_self (a : 𝓞 D.F))
      (Algebra.IsIntegral.isIntegral (R := ℤ) (a : 𝓞 D.F))
    obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at he
    obtain ⟨d, hd⟩ := he
    have h1 : e • x = 0 := by
      have : (algebraMap ℤ (𝓞 D.F) e) • x = e • x := by
        rw [algebraMap_smul]
      rw [← this, ← hd, mul_smul]
      change d • (a • x) = 0
      rw [hax, smul_zero]
    rcases smul_eq_zero.1 h1 with h | h
    · exact absurd h he0
    · exact (Submodule.mem_bot _).2 h
  haveI : Module.Finite (𝓞 D.F) D.La := Module.Finite.of_restrictScalars_finite ℤ (𝓞 D.F) D.La
  have : Module.Flat (𝓞 D.F) D.La := (IsDedekindDomain.flat_iff_torsion_eq_bot).2 htor
  have := Module.finitePresentation_of_finite (𝓞 D.F) D.La
  exact Module.Flat.projective_of_finitePresentation

/-- Localizing the lattice at the nonzero integers gives the same vector space as extending to the coefficient field. -/
theorem finrank_La_ringOfIntegers (D : Datum p) :
    letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
    Module.finrank (𝓞 D.F) D.La = D.m * D.n := by
  let A := 𝓞 D.F
  letI : Module A D.La := Module.compHom D.La (algebraMap A D.O)
  let V := D.F ⊗[A] D.La
  let u : D.La →ₗ[A] V := TensorProduct.mk A D.F D.La 1
  haveI : Module ℚ V := inferInstanceAs (Module ℚ (D.F ⊗[A] D.La))
  haveI : IsScalarTower ℚ D.F V := inferInstanceAs (IsScalarTower ℚ D.F (D.F ⊗[A] D.La))
  have hu : IsBaseChange D.F u := TensorProduct.isBaseChange A D.La D.F
  let P := nonZeroDivisors ℤ
  haveI : IsLocalizedModule (Algebra.algebraMapSubmonoid A P) u :=
    (isLocalizedModule_iff_isBaseChange _ D.F u).2 hu
  haveI : IsLocalizedModule P (u.restrictScalars ℤ) := IsLocalizedModule.restrictScalars _ u
  have hQ : Module.finrank ℚ V = Module.finrank ℤ D.La :=
    (congrArg Cardinal.toNat (IsLocalization.rank_eq ℚ P (N := V) le_rfl)).trans
      (IsLocalizedModule.finrank_eq P (u.restrictScalars ℤ) le_rfl)
  apply Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := ℚ) (M := D.F))
  calc
    Module.finrank ℚ D.F * Module.finrank A D.La =
      Module.finrank ℚ D.F * Module.finrank D.F V := by rw [hu.finrank_eq]
    _ = Module.finrank ℚ V := Module.finrank_mul_finrank ℚ D.F V
    _ = Module.finrank ℚ D.F * (D.m * D.n) := hQ.trans (D.rankLa.trans (Nat.mul_comm _ _))

end GlobalTheory.UPel.HT.EtLev
