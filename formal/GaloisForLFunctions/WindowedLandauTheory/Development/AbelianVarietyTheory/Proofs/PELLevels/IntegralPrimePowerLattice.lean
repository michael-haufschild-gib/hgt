import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.PELLevels.LatticeCoefficientRank
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! Reduction of a PEL lattice modulo a power of a rational prime. -/

open scoped TensorProduct
open NumberField TensorProduct

namespace GlobalTheory.UPel.HT.EtLev

variable {p : ℕ} [Fact p.Prime]

/-- Localization over the rational prime makes the lattice free, and reduction preserves
its coefficient-field rank. -/
theorem latQuot_rational_prime_free (D : Datum p) (ℓ : ℕ) (hℓ : ℓ.Prime) (j : ℕ) :
    letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
    let I := Ideal.span {((ℓ ^ j : ℕ) : 𝓞 D.F)}
    Nonempty ((Fin (D.m * D.n) → 𝓞 D.F ⧸ I) ≃ₗ[𝓞 D.F ⧸ I]
      D.La ⧸ (I • ⊤ : Submodule (𝓞 D.F) D.La)) := by
  let A := 𝓞 D.F
  letI : Module A D.La := Module.compHom D.La (algebraMap A D.O)
  let I := Ideal.span {((ℓ ^ j : ℕ) : A)}
  change Nonempty ((Fin (D.m * D.n) → A ⧸ I) ≃ₗ[A ⧸ I] D.La ⧸ (I • ⊤ : Submodule A D.La))
  rcases Nat.eq_zero_or_pos j with hj | hj
  · have hI : I = ⊤ := by simp [I, hj]
    haveI : Subsingleton (A ⧸ I) := Ideal.Quotient.subsingleton_iff.mpr hI
    haveI : Subsingleton (D.La ⧸ (I • ⊤ : Submodule A D.La)) := by
      rw [hI, Submodule.top_smul]
      exact Submodule.Quotient.subsingleton_iff.mpr rfl
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  haveI := D.finLa
  haveI : Module.Finite A D.La := Module.Finite.of_restrictScalars_finite ℤ A D.La
  haveI : Module.Projective A D.La := projective_La_int D
  let P : Ideal ℤ := Ideal.span {(ℓ : ℤ)}
  haveI : P.IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hℓ.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hℓ)
  have hP : P ≠ ⊥ := by simp [P, hℓ.ne_zero]
  let T := Algebra.algebraMapSubmonoid A P.primeCompl
  let B := Localization T
  have hT : T ≤ nonZeroDivisors A := map_le_nonZeroDivisors_of_injective _
    (FaithfulSMul.algebraMap_injective ℤ A) P.primeCompl_le_nonZeroDivisors
  haveI : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors _ hT
  haveI : IsDedekindDomain B := IsLocalization.isDedekindDomain A hT _
  haveI : IsPrincipalIdealRing B := IsDedekindDomain.isPrincipalIdealRing_localization_over_prime A P hP
  have hunit : ∀ u : T, IsUnit (Ideal.Quotient.mk I (u : A)) := by
    rintro ⟨_, z, hz, rfl⟩
    have hz' : ¬ (ℓ : ℤ) ∣ z := fun hd => hz (Ideal.mem_span_singleton.mpr hd)
    have hc : IsCoprime z ((ℓ : ℤ) ^ j) :=
      (((Nat.prime_iff_prime_int.mp hℓ).irreducible.coprime_iff_not_dvd).mpr hz').symm.pow_right
    obtain ⟨u, v, huv⟩ := hc
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk I (u : A)) ?_
    have hmem : (((ℓ ^ j : ℕ) : A)) ∈ I := Ideal.mem_span_singleton_self _
    have h : (algebraMap ℤ A z) * (u : A) = 1 - (v : A) * ((ℓ ^ j : ℕ) : A) := by
      have e := congrArg (algebraMap ℤ A) huv
      rw [map_add, map_mul, map_mul, map_pow, map_natCast, map_one] at e
      rw [algebraMap_int_eq, Int.coe_castRingHom] at e ⊢
      rw [Nat.cast_pow]
      linear_combination e
    rw [← map_mul, h, map_sub, map_one, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, mul_zero, sub_zero]
  letI : Algebra B (A ⧸ I) := (IsLocalization.lift hunit).toAlgebra
  haveI : IsScalarTower A B (A ⧸ I) := IsScalarTower.of_algebraMap_eq fun c => by
    rw [RingHom.algebraMap_toAlgebra, IsLocalization.lift_eq, Ideal.Quotient.algebraMap_eq]
  haveI : Module.Flat B (B ⊗[A] D.La) := Module.Flat.baseChange _ _ _
  haveI : Module.IsTorsionFree B (B ⊗[A] D.La) := Module.Flat.isTorsionFree
  haveI : Module.Free B (B ⊗[A] D.La) := Module.free_of_finite_type_torsion_free'
  have hr : Module.finrank B (B ⊗[A] D.La) = D.m * D.n := by
    calc
      _ = Module.finrank A (B ⊗[A] D.La) :=
        congrArg Cardinal.toNat (IsLocalization.rank_eq B T hT)
      _ = Module.finrank A D.La := IsLocalizedModule.finrank_eq T (TensorProduct.mk A B D.La 1) hT
      _ = _ := finrank_La_ringOfIntegers D
  have hNorm : I.absNorm = (ℓ ^ j) ^ Module.finrank ℚ D.F := by
    dsimp only [I]
    rw [Ideal.absNorm_span_singleton]
    have he : ((ℓ ^ j : ℕ) : A) = algebraMap ℤ A ((ℓ ^ j : ℕ) : ℤ) := by simp
    rw [he, Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  haveI : Nontrivial (A ⧸ I) := by
    refine Ideal.Quotient.nontrivial_iff.mpr (fun h => ?_)
    have h₁ : 1 < ℓ ^ j := Nat.one_lt_pow hj.ne' hℓ.one_lt
    have h₂ : 1 < I.absNorm := by
      rw [hNorm]
      exact Nat.one_lt_pow Module.finrank_pos.ne' h₁
    rw [h, Ideal.absNorm_top] at h₂
    exact (lt_irrefl 1) h₂
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange A B (A ⧸ I) (A ⧸ I) D.La
  haveI : Module.Free (A ⧸ I) ((A ⧸ I) ⊗[A] D.La) := Module.Free.of_equiv e
  have hF : Module.finrank (A ⧸ I) ((A ⧸ I) ⊗[A] D.La) = D.m * D.n := by
    rw [← e.finrank_eq, Module.finrank_baseChange, hr]
  let e' : ((A ⧸ I) ⊗[A] D.La) ≃ₗ[A ⧸ I] D.La ⧸ (I • ⊤ : Submodule A D.La) :=
    (TensorProduct.quotTensorEquivQuotSMul D.La I).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective
  exact ⟨(Module.finBasisOfFinrankEq (A ⧸ I) _ hF).equivFun.symm.trans e'⟩

end GlobalTheory.UPel.HT.EtLev
