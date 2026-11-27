import GaloisForLFunctions.HTGeometry.PointsSeparate
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! A module of finite type supported at a rational point has dimension
over the base field equal to its length at that point. -/

open TensorProduct

namespace GlobalTheory.PointSupport

/-- The residue field of the localization at a rational point is the
coefficient field, with evaluation induced by the point. -/
theorem exists_residueEquiv_at_rational_point {K R O : Type} [Field K] [CommRing R]
    [Algebra K R] (χ : R →ₐ[K] K) [CommRing O] [Algebra R O] [IsLocalRing O]
    [(RingHom.ker χ.toRingHom).IsPrime] [IsLocalization.AtPrime O (RingHom.ker χ.toRingHom)] :
    ∃ e : IsLocalRing.ResidueField O ≃+* K,
      ∀ r : R, e (IsLocalRing.residue O (algebraMap R O r)) = χ r := by
  let q := RingHom.ker χ.toRingHom
  let f : O →+* K := IsLocalization.lift (M := q.primeCompl) (g := χ.toRingHom)
    (fun r => Ne.isUnit r.2)
  have hf : f.comp (algebraMap R O) = χ.toRingHom := IsLocalization.lift_comp _
  have h (r : R) : f (algebraMap R O r) = χ r :=
    congrArg (fun u : R →+* K => u r) hf
  have hs : Function.Surjective f :=
    fun k => ⟨algebraMap R O (algebraMap K R k), (h _).trans (χ.commutes k)⟩
  have hm := IsLocalRing.ker_eq_maximalIdeal f hs
  refine ⟨(Ideal.quotEquivOfEq hm.symm).trans (RingHom.quotientKerEquivOfSurjective hs), fun r => ?_⟩
  change RingHom.quotientKerEquivOfSurjective hs (Ideal.Quotient.mk _ (algebraMap R O r)) = χ r
  exact (RingHom.quotientKerEquivOfSurjective_apply_mk hs _).trans (h r)

/-- If the only possible closed point in the support is rational, localization
preserves the module and its length equals its dimension over the base field. -/
theorem finiteLength_and_finrank_eq_length {K R O H : Type}
    [Field K] [IsAlgClosed K] [CommRing R] [Algebra K R] [Algebra.FiniteType K R]
    (χ₀ : R →ₐ[K] K) [CommRing O] [Algebra R O] [(RingHom.ker χ₀).IsPrime]
    [IsLocalization.AtPrime O (RingHom.ker χ₀)] [AddCommGroup H] [Module R H] [Module K H]
    [IsScalarTower K R H] [Module.Finite R H]
    (hsupp : ∀ χ : R →ₐ[K] K, χ ≠ χ₀ → ∃ r : R, χ r ≠ 0 ∧ ∀ z : H, r • z = 0) :
    IsFiniteLength O (O ⊗[R] H) ∧ Module.Finite K H ∧
      (Module.finrank K H : ℕ∞) = Module.length O (O ⊗[R] H) := by
  classical
  let p := RingHom.ker χ₀
  let I := Module.annihilator R H
  letI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  letI hmaxp : p.IsMaximal := RingHom.ker_isMaximal_of_surjective χ₀.toRingHom
    (fun k => ⟨algebraMap K R k, χ₀.commutes k⟩)
  have hmax (J : Ideal R) (hJ : J.IsMaximal) (hle : I ≤ J) : J = p := by
    letI := hJ
    obtain ⟨χ, hχ⟩ := GaloisForLFunctions.HTGeometry.exists_algHom_ker_eq_of_isMaximal
      (C := K) J
    by_cases he : χ = χ₀
    · subst χ
      exact Ideal.ext fun r => (hχ r).symm
    · obtain ⟨r, hr, hz⟩ := hsupp χ he
      exact (hr ((hχ r).mpr (hle (Module.mem_annihilator.mpr hz)))).elim
  have hprime (Q : Ideal R) (hQ : Q.IsPrime) (hle : I ≤ Q) : Q = p := by
    rw [← IsJacobsonRing.out' Q hQ.isRadical]
    apply le_antisymm
    · obtain ⟨J, hJ, hQJ⟩ := Ideal.exists_le_maximal Q hQ.ne_top
      rw [← hmax J hJ (hle.trans hQJ)]
      exact sInf_le ⟨hQJ, hJ⟩
    · exact le_sInf fun J hJ => (hmax J hJ.2 (hle.trans hJ.1)).ge
  letI : Module (R ⧸ I) H := Module.quotientAnnihilator
  have hmk (r : R) (z : H) : Ideal.Quotient.mk I r • z = r • z := rfl
  letI : IsScalarTower R (R ⧸ I) H := ⟨fun r q z => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, hmk, hmk, mul_smul]⟩
  letI : IsScalarTower K (R ⧸ I) H := ⟨fun k q z => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, hmk, hmk, ← Algebra.smul_def,
      smul_assoc]⟩
  letI : Module.Finite (R ⧸ I) H := Module.Finite.of_restrictScalars_finite R _ H
  have hprimeq (Q : Ideal (R ⧸ I)) (hQ : Q.IsPrime) : Q.comap (Ideal.Quotient.mk I) = p := by
    refine hprime _ (Ideal.comap_isPrime _ Q) fun r hr => ?_
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hr]
    exact Q.zero_mem
  letI : Ring.KrullDimLE 0 (R ⧸ I) := Ring.KrullDimLE.mk₀ fun Q hQ => by
    rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q, hprimeq Q hQ]
    refine Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective ?_
    rw [Ideal.mk_ker, ← hprimeq Q hQ]
    intro r hr
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hr]
    exact Q.zero_mem
  letI : Algebra.FiniteType K (R ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K I) Ideal.Quotient.mk_surjective
  letI : Module.Finite K (R ⧸ I) := (Module.finite_iff_krullDimLE_zero K _).mpr inferInstance
  letI hfin : Module.Finite K H := Module.Finite.trans (R ⧸ I) H
  have hunit (s : p.primeCompl) : IsUnit (algebraMap R (Module.End R H) s) := by
    have hu : IsUnit (Ideal.Quotient.mk I (s : R)) := by
      by_contra h
      obtain ⟨J, hJ, hsJ⟩ := exists_max_ideal_of_mem_nonunits h
      have hs : (s : R) ∈ J.comap (Ideal.Quotient.mk I) := hsJ
      rw [hprimeq J hJ.isPrime] at hs
      exact s.2 hs
    rw [Module.End.isUnit_iff]
    obtain ⟨a, ha⟩ := hu.exists_right_inv
    refine ⟨fun z w he => ?_, fun z => ⟨a • z, ?_⟩⟩
    · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, ← hmk, ← hmk] at he
      exact hu.smul_left_cancel.mp he
    · rw [Module.algebraMap_end_apply, ← hmk, smul_smul, ha, one_smul]
  letI : IsLocalizedModule p.primeCompl (LinearMap.id : H →ₗ[R] H) :=
    IsLocalizedModule.mk hunit (fun z => ⟨⟨z, 1⟩, one_smul _ _⟩)
      (fun {z w} h => ⟨1, by simpa using h⟩)
  let e : H ≃ₗ[R] O ⊗[R] H := IsLocalizedModule.linearEquiv p.primeCompl
    LinearMap.id (TensorProduct.mk R O H 1)
  letI : Algebra K O := ((algebraMap R O).comp (algebraMap K R)).toAlgebra
  letI : IsScalarTower K R O := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let eK := e.restrictScalars K
  letI : Module.Finite K (O ⊗[R] H) := Module.Finite.equiv eK
  letI : IsLocalRing O := IsLocalization.AtPrime.isLocalRing O p
  letI : IsLocalHom (algebraMap K O) := ⟨fun k hk => by
    by_cases h : k = 0
    · exact (not_isUnit_zero (by simpa only [h, map_zero] using hk)).elim
    · exact Ne.isUnit h⟩
  letI : (RingHom.ker χ₀.toRingHom).IsPrime := RingHom.ker_isPrime _
  letI : IsLocalization.AtPrime O (RingHom.ker χ₀.toRingHom) :=
    inferInstanceAs (IsLocalization.AtPrime O (RingHom.ker χ₀))
  obtain ⟨ψ, hψ⟩ := exists_residueEquiv_at_rational_point (O := O) χ₀
  have hsurj : Function.Surjective (algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O)) := by
    intro z
    refine ⟨IsLocalRing.residue K (ψ z), ψ.injective ?_⟩
    exact (congrArg ψ (IsLocalRing.ResidueField.map_residue (algebraMap K O) (ψ z))).trans
      ((hψ (algebraMap K R (ψ z))).trans (χ₀.commutes (ψ z)))
  have hres : Module.length (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O) = 1 := by
    let f := LinearEquiv.ofBijective
      (Algebra.linearMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O))
      ⟨(algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O)).injective, hsurj⟩
    rw [← f.length_eq, Module.length_eq_one_iff]
    infer_instance
  have hlen := IsLocalRing.length_restrictScalars K O (O ⊗[R] H)
  rw [hres, mul_one, Module.length_eq_finrank K] at hlen
  refine ⟨?_, hfin, (congrArg (fun n : ℕ => (n : ℕ∞)) eK.finrank_eq).trans hlen⟩
  rw [← Module.length_ne_top_iff, ← hlen]
  exact ENat.coe_ne_top _

end GlobalTheory.PointSupport
