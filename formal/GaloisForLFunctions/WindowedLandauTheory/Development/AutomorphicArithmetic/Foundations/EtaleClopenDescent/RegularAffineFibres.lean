import GaloisForLFunctions.HTGeometry.NoetherNormalizationKrullDim
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Over a characteristic-zero field, a polynomial map from an affine domain
to affine space of the same dimension has formally étale fibres away from a
proper closed subset of the target. -/

noncomputable section

open scoped nonZeroDivisors
open GaloisForLFunctions.HTGeometry KaehlerDifferential

namespace GlobalTheory.SchemeCohomology

private theorem trdeg_eq_of_krullDim {K B : Type} [Field K] [CommRing B] [IsDomain B]
    [Algebra K B] [Algebra.FiniteType K B] {d : ℕ} (hd : ringKrullDim B = (d : ℕ∞)) :
    Algebra.trdeg K B = (d : Cardinal) := by
  obtain ⟨n, f, hf, hfin⟩ := exists_integral_inj_algHom_of_fg K B
  have hn : n = d := by
    have e := (ringKrullDim_eq_of_noetherNormalization f hf hfin).symm.trans hd
    exact_mod_cast e
  subst n
  let A := MvPolynomial (Fin d) K
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm
  letI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hf
  letI : Algebra.IsIntegral A B := ⟨hfin⟩
  have h := trdeg_add_eq K A (A := B)
  have hz : Algebra.trdeg A B = 0 := trdeg_eq_zero
  rw [hz, add_zero] at h
  exact h.symm.trans (by simp [A, MvPolynomial.trdeg_of_isDomain])

private theorem isAlgebraic_of_polynomial_krullDim {K B : Type} [Field K] [CommRing B] [IsDomain B]
    [Algebra K B] [Algebra.FiniteType K B] {d : ℕ}
    [Algebra (MvPolynomial (Fin d) K) B] [IsScalarTower K (MvPolynomial (Fin d) K) B]
    [FaithfulSMul (MvPolynomial (Fin d) K) B] (hd : ringKrullDim B = (d : ℕ∞)) :
    Algebra.IsAlgebraic (MvPolynomial (Fin d) K) B := by
  let A := MvPolynomial (Fin d) K
  have hA : Algebra.trdeg K A = (d : Cardinal) := by simp [A, MvPolynomial.trdeg_of_isDomain]
  have h := trdeg_add_eq K A (A := B)
  rw [hA, trdeg_eq_of_krullDim (K := K) hd] at h
  apply trdeg_eq_zero_iff.mp
  rcases Cardinal.add_eq_left_iff.mp h with h | h
  · exact ((show (d : Cardinal) < Cardinal.aleph0 from Cardinal.natCast_lt_aleph0).not_ge ((le_max_left _ _).trans h)).elim
  · exact h

private theorem exists_unramified_localization_of_isAlgebraic
    (A B : Type) [CommRing A] [IsDomain A] [CharZero A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B] :
    ∃ b : B, b ≠ 0 ∧ Algebra.FormallyUnramified A (Localization.Away b) := by
  let E := Localization.AtPrime (⊥ : Ideal B)
  letI : IsFractionRing B E := by
    change IsLocalization (nonZeroDivisors B) E
    rw [← Ideal.primeCompl_bot]
    infer_instance
  letI : Field E := IsFractionRing.toField B
  letI : FaithfulSMul A E := (faithfulSMul_iff_algebraMap_injective A E).mpr
    ((IsFractionRing.injective B E).comp (FaithfulSMul.algebraMap_injective A B))
  letI : Algebra (FractionRing A) E := FractionRing.liftAlgebra A E
  letI : IsScalarTower A (FractionRing A) E := FractionRing.isScalarTower_liftAlgebra A E
  letI : Algebra.IsAlgebraic A E := (IsFractionRing.isAlgebraic_iff' A B E).mp inferInstance
  letI : Algebra.IsAlgebraic (FractionRing A) E := IsFractionRing.comap_isAlgebraic_iff.mp (inferInstance : Algebra.IsAlgebraic A E)
  letI : Algebra.FormallyUnramified A (FractionRing A) :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors A)
  letI : Algebra.FormallyUnramified (FractionRing A) E :=
    Algebra.FormallyUnramified.of_isSeparable _ _
  letI : Algebra.IsUnramifiedAt A (⊥ : Ideal B) :=
    Algebra.FormallyUnramified.comp A (FractionRing A) E
  obtain ⟨b, hb, hu⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt (R := A) (⊥ : Ideal B)
  exact ⟨b, fun h => hb (h ▸ (⊥ : Ideal B).zero_mem), hu⟩

/-- On the shifted fibre, the polynomial map agrees with evaluation at its target point. -/
private theorem quotient_comp_eq_eval {K B : Type} [Field K] [CommRing B] [Algebra K B]
    {d : ℕ} (φ : MvPolynomial (Fin d) K →ₐ[K] B) (c : Fin d → K) :
    let I := Ideal.span (Set.range fun j => φ (MvPolynomial.X j) - algebraMap K B (c j))
    (Ideal.Quotient.mkₐ K I).comp φ = (Algebra.ofId K (B ⧸ I)).comp (MvPolynomial.aeval c) := by
  intro I
  apply MvPolynomial.algHom_ext
  intro j
  let q := Ideal.Quotient.mkₐ K I
  change q (φ (MvPolynomial.X j)) = algebraMap K (B ⧸ I) (MvPolynomial.aeval c (MvPolynomial.X j))
  rw [MvPolynomial.aeval_X, ← q.commutes, ← sub_eq_zero, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self j))

/-- The fibres cut out by coordinate values in a nonempty principal open
of the target are formally étale. A nondominant map has empty fibres there. -/
theorem exists_polynomial_formallyEtale_fibres {K B : Type} [Field K] [CharZero K]
    [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B] {d : ℕ}
    (hd : ringKrullDim B = (d : ℕ∞)) (φ : MvPolynomial (Fin d) K →ₐ[K] B) :
    ∃ a : MvPolynomial (Fin d) K, a ≠ 0 ∧ ∀ c : Fin d → K, MvPolynomial.eval c a ≠ 0 →
      Algebra.FormallyEtale K (B ⧸
        Ideal.span (Set.range fun j => φ (MvPolynomial.X j) - algebraMap K B (c j))) := by
  let A := MvPolynomial (Fin d) K
  by_cases hinj : Function.Injective φ
  · letI : Algebra A B := φ.toRingHom.toAlgebra
    letI : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
    letI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
    letI : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType K A B
    letI : Algebra.IsAlgebraic A B := isAlgebraic_of_polynomial_krullDim hd
    obtain ⟨b, hb, hu⟩ := exists_unramified_localization_of_isAlgebraic A B
    obtain ⟨a, ha, hab⟩ := (Algebra.IsAlgebraic.isAlgebraic b (R := A)).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero hb)
    refine ⟨a, ha, fun c hc => ?_⟩
    let I := Ideal.span (Set.range fun j => φ (MvPolynomial.X j) - algebraMap K B (c j))
    let Q := B ⧸ I
    let ψ : A →ₐ[K] K := MvPolynomial.aeval c
    letI : Algebra A K := ψ.toRingHom.toAlgebra
    letI : IsScalarTower A K Q := IsScalarTower.of_algebraMap_eq fun r =>
      DFunLike.congr_fun (quotient_comp_eq_eval φ c) r
    let q := Ideal.Quotient.mkₐ A I
    have hunit : IsUnit (q b) := by
      apply isUnit_of_dvd_unit (map_dvd q hab)
      have he : q (φ a) = algebraMap K Q (MvPolynomial.eval c a) :=
        DFunLike.congr_fun (quotient_comp_eq_eval φ c) a
      change IsUnit (q (φ a))
      rw [he]
      exact (isUnit_iff_ne_zero.mpr hc).map (algebraMap K Q)
    let f : Localization.Away b →ₐ[A] Q := IsLocalization.Away.liftAlgHom b hunit
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) y
      exact ⟨algebraMap B (Localization.Away b) x, IsLocalization.Away.lift_eq b hunit x⟩
    letI : Algebra.FormallyUnramified A (Localization.Away b) := hu
    letI : Algebra.FormallyUnramified A Q := Algebra.FormallyUnramified.of_surjective f hf
    letI : Algebra.FormallyUnramified K Q := Algebra.FormallyUnramified.of_restrictScalars A K Q
    letI : Algebra.FiniteType K Q :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K I) Ideal.Quotient.mk_surjective
    exact Algebra.FormallyEtale.of_formallyUnramified_of_field K Q
  · rw [injective_iff_map_eq_zero] at hinj
    push Not at hinj
    obtain ⟨a, hφa, ha⟩ := hinj
    refine ⟨a, ha, fun c hc => ?_⟩
    let I := Ideal.span (Set.range fun j => φ (MvPolynomial.X j) - algebraMap K B (c j))
    let Q := B ⧸ I
    have he : Ideal.Quotient.mkₐ K I (φ a) = algebraMap K Q (MvPolynomial.eval c a) :=
      DFunLike.congr_fun (quotient_comp_eq_eval φ c) a
    have hunit : IsUnit (Ideal.Quotient.mkₐ K I (φ a)) := by
      rw [he]
      exact (isUnit_iff_ne_zero.mpr hc).map (algebraMap K Q)
    rw [hφa, map_zero] at hunit
    letI : Subsingleton Q := subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hunit)
    letI : Algebra.FormallyUnramified K Q := Algebra.FormallyUnramified.of_surjective
      (Algebra.ofId K Q) (fun y => ⟨0, Subsingleton.elim _ _⟩)
    letI : Algebra.FiniteType K Q :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K I) Ideal.Quotient.mk_surjective
    exact Algebra.FormallyEtale.of_formallyUnramified_of_field K Q

/-- A rational point of a formally étale quotient has zero cotangent space.
Consequently, the quotient ideal generates the original cotangent space. -/
theorem cotangentSpan_of_formallyEtale_quotient {K B : Type} [Field K] [CommRing B] [Algebra K B]
    (I : Ideal B) [Algebra.FormallyEtale K (B ⧸ I)] (ε : B →ₐ[K] K)
    (hI : I ≤ RingHom.ker ε.toRingHom) :
    let m := RingHom.ker ε.toRingHom
    m ≤ I ⊔ m ^ 2 := by
  intro m
  let Q := B ⧸ I
  let q := Ideal.Quotient.mk I
  let e := Ideal.Quotient.liftₐ I ε (fun a ha => RingHom.mem_ker.mp (hI ha))
  letI : Algebra Q K := e.toRingHom.toAlgebra
  letI : IsScalarTower K Q K := IsScalarTower.of_algebraMap_eq fun a => (e.commutes a).symm
  let m' := RingHom.ker (algebraMap Q K)
  have he : m'.comap q = m := rfl
  have hq : m.map q = m' := he ▸ Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective m'
  have hsurj : Function.Surjective (algebraMap Q K) := fun a => ⟨algebraMap K Q a, e.commutes a⟩
  obtain ⟨L, hL⟩ :=
    (Algebra.FormallySmooth.iff_split_injection (R := K) (P := Q) (A := K) hsurj).mp inferInstance
  letI : Subsingleton Ω[Q⁄K] := (Algebra.formallyUnramified_iff K Q).mp inferInstance
  have hsq : m' ≤ m' ^ 2 := by
    intro a ha
    let z := m'.toCotangent ⟨a, ha⟩
    have hz := LinearMap.congr_fun hL z
    have hzero : kerCotangentToTensor K Q K z = 0 := Subsingleton.elim _ _
    rw [LinearMap.comp_apply, hzero, map_zero, LinearMap.id_apply] at hz
    exact (Ideal.toCotangent_eq_zero _ _).mp hz.symm
  have hker : (⊥ : Ideal Q).comap q = I := SetLike.ext fun a =>
    Ideal.mem_bot.trans Ideal.Quotient.eq_zero_iff_mem
  have h : m ≤ ((m ^ 2).map q).comap q := by
    rw [Ideal.map_pow, hq, ← he]
    exact Ideal.comap_mono hsq
  rwa [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective, hker, sup_comm] at h

end GlobalTheory.SchemeCohomology
