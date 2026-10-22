import GaloisForLFunctions.HTGeometry.Critical.Schur.IntegralClosurePlace
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower

/-!
# Transport from ideal-theoretic to valuation-theoretic Schur inertia

The chosen upper Schur valuation ring is the localization of the normal integral closure at its
contracted prime.  Therefore ideal inertia localizes to the upper ring, fixes its residue field,
and embeds faithfully into the actual valuation-theoretic inertia group.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing
open scoped Pointwise

set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
/-- Ring automorphism induced by an ideal-inertia element on the normal integral closure. -/
noncomputable def criticalSchurIdealInertiaIntegralClosureEquiv
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (σ : criticalSchurIdealInertiaGroup K hm hn) :
    CriticalSchurNormalIntegralClosure K hm hn ≃+*
      CriticalSchurNormalIntegralClosure K hm hn :=
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K hm hn
  letI : Algebra.IsAlgebraic (criticalObservationField K m n)
      (criticalSourceAlgebraicClosure K m n) :=
    Algebra.IsAlgebraic.trans (criticalObservationField K m n)
      (criticalSourceField K m n) (criticalSourceAlgebraicClosure K m n)
  letI : Normal (criticalObservationField K m n)
      (criticalSourceAlgebraicClosure K m n) :=
    { splits' _ := IsAlgClosed.splits _ }
  (galRestrict (CriticalSchurNormalBaseRing K hm hn)
      (criticalObservationField K m n) (criticalNormalClosure K m n)
      (CriticalSchurNormalIntegralClosure K hm hn)
      (σ : criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
        criticalNormalClosure K m n)).toRingEquiv

@[simp] theorem criticalSchurIdealInertiaIntegralClosureEquiv_coe
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (σ : criticalSchurIdealInertiaGroup K hm hn)
    (x : CriticalSchurNormalIntegralClosure K hm hn) :
    ((criticalSchurIdealInertiaIntegralClosureEquiv K hm hn σ x :
        CriticalSchurNormalIntegralClosure K hm hn) :
      criticalNormalClosure K m n) =
      (σ : criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
        criticalNormalClosure K m n) • (x : criticalNormalClosure K m n) := by
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K hm hn
  letI : Algebra.IsAlgebraic (criticalObservationField K m n)
      (criticalSourceAlgebraicClosure K m n) :=
    Algebra.IsAlgebraic.trans (criticalObservationField K m n)
      (criticalSourceField K m n) (criticalSourceAlgebraicClosure K m n)
  letI : Normal (criticalObservationField K m n)
      (criticalSourceAlgebraicClosure K m n) :=
    { splits' _ := IsAlgClosed.splits _ }
  rw [AlgEquiv.smul_def]
  exact algebraMap_galRestrict_apply (CriticalSchurNormalBaseRing K hm hn)
    (σ : criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
      criticalNormalClosure K m n) x

/-- Ideal inertia preserves the complement of the contracted prime. -/
theorem criticalSchurIdealInertiaIntegralClosureEquiv_map_primeCompl
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (σ : criticalSchurIdealInertiaGroup K hm hn) :
    (criticalSchurNormalIntegralClosurePrime K hm hn).primeCompl.map
        (criticalSchurIdealInertiaIntegralClosureEquiv K hm hn σ).toMonoidHom =
      (criticalSchurNormalIntegralClosurePrime K hm hn).primeCompl := by
  let S := CriticalSchurNormalIntegralClosure K hm hn
  let P := criticalSchurNormalIntegralClosurePrime K hm hn
  let τ := criticalSchurIdealInertiaIntegralClosureEquiv K hm hn σ
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change τ x ∉ P
    intro hτx
    apply hx
    have hdiff : τ x - x ∈ P := by
      exact σ.property x
    have hmem := P.sub_mem hτx hdiff
    simpa using hmem
  · intro y hy
    refine ⟨τ.symm y, ?_, τ.apply_symm_apply y⟩
    change τ.symm y ∉ P
    intro hpre
    apply hy
    have hdiff : τ (τ.symm y) - τ.symm y ∈ P := by
      exact σ.property (τ.symm y)
    have hmem := P.add_mem hdiff hpre
    simpa using hmem

/-- Localized automorphism of the chosen upper valuation ring attached to ideal inertia. -/
noncomputable def criticalSchurIdealInertiaUpperEquiv
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (σ : criticalSchurIdealInertiaGroup K hm hn) :
    criticalNormalClosureSchurValuationSubring K hm hn ≃+*
      criticalNormalClosureSchurValuationSubring K hm hn :=
  IsLocalization.ringEquivOfRingEquiv
    (criticalNormalClosureSchurValuationSubring K hm hn)
    (criticalNormalClosureSchurValuationSubring K hm hn)
    (criticalSchurIdealInertiaIntegralClosureEquiv K hm hn σ)
    (criticalSchurIdealInertiaIntegralClosureEquiv_map_primeCompl K hm hn σ)

@[simp] theorem criticalSchurIdealInertiaUpperEquiv_algebraMap
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (σ : criticalSchurIdealInertiaGroup K hm hn)
    (x : CriticalSchurNormalIntegralClosure K hm hn) :
    criticalSchurIdealInertiaUpperEquiv K hm hn σ
        (algebraMap (CriticalSchurNormalIntegralClosure K hm hn)
          (criticalNormalClosureSchurValuationSubring K hm hn) x) =
      algebraMap (CriticalSchurNormalIntegralClosure K hm hn)
        (criticalNormalClosureSchurValuationSubring K hm hn)
        (criticalSchurIdealInertiaIntegralClosureEquiv K hm hn σ x) :=
  IsLocalization.ringEquivOfRingEquiv_eq
    (criticalSchurIdealInertiaIntegralClosureEquiv_map_primeCompl K hm hn σ) x

/-- The localized automorphism is the restriction of the original normal-closure automorphism. -/
theorem criticalSchurIdealInertiaUpperEquiv_coe
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (σ : criticalSchurIdealInertiaGroup K hm hn)
    (a : criticalNormalClosureSchurValuationSubring K hm hn) :
    ((criticalSchurIdealInertiaUpperEquiv K hm hn σ a :
        criticalNormalClosureSchurValuationSubring K hm hn) :
      criticalNormalClosure K m n) =
      (σ : criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
        criticalNormalClosure K m n) • (a : criticalNormalClosure K m n) := by
  let S := CriticalSchurNormalIntegralClosure K hm hn
  let P := criticalSchurNormalIntegralClosurePrime K hm hn
  let A := criticalNormalClosureSchurValuationSubring K hm hn
  let E := criticalNormalClosure K m n
  let G := E ≃ₐ[criticalObservationField K m n] E
  have hhom : A.subtype.comp
      (criticalSchurIdealInertiaUpperEquiv K hm hn σ).toRingHom =
      (σ : G).toRingHom.comp A.subtype := by
    apply IsLocalization.ringHom_ext P.primeCompl
    apply RingHom.ext
    intro x
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      criticalSchurIdealInertiaUpperEquiv_algebraMap K hm hn]
    change
      ((criticalSchurIdealInertiaIntegralClosureEquiv K hm hn σ x : S) : E) =
        (σ : G) • (x : E)
    exact criticalSchurIdealInertiaIntegralClosureEquiv_coe K hm hn σ x
  exact RingHom.congr_fun hhom a

/-- Every ideal-inertia automorphism stabilizes the chosen upper valuation ring. -/
theorem criticalSchurIdealInertia_mem_decompositionGroup
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (σ : criticalSchurIdealInertiaGroup K hm hn) :
    (σ : criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
      criticalNormalClosure K m n) ∈ criticalSchurDecompositionGroup K hm hn := by
  let A := criticalNormalClosureSchurValuationSubring K hm hn
  let E := criticalNormalClosure K m n
  let G := E ≃ₐ[criticalObservationField K m n] E
  let e := criticalSchurIdealInertiaUpperEquiv K hm hn σ
  change (σ : G) • A = A
  apply SetLike.ext
  intro x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨a, ha, rfl⟩
    let aA : A := ⟨a, ha⟩
    have he := criticalSchurIdealInertiaUpperEquiv_coe K hm hn σ aA
    rw [← he]
    exact (e aA).property
  · intro hx
    let xA : A := ⟨x, hx⟩
    let aA : A := e.symm xA
    refine ⟨(aA : E), aA.property, ?_⟩
    calc
      (σ : G) • (aA : E) = (e aA : A) :=
        (criticalSchurIdealInertiaUpperEquiv_coe K hm hn σ aA).symm
      _ = x := congrArg Subtype.val (e.apply_symm_apply xA)

/-- Identity-on-automorphisms homomorphism from ideal inertia to place decomposition. -/
noncomputable def criticalSchurIdealInertiaToDecomposition
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSchurIdealInertiaGroup K hm hn →*
      criticalSchurDecompositionGroup K hm hn where
  toFun σ := ⟨σ, criticalSchurIdealInertia_mem_decompositionGroup K hm hn σ⟩
  map_one' := by apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; rfl

@[simp] theorem criticalSchurIdealInertiaToDecomposition_smul_upper
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (σ : criticalSchurIdealInertiaGroup K hm hn)
    (a : criticalNormalClosureSchurValuationSubring K hm hn) :
    criticalSchurIdealInertiaToDecomposition K hm hn σ • a =
      criticalSchurIdealInertiaUpperEquiv K hm hn σ a := by
  apply Subtype.ext
  exact (criticalSchurIdealInertiaUpperEquiv_coe K hm hn σ a).symm

/-- Ideal inertia acts trivially on the residue field of the localized upper ring. -/
theorem criticalSchurIdealInertiaUpperEquiv_residue
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (σ : criticalSchurIdealInertiaGroup K hm hn)
    (a : criticalNormalClosureSchurValuationSubring K hm hn) :
    IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K hm hn)
        (criticalSchurIdealInertiaUpperEquiv K hm hn σ a) =
      IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K hm hn) a := by
  let S := CriticalSchurNormalIntegralClosure K hm hn
  let P := criticalSchurNormalIntegralClosurePrime K hm hn
  let A := criticalNormalClosureSchurValuationSubring K hm hn
  have hhom : (IsLocalRing.residue A).comp
      (criticalSchurIdealInertiaUpperEquiv K hm hn σ).toRingHom =
      IsLocalRing.residue A := by
    apply IsLocalization.ringHom_ext P.primeCompl
    apply RingHom.ext
    intro x
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      criticalSchurIdealInertiaUpperEquiv_algebraMap K hm hn]
    rw [← sub_eq_zero, ← map_sub, ← map_sub]
    apply (IsLocalRing.residue_eq_zero_iff _).2
    change criticalSchurNormalIntegralClosureToUpper K hm hn
        (criticalSchurIdealInertiaIntegralClosureEquiv K hm hn σ x - x) ∈
      IsLocalRing.maximalIdeal A
    exact σ.property x
  exact RingHom.congr_fun hhom a

/-- Residues of the chosen upper valuation ring are hit by its own elements. -/
theorem criticalSchurUpperResidue_surjective
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Function.Surjective
      (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K hm hn)) :=
  IsLocalRing.residue_surjective

/-- The decomposition element underlying ideal inertia lies in valuation-theoretic inertia. -/
theorem criticalSchurIdealInertiaToDecomposition_mem_inertia
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (σ : criticalSchurIdealInertiaGroup K hm hn) :
    criticalSchurIdealInertiaToDecomposition K hm hn σ ∈
      criticalSchurInertiaGroup K hm hn := by
  refine MonoidHom.mem_ker.2 (RingEquiv.ext ?_)
  refine (criticalSchurUpperResidue_surjective K hm hn).forall.2 fun a => ?_
  change criticalSchurIdealInertiaToDecomposition K hm hn σ •
      IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K hm hn) a =
      IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K hm hn) a
  rw [← IsLocalRing.ResidueField.residue_smul,
    criticalSchurIdealInertiaToDecomposition_smul_upper K hm hn]
  exact criticalSchurIdealInertiaUpperEquiv_residue K hm hn σ a

/-- Canonical injective homomorphism from ideal-theoretic inertia to the chosen-place inertia. -/
noncomputable def criticalSchurIdealInertiaToInertia
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSchurIdealInertiaGroup K hm hn →*
      criticalSchurInertiaGroup K hm hn :=
  MonoidHom.codRestrict (criticalSchurIdealInertiaToDecomposition K hm hn)
    (criticalSchurInertiaGroup K hm hn)
    (criticalSchurIdealInertiaToDecomposition_mem_inertia K hm hn)

theorem criticalSchurIdealInertiaToInertia_injective
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Function.Injective (criticalSchurIdealInertiaToInertia K hm hn) := by
  intro σ τ hστ
  apply Subtype.ext
  exact congrArg
    (fun g : criticalSchurInertiaGroup K hm hn =>
      ((g : criticalSchurDecompositionGroup K hm hn) :
        criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
          criticalNormalClosure K m n)) hστ

end

end GaloisForLFunctions.HTGeometry
