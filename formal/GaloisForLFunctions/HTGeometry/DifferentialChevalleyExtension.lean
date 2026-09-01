import GaloisForLFunctions.HTGeometry.DifferentialChevalleyCertificate
import GaloisForLFunctions.HTGeometry.DifferentialFieldSolution

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open scoped Differential

noncomputable section

attribute [local instance] differentialPolynomialOverDifferential

universe u v

variable {A B K L : Type u}
  [CommRing A] [Differential A]
  [CommRing B] [Differential B] [Algebra A B] [DifferentialAlgebra A B]
  [Field K] [Differential K]
  [Field L] [Differential L]

/-- Descend a differential polynomial map through a surjective differential presentation. -/
theorem exists_differentialRingHom_of_surjective_eval
    {ι : Type v} (y : ι → B)
    (hy : Function.Surjective (differentialPolynomialEvalOver (K := A) y))
    (f : A →+* K)
    (hfδ : ∀ a : A, f (Differential.deriv a) = Differential.deriv (f a))
    (ψ : DifferentialPolynomial ι K →+* L)
    (hψδ : ∀ Q, ψ (differentialPolynomialOverDerivation ι K Q) =
      Differential.deriv (ψ Q))
    (hrel : ∀ Q ∈ differentialRelationIdealOver (K := A) y,
      ψ (MvPolynomial.map f Q) = 0) :
    ∃ (κ : K →+* L) (F : B →+* L),
      (∀ k : K, κ (Differential.deriv k) = Differential.deriv (κ k)) ∧
      (∀ b : B, F (Differential.deriv b) = Differential.deriv (F b)) ∧
      (∀ a : A, F (algebraMap A B a) = κ (f a)) ∧
      ∀ Q : DifferentialPolynomial ι A,
        F (differentialPolynomialEvalOver (K := A) y Q) =
          ψ (MvPolynomial.map f Q) := by
  let ev := (differentialPolynomialEvalOver (K := A) y).toRingHom
  let θ : DifferentialPolynomial ι A →+* L :=
    ψ.comp (MvPolynomial.map f)
  have hker : RingHom.ker ev ≤ RingHom.ker θ := by
    intro Q hQ
    exact hrel Q hQ
  let e : {g : DifferentialPolynomial ι A →+* L //
      RingHom.ker ev ≤ RingHom.ker g} ≃ (B →+* L) :=
    RingHom.liftOfSurjective ev hy
  let F : B →+* L := e ⟨θ, hker⟩
  have hFcomp : F.comp ev = θ := by
    have h := e.symm_apply_apply ⟨θ, hker⟩
    exact congrArg Subtype.val h
  have hFeval (Q : DifferentialPolynomial ι A) :
      F (differentialPolynomialEvalOver (K := A) y Q) = θ Q := by
    exact DFunLike.congr_fun hFcomp Q
  have hθδ (Q : DifferentialPolynomial ι A) :
      θ (differentialPolynomialOverDerivation ι A Q) =
        Differential.deriv (θ Q) := by
    change ψ (MvPolynomial.map f
      (differentialPolynomialOverDerivation ι A Q)) =
      Differential.deriv (ψ (MvPolynomial.map f Q))
    rw [map_differentialPolynomialOverDerivation_of_commutes f hfδ]
    exact hψδ _
  let κ : K →+* L := ψ.comp MvPolynomial.C
  have hκδ : ∀ k : K,
      κ (Differential.deriv k) = Differential.deriv (κ k) := by
    intro k
    change ψ (MvPolynomial.C (Differential.deriv k)) =
      Differential.deriv (ψ (MvPolynomial.C k))
    rw [← differentialPolynomialOverDerivation_C]
    exact hψδ _
  have hFδ : ∀ b : B,
      F (Differential.deriv b) = Differential.deriv (F b) := by
    intro b
    obtain ⟨Q, rfl⟩ := hy b
    calc
      F (Differential.deriv (differentialPolynomialEvalOver (K := A) y Q)) =
          F (differentialPolynomialEvalOver (K := A) y
            (differentialPolynomialOverDerivation ι A Q)) := by
              rw [differentialPolynomialEvalOver_derivation]
      _ = θ (differentialPolynomialOverDerivation ι A Q) := hFeval _
      _ = Differential.deriv (θ Q) := hθδ Q
      _ = Differential.deriv
          (F (differentialPolynomialEvalOver (K := A) y Q)) := by rw [hFeval]
  refine ⟨κ, F, hκδ, hFδ, ?_, ?_⟩
  · intro a
    calc
      F (algebraMap A B a) =
          F (differentialPolynomialEvalOver (K := A) y (MvPolynomial.C a)) := by simp
      _ = θ (MvPolynomial.C a) := hFeval _
      _ = κ (f a) := by simp [θ, κ]
  · intro Q
    exact hFeval Q

variable [IsDomain A] [CharZero A] [Algebra ℚ A]
  [IsDomain B] [CharZero K]

/-- Differential Chevalley extension for a one-generator differential presentation of a domain. -/
theorem exists_differentialChevalley_extension_one
    (y : B)
    (hy : Function.Surjective
      (differentialPolynomialEvalOver (K := A) (fun _ : Unit => y)))
    (hAB : Function.Injective (algebraMap A B)) :
    ∃ g : A, g ≠ 0 ∧ ∀ (f : A →+* K),
      (∀ a : A, f (Differential.deriv a) = Differential.deriv (f a)) →
      f g ≠ 0 →
      ∃ (L : Type u) (_ : Field L) (_ : Differential L)
          (κ : K →+* L) (F : B →+* L),
        (∀ k : K, κ (Differential.deriv k) = Differential.deriv (κ k)) ∧
        (∀ b : B, F (Differential.deriv b) = Differential.deriv (F b)) ∧
        ∀ a : A, F (algebraMap A B a) = κ (f a) := by
  classical
  let I : Ideal (DifferentialPolynomial Unit A) :=
    differentialRelationIdealOver (K := A) (fun _ : Unit => y)
  have hIprime : I.IsPrime := RingHom.ker_isPrime _
  have hIδ : ∀ Q ∈ I,
      differentialPolynomialOverDerivation Unit A Q ∈ I := by
    intro Q hQ
    exact differentialPolynomialOverDerivation_mem_relationIdeal (fun _ : Unit => y) hQ
  have hIC : ∀ a : A,
      (MvPolynomial.C a : DifferentialPolynomial Unit A) ∈ I → a = 0 := by
    intro a ha
    apply hAB
    simpa [I] using ha
  by_cases hI0 : I = ⊥
  · refine ⟨1, one_ne_zero, ?_⟩
    intro f hfδ _
    let ψ := (differentialPolynomialEvalOver (K := K)
      (L := K) (fun _ : Unit => 0)).toRingHom
    have hψδ : ∀ Q, ψ (differentialPolynomialOverDerivation Unit K Q) =
        Differential.deriv (ψ Q) := by
      intro Q
      exact differentialPolynomialEvalOver_derivation (fun _ : Unit => (0 : K)) Q
    have hrel : ∀ Q ∈ I, ψ (MvPolynomial.map f Q) = 0 := by
      intro Q hQ
      rw [hI0, Ideal.mem_bot] at hQ
      simp [hQ]
    obtain ⟨κ, F, hκδ, hFδ, hbase, -⟩ :=
      exists_differentialRingHom_of_surjective_eval
        (A := A) (B := B) (K := K) (L := K) (ι := Unit)
        (fun _ : Unit => y) hy f hfδ ψ hψδ (by simpa [I] using hrel)
    exact ⟨K, inferInstance, inferInstance, κ, F, hκδ, hFδ, hbase⟩
  · obtain ⟨g, hg0, hguard⟩ :=
      exists_primeDifferentialIdeal_over_map_of_primeDifferentialIdeal
        (R := A) (K := K) I hI0 hIprime hIδ hIC
    refine ⟨g, hg0, ?_⟩
    intro f hfδ hfg
    obtain ⟨P, hPprime, hPδ, hmapI⟩ := hguard f hfδ hfg
    obtain ⟨L, instLField, instLDiff, ψ, hψδ, hψP⟩ :=
      exists_differentialField_hom_of_ne_top hPprime.isRadical hPδ hPprime.ne_top
    have hrel : ∀ Q ∈ I, ψ (MvPolynomial.map f Q) = 0 := by
      intro Q hQI
      exact hψP _ (hmapI Q hQI)
    obtain ⟨κ, F, hκδ, hFδ, hbase, -⟩ :=
      exists_differentialRingHom_of_surjective_eval
        (A := A) (B := B) (K := K) (L := L) (ι := Unit)
        (fun _ : Unit => y) hy f hfδ ψ hψδ (by simpa [I] using hrel)
    exact ⟨L, instLField, instLDiff, κ, F, hκδ, hFδ, hbase⟩

/-- Marked one-generator differential Chevalley extension.  Besides extending the coefficient
map, the resulting differential map preserves one prescribed nonzero element. -/
theorem exists_differentialChevalley_extension_one_avoiding
    (y : B)
    (hy : Function.Surjective
      (differentialPolynomialEvalOver (K := A) (fun _ : Unit => y)))
    (hAB : Function.Injective (algebraMap A B))
    (z : B) (hz : z ≠ 0) :
    ∃ g : A, g ≠ 0 ∧ ∀ (f : A →+* K),
      (∀ a : A, f (Differential.deriv a) = Differential.deriv (f a)) →
      f g ≠ 0 →
      ∃ (L : Type u) (_ : Field L) (_ : Differential L)
          (κ : K →+* L) (F : B →+* L),
        (∀ k : K, κ (Differential.deriv k) = Differential.deriv (κ k)) ∧
        (∀ b : B, F (Differential.deriv b) = Differential.deriv (F b)) ∧
        (∀ a : A, F (algebraMap A B a) = κ (f a)) ∧
        F z ≠ 0 := by
  classical
  let I : Ideal (DifferentialPolynomial Unit A) :=
    differentialRelationIdealOver (K := A) (fun _ : Unit => y)
  have hIprime : I.IsPrime := RingHom.ker_isPrime _
  have hIδ : ∀ Q ∈ I,
      differentialPolynomialOverDerivation Unit A Q ∈ I := by
    intro Q hQ
    exact differentialPolynomialOverDerivation_mem_relationIdeal (fun _ : Unit => y) hQ
  have hIC : ∀ a : A,
      (MvPolynomial.C a : DifferentialPolynomial Unit A) ∈ I → a = 0 := by
    intro a ha
    apply hAB
    simpa [I] using ha
  obtain ⟨H, hHz⟩ := hy z
  have hHnot : H ∉ I := by
    intro hHI
    apply hz
    have hzero :
        differentialPolynomialEvalOver (K := A) (fun _ : Unit => y) H = 0 := by
      simpa [I] using hHI
    exact hHz.symm.trans hzero
  by_cases hI0 : I = ⊥
  · have hH0 : H ≠ 0 := by
      intro hzero
      apply hHnot
      rw [hzero]
      exact zero_mem I
    obtain ⟨mH, hcH⟩ : ∃ m, H.coeff m ≠ 0 := by
      by_contra h
      push Not at h
      apply hH0
      ext m
      simpa using h m
    let g : A := H.coeff mH
    refine ⟨g, hcH, ?_⟩
    intro f hfδ hfg
    have hmapH0 : MvPolynomial.map f H ≠ 0 := by
      intro hzero
      have hcoeff := congrArg (MvPolynomial.coeff mH) hzero
      rw [MvPolynomial.coeff_map] at hcoeff
      simp at hcoeff
      exact hfg hcoeff
    have hbotδ : ∀ Q ∈ (⊥ : Ideal (DifferentialPolynomial Unit K)),
        Differential.deriv Q ∈ (⊥ : Ideal (DifferentialPolynomial Unit K)) := by
      intro Q hQ
      rw [Ideal.mem_bot] at hQ ⊢
      simp [hQ]
    obtain ⟨L, instLField, instLDiff, ψ, hψδ, hψzero, hψH⟩ :=
      exists_differentialField_hom_of_notMem
        (R := DifferentialPolynomial Unit K)
        (I := (⊥ : Ideal (DifferentialPolynomial Unit K)))
        (Ideal.isPrime_bot.isRadical) hbotδ hmapH0
    have hrel : ∀ Q ∈ I, ψ (MvPolynomial.map f Q) = 0 := by
      intro Q hQI
      rw [hI0, Ideal.mem_bot] at hQI
      simp [hQI]
    obtain ⟨κ, F, hκδ, hFδ, hbase, hFeval⟩ :=
      exists_differentialRingHom_of_surjective_eval
        (A := A) (B := B) (K := K) (L := L) (ι := Unit)
        (fun _ : Unit => y) hy f hfδ ψ hψδ (by simpa [I] using hrel)
    have hFz : F z ≠ 0 := by
      intro hzero
      apply hψH
      exact (hFeval H).symm.trans (hHz ▸ hzero)
    exact ⟨L, instLField, instLDiff, κ, F, hκδ, hFδ, hbase, hFz⟩
  · obtain ⟨g, hg0, hguard⟩ :=
      exists_primeDifferentialIdeal_over_map_of_primeDifferentialIdeal_avoiding
        (R := A) (K := K) I hI0 hIprime hIδ hIC H hHnot
    refine ⟨g, hg0, ?_⟩
    intro f hfδ hfg
    obtain ⟨P, hPprime, hPδ, hmapI, hmapH⟩ := hguard f hfδ hfg
    obtain ⟨L, instLField, instLDiff, ψ, hψδ, hψP, hψH⟩ :=
      exists_differentialField_hom_of_notMem
        hPprime.isRadical hPδ hmapH
    have hrel : ∀ Q ∈ I, ψ (MvPolynomial.map f Q) = 0 := by
      intro Q hQI
      exact hψP _ (hmapI Q hQI)
    obtain ⟨κ, F, hκδ, hFδ, hbase, hFeval⟩ :=
      exists_differentialRingHom_of_surjective_eval
        (A := A) (B := B) (K := K) (L := L) (ι := Unit)
        (fun _ : Unit => y) hy f hfδ ψ hψδ (by simpa [I] using hrel)
    have hFz : F z ≠ 0 := by
      intro hzero
      apply hψH
      exact (hFeval H).symm.trans (hHz ▸ hzero)
    exact ⟨L, instLField, instLDiff, κ, F, hκδ, hFδ, hbase, hFz⟩

/-- Marked one-generator differential Chevalley extension with one source guard valid over every
characteristic-zero target differential field. -/
theorem exists_differentialChevalley_extension_one_avoiding_universal
    (y : B)
    (hy : Function.Surjective
      (differentialPolynomialEvalOver (K := A) (fun _ : Unit => y)))
    (hAB : Function.Injective (algebraMap A B))
    (z : B) (hz : z ≠ 0) :
    ∃ g : A, g ≠ 0 ∧ ∀ (K' : Type u) (_ : Field K') (_ : Differential K')
      (_ : CharZero K') (f : A →+* K'),
      (∀ a : A, f (Differential.deriv a) = Differential.deriv (f a)) →
      f g ≠ 0 →
      ∃ (L : Type u) (_ : Field L) (_ : Differential L)
          (κ : K' →+* L) (F : B →+* L),
        (∀ k : K', κ (Differential.deriv k) = Differential.deriv (κ k)) ∧
        (∀ b : B, F (Differential.deriv b) = Differential.deriv (F b)) ∧
        (∀ a : A, F (algebraMap A B a) = κ (f a)) ∧
        F z ≠ 0 := by
  classical
  let I : Ideal (DifferentialPolynomial Unit A) :=
    differentialRelationIdealOver (K := A) (fun _ : Unit => y)
  have hIprime : I.IsPrime := RingHom.ker_isPrime _
  have hIδ : ∀ Q ∈ I,
      differentialPolynomialOverDerivation Unit A Q ∈ I := by
    intro Q hQ
    exact differentialPolynomialOverDerivation_mem_relationIdeal (fun _ : Unit => y) hQ
  have hIC : ∀ a : A,
      (MvPolynomial.C a : DifferentialPolynomial Unit A) ∈ I → a = 0 := by
    intro a ha
    apply hAB
    simpa [I] using ha
  obtain ⟨H, hHz⟩ := hy z
  have hHnot : H ∉ I := by
    intro hHI
    apply hz
    have hzero :
        differentialPolynomialEvalOver (K := A) (fun _ : Unit => y) H = 0 := by
      simpa [I] using hHI
    exact hHz.symm.trans hzero
  by_cases hI0 : I = ⊥
  · have hH0 : H ≠ 0 := by
      intro hzero
      apply hHnot
      rw [hzero]
      exact zero_mem I
    obtain ⟨mH, hcH⟩ : ∃ m, H.coeff m ≠ 0 := by
      by_contra h
      push Not at h
      apply hH0
      ext m
      simpa using h m
    let g : A := H.coeff mH
    refine ⟨g, hcH, ?_⟩
    intro K' instKField instKDiff instKCharZero f hfδ hfg
    have hmapH0 : MvPolynomial.map f H ≠ 0 := by
      intro hzero
      have hcoeff := congrArg (MvPolynomial.coeff mH) hzero
      rw [MvPolynomial.coeff_map] at hcoeff
      simp at hcoeff
      exact hfg hcoeff
    have hbotδ : ∀ Q ∈ (⊥ : Ideal (DifferentialPolynomial Unit K')),
        Differential.deriv Q ∈ (⊥ : Ideal (DifferentialPolynomial Unit K')) := by
      intro Q hQ
      rw [Ideal.mem_bot] at hQ ⊢
      simp [hQ]
    obtain ⟨L, instLField, instLDiff, ψ, hψδ, hψzero, hψH⟩ :=
      exists_differentialField_hom_of_notMem
        (R := DifferentialPolynomial Unit K')
        (I := (⊥ : Ideal (DifferentialPolynomial Unit K')))
        (Ideal.isPrime_bot.isRadical) hbotδ hmapH0
    have hrel : ∀ Q ∈ I, ψ (MvPolynomial.map f Q) = 0 := by
      intro Q hQI
      rw [hI0, Ideal.mem_bot] at hQI
      simp [hQI]
    obtain ⟨κ, F, hκδ, hFδ, hbase, hFeval⟩ :=
      exists_differentialRingHom_of_surjective_eval
        (A := A) (B := B) (K := K') (L := L) (ι := Unit)
        (fun _ : Unit => y) hy f hfδ ψ hψδ (by simpa [I] using hrel)
    have hFz : F z ≠ 0 := by
      intro hzero
      apply hψH
      exact (hFeval H).symm.trans (hHz ▸ hzero)
    exact ⟨L, instLField, instLDiff, κ, F, hκδ, hFδ, hbase, hFz⟩
  · obtain ⟨g, hg0, hguard⟩ :=
      exists_primeDifferentialIdeal_over_map_of_primeDifferentialIdeal_avoiding_universal
        I hI0 hIprime hIδ hIC H hHnot
    refine ⟨g, hg0, ?_⟩
    intro K' instKField instKDiff instKCharZero f hfδ hfg
    obtain ⟨P, hPprime, hPδ, hmapI, hmapH⟩ :=
      hguard K' instKField instKCharZero instKDiff f hfδ hfg
    obtain ⟨L, instLField, instLDiff, ψ, hψδ, hψP, hψH⟩ :=
      exists_differentialField_hom_of_notMem
        hPprime.isRadical hPδ hmapH
    have hrel : ∀ Q ∈ I, ψ (MvPolynomial.map f Q) = 0 := by
      intro Q hQI
      exact hψP _ (hmapI Q hQI)
    obtain ⟨κ, F, hκδ, hFδ, hbase, hFeval⟩ :=
      exists_differentialRingHom_of_surjective_eval
        (A := A) (B := B) (K := K') (L := L) (ι := Unit)
        (fun _ : Unit => y) hy f hfδ ψ hψδ (by simpa [I] using hrel)
    have hFz : F z ≠ 0 := by
      intro hzero
      apply hψH
      exact (hFeval H).symm.trans (hHz ▸ hzero)
    exact ⟨L, instLField, instLDiff, κ, F, hκδ, hFδ, hbase, hFz⟩

end

end GaloisForLFunctions.HTGeometry
