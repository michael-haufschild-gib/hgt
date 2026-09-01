import GaloisForLFunctions.HTGeometry.DifferentialChevalleyCharacteristic
import GaloisForLFunctions.HTGeometry.RittBasisTrivialContraction
import GaloisForLFunctions.HTGeometry.DifferentialLurothComponentTransfer
import GaloisForLFunctions.HTGeometry.SeparantCoefficientMap
import GaloisForLFunctions.HTGeometry.DifferentialFieldSolution

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open scoped Differential

noncomputable section

attribute [local instance] differentialPolynomialOverDifferential

/-- One denominator clears a finite family of multivariable polynomials. -/
theorem exists_mvPolynomial_family_fraction_clear
    {R K σ ι : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Finite ι] (P : ι → MvPolynomial σ K) :
    ∃ d : nonZeroDivisors R, ∃ Q : ι → MvPolynomial σ R, ∀ i,
      MvPolynomial.map (algebraMap R K) (Q i) =
        MvPolynomial.C (algebraMap R K (d : R)) * P i := by
  let M : Submonoid R := nonZeroDivisors R
  letI := MvPolynomial.algebraMvPolynomial (σ := σ) (R := R) (S := K)
  haveI : IsLocalization (M.map (MvPolynomial.C (σ := σ)))
      (MvPolynomial σ K) := MvPolynomial.isLocalization M K
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finite
      (M.map (MvPolynomial.C (σ := σ))) P
  rcases b.2 with ⟨d, hdM, hdb⟩
  let Q : ι → MvPolynomial σ R := fun i => Classical.choose (hb i)
  have hQ (i : ι) :
      algebraMap (MvPolynomial σ R) (MvPolynomial σ K) (Q i) =
        (b : MvPolynomial σ R) • P i := Classical.choose_spec (hb i)
  refine ⟨⟨d, hdM⟩, Q, fun i => ?_⟩
  rw [MvPolynomial.algebraMap_def] at hQ
  calc
    MvPolynomial.map (algebraMap R K) (Q i) =
        (b : MvPolynomial σ R) • P i := hQ i
    _ = algebraMap (MvPolynomial σ R) (MvPolynomial σ K)
          (MvPolynomial.C d) * P i := by
      rw [Algebra.smul_def, hdb]
    _ = MvPolynomial.C (algebraMap R K (d : R)) * P i := by
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_C]

/-- Differential stability survives coefficient localization. -/
theorem deriv_mem_map_differentialPolynomial_of_commutes
    {R K ι : Type*} [CommRing R] [CommRing K] [Differential R] [Differential K]
    [Algebra R K]
    (hf : ∀ r : R, Differential.deriv (algebraMap R K r) =
      algebraMap R K (Differential.deriv r))
    {I : Ideal (DifferentialPolynomial ι R)}
    (hδ : ∀ Q ∈ I, differentialPolynomialOverDerivation ι R Q ∈ I) :
    ∀ Q ∈ Ideal.map (MvPolynomial.map (algebraMap R K)) I,
      differentialPolynomialOverDerivation ι K Q ∈
        Ideal.map (MvPolynomial.map (algebraMap R K)) I := by
  intro z hz
  set J : Ideal (DifferentialPolynomial ι K) :=
    Ideal.map (MvPolynomial.map (algebraMap R K)) I with hJ
  have hzz : z ∈ Ideal.span
      (MvPolynomial.map (algebraMap R K) '' (I : Set _)) := hz
  refine Submodule.span_induction
    (p := fun w _ => differentialPolynomialOverDerivation ι K w ∈ J)
    ?_ ?_ ?_ ?_ hzz
  · rintro w ⟨x, hx, rfl⟩
    rw [← map_differentialPolynomialOverDerivation_of_commutes
      (algebraMap R K) (fun r => (hf r).symm)]
    exact Ideal.mem_map_of_mem _ (hδ x hx)
  · rw [map_zero]
    exact zero_mem _
  · intro a b _ _ ha hb
    rw [map_add]
    exact add_mem ha hb
  · intro a w hw hderiv
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    refine add_mem (Ideal.mul_mem_left _ _ hderiv) (Ideal.mul_mem_right _ _ hw)

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R] [Algebra ℚ R]
  [Differential R]

theorem exists_characteristicSpecializationCertificate
    (I : Ideal (DifferentialPolynomial Unit R))
    (hI0 : I ≠ ⊥) (hprime : I.IsPrime)
    (hδ : ∀ Q ∈ I, differentialPolynomialOverDerivation Unit R Q ∈ I)
    (hIC : ∀ r : R, (MvPolynomial.C r : DifferentialPolynomial Unit R) ∈ I → r = 0) :
    ∃ A U V N : DifferentialPolynomial Unit R,
      A.vars.Nonempty ∧
      (∀ Q ∈ I, ∃ a b : ℕ,
        scalarDifferentialPolynomialInitial A ^ a *
            (scalarDifferentialPolynomialSeparant A ^ b * Q) ∈ diffPolyIterateIdeal A) ∧
      N ≠ 0 ∧
      ((), scalarDifferentialPolynomialOrder A) ∉ N.vars ∧
      U * A + V * scalarDifferentialPolynomialSeparant A = N := by
  classical
  let K := FractionRing R
  letI : Differential K := fractionRingDifferential R
  let φ : R →+* K := algebraMap R K
  let S := DifferentialPolynomial Unit R
  letI : Algebra S (DifferentialPolynomial Unit K) :=
    MvPolynomial.algebraMvPolynomial
  let M : Submonoid S :=
    (nonZeroDivisors R).map (MvPolynomial.C : R →+* S).toMonoidHom
  let IK : Ideal (DifferentialPolynomial Unit K) :=
    Ideal.map (MvPolynomial.map φ) I
  have hφinj : Function.Injective φ := IsFractionRing.injective R K
  have hφδ : ∀ r : R, φ (Differential.deriv r) = Differential.deriv (φ r) := by
    intro r
    simpa [φ] using (fractionRingDifferential_algebraMap R r).symm
  have hloc : IsLocalization M (DifferentialPolynomial Unit K) := by
    exact MvPolynomial.isLocalization (nonZeroDivisors R) K
  letI : IsLocalization M (DifferentialPolynomial Unit K) := hloc
  have hdisjoint : Disjoint (M : Set S) (I : Set S) := by
    rw [Set.disjoint_left]
    intro Z hZM hZI
    rcases hZM with ⟨r, hr, rfl⟩
    have hr0 : r = 0 := hIC r hZI
    exact (nonZeroDivisors.ne_zero hr) hr0
  have hIKprime : IK.IsPrime := by
    exact IsLocalization.isPrime_of_isPrime_disjoint M
      (DifferentialPolynomial Unit K) I hprime hdisjoint
  have hIK0 : IK ≠ ⊥ := by
    intro hzero
    apply hI0
    apply le_antisymm
    · intro Q hQI
      have hmap : MvPolynomial.map φ Q ∈ IK := Ideal.mem_map_of_mem _ hQI
      rw [hzero, Ideal.mem_bot] at hmap
      apply MvPolynomial.map_injective φ hφinj
      simpa using hmap
    · exact bot_le
  have hIKδ : ∀ Q ∈ IK,
      differentialPolynomialOverDerivation Unit K Q ∈ IK := by
    exact deriv_mem_map_differentialPolynomial_of_commutes
      (K := K) (ι := Unit) (fun r => (hφδ r).symm) hδ
  obtain ⟨AK, hAK⟩ :=
    Ideal.exists_minimal_scalarDifferentialPolynomialRank_ne_zero
      hIK0 hIKprime.ne_top
  have hAKirr : Irreducible AK := hAK.irreducible_of_isPrime hIKprime
  have hAKinitNot : scalarDifferentialPolynomialInitial AK ∉ IK :=
    hAK.initial_not_mem hIKprime.ne_top
  obtain ⟨dA, A, hA0, hAmap⟩ :=
    exists_mvPolynomial_fraction_clear_ne_zero
      (R := R) (K := K) (σ := Unit × ℕ) hAK.2.1
  have hAmapφ : MvPolynomial.map φ A = MvPolynomial.C (φ (dA : R)) * AK := by
    simpa [φ] using hAmap
  have hdAK : φ (dA : R) ≠ 0 := by
    intro hzero
    exact (nonZeroDivisors.ne_zero dA.2) (hφinj (by simpa using hzero))
  have hCdAunit : IsUnit
      (MvPolynomial.C (φ (dA : R)) : DifferentialPolynomial Unit K) :=
    IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr hdAK)
  have hmapA0 : MvPolynomial.map φ A ≠ 0 := by
    rw [hAmapφ]
    exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr hdAK) hAK.2.1
  have hAKdvdA : AK ∣ MvPolynomial.map φ A := by
    rw [hAmapφ]
    exact dvd_mul_left AK _
  have hAdvdAK : MvPolynomial.map φ A ∣ AK := by
    rcases hCdAunit with ⟨u, hu⟩
    refine ⟨(↑(u⁻¹) : DifferentialPolynomial Unit K), ?_⟩
    rw [hAmapφ]
    rw [← hu]
    simp [mul_assoc, mul_comm]
  have hvarsEq : (MvPolynomial.map φ A).vars = AK.vars := by
    apply Finset.Subset.antisymm
    · exact mvPolynomial_vars_subset_of_dvd hAdvdAK hAK.2.1
    · exact mvPolynomial_vars_subset_of_dvd hAKdvdA hmapA0
  have hAvars : A.vars.Nonempty := by
    rw [← MvPolynomial.vars_map_of_injective A hφinj, hvarsEq]
    exact hAK.2.2.1
  have horderEq : scalarDifferentialPolynomialOrder (MvPolynomial.map φ A) =
      scalarDifferentialPolynomialOrder AK := by
    unfold scalarDifferentialPolynomialOrder
    rw [hvarsEq]
  have hAle : differentialPolynomialIterateIdeal (MvPolynomial.map φ A) ≤ IK :=
    differentialPolynomialIterateIdeal_le_of_derivation_stable
      (by rw [hAmapφ]; exact IK.mul_mem_left _ hAK.1) hIKδ
  have hPdvd : ∀ Z : DifferentialPolynomial Unit K, Z ∈ IK →
      scalarDifferentialPolynomialOrder Z ≤
        scalarDifferentialPolynomialOrder (MvPolynomial.map φ A) →
      MvPolynomial.map φ A ∣ Z := by
    intro Z hZI hZorder
    have hAKdiv : AK ∣ Z :=
      hAK.dvd_of_relation_order_le hIKprime.ne_top hAKirr hAKinitNot hZI
        (by rwa [horderEq] at hZorder)
    exact dvd_trans hAdvdAK hAKdiv
  have hsat : ∀ Q ∈ I, ∃ a b : ℕ,
      scalarDifferentialPolynomialInitial A ^ a *
          (scalarDifferentialPolynomialSeparant A ^ b * Q) ∈ diffPolyIterateIdeal A := by
    intro Q hQI
    exact exists_oracle_initial_separant_powers_mem_diffPolyIterateIdeal
      φ hφinj hφδ hAvars hAle hPdvd (Ideal.mem_map_of_mem _ hQI)
  let v : Unit × ℕ := ((), scalarDifferentialPolynomialOrder A)
  have horderMap : scalarDifferentialPolynomialOrder (MvPolynomial.map φ A) =
      scalarDifferentialPolynomialOrder A := scalarDifferentialPolynomialOrder_map hφinj A
  have hmapAirr : Irreducible (MvPolynomial.map φ A) := by
    rcases hCdAunit with ⟨u, hu⟩
    have hassoc : Associated AK (MvPolynomial.map φ A) := by
      refine ⟨u, ?_⟩
      rw [hAmapφ, ← hu]
      exact mul_comm _ _
    exact hassoc.irreducible hAKirr
  have hmapAvars : (MvPolynomial.map φ A).vars.Nonempty := by
    rw [MvPolynomial.vars_map_of_injective A hφinj]
    exact hAvars
  have hrelprime : IsRelPrime (MvPolynomial.map φ A)
      (scalarDifferentialPolynomialSeparant (MvPolynomial.map φ A)) := by
    intro D hDA hDS
    rcases hmapAirr.dvd_iff.mp hDA with hunit | hassoc
    · exact hunit
    · exfalso
      exact irreducible_not_dvd_scalarDifferentialPolynomialSeparant
        hmapAvars hmapAirr (dvd_trans hassoc.dvd hDS)
  obtain ⟨UK, VK, NK, hNK0, hNvK, hbezoutK⟩ :=
    exists_mvPolynomial_bezout_clear_away_from_variable v hrelprime
  let H : Fin 3 → DifferentialPolynomial Unit K :=
    ![UK, VK, NK]
  obtain ⟨dB, B, hB⟩ :=
    exists_mvPolynomial_family_fraction_clear
      (R := R) (K := K) (σ := Unit × ℕ) H
  let U := B 0
  let V := B 1
  let N := B 2
  have hdBK : φ (dB : R) ≠ 0 := by
    intro hzero
    exact (nonZeroDivisors.ne_zero dB.2) (hφinj (by simpa using hzero))
  have hCdBunit : IsUnit
      (MvPolynomial.C (φ (dB : R)) : DifferentialPolynomial Unit K) :=
    IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr hdBK)
  have hUmap : MvPolynomial.map φ U = MvPolynomial.C (φ (dB : R)) * UK := by
    simpa [U, H, φ] using hB 0
  have hVmap : MvPolynomial.map φ V = MvPolynomial.C (φ (dB : R)) * VK := by
    simpa [V, H, φ] using hB 1
  have hNmap : MvPolynomial.map φ N = MvPolynomial.C (φ (dB : R)) * NK := by
    simpa [N, H, φ] using hB 2
  have hsepMap : scalarDifferentialPolynomialSeparant (MvPolynomial.map φ A) =
      MvPolynomial.map φ (scalarDifferentialPolynomialSeparant A) :=
    scalarDifferentialPolynomialSeparant_map hφinj A
  have hbezout : U * A + V * scalarDifferentialPolynomialSeparant A = N := by
    apply MvPolynomial.map_injective φ hφinj
    rw [map_add, map_mul, map_mul, hUmap, hVmap, hNmap, ← hsepMap]
    calc
      MvPolynomial.C (φ (dB : R)) * UK * MvPolynomial.map φ A +
          MvPolynomial.C (φ (dB : R)) * VK *
            scalarDifferentialPolynomialSeparant (MvPolynomial.map φ A) =
          MvPolynomial.C (φ (dB : R)) *
            (UK * MvPolynomial.map φ A +
              VK * scalarDifferentialPolynomialSeparant (MvPolynomial.map φ A)) := by ring
      _ = MvPolynomial.C (φ (dB : R)) * NK := by rw [hbezoutK]
  have hN0 : N ≠ 0 := by
    intro hzero
    have hprod0 : MvPolynomial.C (φ (dB : R)) * NK = 0 := by
      rw [← hNmap, hzero, map_zero]
    exact hNK0 ((mul_eq_zero.mp hprod0).resolve_left (MvPolynomial.C_ne_zero.mpr hdBK))
  have hNv : v ∉ N.vars := by
    intro hv
    have hvmap : v ∈ (MvPolynomial.map φ N).vars := by
      rw [MvPolynomial.vars_map_of_injective N hφinj]
      exact hv
    rw [hNmap] at hvmap
    have hprodDvd : MvPolynomial.C (φ (dB : R)) * NK ∣ NK := by
      rcases hCdBunit with ⟨u, hu⟩
      refine ⟨(↑(u⁻¹) : DifferentialPolynomial Unit K), ?_⟩
      rw [← hu]
      simp [mul_assoc, mul_comm]
    exact hNvK (mvPolynomial_vars_subset_of_dvd hprodDvd hNK0 hvmap)
  refine ⟨A, U, V, N, hAvars, hsat, hN0, ?_, hbezout⟩
  simpa [v] using hNv

variable {K : Type*} [Field K] [CharZero K] [Differential K]

/-- One nonzero source coefficient guard specializes every relation in a nonzero prime
differential ideal with trivial coefficient contraction into a prime differential ideal. -/
theorem exists_primeDifferentialIdeal_over_map_of_primeDifferentialIdeal
    (I : Ideal (DifferentialPolynomial Unit R))
    (hI0 : I ≠ ⊥) (hprime : I.IsPrime)
    (hδ : ∀ Q ∈ I, differentialPolynomialOverDerivation Unit R Q ∈ I)
    (hIC : ∀ r : R, (MvPolynomial.C r : DifferentialPolynomial Unit R) ∈ I → r = 0) :
    ∃ g : R, g ≠ 0 ∧ ∀ (f : R →+* K),
      (∀ r : R, f (Differential.deriv r) = Differential.deriv (f r)) →
      f g ≠ 0 →
      ∃ P : Ideal (DifferentialPolynomial Unit K), P.IsPrime ∧
        (∀ Q ∈ P, Differential.deriv Q ∈ P) ∧
        ∀ Q ∈ I, MvPolynomial.map f Q ∈ P := by
  classical
  obtain ⟨A, U, V, N, hAvars, hsat, hN0, hNv, hbezout⟩ :=
    exists_characteristicSpecializationCertificate I hI0 hprime hδ hIC
  let v : Unit × ℕ := ((), scalarDifferentialPolynomialOrder A)
  have hvA : v ∈ A.vars := scalarDifferentialPolynomialLeader_mem_vars hAvars
  obtain ⟨mA, hmA, hvmA⟩ :=
    (MvPolynomial.mem_vars_iff_mem_support v).mp hvA
  have hcA : A.coeff mA ≠ 0 := by
    simpa [MvPolynomial.mem_support_iff] using hmA
  have hinit0 : scalarDifferentialPolynomialInitial A ≠ 0 :=
    scalarDifferentialPolynomialInitial_ne_zero (by
      intro hzero
      simp [hzero] at hvA)
  obtain ⟨mI, hcI⟩ : ∃ m,
      (scalarDifferentialPolynomialInitial A).coeff m ≠ 0 := by
    by_contra h
    push Not at h
    apply hinit0
    ext m
    simpa using h m
  obtain ⟨mN, hcN⟩ : ∃ m, N.coeff m ≠ 0 := by
    by_contra h
    push Not at h
    apply hN0
    ext m
    simpa using h m
  let g : R := A.coeff mA *
    (scalarDifferentialPolynomialInitial A).coeff mI * N.coeff mN
  have hg0 : g ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hcA hcI) hcN
  refine ⟨g, hg0, ?_⟩
  intro f hfδ hfg
  have hfcA : f (A.coeff mA) ≠ 0 := by
    intro hzero
    apply hfg
    simp [g, hzero]
  have hfcI : f ((scalarDifferentialPolynomialInitial A).coeff mI) ≠ 0 := by
    intro hzero
    apply hfg
    simp [g, hzero]
  have hfcN : f (N.coeff mN) ≠ 0 := by
    intro hzero
    apply hfg
    simp [g, hzero]
  have hmAmap : mA ∈ (MvPolynomial.map f A).support := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map]
    exact hfcA
  have hvMap : v ∈ (MvPolynomial.map f A).vars :=
    (MvPolynomial.mem_vars_iff_mem_support v).mpr ⟨mA, hmAmap, hvmA⟩
  have horder : scalarDifferentialPolynomialOrder (MvPolynomial.map f A) =
      scalarDifferentialPolynomialOrder A := by
    apply Nat.le_antisymm
    · unfold scalarDifferentialPolynomialOrder
      exact Finset.sup_le fun q hq => Finset.le_sup (MvPolynomial.vars_map _ f hq)
    · exact Finset.le_sup (f := fun q : Unit × ℕ => q.2) hvMap
  have hinitMap : MvPolynomial.map f
      (scalarDifferentialPolynomialInitial A) ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (MvPolynomial.coeff mI) hzero
    rw [MvPolynomial.coeff_map] at hcoeff
    simp at hcoeff
    exact hfcI hcoeff
  have hNmap : MvPolynomial.map f N ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (MvPolynomial.coeff mN) hzero
    rw [MvPolynomial.coeff_map] at hcoeff
    simp at hcoeff
    exact hfcN hcoeff
  apply exists_primeDifferentialIdeal_over_map_of_characteristicCertificate
    f hfδ I A U V N hAvars hsat horder
  · simpa [v] using hvMap
  · exact hinitMap
  · exact hNmap
  · exact hNv
  · exact hbezout

end

end GaloisForLFunctions.HTGeometry
