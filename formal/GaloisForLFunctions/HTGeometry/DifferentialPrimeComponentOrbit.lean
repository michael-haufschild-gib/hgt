import GaloisForLFunctions.HTGeometry.CommonPeriodIterate
import GaloisForLFunctions.HTGeometry.DifferentialPrimeDecomposition
import GaloisForLFunctions.HTGeometry.RamificationIdxTransport

/-!
# Difference orbits of differential-prime components

A ring automorphism commuting with the derivation transports minimal differential primes to
minimal differential primes.  Consequently, every component in a finite intrinsic component
family is periodic under the automorphism.  This is the component-orbit input in the reduced
Hardouin--Singer no-new-constants argument.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

universe u

variable {R : Type u} [CommRing R] [Differential R]

private theorem commutesDeriv_symm' (σ : R ≃+* R) (hσ : CommutesDeriv σ) :
    CommutesDeriv σ.symm := by
  intro x
  apply σ.injective
  rw [σ.apply_symm_apply, hσ, σ.apply_symm_apply]

/-- A derivation-commuting automorphism transports differential-prime minimality. -/
theorem IsMinimalPrimeDifferentialIdeal.map_ringEquiv
    {P : Ideal R} (hP : IsMinimalPrimeDifferentialIdeal P)
    (σ : R ≃+* R) (hσ : CommutesDeriv σ) :
    IsMinimalPrimeDifferentialIdeal (Ideal.map (σ : R →+* R) P) := by
  letI : P.IsPrime := hP.1
  have hprime : (Ideal.map (σ : R →+* R) P).IsPrime :=
    Ideal.map_isPrime_of_surjective σ.surjective
      ((RingHom.injective_iff_ker_eq_bot (σ : R →+* R)).mp σ.injective ▸ bot_le)
  refine ⟨hprime, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hxP, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective (σ : R →+* R) σ.surjective).mp hy
    change Differential.deriv (σ x) ∈ Ideal.map (σ : R →+* R) P
    rw [← hσ x]
    exact Ideal.mem_map_of_mem (σ : R →+* R) (hP.2.1 x hxP)
  · intro Q hQprime hQderiv hQP
    let Q' : Ideal R := Ideal.map (σ.symm : R →+* R) Q
    have hsymm : CommutesDeriv σ.symm := commutesDeriv_symm' σ hσ
    have hQ'minData : Q'.IsPrime ∧ ∀ x ∈ Q', Differential.deriv x ∈ Q' := by
      letI : Q.IsPrime := hQprime
      refine ⟨Ideal.map_isPrime_of_surjective σ.symm.surjective
          ((RingHom.injective_iff_ker_eq_bot (σ.symm : R →+* R)).mp
            σ.symm.injective ▸ bot_le), ?_⟩
      intro y hy
      obtain ⟨x, hxQ, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective (σ.symm : R →+* R)
          σ.symm.surjective).mp hy
      change Differential.deriv (σ.symm x) ∈ Q'
      rw [← hsymm x]
      exact Ideal.mem_map_of_mem (σ.symm : R →+* R) (hQderiv x hxQ)
    have hQ'P : Q' ≤ P := by
      simpa [Q', Ideal.map_map] using
        Ideal.map_mono (f := (σ.symm : R →+* R)) hQP
    have hPQ' : P ≤ Q' := hP.2.2 Q' hQ'minData.1 hQ'minData.2 hQ'P
    simpa [Q', Ideal.map_map] using Ideal.map_mono (f := (σ : R →+* R)) hPQ'

/-- A finite zero-intersection family of minimal differential primes contains every minimal
differential prime. -/
theorem mem_finite_minimalPrimeDifferential_family
    (S : Finset (Ideal R))
    (hSmin : ∀ P ∈ S, IsMinimalPrimeDifferentialIdeal P)
    (hSbot : sInf (S : Set (Ideal R)) = ⊥)
    {P : Ideal R} (hP : IsMinimalPrimeDifferentialIdeal P) : P ∈ S := by
  have hInfP : sInf (S : Set (Ideal R)) ≤ P := by rw [hSbot]; exact bot_le
  obtain ⟨Q, hQS, hQP⟩ := exists_mem_le_of_sInf_le_isPrime S hP.1 hInfP
  have hPQ := hP.2.2 Q (hSmin Q hQS).1 (hSmin Q hQS).2.1 hQP
  exact (show Q = P from le_antisymm hQP hPQ) ▸ hQS

/-- Every minimal differential-prime component in a finite intrinsic family is fixed by a
positive iterate of a derivation-commuting automorphism. -/
theorem exists_pos_iterate_map_eq_self_of_minimalPrimeDifferential
    (σ : R ≃+* R) (hσ : CommutesDeriv σ)
    (S : Finset (Ideal R))
    (hSmin : ∀ P ∈ S, IsMinimalPrimeDifferentialIdeal P)
    (hSbot : sInf (S : Set (Ideal R)) = ⊥)
    {P : Ideal R} (hPS : P ∈ S) :
    ∃ n, 0 < n ∧
      (fun Q : Ideal R => Ideal.map (σ : R →+* R) Q)^[n] P = P := by
  let F : Ideal R → Ideal R := fun Q => Ideal.map (σ : R →+* R) Q
  have hFsurj : Function.Surjective F := by
    intro Q
    refine ⟨Ideal.map (σ.symm : R →+* R) Q, ?_⟩
    simp only [F, Ideal.map_map]
    convert Ideal.map_id Q
    ext x
    simp
  have hback : ∀ Q, F Q ∈ (S : Set (Ideal R)) → Q ∈ (S : Set (Ideal R)) := by
    intro Q hFQS
    have hFQmin := hSmin (F Q) hFQS
    have hQmin : IsMinimalPrimeDifferentialIdeal Q := by
      have hbackmin := hFQmin.map_ringEquiv σ.symm (commutesDeriv_symm' σ hσ)
      simpa [F, Ideal.map_map] using hbackmin
    exact mem_finite_minimalPrimeDifferential_family S hSmin hSbot hQmin
  exact exists_pos_iterate_eq_self_of_backwardStable hFsurj
    S.finite_toSet hback hPS

/-- In a `σ`-`δ`-simple reduced ring, the automorphism acts transitively on every finite intrinsic
family of minimal differential-prime components. -/
theorem exists_iterate_map_eq_of_isSigmaDeltaSimple
    [Nontrivial R] (σ : R ≃+* R) (hσ : CommutesDeriv σ)
    (hsimple : IsSigmaDeltaSimple σ)
    (S : Finset (Ideal R))
    (hSmin : ∀ P ∈ S, IsMinimalPrimeDifferentialIdeal P)
    (hSbot : sInf (S : Set (Ideal R)) = ⊥)
    {P Q : Ideal R} (hPS : P ∈ S) (hQS : Q ∈ S) :
    ∃ n : ℕ, (fun J : Ideal R => Ideal.map (σ : R →+* R) J)^[n] P = Q := by
  classical
  let F : Ideal R → Ideal R := fun J => Ideal.map (σ : R →+* R) J
  obtain ⟨period, hperiodPos, hperiod⟩ :=
    exists_pos_iterate_map_eq_self_of_minimalPrimeDifferential σ hσ S hSmin hSbot hPS
  let O : Finset (Ideal R) := S.filter (fun J => ∃ n : ℕ, F^[n] P = J)
  have hPO : P ∈ O := Finset.mem_filter.mpr ⟨hPS, ⟨0, rfl⟩⟩
  have hpre : ∀ J ∈ O, ∃ U ∈ O, F U = J := by
    intro J hJO
    obtain ⟨hJS, n, hn⟩ := Finset.mem_filter.mp hJO
    cases n with
    | zero =>
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hperiodPos)
        refine ⟨F^[k] P, Finset.mem_filter.mpr ⟨?_, ⟨k, rfl⟩⟩, ?_⟩
        · have hmin := (hSmin P hPS).map_ringEquiv σ hσ
          have hiterMin : IsMinimalPrimeDifferentialIdeal (F^[k] P) := by
            induction k with
            | zero => simpa using hSmin P hPS
            | succ k ih =>
                rw [Function.iterate_succ_apply']
                exact ih.map_ringEquiv σ hσ
          exact mem_finite_minimalPrimeDifferential_family S hSmin hSbot hiterMin
        · rw [← Function.iterate_succ_apply', hperiod]
          exact hn.symm
    | succ n =>
        refine ⟨F^[n] P, Finset.mem_filter.mpr ⟨?_, ⟨n, rfl⟩⟩, ?_⟩
        · have hiterMin : IsMinimalPrimeDifferentialIdeal (F^[n] P) := by
            induction n with
            | zero => simpa using hSmin P hPS
            | succ n ih =>
                rw [Function.iterate_succ_apply']
                exact ih.map_ringEquiv σ hσ
          exact mem_finite_minimalPrimeDifferential_family S hSmin hSbot hiterMin
        · rw [← Function.iterate_succ_apply']
          exact hn
  have hOeq : O = S := by
    by_contra hOS
    have hOSub : O ⊆ S := Finset.filter_subset _ _
    have hproper : ∃ J ∈ S, J ∉ O := by
      by_contra hnone
      push Not at hnone
      exact hOS (Finset.Subset.antisymm hOSub hnone)
    obtain ⟨J, hJS, hJnotO⟩ := hproper
    let I : Ideal R := sInf (O : Set (Ideal R))
    have hIneBot : I ≠ ⊥ := by
      intro hIbot
      obtain ⟨U, hUO, hUJ⟩ := exists_mem_le_of_sInf_le_isPrime O
        (hSmin J hJS).1 (by rw [show sInf (O : Set (Ideal R)) = ⊥ from hIbot]; exact bot_le)
      have hUS : U ∈ S := hOSub hUO
      have hJU := (hSmin J hJS).2.2 U (hSmin U hUS).1
        (hSmin U hUS).2.1 hUJ
      exact hJnotO ((show U = J from le_antisymm hUJ hJU) ▸ hUO)
    have hIneTop : I ≠ ⊤ := by
      intro hItop
      have htopP : (⊤ : Ideal R) ≤ P := hItop ▸ sInf_le hPO
      exact (hSmin P hPS).1.ne_top (top_unique htopP)
    have hIstable : IsSigmaDeltaIdeal σ I := by
      refine ⟨?_, ?_⟩
      · intro x hx
        apply le_sInf
        intro J hJO
        obtain ⟨U, hUO, hFU⟩ := hpre J hJO
        rw [← hFU]
        exact Ideal.mem_map_of_mem (σ : R →+* R) ((sInf_le hUO) hx)
      · intro x hx
        apply le_sInf
        intro J hJO
        have hJS : J ∈ S := hOSub hJO
        exact (hSmin J hJS).2.1 x ((sInf_le hJO) hx)
    rcases hsimple I hIstable with hIbot | hItop
    · exact hIneBot hIbot
    · exact hIneTop hItop
  have hQO : Q ∈ O := hOeq.symm ▸ hQS
  exact (Finset.mem_filter.mp hQO).2

end

end GaloisForLFunctions.HTGeometry
