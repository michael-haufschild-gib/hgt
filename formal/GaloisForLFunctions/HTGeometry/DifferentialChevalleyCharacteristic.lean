import GaloisForLFunctions.HTGeometry.RittRingGeneralComponent
import GaloisForLFunctions.HTGeometry.RadicalDifferentialIdealAvoiding
import GaloisForLFunctions.HTGeometry.MvPolynomialGaussAscent
import GaloisForLFunctions.HTGeometry.DifferentialSystemSolution
import GaloisForLFunctions.HTGeometry.ComponentFactorExclusion

/-!
# Specializing a differential characteristic certificate

This file supplies the algebraic core of differential Chevalley extension.  A characteristic
polynomial, its saturation certificate, and a lower-jet Bezout witness survive any coefficient
specialization that preserves their finite nonvanishing guard.  The resulting specialized
relations lie in a prime differential ideal.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open scoped Differential

noncomputable section

attribute [local instance] differentialPolynomialOverDifferential

variable {R K : Type*} [CommRing R] [Differential R]
  [Field K] [CharZero K] [Differential K]

omit [CharZero K] in
/-- A differential-ideal certificate maps from a coefficient ring into the differential principal
ideal over a differential field. -/
theorem map_mem_differentialPolynomialIterateIdeal_of_mem_diffPoly
    (f : R →+* K) (hfδ : ∀ r : R, f (Differential.deriv r) = Differential.deriv (f r))
    {A Q : DifferentialPolynomial Unit R} (hQ : Q ∈ diffPolyIterateIdeal A) :
    MvPolynomial.map f Q ∈
      differentialPolynomialIterateIdeal (MvPolynomial.map f A) := by
  let S := DifferentialPolynomial Unit R
  change Q ∈ Submodule.span S (Set.range fun n : ℕ => diffPolyIterate n A) at hQ
  refine Submodule.span_induction (hx := hQ) ?_ ?_ ?_ ?_
  · rintro _ ⟨n, rfl⟩
    rw [map_diffPolyIterate_of_commutes f hfδ,
      diffPolyIterate_eq_iterateOver]
    exact differentialPolynomialIterateOver_mem_iterateIdeal _ _
  · simp
  · intro P Q _ _ hP hQ
    simpa using (Ideal.add_mem _ hP hQ)
  · intro c P _ hP
    simpa [smul_eq_mul] using
      (differentialPolynomialIterateIdeal (MvPolynomial.map f A)).mul_mem_left
        (MvPolynomial.map f c) hP

/-- A characteristic saturation certificate survives a coefficient specialization while one
marked polynomial remains outside the resulting prime differential ideal. -/
theorem exists_primeDifferentialIdeal_over_map_of_characteristicCertificate_avoiding
    (f : R →+* K) (hfδ : ∀ r : R, f (Differential.deriv r) = Differential.deriv (f r))
    (I : Ideal (DifferentialPolynomial Unit R))
    (A U V N X Y M W H : DifferentialPolynomial Unit R) (a b : ℕ)
    (hAvars : A.vars.Nonempty)
    (hsat : ∀ Q ∈ I, ∃ a b : ℕ,
      scalarDifferentialPolynomialInitial A ^ a *
          (scalarDifferentialPolynomialSeparant A ^ b * Q) ∈
        diffPolyIterateIdeal A)
    (horder : scalarDifferentialPolynomialOrder (MvPolynomial.map f A) =
      scalarDifferentialPolynomialOrder A)
    (hvC : ((), scalarDifferentialPolynomialOrder A) ∈
      (MvPolynomial.map f A).vars)
    (hinit : MvPolynomial.map f (scalarDifferentialPolynomialInitial A) ≠ 0)
    (hN0 : MvPolynomial.map f N ≠ 0)
    (hNv : ((), scalarDifferentialPolynomialOrder A) ∉ N.vars)
    (hbezout : U * A + V * scalarDifferentialPolynomialSeparant A = N)
    (hM0 : MvPolynomial.map f M ≠ 0)
    (hMv : ((), scalarDifferentialPolynomialOrder A) ∉ M.vars)
    (hbezoutM : X * A + Y * W = M)
    (hWorder : scalarDifferentialPolynomialOrder (MvPolynomial.map f W) ≤
      scalarDifferentialPolynomialOrder A)
    (hred : scalarDifferentialPolynomialInitial A ^ a *
      (scalarDifferentialPolynomialSeparant A ^ b * H) - W ∈ diffPolyIterateIdeal A) :
    ∃ P : Ideal (DifferentialPolynomial Unit K), P.IsPrime ∧
      (∀ Q ∈ P, Differential.deriv Q ∈ P) ∧
      (∀ Q ∈ I, MvPolynomial.map f Q ∈ P) ∧
      MvPolynomial.map f H ∉ P := by
  classical
  let C : DifferentialPolynomial Unit K := MvPolynomial.map f A
  let initK : DifferentialPolynomial Unit K :=
    MvPolynomial.map f (scalarDifferentialPolynomialInitial A)
  let sepK : DifferentialPolynomial Unit K :=
    MvPolynomial.map f (scalarDifferentialPolynomialSeparant A)
  let NK : DifferentialPolynomial Unit K := MvPolynomial.map f N
  let MK : DifferentialPolynomial Unit K := MvPolynomial.map f M
  let WK : DifferentialPolynomial Unit K := MvPolynomial.map f W
  let v : Unit × ℕ := ((), scalarDifferentialPolynomialOrder A)
  have hvA : v ∈ A.vars := by
    exact scalarDifferentialPolynomialLeader_mem_vars hAvars
  have hvC : v ∈ C.vars := by simpa [v, C] using hvC
  have horderC : scalarDifferentialPolynomialOrder C =
      scalarDifferentialPolynomialOrder A := by simpa [C] using horder
  have hC0 : C ≠ 0 := by
    intro h0
    simp [h0] at hvC
  obtain ⟨F, hFirr, hFdvd, hvF⟩ :=
    exists_irreducible_factor_mem_vars hC0 hvC
  have hFvars : F.vars.Nonempty := ⟨v, hvF⟩
  have hFvarsC : F.vars ⊆ C.vars :=
    mvPolynomial_vars_subset_of_dvd hFdvd hC0
  have hForderLe : scalarDifferentialPolynomialOrder F ≤
      scalarDifferentialPolynomialOrder C :=
    scalarDifferentialPolynomialOrder_le_of_vars_subset hFvarsC
  have hmF : scalarDifferentialPolynomialOrder A ≤
      scalarDifferentialPolynomialOrder F := by
    exact Finset.le_sup (f := fun q : Unit × ℕ => q.2) hvF
  have hForder : scalarDifferentialPolynomialOrder F =
      scalarDifferentialPolynomialOrder A := by
    omega
  obtain ⟨Pcomp, hPcompPrime, hIterF, hPcompDvd, -, -, -⟩ :=
    exists_component_prime_of_irreducible hFvars hFirr
  have hinitNot : initK ∉ Pcomp := by
    intro hmem
    have hinitVars : initK.vars ⊆ A.vars := fun q hq =>
      scalarDifferentialPolynomialInitial_vars_subset A
        (MvPolynomial.vars_map _ f hq)
    have hinitOrder : scalarDifferentialPolynomialOrder initK ≤
        scalarDifferentialPolynomialOrder F := by
      rw [hForder]
      unfold scalarDifferentialPolynomialOrder
      exact Finset.sup_le fun q hq => Finset.le_sup (hinitVars hq)
    have hdiv := hPcompDvd initK hmem hinitOrder
    have hvInit : v ∈ initK.vars :=
      mvPolynomial_vars_subset_of_dvd hdiv hinit hvF
    exact scalarDifferentialPolynomialLeader_not_mem_initial_vars A
      (MvPolynomial.vars_map _ f hvInit)
  have hsepOrder : scalarDifferentialPolynomialOrder sepK ≤
      scalarDifferentialPolynomialOrder F := by
    rw [hForder]
    unfold scalarDifferentialPolynomialOrder
    refine Finset.sup_le fun q hq => Finset.le_sup ?_
    exact scalarDifferentialPolynomialSeparant_vars_subset A
      (MvPolynomial.vars_map _ f hq)
  have hNvK : v ∉ NK.vars := fun hv => hNv (MvPolynomial.vars_map _ f hv)
  have hbezoutK : MvPolynomial.map f U * C + MvPolynomial.map f V * sepK = NK := by
    simpa [C, sepK, NK] using congrArg (MvPolynomial.map f) hbezout
  have hsepNot : sepK ∉ Pcomp := by
    intro hmem
    have hsepDvd : F ∣ sepK := hPcompDvd sepK hmem hsepOrder
    have hNdvd : F ∣ NK := by
      rw [← hbezoutK]
      exact dvd_add (dvd_mul_of_dvd_right hFdvd _) (dvd_mul_of_dvd_right hsepDvd _)
    exact hNvK (mvPolynomial_vars_subset_of_dvd hNdvd hN0 hvF)
  have hMvK : v ∉ MK.vars := fun hv => hMv (MvPolynomial.vars_map _ f hv)
  have hWorderF : scalarDifferentialPolynomialOrder WK ≤
      scalarDifferentialPolynomialOrder F := by
    simpa [WK, hForder] using hWorder
  have hbezoutMK : MvPolynomial.map f X * C + MvPolynomial.map f Y * WK = MK := by
    simpa [C, WK, MK] using congrArg (MvPolynomial.map f) hbezoutM
  have hWNot : WK ∉ Pcomp := by
    intro hmem
    have hWdvd : F ∣ WK := hPcompDvd WK hmem hWorderF
    have hMdvd : F ∣ MK := by
      rw [← hbezoutMK]
      exact dvd_add (dvd_mul_of_dvd_right hFdvd _) (dvd_mul_of_dvd_right hWdvd _)
    exact hMvK (mvPolynomial_vars_subset_of_dvd hMdvd hM0 hvF)
  have havoidNot : initK * sepK * WK ∉ Pcomp := by
    intro hmem
    rcases hPcompPrime.mem_or_mem hmem with hpair | hM
    · rcases hPcompPrime.mem_or_mem hpair with hinit | hsep
      · exact hinitNot hinit
      · exact hsepNot hsep
    · exact hWNot hM
  let J₀ : Ideal (DifferentialPolynomial Unit K) :=
    (differentialPolynomialIterateIdeal F).radical
  have hJ₀rad : J₀.IsRadical := Ideal.radical_isRadical _
  have hJ₀δ : ∀ Q ∈ J₀, Differential.deriv Q ∈ J₀ := by
    intro Q hQ
    exact deriv_mem_radical (I := differentialPolynomialIterateIdeal F)
      (fun _ hZ => differentialPolynomialOverDerivation_mem_iterateIdeal (P := F) hZ) hQ
  have hJ₀le : J₀ ≤ Pcomp := by
    calc
      J₀ = (differentialPolynomialIterateIdeal F).radical := rfl
      _ ≤ Pcomp.radical := Ideal.radical_mono hIterF
      _ = Pcomp := hPcompPrime.isRadical.radical
  have havoidJ₀ : initK * sepK * WK ∉ J₀ := fun h => havoidNot (hJ₀le h)
  obtain ⟨P, hPprime, hPδ, hJ₀P, havoidP⟩ :=
    exists_isPrime_avoiding_radicalDifferential hJ₀rad hJ₀δ havoidJ₀
  have hFC : differentialPolynomialIterateIdeal C ≤
      differentialPolynomialIterateIdeal F :=
    differentialPolynomialIterateIdeal_le_of_dvd hFdvd
  have hinitP : initK ∉ P := by
    intro h
    exact havoidP (P.mul_mem_right WK (P.mul_mem_right sepK h))
  have hsepP : sepK ∉ P := by
    intro h
    exact havoidP (P.mul_mem_right WK (P.mul_mem_left initK h))
  have hWP : WK ∉ P := by
    intro h
    exact havoidP (P.mul_mem_left (initK * sepK) h)
  refine ⟨P, hPprime, hPδ, ?_, ?_⟩
  · intro Q hQI
    obtain ⟨c, d, hQsat⟩ := hsat Q hQI
    have hmapSat : MvPolynomial.map f
        (scalarDifferentialPolynomialInitial A ^ c *
          (scalarDifferentialPolynomialSeparant A ^ d * Q)) ∈
        differentialPolynomialIterateIdeal C :=
      map_mem_differentialPolynomialIterateIdeal_of_mem_diffPoly f hfδ hQsat
    have hmemP : initK ^ c * (sepK ^ d * MvPolynomial.map f Q) ∈ P := by
      apply hJ₀P
      apply Ideal.le_radical
      apply hFC
      simpa [initK, sepK, C] using hmapSat
    rcases hPprime.mem_or_mem hmemP with hic | hrest
    · exact absurd (hPprime.mem_of_pow_mem c hic) hinitP
    · rcases hPprime.mem_or_mem hrest with hsd | hQ
      · exact absurd (hPprime.mem_of_pow_mem d hsd) hsepP
      · exact hQ
  · intro hHP
    apply hWP
    have hmapRed :=
      map_mem_differentialPolynomialIterateIdeal_of_mem_diffPoly f hfδ hred
    have hredP : initK ^ a * (sepK ^ b * MvPolynomial.map f H) - WK ∈ P := by
      apply hJ₀P
      apply Ideal.le_radical
      apply hFC
      simpa [initK, sepK, C, WK] using hmapRed
    have hprodHP : initK ^ a * (sepK ^ b * MvPolynomial.map f H) ∈ P :=
      P.mul_mem_left _ (P.mul_mem_left _ hHP)
    rw [show WK =
        initK ^ a * (sepK ^ b * MvPolynomial.map f H) -
          (initK ^ a * (sepK ^ b * MvPolynomial.map f H) - WK) by ring]
    exact P.sub_mem hprodHP hredP

/-- A characteristic saturation certificate survives a coefficient specialization whenever the
characteristic order, its initial, and one lower-jet Bezout witness survive. -/
theorem exists_primeDifferentialIdeal_over_map_of_characteristicCertificate
    (f : R →+* K) (hfδ : ∀ r : R, f (Differential.deriv r) = Differential.deriv (f r))
    (I : Ideal (DifferentialPolynomial Unit R))
    (A U V N : DifferentialPolynomial Unit R)
    (hAvars : A.vars.Nonempty)
    (hsat : ∀ Q ∈ I, ∃ a b : ℕ,
      scalarDifferentialPolynomialInitial A ^ a *
          (scalarDifferentialPolynomialSeparant A ^ b * Q) ∈
        diffPolyIterateIdeal A)
    (horder : scalarDifferentialPolynomialOrder (MvPolynomial.map f A) =
      scalarDifferentialPolynomialOrder A)
    (hvC : ((), scalarDifferentialPolynomialOrder A) ∈
      (MvPolynomial.map f A).vars)
    (hinit : MvPolynomial.map f (scalarDifferentialPolynomialInitial A) ≠ 0)
    (hN0 : MvPolynomial.map f N ≠ 0)
    (hNv : ((), scalarDifferentialPolynomialOrder A) ∉ N.vars)
    (hbezout : U * A + V * scalarDifferentialPolynomialSeparant A = N) :
    ∃ P : Ideal (DifferentialPolynomial Unit K), P.IsPrime ∧
      (∀ Q ∈ P, Differential.deriv Q ∈ P) ∧
      ∀ Q ∈ I, MvPolynomial.map f Q ∈ P := by
  obtain ⟨P, hPprime, hPδ, hPI, -⟩ :=
    exists_primeDifferentialIdeal_over_map_of_characteristicCertificate_avoiding
      f hfδ I A U V N 0 1 1 1 1 0 0 hAvars hsat horder hvC hinit hN0 hNv hbezout
      (by simp) (by simp) (by simp)
      (by
        unfold scalarDifferentialPolynomialOrder
        simp)
      (by simp)
  exact ⟨P, hPprime, hPδ, hPI⟩

end

end GaloisForLFunctions.HTGeometry
