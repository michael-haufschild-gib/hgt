import GaloisForLFunctions.HTGeometry.MvPolynomialHomogeneousDehomogenization
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# Prime descent through a projective chart

This module proves the integral affine-chart theorem needed for normalized Hankel secants.  If a
homogeneous prime ideal avoids a distinguished coordinate, then setting that coordinate to one
maps it to a prime ideal.  The proof is constructive at polynomial level: affine polynomials are
homogenized by homogeneous components, ideal membership is lifted degree by degree, and prime
cancellation occurs before dehomogenization.  No field, reducedness, or Noetherian hypothesis is
used.
-/

namespace GaloisForLFunctions
noncomputable section

open MvPolynomial
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Homogenize a tail polynomial to degree `d` using the distinguished `none` coordinate. -/
def optionHeadHomogenize {R σ : Type*} [CommSemiring R]
    (P : MvPolynomial σ R) (d : ℕ) : MvPolynomial (Option σ) R :=
  ∑ k ∈ Finset.range (d + 1),
    MvPolynomial.X none ^ (d - k) *
      MvPolynomial.rename some (MvPolynomial.homogeneousComponent k P)

theorem optionHeadHomogenize_isHomogeneous {R σ : Type*} [CommSemiring R]
    (P : MvPolynomial σ R) (d : ℕ) :
    (optionHeadHomogenize P d).IsHomogeneous d := by
  apply MvPolynomial.IsHomogeneous.sum (Finset.range (d + 1))
  intro k hk
  have hkd : k ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hx : (MvPolynomial.X (none : Option σ) ^ (d - k) :
      MvPolynomial (Option σ) R).IsHomogeneous (d - k) := by
    simpa using (MvPolynomial.isHomogeneous_X R (none : Option σ)).pow (d - k)
  have hc : (MvPolynomial.rename some
      (MvPolynomial.homogeneousComponent k P)).IsHomogeneous k :=
    (MvPolynomial.homogeneousComponent_isHomogeneous k P).rename_isHomogeneous
  convert hx.mul hc using 1
  omega

/-- Tail inclusion is a section of distinguished-coordinate dehomogenization. -/
theorem optionHeadDehomogenize_rename_some {R σ : Type*} [CommSemiring R]
    (P : MvPolynomial σ R) :
    optionHeadDehomogenize (MvPolynomial.rename some P) = P := by
  let f : MvPolynomial σ R →+* MvPolynomial σ R :=
    optionHeadDehomogenize.comp (MvPolynomial.rename some).toRingHom
  have hf : f = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [f, optionHeadDehomogenize]
    · intro i
      simp [f, optionHeadDehomogenize]
  exact RingHom.congr_fun hf P

/-- Homogenization followed by the affine-chart map recovers the source polynomial. -/
theorem optionHeadDehomogenize_optionHeadHomogenize
    {R σ : Type*} [CommSemiring R]
    (P : MvPolynomial σ R) (d : ℕ) (hP : P.totalDegree ≤ d) :
    optionHeadDehomogenize (optionHeadHomogenize P d) = P := by
  rw [optionHeadHomogenize, map_sum]
  simp only [map_mul, map_pow, optionHeadDehomogenize_X_none, one_pow,
    one_mul, optionHeadDehomogenize_rename_some]
  have hsum : (∑ k ∈ Finset.range (d + 1),
      MvPolynomial.homogeneousComponent k P) =
      ∑ k ∈ Finset.range (P.totalDegree + 1),
        MvPolynomial.homogeneousComponent k P := by
    symm
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hP))
    intro k hkbig hksmall
    apply MvPolynomial.homogeneousComponent_eq_zero
    have hkge : P.totalDegree + 1 ≤ k := Nat.le_of_not_gt
      (fun h => hksmall (Finset.mem_range.mpr h))
    omega
  rw [hsum, MvPolynomial.sum_homogeneousComponent]

theorem optionHeadDehomogenize_surjective {R σ : Type*} [CommSemiring R] :
    Function.Surjective (optionHeadDehomogenize :
      MvPolynomial (Option σ) R → MvPolynomial σ R) := by
  intro P
  exact ⟨MvPolynomial.rename some P, optionHeadDehomogenize_rename_some P⟩

/-- Dehomogenization is injective on each fixed homogeneous sector. -/
theorem eq_of_isHomogeneous_of_optionHeadDehomogenize_eq
    {R σ : Type*} [CommRing R] [Nontrivial R]
    {P Q : MvPolynomial (Option σ) R} {d : ℕ}
    (hP : P.IsHomogeneous d) (hQ : Q.IsHomogeneous d)
    (hdehom : optionHeadDehomogenize P = optionHeadDehomogenize Q) : P = Q := by
  by_contra hne
  have hsub : (P - Q).IsHomogeneous d := hP.sub hQ
  have hsub0 : P - Q ≠ 0 := sub_ne_zero.mpr hne
  have hfaith := optionHeadDehomogenize_ne_zero_of_isHomogeneous hsub hsub0
  apply hfaith
  rw [map_sub, hdehom, sub_self]

/-- Homogenization is multiplicative when degrees are chosen additively. -/
theorem optionHeadHomogenize_mul
    {R σ : Type*} [CommRing R] [Nontrivial R]
    (P Q : MvPolynomial σ R) :
    optionHeadHomogenize (P * Q) (P.totalDegree + Q.totalDegree) =
      optionHeadHomogenize P P.totalDegree * optionHeadHomogenize Q Q.totalDegree := by
  apply eq_of_isHomogeneous_of_optionHeadDehomogenize_eq
  · exact optionHeadHomogenize_isHomogeneous _ _
  · exact (optionHeadHomogenize_isHomogeneous P P.totalDegree).mul
      (optionHeadHomogenize_isHomogeneous Q Q.totalDegree)
  rw [map_mul]
  rw [optionHeadDehomogenize_optionHeadHomogenize _ _
      (MvPolynomial.totalDegree_mul P Q)]
  rw [optionHeadDehomogenize_optionHeadHomogenize _ _ le_rfl,
    optionHeadDehomogenize_optionHeadHomogenize _ _ le_rfl]

/-- Raising homogenization degree only introduces a power of the distinguished coordinate. -/
theorem optionHeadHomogenize_raise
    {R σ : Type*} [CommRing R] [Nontrivial R]
    (P : MvPolynomial σ R) {d D : ℕ}
    (hPd : P.totalDegree ≤ d) (hdD : d ≤ D) :
    optionHeadHomogenize P D =
      MvPolynomial.X none ^ (D - d) * optionHeadHomogenize P d := by
  apply eq_of_isHomogeneous_of_optionHeadDehomogenize_eq
  · exact optionHeadHomogenize_isHomogeneous _ _
  · have hx : (MvPolynomial.X (none : Option σ) ^ (D - d) :
        MvPolynomial (Option σ) R).IsHomogeneous (D - d) := by
      simpa using (MvPolynomial.isHomogeneous_X R (none : Option σ)).pow (D - d)
    convert hx.mul (optionHeadHomogenize_isHomogeneous P d) using 1
    omega
  rw [map_mul, map_pow, optionHeadDehomogenize_X_none, one_pow, one_mul,
    optionHeadDehomogenize_optionHeadHomogenize _ _ (hPd.trans hdD),
    optionHeadDehomogenize_optionHeadHomogenize _ _ hPd]

@[simp] theorem optionHeadHomogenize_one
    {R σ : Type*} [CommRing R] [Nontrivial R] (d : ℕ) :
    optionHeadHomogenize (1 : MvPolynomial σ R) d =
      MvPolynomial.X (none : Option σ) ^ d := by
  apply eq_of_isHomogeneous_of_optionHeadDehomogenize_eq
  · exact optionHeadHomogenize_isHomogeneous _ _
  · simpa using (MvPolynomial.isHomogeneous_X R (none : Option σ)).pow d
  rw [optionHeadDehomogenize_optionHeadHomogenize _ _ (by simp),
    map_pow, optionHeadDehomogenize_X_none, one_pow]

/-- Membership in a homogeneous ideal survives homogenizing its affine-chart image. -/
theorem optionHeadHomogenize_dehom_mem_of_mem
    {R σ : Type*} [CommRing R] [Nontrivial R]
    (I : Ideal (MvPolynomial (Option σ) R))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Option σ) R))
    {H : MvPolynomial (Option σ) R} (hH : H ∈ I) {D : ℕ}
    (hHD : H.totalDegree ≤ D)
    (hdehomD : (optionHeadDehomogenize H).totalDegree ≤ D) :
    optionHeadHomogenize (optionHeadDehomogenize H) D ∈ I := by
  let S : MvPolynomial (Option σ) R :=
    ∑ k ∈ Finset.range (D + 1),
      MvPolynomial.X none ^ (D - k) * MvPolynomial.homogeneousComponent k H
  have hSmem : S ∈ I := by
    apply Ideal.sum_mem
    intro k hk
    exact I.mul_mem_left _ (MvPolynomial.homogeneousComponent_mem_of_mem hI hH k)
  have hShom : S.IsHomogeneous D := by
    apply MvPolynomial.IsHomogeneous.sum (Finset.range (D + 1))
    intro k hk
    have hkD : k ≤ D := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hx : (MvPolynomial.X (none : Option σ) ^ (D - k) :
        MvPolynomial (Option σ) R).IsHomogeneous (D - k) := by
      simpa using (MvPolynomial.isHomogeneous_X R (none : Option σ)).pow (D - k)
    convert hx.mul (MvPolynomial.homogeneousComponent_isHomogeneous k H) using 1
    omega
  have hdehomS : optionHeadDehomogenize S = optionHeadDehomogenize H := by
    dsimp [S]
    rw [map_sum]
    simp only [map_mul, map_pow, optionHeadDehomogenize_X_none, one_pow, one_mul]
    have hsum : (∑ k ∈ Finset.range (D + 1),
        MvPolynomial.homogeneousComponent k H) = H := by
      have heq : (∑ k ∈ Finset.range (D + 1),
          MvPolynomial.homogeneousComponent k H) =
          ∑ k ∈ Finset.range (H.totalDegree + 1),
            MvPolynomial.homogeneousComponent k H := by
        symm
        apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hHD))
        intro k hkbig hksmall
        apply MvPolynomial.homogeneousComponent_eq_zero
        have hkge : H.totalDegree + 1 ≤ k := Nat.le_of_not_gt
          (fun h => hksmall (Finset.mem_range.mpr h))
        omega
      rw [heq, MvPolynomial.sum_homogeneousComponent]
    rw [← map_sum, hsum]
  have heq : optionHeadHomogenize (optionHeadDehomogenize H) D = S := by
    apply eq_of_isHomogeneous_of_optionHeadDehomogenize_eq
    · exact optionHeadHomogenize_isHomogeneous _ _
    · exact hShom
    rw [optionHeadDehomogenize_optionHeadHomogenize _ _ hdehomD]
    exact hdehomS.symm
  rwa [heq]

/-- **Projective-chart prime descent.** A homogeneous prime ideal avoiding the distinguished
coordinate remains prime after setting that coordinate to one. -/
theorem Ideal.IsPrime.map_optionHeadDehomogenize
    {R σ : Type*} [CommRing R] [Nontrivial R]
    (I : Ideal (MvPolynomial (Option σ) R)) (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Option σ) R))
    (hhead : MvPolynomial.X (none : Option σ) ∉ I) :
    (Ideal.map optionHeadDehomogenize I).IsPrime := by
  rw [Ideal.isPrime_iff]
  refine ⟨?_, ?_⟩
  · intro htop
    have hone : (1 : MvPolynomial σ R) ∈ Ideal.map optionHeadDehomogenize I := by
      rw [htop]
      trivial
    obtain ⟨H, hHI, hHone⟩ :=
      (Ideal.mem_map_iff_of_surjective optionHeadDehomogenize
        optionHeadDehomogenize_surjective).mp hone
    let D := H.totalDegree + 1
    have hHD : H.totalDegree ≤ D := by omega
    have hdehomD : (optionHeadDehomogenize H).totalDegree ≤ D := by
      rw [hHone]
      simp [D]
    have hLift := optionHeadHomogenize_dehom_mem_of_mem I hhom hHI hHD hdehomD
    rw [hHone] at hLift
    have hpow : MvPolynomial.X (none : Option σ) ^ D ∈ I := by
      rwa [optionHeadHomogenize_one] at hLift
    exact hhead ((hprime.pow_mem_iff_mem D (by omega)).mp hpow)
  · intro P Q hPQ
    obtain ⟨H, hHI, hHPQ⟩ :=
      (Ideal.mem_map_iff_of_surjective optionHeadDehomogenize
        optionHeadDehomogenize_surjective).mp hPQ
    let d := P.totalDegree + Q.totalDegree
    let D := H.totalDegree + d + 1
    have hHD : H.totalDegree ≤ D := by omega
    have hdehomD : (optionHeadDehomogenize H).totalDegree ≤ D := by
      rw [hHPQ]
      exact (MvPolynomial.totalDegree_mul P Q).trans (by omega)
    have hLift := optionHeadHomogenize_dehom_mem_of_mem I hhom hHI hHD hdehomD
    rw [hHPQ] at hLift
    have hdd : d ≤ D := by omega
    rw [optionHeadHomogenize_raise (P * Q)
      (MvPolynomial.totalDegree_mul P Q) hdd,
      optionHeadHomogenize_mul] at hLift
    have hfactor := hprime.mem_or_mem hLift
    rcases hfactor with hheadpow | hpq
    · have hexp : 0 < D - d := by simp [D, d]
      exact (hhead ((hprime.pow_mem_iff_mem (D - d) hexp).mp hheadpow)).elim
    · rcases hprime.mem_or_mem hpq with hp | hq
      · have hm := Ideal.mem_map_of_mem optionHeadDehomogenize hp
        rw [optionHeadDehomogenize_optionHeadHomogenize _ _ le_rfl] at hm
        exact Or.inl hm
      · have hm := Ideal.mem_map_of_mem optionHeadDehomogenize hq
        rw [optionHeadDehomogenize_optionHeadHomogenize _ _ le_rfl] at hm
        exact Or.inr hm

end
end GaloisForLFunctions
