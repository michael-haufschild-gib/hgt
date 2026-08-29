import GaloisForLFunctions.HTGeometry.RittBasisTrivialContraction
import GaloisForLFunctions.HTGeometry.RadDiffFGTransfer
import GaloisForLFunctions.HTGeometry.ParameterizedPrimitiveQuotient
import GaloisForLFunctions.HTGeometry.DifferentialLurothComponentTransfer

/-!
# Ritt's basis theorem over a coefficient ring

The contraction of a radical differential ideal of `R{y}` to the coefficients is a radical
differential ideal of `R`, so it is the radical differential ideal of a finite set as soon as `R`
itself has that property.  Killing it turns the coefficient ring into a differential domain again
and makes the contraction trivial, which is the only extra hypothesis the reduction argument needs.

Finite generation then climbs back along the quotient map, because the kernel is carried by the
finite set generating the contraction.

* `radDiffFG_differentialPolynomial_of_base` — one differential indeterminate over a coefficient
  ring in which every radical differential ideal is the radical differential ideal of a finite set.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

attribute [local instance] differentialPolynomialDifferential

/-- The image of a finitely generated radical differential ideal containing the kernel is finitely
generated. -/
theorem isRadDiffFG_map_of_surjective {A B : Type*} [CommRing A] [Differential A]
    [CommRing B] [Differential B] (f : A →+* B)
    (hf : ∀ x, f (Differential.deriv x) = Differential.deriv (f x))
    (hsurj : Function.Surjective f) {I : Ideal A} (hker : RingHom.ker f ≤ I)
    (hrad : I.IsRadical) (hδ : ∀ x ∈ I, Differential.deriv x ∈ I)
    (hI : IsRadDiffFG I) : IsRadDiffFG (Ideal.map f I) := by
  classical
  obtain ⟨T, hT⟩ := hI
  refine ⟨T.image f, le_antisymm ?_ ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have hmem : f x ∈ radicalDifferentialIdeal (f '' (T : Set A)) := by
      rw [hT] at hx
      exact map_mem_radicalDifferentialIdeal f hf (T : Set A) hx
    show f x ∈ radicalDifferentialIdeal ((T.image f : Finset B) : Set B)
    rwa [Finset.coe_image]
  · refine radicalDifferentialIdeal_le ?_ (isRadical_map_of_surjective f hsurj hker hrad)
      (deriv_mem_map_of_surjective f hf hsurj hδ)
    intro y hy
    rw [Finset.coe_image] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    refine Ideal.mem_map_of_mem f ?_
    rw [hT]
    exact subset_radicalDifferentialIdeal _ ht

variable {R : Type*} [CommRing R] [Algebra ℚ R] [Differential R]

/-- **Ritt's basis theorem in one differential indeterminate over a coefficient ring.**  If every
radical differential ideal of the differential domain `R` is the radical differential ideal of a
finite set, the same holds in `R{y}`. -/
theorem radDiffFG_differentialPolynomial_of_base
    (hR : ∀ J : Ideal R, J.IsRadical → (∀ x ∈ J, Differential.deriv x ∈ J) → IsRadDiffFG J)
    (I : Ideal (DifferentialPolynomial Unit R))
    (hrad : I.IsRadical) (hδ : ∀ x ∈ I, Differential.deriv x ∈ I) :
    IsRadDiffFG I := by
  classical
  by_contra hIfg
  obtain ⟨M, hMrad, hMδ, hMfg, hMmax⟩ := exists_maximal_not_radDiffFG ⟨I, hrad, hδ, hIfg⟩
  have hMtop : M ≠ ⊤ := fun h => hMfg (h ▸ isRadDiffFG_top)
  have hMprime : M.IsPrime :=
    ⟨hMtop, fun {x y} hxy => mem_or_mem_of_maximal_not_radDiffFG hMrad hMδ hMfg hMmax hxy⟩
  set p : Ideal R := Ideal.comap (MvPolynomial.C : R →+* DifferentialPolynomial Unit R) M with hp
  haveI hpprime : p.IsPrime := Ideal.comap_isPrime _ M
  have hprad : p.IsRadical := hpprime.isRadical
  have hCδ : ∀ c : R,
      (MvPolynomial.C (Differential.deriv c) : DifferentialPolynomial Unit R)
        = Differential.deriv (MvPolynomial.C c) :=
    fun c => (differentialPolynomialOverDerivation_C c).symm
  have hpδ : ∀ x ∈ p, Differential.deriv x ∈ p := by
    intro x hx
    show (MvPolynomial.C (Differential.deriv x) : DifferentialPolynomial Unit R) ∈ M
    rw [hCδ x]
    exact hMδ _ hx
  obtain ⟨T₀, hT₀⟩ := hR p hprad hpδ
  letI : Differential (R ⧸ p) := ⟨quotientDerivation Differential.deriv p hpδ⟩
  haveI : IsDomain (R ⧸ p) := Ideal.Quotient.isDomain p
  letI : Algebra ℚ (R ⧸ p) :=
    ((Ideal.Quotient.mk p).comp (algebraMap ℚ R)).toAlgebra
  haveI : CharZero (R ⧸ p) :=
    charZero_of_injective_algebraMap (R := ℚ) (A := R ⧸ p)
      ((algebraMap ℚ (R ⧸ p)).injective)
  have hmkδ : ∀ c : R, Ideal.Quotient.mk p (Differential.deriv c)
      = Differential.deriv (Ideal.Quotient.mk p c) := fun _ => rfl
  set π : DifferentialPolynomial Unit R →+* DifferentialPolynomial Unit (R ⧸ p) :=
    MvPolynomial.map (Ideal.Quotient.mk p) with hπ
  have hπsurj : Function.Surjective π :=
    MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hπδ : ∀ x, π (Differential.deriv x) = Differential.deriv (π x) := fun x =>
    map_differentialPolynomialOverDerivation_of_commutes (Ideal.Quotient.mk p) hmkδ x
  have hkerπ : RingHom.ker π = Ideal.map (MvPolynomial.C : R →+* _) p := by
    rw [hπ, MvPolynomial.ker_map, Ideal.mk_ker]
  have hkerM : RingHom.ker π ≤ M := by
    rw [hkerπ, Ideal.map_le_iff_le_comap]
  have hT₀p : ↑T₀ ⊆ (p : Set R) := by
    rw [hT₀]
    exact subset_radicalDifferentialIdeal _
  have hT₀M : ↑(T₀.image (MvPolynomial.C : R →+* DifferentialPolynomial Unit R))
      ⊆ (M : Set (DifferentialPolynomial Unit R)) := by
    intro y hy
    rw [Finset.coe_image] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    exact hT₀p ht
  have hkerT : RingHom.ker π ≤ radicalDifferentialIdeal
      ((T₀.image (MvPolynomial.C : R →+* DifferentialPolynomial Unit R) : Finset _) : Set _) := by
    rw [hkerπ, Ideal.map_le_iff_le_comap]
    intro x hx
    have hx' : x ∈ radicalDifferentialIdeal (T₀ : Set R) := by rw [← hT₀]; exact hx
    have hmem := map_mem_radicalDifferentialIdeal
      (MvPolynomial.C : R →+* DifferentialPolynomial Unit R) hCδ (T₀ : Set R) hx'
    show (MvPolynomial.C x : DifferentialPolynomial Unit R) ∈
      radicalDifferentialIdeal
        ((T₀.image (MvPolynomial.C : R →+* DifferentialPolynomial Unit R) : Finset _) : Set _)
    rwa [Finset.coe_image]
  set N : Ideal (DifferentialPolynomial Unit (R ⧸ p)) := Ideal.map π M with hN
  have hNrad : N.IsRadical := isRadical_map_of_surjective π hπsurj hkerM hMrad
  have hNδ : ∀ y ∈ N, Differential.deriv y ∈ N :=
    deriv_mem_map_of_surjective π hπδ hπsurj hMδ
  have hcm : Ideal.comap π N = M := by
    rw [hN, Ideal.comap_map_of_surjective π hπsurj M]
    exact sup_eq_left.mpr hkerM
  have hNprime : N.IsPrime := by
    constructor
    · intro htop
      apply hMtop
      rw [← hcm, htop, Ideal.comap_top]
    · intro x y hxy
      obtain ⟨a, rfl⟩ := hπsurj x
      obtain ⟨b, rfl⟩ := hπsurj y
      have hab : a * b ∈ M := by
        rw [← hcm]
        show π (a * b) ∈ N
        rw [map_mul]
        exact hxy
      rcases hMprime.mem_or_mem hab with h | h
      · exact Or.inl (Ideal.mem_map_of_mem π h)
      · exact Or.inr (Ideal.mem_map_of_mem π h)
  have hNC : ∀ r : R ⧸ p,
      (MvPolynomial.C r : DifferentialPolynomial Unit (R ⧸ p)) ∈ N → r = 0 := by
    intro r hr
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    have hmem : MvPolynomial.C a ∈ Ideal.comap π N := by
      show π (MvPolynomial.C a) ∈ N
      rw [hπ, MvPolynomial.map_C]
      exact hr
    rw [hcm] at hmem
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hNmax : ∀ J : Ideal (DifferentialPolynomial Unit (R ⧸ p)), J.IsRadical →
      (∀ x ∈ J, Differential.deriv x ∈ J) → N < J → IsRadDiffFG J := by
    intro J hJrad hJδ hNJ
    have hJcrad : (Ideal.comap π J).IsRadical := by
      intro x hx
      obtain ⟨n, hn⟩ := hx
      refine hJrad ⟨n, ?_⟩
      show π x ^ n ∈ J
      rw [← map_pow]
      exact hn
    have hJcδ : ∀ x ∈ Ideal.comap π J, Differential.deriv x ∈ Ideal.comap π J := by
      intro x hx
      show π (Differential.deriv x) ∈ J
      rw [hπδ x]
      exact hJδ _ hx
    have hMle : M < Ideal.comap π J := by
      refine lt_of_le_of_ne ?_ ?_
      · intro x hx
        exact hNJ.1 (Ideal.mem_map_of_mem π hx)
      · intro heq
        have hJ : Ideal.map π (Ideal.comap π J) = J :=
          Ideal.map_comap_of_surjective π hπsurj J
        rw [← heq] at hJ
        exact absurd hJ (ne_of_lt hNJ)
    have hkerJ : RingHom.ker π ≤ Ideal.comap π J := le_trans hkerM hMle.le
    have hfg := hMmax _ hJcrad hJcδ hMle
    have := isRadDiffFG_map_of_surjective π hπδ hπsurj hkerJ hJcrad hJcδ hfg
    rwa [Ideal.map_comap_of_surjective π hπsurj J] at this
  have hNfg : IsRadDiffFG N :=
    radDiffFG_of_trivialContraction N hNrad hNδ hNC hNmax hNprime
  exact hMfg (isRadDiffFG_of_map π hπδ hπsurj hMrad hMδ hkerM hT₀M hkerT hNfg)

end

end GaloisForLFunctions.HTGeometry
