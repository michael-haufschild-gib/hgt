import GaloisForLFunctions.HTGeometry.DifferentialLurothComponentTransfer

/-!
# Gauss ascent: a primitive irreducible polynomial stays irreducible over the fraction field

Contraction of divisibility from the fraction field to a primitive polynomial over the coefficient
ring is the classical Gauss step, and the corpus already owns it.  The converse direction -- that
irreducibility of a primitive polynomial ascends to the fraction field -- is proved here for
multivariable polynomials in an arbitrary, possibly infinite, variable type.

The mechanism is the usual one: clear denominators of a would-be factorization into primitive
polynomials over the coefficient ring, contract the divisibility, and observe that the leftover
scalar is a unit because a product of primitive polynomials is primitive.
-/

namespace GaloisForLFunctions

noncomputable section

variable {R K σ : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
  [NormalizedGCDMonoid R] [Field K] [Algebra R K] [IsFractionRing R K]

omit [UniqueFactorizationMonoid R] [NormalizedGCDMonoid R] in
/-- A polynomial whose image under an injective coefficient map is a constant is a constant. -/
theorem eq_C_of_map_eq_C {T : MvPolynomial σ R} {c : K}
    (hT : MvPolynomial.map (algebraMap R K) T = MvPolynomial.C c) :
    T = MvPolynomial.C (T.coeff 0) := by
  classical
  refine MvPolynomial.ext _ _ fun s => ?_
  by_cases hs : (0 : σ →₀ ℕ) = s
  · subst hs
    simp
  · have hcoeff := congrArg (MvPolynomial.coeff s) hT
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C, if_neg hs] at hcoeff
    rw [MvPolynomial.coeff_C, if_neg hs]
    exact IsFractionRing.injective R K (by simpa using hcoeff)

/-- **Gauss ascent.**  A primitive irreducible multivariable polynomial over a unique factorization
domain remains irreducible over the fraction field. -/
theorem MvPolynomialPrimitive.irreducible_map {P : MvPolynomial σ R}
    (hprim : MvPolynomialPrimitive P) (hirr : Irreducible P) :
    Irreducible (MvPolynomial.map (algebraMap R K) P) := by
  classical
  have hP0 : P ≠ 0 := hirr.ne_zero
  have hmapinj : Function.Injective (MvPolynomial.map (σ := σ) (algebraMap R K)) :=
    MvPolynomial.map_injective _ (IsFractionRing.injective R K)
  have hmap0 : MvPolynomial.map (algebraMap R K) P ≠ 0 := fun h =>
    hP0 (hmapinj (by simpa using h))
  refine ⟨?_, ?_⟩
  · intro hu
    refine hirr.not_isUnit ?_
    have hdvd : MvPolynomial.map (algebraMap R K) P ∣
        MvPolynomial.map (algebraMap R K) (1 : MvPolynomial σ R) := by
      simpa using hu.dvd
    exact isUnit_of_dvd_one (hprim.dvd_of_fraction_map_dvd hP0 hdvd)
  · intro g h hgh
    have hg0 : g ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hgh
      exact hmap0 hgh
    have hh0 : h ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hgh
      exact hmap0 hgh
    obtain ⟨g₀, hg₀0, hg₀prim, a, hga⟩ :=
      exists_primitive_mvPolynomial_fraction_clear (R := R) (K := K) (σ := σ) hg0
    obtain ⟨h₀, hh₀0, hh₀prim, b, hhb⟩ :=
      exists_primitive_mvPolynomial_fraction_clear (R := R) (K := K) (σ := σ) hh0
    have hprod : MvPolynomial.map (algebraMap R K) (g₀ * h₀) =
        MvPolynomial.C ((a : K) * (b : K)) * MvPolynomial.map (algebraMap R K) P := by
      rw [map_mul, hga, hhb, hgh, MvPolynomial.C_mul]
      ring
    have hdvdK : MvPolynomial.map (algebraMap R K) P ∣
        MvPolynomial.map (algebraMap R K) (g₀ * h₀) :=
      ⟨MvPolynomial.C ((a : K) * (b : K)), by rw [hprod]; ring⟩
    obtain ⟨T, hT⟩ := hprim.dvd_of_fraction_map_dvd hP0 hdvdK
    have hmapT : MvPolynomial.map (algebraMap R K) T =
        MvPolynomial.C ((a : K) * (b : K)) := by
      refine mul_left_cancel₀ hmap0 ?_
      rw [← map_mul, ← hT, hprod]
      ring
    have hTC : T = MvPolynomial.C (T.coeff 0) := eq_C_of_map_eq_C hmapT
    have hprimprod : MvPolynomialPrimitive (g₀ * h₀) :=
      hg₀prim.mul hh₀prim hg₀0 hh₀0
    have htunit : IsUnit (T.coeff 0) := by
      refine hprimprod (T.coeff 0) ⟨P, ?_⟩
      rw [hT]
      conv_lhs => rw [hTC]
      ring
    obtain ⟨t, ht⟩ := htunit
    have hCt : (MvPolynomial.C ((t : R)) : MvPolynomial σ R) *
        MvPolynomial.C ((t⁻¹ : Rˣ) : R) = 1 := by
      rw [← MvPolynomial.C_mul]
      simp
    have hTt : T = MvPolynomial.C ((t : R)) := by rw [hTC, ht]
    have hfac : g₀ * h₀ = P * MvPolynomial.C ((t : R)) := by rw [hT, hTt]
    have hPfac : P = (g₀ * MvPolynomial.C ((t⁻¹ : Rˣ) : R)) * h₀ := by
      calc P = (P * MvPolynomial.C ((t : R))) * MvPolynomial.C ((t⁻¹ : Rˣ) : R) := by
            rw [mul_assoc, hCt, mul_one]
        _ = (g₀ * h₀) * MvPolynomial.C ((t⁻¹ : Rˣ) : R) := by rw [hfac]
        _ = (g₀ * MvPolynomial.C ((t⁻¹ : Rˣ) : R)) * h₀ := by ring
    rcases hirr.isUnit_or_isUnit hPfac with hu | hu
    · left
      have hg₀unit : IsUnit g₀ := isUnit_of_mul_isUnit_left hu
      have hmapunit : IsUnit (MvPolynomial.map (algebraMap R K) g₀) :=
        hg₀unit.map (MvPolynomial.map (algebraMap R K))
      rw [hga] at hmapunit
      exact isUnit_of_mul_isUnit_right hmapunit
    · right
      have hmapunit : IsUnit (MvPolynomial.map (algebraMap R K) h₀) :=
        hu.map (MvPolynomial.map (algebraMap R K))
      rw [hhb] at hmapunit
      exact isUnit_of_mul_isUnit_right hmapunit

section Support

variable {S : Type*} [CommRing S] [IsDomain S] {τ : Type*}

/-- Over a domain, multiplying by a nonzero polynomial keeps every variable. -/
theorem mvPolynomial_mem_vars_mul_left {f g : MvPolynomial τ S} (hf : f ≠ 0) (hg : g ≠ 0)
    {v : τ} (hv : v ∈ f.vars) : v ∈ (f * g).vars := by
  classical
  rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero] at hv ⊢
  rw [MvPolynomial.degreeOf_mul_eq hf hg]
  omega

/-- Over a domain, multiplying by a nonzero polynomial keeps every variable of the second factor. -/
theorem mvPolynomial_mem_vars_mul_right {f g : MvPolynomial τ S} (hf : f ≠ 0) (hg : g ≠ 0)
    {v : τ} (hv : v ∈ g.vars) : v ∈ (f * g).vars := by
  rw [mul_comm]
  exact mvPolynomial_mem_vars_mul_left hg hf hv

/-- **A variable of a polynomial occurs in one of its irreducible factors.** -/
theorem exists_irreducible_factor_mem_vars [UniqueFactorizationMonoid S]
    {X : MvPolynomial τ S} (hX : X ≠ 0) {v : τ} (hv : v ∈ X.vars) :
    ∃ A : MvPolynomial τ S, Irreducible A ∧ A ∣ X ∧ v ∈ A.vars := by
  classical
  induction X using WfDvdMonoid.induction_on_irreducible with
  | zero => exact absurd rfl hX
  | unit u hu =>
      exfalso
      have hsubset : (u : MvPolynomial τ S).vars ⊆ (1 : MvPolynomial τ S).vars :=
        mvPolynomial_vars_subset_of_dvd hu.dvd one_ne_zero
      have : v ∈ (1 : MvPolynomial τ S).vars := hsubset hv
      simp at this
  | mul A p hA0 hp ih =>
      have hp0 : p ≠ 0 := hp.ne_zero
      rcases Finset.mem_union.mp (MvPolynomial.vars_mul p A hv) with hvp | hvA
      · exact ⟨p, hp, dvd_mul_right p A, hvp⟩
      · obtain ⟨B, hBirr, hBdvd, hBvars⟩ := ih hA0 hvA
        exact ⟨B, hBirr, hBdvd.trans (dvd_mul_left A p), hBvars⟩

end Support

end

end GaloisForLFunctions
