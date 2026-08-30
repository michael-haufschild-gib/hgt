import GaloisForLFunctions.HTGeometry.AutPermutesRoots

/-!
# Finite automorphism orbits force algebraicity

The orbit product of a finite automorphism-stable packet has invariant coefficients.  If the
ambient fixed field is the base field, coefficientwise descent produces a nonzero base polynomial
vanishing at every orbit member.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Finset

variable {K L : Type*} [Field K] [CommRing L] [Algebra K L]

local instance : DecidableEq L := Classical.decEq L

/-- Monic polynomial whose roots are the members of a finite packet. -/
def finiteOrbitPolynomial (S : Finset L) : Polynomial L :=
  ∏ y ∈ S, (Polynomial.X - Polynomial.C y)

theorem finiteOrbitPolynomial_monic (S : Finset L) :
    (finiteOrbitPolynomial S).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro y _
  exact Polynomial.monic_X_sub_C y

theorem finiteOrbitPolynomial_eval_eq_zero {S : Finset L} {x : L} (hx : x ∈ S) :
    (finiteOrbitPolynomial S).eval x = 0 := by
  classical
  rw [finiteOrbitPolynomial]
  change (Polynomial.evalRingHom x) (∏ y ∈ S, (Polynomial.X - Polynomial.C y)) = 0
  rw [map_prod]
  exact Finset.prod_eq_zero hx (by simp)

/-- An automorphism maps the orbit polynomial to the polynomial of the image packet. -/
theorem finiteOrbitPolynomial_map (S : Finset L) (σ : L ≃ₐ[K] L) :
    (finiteOrbitPolynomial S).map σ.toRingHom =
      finiteOrbitPolynomial (S.image σ) := by
  classical
  rw [finiteOrbitPolynomial, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [finiteOrbitPolynomial, Finset.prod_image σ.injective.injOn]
  apply Finset.prod_congr rfl
  intro y _
  change Polynomial.X - Polynomial.C (σ y) = Polynomial.X - Polynomial.C (σ y)
  rfl

omit [Algebra K L] in
/-- A polynomial whose coefficients lie in a ring-homomorphism range descends coefficientwise. -/
theorem exists_map_polynomial_eq_of_coeff_mem_range
    (φ : K →+* L) (P : Polynomial L) (h : ∀ n, P.coeff n ∈ φ.range) :
    ∃ q : Polynomial K, q.map φ = P := by
  classical
  choose c hc using h
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1),
    Polynomial.C (c i) * Polynomial.X ^ i, ?_⟩
  ext i
  rw [Polynomial.coeff_map, Polynomial.finsetSum_coeff]
  by_cases hi : i ≤ P.natDegree
  · rw [Finset.sum_eq_single i]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one, hc]
    · intro b _ hb
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hb), mul_zero]
    · intro hcon
      exact absurd (Finset.mem_range.2 (by omega)) hcon
  · have hsum : (∑ b ∈ Finset.range (P.natDegree + 1),
        (Polynomial.C (c b) * Polynomial.X ^ b).coeff i) = 0 := by
      refine Finset.sum_eq_zero fun b hb => ?_
      have hbd : b < P.natDegree + 1 := Finset.mem_range.1 hb
      have hne : i ≠ b := by omega
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne, mul_zero]
    rw [hsum, map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

variable [Nontrivial L]

/-- A finite stable packet containing `x` makes `x` algebraic when every automorphism-fixed
coefficient descends to the base field. -/
theorem isAlgebraic_of_finite_stable_automorphism_orbit
    {x : L} {S : Finset L} (hx : x ∈ S)
    (hstable : ∀ σ : L ≃ₐ[K] L, S.image σ = S)
    (hfixed : ∀ y : L, (∀ σ : L ≃ₐ[K] L, σ y = y) →
      ∃ k : K, algebraMap K L k = y) :
    IsAlgebraic K x := by
  classical
  let P := finiteOrbitPolynomial S
  have hcoeff : ∀ n, P.coeff n ∈ (algebraMap K L).range := by
    intro n
    apply hfixed
    intro σ
    have hmap :
        (finiteOrbitPolynomial S).map σ.toRingEquiv.toRingHom =
          finiteOrbitPolynomial S := by
      rw [finiteOrbitPolynomial_map, hstable σ]
    have hc := congrArg (fun Q : Polynomial L => Q.coeff n) hmap
    change σ.toRingEquiv.toRingHom (P.coeff n) = P.coeff n
    simpa only [P, Polynomial.coeff_map] using hc
  obtain ⟨q, hq⟩ := exists_map_polynomial_eq_of_coeff_mem_range
    (algebraMap K L) P hcoeff
  have hP0 : P ≠ 0 := (finiteOrbitPolynomial_monic S).ne_zero
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.map_zero] at hq
    exact hP0 hq.symm
  refine ⟨q, hq0, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hq]
  exact finiteOrbitPolynomial_eval_eq_zero hx

/-- Finiteness of the full automorphism orbit forces algebraicity when the automorphism fixed
field is exactly the base field. -/
theorem isAlgebraic_of_finite_automorphismOrbit
    {x : L}
    (hfinite : (Set.range (fun σ : L ≃ₐ[K] L => σ x)).Finite)
    (hfixed : ∀ y : L, (∀ σ : L ≃ₐ[K] L, σ y = y) →
      ∃ k : K, algebraMap K L k = y) :
    IsAlgebraic K x := by
  classical
  let S := hfinite.toFinset
  have hx : x ∈ S := by
    have hxRange : x ∈ Set.range (fun σ : L ≃ₐ[K] L => σ x) :=
      ⟨AlgEquiv.refl, rfl⟩
    simpa only [S, Set.Finite.mem_toFinset] using hxRange
  have hstable : ∀ σ : L ≃ₐ[K] L, S.image σ = S := by
    intro σ
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy
      have hzRange : z ∈ Set.range (fun τ : L ≃ₐ[K] L => τ x) := by
        simpa only [S, Set.Finite.mem_toFinset] using hz
      obtain ⟨τ, rfl⟩ := hzRange
      have hyRange : y ∈ Set.range (fun τ : L ≃ₐ[K] L => τ x) :=
        ⟨τ.trans σ, hzy⟩
      simpa only [S, Set.Finite.mem_toFinset] using hyRange
    · intro hy
      have hyRange : y ∈ Set.range (fun τ : L ≃ₐ[K] L => τ x) := by
        simpa only [S, Set.Finite.mem_toFinset] using hy
      obtain ⟨τ, rfl⟩ := hyRange
      refine Finset.mem_image.mpr ⟨σ.symm (τ x), ?_, σ.apply_symm_apply (τ x)⟩
      have hzRange : σ.symm (τ x) ∈ Set.range (fun υ : L ≃ₐ[K] L => υ x) :=
        ⟨τ.trans σ.symm, rfl⟩
      simpa only [S, Set.Finite.mem_toFinset] using hzRange
  exact isAlgebraic_of_finite_stable_automorphism_orbit hx hstable hfixed

/-- A transcendental element has an infinite full automorphism orbit whenever the automorphism
fixed field is the base field. -/
theorem infinite_automorphismOrbit_of_transcendental
    {x : L} (hx : Transcendental K x)
    (hfixed : ∀ y : L, (∀ σ : L ≃ₐ[K] L, σ y = y) →
      ∃ k : K, algebraMap K L k = y) :
    (Set.range (fun σ : L ≃ₐ[K] L => σ x)).Infinite := by
  intro hfinite
  exact hx (isAlgebraic_of_finite_automorphismOrbit hfinite hfixed)

/-- A finite full automorphism group forces every element to be algebraic when its fixed field is
the base field. -/
theorem isAlgebraic_of_finite_automorphismGroup
    {x : L} [Finite (L ≃ₐ[K] L)]
    (hfixed : ∀ y : L, (∀ σ : L ≃ₐ[K] L, σ y = y) →
      ∃ k : K, algebraMap K L k = y) :
    IsAlgebraic K x :=
  isAlgebraic_of_finite_automorphismOrbit (Set.finite_range _) hfixed

/-- A transcendental element rules out finiteness of the full automorphism group when its fixed
field is the base field. -/
theorem not_finite_automorphismGroup_of_transcendental
    {x : L} (hx : Transcendental K x)
    (hfixed : ∀ y : L, (∀ σ : L ≃ₐ[K] L, σ y = y) →
      ∃ k : K, algebraMap K L k = y) :
    ¬ Finite (L ≃ₐ[K] L) := by
  intro hfinite
  letI : Finite (L ≃ₐ[K] L) := hfinite
  exact hx (isAlgebraic_of_finite_automorphismGroup hfixed)

end

end GaloisForLFunctions.HTGeometry
