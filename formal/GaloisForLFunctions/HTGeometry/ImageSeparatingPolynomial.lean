import GaloisForLFunctions.HTGeometry.ParameterCountTranscendenceBound

/-!
# Separating an independent point from a low-dimensional image

A point whose coordinates are algebraically independent cannot lie in the image of a polynomial
parametrisation with fewer parameters — and more than that, a *single polynomial* certifies the
separation: there is one polynomial vanishing identically on the image and not vanishing at the
point.

The proof is the parameter count.  With more coordinates than parameters the parametrising
polynomials are algebraically dependent, so some nonzero `h` lies in the kernel of the
parametrisation; that `h` vanishes at every point of the image, and it cannot vanish at the given
point because the coordinates there are algebraically independent and `h ≠ 0`.

This replaces semialgebraic geometry in the following situation: to show that a curve meets the
image of a parametrisation only finitely often, one need not know that the image is semialgebraic —
it is enough that a single polynomial vanishes on the image and not along the curve, and then the
curve's finitely many zeros of that one polynomial contain all the intersections.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K L : Type} [Field K] [CommRing L] [IsDomain L] [Algebra K L]

/-- **More polynomials than variables are algebraically dependent.** -/
theorem exists_ne_zero_aeval_eq_zero {m r : ℕ} (hr : m < r)
    (Φ : Fin r → MvPolynomial (Fin m) K) :
    ∃ h : MvPolynomial (Fin r) K, h ≠ 0 ∧ MvPolynomial.aeval Φ h = 0 := by
  classical
  have hnotind : ¬ AlgebraicIndependent K Φ := by
    intro hind
    have hle := card_le_of_algebraicIndependent_of_mem_adjoin (K := K)
      (L := MvPolynomial (Fin m) K) hind
      (x := (MvPolynomial.X : Fin m → MvPolynomial (Fin m) K))
      (fun i => by rw [MvPolynomial.adjoin_range_X]; exact Algebra.mem_top)
    omega
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero] at hnotind
  by_contra hcon
  refine hnotind fun a ha => ?_
  by_contra hane
  exact hcon ⟨a, hane, ha⟩

/-- A polynomial in the kernel of a parametrisation vanishes at every point of the image. -/
theorem aeval_eq_zero_of_aeval_eq_zero {B : Type*} [CommRing B] [Algebra K B]
    {m r : ℕ} {Φ : Fin r → MvPolynomial (Fin m) K} {h : MvPolynomial (Fin r) K}
    (hh : MvPolynomial.aeval Φ h = 0) (u : Fin m → B) :
    MvPolynomial.aeval (fun i => MvPolynomial.aeval u (Φ i)) h = 0 := by
  have hcomp := MvPolynomial.comp_aeval (R := K) Φ
    (MvPolynomial.aeval u : MvPolynomial (Fin m) K →ₐ[K] B)
  have happ := congrArg (fun φ => φ h) hcomp
  simp only [AlgHom.comp_apply] at happ
  rw [← happ, hh, map_zero]

omit [IsDomain L] in
/-- **A single polynomial separates an algebraically independent point from the image.**  If the
point has more algebraically independent coordinates than the parametrisation has parameters, there
is a polynomial vanishing identically on the image but not at the point. -/
theorem exists_separating_polynomial {m r : ℕ} (hr : m < r)
    (Φ : Fin r → MvPolynomial (Fin m) K) {P : Fin r → L} (hP : AlgebraicIndependent K P) :
    ∃ h : MvPolynomial (Fin r) K,
      (∀ u : Fin m → K, MvPolynomial.aeval (fun i => MvPolynomial.aeval u (Φ i)) h = 0) ∧
        MvPolynomial.aeval Φ h = 0 ∧ MvPolynomial.aeval P h ≠ 0 := by
  obtain ⟨h, hne, hzero⟩ := exists_ne_zero_aeval_eq_zero hr Φ
  refine ⟨h, fun u => aeval_eq_zero_of_aeval_eq_zero hzero u, hzero, ?_⟩
  intro hcon
  refine hne ?_
  have hinj := (algebraicIndependent_iff_injective_aeval (R := K)).1 hP
  have := hinj (a₁ := h) (a₂ := 0) (by rw [hcon, map_zero])
  exact this

omit [IsDomain L] in
/-- **Separation from a subfamily.**  Only some of the coordinates need be algebraically
independent: if `k > m` of them are, the separating polynomial can be taken in those variables. -/
theorem exists_separating_polynomial_subfamily {m r k : ℕ} (hr : m < k) (σ : Fin k → Fin r)
    (Φ : Fin r → MvPolynomial (Fin m) K) {P : Fin r → L}
    (hP : AlgebraicIndependent K (fun i => P (σ i))) :
    ∃ h : MvPolynomial (Fin r) K,
      MvPolynomial.aeval Φ h = 0 ∧ MvPolynomial.aeval P h ≠ 0 := by
  obtain ⟨h₀, hne, hzero⟩ := exists_ne_zero_aeval_eq_zero hr (fun i => Φ (σ i))
  refine ⟨MvPolynomial.rename σ h₀, ?_, ?_⟩
  · rw [MvPolynomial.aeval_rename]
    exact hzero
  · rw [MvPolynomial.aeval_rename]
    intro hcon
    exact hne ((algebraicIndependent_iff_injective_aeval (R := K)).1 hP
      (a₁ := h₀) (a₂ := 0) (by rw [map_zero]; exact hcon))

end GaloisForLFunctions.HTGeometry
