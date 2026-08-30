import GaloisForLFunctions.HTGeometry.SecantMomentIndependence
import GaloisForLFunctions.RHTower.DeningerHankelHigherRankGroebner

/-!
# The dimension of the Hankel secant variety

The ideal of `(r+1)`-minors of a finite Hankel matrix is the kernel of the `r`-atom moment
parameterization, so the Hankel determinantal variety is the closure of the span of `r` points of
the rational normal curve.  This file computes its dimension.

The moment Hankel matrix factors as `Vᵀ D V` with `V` the node Vandermonde and `D` the amplitude
diagonal, so its determinant is `(det V)² ∏ⱼ Uⱼ` and is nonzero: the first `2r−1` moments of `r`
generic atoms determine the nodes.  And `2r` of the coefficient coordinates stay algebraically
independent modulo the determinantal ideal, so the variety has dimension at least `2r`; since the
quotient embeds in the polynomial ring on the `2r` atom coordinates, that is its exact dimension.
With `N = 2m − 1` consecutive coefficients and `r = m − k` this is the codimension `2k − 1` of the
corank-`k` locus.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

variable {K : Type*} [CommRing K] {r : ℕ}

/-- The Hankel matrix of the first `2r−1` moments of `r` atoms. -/
noncomputable def secantMomentHankel (K : Type*) [CommRing K] (r : ℕ) :
    Matrix (Fin r) (Fin r) (MvPolynomial (Fin r × Fin 2) K) :=
  Matrix.of fun i j => secantMomentPoly K r ((i : ℕ) + (j : ℕ))

/-- The node Vandermonde matrix of the atoms. -/
noncomputable def secantNodeVandermonde (K : Type*) [CommRing K] (r : ℕ) :
    Matrix (Fin r) (Fin r) (MvPolynomial (Fin r × Fin 2) K) :=
  Matrix.vandermonde fun l : Fin r => MvPolynomial.X (l, (1 : Fin 2))

/-- The amplitude diagonal of the atoms. -/
noncomputable def secantAmplitudeDiagonal (K : Type*) [CommRing K] (r : ℕ) :
    Matrix (Fin r) (Fin r) (MvPolynomial (Fin r × Fin 2) K) :=
  Matrix.diagonal fun l : Fin r => MvPolynomial.X (l, (0 : Fin 2))

/-- **The atomic Hankel factorization.**  The moment Hankel matrix is the Vandermonde of the nodes
conjugating the diagonal of the amplitudes. -/
theorem secantMomentHankel_eq (K : Type*) [CommRing K] (r : ℕ) :
    secantMomentHankel K r
      = (secantNodeVandermonde K r).transpose * secantAmplitudeDiagonal K r
          * secantNodeVandermonde K r := by
  classical
  funext i j
  rw [secantMomentHankel, Matrix.of_apply, secantMomentPoly]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single l]
  · simp [secantNodeVandermonde, secantAmplitudeDiagonal, Matrix.vandermonde, pow_add]
    ring
  · intro p _ hpl
    simp [secantAmplitudeDiagonal, Matrix.diagonal, hpl]
  · intro hl; exact absurd (Finset.mem_univ l) hl

/-- **The atomic Hankel determinant.**  It is the square of the node Vandermonde determinant times
the product of the amplitudes. -/
theorem det_secantMomentHankel (K : Type*) [CommRing K] (r : ℕ) :
    (secantMomentHankel K r).det
      = (secantNodeVandermonde K r).det ^ 2
        * ∏ l : Fin r, MvPolynomial.X (l, (0 : Fin 2)) := by
  classical
  rw [secantMomentHankel_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    secantAmplitudeDiagonal, Matrix.det_diagonal]
  ring

private theorem X_sub_X_ne_zero {σ : Type*} [DecidableEq σ] {K : Type*} [CommRing K] [Nontrivial K]
    {a b : σ} (hab : a ≠ b) :
    (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial σ K) ≠ 0 := by
  intro h
  have hc := congrArg (MvPolynomial.eval (fun x => if x = a then (1 : K) else 0)) h
  simp [Ne.symm hab] at hc

theorem det_secantNodeVandermonde_ne_zero (K : Type*) [Field K] (r : ℕ) :
    (secantNodeVandermonde K r).det ≠ 0 := by
  classical
  rw [secantNodeVandermonde, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  have hij : j ≠ i := (Finset.mem_Ioi.mp hj).ne'
  exact X_sub_X_ne_zero (by simpa using hij)

/-- **The atomic Hankel matrix is generically nonsingular.**  This is the Prony inversion: the
first `2r−1` moments of `r` generic atoms determine the nodes. -/
theorem det_secantMomentHankel_ne_zero (K : Type*) [Field K] (r : ℕ) :
    (secantMomentHankel K r).det ≠ 0 := by
  classical
  rw [det_secantMomentHankel]
  refine mul_ne_zero (pow_ne_zero 2 (det_secantNodeVandermonde_ne_zero K r)) ?_
  refine Finset.prod_ne_zero_iff.mpr fun l _ => ?_
  exact MvPolynomial.X_ne_zero _


/-! ### The Hankel determinantal quotient -/

/-- The atom-moment parameterization as an algebra map. -/
noncomputable def secantMomentAlgHom (K : Type*) [CommRing K] (N r : ℕ) :
    MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin r × Fin 2) K :=
  MvPolynomial.aeval fun i : Fin N => secantMomentPoly K r (i : ℕ)

theorem secantMomentAlgHom_eq (K : Type*) [CommRing K] (N r : ℕ) :
    (secantMomentAlgHom K N r : MvPolynomial (Fin N) K →+* MvPolynomial (Fin r × Fin 2) K)
      = RHTower.finiteHankelSecantParameterization K N r := by
  refine MvPolynomial.ringHom_ext ?_ ?_
  · intro a
    simp [secantMomentAlgHom, RHTower.finiteHankelSecantParameterization,
      RHTower.deningerHankelSecantParameterization]
  · intro i
    simp [secantMomentAlgHom, RHTower.deningerHankelSecantMoment, secantMomentPoly]

/-- The Hankel determinantal quotient, mapped into the atom coordinates. -/
noncomputable def hankelSecantQuotientHom (K : Type*) [Field K] (N r : ℕ) :
    (MvPolynomial (Fin N) K ⧸ RHTower.finiteHankelSecantIdeal K N r)
      →ₐ[K] MvPolynomial (Fin r × Fin 2) K :=
  Ideal.Quotient.liftₐ _ (secantMomentAlgHom K N r) (by
    intro a ha
    have hker : RHTower.finiteHankelSecantIdeal K N r
        = RingHom.ker (RHTower.finiteHankelSecantParameterization K N r) :=
      RHTower.finiteHankelSecantIdeal_eq_parameterization_ker K N r
    have : a ∈ RingHom.ker (RHTower.finiteHankelSecantParameterization K N r) := by
      rwa [hker] at ha
    have hval : RHTower.finiteHankelSecantParameterization K N r a = 0 :=
      RingHom.mem_ker.mp this
    rw [show (secantMomentAlgHom K N r) a
        = RHTower.finiteHankelSecantParameterization K N r a from
      congrFun (congrArg (fun f : MvPolynomial (Fin N) K →+* MvPolynomial (Fin r × Fin 2) K =>
        (f : MvPolynomial (Fin N) K → MvPolynomial (Fin r × Fin 2) K))
        (secantMomentAlgHom_eq K N r)) a]
    exact hval)

/-- **The Hankel determinantal variety has dimension at least `2r`.**  Modulo the ideal of
`(r+1)`-minors of the Hankel matrix, `2r` of the coefficient coordinates stay algebraically
independent, so the closure of the span of `r` points of the rational normal curve is
`2r`-dimensional.  With `N = 2m − 1` and `r = m − k` this is the codimension `2k − 1`. -/
theorem algebraicIndependent_hankelSecantQuotient (K : Type*) [Field K] [CharZero K]
    {N r : ℕ} (hN : 2 * r ≤ N) :
    AlgebraicIndependent K (fun k : Fin r ⊕ Fin r =>
      Ideal.Quotient.mk (RHTower.finiteHankelSecantIdeal K N r)
        (MvPolynomial.X ⟨confluentExp k, lt_of_lt_of_le (confluentExp_lt k) hN⟩)) := by
  refine AlgebraicIndependent.of_comp (hankelSecantQuotientHom K N r) ?_
  have hcomp : (hankelSecantQuotientHom K N r) ∘ (fun k : Fin r ⊕ Fin r =>
      Ideal.Quotient.mk (RHTower.finiteHankelSecantIdeal K N r)
        (MvPolynomial.X ⟨confluentExp k, lt_of_lt_of_le (confluentExp_lt k) hN⟩))
      = fun k : Fin r ⊕ Fin r => secantMomentPoly K r (confluentExp k) := by
    funext k
    simp [hankelSecantQuotientHom, secantMomentAlgHom]
  rw [hcomp]
  exact algebraicIndependent_secantMomentPoly K r


/-! ### The transcendence degree -/

theorem hankelSecantQuotientHom_injective (K : Type) [Field K] (N r : ℕ) :
    Function.Injective (hankelSecantQuotientHom K N r) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  · have hp : (secantMomentAlgHom K N r) p = 0 := ha
    have hker : RHTower.finiteHankelSecantIdeal K N r
        = RingHom.ker (RHTower.finiteHankelSecantParameterization K N r) :=
      RHTower.finiteHankelSecantIdeal_eq_parameterization_ker K N r
    have hval : RHTower.finiteHankelSecantParameterization K N r p = 0 := by
      rw [← congrFun (congrArg
        (fun f : MvPolynomial (Fin N) K →+* MvPolynomial (Fin r × Fin 2) K =>
          (f : MvPolynomial (Fin N) K → MvPolynomial (Fin r × Fin 2) K))
        (secantMomentAlgHom_eq K N r)) p]
      exact hp
    rw [Ideal.Quotient.eq_zero_iff_mem, hker]
    exact RingHom.mem_ker.mpr hval

theorem trdeg_mvPolynomial_eq (K : Type) [Field K] (σ : Type) :
    Algebra.trdeg K (MvPolynomial σ K) = Cardinal.mk σ :=
  (IsTranscendenceBasis.cardinalMk_eq_trdeg (IsTranscendenceBasis.mvPolynomial σ K)).symm

/-- **The Hankel determinantal variety has transcendence degree exactly `2r`.** -/
theorem trdeg_hankelSecantQuotient (K : Type) [Field K] [CharZero K] {N r : ℕ}
    (hN : 2 * r ≤ N) :
    Algebra.trdeg K (MvPolynomial (Fin N) K ⧸ RHTower.finiteHankelSecantIdeal K N r)
      = ((2 * r : ℕ) : Cardinal) := by
  classical
  haveI hprime : (RHTower.finiteHankelSecantIdeal K N r).IsPrime :=
    RHTower.finiteHankelSecantIdeal_isPrime K N r
  haveI : Nontrivial (MvPolynomial (Fin N) K ⧸ RHTower.finiteHankelSecantIdeal K N r) :=
    Ideal.Quotient.nontrivial_iff.mpr hprime.ne_top
  have hinjK : Function.Injective
      (algebraMap K (MvPolynomial (Fin N) K ⧸ RHTower.finiteHankelSecantIdeal K N r)) :=
    (algebraMap K _).injective
  haveI : Nonempty {s : Set (MvPolynomial (Fin N) K ⧸ RHTower.finiteHankelSecantIdeal K N r)
      // AlgebraicIndepOn K id s} := ⟨⟨∅, by simpa [AlgebraicIndepOn] using hinjK⟩⟩
  refine le_antisymm ?_ ?_
  · refine ciSup_le fun s => ?_
    have hmap := s.2.map (f := hankelSecantQuotientHom K N r)
      ((hankelSecantQuotientHom_injective K N r).injOn)
    have hcard := hmap.cardinalMk_le_trdeg
    rw [trdeg_mvPolynomial_eq] at hcard
    refine hcard.trans (le_of_eq ?_)
    rw [Cardinal.mk_prod]
    simp
    ring
  · have hind := algebraicIndependent_hankelSecantQuotient K hN
    have hcard := hind.cardinalMk_le_trdeg
    refine le_trans (le_of_eq ?_) hcard
    simp
    ring


end GaloisForLFunctions.HTGeometry
