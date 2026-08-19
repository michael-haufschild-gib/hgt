import GaloisForLFunctions.HTGeometry.CoordinatePrefixPrimeChain
import GaloisForLFunctions.HTGeometry.DegreeOnePolynomialQuotient
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Dimension of a degree-one hypersurface

The hypersurface cut out of `k[x_1, ..., x_N][X]` by `a * X + b` has Krull dimension exactly `N`.

The lower bound is the substance: the coordinate-prefix primes through a point where `a` does not
vanish give a chain of `N + 1` primes of the base avoiding `a`, and the degree-one evaluation map
of `DegreeOnePolynomialQuotient` turns that into a chain of `N + 1` primes lying on the
hypersurface.  The upper bound is the usual drop of the Krull dimension along a nonzerodivisor.

Combined with Noether normalization this is a special case of the dimension formula for polynomial
rings, proved here directly and without any catenary theory.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Polynomial Order

variable {k : Type*} [Field k] {N : ℕ}

/-- The coordinate-prefix substitutions, pushed into the rational function field. -/
noncomputable def coordinatePrefixFieldHom (c : Fin N → k) (j : ℕ) :
    MvPolynomial (Fin N) k →+* FractionRing (MvPolynomial (Fin N) k) :=
  (algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k))).comp
    (coordinatePrefixSubst c j).toRingHom

theorem ker_coordinatePrefixFieldHom (c : Fin N → k) (j : ℕ) :
    RingHom.ker (coordinatePrefixFieldHom c j) = coordinatePrefixIdeal c j := by
  ext f
  rw [RingHom.mem_ker, mem_coordinatePrefixIdeal_iff]
  simp only [coordinatePrefixFieldHom, RingHom.coe_comp, Function.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  exact map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin N) k)
    (FractionRing (MvPolynomial (Fin N) k)))

theorem coordinatePrefixFieldHom_ne_zero (c : Fin N → k) {a : MvPolynomial (Fin N) k}
    (ha : MvPolynomial.eval c a ≠ 0) {j : ℕ} (hj : j ≤ N) :
    coordinatePrefixFieldHom c j a ≠ 0 := fun hcon =>
  notMem_coordinatePrefixIdeal_of_eval_ne_zero c ha hj
    (by rw [← ker_coordinatePrefixFieldHom]; exact RingHom.mem_ker.mpr hcon)

/-- The chain of primes lying on the degree-one hypersurface `a X + b`. -/
noncomputable def hypersurfacePrefixIdeal (c : Fin N → k) (a b : MvPolynomial (Fin N) k)
    (j : ℕ) : Ideal ((MvPolynomial (Fin N) k)[X]) :=
  RingHom.ker (degreeOneEval (coordinatePrefixFieldHom c j) a b)

instance hypersurfacePrefixIdeal_isPrime (c : Fin N → k) (a b : MvPolynomial (Fin N) k) (j : ℕ) :
    (hypersurfacePrefixIdeal c a b j).IsPrime := ker_degreeOneEval_isPrime _ _ _

theorem span_le_hypersurfacePrefixIdeal (c : Fin N → k) {a b : MvPolynomial (Fin N) k}
    (ha : MvPolynomial.eval c a ≠ 0) {j : ℕ} (hj : j ≤ N) :
    Ideal.span {degreeOnePoly a b} ≤ hypersurfacePrefixIdeal c a b j :=
  span_le_ker_degreeOneEval _ (coordinatePrefixFieldHom_ne_zero c ha hj)

theorem hypersurfacePrefixIdeal_mono (c : Fin N → k) {a b : MvPolynomial (Fin N) k}
    (ha : MvPolynomial.eval c a ≠ 0) {j l : ℕ} (hjl : j ≤ l) (hl : l ≤ N) :
    hypersurfacePrefixIdeal c a b j ≤ hypersurfacePrefixIdeal c a b l :=
  ker_degreeOneEval_mono (coordinatePrefixFieldHom_ne_zero c ha (hjl.trans hl))
    (coordinatePrefixFieldHom_ne_zero c ha hl)
    (by rw [ker_coordinatePrefixFieldHom, ker_coordinatePrefixFieldHom]
        exact coordinatePrefixIdeal_mono c hjl)

theorem hypersurfacePrefixIdeal_lt (c : Fin N → k) {a b : MvPolynomial (Fin N) k}
    (ha : MvPolynomial.eval c a ≠ 0) {j : ℕ} (hj : j < N) :
    hypersurfacePrefixIdeal c a b j < hypersurfacePrefixIdeal c a b (j + 1) := by
  refine lt_of_le_of_ne (hypersurfacePrefixIdeal_mono c ha (Nat.le_succ j) hj) fun hcon => ?_
  obtain ⟨u, hu1, hu2⟩ := SetLike.exists_of_lt (coordinatePrefixIdeal_lt c hj)
  have hmem : (Polynomial.C u : (MvPolynomial (Fin N) k)[X])
      ∈ hypersurfacePrefixIdeal c a b (j + 1) := by
    rw [hypersurfacePrefixIdeal, mem_ker_degreeOneEval_C, ker_coordinatePrefixFieldHom]
    exact hu1
  rw [← hcon] at hmem
  rw [hypersurfacePrefixIdeal, mem_ker_degreeOneEval_C, ker_coordinatePrefixFieldHom] at hmem
  exact hu2 hmem

/-- **The degree-one hypersurface has full dimension.**  A chain of `N + 1` primes on the
hypersurface cut out by `a X + b` inside `k[x₁,…,x_N][X]`. -/
theorem le_ringKrullDim_quotient_degreeOnePoly [Infinite k]
    {a b : MvPolynomial (Fin N) k} (ha : a ≠ 0) :
    (N : WithBot ℕ∞)
      ≤ ringKrullDim ((MvPolynomial (Fin N) k)[X] ⧸ Ideal.span {degreeOnePoly a b}) := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : Fin N → k, MvPolynomial.eval c a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha (MvPolynomial.funext fun x => by simpa using hcon x)
  set I : Ideal ((MvPolynomial (Fin N) k)[X]) := Ideal.span {degreeOnePoly a b} with hI
  set Q : ℕ → Ideal ((MvPolynomial (Fin N) k)[X] ⧸ I) := fun j =>
    (hypersurfacePrefixIdeal c a b j).map (Ideal.Quotient.mk I) with hQ
  have hker : ∀ j ≤ N, RingHom.ker (Ideal.Quotient.mk I) ≤ hypersurfacePrefixIdeal c a b j := by
    intro j hj
    rw [Ideal.mk_ker]
    exact span_le_hypersurfacePrefixIdeal c hc hj
  have hprime : ∀ j : Fin (N + 1), (Q (j : ℕ)).IsPrime := by
    intro j
    exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (hker (j : ℕ) (Nat.lt_succ_iff.mp j.isLt))
  have hcomap : ∀ j ≤ N, (Q j).comap (Ideal.Quotient.mk I) = hypersurfacePrefixIdeal c a b j := by
    intro j hj
    rw [hQ, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left]
    exact span_le_hypersurfacePrefixIdeal c hc hj
  have hstep : ∀ j : Fin N, Q (j : ℕ) < Q ((j : ℕ) + 1) := by
    intro j
    refine lt_of_le_of_ne (Ideal.map_mono
      (hypersurfacePrefixIdeal_mono c hc (Nat.le_succ _) j.isLt)) fun hcon => ?_
    have h1 := hcomap (j : ℕ) (le_of_lt j.isLt)
    have h2 := hcomap ((j : ℕ) + 1) j.isLt
    rw [hcon, h2] at h1
    exact absurd h1.symm (ne_of_lt (hypersurfacePrefixIdeal_lt c hc j.isLt))
  refine le_trans (le_of_eq (by simp)) (LTSeries.length_le_krullDim
    ({ length := N
       toFun := fun j => ⟨Q (j : ℕ), hprime j⟩
       step := fun i => by
         have := hstep i
         exact this } :
      LTSeries (PrimeSpectrum ((MvPolynomial (Fin N) k)[X] ⧸ I))))

end GaloisForLFunctions.HTGeometry
