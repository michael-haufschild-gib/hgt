import GaloisForLFunctions.RHTower.FiniteAlgebraicFamilyPrimitiveElement
import GaloisForLFunctions.RHTower.FiniteAlgebraicRootPolynomial
import GaloisForLFunctions.RHTower.FiniteProductTupleNondegeneracy
import GaloisForLFunctions.RHTower.RationalPolynomialCommonDenominator
import GaloisForLFunctions.RHTower.ScaledHermiteContradiction
import GaloisForLFunctions.RHTower.SymmetricConjugateIntegral
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-!
# Finite Lindemann--Weierstrass infrastructure

This file proves finite rational-coefficient exponential separation for distinct algebraic
exponents and algebraic independence over `ℚ` for exponentials of rational-linearly-independent
algebraic families, using the project's single cached Hermite approximation engine.  The remaining
arbitrary-distinct-exponent/algebraic-coefficient wrapper is intentionally not claimed here.
-/

open Polynomial MvPolynomial Finset Complex
open scoped Classical Nat

namespace GaloisForLFunctions.RHTower

/-- Evaluating an integer polynomial at an algebraic integer again gives an algebraic integer. -/
theorem isIntegral_aeval_intPolynomial {x : ℂ} (hx : IsIntegral ℤ x) (p : ℤ[X]) :
    IsIntegral ℤ (Polynomial.aeval x p) := by
  rw [Polynomial.aeval_eq_sum_range]
  apply IsIntegral.sum
  intro i _
  exact (hx.pow i).zsmul (p.coeff i)

/-- The multivariate polynomial recording a coordinatewise polynomial choice. -/
noncomputable def polynomialChoiceTuple {J ι : Type*} [Fintype J]
    (A : ι → ℤ[X]) (k : J → ι) : MvPolynomial J ℤ :=
  ∑ j, Polynomial.aeval (MvPolynomial.X j) (A (k j))

theorem rename_polynomialChoiceTuple {J ι : Type*} [Fintype J]
    (σ : Equiv.Perm J) (A : ι → ℤ[X]) (k : J → ι) :
    MvPolynomial.rename σ (polynomialChoiceTuple A k) =
      polynomialChoiceTuple A (k ∘ σ.symm) := by
  rw [polynomialChoiceTuple, polynomialChoiceTuple, map_sum]
  rw [← Equiv.sum_comp σ
    (fun j => Polynomial.aeval (MvPolynomial.X j) (A ((k ∘ σ.symm) j)))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Polynomial.aeval_algHom_apply, MvPolynomial.rename_X]
  simp only [Function.comp_apply, Equiv.symm_apply_apply]

theorem aeval_polynomialChoiceTuple {J ι : Type*} [Fintype J]
    (β : J → ℂ) (A : ι → ℤ[X]) (k : J → ι) :
    MvPolynomial.aeval β (polynomialChoiceTuple A k) =
      ∑ j, Polynomial.aeval (β j) (A (k j)) := by
  rw [polynomialChoiceTuple, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]

/-- The polynomially weighted difference-orbit sum is symmetric in the conjugate coordinates. -/
theorem polynomialChoiceDiffOrbit_isSymmetric
    {J ι : Type*} [Fintype J] [Fintype ι]
    (A : ι → ℤ[X]) (c : ι → ℤ) (q : ℤ[X]) :
    (∑ p : (J → ι) × (J → ι),
      (finiteProductCoefficient c p.1 * finiteProductCoefficient c p.2) •
        Polynomial.aeval
          (polynomialChoiceTuple A p.1 - polynomialChoiceTuple A p.2) q).IsSymmetric := by
  classical
  intro σ
  rw [map_sum]
  refine Finset.sum_nbij'
    (fun p => (p.1 ∘ σ.symm, p.2 ∘ σ.symm))
    (fun p => (p.1 ∘ σ, p.2 ∘ σ))
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro p _
    simp only [Function.comp_def, Equiv.symm_apply_apply, Prod.mk.eta]
  · intro p _
    simp only [Function.comp_def, Equiv.apply_symm_apply, Prod.mk.eta]
  · intro p _
    rw [map_zsmul, ← Polynomial.aeval_algHom_apply, map_sub,
      rename_polynomialChoiceTuple, rename_polynomialChoiceTuple]
    simp only [Function.comp_def]
    congr 1
    simp only [finiteProductCoefficient]
    rw [Equiv.prod_comp σ.symm (fun j => c (p.1 j)),
      Equiv.prod_comp σ.symm (fun j => c (p.2 j))]

/-- Evaluation of the symmetric orbit polynomial at the complete conjugate set. -/
theorem aeval_polynomialChoiceDiffOrbit
    {J ι : Type*} [Fintype J] [Fintype ι]
    (β : J → ℂ) (A : ι → ℤ[X]) (c : ι → ℤ) (q : ℤ[X]) :
    MvPolynomial.aeval β
        (∑ p : (J → ι) × (J → ι),
          (finiteProductCoefficient c p.1 * finiteProductCoefficient c p.2) •
            Polynomial.aeval
              (polynomialChoiceTuple A p.1 - polynomialChoiceTuple A p.2) q) =
      ∑ p : (J → ι) × (J → ι),
        ((finiteProductCoefficient c p.1 * finiteProductCoefficient c p.2 : ℤ) : ℂ) *
          Polynomial.aeval
            ((∑ j, Polynomial.aeval (β j) (A (p.1 j))) -
              ∑ j, Polynomial.aeval (β j) (A (p.2 j))) q := by
  rw [map_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [map_zsmul, zsmul_eq_mul, ← Polynomial.aeval_algHom_apply, map_sub,
    aeval_polynomialChoiceTuple, aeval_polynomialChoiceTuple]

set_option maxHeartbeats 2000000

/-- **Integral-conjugate finite exponential separation.**  A nonzero integer relation among
coordinatewise polynomial choices evaluated at one member of a complete monic conjugate set is
impossible when every conjugate coordinate keeps the choices distinct. -/
theorem exp_integer_relation_ne_of_integral_conjugate_orbit
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : ℤ[X]) (hμ : μ.Monic) (β : Fin d → ℂ)
    (hβ : (Multiset.map (fun j => Polynomial.X - Polynomial.C (β j)) Finset.univ.val).prod =
      μ.map (Int.castRingHom ℂ))
    (A : ι → ℤ[X]) (D : ℤ) (hD : D ≠ 0)
    (hinj : ∀ j, Function.Injective (fun i => Polynomial.aeval (β j) (A i)))
    (c : ι → ℤ) (hc : ∀ i, c i ≠ 0) (j₀ : Fin d)
    (hrel : ∑ i : ι, (c i : ℂ) *
      Complex.exp ((D : ℂ)⁻¹ * Polynomial.aeval (β j₀) (A i)) = 0) : False := by
  classical
  letI : DecidableEq (Fin d) := Classical.decEq _
  let z : Fin d → ι → ℂ := fun j i => Polynomial.aeval (β j) (A i)
  let E : ((Fin d → ι) × (Fin d → ι)) → ℂ := fun p =>
    (D : ℂ)⁻¹ * (finiteProductExponent z p.1 - finiteProductExponent z p.2)
  let C : ((Fin d → ι) × (Fin d → ι)) → ℂ := fun p =>
    ((finiteProductCoefficient c p.1 * finiteProductCoefficient c p.2 : ℤ) : ℂ)
  have hβint : ∀ j, IsIntegral ℤ (β j) := by
    intro j
    refine ⟨μ, hμ, ?_⟩
    change Polynomial.aeval (β j) μ = 0
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    have hβ' :
        (Multiset.map (fun j => Polynomial.X - Polynomial.C (β j)) Finset.univ.val).prod =
          μ.map (algebraMap ℤ ℂ) := by
      simpa only [algebraMap_int_eq] using hβ
    rw [← hβ', Polynomial.eval_multiset_prod]
    apply Multiset.prod_eq_zero
    apply Multiset.mem_map.mpr
    refine ⟨Polynomial.X - Polynomial.C (β j),
      Multiset.mem_map_of_mem _ (Finset.mem_univ j), ?_⟩
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
  have hEalgQ : ∀ p, IsAlgebraic ℚ (E p) := by
    intro p
    have hraw : IsIntegral ℤ
        (finiteProductExponent z p.1 - finiteProductExponent z p.2) := by
      apply IsIntegral.sub
      · dsimp [finiteProductExponent, z]
        apply IsIntegral.sum
        intro j _
        exact isIntegral_aeval_intPolynomial (hβint j) (A (p.1 j))
      · dsimp [finiteProductExponent, z]
        apply IsIntegral.sum
        intro j _
        exact isIntegral_aeval_intPolynomial (hβint j) (A (p.2 j))
    have hrawQ : IsAlgebraic ℚ
        (finiteProductExponent z p.1 - finiteProductExponent z p.2) :=
      hraw.tower_top.isAlgebraic
    have hDinv : IsAlgebraic ℚ ((D : ℂ)⁻¹) := by
      have hcast : (D : ℂ)⁻¹ = algebraMap ℚ ℂ ((D : ℚ)⁻¹) := by simp
      rw [hcast]
      exact isAlgebraic_algebraMap _
    exact hDinv.mul hrawQ
  have hEalgZ : ∀ p, IsAlgebraic ℤ (E p) := fun p =>
    (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr (hEalgQ p)
  obtain ⟨g, hg0, hgroot⟩ :=
    exists_integer_polynomial_cover_of_finite_algebraic E hEalgZ
  have hArel : ∑ k : Fin d → ι,
      (finiteProductCoefficient c k : ℂ) *
        Complex.exp ((D : ℂ)⁻¹ * finiteProductExponent z k) = 0 := by
    have hprod :
        (∑ k : Fin d → ι, (finiteProductCoefficient c k : ℂ) *
            Complex.exp ((D : ℂ)⁻¹ * finiteProductExponent z k)) =
          ∏ j : Fin d, ∑ i : ι, (c i : ℂ) *
            Complex.exp ((D : ℂ)⁻¹ * z j i) := by
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
      simp only [finiteProductCoefficient, finiteProductExponent, z]
      push_cast
      congr 1
      rw [Finset.mul_sum]
    rw [hprod]
    exact Finset.prod_eq_zero (Finset.mem_univ j₀) (by simpa [z] using hrel)
  have hpairRel : ∑ p : (Fin d → ι) × (Fin d → ι), C p * Complex.exp (E p) = 0 := by
    have hfactor :
        (∑ p : (Fin d → ι) × (Fin d → ι), C p * Complex.exp (E p)) =
          (∑ k : Fin d → ι, (finiteProductCoefficient c k : ℂ) *
              Complex.exp ((D : ℂ)⁻¹ * finiteProductExponent z k)) *
            (∑ k : Fin d → ι, (finiteProductCoefficient c k : ℂ) *
              Complex.exp (-((D : ℂ)⁻¹ * finiteProductExponent z k))) := by
      rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      refine Finset.sum_congr rfl (fun k' _ => ?_)
      simp only [C, E]
      push_cast
      rw [mul_mul_mul_comm, ← Complex.exp_add]
      congr 2
      ring
    rw [hfactor, hArel, zero_mul]
  let a0 : ℤ := ∑ p ∈
      (Finset.univ : Finset ((Fin d → ι) × (Fin d → ι))).filter (fun p => E p = 0),
      finiteProductCoefficient c p.1 * finiteProductCoefficient c p.2
  have ha0ne : a0 ≠ 0 := by
    have hzero : ∀ p,
        E p = 0 ↔ finiteProductExponent z p.1 - finiteProductExponent z p.2 = 0 := by
      intro p
      dsimp [E]
      rw [mul_eq_zero]
      simp only [inv_eq_zero, Int.cast_eq_zero, hD, false_or]
    simp only [a0]
    rw [show
      (Finset.univ : Finset ((Fin d → ι) × (Fin d → ι))).filter (fun p => E p = 0) =
        Finset.univ.filter
          (fun p => finiteProductExponent z p.1 - finiteProductExponent z p.2 = 0) by
      apply Finset.filter_congr
      intro p _
      exact hzero p]
    exact finiteProductTupleDiff_nondegenerate (J := Fin d) (ι := ι)
      z (fun j => hinj j) c hc
  refine exp_scaled_aggregate_zero_relation_ne E C g hg0 hgroot D a0 hD 1 0
    hpairRel ?_ ha0ne ?_
  · simp only [a0, C, Int.cast_sum, Int.cast_mul]
  · intro q
    let Ψ : MvPolynomial (Fin d) ℤ :=
      ∑ p : (Fin d → ι) × (Fin d → ι),
        (finiteProductCoefficient c p.1 * finiteProductCoefficient c p.2) •
          Polynomial.aeval
            (polynomialChoiceTuple A p.1 - polynomialChoiceTuple A p.2)
            (q.scaleRoots D)
    have hΨsym : Ψ.IsSymmetric :=
      polynomialChoiceDiffOrbit_isSymmetric (J := Fin d) (ι := ι)
        A c (q.scaleRoots D)
    obtain ⟨T, hT⟩ := symmetric_aeval_conj_isInt μ β hβ Ψ hΨsym
    have hscale : ∀ p : (Fin d → ι) × (Fin d → ι),
        Polynomial.aeval
            ((∑ j, Polynomial.aeval (β j) (A (p.1 j))) -
              ∑ j, Polynomial.aeval (β j) (A (p.2 j)))
            (q.scaleRoots D) =
          (D : ℂ) ^ q.natDegree * Polynomial.aeval (E p) q := by
      intro p
      have hmul : (D : ℂ) * E p =
          (∑ j, Polynomial.aeval (β j) (A (p.1 j))) -
            ∑ j, Polynomial.aeval (β j) (A (p.2 j)) := by
        dsimp [E, finiteProductExponent, z]
        have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD
        field_simp
      have hs := Polynomial.scaleRoots_eval₂_mul (p := q)
        (Int.castRingHom ℂ) (E p) D
      change Polynomial.eval₂ (Int.castRingHom ℂ) ((D : ℂ) * E p)
          (q.scaleRoots D) =
        (D : ℂ) ^ q.natDegree * Polynomial.eval₂ (Int.castRingHom ℂ) (E p) q at hs
      rw [hmul] at hs
      simpa [Polynomial.aeval_def] using hs
    have hEval : MvPolynomial.aeval β Ψ =
        (D : ℂ) ^ q.natDegree *
          ∑ p : (Fin d → ι) × (Fin d → ι), C p * Polynomial.aeval (E p) q := by
      rw [show MvPolynomial.aeval β Ψ =
        ∑ p : (Fin d → ι) × (Fin d → ι),
          ((finiteProductCoefficient c p.1 * finiteProductCoefficient c p.2 : ℤ) : ℂ) *
            Polynomial.aeval
              ((∑ j, Polynomial.aeval (β j) (A (p.1 j))) -
                ∑ j, Polynomial.aeval (β j) (A (p.2 j))) (q.scaleRoots D) by
          exact aeval_polynomialChoiceDiffOrbit β A c (q.scaleRoots D)]
      simp_rw [hscale]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      simp only [C]
      ring
    refine ⟨q.natDegree, T, by omega, ?_⟩
    rw [← hT, hEval]

/-- Rational coefficients reduce to integer coefficients by one common denominator. -/
theorem exp_rational_relation_ne
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (E : ι → ℂ) (hE : ∀ i, IsAlgebraic ℚ (E i)) (hEinj : Function.Injective E)
    (c : ι → ℚ) (hc : ∀ i, c i ≠ 0)
    (hrel : ∑ i, (c i : ℂ) * Complex.exp (E i) = 0) : False := by
  classical
  obtain ⟨D, hD, A, hA⟩ :=
    exists_common_integer_polynomial_scale (fun i => Polynomial.C (c i))
  let a : ι → ℤ := fun i => (A i).coeff 0
  have ha : ∀ i, (a i : ℚ) = (D : ℚ) * c i := by
    intro i
    have hi := congrArg (fun p : ℚ[X] => p.coeff 0) (hA i)
    simpa [a] using hi
  have ha0 : ∀ i, a i ≠ 0 := by
    intro i hai
    have hi := ha i
    rw [hai, Int.cast_zero] at hi
    exact (mul_ne_zero (by exact_mod_cast hD) (hc i)) hi.symm
  have hrelZ : ∑ i, (a i : ℂ) * Complex.exp (E i) = 0 := by
    have hDℂ : (D : ℂ) ≠ 0 := by exact_mod_cast hD
    calc
      ∑ i, (a i : ℂ) * Complex.exp (E i) =
          (D : ℂ) * ∑ i, (c i : ℂ) * Complex.exp (E i) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            have hi := congrArg (fun x : ℚ => (x : ℂ)) (ha i)
            push_cast at hi
            rw [hi]
            ring
      _ = 0 := by rw [hrel, mul_zero]
  obtain ⟨θ, q, hθint, hqdeg, hq⟩ :=
    exists_integral_primitive_polynomial_representation E hE
  obtain ⟨S, hS, B, hB⟩ := exists_common_integer_polynomial_scale q
  have hBalg : ∀ i, (B i).map (algebraMap ℤ ℚ) = (S : ℚ) • q i := by
    simpa only [algebraMap_int_eq] using hB
  set μ := minpoly ℤ θ
  have hμ : μ.Monic := minpoly.monic hθint
  have hqmin : minpoly ℚ θ = μ.map (Int.castRingHom ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions'
      (R := ℤ) (K := ℚ) (S := ℂ) hθint
  have hμmapMonic : (μ.map (Int.castRingHom ℂ)).Monic := hμ.map _
  have hdegmap : (μ.map (Int.castRingHom ℂ)).natDegree = μ.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (Int.cast_injective (α := ℂ)) _
  have hcard : Multiset.card (μ.map (Int.castRingHom ℂ)).roots = μ.natDegree := by
    rw [Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _), hdegmap]
  obtain ⟨l, hl⟩ := Quotient.exists_rep (μ.map (Int.castRingHom ℂ)).roots
  have hmap : Multiset.map l.get Finset.univ.val = (μ.map (Int.castRingHom ℂ)).roots := by
    rw [Fin.univ_val_map, List.ofFn_get]
    exact hl
  have hβfac :
      (Multiset.map (fun j => Polynomial.X - Polynomial.C (l.get j)) Finset.univ.val).prod =
        μ.map (Int.castRingHom ℂ) := by
    have hrw :
        Multiset.map (fun j => Polynomial.X - Polynomial.C (l.get j)) Finset.univ.val =
          (μ.map (Int.castRingHom ℂ)).roots.map
            (fun x => Polynomial.X - Polynomial.C x) := by
      rw [← hmap, Multiset.map_map]
      rfl
    rw [hrw, prod_multiset_X_sub_C_of_monic_of_roots_card_eq
      hμmapMonic (hcard.trans hdegmap.symm)]
  have hθroot : θ ∈ (μ.map (Int.castRingHom ℂ)).roots := by
    rw [Polynomial.mem_roots']
    refine ⟨hμmapMonic.ne_zero, ?_⟩
    rw [Polynomial.IsRoot.def, Polynomial.eval_map]
    have hh := minpoly.aeval ℤ θ
    rw [Polynomial.aeval_def] at hh
    exact hh
  have hθmem : θ ∈ Multiset.map l.get Finset.univ.val := by
    rw [hmap]
    exact hθroot
  obtain ⟨j₀, _, hj₀⟩ := Multiset.mem_map.mp hθmem
  let β : Fin l.length → ℂ := l.get
  have hBinj : ∀ j, Function.Injective (fun i => Polynomial.aeval (β j) (B i)) := by
    intro j i k hik
    by_contra hneik
    have hβmem : β j ∈ (μ.map (Int.castRingHom ℂ)).roots := by
      rw [← hmap]
      exact Multiset.mem_map_of_mem _ (Finset.mem_univ j)
    have hβroot : (μ.map (Int.castRingHom ℂ)).eval (β j) = 0 :=
      (Polynomial.mem_roots'.mp hβmem).2
    have hβqroot : Polynomial.aeval (β j) (minpoly ℚ θ) = 0 := by
      rw [hqmin, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
        Polynomial.map_map]
      simpa using! hβroot
    have hminθβ : minpoly ℚ θ = minpoly ℚ (β j) :=
      minpoly.eq_of_irreducible_of_monic
        (minpoly.irreducible hθint.tower_top) hβqroot
        (minpoly.monic hθint.tower_top)
    have hminβ : minpoly ℚ (β j) = minpoly ℚ θ := hminθβ.symm
    have hqeq : Polynomial.aeval (β j) (q i - q k) = 0 := by
      have hBi := congrArg (fun p : ℚ[X] => Polynomial.aeval (β j) p) (hBalg i)
      have hBk := congrArg (fun p : ℚ[X] => Polynomial.aeval (β j) p) (hBalg k)
      change Polynomial.aeval (β j) ((B i).map (algebraMap ℤ ℚ)) =
        Polynomial.aeval (β j) ((S : ℚ) • q i) at hBi
      change Polynomial.aeval (β j) ((B k).map (algebraMap ℤ ℚ)) =
        Polynomial.aeval (β j) ((S : ℚ) • q k) at hBk
      rw [Polynomial.aeval_map_algebraMap, map_smul] at hBi hBk
      have hSℂ : (S : ℂ) ≠ 0 := by exact_mod_cast hS
      rw [map_sub]
      apply sub_eq_zero.mpr
      apply mul_left_cancel₀ hSℂ
      simpa [Algebra.smul_def] using hBi.symm.trans (hik.trans hBk)
    have hdiv : minpoly ℚ (β j) ∣ q i - q k := minpoly.dvd ℚ (β j) hqeq
    have hne : q i - q k ≠ 0 := by
      intro hz
      have hqi : q i = q k := sub_eq_zero.mp hz
      exact hneik (hEinj (by rw [hq i, hq k, hqi]))
    have hdeg : (q i - q k).natDegree < (minpoly ℚ θ).natDegree := by
      exact (Polynomial.natDegree_sub_le (q i) (q k)).trans_lt
        (max_lt (hqdeg i) (hqdeg k))
    have hle := Polynomial.natDegree_le_of_dvd hdiv hne
    rw [hminβ] at hle
    omega
  have hrelB : ∑ i, (a i : ℂ) * Complex.exp
      ((S : ℂ)⁻¹ * Polynomial.aeval (β j₀) (B i)) = 0 := by
    have hval : ∀ i, (S : ℂ)⁻¹ * Polynomial.aeval (β j₀) (B i) = E i := by
      intro i
      have hi := congrArg (fun p : ℚ[X] => Polynomial.aeval θ p) (hBalg i)
      change Polynomial.aeval θ ((B i).map (algebraMap ℤ ℚ)) =
        Polynomial.aeval θ ((S : ℚ) • q i) at hi
      have hSℂ : (S : ℂ) ≠ 0 := by exact_mod_cast hS
      change (S : ℂ)⁻¹ * Polynomial.aeval (l.get j₀) (B i) = E i
      rw [Polynomial.aeval_map_algebraMap, map_smul] at hi
      rw [hj₀]
      rw [hi, hq i]
      simp [Algebra.smul_def, hSℂ]
    simpa only [hval] using hrelZ
  exact exp_integer_relation_ne_of_integral_conjugate_orbit μ hμ β hβfac B S hS
    hBinj a ha0 j₀ hrelB

/-- Exponentials of a finite rational-linearly-independent algebraic family are algebraically
independent over `ℚ`. -/
theorem exp_algebraicIndependent_of_linearIndependent
    {J : Type*} [Fintype J]
    (β : J → ℂ) (hβalg : ∀ j, IsAlgebraic ℚ (β j))
    (hβlin : LinearIndependent ℚ β) :
    AlgebraicIndependent ℚ (fun j => Complex.exp (β j)) := by
  classical
  rw [algebraicIndependent_iff]
  intro P hP
  by_contra hP0
  let I := P.support
  have hI : P.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (fun h => hP0 (MvPolynomial.support_eq_empty.mp h))
  letI : Nonempty I := hI.to_subtype
  let exponent : I → ℂ := fun m => ∑ j : J, (m.1 j) • β j
  have hexponentAlg : ∀ m, IsAlgebraic ℚ (exponent m) := by
    intro m
    rw [← mem_algebraicClosure_iff]
    dsimp [exponent]
    apply Subalgebra.sum_mem
    intro j _
    exact (algebraicClosure ℚ ℂ).nsmul_mem
      (mem_algebraicClosure_iff.mpr (hβalg j)) _
  have hexponentInj : Function.Injective exponent := by
    intro m n hmn
    apply Subtype.ext
    apply Finsupp.ext
    intro j
    have hzero : ∑ k : J,
        ((((m.1 k : ℕ) : ℤ) - ((n.1 k : ℕ) : ℤ) : ℤ) : ℚ) • β k = 0 := by
      calc
        ∑ k : J, ((((m.1 k : ℕ) : ℤ) - ((n.1 k : ℕ) : ℤ) : ℤ) : ℚ) • β k =
            (∑ k : J, (m.1 k : ℚ) • β k) - ∑ k : J, (n.1 k : ℚ) • β k := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro k _
              push_cast
              rw [sub_smul]
        _ = exponent m - exponent n := by
              congr 1 <;>
                apply Finset.sum_congr rfl <;>
                intro k _ <;>
                simp [Nat.cast_smul_eq_nsmul]
        _ = 0 := sub_eq_zero.mpr hmn
    have hk := Fintype.linearIndependent_iff.mp hβlin
      (fun k => ((((m.1 k : ℕ) : ℤ) - ((n.1 k : ℕ) : ℤ) : ℤ) : ℚ)) hzero j
    have hkZ : ((m.1 j : ℕ) : ℤ) - ((n.1 j : ℕ) : ℤ) = 0 := by
      exact_mod_cast hk
    exact_mod_cast sub_eq_zero.mp hkZ
  have hmonomialAll : ∀ m : J →₀ ℕ,
      (∏ j : J, Complex.exp (β j) ^ (m j)) =
        Complex.exp (∑ j : J, (m j) • β j) := by
    intro m
    simp_rw [← Complex.exp_nsmul]
    rw [← Complex.exp_sum]
  have hrel : ∑ m : I, ((P.coeff m.1 : ℚ) : ℂ) * Complex.exp (exponent m) = 0 := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq'] at hP
    calc
      ∑ m : I, ((P.coeff m.1 : ℚ) : ℂ) * Complex.exp (exponent m) =
          ∑ m ∈ P.support, ((P.coeff m : ℚ) : ℂ) *
            Complex.exp (∑ j : J, (m j) • β j) := by
              dsimp [I, exponent]
              exact (Finset.sum_subtype (M := ℂ) P.support (fun _ => Iff.rfl)
                (fun m => ((P.coeff m : ℚ) : ℂ) *
                  Complex.exp (∑ j : J, (m j) • β j))).symm
      _ = ∑ m ∈ P.support, ((P.coeff m : ℚ) : ℂ) *
            ∏ j : J, Complex.exp (β j) ^ (m j) := by
              apply Finset.sum_congr rfl
              intro m _
              rw [hmonomialAll]
      _ = 0 := hP
  exact exp_rational_relation_ne exponent hexponentAlg hexponentInj
    (fun m : I => P.coeff m.1)
    (fun m => MvPolynomial.mem_support_iff.mp m.2) hrel

/-- Distinct monomials in an algebraically independent family are linearly independent. -/
theorem monomial_linearIndependent_of_algebraicIndependent
    {K J I A : Type*} [Field K] [CommRing A] [Algebra K A]
    [Fintype J] [Fintype I]
    (x : J → A) (hx : AlgebraicIndependent K x)
    (m : I → J →₀ ℕ) (hm : Function.Injective m) :
    LinearIndependent K (fun i => (m i).prod fun j n => x j ^ n) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hrel i
  let P : MvPolynomial J K := ∑ i : I, MvPolynomial.monomial (m i) (c i)
  have hPev : MvPolynomial.aeval x P = 0 := by
    change MvPolynomial.aeval x
      (∑ i : I, MvPolynomial.monomial (m i) (c i)) = 0
    rw [map_sum]
    simpa only [MvPolynomial.aeval_monomial, Algebra.smul_def] using hrel
  have hP0 : P = 0 := hx.eq_zero_of_aeval_eq_zero P hPev
  have hcoeff := congrArg (MvPolynomial.coeff (m i)) hP0
  have hcoeffP : MvPolynomial.coeff (m i) P = c i := by
    simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [if_neg]
      exact fun heq => hji (hm heq)
    · simp
  rw [hcoeffP, MvPolynomial.coeff_zero] at hcoeff
  exact hcoeff

end GaloisForLFunctions.RHTower
