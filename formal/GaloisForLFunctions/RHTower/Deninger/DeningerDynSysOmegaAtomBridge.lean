import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysOmegaRing
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysAtomMultiplicity
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysNormalizedFactorization

/-!
# The image of `W_rat (κ₀)` inside `ℤ̲κ`

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 1.3
(`t26n`), the lower row.

Under `ω : ℤ̲κ ≅ W_rat (κ)` the normalized polynomial `P` corresponds to the sum of the atoms
attached to the inverses of its roots.  Combined with the coefficient law — the atoms of the image
of a normalized polynomial over `κ₀` occur with multiplicities divisible by their degrees of
inseparability — this shows that the image of `W_rat (κ₀)` inside `ℤ̲κ` is contained in Deninger's
subring `ℤ̲κ / κ₀`.
-/

namespace RHTower

noncomputable section

open Polynomial

variable {K : Type*} [Field K] [IsAlgClosed K]

omit [IsAlgClosed K] in
/-- The coefficient of a sum of atoms is the multiplicity in the multiset. -/
theorem deningerAtomSum_coeff [DecidableEq Kˣ] (s : Multiset Kˣ) (u : Kˣ) :
    (deningerRationalWittAtomSum s).coeff u = (Multiset.count u s : ℤ) := by
  induction s using Multiset.induction_on with
  | empty => simp [deningerRationalWittAtomSum]
  | cons a s ih =>
      rw [deningerRationalWittAtomSum, Multiset.map_cons, Multiset.sum_cons]
      show (MonoidAlgebra.single a (1 : ℤ)).coeff u
        + (deningerRationalWittAtomSum s).coeff u = _
      rw [ih]
      show (Finsupp.single a (1 : ℤ)) u + _ = _
      rw [Finsupp.single_apply, Multiset.count_cons]
      by_cases h : a = u
      · rw [if_pos h, if_pos h.symm]
        push_cast
        ring
      · rw [if_neg h, if_neg (fun hc => h hc.symm)]
        push_cast
        ring

/-- **Deninger, Proposition 1.3 (`t26n`).**  Under `ω` the atoms of a normalized polynomial give
the corresponding rational Witt vector. -/
theorem deningerOmega_atomSum_normalizedPolynomial (P : Polynomial K) (hP : P.coeff 0 = 1) :
    deningerOmegaAddHom K
        (deningerRationalWittAtomSum (deningerNormalizedPolynomialRootUnits P hP))
      = deningerCanonicalRationalWittNormalizedPolynomial P hP := by
  apply DeningerCanonicalRationalWittRing.ext
  rw [deningerOmegaAddHom_apply]
  show deningerRationalWittReducedMonoidAlgebraToAdditive K
      (deningerRationalWittAtomSum (deningerNormalizedPolynomialRootUnits P hP))
    = Additive.ofMul (deningerRationalWittNormalizedPolynomial P hP)
  apply Additive.toMul.injective
  rw [deningerRationalWittReducedMonoidAlgebraToAdditive_atomSum_toMul]
  apply Subtype.ext
  apply Units.ext
  rw [deningerRationalWitt_prod_teichmuller_val,
    ← deningerPolynomial_eq_prod_normalizedRootUnits P hP]
  show algebraMap (Polynomial K) (DeningerRationalWittLocalization K) P
    = ((deningerRationalWittNormalizedPolynomialUnit P hP :
        (DeningerRationalWittLocalization K)ˣ) : DeningerRationalWittLocalization K)
  rw [deningerRationalWittNormalizedPolynomialUnit_val]

/-- **Deninger, Proposition 1.3 (`t26n`), the lower row.**  The atoms of the image of a normalized
polynomial over `κ₀` form an element of the subring `ℤ̲κ / κ₀`. -/
theorem deningerAtomSum_map_mem_insepSubring {F : Type*} [Field F] [Algebra F K]
    [Algebra.IsAlgebraic F K] [DecidableEq Kˣ] (q : ℕ) [ExpChar F q]
    (P₀ : Polynomial F) (hP₀ : P₀.coeff 0 = 1)
    (hmap : (P₀.map (algebraMap F K)).coeff 0 = 1) :
    deningerRationalWittAtomSum
        (deningerNormalizedPolynomialRootUnits (P₀.map (algebraMap F K)) hmap)
      ∈ deningerInsepSubring F K q := by
  classical
  intro u
  rw [deningerAtomSum_coeff]
  have hspec := deningerNormalizedFactors_spec hP₀
  have hprod : (deningerNormalizedFactors P₀).prod = P₀ := hspec.2
  have hmap' : (((deningerNormalizedFactors P₀).prod).map (algebraMap F K)).coeff 0 = 1 := by
    rw [hprod]; exact hmap
  have hdvd := deningerRootUnits_map_prod_count_dvd (F := F) (E := K) q
    (deningerNormalizedFactors P₀) hspec.1 hmap' u
  have hcongr := deningerRootUnits_congr
    (P := ((deningerNormalizedFactors P₀).prod).map (algebraMap F K))
    (Q := P₀.map (algebraMap F K)) hmap' hmap (by rw [hprod])
  rw [hcongr] at hdvd
  exact_mod_cast Int.natCast_dvd_natCast.2 hdvd

end

end RHTower
