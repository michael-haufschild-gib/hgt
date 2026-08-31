import GaloisForLFunctions.HTGeometry.RationalNormalConeNormal
import GaloisForLFunctions.HTGeometry.MonomialRegularity

/-!
# The cone over the rational normal curve is integrally closed

Multiplying by a high enough power of `U` pushes any polynomial into the cone, so the cone and
`K[U,T]` have the same fraction field.  The explicit normality theorem of
`RationalNormalConeNormal.lean` then upgrades to the `IsIntegrallyClosed` class.

```text
exists_pow_mul_mem_rationalNormalCone   every polynomial enters the cone after U ^ k
coneIsFractionRing                      ** the cone and K[U,T] share a fraction field **
isIntegrallyClosed_rationalNormalCone   ** the cone is integrally closed — i.e. normal **
```

With `isCohenMacaulayRing_rationalNormalCone` this is the Hankel card's clause "normal and
Cohen–Macaulay" for the last stratum, both halves now stated as the standard classes.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {K : Type u} [Field K]

/-- **Every polynomial enters the cone after multiplication by a power of `U`.**  Hence the cone and
`K[U,T]` have the same fraction field. -/
theorem exists_pow_mul_mem_rationalNormalCone {d : ℕ} (hd : 0 < d) (p : MvPolynomial (Fin 2) K) :
    ∃ k : ℕ, p * MvPolynomial.monomial (Finsupp.single 0 k) (1 : K)
      ∈ rationalNormalCone K d := by
  classical
  refine ⟨p.support.sup (fun e => e 1), ?_⟩
  rw [mem_rationalNormalCone_iff]
  intro e he
  rw [support_mul_monomial_one] at he
  simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, addRightEmbedding_apply] at he
  obtain ⟨f, hf, rfl⟩ := he
  have hbound : f 1 ≤ p.support.sup (fun e => e 1) :=
    Finset.le_sup (f := fun e : Fin 2 →₀ ℕ => e 1) hf
  show (f + Finsupp.single (0 : Fin 2) (p.support.sup fun e => e 1)) 1
    ≤ d * (f + Finsupp.single (0 : Fin 2) (p.support.sup fun e => e 1)) 0
  simp only [Finsupp.add_apply]
  have h0 : (Finsupp.single (0 : Fin 2) (p.support.sup fun e => e 1)) 0
      = p.support.sup fun e => e 1 := by simp
  have h1 : (Finsupp.single (0 : Fin 2) (p.support.sup fun e => e 1)) 1 = 0 := by simp
  rw [h0, h1, add_zero]
  calc f 1 ≤ p.support.sup (fun e => e 1) := hbound
    _ ≤ d * (p.support.sup fun e => e 1) := Nat.le_mul_of_pos_left _ hd
    _ ≤ d * (f 0 + p.support.sup fun e => e 1) := by
        exact Nat.mul_le_mul_left d (by omega)

/-! ## The cone has the same fraction field as `K[U, T]` -/

/-- The cone ring maps into the fraction field of the ambient polynomial ring. -/
noncomputable instance coneFractionAlgebra (K : Type u) [Field K] (d : ℕ) :
    Algebra (rationalNormalCone K d) (FractionRing (MvPolynomial (Fin 2) K)) :=
  ((algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))).comp
    (rationalNormalCone K d).val.toRingHom).toAlgebra

theorem coneAlgebraMap_apply {d : ℕ} (x : rationalNormalCone K d) :
    algebraMap (rationalNormalCone K d) (FractionRing (MvPolynomial (Fin 2) K)) x
      = algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
        (x : MvPolynomial (Fin 2) K) := rfl

theorem coneAlgebraMap_injective (d : ℕ) :
    Function.Injective
      (algebraMap (rationalNormalCone K d) (FractionRing (MvPolynomial (Fin 2) K))) := by
  intro x y hxy
  rw [coneAlgebraMap_apply, coneAlgebraMap_apply] at hxy
  exact Subtype.ext (IsFractionRing.injective _ _ hxy)

/-- **The cone and the ambient polynomial ring have the same fraction field.** -/
theorem coneIsFractionRing {d : ℕ} (hd : 0 < d) :
    IsFractionRing (rationalNormalCone K d) (FractionRing (MvPolynomial (Fin 2) K)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro y
    refine isUnit_iff_ne_zero.mpr ?_
    intro hzero
    have hy : (y : rationalNormalCone K d) = 0 :=
      coneAlgebraMap_injective d (by rw [map_zero]; exact hzero)
    exact (nonZeroDivisors.coe_ne_zero y) hy
  · intro z
    obtain ⟨a, b, hb, hab⟩ :=
      IsFractionRing.div_surjective (A := MvPolynomial (Fin 2) K)
        (K := FractionRing (MvPolynomial (Fin 2) K)) z
    have hb0 : b ≠ 0 := fun h => by
      simp only [h] at hb
      exact zero_notMem_nonZeroDivisors hb
    obtain ⟨ka, hka⟩ := exists_pow_mul_mem_rationalNormalCone hd a
    obtain ⟨kb, hkb⟩ := exists_pow_mul_mem_rationalNormalCone hd b
    set k := max ka kb with hk
    have hmono : ∀ (p : MvPolynomial (Fin 2) K) (j : ℕ),
        p * MvPolynomial.monomial (Finsupp.single 0 j) (1 : K) ∈ rationalNormalCone K d →
        ∀ l, j ≤ l →
        p * MvPolynomial.monomial (Finsupp.single 0 l) (1 : K) ∈ rationalNormalCone K d := by
      intro p j hj l hjl
      have hjl' : j + (l - j) = l := by omega
      have hsplit : p * MvPolynomial.monomial (Finsupp.single (0 : Fin 2) l) (1 : K)
          = (p * MvPolynomial.monomial (Finsupp.single 0 j) (1 : K))
            * MvPolynomial.monomial (Finsupp.single 0 (l - j)) (1 : K) := by
        rw [mul_assoc, MvPolynomial.monomial_mul, one_mul, ← Finsupp.single_add, hjl']
      rw [hsplit]
      refine Subalgebra.mul_mem _ hj ?_
      refine monomial_mem_monomialSpan ?_
      show (Finsupp.single (0 : Fin 2) (l - j)) 1 ≤ d * (Finsupp.single (0 : Fin 2) (l - j)) 0
      simp
    have hA : a * MvPolynomial.monomial (Finsupp.single 0 k) (1 : K) ∈ rationalNormalCone K d :=
      hmono a ka hka k (le_max_left _ _)
    have hB : b * MvPolynomial.monomial (Finsupp.single 0 k) (1 : K) ∈ rationalNormalCone K d :=
      hmono b kb hkb k (le_max_right _ _)
    have hBne : (⟨b * MvPolynomial.monomial (Finsupp.single 0 k) (1 : K), hB⟩ :
        rationalNormalCone K d) ∈ nonZeroDivisors (rationalNormalCone K d) := by
      rw [mem_nonZeroDivisors_iff_ne_zero]
      intro hcon
      have hval : b * MvPolynomial.monomial (Finsupp.single (0 : Fin 2) k) (1 : K) = 0 :=
        congrArg Subtype.val hcon
      rcases mul_eq_zero.mp hval with h | h
      · exact hb0 h
      · exact absurd h (by simp)
    refine ⟨⟨⟨a * MvPolynomial.monomial (Finsupp.single 0 k) (1 : K), hA⟩,
      ⟨_, hBne⟩⟩, ?_⟩
    rw [coneAlgebraMap_apply, coneAlgebraMap_apply]
    show z * algebraMap _ _ (b * MvPolynomial.monomial (Finsupp.single (0 : Fin 2) k) (1 : K))
      = algebraMap _ _ (a * MvPolynomial.monomial (Finsupp.single (0 : Fin 2) k) (1 : K))
    rw [map_mul, map_mul, ← mul_assoc, ← hab]
    have hbF : algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K)) b ≠ 0 := by
      intro hcon
      refine hb0 (IsFractionRing.injective (MvPolynomial (Fin 2) K)
        (FractionRing (MvPolynomial (Fin 2) K)) ?_)
      rw [map_zero]
      exact hcon
    field_simp
  · intro x y hxy
    exact ⟨1, by rw [coneAlgebraMap_injective d hxy]⟩


/-- **The cone over the rational normal curve is integrally closed.** -/
theorem isIntegrallyClosed_rationalNormalCone {d : ℕ} (hd : 0 < d) :
    IsIntegrallyClosed (rationalNormalCone K d) := by
  classical
  haveI := coneIsFractionRing (K := K) hd
  rw [isIntegrallyClosed_iff (FractionRing (MvPolynomial (Fin 2) K))]
  intro x hx
  obtain ⟨P, hmonic, hroot⟩ := hx
  by_cases hn : P.natDegree = 0
  · rw [Polynomial.eq_one_of_monic_natDegree_zero hmonic hn, Polynomial.eval₂_one] at hroot
    exact absurd hroot one_ne_zero
  · rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hmonic.coeff_natDegree,
      map_one, one_mul] at hroot
    obtain ⟨y, hy, hyx⟩ := exists_mem_rationalNormalCone_of_relation_fractionRing
      (K := K) (F := FractionRing (MvPolynomial (Fin 2) K))
      (d := d) (n := P.natDegree) (Nat.pos_of_ne_zero hn)
      (fun j => ((P.coeff j : rationalNormalCone K d) : MvPolynomial (Fin 2) K))
      (fun j => (P.coeff j).2) (by rw [add_comm]; exact hroot)
    exact ⟨⟨y, hy⟩, by rw [coneAlgebraMap_apply]; exact hyx⟩


end GaloisForLFunctions.HTGeometry
