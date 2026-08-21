import GaloisForLFunctions.HTGeometry.ABHN.CyclicAlgebra
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2

/-!
# Cyclic Galois specialization of the twisted cyclic-algebra carrier

This module specializes the raw skew quotient to the automorphism group of `L/K`.  In the intended
finite cyclic Galois case, its parameter comes from `K`, its degree is `finrank K L`, and its skew
automorphism is the chosen Galois generator.  The resulting relations are the algebraic input for
the map from cyclic degree-two cohomology to Brauer classes.

It proves centrality of the base-field map and a bounded normal-form spanning theorem, hence
finite dimensionality whenever `L/K` is finite.  It does not prove simplicity: that requires the
usual nonzero cyclic parameter together with a Galois-descent argument.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open Multiplicative

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)]

/-- The raw cyclic algebra attached to the cyclic automorphism group and a base-field parameter.
In its intended finite cyclic Galois use, this is the usual cyclic-algebra carrier. -/
noncomputable abbrev cyclicGaloisAlgebra (a : K) :=
  CyclicAlgebra (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L) (algebraMap K L a)

/-- The image of the cyclic generator in the Galois cyclic algebra. -/
noncomputable abbrev cyclicGaloisAlgebraX (a : K) : cyclicGaloisAlgebra K L a :=
  cyclicAlgebraX (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L) (algebraMap K L a)

/-- The image of a coefficient from `L` in the Galois cyclic algebra. -/
noncomputable abbrev cyclicGaloisAlgebraC (a : K) (b : L) : cyclicGaloisAlgebra K L a :=
  cyclicAlgebraC (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
    (algebraMap K L a) b

/-- The prospective base-field coefficient map.  Upgrading it to an `Algebra K` structure waits
for the proof that its image commutes with every quotient element. -/
noncomputable def cyclicGaloisAlgebraBaseRingHom (a : K) :
    K →+* cyclicGaloisAlgebra K L a :=
  (cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
    (algebraMap K L a)).comp (algebraMap K L)

/-- Evaluation of the prospective base-field map is the named embedded coefficient. -/
theorem cyclicGaloisAlgebraBaseRingHom_apply (a b : K) :
    cyclicGaloisAlgebraBaseRingHom K L a b =
      cyclicGaloisAlgebraC K L a (algebraMap K L b) := rfl

/-- The Galois cyclic generator satisfies its degree relation. -/
theorem cyclicGaloisAlgebraX_pow (a : K) :
    cyclicGaloisAlgebraX K L a ^ Module.finrank K L =
      cyclicGaloisAlgebraC K L a (algebraMap K L a) := by
  exact cyclicAlgebraX_pow L (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
    (algebraMap K L a)

/-- The cyclic generator commutes with coefficients embedded from the base field. -/
theorem cyclicGaloisAlgebraX_mul_baseC (a b : K) :
    cyclicGaloisAlgebraX K L a * cyclicGaloisAlgebraC K L a (algebraMap K L b) =
      cyclicGaloisAlgebraC K L a (algebraMap K L b) * cyclicGaloisAlgebraX K L a := by
  rw [cyclicAlgebraX_mul_cyclicAlgebraC]
  simp

/-- Every power of the cyclic generator commutes with a base-field coefficient. -/
theorem cyclicGaloisAlgebraX_pow_mul_baseC (a b : K) (m : ℕ) :
    cyclicGaloisAlgebraX K L a ^ m * cyclicGaloisAlgebraC K L a (algebraMap K L b) =
      cyclicGaloisAlgebraC K L a (algebraMap K L b) * cyclicGaloisAlgebraX K L a ^ m := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    rw [pow_succ, mul_assoc, cyclicGaloisAlgebraX_mul_baseC]
    rw [← mul_assoc, ih, mul_assoc]

/-- A base coefficient commutes with the quotient image of each skew monomial. -/
theorem cyclicGaloisAlgebraBaseC_commutes_monomial (a b : K) (m : ℕ) (c : L) :
    cyclicGaloisAlgebraC K L a (algebraMap K L b) *
      (Ideal.Quotient.mk
        (cyclicRelationIdeal (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
          (algebraMap K L a))
        (SkewPolynomial.monomial m c) : cyclicGaloisAlgebra K L a) =
      (Ideal.Quotient.mk
        (cyclicRelationIdeal (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
          (algebraMap K L a))
        (SkewPolynomial.monomial m c) : cyclicGaloisAlgebra K L a) *
        cyclicGaloisAlgebraC K L a (algebraMap K L b) := by
  rw [cyclicAlgebraMonomial_eq]
  calc
    cyclicGaloisAlgebraC K L a (algebraMap K L b) *
        (cyclicGaloisAlgebraC K L a c * cyclicGaloisAlgebraX K L a ^ m) =
      (cyclicGaloisAlgebraC K L a (algebraMap K L b) *
        cyclicGaloisAlgebraC K L a c) * cyclicGaloisAlgebraX K L a ^ m :=
          (mul_assoc _ _ _).symm
    _ = (cyclicGaloisAlgebraC K L a c *
        cyclicGaloisAlgebraC K L a (algebraMap K L b)) * cyclicGaloisAlgebraX K L a ^ m := by
          rw [cyclicAlgebraC_comm]
    _ = cyclicGaloisAlgebraC K L a c *
        (cyclicGaloisAlgebraC K L a (algebraMap K L b) * cyclicGaloisAlgebraX K L a ^ m) :=
          mul_assoc _ _ _
    _ = cyclicGaloisAlgebraC K L a c *
        (cyclicGaloisAlgebraX K L a ^ m * cyclicGaloisAlgebraC K L a (algebraMap K L b)) := by
          rw [cyclicGaloisAlgebraX_pow_mul_baseC]
    _ = (cyclicGaloisAlgebraC K L a c * cyclicGaloisAlgebraX K L a ^ m) *
        cyclicGaloisAlgebraC K L a (algebraMap K L b) := by
          rw [mul_assoc]

/-- A base coefficient commutes with the quotient image of every skew polynomial. -/
theorem cyclicGaloisAlgebraBaseC_commutes_mk (a b : K)
    (p : CyclicSkewPolynomial L (cyclicGaloisGenerator K L).toRingEquiv) :
    cyclicGaloisAlgebraC K L a (algebraMap K L b) *
      Ideal.Quotient.mk
        (cyclicRelationIdeal (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
          (algebraMap K L a)) p =
      Ideal.Quotient.mk
        (cyclicRelationIdeal (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
          (algebraMap K L a)) p *
        cyclicGaloisAlgebraC K L a (algebraMap K L b) := by
  induction p using SkewMonoidAlgebra.induction_on with
  | zero =>
    simp
  | single g c =>
    change cyclicGaloisAlgebraC K L a (algebraMap K L b) *
        (Ideal.Quotient.mk
          (cyclicRelationIdeal (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
            (algebraMap K L a))
          (SkewPolynomial.monomial (toAdd g) c) : cyclicGaloisAlgebra K L a) =
      (Ideal.Quotient.mk
          (cyclicRelationIdeal (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
            (algebraMap K L a))
          (SkewPolynomial.monomial (toAdd g) c) : cyclicGaloisAlgebra K L a) *
          cyclicGaloisAlgebraC K L a (algebraMap K L b)
    exact cyclicGaloisAlgebraBaseC_commutes_monomial K L a b (toAdd g) c
  | add p q hp hq =>
    rw [map_add, mul_add, add_mul, hp, hq]

/-- The prospective base-field map is central in the whole quotient. -/
theorem cyclicGaloisAlgebraBaseRingHom_commutes (a b : K) (x : cyclicGaloisAlgebra K L a) :
    Commute (cyclicGaloisAlgebraBaseRingHom K L a b) x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact cyclicGaloisAlgebraBaseC_commutes_mk K L a b p

/-- The cyclic Galois quotient is a `K`-algebra: the preceding theorem supplies centrality. -/
noncomputable instance (a : K) : Algebra K (cyclicGaloisAlgebra K L a) := by
  letI : SMul K (cyclicGaloisAlgebra K L a) :=
    ⟨fun b x => cyclicGaloisAlgebraBaseRingHom K L a b * x⟩
  exact
    { algebraMap := cyclicGaloisAlgebraBaseRingHom K L a
      commutes' := fun b x => (cyclicGaloisAlgebraBaseRingHom_commutes K L a b x).eq
      smul_def' := fun _ _ => rfl }

/-- The `K`-algebra map is the central coefficient inclusion. -/
theorem cyclicGaloisAlgebra_algebraMap_apply (a b : K) :
    algebraMap K (cyclicGaloisAlgebra K L a) b =
      cyclicGaloisAlgebraC K L a (algebraMap K L b) := rfl

/-- The `i`th normal-form coefficient map, linear over the base field. -/
noncomputable def cyclicGaloisAlgebraCoefficientLinearMap (a : K) (i : ℕ) :
    L →ₗ[K] cyclicGaloisAlgebra K L a where
  toFun := fun c => cyclicGaloisAlgebraC K L a c * cyclicGaloisAlgebraX K L a ^ i
  map_add' := by
    intro c d
    change cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
      (Module.finrank K L) (algebraMap K L a) (c + d) * cyclicGaloisAlgebraX K L a ^ i = _
    rw [map_add, add_mul]
    rfl
  map_smul' := by
    intro r c
    simp only [RingHom.id_apply, Algebra.smul_def]
    rw [cyclicGaloisAlgebra_algebraMap_apply]
    rw [← mul_assoc, cyclicAlgebraC_mul]

/-- The bounded normal-form map: one coefficient from `L` for each variable exponent below
`finrank K L`. -/
noncomputable def cyclicGaloisAlgebraNormalFormLinearMap (a : K) :
    (Fin (Module.finrank K L) → L) →ₗ[K] cyclicGaloisAlgebra K L a :=
  LinearMap.lsum K (fun _ : Fin (Module.finrank K L) => L) K
    (fun i => cyclicGaloisAlgebraCoefficientLinearMap K L a i)

/-- Evaluation of the bounded normal-form map on one nonzero coordinate. -/
theorem cyclicGaloisAlgebraNormalFormLinearMap_single (a : K)
    (i : Fin (Module.finrank K L)) (c : L) :
    cyclicGaloisAlgebraNormalFormLinearMap K L a (Pi.single i c) =
      cyclicGaloisAlgebraC K L a c * cyclicGaloisAlgebraX K L a ^ (i : ℕ) := by
  simp [cyclicGaloisAlgebraNormalFormLinearMap, LinearMap.lsum_apply,
    cyclicGaloisAlgebraCoefficientLinearMap]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
    change cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
      (Module.finrank K L) (algebraMap K L a) 0 * cyclicGaloisAlgebraX K L a ^ (j : ℕ) = 0
    rw [map_zero, zero_mul]
  · simp

/-- Every cyclic quotient element has a bounded normal-form representative. -/
theorem cyclicGaloisAlgebraNormalFormLinearMap_surjective [FiniteDimensional K L] (a : K) :
    Function.Surjective (cyclicGaloisAlgebraNormalFormLinearMap K L a) := by
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using SkewMonoidAlgebra.induction_on with
  | zero =>
    refine ⟨0, ?_⟩
    simp
  | add p q hp hq =>
    obtain ⟨fp, hfp⟩ := hp
    obtain ⟨fq, hfq⟩ := hq
    refine ⟨fp + fq, ?_⟩
    rw [map_add, hfp, hfq, map_add]
  | single g c =>
    let i : Fin (Module.finrank K L) :=
      ⟨toAdd g % Module.finrank K L,
        Nat.mod_lt _ (Module.finrank_pos (R := K) (M := L))⟩
    refine ⟨Pi.single i (c * (algebraMap K L a) ^ (toAdd g / Module.finrank K L)), ?_⟩
    rw [cyclicGaloisAlgebraNormalFormLinearMap_single]
    change cyclicGaloisAlgebraC K L a
        (c * (algebraMap K L a) ^ (toAdd g / Module.finrank K L)) *
        cyclicGaloisAlgebraX K L a ^ (toAdd g % Module.finrank K L) =
      (Ideal.Quotient.mk
        (cyclicRelationIdeal (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
          (algebraMap K L a))
        (SkewPolynomial.monomial (toAdd g) c) : cyclicGaloisAlgebra K L a)
    exact (cyclicAlgebraMonomial_mod_normalForm (cyclicGaloisGenerator K L).toRingEquiv
      (Module.finrank K L) (algebraMap K L a) c (toAdd g)).symm

/-- A cyclic Galois quotient is finite-dimensional whenever its coefficient field is. -/
theorem cyclicGaloisAlgebra_finiteDimensional [FiniteDimensional K L] (a : K) :
    FiniteDimensional K (cyclicGaloisAlgebra K L a) := by
  exact FiniteDimensional.of_surjective (cyclicGaloisAlgebraNormalFormLinearMap K L a)
    (cyclicGaloisAlgebraNormalFormLinearMap_surjective K L a)

noncomputable instance (a : K) [FiniteDimensional K L] :
    FiniteDimensional K (cyclicGaloisAlgebra K L a) :=
  cyclicGaloisAlgebra_finiteDimensional K L a

/-- The bounded normal form gives the expected square upper bound on the dimension. -/
theorem cyclicGaloisAlgebra_finrank_le [FiniteDimensional K L] (a : K) :
    Module.finrank K (cyclicGaloisAlgebra K L a) ≤
      Module.finrank K L * Module.finrank K L := by
  calc
    Module.finrank K (cyclicGaloisAlgebra K L a) ≤
        Module.finrank K (Fin (Module.finrank K L) → L) :=
      LinearMap.finrank_le_finrank_of_surjective
        (cyclicGaloisAlgebraNormalFormLinearMap_surjective K L a)
    _ = Module.finrank K L * Module.finrank K L := by
      rw [Module.finrank_pi_fintype]
      simp

end GaloisForLFunctions.HTGeometry.ABHN
