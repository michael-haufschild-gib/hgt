import GaloisForLFunctions.HTGeometry.ReparametrizationAutomorphism

/-!
# Similarity automorphisms act on the generic reparametrisation

An isogeny pullback rescales the derivation rather than preserving it: on the plane,
`(f (m ·))′ = m · f′(m ·)`.  Such a *similarity* of a differential field still acts on the generic
reparametrisation, provided the jets are rescaled by the same constant factor: the reparametrisation
`u` is replaced by `c · u`.

The resulting automorphism commutes with the chain-rule derivation, so an isogeny protocol acts on
the differential-generic carrier exactly as it acts on the base.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace ReparamField

universe u

variable {K : Type u} [Field K] [Differential K]

section

variable (e : K ≃+* K) (c : K)

/-- The coefficient part of a similarity, as a ring homomorphism to the jet polynomial ring. -/
noncomputable def twistBaseHom : K →+* ReparamPoly K :=
  (MvPolynomial.C : K →+* ReparamPoly K).comp (e : K →+* K)

/-- A similarity acts on the jet polynomial ring: coefficients by `e`, jets by the factor `c`. -/
noncomputable def twistPolyHom : ReparamPoly K →+* ReparamPoly K :=
  MvPolynomial.eval₂Hom (twistBaseHom e) fun i : ℕ => MvPolynomial.C c * MvPolynomial.X i

@[simp] theorem twistPolyHom_C (a : K) :
    twistPolyHom e c (MvPolynomial.C a) = MvPolynomial.C (e a) := by
  simp [twistPolyHom, twistBaseHom]

@[simp] theorem twistPolyHom_X (i : ℕ) :
    twistPolyHom e c (MvPolynomial.X i) = MvPolynomial.C c * MvPolynomial.X i := by
  simp [twistPolyHom]

end

variable {e : K ≃+* K} {c : K}

theorem twistPolyHom_comp (hc : c ≠ 0) (hec : e c = c) :
    (twistPolyHom e.symm c⁻¹).comp (twistPolyHom e c) = RingHom.id (ReparamPoly K) := by
  refine MvPolynomial.ringHom_ext ?_ ?_
  · intro a
    simp [twistPolyHom_C]
  · intro i
    have hsymm : e.symm c = c := by
      rw [RingEquiv.symm_apply_eq]
      exact hec.symm
    simp only [RingHom.coe_comp, Function.comp_apply, twistPolyHom_X, map_mul, twistPolyHom_C,
      hsymm, RingHom.id_apply]
    rw [← mul_assoc, ← MvPolynomial.C_mul, mul_inv_cancel₀ hc, MvPolynomial.C_1, one_mul]

/-- **A similarity of the base acts on the jet polynomial ring.** -/
noncomputable def twistPolyEquiv (hc : c ≠ 0) (hec : e c = c) :
    ReparamPoly K ≃+* ReparamPoly K where
  toFun := twistPolyHom e c
  invFun := twistPolyHom e.symm c⁻¹
  left_inv := by
    intro p
    exact RingHom.congr_fun (twistPolyHom_comp hc hec) p
  right_inv := by
    intro p
    have hc' : c⁻¹ ≠ 0 := inv_ne_zero hc
    have hec' : e.symm c⁻¹ = c⁻¹ := by
      rw [RingEquiv.symm_apply_eq, map_inv₀, hec]
    have hcomp := twistPolyHom_comp (e := e.symm) (c := c⁻¹) hc' hec'
    have := RingHom.congr_fun hcomp p
    simpa [inv_inv] using this
  map_add' _ _ := map_add _ _ _
  map_mul' _ _ := map_mul _ _ _

@[simp] theorem twistPolyEquiv_apply (hc : c ≠ 0) (hec : e c = c) (p : ReparamPoly K) :
    twistPolyEquiv hc hec p = twistPolyHom e c p := rfl

/-- **A similarity of the base acts on the generic reparametrisation.** -/
noncomputable def twistFieldEquiv (hc : c ≠ 0) (hec : e c = c) :
    ReparamField K ≃+* ReparamField K :=
  IsFractionRing.ringEquivOfRingEquiv (twistPolyEquiv hc hec)

theorem twistFieldEquiv_algebraMap (hc : c ≠ 0) (hec : e c = c) (p : ReparamPoly K) :
    twistFieldEquiv hc hec (algebraMap (ReparamPoly K) (ReparamField K) p)
      = algebraMap (ReparamPoly K) (ReparamField K) (twistPolyHom e c p) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (twistPolyEquiv hc hec) p

theorem algebraMap_base_eq (a : K) :
    (algebraMap K (ReparamField K) a)
      = algebraMap (ReparamPoly K) (ReparamField K) (MvPolynomial.C a) := by
  rw [IsScalarTower.algebraMap_apply K (ReparamPoly K) (ReparamField K)]
  rfl

@[simp] theorem twistFieldEquiv_base (hc : c ≠ 0) (hec : e c = c) (a : K) :
    twistFieldEquiv hc hec (algebraMap K (ReparamField K) a)
      = algebraMap K (ReparamField K) (e a) := by
  rw [algebraMap_base_eq a, twistFieldEquiv_algebraMap, twistPolyHom_C, ← algebraMap_base_eq]

@[simp] theorem twistFieldEquiv_jet (hc : c ≠ 0) (hec : e c = c) (i : ℕ) :
    twistFieldEquiv hc hec (jet i : ReparamField K)
      = algebraMap K (ReparamField K) c * jet i := by
  rw [jet, twistFieldEquiv_algebraMap, twistPolyHom_X, map_mul, ← algebraMap_base_eq]

theorem twistFieldEquiv_symm_base (hc : c ≠ 0) (hec : e c = c) (a : K) :
    (twistFieldEquiv hc hec).symm (algebraMap K (ReparamField K) (e a))
      = algebraMap K (ReparamField K) a := by
  apply (twistFieldEquiv hc hec).injective
  rw [RingEquiv.apply_symm_apply, twistFieldEquiv_base]

theorem twistFieldEquiv_symm_jet (hc : c ≠ 0) (hec : e c = c) (i : ℕ) :
    (twistFieldEquiv hc hec).symm (algebraMap K (ReparamField K) c * jet i)
      = (jet i : ReparamField K) := by
  apply (twistFieldEquiv hc hec).injective
  rw [RingEquiv.apply_symm_apply, twistFieldEquiv_jet]

theorem twistFieldEquiv_symm_jet' (hc : c ≠ 0) (hec : e c = c) (i : ℕ) :
    (twistFieldEquiv hc hec).symm (jet i : ReparamField K)
      = algebraMap K (ReparamField K) c⁻¹ * jet i := by
  apply (twistFieldEquiv hc hec).injective
  rw [RingEquiv.apply_symm_apply, map_mul, twistFieldEquiv_base, twistFieldEquiv_jet,
    show e c⁻¹ = c⁻¹ from by rw [map_inv₀, hec], ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc,
    map_one, one_mul]

/-- The conjugate of the chain-rule derivation by a similarity. -/
noncomputable def twistConjDerivation (hc : c ≠ 0) (hec : e c = c) :
    Derivation ℤ (ReparamField K) (ReparamField K) := by
  let D : ReparamField K →+ ReparamField K :=
    { toFun := fun z =>
        (twistFieldEquiv hc hec).symm (fieldDerivation K (twistFieldEquiv hc hec z))
      map_zero' := by simp
      map_add' := by
        intro x y
        simp }
  refine Derivation.mk' D.toIntLinearMap ?_
  intro x y
  show (twistFieldEquiv hc hec).symm (fieldDerivation K (twistFieldEquiv hc hec (x * y)))
    = x • (twistFieldEquiv hc hec).symm (fieldDerivation K (twistFieldEquiv hc hec y))
      + y • (twistFieldEquiv hc hec).symm (fieldDerivation K (twistFieldEquiv hc hec x))
  rw [map_mul, Derivation.leibniz]
  simp only [smul_eq_mul, map_add, map_mul, RingEquiv.symm_apply_apply]

@[simp] theorem twistConjDerivation_apply (hc : c ≠ 0) (hec : e c = c) (z : ReparamField K) :
    twistConjDerivation hc hec z
      = (twistFieldEquiv hc hec).symm (fieldDerivation K (twistFieldEquiv hc hec z)) := rfl

/-- **A similarity of the base extends to an automorphism commuting with the chain-rule
derivation.** -/
theorem twistFieldEquiv_deriv (hc : c ≠ 0) (hec : e c = c)
    (hconstc : Differential.deriv c = 0)
    (htw : ∀ a : K, Differential.deriv (e a) = c * e (Differential.deriv a))
    (z : ReparamField K) :
    twistFieldEquiv hc hec (z′) = (twistFieldEquiv hc hec z)′ := by
  have hjet : ∀ i : ℕ, twistConjDerivation hc hec (jet i : ReparamField K)
      = fieldDerivation K (jet i) := by
    intro i
    rw [twistConjDerivation_apply, twistFieldEquiv_jet]
    simp only [← deriv_eq]
    rw [Differential.deriv.leibniz, deriv_jet, deriv_algebraMap, hconstc]
    simp only [map_zero, zero_mul, smul_eq_mul, mul_zero, add_zero]
    rw [twistFieldEquiv_symm_jet]
  have hbase : ∀ a : K, twistConjDerivation hc hec (algebraMap K (ReparamField K) a)
      = fieldDerivation K (algebraMap K (ReparamField K) a) := by
    intro a
    rw [twistConjDerivation_apply, twistFieldEquiv_base]
    simp only [← deriv_eq]
    rw [deriv_algebraMap, deriv_algebraMap, htw a]
    have hce : c * e (Differential.deriv a) = e (c * Differential.deriv a) := by
      rw [map_mul, hec]
    rw [hce, map_mul, twistFieldEquiv_symm_base, twistFieldEquiv_symm_jet', ← mul_assoc,
      ← map_mul]
    congr 2
    rw [mul_comm c (Differential.deriv a), mul_assoc, mul_inv_cancel₀ hc, mul_one]
  have hconj : twistConjDerivation hc hec = fieldDerivation K := by
    refine GaloisForLFunctions.fractionRing_derivation_ext (A := ReparamPoly K)
      (twistConjDerivation hc hec) (fieldDerivation K) ?_
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
        rw [← algebraMap_base_eq]
        exact hbase a
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
        have hb : (algebraMap (ReparamPoly K) (ReparamField K) (MvPolynomial.X i))
            = (jet i : ReparamField K) := rfl
        rw [map_mul, Derivation.leibniz, Derivation.leibniz, hp, hb, hjet i]
  have hz := congrArg (fun D => D z) hconj
  simp only [twistConjDerivation_apply] at hz
  rw [deriv_eq, ← hz]
  exact (twistFieldEquiv hc hec).apply_symm_apply _

end ReparamField

end GaloisForLFunctions.HTGeometry
