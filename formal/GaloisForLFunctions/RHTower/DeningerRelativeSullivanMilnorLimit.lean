import GaloisForLFunctions.RHTower.DeningerRelativeSullivanMilnorResolution
import GaloisForLFunctions.HTGeometry.GradedSullivanAugmented

/-!
# The relative Sullivan resolution of the two-term algebra

The two-term algebra `k ⊕ V`, with the product of any two elements of `V` equal to zero, is the
target of the relative Sullivan factorization of the exterior algebra on `V`.  Instantiating the
general relative tower at this target produces a free graded-commutative differential algebra over
`Λ(V)` whose cohomology is exactly `k ⊕ V`.

The base is the degree-one free graded-commutative algebra on a basis of `V`, which is the exterior
algebra on `V`; its augmentation is the canonical map to the split square-zero extension, which is
surjective and kills the degree-two part.  The two-term algebra carries the grading involution
fixing the scalars and negating the degree-one part, and the augmentation intertwines it with the
grading involution of the model.

* `deningerMilnorSigma` : the grading involution of the two-term algebra.
* `deningerMilnorGCAEps` : the augmentation of the degree-one model.
* `deningerMilnorAugBase` : the augmented base stage of the tower.
* `deningerMilnorTower_quasiIso` : the limit augmentation is a surjective quasi-isomorphism.
-/

namespace RHTower

open HTGeometry

section MilnorLimit

universe u

variable {k : Type u} [CommRing k] {V : Type u} [AddCommGroup V] [Module k V]
  [Module kᵐᵒᵖ V] [IsCentralScalar k V] {G : Type u}

variable (k V) in
/-- **The grading involution of the two-term algebra**: the identity on the scalars and minus the
identity on the degree-one part. -/
noncomputable def deningerMilnorSigma : TrivSqZeroExt k V →ₐ[k] TrivSqZeroExt k V :=
  TrivSqZeroExt.map (-LinearMap.id)

@[simp]
theorem deningerMilnorSigma_inr (v : V) :
    deningerMilnorSigma k V (TrivSqZeroExt.inr v) = -TrivSqZeroExt.inr v := by
  rw [deningerMilnorSigma, TrivSqZeroExt.map_inr]
  exact map_neg (TrivSqZeroExt.inrHom k V) v

variable (k V) in
/-- **The weight action of the two-term algebra**: the identity on the scalars and scaling by `t` on
the degree-one part.  The grading involution is its value at `-1`. -/
noncomputable def deningerMilnorWeight (t : k) : TrivSqZeroExt k V →ₐ[k] TrivSqZeroExt k V :=
  TrivSqZeroExt.map (t • LinearMap.id)

@[simp]
theorem deningerMilnorWeight_inr (t : k) (v : V) :
    deningerMilnorWeight k V t (TrivSqZeroExt.inr v) = t • TrivSqZeroExt.inr v := by
  rw [deningerMilnorWeight, TrivSqZeroExt.map_inr]
  show TrivSqZeroExt.inrHom k V (t • v) = _
  rw [map_smul]
  rfl

/-- **The augmentation of the degree-one model**: the free graded-commutative algebra on a basis of
`V` maps to the two-term algebra by sending each generator to its square-zero copy.  This is the map
`(2)` of the statement, read through the identification of the degree-one model with the exterior
algebra. -/
noncomputable def deningerMilnorGCAEps (B : Module.Basis G k V) :
    DeningerFreeGCA k G (fun _ : G => 1) →ₐ[k] TrivSqZeroExt k V :=
  (deningerMilnorEpsilon k V).comp (deningerGCAExteriorEquiv k B).toAlgHom

@[simp]
theorem deningerMilnorGCAEps_ι (B : Module.Basis G k V) (x : G) :
    deningerMilnorGCAEps B (deningerGCAι k (fun _ : G => 1) x) = TrivSqZeroExt.inr (B x) := by
  rw [deningerMilnorGCAEps, AlgHom.comp_apply]
  show deningerMilnorEpsilon k V (deningerGCAExteriorEquiv k B _) = _
  rw [deningerGCAExteriorEquiv_ι, deningerMilnorEpsilon_ι]

/-- **The augmentation is the identity on the scalars.**  Together with `deningerMilnorGCAEps_ι`
this is the requirement that the map `(2)` of the statement be the identity on `k ⊕ V`. -/
@[simp]
theorem deningerMilnorGCAEps_algebraMap (B : Module.Basis G k V) (c : k) :
    deningerMilnorGCAEps B (algebraMap k (DeningerFreeGCA k G (fun _ : G => 1)) c) =
      TrivSqZeroExt.inl c := by
  rw [AlgHom.commutes]
  exact congrFun (TrivSqZeroExt.algebraMap_eq_inl k V) c

/-- **The augmentation of the degree-one model is surjective.** -/
theorem deningerMilnorGCAEps_surjective (B : Module.Basis G k V) :
    Function.Surjective (deningerMilnorGCAEps B) := by
  intro y
  obtain ⟨w, hw⟩ := deningerMilnorEpsilon_surjective (k := k) (V := V) y
  refine ⟨(deningerGCAExteriorEquiv k B).symm w, ?_⟩
  show deningerMilnorEpsilon k V (deningerGCAExteriorEquiv k B
    ((deningerGCAExteriorEquiv k B).symm w)) = y
  rw [AlgEquiv.apply_symm_apply, hw]

/-- **The augmented base of the Milnor tower**: the degree-one free graded-commutative algebra on a
basis of `V`, with no differential, augmented onto the two-term algebra. -/
noncomputable def deningerMilnorAugBase (B : Module.Basis G k V) :
    DeningerGCAAugStage k (TrivSqZeroExt k V) :=
  deningerGCAAugBase k (TrivSqZeroExt k V) (fun _ : G => 1) (deningerMilnorGCAEps B)

@[simp]
theorem deningerMilnorAugBase_eps (B : Module.Basis G k V) :
    (deningerMilnorAugBase B).eps = deningerMilnorGCAEps B := rfl

/-- **The augmentation intertwines the two grading involutions.**  A generator of the model has
degree one, and its image in the two-term algebra is negated by the involution there. -/
theorem deningerMilnorGCAEps_sigma (B : Module.Basis G k V) (x : G) :
    deningerMilnorSigma k V
        ((deningerMilnorAugBase B).eps
          (deningerGCAι k (deningerMilnorAugBase B).toStage.deg x)) =
      ((-1 : k) ^ (deningerMilnorAugBase B).toStage.deg x) •
        (deningerMilnorAugBase B).eps
          (deningerGCAι k (deningerMilnorAugBase B).toStage.deg x) := by
  show deningerMilnorSigma k V (deningerMilnorGCAEps B (deningerGCAι k (fun _ : G => 1) x)) =
    ((-1 : k) ^ 1) • deningerMilnorGCAEps B (deningerGCAι k (fun _ : G => 1) x)
  rw [deningerMilnorGCAEps_ι, deningerMilnorSigma_inr, pow_one]
  module

/-- **The augmentation intertwines the weight actions.**  A generator of the model has degree one and
its image in the two-term algebra is scaled by `t`. -/
theorem deningerMilnorGCAEps_weight (B : Module.Basis G k V) (t : k) (x : G) :
    deningerMilnorWeight k V t
        ((deningerMilnorAugBase B).eps
          (deningerGCAι k (deningerMilnorAugBase B).toStage.deg x)) =
      (t ^ (deningerMilnorAugBase B).toStage.deg x) •
        (deningerMilnorAugBase B).eps
          (deningerGCAι k (deningerMilnorAugBase B).toStage.deg x) := by
  show deningerMilnorWeight k V t (deningerMilnorGCAEps B (deningerGCAι k (fun _ : G => 1) x)) =
    (t ^ 1) • deningerMilnorGCAEps B (deningerGCAι k (fun _ : G => 1) x)
  rw [deningerMilnorGCAEps_ι, deningerMilnorWeight_inr, pow_one]

/-- **The relative Sullivan resolution of the two-term algebra.**  The limit of the relative tower
over the degree-one model of `Λ(V)`, augmented onto `k ⊕ V`, is a free graded-commutative
differential algebra whose augmentation is a surjective quasi-isomorphism: every element of the
two-term algebra is the image of a cocycle, and every cocycle dying there is a coboundary.

This is the specialization `(4)` of the statement, carried through the factorization `(3)`. -/
theorem deningerMilnorTower_quasiIso [Invertible (2 : k)] (B : Module.Basis G k V) :
    (∀ y : TrivSqZeroExt k V, ∃ z,
        (DeningerGCAAugStage.omega (deningerMilnorAugBase B)).d z = 0 ∧
          DeningerGCAAugStage.epsOmega (deningerMilnorAugBase B) z = y) ∧
      (∀ z : DeningerFreeGCA k (DeningerGCAAugStage.omegaGen (deningerMilnorAugBase B))
          (DeningerGCAAugStage.omegaDeg (deningerMilnorAugBase B)),
        (DeningerGCAAugStage.omega (deningerMilnorAugBase B)).d z = 0 →
        DeningerGCAAugStage.epsOmega (deningerMilnorAugBase B) z = 0 →
        ∃ y, (DeningerGCAAugStage.omega (deningerMilnorAugBase B)).d y = z) :=
  DeningerGCAAugStage.omega_quasiIso' (deningerMilnorAugBase B) (deningerMilnorSigma k V)
    (deningerMilnorGCAEps_sigma B)
    (fun z => DeningerGCAStage.base_d (fun _ : G => 1) z)
    (deningerMilnorGCAEps_surjective B)

/-- **The statement over a field of characteristic zero.**  Every vector space over such a field has
a basis and `2` is invertible there, so the relative Sullivan resolution of the two-term algebra
exists with no hypotheses beyond those of the theorem: the limit of the relative tower over the
degree-one model of `Λ(V)` has an augmentation onto `k ⊕ V` which is a surjective
quasi-isomorphism. -/
theorem deningerMilnorTower_quasiIso_ofVectorSpace {k : Type u} [Field k] [CharZero k]
    {V : Type u} [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V] :
    (∀ y : TrivSqZeroExt k V, ∃ z,
        (DeningerGCAAugStage.omega
          (deningerMilnorAugBase (Module.Basis.ofVectorSpace k V))).d z = 0 ∧
          DeningerGCAAugStage.epsOmega
            (deningerMilnorAugBase (Module.Basis.ofVectorSpace k V)) z = y) ∧
      (∀ z : DeningerFreeGCA k
          (DeningerGCAAugStage.omegaGen (deningerMilnorAugBase (Module.Basis.ofVectorSpace k V)))
          (DeningerGCAAugStage.omegaDeg (deningerMilnorAugBase (Module.Basis.ofVectorSpace k V))),
        (DeningerGCAAugStage.omega
          (deningerMilnorAugBase (Module.Basis.ofVectorSpace k V))).d z = 0 →
        DeningerGCAAugStage.epsOmega
          (deningerMilnorAugBase (Module.Basis.ofVectorSpace k V)) z = 0 →
        ∃ y, (DeningerGCAAugStage.omega
          (deningerMilnorAugBase (Module.Basis.ofVectorSpace k V))).d y = z) := by
  haveI : Invertible (2 : k) := invertibleOfNonzero (by norm_num)
  exact deningerMilnorTower_quasiIso (Module.Basis.ofVectorSpace k V)

/-- **The augmentation of the resolution is surjective.** -/
theorem deningerMilnorTower_epsOmega_surjective [Invertible (2 : k)] (B : Module.Basis G k V) :
    Function.Surjective
      (DeningerGCAAugStage.epsOmega (deningerMilnorAugBase B)) :=
  DeningerGCAAugStage.epsOmega_surjective (deningerMilnorAugBase B)
    (fun z => DeningerGCAStage.base_d (fun _ : G => 1) z) (deningerMilnorGCAEps_surjective B)

end MilnorLimit

end RHTower
