import GaloisForLFunctions.RepresentationLifting.Descent.SemilinearAveraging
import GaloisForLFunctions.RHTower.Deninger.DeningerCohomologyDimensionShift

/-!
# Semilinear representations have no positive group cohomology

Trace-one averaging turns a linear retraction of the coinduction unit into
an equivariant retraction. Thus a semilinear representation is a direct
summand of a coinduced representation. Shapiro vanishing then kills every
positive cohomology group, without an invertibility assumption on the
group order or a finite-dimensionality assumption on the representation.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open CategoryTheory Limits
open scoped BigOperators
universe u
variable (K L G V : Type u) [CommRing K] [Field L] [Algebra K L]
  [Group G] [Fintype G] [MulSemiringAction G L]
  [AddCommGroup V] [Module K V] [Module L V] [IsScalarTower K L V]
  [DistribMulAction G V] [SMulDistribClass G L V] [SMulCommClass G K V]

/-- Scalar-weighted conjugation averages an ordinary linear map. -/
def semilinearAverageLinearMap (B : Rep K G) (f : B →ₗ[K] V) (a : L) : B →ₗ[K] V :=
  ∑ g : G, (g • a) • ((Representation.ofDistribMulAction K G V g).comp
    (f.comp (B.ρ g⁻¹)))

omit [SMulDistribClass G L V] in
theorem semilinearAverageLinearMap_apply (B : Rep K G) (f : B →ₗ[K] V) (a : L) (v : B) :
    semilinearAverageLinearMap K L G V B f a v =
      ∑ g : G, (g • a) • (g • f (B.ρ g⁻¹ v)) := by
  simp only [semilinearAverageLinearMap, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, Representation.ofDistribMulAction_apply_apply]

/-- Weighted conjugation is equivariant even in modular characteristic. -/
def semilinearAveragedHom (B : Rep K G) (f : B →ₗ[K] V) (a : L) :
    B ⟶ Rep.ofDistribMulAction K G V :=
  Rep.ofHom ⟨semilinearAverageLinearMap K L G V B f a, fun h => by
    ext v
    change semilinearAverageLinearMap K L G V B f a (B.ρ h v) =
      h • semilinearAverageLinearMap K L G V B f a v
    symm
    rw [semilinearAverageLinearMap_apply, Finset.smul_sum, semilinearAverageLinearMap_apply]
    simp only [smul_distrib_smul, smul_smul]
    apply Fintype.sum_equiv (Equiv.mulLeft h)
      (fun g : G => ((h * g) • a) • ((h * g) • f (B.ρ g⁻¹ v)))
      (fun g : G => (g • a) • (g • f (B.ρ g⁻¹ (B.ρ h v))))
    intro g
    have he : B.ρ ((h * g)⁻¹) (B.ρ h v) = B.ρ g⁻¹ v := by
      rw [← Module.End.mul_apply, ← map_mul]
      congr 1
      group
    change ((h * g) • a) • ((h * g) • f (B.ρ g⁻¹ v)) =
      ((h * g) • a) • ((h * g) • f (B.ρ ((h * g)⁻¹) (B.ρ h v)))
    rw [he]⟩

/-- Trace-one averaging preserves a linear retraction of an equivariant inclusion. -/
theorem semilinearAveragedHom_retraction (B : Rep K G)
    (j : Rep.ofDistribMulAction K G V ⟶ B) (f : B →ₗ[K] V)
    (hf : ∀ v : V, f (j.hom v) = v) (a : L) (ha : ∑ g : G, g • a = 1) :
    j ≫ semilinearAveragedHom K L G V B f a = 𝟙 (Rep.ofDistribMulAction K G V) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine LinearMap.ext (fun (v : V) => ?_)
  change semilinearAverageLinearMap K L G V B f a (j.hom v) = v
  rw [semilinearAverageLinearMap_apply]
  have hterm (g : G) : (g • a) • (g • f (B.ρ g⁻¹ (j.hom v))) = (g • a) • v := by
    rw [← Rep.hom_comm_apply, hf]
    change (g • a) • (g • (g⁻¹ • v)) = (g • a) • v
    rw [smul_inv_smul]
  simp only [hterm]
  rw [← Finset.sum_smul, ha, one_smul]

variable [FaithfulSMul G L]

include L in
/-- The coinduction unit of a semilinear representation admits an equivariant retraction. -/
theorem semilinearCoindUnit_isSplitMono :
    IsSplitMono (RHTower.deningerCoindUnit (Rep.ofDistribMulAction K G V)) := by
  let A := Rep.ofDistribMulAction K G V
  let B := (Rep.coindFunctor K (⊥ : Subgroup G).subtype).obj
    ((Rep.resFunctor (⊥ : Subgroup G).subtype).obj A)
  let c := (Rep.resCoindAdjunction K (⊥ : Subgroup G).subtype).counit.app
    ((Rep.resFunctor (⊥ : Subgroup G).subtype).obj A)
  let f : B →ₗ[K] V := c.hom.toLinearMap
  have hf (v : V) : f ((RHTower.deningerCoindUnit A).hom v) = v := by
    have h := (Rep.resCoindAdjunction K (⊥ : Subgroup G).subtype).left_triangle_components A
    exact congrArg (fun t => t.hom v) h
  obtain ⟨a, ha⟩ := exists_scalarOrbitTrace_one G L
  refine ⟨⟨semilinearAveragedHom K L G V B f a, ?_⟩⟩
  exact semilinearAveragedHom_retraction K L G V B (RHTower.deningerCoindUnit A) f hf a ha

include L in
/-- Every positive native group cohomology object of a semilinear representation is zero. -/
theorem semilinear_groupCohomology_isZero (n : ℕ) :
    IsZero (groupCohomology (Rep.ofDistribMulAction K G V) (n + 1)) := by
  let A := Rep.ofDistribMulAction K G V
  have hs : IsSplitMono (RHTower.deningerCoindUnit A) :=
    semilinearCoindUnit_isSplitMono K L G V
  let s := hs.exists_splitMono.some.map (groupCohomology.functor K G (n + 1))
  have hz : IsZero ((groupCohomology.functor K G (n + 1)).obj
      ((Rep.coindFunctor K (⊥ : Subgroup G).subtype).obj
        ((Rep.resFunctor (⊥ : Subgroup G).subtype).obj A))) :=
    RHTower.deningerIsZero_coind_succ
      ((Rep.resFunctor (⊥ : Subgroup G).subtype).obj A) n
  -- Cohomology preserves the splitting, so its identity factors through a zero object.
  change IsZero ((groupCohomology.functor K G (n + 1)).obj A)
  apply (IsZero.iff_id_eq_zero _).2
  exact s.id.symm.trans (by rw [hz.eq_zero_of_src s.retraction, comp_zero])

/-- Additive Hilbert 90 in all positive degrees for the actual automorphism action of a finite extension. -/
theorem finiteExtension_additive_groupCohomology_isZero
    (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (n : ℕ) :
    IsZero (groupCohomology (Rep.ofDistribMulAction K (L ≃ₐ[K] L) L) (n + 1)) := by
  letI : SMulDistribClass (L ≃ₐ[K] L) L L :=
    ⟨fun g x y => map_mul g x y⟩
  exact semilinear_groupCohomology_isZero K L (L ≃ₐ[K] L) L n

/-- The same vanishing for ordinary integral group cohomology of the additive field. -/
theorem finiteExtension_additiveIntegralCohomology_isZero
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (n : ℕ) :
    IsZero (groupCohomology (Rep.ofDistribMulAction ℤ (L ≃ₐ[K] L) L) (n + 1)) := by
  letI : SMulDistribClass (L ≃ₐ[K] L) L L :=
    ⟨fun g x y => map_mul g x y⟩
  exact semilinear_groupCohomology_isZero ℤ L (L ≃ₐ[K] L) L n

end GaloisForLFunctions.RepresentationLifting
