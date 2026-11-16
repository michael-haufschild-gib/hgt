import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Cyclic quotient homomorphisms are operator kernels

Evaluation at the class of one identifies `Hom_R(R/Rp,M)` with the kernel
of multiplication by `p` on `M`. The inverse sends a generator image `v`
to the map `r ↦ r • v`, descended through the actual quotient. This is the
exact cyclic form of the generator-to-kernel reduction in Zehavi, §2.3,
arXiv:2611.18218; no annihilation hypothesis on the target module is needed.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The cyclic module presented by the single relation `p`. -/
abbrev CyclicQuotient (p : R) := R ⧸ Submodule.span R ({p} : Set R)

/-- The distinguished generator in the actual quotient. -/
def cyclicQuotientGenerator (p : R) : CyclicQuotient p :=
  (Submodule.span R ({p} : Set R)).mkQ 1

/-- The defining relation holds on the quotient generator. -/
theorem cyclicQuotientGenerator_relation (p : R) :
    p • cyclicQuotientGenerator p = 0 := by
  change p • (Submodule.span R ({p} : Set R)).mkQ 1 = 0
  rw [← map_smul, smul_eq_mul, mul_one]
  apply LinearMap.mem_ker.mp
  rw [Submodule.ker_mkQ]
  exact Submodule.subset_span (Set.mem_singleton p)

private theorem cyclic_relation_le_kernel (p : R)
    (v : LinearMap.ker (LinearMap.lsmul R M p)) :
    Submodule.span R ({p} : Set R) ≤ (LinearMap.toSpanSingleton R M v.val).ker := by
  apply Submodule.span_le.mpr
  intro r hr
  rw [Set.mem_singleton_iff] at hr
  subst r
  exact v.property

/-- Evaluation at the cyclic generator is a linear equivalence with the full annihilator. -/
def cyclicQuotientHomEquiv (p : R) :
    (CyclicQuotient p →ₗ[R] M) ≃ₗ[R] LinearMap.ker (LinearMap.lsmul R M p) where
  toFun f := ⟨f (cyclicQuotientGenerator p), by
    change p • f (cyclicQuotientGenerator p) = 0
    rw [← map_smul, cyclicQuotientGenerator_relation, map_zero]⟩
  invFun v := (Submodule.span R ({p} : Set R)).liftQ
    (LinearMap.toSpanSingleton R M v.val) (cyclic_relation_le_kernel p v)
  left_inv f := by
    apply LinearMap.ext
    intro q
    obtain ⟨r, rfl⟩ := (Submodule.span R ({p} : Set R)).mkQ_surjective q
    change r • f (cyclicQuotientGenerator p) =
      f ((Submodule.span R ({p} : Set R)).mkQ r)
    rw [← map_smul]
    congr 1
    change r • (Submodule.span R ({p} : Set R)).mkQ 1 = _
    rw [← map_smul, smul_eq_mul, mul_one]
  right_inv v := by
    apply Subtype.ext
    change (1 : R) • v.val = v.val
    exact one_smul R v.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem cyclicQuotientHomEquiv_apply (p : R) (f : CyclicQuotient p →ₗ[R] M) :
    (cyclicQuotientHomEquiv p f).val = f (cyclicQuotientGenerator p) := rfl

/-- Every homomorphism is recovered exactly from its generator image. -/
theorem cyclicQuotientHom_apply (p r : R) (f : CyclicQuotient p →ₗ[R] M) :
    f ((Submodule.span R ({p} : Set R)).mkQ r) = r • f (cyclicQuotientGenerator p) := by
  rw [← map_smul]
  congr 1
  change (Submodule.span R ({p} : Set R)).mkQ r =
    r • (Submodule.span R ({p} : Set R)).mkQ 1
  rw [← map_smul, smul_eq_mul, mul_one]

end GaloisForLFunctions.RepresentationLifting.OperatorKernels

#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.cyclicQuotientHomEquiv
