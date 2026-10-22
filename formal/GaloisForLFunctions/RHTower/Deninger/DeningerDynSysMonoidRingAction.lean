import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysInvariantPoints
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# The induced action on the monoid ring

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Theorem 1.4 (`t27n`),
second assertion.  The source deduces

`Hom (W_rat (A), C) / H ≅ Hom (W_rat (A ^ H), C)`

from the first assertion applied to `W_rat (A)`, the step being the observation — flagged in the
source with an exclamation mark — that a profinite group acting with finite orbits on `A` acts with
finite orbits on the monoid ring, hence continuously.

That step is `stabilizer_isOpen`: an element of `ℤ A` has finite support, so its stabilizer
contains the finite intersection of the stabilizers of the support elements, which is open.  The
resulting bijection is `restrict_surjective` together with `restrict_eq_iff`; via the Teichmüller
comparison `ω : ℤ̲A → W_rat (A)` it is the source's statement.

The action of `G` on `ℤ A` is a `scoped instance` so that it does not interfere with unrelated
`MonoidAlgebra` instances elsewhere.
-/

namespace RHTower

namespace DeningerMonoidRing

open MulAction MonoidAlgebra

variable {A : Type*} [CommRing A] {G : Type*} [Group G] [MulSemiringAction G A]

/-- The multiplicative equivalence of `A` given by an element of `G`. -/
def mulEquivOf (σ : G) : A ≃* A :=
  (MulSemiringAction.toRingEquiv G A σ).toMulEquiv

@[simp] theorem mulEquivOf_apply (σ : G) (a : A) : mulEquivOf σ a = σ • a := rfl

@[simp] theorem mulEquivOf_symm_apply (σ : G) (a : A) :
    (mulEquivOf (A := A) σ).symm a = σ⁻¹ • a := rfl

/-- The action of `G` on the monoid ring `ℤ A` induced by a semiring action on `A`. -/
noncomputable scoped instance instMulSemiringAction :
    MulSemiringAction G (MonoidAlgebra ℤ A) where
  smul σ x := MonoidAlgebra.domCongr ℤ ℤ (mulEquivOf σ) x
  one_smul x := by
    refine MonoidAlgebra.ext (Finsupp.ext fun n => ?_)
    show (MonoidAlgebra.domCongr ℤ ℤ (mulEquivOf (1 : G)) x).coeff n = x.coeff n
    rw [coeff_domCongr]
    simp
  mul_smul σ τ x := by
    refine MonoidAlgebra.ext (Finsupp.ext fun n => ?_)
    show (MonoidAlgebra.domCongr ℤ ℤ (mulEquivOf (σ * τ)) x).coeff n
      = (MonoidAlgebra.domCongr ℤ ℤ (mulEquivOf σ)
          (MonoidAlgebra.domCongr ℤ ℤ (mulEquivOf τ) x)).coeff n
    rw [coeff_domCongr, coeff_domCongr, coeff_domCongr]
    simp [mul_smul, mul_inv_rev]
  smul_zero σ := map_zero (MonoidAlgebra.domCongr ℤ ℤ (mulEquivOf (A := A) σ))
  smul_add σ x y := map_add (MonoidAlgebra.domCongr ℤ ℤ (mulEquivOf (A := A) σ)) x y
  smul_one σ := map_one (MonoidAlgebra.domCongr ℤ ℤ (mulEquivOf (A := A) σ))
  smul_mul σ x y := map_mul (MonoidAlgebra.domCongr ℤ ℤ (mulEquivOf (A := A) σ)) x y

theorem coeff_smul (σ : G) (x : MonoidAlgebra ℤ A) (n : A) :
    (σ • x).coeff n = x.coeff (σ⁻¹ • n) := by
  show (MonoidAlgebra.domCongr ℤ ℤ (mulEquivOf σ) x).coeff n = _
  rw [coeff_domCongr]
  simp

/-- **Deninger, Theorem 1.4, the step marked `(!)`.**  A group acting with open stabilizers on a
ring acts with open stabilizers on its monoid ring, because an element of the monoid ring has
finite support. -/
theorem stabilizer_isOpen [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace A]
    [DiscreteTopology A] [ContinuousSMul G A] (x : MonoidAlgebra ℤ A) :
    IsOpen (MulAction.stabilizer G x : Set G) := by
  classical
  set S : Subgroup G := ⨅ a ∈ x.coeff.support, MulAction.stabilizer G a with hS
  have hSopen : IsOpen (S : Set G) := by
    rw [hS]
    have : ((⨅ a ∈ x.coeff.support, MulAction.stabilizer G a : Subgroup G) : Set G)
        = ⋂ a ∈ x.coeff.support, (MulAction.stabilizer G a : Set G) := by
      simp [Subgroup.coe_iInf]
    rw [this]
    refine Set.Finite.isOpen_biInter x.coeff.support.finite_toSet (fun a _ => ?_)
    show IsOpen ((MulAction.stabilizer G a : Subgroup G) : Set G)
    have hpre : ((MulAction.stabilizer G a : Subgroup G) : Set G)
        = (fun g : G => g • a) ⁻¹' {a} := rfl
    rw [hpre]
    exact IsOpen.preimage (by fun_prop) (isOpen_discrete {a})
  have hle : S ≤ MulAction.stabilizer G x := by
    intro σ hσ
    have hfix : ∀ a ∈ x.coeff.support, σ • a = a := by
      intro a ha
      have := (Subgroup.mem_iInf.mp hσ) a
      exact (Subgroup.mem_iInf.mp this) ha
    show σ • x = x
    refine MonoidAlgebra.ext (Finsupp.ext fun n => ?_)
    rw [coeff_smul]
    by_cases hn : n ∈ x.coeff.support
    · have hfixn : σ • n = n := hfix n hn
      have hinv : σ⁻¹ • n = n := by rw [inv_smul_eq_iff]; exact hfixn.symm
      rw [hinv]
    · by_cases hn' : σ⁻¹ • n ∈ x.coeff.support
      · have h1 : σ • (σ⁻¹ • n) = σ⁻¹ • n := hfix _ hn'
        rw [smul_inv_smul] at h1
        exact absurd (h1 ▸ hn') hn
      · rw [Finsupp.notMem_support_iff.mp hn, Finsupp.notMem_support_iff.mp hn']
  refine Subgroup.isOpen_of_one_mem_interior _ ?_
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hSopen.mem_nhds (one_mem S)) hle)

/-- The induced action on the monoid ring is continuous for the discrete topologies. -/
scoped instance instContinuousSMul [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace A]
    [DiscreteTopology A] [ContinuousSMul G A]
    [TopologicalSpace (MonoidAlgebra ℤ A)] [DiscreteTopology (MonoidAlgebra ℤ A)] :
    ContinuousSMul G (MonoidAlgebra ℤ A) :=
  continuousSMul_iff_stabilizer_isOpen.mpr (fun x => stabilizer_isOpen x)

variable [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G]
variable [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul G A]
variable [TopologicalSpace (MonoidAlgebra ℤ A)] [DiscreteTopology (MonoidAlgebra ℤ A)]
variable {C : Type*} [Field C]

/-- **Deninger, Theorem 1.4 (`t27n`), second assertion, surjectivity.**  Restriction to the
invariants of the monoid ring is surjective on homomorphisms into an algebraically closed field. -/
theorem restrict_surjective [IsAlgClosed C] :
    Function.Surjective (fun ψ : MonoidAlgebra ℤ A →+* C =>
      ψ.comp (algebraMap (FixedPoints.subring (MonoidAlgebra ℤ A) G) (MonoidAlgebra ℤ A))) :=
  deningerFixedSubring_restrict_surjective

/-- **Deninger, Theorem 1.4 (`t27n`), second assertion, injectivity modulo `G`.** -/
theorem restrict_eq_iff (ψ₁ ψ₂ : MonoidAlgebra ℤ A →+* C) :
    ψ₁.comp (algebraMap (FixedPoints.subring (MonoidAlgebra ℤ A) G) (MonoidAlgebra ℤ A))
        = ψ₂.comp (algebraMap (FixedPoints.subring (MonoidAlgebra ℤ A) G) (MonoidAlgebra ℤ A))
      ↔ ∃ g : G, ∀ x : MonoidAlgebra ℤ A, ψ₂ x = ψ₁ (g • x) :=
  deningerFixedSubring_restrict_eq_iff ψ₁ ψ₂

end DeningerMonoidRing

end RHTower
