import GaloisForLFunctions.RHTower.DeningerDynSysInvariantPoints
import GaloisForLFunctions.RHTower.DeningerRationalWittCanonicalMultiplication
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# The induced action on the rational Witt ring

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Theorem 1.4 (`t27n`),
second assertion, on the actual rational Witt ring:

`Hom (W_rat (A), C) / G ≅ Hom (W_rat (A) ^ G, C)`

for a ring `A` with a continuous action of a profinite group `G` and an algebraically closed
field `C`.

The step the source flags with an exclamation mark — that `G` acts with finite orbits on
`W_rat (A)` as soon as it does on `A` — is `stabilizer_isOpen`: a rational Witt vector is a
normalized fraction `P / Q` of polynomials, so it is determined by finitely many elements of `A`,
and its stabilizer contains the (open) finite intersection of their stabilizers.

The ring `W_rat (A)` and its functoriality are the corpus's
`DeningerCanonicalRationalWittRing` and `deningerCanonicalRationalWittMap`; the action is a
`scoped instance` so that it does not interfere with other uses of that ring.
-/

namespace RHTower

namespace DeningerWittRing

open MulAction

variable {A : Type*} [CommRing A] {G : Type*} [Group G] [MulSemiringAction G A]

/-- The action of `G` on the rational Witt ring induced by a semiring action on `A`. -/
noncomputable scoped instance instMulSemiringAction :
    MulSemiringAction G (DeningerCanonicalRationalWittRing A) where
  smul σ w := deningerCanonicalRationalWittMap (MulSemiringAction.toRingHom G A σ) w
  one_smul w := by
    have hid : MulSemiringAction.toRingHom G A (1 : G) = RingHom.id A := by
      ext a
      exact one_smul G a
    show deningerCanonicalRationalWittMapFun
        (MulSemiringAction.toRingHom G A (1 : G)) w = w
    rw [hid]
    apply DeningerCanonicalRationalWittRing.ext
    show Additive.ofMul (deningerRationalWittAdditiveMap (RingHom.id A)
      (Additive.toMul w.additiveVal)) = w.additiveVal
    rw [deningerRationalWittAdditiveMap_id]
    rfl
  mul_smul σ τ w := by
    have hcomp : MulSemiringAction.toRingHom G A (σ * τ)
        = (MulSemiringAction.toRingHom G A σ).comp (MulSemiringAction.toRingHom G A τ) := by
      ext a
      exact mul_smul σ τ a
    show deningerCanonicalRationalWittMapFun (MulSemiringAction.toRingHom G A (σ * τ)) w
      = deningerCanonicalRationalWittMapFun (MulSemiringAction.toRingHom G A σ)
          (deningerCanonicalRationalWittMapFun (MulSemiringAction.toRingHom G A τ) w)
    rw [hcomp]
    apply DeningerCanonicalRationalWittRing.ext
    show Additive.ofMul (deningerRationalWittAdditiveMap
        ((MulSemiringAction.toRingHom G A σ).comp (MulSemiringAction.toRingHom G A τ))
        (Additive.toMul w.additiveVal))
      = Additive.ofMul (deningerRationalWittAdditiveMap (MulSemiringAction.toRingHom G A σ)
          (deningerRationalWittAdditiveMap (MulSemiringAction.toRingHom G A τ)
            (Additive.toMul w.additiveVal)))
    rw [deningerRationalWittAdditiveMap_comp]
    rfl
  smul_zero σ := map_zero (deningerCanonicalRationalWittMap (MulSemiringAction.toRingHom G A σ))
  smul_add σ x y :=
    map_add (deningerCanonicalRationalWittMap (MulSemiringAction.toRingHom G A σ)) x y
  smul_one σ := map_one (deningerCanonicalRationalWittMap (MulSemiringAction.toRingHom G A σ))
  smul_mul σ x y :=
    map_mul (deningerCanonicalRationalWittMap (MulSemiringAction.toRingHom G A σ)) x y

theorem smul_def (σ : G) (w : DeningerCanonicalRationalWittRing A) :
    σ • w = deningerCanonicalRationalWittMap (MulSemiringAction.toRingHom G A σ) w := rfl

/-- If `σ` fixes every coefficient of a polynomial, it fixes the polynomial. -/
theorem map_eq_self_of_coeff_fixed (σ : G) (P : Polynomial A)
    (h : ∀ n, σ • P.coeff n = P.coeff n) :
    P.map (MulSemiringAction.toRingHom G A σ) = P := by
  ext n
  rw [Polynomial.coeff_map]
  exact h n

/-- **Deninger, Theorem 1.4, the step marked `(!)`, for the rational Witt ring.**  A group acting
with open stabilizers on `A` acts with open stabilizers on `W_rat (A)`: a rational Witt vector is
a normalized fraction of two polynomials, hence determined by finitely many elements of `A`. -/
theorem stabilizer_isOpen [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace A]
    [DiscreteTopology A] [ContinuousSMul G A] (w : DeningerCanonicalRationalWittRing A) :
    IsOpen (MulAction.stabilizer G w : Set G) := by
  classical
  obtain ⟨P, Q, hQmem, hP0, hQ0, hval⟩ :=
    deningerRationalWittAdditive_exists_normalized_fraction A (Additive.toMul w.additiveVal)
  set T : Finset ℕ := P.support ∪ Q.support with hT
  set S : Subgroup G :=
    (⨅ n ∈ T, MulAction.stabilizer G (P.coeff n)) ⊓
      (⨅ n ∈ T, MulAction.stabilizer G (Q.coeff n)) with hS
  have hstab : ∀ a : A, IsOpen ((MulAction.stabilizer G a : Subgroup G) : Set G) := by
    intro a
    have hpre : ((MulAction.stabilizer G a : Subgroup G) : Set G)
        = (fun g : G => g • a) ⁻¹' {a} := rfl
    rw [hpre]
    exact IsOpen.preimage (by fun_prop) (isOpen_discrete {a})
  have hSopen : IsOpen (S : Set G) := by
    have h1 : ((⨅ n ∈ T, MulAction.stabilizer G (P.coeff n) : Subgroup G) : Set G)
        = ⋂ n ∈ T, ((MulAction.stabilizer G (P.coeff n) : Subgroup G) : Set G) := by
      simp [Subgroup.coe_iInf]
    have h2 : ((⨅ n ∈ T, MulAction.stabilizer G (Q.coeff n) : Subgroup G) : Set G)
        = ⋂ n ∈ T, ((MulAction.stabilizer G (Q.coeff n) : Subgroup G) : Set G) := by
      simp [Subgroup.coe_iInf]
    rw [hS, Subgroup.coe_inf, h1, h2]
    exact (Set.Finite.isOpen_biInter T.finite_toSet (fun n _ => hstab _)).inter
      (Set.Finite.isOpen_biInter T.finite_toSet (fun n _ => hstab _))
  have hle : S ≤ MulAction.stabilizer G w := by
    intro σ hσ
    obtain ⟨hσP, hσQ⟩ := hσ
    have hPfix : ∀ n, σ • P.coeff n = P.coeff n := by
      intro n
      by_cases hn : n ∈ T
      · exact (Subgroup.mem_iInf.mp ((Subgroup.mem_iInf.mp hσP) n)) hn
      · have hnP : P.coeff n = 0 := by
          rw [← Polynomial.notMem_support_iff]
          intro hc
          exact hn (Finset.mem_union_left _ hc)
        rw [hnP, smul_zero]
    have hQfix : ∀ n, σ • Q.coeff n = Q.coeff n := by
      intro n
      by_cases hn : n ∈ T
      · exact (Subgroup.mem_iInf.mp ((Subgroup.mem_iInf.mp hσQ) n)) hn
      · have hnQ : Q.coeff n = 0 := by
          rw [← Polynomial.notMem_support_iff]
          intro hc
          exact hn (Finset.mem_union_right _ hc)
        rw [hnQ, smul_zero]
    show σ • w = w
    rw [smul_def]
    apply DeningerCanonicalRationalWittRing.ext
    show Additive.ofMul (deningerRationalWittAdditiveMap (MulSemiringAction.toRingHom G A σ)
      (Additive.toMul w.additiveVal)) = w.additiveVal
    apply Subtype.ext
    apply Units.ext
    show deningerRationalWittLocalizationMap (MulSemiringAction.toRingHom G A σ)
        ((Additive.toMul w.additiveVal).1 : DeningerRationalWittLocalization A)
      = ((Additive.toMul w.additiveVal).1 : DeningerRationalWittLocalization A)
    rw [hval, deningerRationalWittLocalizationMap, IsLocalization.map_mk']
    congr 1
    · exact map_eq_self_of_coeff_fixed σ P hPfix
    · apply Subtype.ext
      exact map_eq_self_of_coeff_fixed σ Q hQfix
  refine Subgroup.isOpen_of_one_mem_interior _ ?_
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hSopen.mem_nhds (one_mem S)) hle)

/-- The induced action on the rational Witt ring is continuous for the discrete topologies. -/
scoped instance instContinuousSMul [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace A]
    [DiscreteTopology A] [ContinuousSMul G A]
    [TopologicalSpace (DeningerCanonicalRationalWittRing A)]
    [DiscreteTopology (DeningerCanonicalRationalWittRing A)] :
    ContinuousSMul G (DeningerCanonicalRationalWittRing A) :=
  continuousSMul_iff_stabilizer_isOpen.mpr (fun w => stabilizer_isOpen w)

section Points

variable [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G]
variable [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul G A]
variable [TopologicalSpace (DeningerCanonicalRationalWittRing A)]
variable [DiscreteTopology (DeningerCanonicalRationalWittRing A)]
variable {C : Type*} [Field C]

/-- **Deninger, Theorem 1.4 (`t27n`), second assertion, surjectivity.**  Restriction to the
`G`-invariants of `W_rat (A)` is surjective on homomorphisms into an algebraically closed
field. -/
theorem restrict_surjective [IsAlgClosed C] :
    Function.Surjective (fun ψ : DeningerCanonicalRationalWittRing A →+* C =>
      ψ.comp (algebraMap (FixedPoints.subring (DeningerCanonicalRationalWittRing A) G)
        (DeningerCanonicalRationalWittRing A))) :=
  deningerFixedSubring_restrict_surjective

/-- **Deninger, Theorem 1.4 (`t27n`), second assertion, injectivity modulo `G`.** -/
theorem restrict_eq_iff (ψ₁ ψ₂ : DeningerCanonicalRationalWittRing A →+* C) :
    ψ₁.comp (algebraMap (FixedPoints.subring (DeningerCanonicalRationalWittRing A) G)
          (DeningerCanonicalRationalWittRing A))
        = ψ₂.comp (algebraMap (FixedPoints.subring (DeningerCanonicalRationalWittRing A) G)
          (DeningerCanonicalRationalWittRing A))
      ↔ ∃ g : G, ∀ w : DeningerCanonicalRationalWittRing A, ψ₂ w = ψ₁ (g • w) :=
  deningerFixedSubring_restrict_eq_iff ψ₁ ψ₂

end Points

end DeningerWittRing

end RHTower
