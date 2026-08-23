import GaloisForLFunctions.RHTower.DeningerDynSysInvariantPoints
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Invariant.Profinite

/-!
# The stabilizer of a prime surjects onto the automorphisms of its residue field

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), equation (23), which
the source quotes from Bourbaki, *Algèbre commutative* V, §2, no 3, Proposition 6.

Let a profinite group `G` act continuously on a ring `B` with invariant subring `A`, let `Q` be a
prime of `B` lying over `P`, and let `K` and `L` be the fraction fields of `A ⧸ P` and `B ⧸ Q`,
that is the residue fields.  Then

`stabilizer G Q ⟶ Gal (L / K)`

is surjective.  Mathlib has this for the quotients `(B ⧸ Q) / (A ⧸ P)`
(`Ideal.Quotient.stabilizerHom_surjective_of_profinite`) and for the residue fields only when `G`
is finite; the residue-field statement for a profinite group is obtained here by showing that a
`K`-automorphism of `L` restricts to `B ⧸ Q`.

The restriction step is the orbit polynomial `∏_{c ∈ Gb} (X - c)`: its coefficients are invariant,
hence lie in `A`, hence are fixed by every `K`-automorphism of `L`; so such an automorphism sends
a root of the polynomial to a root, and all roots in `L` are images of the orbit of `b`.  The
resulting self-map of `B ⧸ Q` is bijective because the same applies to the inverse automorphism,
and it is a ring homomorphism because `B ⧸ Q ⟶ L` is injective.
-/

namespace RHTower
open MulAction Polynomial

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
variable [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G]
variable [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B]
variable (P : Ideal A) (Q : Ideal B) [Q.IsPrime] [Q.LiesOver P]
variable (K L : Type*) [Field K] [Field L]
  [Algebra (A ⧸ P) K] [Algebra (B ⧸ Q) L]
  [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
  [Algebra K L] [IsScalarTower (A ⧸ P) K L]
variable [instInv : Algebra.IsInvariant A B G]

/-- The composite `B → B ⧸ Q → L` into the residue field of `Q`. -/
noncomputable def deningerResidueHom : B →+* L :=
  (algebraMap (B ⧸ Q) L).comp (Ideal.Quotient.mk Q)

omit [TopologicalSpace B] [DiscreteTopology B] [Q.IsPrime] instInv in
/-- On the image of `A` the residue map factors through `K`. -/
theorem deningerResidueHom_algebraMap (a : A) :
    deningerResidueHom Q L (algebraMap A B a)
      = algebraMap K L (algebraMap (A ⧸ P) K (Ideal.Quotient.mk P a)) := by
  rw [← IsScalarTower.algebraMap_apply (A ⧸ P) K L]
  have h1 : (Ideal.Quotient.mk Q) ((algebraMap A B) a)
      = algebraMap (A ⧸ P) (B ⧸ Q) (Ideal.Quotient.mk P a) := by
    show algebraMap B (B ⧸ Q) (algebraMap A B a) = _
    rw [← IsScalarTower.algebraMap_apply A B (B ⧸ Q),
      IsScalarTower.algebraMap_apply A (A ⧸ P) (B ⧸ Q)]
    rfl
  show algebraMap (B ⧸ Q) L (Ideal.Quotient.mk Q (algebraMap A B a)) = _
  rw [h1, ← IsScalarTower.algebraMap_apply (A ⧸ P) (B ⧸ Q) L]

omit [TopologicalSpace B] [DiscreteTopology B] [Q.IsPrime] instInv in
include P in
/-- A `K`-automorphism of `L` fixes the image of `A`. -/
theorem deningerResidueHom_algEquiv_fixed (σ : L ≃ₐ[K] L) (a : A) :
    σ (deningerResidueHom Q L (algebraMap A B a)) = deningerResidueHom Q L (algebraMap A B a) := by
  rw [deningerResidueHom_algebraMap P Q K L a]
  exact σ.commutes _

omit [SMulCommClass G A B] [TotallyDisconnectedSpace G] [Q.IsPrime] in
include instInv P in
/-- **Deninger, (23), the orbit step.**  A `K`-automorphism of `L` sends the image of `b` to the
image of a point of the `G`-orbit of `b`: the orbit polynomial of `b` has coefficients in `A`,
hence is fixed by the automorphism, and its roots in `L` are exactly the images of the orbit. -/
theorem deningerResidueHom_algEquiv_orbit (σ : L ≃ₐ[K] L) (b : B) :
    ∃ c ∈ MulAction.orbit G b, σ (deningerResidueHom Q L b) = deningerResidueHom Q L c := by
  classical
  obtain ⟨F, hF⟩ := deningerOrbitPoly_lifts (A := A) (G := G) b
  set ψ : B →+* L := deningerResidueHom Q L with hψ
  set f : Polynomial B := deningerOrbitPoly (G := G) b with hf
  have hcomp : ((σ : L →+* L).comp ψ).comp (algebraMap A B) = ψ.comp (algebraMap A B) :=
    RingHom.ext fun a => deningerResidueHom_algEquiv_fixed P Q K L σ a
  have hfix : (f.map ψ).map (σ : L →+* L) = f.map ψ := by
    rw [← hF]
    simp only [Polynomial.map_map]
    exact congrArg (fun h : A →+* L => F.map h) hcomp
  have hzero : (f.map ψ).eval (ψ b) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom, hf, deningerOrbitPoly_eval, map_zero]
  have hstep : (f.map ψ).eval (σ (ψ b)) = 0 := by
    have h2 : ((f.map ψ).map (σ : L →+* L)).eval ((σ : L →+* L) (ψ b)) = 0 := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom, hzero, map_zero]
    rw [hfix] at h2
    exact h2
  have hprod : (f.map ψ).eval (σ (ψ b))
      = ∏ c ∈ deningerOrbitFinset (G := G) b, (σ (ψ b) - ψ c) := by
    simp only [hf, deningerOrbitPoly, Polynomial.map_prod, Polynomial.eval_prod]
    refine Finset.prod_congr rfl fun c _ => ?_
    simp
  rw [hprod] at hstep
  obtain ⟨c, hc, hc0⟩ := Finset.prod_eq_zero_iff.mp hstep
  exact ⟨c, deningerMem_orbitFinset.mp hc, sub_eq_zero.mp hc0⟩

omit [SMulCommClass G A B] [TotallyDisconnectedSpace G] [Q.IsPrime] in
include instInv P in
/-- A `K`-automorphism of `L` maps the image of `B ⧸ Q` into itself. -/
theorem deningerQuotient_mem_range_algEquiv (σ : L ≃ₐ[K] L) (x : B ⧸ Q) :
    ∃ y : B ⧸ Q, σ (algebraMap (B ⧸ Q) L x) = algebraMap (B ⧸ Q) L y := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨c, -, hc⟩ := deningerResidueHom_algEquiv_orbit (G := G) P Q K L σ b
  exact ⟨Ideal.Quotient.mk Q c, hc⟩

omit [SMulCommClass G A B] [TotallyDisconnectedSpace G] [Q.IsPrime] in
include instInv P in
/-- The underlying map of the restriction of a `K`-automorphism of `L` to `B ⧸ Q`. -/
noncomputable def deningerQuotientRestrictFun (σ : L ≃ₐ[K] L) (x : B ⧸ Q) : B ⧸ Q :=
  (deningerQuotient_mem_range_algEquiv (G := G) P Q K L σ x).choose

omit [SMulCommClass G A B] [TotallyDisconnectedSpace G] [Q.IsPrime] in
include instInv P in
/-- The restriction agrees with the automorphism on the image of `B ⧸ Q`. -/
theorem deningerQuotientRestrictFun_spec (σ : L ≃ₐ[K] L) (x : B ⧸ Q) :
    algebraMap (B ⧸ Q) L (deningerQuotientRestrictFun (G := G) P Q K L σ x)
      = σ (algebraMap (B ⧸ Q) L x) :=
  (deningerQuotient_mem_range_algEquiv (G := G) P Q K L σ x).choose_spec.symm

variable [IsFractionRing (A ⧸ P) K] [IsFractionRing (B ⧸ Q) L]

omit [SMulCommClass G A B] [TotallyDisconnectedSpace G] [IsFractionRing (A ⧸ P) K]
  [Q.IsPrime] in
include instInv P in
/-- **Deninger, (23).**  A `K`-automorphism of `L` restricts to an `A ⧸ P`-automorphism of
`B ⧸ Q`. -/
noncomputable def deningerQuotientRestrict (σ : L ≃ₐ[K] L) : (B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q) where
  toFun := deningerQuotientRestrictFun (G := G) P Q K L σ
  invFun := deningerQuotientRestrictFun (G := G) P Q K L σ.symm
  left_inv x := by
    refine IsFractionRing.injective (B ⧸ Q) L ?_
    rw [deningerQuotientRestrictFun_spec, deningerQuotientRestrictFun_spec,
      AlgEquiv.symm_apply_apply]
  right_inv x := by
    refine IsFractionRing.injective (B ⧸ Q) L ?_
    rw [deningerQuotientRestrictFun_spec, deningerQuotientRestrictFun_spec,
      AlgEquiv.apply_symm_apply]
  map_mul' x y := by
    refine IsFractionRing.injective (B ⧸ Q) L ?_
    rw [map_mul, deningerQuotientRestrictFun_spec, deningerQuotientRestrictFun_spec,
      deningerQuotientRestrictFun_spec, map_mul, map_mul]
  map_add' x y := by
    refine IsFractionRing.injective (B ⧸ Q) L ?_
    rw [map_add, deningerQuotientRestrictFun_spec, deningerQuotientRestrictFun_spec,
      deningerQuotientRestrictFun_spec, map_add, map_add]
  commutes' a := by
    refine IsFractionRing.injective (B ⧸ Q) L ?_
    rw [deningerQuotientRestrictFun_spec, ← IsScalarTower.algebraMap_apply (A ⧸ P) (B ⧸ Q) L,
      IsScalarTower.algebraMap_apply (A ⧸ P) K L]
    exact σ.commutes _

omit [SMulCommClass G A B] [TotallyDisconnectedSpace G] [IsFractionRing (A ⧸ P) K]
  [Q.IsPrime] in
include instInv P in
/-- The restriction agrees with the automorphism on the image of `B ⧸ Q`. -/
theorem deningerQuotientRestrict_apply (σ : L ≃ₐ[K] L) (x : B ⧸ Q) :
    algebraMap (B ⧸ Q) L (deningerQuotientRestrict (G := G) P Q K L σ x)
      = σ (algebraMap (B ⧸ Q) L x) :=
  deningerQuotientRestrictFun_spec (G := G) P Q K L σ x

omit [SMulCommClass G A B] [TotallyDisconnectedSpace G] [Q.IsPrime] in
include instInv P in
/-- The restriction of a `K`-automorphism of `L` to `B ⧸ Q` extends back to it. -/
theorem deningerFieldEquivOfAlgEquivHom_quotientRestrict (σ : L ≃ₐ[K] L) :
    IsFractionRing.fieldEquivOfAlgEquivHom K L
      (deningerQuotientRestrict (G := G) P Q K L σ) = σ := by
  have h : ((IsFractionRing.fieldEquivOfAlgEquivHom K L
        (deningerQuotientRestrict (G := G) P Q K L σ) : L ≃ₐ[K] L) : L →+* L).comp
        (algebraMap (B ⧸ Q) L)
      = ((σ : L ≃ₐ[K] L) : L →+* L).comp (algebraMap (B ⧸ Q) L) := by
    refine RingHom.ext fun x => ?_
    show IsFractionRing.fieldEquivOfAlgEquivHom K L
      (deningerQuotientRestrict (G := G) P Q K L σ) (algebraMap (B ⧸ Q) L x) = σ _
    rw [IsFractionRing.fieldEquivOfAlgEquivHom]
    show IsFractionRing.fieldEquivOfAlgEquiv K L L
      (deningerQuotientRestrict (G := G) P Q K L σ) (algebraMap (B ⧸ Q) L x) = σ _
    rw [IsFractionRing.fieldEquivOfAlgEquiv_algebraMap]
    exact deningerQuotientRestrict_apply P Q K L σ x
  have h2 := IsLocalization.ringHom_ext (nonZeroDivisors (B ⧸ Q)) h
  exact AlgEquiv.ext fun z => RingHom.congr_fun h2 z

include instInv P in
/-- **Deninger, (23), for a profinite group.**  The stabilizer of a prime `Q` of `B` surjects onto
the automorphism group of the residue field of `Q` over the residue field of the prime of `A`
below it. -/
theorem deningerStabilizerHom_surjective :
    Function.Surjective (IsFractionRing.stabilizerHom G P Q K L) := by
  intro σ
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := G) P Q
    (deningerQuotientRestrict (G := G) P Q K L σ)
  refine ⟨g, ?_⟩
  show IsFractionRing.fieldEquivOfAlgEquivHom K L (Ideal.Quotient.stabilizerHom Q P G g) = σ
  rw [hg]
  exact deningerFieldEquivOfAlgEquivHom_quotientRestrict P Q K L σ

end RHTower
