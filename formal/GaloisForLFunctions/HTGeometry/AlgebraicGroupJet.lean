import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Algebraic-group jets over truncated arcs

This file constructs finite algebraic jets without choosing affine coordinates on the target.
For a commutative ring `R`, the order-`n` arc algebra is

`R[t] / (t^(n + 1))`.

An order-`n` jet of a scheme `G` over `K`, valued in a `K`-algebra `R`, is a morphism over
`Spec K` from the spectrum of that arc algebra to `G`.  Consequently the definition applies to
non-affine group schemes, including abelian varieties.  Group structure comes from the Yoneda
group of points of a group object.

The constant section, evaluation at `t = 0`, and restriction from order `m` to order `n ≤ m` are
constructed as actual scheme morphisms and proved compatible.  No representability, smoothness,
or coordinate-triviality conclusion is included in the definitions.
-/

open CategoryTheory Polynomial
open AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable (R : Type u) [CommRing R]

/-- The ideal `(t^(n + 1))` defining order-`n` truncated arcs. -/
def truncatedArcIdeal (n : ℕ) : Ideal R[X] :=
  Ideal.span {X ^ (n + 1)}

/-- The order-`n` truncated arc algebra `R[t] / (t^(n + 1))`. -/
abbrev TruncatedArcAlgebra (n : ℕ) := R[X] ⧸ truncatedArcIdeal R n

/-- Evaluation of a truncated arc at `t = 0`. -/
def truncatedArcAugmentation (n : ℕ) : TruncatedArcAlgebra R n →ₐ[R] R :=
  Ideal.Quotient.liftₐ (truncatedArcIdeal R n) (Polynomial.aeval (R := R) 0) (by
    intro p hp
    rw [truncatedArcIdeal, Ideal.mem_span_singleton'] at hp
    obtain ⟨q, rfl⟩ := hp
    simp)

@[simp]
theorem truncatedArcAugmentation_mk (n : ℕ) (p : R[X]) :
    truncatedArcAugmentation R n (Ideal.Quotient.mk (truncatedArcIdeal R n) p) = p.eval 0 := by
  rfl

@[simp]
theorem truncatedArcAugmentation_algebraMap (n : ℕ) (r : R) :
    truncatedArcAugmentation R n (algebraMap R (TruncatedArcAlgebra R n) r) = r := by
  simp [truncatedArcAugmentation]

/-- The defining ideals are antitone in jet order. -/
theorem truncatedArcIdeal_antitone {n m : ℕ} (h : n ≤ m) :
    truncatedArcIdeal R m ≤ truncatedArcIdeal R n := by
  rw [truncatedArcIdeal, truncatedArcIdeal]
  apply Ideal.span_le.2
  intro p hp
  simp only [Set.mem_singleton_iff] at hp
  subst p
  exact Ideal.mem_span_singleton'.2 ⟨X ^ (m - n), by
    rw [← pow_add]
    congr 1
    omega⟩

/-- Restriction of truncated arcs from order `m` to order `n ≤ m`. -/
def truncateArcAlgHom {n m : ℕ} (h : n ≤ m) :
    TruncatedArcAlgebra R m →ₐ[R] TruncatedArcAlgebra R n :=
  Ideal.Quotient.factorₐ R (truncatedArcIdeal_antitone R h)

@[simp]
theorem truncateArcAlgHom_mk {n m : ℕ} (h : n ≤ m) (p : R[X]) :
    truncateArcAlgHom R h (Ideal.Quotient.mk (truncatedArcIdeal R m) p) =
      Ideal.Quotient.mk (truncatedArcIdeal R n) p := by
  rfl

@[simp]
theorem truncatedArcAugmentation_comp_truncateArcAlgHom {n m : ℕ} (h : n ≤ m) :
    (truncatedArcAugmentation R n).comp (truncateArcAlgHom R h) =
      truncatedArcAugmentation R m := by
  apply Ideal.Quotient.algHom_ext R
  ext
  simp

variable {K : Type u} [CommRing K]
variable {R} [Algebra K R]

/-- The functor-of-points source `Spec R` over `Spec K`. -/
def algebraicPointSource : Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K R)))

/-- The order-`n` truncated-arc source over `Spec K`. -/
def algebraicJetSource (n : ℕ) : Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom <|
    (algebraMap R (TruncatedArcAlgebra R n)).comp (algebraMap K R)))

/-- The scheme morphism which turns an `R`-point into a constant order-`n` jet. -/
def constantJetSourceHom (n : ℕ) :
    algebraicJetSource (K := K) (R := R) n ⟶ algebraicPointSource (K := K) (R := R) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R (TruncatedArcAlgebra R n)))) (by
    change Spec.map (CommRingCat.ofHom (algebraMap R (TruncatedArcAlgebra R n))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K R)) =
        Spec.map (CommRingCat.ofHom
          ((algebraMap R (TruncatedArcAlgebra R n)).comp (algebraMap K R)))
    rw [← Spec.map_comp, Spec.map_inj]
    ext r
    simp)

/-- The scheme morphism induced by evaluation of an order-`n` jet at `t = 0`. -/
def evaluateJetSourceHom (n : ℕ) :
    algebraicPointSource (K := K) (R := R) ⟶ algebraicJetSource (K := K) (R := R) n :=
  Over.homMk (Spec.map (CommRingCat.ofHom (truncatedArcAugmentation R n).toRingHom)) (by
    change Spec.map (CommRingCat.ofHom (truncatedArcAugmentation R n).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        ((algebraMap R (TruncatedArcAlgebra R n)).comp (algebraMap K R))) =
        Spec.map (CommRingCat.ofHom (algebraMap K R))
    rw [← Spec.map_comp, Spec.map_inj]
    ext r
    simp [truncatedArcAugmentation])

/-- The source morphism which restricts an order-`m` jet to order `n ≤ m`. -/
def truncateJetSourceHom {n m : ℕ} (h : n ≤ m) :
    algebraicJetSource (K := K) (R := R) n ⟶ algebraicJetSource (K := K) (R := R) m :=
  Over.homMk (Spec.map (CommRingCat.ofHom (truncateArcAlgHom R h).toRingHom)) (by
    change Spec.map (CommRingCat.ofHom (truncateArcAlgHom R h).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        ((algebraMap R (TruncatedArcAlgebra R m)).comp (algebraMap K R))) =
        Spec.map (CommRingCat.ofHom
          ((algebraMap R (TruncatedArcAlgebra R n)).comp (algebraMap K R)))
    rw [← Spec.map_comp, Spec.map_inj]
    ext r
    simp)

/-- Evaluating a constant jet recovers its point. -/
theorem evaluateJetSourceHom_comp_constantJetSourceHom (n : ℕ) :
    evaluateJetSourceHom (K := K) (R := R) n ≫
      constantJetSourceHom (K := K) (R := R) n = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (truncatedArcAugmentation R n).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (TruncatedArcAlgebra R n))) =
      𝟙 (Spec (.of R))
  rw [← Spec.map_comp, ← Spec.map_id, Spec.map_inj]
  ext r
  simp [truncatedArcAugmentation]

/-- Restriction of a constant jet is constant. -/
theorem truncateJetSourceHom_comp_constantJetSourceHom {n m : ℕ} (h : n ≤ m) :
    truncateJetSourceHom (K := K) (R := R) h ≫
      constantJetSourceHom (K := K) (R := R) m =
        constantJetSourceHom (K := K) (R := R) n := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (truncateArcAlgHom R h).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (TruncatedArcAlgebra R m))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (TruncatedArcAlgebra R n)))
  rw [← Spec.map_comp, Spec.map_inj, ← CommRingCat.ofHom_comp]
  apply congrArg CommRingCat.ofHom
  ext r
  exact (truncateArcAlgHom R h).commutes r

variable (G : Over (Spec (.of K))) [GrpObj G]

/-- `R`-valued points of a `K`-scheme. -/
abbrev AlgebraicPoint := algebraicPointSource (K := K) (R := R) ⟶ G

/-- Order-`n`, `R`-valued algebraic jets of a `K`-scheme. -/
abbrev AlgebraicJetPoint (n : ℕ) := algebraicJetSource (K := K) (R := R) n ⟶ G

/-- Constant jets form a group homomorphism on the points of a group scheme. -/
def constantJet (n : ℕ) :
    AlgebraicPoint (K := K) (R := R) G →* AlgebraicJetPoint (K := K) (R := R) G n where
  toFun p := constantJetSourceHom (K := K) (R := R) n ≫ p
  map_one' := MonObj.comp_one _
  map_mul' p q := MonObj.comp_mul _ p q

/-- Evaluation at `t = 0` is a group homomorphism on algebraic jets. -/
def evaluateJet (n : ℕ) :
    AlgebraicJetPoint (K := K) (R := R) G n →* AlgebraicPoint (K := K) (R := R) G where
  toFun p := evaluateJetSourceHom (K := K) (R := R) n ≫ p
  map_one' := MonObj.comp_one _
  map_mul' p q := MonObj.comp_mul _ p q

/-- Restriction in jet order is a group homomorphism. -/
def truncateJet {n m : ℕ} (h : n ≤ m) :
    AlgebraicJetPoint (K := K) (R := R) G m →* AlgebraicJetPoint (K := K) (R := R) G n where
  toFun p := truncateJetSourceHom (K := K) (R := R) h ≫ p
  map_one' := MonObj.comp_one _
  map_mul' p q := MonObj.comp_mul _ p q

/-- Evaluation is a left inverse to the constant-jet section. -/
theorem evaluateJet_comp_constantJet (n : ℕ) :
    (evaluateJet (K := K) (R := R) G n).comp (constantJet (K := K) (R := R) G n) =
      MonoidHom.id _ := by
  apply MonoidHom.ext
  intro p
  change evaluateJetSourceHom (K := K) (R := R) n ≫
    constantJetSourceHom (K := K) (R := R) n ≫ p = p
  rw [← Category.assoc, evaluateJetSourceHom_comp_constantJetSourceHom, Category.id_comp]

/-- Jet evaluation commutes with restriction in order. -/
theorem evaluateJet_truncateJet {n m : ℕ} (h : n ≤ m) :
    (evaluateJet (K := K) (R := R) G n).comp (truncateJet (K := K) (R := R) G h) =
      evaluateJet (K := K) (R := R) G m := by
  apply MonoidHom.ext
  intro p
  change evaluateJetSourceHom (K := K) (R := R) n ≫
    truncateJetSourceHom (K := K) (R := R) h ≫ p =
      evaluateJetSourceHom (K := K) (R := R) m ≫ p
  have hs : evaluateJetSourceHom (K := K) (R := R) n ≫
      truncateJetSourceHom (K := K) (R := R) h =
        evaluateJetSourceHom (K := K) (R := R) m := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (truncatedArcAugmentation R n).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (truncateArcAlgHom R h).toRingHom) =
        Spec.map (CommRingCat.ofHom (truncatedArcAugmentation R m).toRingHom)
    rw [← Spec.map_comp, Spec.map_inj, ← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom
      (congrArg AlgHom.toRingHom (truncatedArcAugmentation_comp_truncateArcAlgHom R h))
  rw [← Category.assoc, hs]

/-- Restriction in order commutes with the constant-jet section. -/
theorem truncateJet_constantJet {n m : ℕ} (h : n ≤ m) :
    (truncateJet (K := K) (R := R) G h).comp (constantJet (K := K) (R := R) G m) =
      constantJet (K := K) (R := R) G n := by
  apply MonoidHom.ext
  intro p
  change truncateJetSourceHom (K := K) (R := R) h ≫
    constantJetSourceHom (K := K) (R := R) m ≫ p =
      constantJetSourceHom (K := K) (R := R) n ≫ p
  rw [← Category.assoc, truncateJetSourceHom_comp_constantJetSourceHom]

variable {H : Over (Spec (.of K))} [GrpObj H]

/-- A group-scheme morphism acts on every finite order of the jet tower. -/
def mapAlgebraicJet (n : ℕ) (f : G ⟶ H) [IsMonHom f] :
    AlgebraicJetPoint (K := K) (R := R) G n →*
      AlgebraicJetPoint (K := K) (R := R) H n where
  toFun p := p ≫ f
  map_one' := MonObj.one_comp f
  map_mul' p q := MonObj.mul_comp p q f

end

end GaloisForLFunctions.HTGeometry
