import GaloisForLFunctions.HTGeometry.DerivationPrescription
import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# The jet field of a function field

Let `F/C` be a field extension of characteristic zero with a transcendence basis
`t₁,…,t_d`.  The function field of the infinite jet space of a variety with function field `F` is

`K = F(y_(i,k) : i < d, k ≥ 0)`,  `y_(i,k) = t_i^(k+1)`,

with the unique derivation `δ` that kills `C`, sends `t_i` to `y_(i,0)` and advances every
`y_(i,k)` to `y_(i,k+1)`.  On `F` it is `δa = Σ_i (∂a/∂t_i) y_(i,0)`, where the partial derivations
`∂/∂t_i` exist because `F` is algebraic, hence separable, over `C(t)`.

The derivation is built on the polynomial ring `F[y]` as the second coordinate of the graph
homomorphism `F[y] → K ⊕ εK` and extended to the fraction field.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable (F : Type*) [Field F] (d : ℕ)

/-- The polynomial ring on the positive jets `y_(i,k) = t_i^(k+1)`. -/
abbrev FunctionJetPoly := MvPolynomial (Fin d × ℕ) F

/-- The jet field `F(t_i^(k+1))`. -/
abbrev FunctionJetField := FractionRing (FunctionJetPoly F d)

variable {F d}

/-- The positive jet `y_(i,k) = t_i^(k+1)`. -/
def functionJet (p : Fin d × ℕ) : FunctionJetField F d :=
  algebraMap (FunctionJetPoly F d) (FunctionJetField F d) (X p)

variable {C : Type*} [Field C] [CharZero C] [Algebra C F]

/-- The partial derivation `∂/∂t_i` of `F` along a transcendence basis. -/
def jetPartial {t : Fin d → F} (ht : IsTranscendenceBasis C t) (i : Fin d) :
    Derivation C F F :=
  Classical.choose (exists_derivation_prescribed ht.1 (fun j => if j = i then (1 : C) else 0))

theorem jetPartial_apply_basis {t : Fin d → F} (ht : IsTranscendenceBasis C t) (i j : Fin d) :
    jetPartial ht i (t j) = if j = i then 1 else 0 := by
  have h := Classical.choose_spec
    (exists_derivation_prescribed ht.1 (fun j => if j = i then (1 : C) else 0)) j
  rw [jetPartial, h]
  split_ifs <;> simp

/-- The derivation of `F` into the jet field: `δa = Σ_i (∂a/∂t_i) y_(i,0)`. -/
def jetBaseDerivation {t : Fin d → F} (ht : IsTranscendenceBasis C t) :
    Derivation C F (FunctionJetField F d) :=
  Derivation.mk'
    { toFun := fun a => ∑ i, (functionJet (i, 0) : FunctionJetField F d) *
        algebraMap F (FunctionJetField F d) (jetPartial ht i a)
      map_add' := fun a b => by
        simp only [map_add, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Derivation.map_smul, Algebra.smul_def c ((jetPartial ht i) a), map_mul,
          Algebra.smul_def c, ← IsScalarTower.algebraMap_apply C F (FunctionJetField F d)]
        ring }
    (fun a b => by
      change ∑ i, (functionJet (i, 0) : FunctionJetField F d) *
          algebraMap F (FunctionJetField F d) (jetPartial ht i (a * b)) =
        a • ∑ i, (functionJet (i, 0) : FunctionJetField F d) *
          algebraMap F (FunctionJetField F d) (jetPartial ht i b) +
        b • ∑ i, (functionJet (i, 0) : FunctionJetField F d) *
          algebraMap F (FunctionJetField F d) (jetPartial ht i a)
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, Algebra.smul_def, mul_add,
        Finset.sum_add_distrib]
      rw [Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring)

theorem jetBaseDerivation_apply {t : Fin d → F} (ht : IsTranscendenceBasis C t) (a : F) :
    jetBaseDerivation ht a =
      ∑ i, functionJet (i, 0) * algebraMap F (FunctionJetField F d) (jetPartial ht i a) := rfl

/-- The graph of the jet derivation on the polynomial ring. -/
def jetPolyGraph {t : Fin d → F} (ht : IsTranscendenceBasis C t) :
    FunctionJetPoly F d →+* TrivSqZeroExt (FunctionJetField F d) (FunctionJetField F d) :=
  eval₂Hom (derivationGraphAlgHom (jetBaseDerivation ht)).toRingHom
    (fun p => TrivSqZeroExt.inl (functionJet p) + TrivSqZeroExt.inr (functionJet (p.1, p.2 + 1)))

theorem jetPolyGraph_fst {t : Fin d → F} (ht : IsTranscendenceBasis C t) (P : FunctionJetPoly F d) :
    (jetPolyGraph ht P).fst = algebraMap (FunctionJetPoly F d) (FunctionJetField F d) P := by
  have h : (TrivSqZeroExt.fstHom (FunctionJetField F d) (FunctionJetField F d)
      (FunctionJetField F d)).toRingHom.comp (jetPolyGraph ht) =
      algebraMap (FunctionJetPoly F d) (FunctionJetField F d) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [jetPolyGraph, IsScalarTower.algebraMap_apply F (FunctionJetPoly F d)
        (FunctionJetField F d)]
    · intro p
      simp [jetPolyGraph, functionJet]
  exact RingHom.congr_fun h P

/-- The jet derivation on the polynomial ring. -/
def jetPolyDerivation {t : Fin d → F} (ht : IsTranscendenceBasis C t) :
    Derivation C (FunctionJetPoly F d) (FunctionJetField F d) :=
  Derivation.mk'
    { toFun := fun P => (jetPolyGraph ht P).snd
      map_add' := fun P Q => by rw [map_add, TrivSqZeroExt.snd_add]
      map_smul' := fun c P => by
        rw [RingHom.id_apply, Algebra.smul_def, map_mul, TrivSqZeroExt.snd_mul, jetPolyGraph_fst,
          jetPolyGraph_fst]
        have hc : jetPolyGraph ht (algebraMap C (FunctionJetPoly F d) c) =
            TrivSqZeroExt.inl (algebraMap C (FunctionJetField F d) c) := by
          rw [IsScalarTower.algebraMap_apply C F (FunctionJetPoly F d), MvPolynomial.algebraMap_eq,
            jetPolyGraph, eval₂Hom_C]
          change derivationGraphAlgHom (jetBaseDerivation ht) (algebraMap C F c) = _
          rw [AlgHom.commutes, TrivSqZeroExt.algebraMap_eq_inl']
        rw [hc, TrivSqZeroExt.snd_inl, smul_zero, add_zero, smul_eq_mul, Algebra.smul_def,
          ← IsScalarTower.algebraMap_apply] }
    (fun P Q => by
      change (jetPolyGraph ht (P * Q)).snd = P • (jetPolyGraph ht Q).snd +
        Q • (jetPolyGraph ht P).snd
      rw [map_mul, TrivSqZeroExt.snd_mul, jetPolyGraph_fst, jetPolyGraph_fst]
      simp only [smul_eq_mul, Algebra.smul_def, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op]
      ring)

theorem jetPolyDerivation_apply {t : Fin d → F} (ht : IsTranscendenceBasis C t)
    (P : FunctionJetPoly F d) : jetPolyDerivation ht P = (jetPolyGraph ht P).snd := rfl

/-- **The jet derivation** of the jet field. -/
def jetFieldDerivation {t : Fin d → F} (ht : IsTranscendenceBasis C t) :
    Derivation C (FunctionJetField F d) (FunctionJetField F d) :=
  fractionRingDerivation (jetPolyDerivation ht)

theorem jetFieldDerivation_algebraMap_poly {t : Fin d → F} (ht : IsTranscendenceBasis C t)
    (P : FunctionJetPoly F d) :
    jetFieldDerivation ht (algebraMap (FunctionJetPoly F d) (FunctionJetField F d) P) =
      jetPolyDerivation ht P :=
  fractionRingDerivation_algebraMap _ P

/-- On `F` the jet derivation is `δa = Σ_i (∂a/∂t_i) y_(i,0)`. -/
theorem jetFieldDerivation_algebraMap {t : Fin d → F} (ht : IsTranscendenceBasis C t) (a : F) :
    jetFieldDerivation ht (algebraMap F (FunctionJetField F d) a) =
      ∑ i, functionJet (i, 0) * algebraMap F (FunctionJetField F d) (jetPartial ht i a) := by
  rw [IsScalarTower.algebraMap_apply F (FunctionJetPoly F d) (FunctionJetField F d),
    jetFieldDerivation_algebraMap_poly, jetPolyDerivation_apply, MvPolynomial.algebraMap_eq,
    jetPolyGraph, eval₂Hom_C]
  exact jetBaseDerivation_apply ht a

/-- The jet derivation sends the basis element `t_i` to its first jet. -/
theorem jetFieldDerivation_basis {t : Fin d → F} (ht : IsTranscendenceBasis C t) (i : Fin d) :
    jetFieldDerivation ht (algebraMap F (FunctionJetField F d) (t i)) = functionJet (i, 0) := by
  rw [jetFieldDerivation_algebraMap]
  simp [jetPartial_apply_basis]

/-- The jet derivation advances every jet. -/
theorem jetFieldDerivation_functionJet {t : Fin d → F} (ht : IsTranscendenceBasis C t)
    (p : Fin d × ℕ) : jetFieldDerivation ht (functionJet p) = functionJet (p.1, p.2 + 1) := by
  rw [functionJet, jetFieldDerivation_algebraMap_poly, jetPolyDerivation_apply, jetPolyGraph,
    eval₂Hom_X']
  simp

end

end GaloisForLFunctions.HTGeometry
