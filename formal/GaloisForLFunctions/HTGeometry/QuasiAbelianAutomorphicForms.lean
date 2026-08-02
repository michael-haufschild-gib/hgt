import GaloisForLFunctions.HTGeometry.MultivariateMultiIndexJet

/-!
# Automorphic factors and their finite jet packets

This file supplies the literal section space needed by the torusless quasi-Abelian fixed-factor
theorem.  A factor is a nowhere-vanishing line-entire cocycle for a discrete additive subgroup of
`ℂ^d`.  Its automorphic forms are the line-entire functions satisfying Abe's transformation law

`f (x + γ) = ψ γ x * f x`.

The automorphic-form locus is a closed complex linear subspace of the compact-open entire-source
space.  It is therefore completely metrizable and Baire.  Finite local Artin jet packets are
represented without losing mixed derivatives: coordinates are point/multi-index pairs and the
evaluation map uses the project's polarized Frechet jets.
-/

open Set Topology TopologicalSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A nowhere-vanishing line-entire automorphic factor for the translation lattice `Γ`.
The cocycle convention is the one compatible with `f (x + γ) = ψ γ x * f x`. -/
structure AutomorphicFactor (d : ℕ)
    (Γ : AddSubgroup (Fin d → ℂ)) where
  factor : Γ → MultivariateEntire d
  normalized : ∀ x, (factor 0).1 x = 1
  cocycle : ∀ γ δ x,
    (factor (γ + δ)).1 x = (factor γ).1 (x + δ.1) * (factor δ).1 x
  nowhereZero : ∀ γ x, (factor γ).1 x ≠ 0

/-- Entire automorphic forms for one fixed factor, as a complex linear subspace. -/
def AutomorphicFactor.forms {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) : Submodule ℂ (MultivariateEntire d) where
  carrier := {f | ∀ γ x, f.1 (x + γ.1) = (ψ.factor γ).1 x * f.1 x}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg γ x
    change f.1 (x + γ.1) + g.1 (x + γ.1) =
      (ψ.factor γ).1 x * (f.1 x + g.1 x)
    rw [hf γ x, hg γ x]
    ring
  smul_mem' := by
    intro c f hf γ x
    change c * f.1 (x + γ.1) = (ψ.factor γ).1 x * (c * f.1 x)
    rw [hf γ x]
    ring

/-- A fixed-factor section space inherits additive inverses from the entire-source space. -/
noncomputable instance AutomorphicFactor.formsAddCommGroup {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ) :
    AddCommGroup ψ.forms :=
  @Submodule.addCommGroup ℂ (MultivariateEntire d)
    inferInstance inferInstance inferInstance ψ.forms

/-- Addition is continuous on the fixed-factor compact-open subspace. -/
noncomputable instance AutomorphicFactor.formsContinuousAdd {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ) :
    ContinuousAdd ψ.forms :=
  continuousAdd_induced ψ.forms.subtype

/-- Complex scalar multiplication is continuous on the fixed-factor compact-open subspace. -/
noncomputable instance AutomorphicFactor.formsContinuousSMul {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ) :
    ContinuousSMul ℂ ψ.forms :=
  continuousSMul_induced ψ.forms.subtype

@[simp]
theorem AutomorphicFactor.mem_forms_iff {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ)
    (f : MultivariateEntire d) :
    f ∈ ψ.forms ↔ ∀ γ x, f.1 (x + γ.1) = (ψ.factor γ).1 x * f.1 x :=
  Iff.rfl

/-- Automorphy is closed under compact-open convergence. -/
theorem AutomorphicFactor.isClosed_forms {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ) :
    IsClosed (ψ.forms : Set (MultivariateEntire d)) := by
  change IsClosed {f : MultivariateEntire d | ∀ γ x,
    f.1 (x + γ.1) = (ψ.factor γ).1 x * f.1 x}
  simp_rw [setOf_forall]
  apply isClosed_iInter
  intro γ
  apply isClosed_iInter
  intro x
  apply isClosed_eq
  · exact (continuous_eval_const (x + γ.1)).comp continuous_subtype_val
  · exact continuous_const.mul
      ((continuous_eval_const x).comp continuous_subtype_val)

/-- Fixed-factor automorphic sections are complete for compact-open convergence. -/
noncomputable instance AutomorphicFactor.formsComplete {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ) :
    CompleteSpace ψ.forms :=
  ψ.isClosed_forms.completeSpace_coe

/-- Fixed-factor automorphic sections are completely metrizable. -/
noncomputable instance AutomorphicFactor.formsCompletelyMetrizable {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ) :
    IsCompletelyMetrizableSpace ψ.forms :=
  ψ.isClosed_forms.isCompletelyMetrizableSpace

/-- Hence the fixed-factor section space has the Baire property used in the residual orbit
construction. -/
noncomputable instance AutomorphicFactor.formsBaire {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ) :
    BaireSpace ψ.forms := by
  infer_instance

/-- Multi-indices of total degree strictly below `m`; these are the coordinate basis of the
truncated local algebra `𝒪 / 𝔪^m`. -/
def FiniteJetMultiIndex (d m : ℕ) :=
  {a : Fin d →₀ ℕ // Finsupp.degree a < m}

noncomputable instance (d m : ℕ) : Fintype (FiniteJetMultiIndex d m) :=
  (Finsupp.finite_of_degree_lt m).fintype

instance (d m : ℕ) : DecidableEq (FiniteJetMultiIndex d m) :=
  Classical.decEq _

/-- Coordinate set of a finite point packet with independently prescribed truncation orders. -/
def FiniteJetPacketIndex (d : ℕ) (I : Type*) (m : I → ℕ) :=
  Σ i : I, FiniteJetMultiIndex d (m i)

noncomputable instance (d : ℕ) (I : Type*) [Fintype I] (m : I → ℕ) :
    Fintype (FiniteJetPacketIndex d I m) := by
  unfold FiniteJetPacketIndex
  infer_instance

instance (d : ℕ) (I : Type*) [DecidableEq I] (m : I → ℕ) :
    DecidableEq (FiniteJetPacketIndex d I m) :=
  Classical.decEq _

/-- Two chosen lifts represent distinct quotient points precisely when their difference is not a
period. -/
def PairwiseDistinctModulo {d : ℕ} (Γ : AddSubgroup (Fin d → ℂ))
    {I : Type*} (w : I → Fin d → ℂ) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → w i - w j ∉ Γ

/-- Restriction of fixed-factor automorphic sections to a finite full mixed-jet packet. -/
def AutomorphicFactor.jetPacketLinearMap {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ)
    {I : Type*} (w : I → Fin d → ℂ) (m : I → ℕ) :
    ψ.forms →ₗ[ℂ] (FiniteJetPacketIndex d I m → ℂ) where
  toFun f q := multiIndexJetEvalCLM (w q.1) q.2.1 f.1
  map_add' f g := by
    funext q
    exact map_add (multiIndexJetEvalCLM (w q.1) q.2.1) f.1 g.1
  map_smul' c f := by
    funext q
    exact map_smul (multiIndexJetEvalCLM (w q.1) q.2.1) c f.1

@[simp]
theorem AutomorphicFactor.jetPacketLinearMap_apply {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ)
    {I : Type*} (w : I → Fin d → ℂ) (m : I → ℕ)
    (f : ψ.forms) (q : FiniteJetPacketIndex d I m) :
    ψ.jetPacketLinearMap w m f q =
      multiIndexJetEvalCLM (w q.1) q.2.1 f.1 :=
  rfl

/-- The same finite-jet restriction map with its compact-open continuity retained. -/
def AutomorphicFactor.jetPacketCLM {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ)
    {I : Type*} [Fintype I] (w : I → Fin d → ℂ) (m : I → ℕ) :
    ψ.forms →L[ℂ] (FiniteJetPacketIndex d I m → ℂ) where
  toLinearMap := ψ.jetPacketLinearMap w m
  cont := continuous_pi fun q =>
    (multiIndexJetEvalCLM (w q.1) q.2.1).continuous.comp continuous_subtype_val

@[simp]
theorem AutomorphicFactor.jetPacketCLM_apply {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ)
    {I : Type*} [Fintype I] (w : I → Fin d → ℂ) (m : I → ℕ)
    (f : ψ.forms) (q : FiniteJetPacketIndex d I m) :
    ψ.jetPacketCLM w m f q = multiIndexJetEvalCLM (w q.1) q.2.1 f.1 :=
  rfl

/-- Exact fixed-factor all-order jet-ampleness predicate.  It asks for surjectivity onto every
finite local Artin packet at pairwise distinct quotient points, with the same automorphic factor
at all orders. -/
def AutomorphicFactor.JetAmpleEveryFiniteOrder {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ) : Prop :=
  ∀ (I : Type*) [Fintype I] [DecidableEq I]
    (w : I → Fin d → ℂ) (m : I → ℕ),
    PairwiseDistinctModulo Γ w →
    (∀ i, 0 < m i) →
    Function.Surjective (ψ.jetPacketLinearMap w m)

end

end GaloisForLFunctions.HTGeometry
