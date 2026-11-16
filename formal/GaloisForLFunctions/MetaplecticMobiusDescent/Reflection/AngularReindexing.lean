import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.AngularMixedReflection
import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.FrozenBranchColumns

/-!
# Reindexing actual angular cusp reflection

The angular denominator depends only on the prime product; its character survives
reindexing and pullback of controlled cusp data. The opposite frequency character
is independent of the prime labels.
-/

open scoped BigOperators Classical ComplexConjugate MatrixGroups
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection CanonicalQuadraticSieve
open InverseMoment
namespace InverseReflectedPhase
noncomputable section
local notation "Eis" => Eisenstein.O
lemma angularMixedReflectedValue_cast (ℓ : ℕ) {ι : Type*} [Fintype ι] {p q : ι→Eis} {N a c : Eis} {mode : Bool}
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (h : p=q) (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i≠0) (hq : ∀ i, q i≠0) (hc : c≠0)
    (hgp : ∀ i, lambda∉Ideal.span {p i}) (hgq : ∀ i, lambda∉Ideal.span {q i})
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    angularMixedReflectedValue ℓ (castControlled h D) s hq hc hgq j S W X=
      angularMixedReflectedValue ℓ D s hp hc hgp j S W X := by
  subst q
  rfl

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι→Eis} {N a c : Eis} {mode : Bool}

theorem angularMixedReflectedValue_reindex (ℓ : ℕ) [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i≠0) (hc : c≠0) (hg : ∀ i, lambda∉Ideal.span {p i})
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    angularMixedReflectedValue ℓ (reindexControlled D e) s (fun k => hp (e k)) hc (fun k => hg (e k))
      (fun k => j (e k)) (reindexMarks e S) W X =angularMixedReflectedValue ℓ D s hp hc hg j S W X := by
  have hprod (x : Eis) :
      (∏ k, mixedActiveBracket (fun k => hp (e k)) (fun k => hg (e k)) (fun k => j (e k))
        (reindexMarks e S) (reindexControlled D e) k x)=∏ i, mixedActiveBracket hp hg j S D i x := by
    simp_rw [mixedActiveBracket_reindex]
    exact e.prod_comp (fun i => mixedActiveBracket hp hg j S D i x)
  simp only [angularMixedReflectedValue,e.prod_comp p,reindexControlled_fixedFactor,
    reindexControlled_matrix_one,reindexControlled_U,hprod]
end

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι→Eis} {q : κ→Eis}
    {N a c : Eis} {mode : Bool}

theorem angularMixedReflectedValue_pullback (ℓ : ℕ)
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ k, (Ideal.span {q k}).IsMaximal]
    (e : κ≃ι) (h : (fun k => p (e k))=q)
    (D : ControlledStratumArithmetic q N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i≠0) (hq : ∀ k, q k≠0) (hc : c≠0)
    (hgp : ∀ i, lambda∉Ideal.span {p i}) (hgq : ∀ k, lambda∉Ideal.span {q k})
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    angularMixedReflectedValue ℓ (pullbackControlled e h D) s hp hc hgp j S W X=
      angularMixedReflectedValue ℓ D s hq hc hgq (fun k => j (e k)) (reindexMarks e S) W X := by
  unfold pullbackControlled
  rw [angularMixedReflectedValue_cast ℓ _ _ s (fun i => hq (e.symm i)) hp hc
    (fun i => hgq (e.symm i)) hgp]
  have hj : (fun i => j (e (e.symm i)))=j := by funext i; simp only [Equiv.apply_symm_apply]
  have he := angularMixedReflectedValue_reindex ℓ D e.symm s hq hc hgq
    (fun k => j (e k)) (reindexMarks e S) W X
  rw [hj,reindexMarks_symm] at he
  exact he
end

end
end InverseReflectedPhase
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
