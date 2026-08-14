import GaloisForLFunctions.HTGeometry.AffineJetDifferentialIndependence
import GaloisForLFunctions.HTGeometry.MultivariateJetCompositionLaw
import GaloisForLFunctions.HTGeometry.LinearFormSubstitution

/-!
# Constant-coefficient operator rows on an affine orbit

A finitely supported row of constant-coefficient differential operators produces one entire source
from an affine orbit, and its mixed jets are the shifted jets of the orbit weighted by the operator
coefficients.  A differential relation among finitely many such rows therefore pulls back along the
substitution that sends each output jet variable to the corresponding shifted linear form in the
orbit jet variables.  When the shifted rows are linearly independent that substitution is injective,
so the outputs inherit the differential independence of the orbit.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- The value of a differential relation at a finite family of sources. -/
def jetRelationValue {d m : ℕ} (H : Fin m → MultivariateEntire d)
    (Q : MvPolynomial (Fin m × (Fin d →₀ ℕ)) (MvPolynomial (Fin d) ℂ)) (z : Fin d → ℂ) : ℂ :=
  eval₂ (eval z) (fun q => multiIndexJetEvalCLM z q.2 (H q.1)) Q

theorem affineJetRelationValue_eq_jetRelationValue {d n : ℕ}
    (frame : Fin n → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (f : MultivariateEntire d)
    (P : MvPolynomial (RelationJetVar d n) (MvPolynomial (Fin d) ℂ)) (z : Fin d → ℂ) :
    affineJetRelationValue frame f P z =
      jetRelationValue (fun j => multivariateEntireAffinePullback (frame j) f) P z := rfl

/-- Evaluating a substituted relation is evaluating the relation at the substituted values. -/
theorem eval₂_aeval_comp {A B R : Type*} [CommSemiring R] (g : R →+* ℂ) (Y : B → ℂ)
    (S : A → MvPolynomial B R) (Q : MvPolynomial A R) :
    eval₂ g Y (aeval S Q) = eval₂ g (fun a => eval₂ g Y (S a)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => rw [map_add, eval₂_add, eval₂_add, hp, hq]
  | mul_X p a hp => rw [map_mul, eval₂_mul, eval₂_mul, hp, aeval_X, eval₂_X]

/-- The source produced by one constant-coefficient operator row. -/
def operatorRowSource {d n : ℕ} (frame : Fin n → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ)))
    (f : MultivariateEntire d) (L : Fin n → MvPolynomial (Fin d) ℂ) : MultivariateEntire d :=
  ∑ j : Fin n, ∑ β ∈ (L j).support,
    coeff β (L j) • multiPartialDerivEntire β (multivariateEntireAffinePullback (frame j) f)

/-- **The jets of an operator row are the shifted jets of the orbit.** -/
theorem multiIndexJetEvalCLM_operatorRowSource {d n : ℕ}
    (frame : Fin n → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (f : MultivariateEntire d)
    (L : Fin n → MvPolynomial (Fin d) ℂ) (z : Fin d → ℂ) (γ : Fin d →₀ ℕ) :
    multiIndexJetEvalCLM z γ (operatorRowSource frame f L) =
      ∑ j : Fin n, ∑ β ∈ (L j).support,
        coeff β (L j) * affineMultiIndexJetEvalCLM (frame j) z (γ + β) f := by
  rw [operatorRowSource, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, multiIndexJetEvalCLM_multiPartialDerivEntire, smul_eq_mul]
  rfl

/-- The jet-variable coefficient vector attached to an operator matrix. -/
def operatorJetSubstVector {d m n : ℕ} (L : Fin m → Fin n → MvPolynomial (Fin d) ℂ)
    (q : Fin m × (Fin d →₀ ℕ)) : (RelationJetVar d n) →₀ ℂ :=
  ∑ j : Fin n, ∑ β ∈ (L q.1 j).support,
    Finsupp.single (j, q.2 + β) (coeff β (L q.1 j))

/-- Evaluating a linear form is the weighted sum of its coefficients. -/
theorem eval₂_linForm {d : ℕ} {B : Type*} (Y : B → ℂ) (z : Fin d → ℂ)
    (s : B →₀ ℂ) :
    eval₂ (eval z) Y (linForm (MvPolynomial (Fin d) ℂ) s) = s.sum fun b c => c * Y b := by
  induction s using Finsupp.induction_linear with
  | zero => simp
  | add s t hs ht =>
      rw [map_add, eval₂_add, hs, ht,
        Finsupp.sum_add_index' (by simp) (by intro b c₁ c₂; ring)]
  | single b c =>
      rw [linForm_single, Finsupp.sum_single_index (by simp)]
      have hsm : (c • (X b : MvPolynomial B (MvPolynomial (Fin d) ℂ))) =
          C (MvPolynomial.C c) * X b := by
        rw [Algebra.smul_def]
        congr 1
      rw [hsm, eval₂_mul, eval₂_C, eval₂_X, MvPolynomial.eval_C]

/-- Evaluating a linear form is the corresponding linear combination. -/
theorem eval₂_linForm_eq_linearCombination {d : ℕ} {B : Type*} (Y : B → ℂ) (z : Fin d → ℂ)
    (s : B →₀ ℂ) :
    eval₂ (eval z) Y (linForm (MvPolynomial (Fin d) ℂ) s) =
      Finsupp.linearCombination ℂ Y s := by
  rw [eval₂_linForm, Finsupp.linearCombination_apply]
  rfl

/-- The output jets are the substituted orbit jets. -/
theorem multiIndexJetEvalCLM_operatorRowSource_eq_eval₂ {d m n : ℕ}
    (frame : Fin n → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (f : MultivariateEntire d)
    (L : Fin m → Fin n → MvPolynomial (Fin d) ℂ) (i : Fin m) (γ : Fin d →₀ ℕ)
    (z : Fin d → ℂ) :
    multiIndexJetEvalCLM z γ (operatorRowSource frame f (L i)) =
      eval₂ (eval z) (fun q => affineMultiIndexJetEvalCLM (frame q.1) z q.2 f)
        (linForm (MvPolynomial (Fin d) ℂ) (operatorJetSubstVector L (i, γ))) := by
  rw [eval₂_linForm, multiIndexJetEvalCLM_operatorRowSource, operatorJetSubstVector,
    ← Finsupp.sum_finsetSum_index (by simp) (by intro b c₁ c₂; ring)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finsupp.sum_finsetSum_index (by simp) (by intro b c₁ c₂; ring)]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finsupp.sum_single_index (by simp)]

/-- **Constant-coefficient operator rows inherit differential independence.**  If the shifted rows
are linearly independent over `ℂ`, i.e. the rows are independent over the operator ring, then no
nonzero differential relation holds among the row outputs on a generic source. -/
theorem exists_jetRelationValue_operatorRowSource_ne_zero {d : ℕ} (hd : 0 < d) {Λ : Type*}
    [Countable Λ] (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (hframe : Function.Injective frame)
    {f : MultivariateEntire d} (hf : f ∈ affineJetPacketGenericSet hd frame hframe)
    {n : ℕ} (lab : Fin n → Λ) (hlab : Function.Injective lab)
    {m : ℕ} (L : Fin m → Fin n → MvPolynomial (Fin d) ℂ)
    (hL : LinearIndependent ℂ (operatorJetSubstVector L))
    {Q : MvPolynomial (Fin m × (Fin d →₀ ℕ)) (MvPolynomial (Fin d) ℂ)} (hQ : Q ≠ 0) :
    ∃ z : Fin d → ℂ,
      jetRelationValue (fun i => operatorRowSource (fun j => frame (lab j)) f (L i)) Q z ≠ 0 := by
  have hsub : aeval (fun q => linForm (MvPolynomial (Fin d) ℂ) (operatorJetSubstVector L q)) Q ≠ 0 := by
    intro hzero
    exact hQ (injective_aeval_linForm (operatorJetSubstVector L) hL (by simpa using hzero))
  obtain ⟨z, hz⟩ := exists_affineJetRelationValue_ne_zero hd frame hframe hf lab hlab hsub
  refine ⟨z, ?_⟩
  intro hcontra
  apply hz
  rw [affineJetRelationValue, eval₂_aeval_comp]
  have hfun : (fun q : Fin m × (Fin d →₀ ℕ) =>
      eval₂ (eval z) (fun r : RelationJetVar d n =>
          affineMultiIndexJetEvalCLM (frame (lab r.1)) z r.2 f)
        (linForm (MvPolynomial (Fin d) ℂ) (operatorJetSubstVector L q))) =
      fun q : Fin m × (Fin d →₀ ℕ) =>
        multiIndexJetEvalCLM z q.2 (operatorRowSource (fun j => frame (lab j)) f (L q.1)) := by
    funext q
    exact (multiIndexJetEvalCLM_operatorRowSource_eq_eval₂
      (fun j => frame (lab j)) f L q.1 q.2 z).symm
  rw [hfun]
  exact hcontra

/-- **Operator rows dependent over the operator ring satisfy a linear differential relation.**
The relation is the linear form of any nontrivial dependence between the shifted rows. -/
theorem exists_nonzero_jetRelation_of_not_linearIndependent {d m n : ℕ}
    (frame : Fin n → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (f : MultivariateEntire d)
    (L : Fin m → Fin n → MvPolynomial (Fin d) ℂ)
    (hL : ¬ LinearIndependent ℂ (operatorJetSubstVector L)) :
    ∃ Q : MvPolynomial (Fin m × (Fin d →₀ ℕ)) (MvPolynomial (Fin d) ℂ), Q ≠ 0 ∧
      ∀ z : Fin d → ℂ,
        jetRelationValue (fun i => operatorRowSource frame f (L i)) Q z = 0 := by
  have hex : ∃ κ : (Fin m × (Fin d →₀ ℕ)) →₀ ℂ,
      Finsupp.linearCombination ℂ (operatorJetSubstVector L) κ = 0 ∧ κ ≠ 0 := by
    by_contra hcon
    refine hL ?_
    rw [linearIndependent_iff]
    intro l hl
    by_contra hl0
    exact hcon ⟨l, hl, hl0⟩
  obtain ⟨κ, hκ, hκ0⟩ := hex
  have halg : Function.Injective (algebraMap ℂ (MvPolynomial (Fin d) ℂ)) := by
    simpa [MvPolynomial.algebraMap_eq] using MvPolynomial.C_injective (Fin d) ℂ
  refine ⟨linForm (MvPolynomial (Fin d) ℂ) κ, ?_, ?_⟩
  · intro hzero
    exact hκ0 (linForm_injective halg (by simpa using hzero))
  · intro z
    rw [jetRelationValue, eval₂_linForm_eq_linearCombination]
    have hjets : (fun q : Fin m × (Fin d →₀ ℕ) =>
        multiIndexJetEvalCLM z q.2 (operatorRowSource frame f (L q.1))) =
        (Finsupp.linearCombination ℂ
            (fun r : RelationJetVar d n => affineMultiIndexJetEvalCLM (frame r.1) z r.2 f)) ∘
          (operatorJetSubstVector L) := by
      funext q
      rw [Function.comp_apply, multiIndexJetEvalCLM_operatorRowSource_eq_eval₂,
        eval₂_linForm_eq_linearCombination]
    rw [hjets, ← Finsupp.apply_linearCombination, hκ, map_zero]

end

end GaloisForLFunctions.HTGeometry
