/-
# From one packet escape to the whole labeling orbit

The labeling-orbit obstruction is a product over relabelings, and the `σ`-labeled factor of a
coefficient packet `c` is the *unlabeled* relation of the relabeled packet `c ∘ σ⁻¹`.  Relabeling
preserves both "nonzero" and "zero sum", so a rigidity statement quantified over all nonzero
zero-sum packets already supplies an escape for every labeling.

Composing that with the moving-rate chart escape gives the globalisation step in the form the
fixed-shell nonflatness theorem uses: inside every nonempty open set of real parameters there is a
point at which *no* relabeling of the quadratic-rate relation holds, for *any* simple root packet
sitting over it.

Main results:
* `forall_perm_exists_permutedAnalyticVariableRate_ne_zero` — a packet escape is a labeling escape.
* `exists_mem_forall_relabelled_quadraticRate_ne_zero_of_packetEscape` — the globalisation step.
-/
import GaloisForLFunctions.HTGeometry.VariableRateAnalyticEscape

open Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **A packet escape is a labeling escape.**  The `σ`-labeled factor of `c` is the unlabeled
relation of `c ∘ σ⁻¹`, which is again nonzero with zero sum. -/
theorem forall_perm_exists_permutedAnalyticVariableRate_ne_zero
    {I E : Type*} [Fintype I] [DecidableEq I] (c : I → ℂ) (rate : E → ℂ)
    (branch : I → E → ℂ) {U : Set E}
    (hpacket : ∀ d : I → ℂ, d ≠ 0 → (∑ i, d i) = 0 →
      ∃ p ∈ U, (∑ i, d i * branch i p) ^ (2 : ℕ) - rate p * ∑ i, branch i p ^ (2 : ℕ) ≠ 0)
    (hc : c ≠ 0) (hsum : ∑ i, c i = 0) :
    ∀ σ : Equiv.Perm I, ∃ p ∈ U, permutedAnalyticVariableRate c rate branch σ p ≠ 0 := by
  intro σ
  have hne : (fun j => c (σ.symm j)) ≠ 0 := by
    intro hzero
    refine hc ?_
    funext i
    have := congrFun hzero (σ i)
    simpa using this
  have hzsum : (∑ j, c (σ.symm j)) = 0 := by
    rw [Fintype.sum_equiv σ (fun i => c i) (fun j => c (σ.symm j)) fun i => by simp] at hsum
    exact hsum
  obtain ⟨p, hp, hpne⟩ := hpacket (fun j => c (σ.symm j)) hne hzsum
  refine ⟨p, hp, ?_⟩
  have hswap : (∑ i, c i * branch (σ i) p) = ∑ j, c (σ.symm j) * branch j p :=
    Fintype.sum_equiv σ _ _ fun i => by simp
  rw [permutedAnalyticVariableRate, hswap]
  exact hpne

/-- **The globalisation step of fixed-shell nonflatness, at a moving rate.**  A rigidity statement
for every nonzero zero-sum packet on one connected analytic chart forces, inside every nonempty
open set of real parameters, a point at which no relabeling of the quadratic-rate relation holds
for any simple root packet over it. -/
theorem exists_mem_forall_relabelled_quadraticRate_ne_zero_of_packetEscape
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin m) ℂ)) (c : I → ℂ) (κ : MvPolynomial (Fin m) ℂ)
    (hc : c ≠ 0) (hsum : ∑ i, c i = 0)
    {U : Set (Fin m → ℂ)} (hUopen : IsOpen U) (hUconnected : IsPreconnected U)
    (hUnonempty : U.Nonempty)
    (branch : I → (Fin m → ℂ) → ℂ)
    (hbranchA : ∀ x, AnalyticOnNhd ℂ (branch x) U)
    (hbranchInj : ∀ p ∈ U, Function.Injective fun x => branch x p)
    (hbranchRoot : ∀ x, ∀ p ∈ U,
      matrixCharpolyRelation
        (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) p), branch x p) = 0)
    (hpacket : ∀ d : I → ℂ, d ≠ 0 → (∑ i, d i) = 0 →
      ∃ p ∈ U, (∑ i, d i * branch i p) ^ (2 : ℕ)
        - MvPolynomial.eval₂ (RingHom.id ℂ) p κ * ∑ i, branch i p ^ (2 : ℕ) ≠ 0)
    {V : Set (Fin m → ℝ)} (hVopen : IsOpen V) (hVne : V.Nonempty) :
    ∃ q ∈ V, ∀ energy : I → ℂ, Function.Injective energy →
      (∀ i, matrixCharpolyRelation
        (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (q t : ℂ))), energy i) = 0) →
      ∀ σ : Equiv.Perm I,
        (∑ j, c (σ.symm j) * energy j) ^ (2 : ℕ)
          - MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (q t : ℂ)) κ * ∑ j, energy j ^ (2 : ℕ) ≠ 0 := by
  have hlabel := forall_perm_exists_permutedAnalyticVariableRate_ne_zero c
    (fun p : Fin m → ℂ => MvPolynomial.eval₂ (RingHom.id ℂ) p κ) branch hpacket hc hsum
  obtain ⟨q, hq, hqne⟩ :=
    exists_mem_eval_variableRateObstructionPullback_ne_zero_of_analyticBranchEscape M c κ
      hUopen hUconnected hUnonempty branch hbranchA hbranchInj hbranchRoot hlabel hVopen hVne
  refine ⟨q, hq, fun energy hinj hroot σ hσ => hqne ?_⟩
  rw [eval_variableRateObstructionPullback M c κ (fun t => (q t : ℂ)) energy hinj hroot]
  exact (fieldQuadraticRateOrbitValue_eq_zero_iff c _ energy).mpr ⟨σ, hσ⟩

end GaloisForLFunctions.HTGeometry
