/-
# Endpoint-complete witnesses at every chain length

A single qubit carries an injective real field and the exchange operator as its endpoint channel.
One extension step turns that data into the same data one qubit longer, so the recursion runs from
one site upwards: at every chain length there is a physical one-qubit attachment whose spectrum is
simple and real and whose canonical eigenvectors are pairwise visible from the attached endpoint.

Main results:
* `qubitChain` — the index type of an `n`-fold qubit extension.
* `exists_hermitian_covering_channel` — the new endpoint channel of an endpoint-complete family.
* `exists_covering_channel_chain` — the propagating data at every length.
* `exists_endpointComplete_chain` — **complete endpoint witnesses at every chain length**.
-/
import GaloisForLFunctions.HTGeometry.LayerSplitEndpointStep

open Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
/-- **The new endpoint channel.**  An endpoint-complete eigenvector family supplies a Hermitian
channel on its own labelling which sees every ordered pair. -/
theorem exists_hermitian_covering_channel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : ι → (A × Bool) → ℂ)
    (hne : ∀ p : ι × ι, p.1 ≠ p.2 → layerReducedTransition (ψ p.1) (ψ p.2) ≠ 0) :
    ∃ N : Matrix ι ι ℂ, N.IsHermitian ∧ ∀ α β : ι, α ≠ β → N β α ≠ 0 := by
  classical
  obtain ⟨X, hXherm, hX⟩ :=
    exists_hermitian_covering_endpoint_probe (fun i => ψ i ∘ Prod.swap)
      (fun i j hij => by
        have h := hne (i, j) hij
        rwa [layerReducedTransition_eq_reducedTransition] at h)
  exact ⟨endpointChannel (fun i => ψ i ∘ Prod.swap) X,
    isHermitian_endpointChannel _ hXherm,
    fun α β hαβ => endpointChannel_ne_zero _ hX β α (Ne.symm hαβ)⟩

/-- The index type of an `n`-fold qubit extension of a single qubit. -/
def qubitChain : ℕ → Type
  | 0 => Bool
  | (n + 1) => qubitChain n × Bool

instance qubitChainFintype : ∀ n, Fintype (qubitChain n)
  | 0 => inferInstanceAs (Fintype Bool)
  | (n + 1) => @instFintypeProd _ _ (qubitChainFintype n) inferInstance

instance qubitChainDecidableEq : ∀ n, DecidableEq (qubitChain n)
  | 0 => inferInstanceAs (DecidableEq Bool)
  | (n + 1) => @instDecidableEqProd _ _ (qubitChainDecidableEq n) inferInstance

/-- The exchange operator of one qubit is Hermitian. -/
theorem isHermitian_layerExchange : layerExchange.IsHermitian := by
  refine Matrix.ext fun u v => ?_
  rw [Matrix.conjTranspose_apply, layerExchange_apply, layerExchange_apply]
  by_cases h : v = u
  · subst h; simp
  · have h' : ¬ u = v := fun hc => h hc.symm
    simp [h, h']

/-- A single qubit carries an injective real field and a Hermitian endpoint channel seeing its
only ordered pairs. -/
theorem exists_covering_channel_bool :
    ∃ (E : Bool → ℝ) (N : Matrix Bool Bool ℂ), Function.Injective E ∧ N.IsHermitian ∧
      ∀ α β : Bool, α ≠ β → N β α ≠ 0 := by
  refine ⟨fun b => if b then 1 else 0, layerExchange, ?_, isHermitian_layerExchange, ?_⟩
  · intro a b hab
    cases a <;> cases b <;> simp_all
  · intro α β hαβ
    rw [layerExchange_apply, if_neg (fun h : β = α => hαβ h.symm)]
    exact one_ne_zero

/-- **The propagating data at every chain length.** -/
theorem exists_covering_channel_chain : ∀ n : ℕ,
    ∃ (E : qubitChain n → ℝ) (N : Matrix (qubitChain n) (qubitChain n) ℂ),
      Function.Injective E ∧ N.IsHermitian ∧ ∀ α β : qubitChain n, α ≠ β → N β α ≠ 0
  | 0 => exists_covering_channel_bool
  | (n + 1) => by
      obtain ⟨E, N, hE, hNherm, hNne⟩ := exists_covering_channel_chain n
      obtain ⟨z, t, E', ψ, _htne, hE', _hherm, _heig, _hψ, hcomplete⟩ :=
        exists_layerSplit_endpointComplete_step hE hNherm hNne
      obtain ⟨N', hN'herm, hN'ne⟩ := exists_hermitian_covering_channel ψ hcomplete
      exact ⟨E', N', hE', hN'herm, hN'ne⟩

/-- **Complete endpoint witnesses at every chain length.**  For every `n` there are a real level
shift, a nonzero real coupling, a simple real old spectrum and a Hermitian attachment operator
whose split system is Hermitian, has a simple real spectrum, and whose canonical eigenvectors are
pairwise visible from the attached endpoint qubit. -/
theorem exists_endpointComplete_chain (n : ℕ) :
    ∃ (z t : ℝ) (E : qubitChain n → ℝ) (M : Matrix (qubitChain n) (qubitChain n) ℂ)
      (E' : qubitChain (n + 1) → ℝ) (ψ : qubitChain (n + 1) → qubitChain (n + 1) → ℂ),
      t ≠ 0 ∧ Function.Injective E ∧ M.IsHermitian ∧ Function.Injective E' ∧
      (layerSplitMatrix E z t M).IsHermitian ∧
      (∀ x, (layerSplitMatrix E z t M) *ᵥ (ψ x) = ((E' x : ℝ) : ℂ) • ψ x) ∧
      (∀ x, ψ x ≠ 0) ∧
      (∀ p : qubitChain (n + 1) × qubitChain (n + 1), p.1 ≠ p.2 →
        layerReducedTransition (ψ p.1) (ψ p.2) ≠ 0) := by
  obtain ⟨E, N, hE, hNherm, hNne⟩ := exists_covering_channel_chain n
  obtain ⟨z, t, E', ψ, htne, hE', hherm, heig, hψ, hcomplete⟩ :=
    exists_layerSplit_endpointComplete_step hE hNherm hNne
  exact ⟨z, t, E, N, E', ψ, htne, hE, hNherm, hE', hherm, heig, hψ, hcomplete⟩

end

end GaloisForLFunctions.HTGeometry
