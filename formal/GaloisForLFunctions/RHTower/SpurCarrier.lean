/-
Intended one-sided-far SPUR-R carrier protocol.

Docs 26/35--37 recut the SPUR-R reader around the reversed carrier
`S(y) = Σβ (y/(y - β))^2`, where the transported equilibria `y` march along the
outer one-sided window.  The proved ledger stack supplies four ways to certify one
adjacent positive S-step: deep/endpoint sum-tail regimes and deep/endpoint direct
finite evaluations.  This module packages those per-carrier certificates into a
typed chain over the actual reversed S-readings and instantiates `SpurRAMPInput`.

The numerical #136/#140 per-carrier checks are still inputs here; the gain is that
their exact Lean interface is no longer the abstract `SMonoStepCerts` predicate but
the intended carrier protocol.
-/
import GaloisForLFunctions.RHTower.SpurStack

noncomputable section

namespace RHTower

/-- Reversed-coordinate pole weight `ξ = y/(y - β)`. -/
def reversedPoleWeight (y β : ℝ) : ℝ := y / (y - β)

/-- The intended SPUR-R S-reading on the reversed one-sided carrier:
`S(y) = Σβ (y/(y-β))²`. -/
def reversedCarrierS (β : Multiset ℝ) (y : ℝ) : ℝ :=
  (β.map fun b => (reversedPoleWeight y b) ^ 2).sum

/-- S-readings along an ordered list of transported equilibria on the reversed carrier. -/
def reversedCarrierReadings (β : Multiset ℝ) (ys : List ℝ) : List ℝ :=
  ys.map (reversedCarrierS β)

/-- Common data for a ledger sum-tail certified adjacent S-step. -/
structure SumTailStepCore (S₀ S₁ : ℝ) where
  ι : Type
  idx : Finset ι
  C0 : ℝ
  delta : ℝ
  extra : ℝ
  paired : ℝ
  tail : ℝ
  deltaG : ℝ
  W : ℝ
  inc : ℝ
  M : ℝ
  response : ℝ
  error : ℝ
  a : ι → ℝ
  hC0 : 0 ≤ C0
  hCsmall : C0 ≤ (1 : ℝ) / 15
  hdelta : 0 < delta
  hextra : 2 ≤ extra
  hpaired : 0 ≤ paired
  hcard : (idx.card : ℝ) * delta ≤ 4
  ha : ∀ x ∈ idx, a x ≤ 43 * C0 ^ 2 * delta
  htail : tail ≤ 28 * C0 ^ 2
  hdeltaG : deltaG = extra + paired - ((∑ x ∈ idx, a x) + tail)
  hWpos : 0 < W
  hW : W ≤ 40 / delta ^ 2
  hinc : inc = deltaG / (2 * W)
  herror : error ≤ 16 / (M ^ 2 * delta ^ 2)
  hdeltaS : S₁ - S₀ = inc * response - error

/-- Deep-band sum-tail certificate for one intended-carrier S-step. -/
structure DeepSumTailCarrierStep (S₀ S₁ : ℝ) where
  core : SumTailStepCore S₀ S₁
  hM : 36 ≤ core.M ^ 2 * core.delta
  hresponse : ((189 : ℝ) / 5) / core.delta ^ 3 ≤ core.response

/-- Endpoint-band sum-tail certificate for one intended-carrier S-step. -/
structure EndpointSumTailCarrierStep (S₀ S₁ : ℝ) where
  core : SumTailStepCore S₀ S₁
  hM : 3136 ≤ core.M ^ 2 * core.delta ^ 2
  hresponse : (5 : ℝ) / (12 * core.delta ^ 2) ≤ core.response

/-- Common data for a direct finite-evaluation certified adjacent S-step. -/
structure DirectEvalStepCore (S₀ S₁ : ℝ) where
  delta : ℝ
  extra : ℝ
  paired : ℝ
  reversal : ℝ
  deltaG : ℝ
  gamma : ℝ
  W : ℝ
  inc : ℝ
  M : ℝ
  response : ℝ
  error : ℝ
  hdelta : 0 < delta
  hgamma : 1 ≤ gamma
  heval : gamma ≤ extra + paired - reversal
  hdeltaG : deltaG = extra + paired - reversal
  hWpos : 0 < W
  hW : W ≤ 40 / delta ^ 2
  hinc : inc = deltaG / (2 * W)
  herror : error ≤ 16 / (M ^ 2 * delta ^ 2)
  hdeltaS : S₁ - S₀ = inc * response - error

/-- Deep-band direct finite-evaluation certificate for one intended-carrier S-step. -/
structure DeepDirectCarrierStep (S₀ S₁ : ℝ) where
  core : DirectEvalStepCore S₀ S₁
  hM : 36 ≤ core.M ^ 2 * core.delta
  hresponse : ((189 : ℝ) / 5) / core.delta ^ 3 ≤ core.response

/-- Endpoint-band direct finite-evaluation certificate for one intended-carrier S-step. -/
structure EndpointDirectCarrierStep (S₀ S₁ : ℝ) where
  core : DirectEvalStepCore S₀ S₁
  hM : 3136 ≤ core.M ^ 2 * core.delta ^ 2
  hresponse : (5 : ℝ) / (12 * core.delta ^ 2) ≤ core.response

/-- One adjacent step in the intended one-sided-far SPUR-R carrier protocol. -/
inductive SpurROneSidedFarStep (S₀ S₁ : ℝ) : Type 2
  | deepSumTail (data : DeepSumTailCarrierStep S₀ S₁)
  | endpointSumTail (data : EndpointSumTailCarrierStep S₀ S₁)
  | deepDirect (data : DeepDirectCarrierStep S₀ S₁)
  | endpointDirect (data : EndpointDirectCarrierStep S₀ S₁)

/-- Any intended-carrier step certificate produces the S-mono step certificate. -/
def SpurROneSidedFarStep.toSMonoStepCert {S₀ S₁ : ℝ} :
    SpurROneSidedFarStep S₀ S₁ → SMonoStepCert S₀ S₁
  | .deepSumTail data =>
      smonoStepCert_of_deep_sum_tail data.core.idx data.core.a data.core.hC0
        data.core.hCsmall data.core.hdelta data.core.hextra data.core.hpaired data.core.hcard
        data.core.ha data.core.htail data.core.hdeltaG data.core.hWpos data.core.hW
        data.core.hinc data.hM data.hresponse data.core.herror data.core.hdeltaS
  | .endpointSumTail data =>
      smonoStepCert_of_endpoint_sum_tail data.core.idx data.core.a data.core.hC0
        data.core.hCsmall data.core.hdelta data.core.hextra data.core.hpaired data.core.hcard
        data.core.ha data.core.htail data.core.hdeltaG data.core.hWpos data.core.hW
        data.core.hinc data.hM data.hresponse data.core.herror data.core.hdeltaS
  | .deepDirect data =>
      smonoStepCert_of_deep_direct_eval data.core.hdelta data.core.hgamma data.core.heval
        data.core.hdeltaG data.core.hWpos data.core.hW data.core.hinc data.hM data.hresponse
        data.core.herror data.core.hdeltaS
  | .endpointDirect data =>
      smonoStepCert_of_endpoint_direct_eval data.core.hdelta data.core.hgamma data.core.heval
        data.core.hdeltaG data.core.hWpos data.core.hW data.core.hinc data.hM data.hresponse
        data.core.herror data.core.hdeltaS

/-- A chain of intended-carrier adjacent step certificates. -/
inductive SpurROneSidedFarChain : List ℝ → Type 2
  | nil : SpurROneSidedFarChain []
  | singleton (S₀ : ℝ) : SpurROneSidedFarChain [S₀]
  | cons {S₀ S₁ : ℝ} {rest : List ℝ}
      (head : SpurROneSidedFarStep S₀ S₁)
      (tail : SpurROneSidedFarChain (S₁ :: rest)) :
      SpurROneSidedFarChain (S₀ :: S₁ :: rest)

/-- The intended-carrier step chain realizes the abstract S-mono certificate chain. -/
def smonoStepCerts_of_spurROneSidedFarChain :
    {S : List ℝ} → SpurROneSidedFarChain S → SMonoStepCerts S
  | [], .nil => trivial
  | [_], .singleton _ => trivial
  | _ :: _ :: _, .cons head tail =>
      ⟨head.toSMonoStepCert, smonoStepCerts_of_spurROneSidedFarChain tail⟩

/-- The intended one-sided-far SPUR-R carrier input for the full AMP reader stack. -/
structure SpurROneSidedFarCarrierInput (β : Multiset ℝ) (ys : List ℝ)
    (Z : ℕ) (dress : ℝ → ℝ) : Type 2 where
  chain : SpurROneSidedFarChain (reversedCarrierReadings β ys)
  dressing : Monotone dress ∨ Antitone dress
  visible : 0 < Z
  even : Even Z
  counting_bound :
    Z ≤ 2 + copyFlipTransitions (ampMarginStates ((reversedCarrierReadings β ys).map dress))

/-- The intended one-sided-far carrier protocol instantiates the full SPUR-R / AMP provider. -/
theorem spurRAMPInput_of_oneSidedFarCarrierInput {β : Multiset ℝ} {ys : List ℝ}
    {Z : ℕ} {dress : ℝ → ℝ} (h : SpurROneSidedFarCarrierInput β ys Z dress) :
    SpurRAMPInput (reversedCarrierReadings β ys) Z dress where
  steps := smonoStepCerts_of_spurROneSidedFarChain h.chain
  dressing := h.dressing
  visible := h.visible
  even := h.even
  counting_bound := h.counting_bound

/-- Exact reader pair on the intended one-sided-far SPUR-R carrier. -/
theorem amp_reader_exact_pair_of_oneSidedFarCarrierInput {β : Multiset ℝ} {ys : List ℝ}
    {Z : ℕ} {dress : ℝ → ℝ} (h : SpurROneSidedFarCarrierInput β ys Z dress) :
    Z = 2 :=
  amp_reader_exact_pair_of_spurRAMPInput (spurRAMPInput_of_oneSidedFarCarrierInput h)

end RHTower
