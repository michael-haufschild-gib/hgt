/-
Regime-step provider bridge for the SPUR-R / AMP stack.

`LedgerConvex` proves positive S-increments from the corrected deep/endpoint
regime ledgers.  `SpurSMono` consumes positive adjacent S-increments.  This
module packages the reusable handoff: each ledger regime produces one
`SMonoStepCert`, and a certified adjacent S-chain feeds the AMP exact-pair
reader through a monotone or antitone dressing.
-/
import GaloisForLFunctions.RHTower.LedgerConvex
import GaloisForLFunctions.RHTower.SpurSMono

noncomputable section

namespace RHTower

/-- A regime certificate for one adjacent S-step: the realized step is positive. -/
def SMonoStepCert (S₀ S₁ : ℝ) : Prop := 0 < S₁ - S₀

/-- Adjacent S-step certificates for a complete list of S-readings. -/
def SMonoStepCerts (S : List ℝ) : Prop := AdjacentStepPos S

/-- Any explicit positive S-increment is a one-step S-mono certificate. -/
theorem smonoStepCert_of_pos {S₀ S₁ : ℝ} (h : 0 < S₁ - S₀) :
    SMonoStepCert S₀ S₁ := h

/-- Deep-band ledger regime, using the Lemma-H sum/tail reversal budget, as one S-step. -/
theorem smonoStepCert_of_deep_sum_tail {S₀ S₁ : ℝ} {ι : Type*} (s : Finset ι)
    {C₀ δ extra paired tail ΔG W inc M response error : ℝ} (a : ι → ℝ)
    (hC₀ : 0 ≤ C₀) (hCsmall : C₀ ≤ (1 : ℝ) / 15)
    (hδ : 0 < δ) (hextra : 2 ≤ extra) (hpaired : 0 ≤ paired)
    (hcard : (s.card : ℝ) * δ ≤ 4)
    (ha : ∀ x ∈ s, a x ≤ 43 * C₀ ^ 2 * δ)
    (htail : tail ≤ 28 * C₀ ^ 2)
    (hΔG : ΔG = extra + paired - ((∑ x ∈ s, a x) + tail))
    (hWpos : 0 < W) (hW : W ≤ 40 / δ ^ 2)
    (hinc : inc = ΔG / (2 * W))
    (hM : 36 ≤ M ^ 2 * δ)
    (hresponse : ((189 : ℝ) / 5) / δ ^ 3 ≤ response)
    (herror : error ≤ 16 / (M ^ 2 * δ ^ 2))
    (hΔS : S₁ - S₀ = inc * response - error) :
    SMonoStepCert S₀ S₁ := by
  exact corrected_deep_regime_of_sum_tail s a hC₀ hCsmall hδ hextra hpaired hcard ha htail
    hΔG hWpos hW hinc hM hresponse herror hΔS

/-- Endpoint-band ledger regime, using the Lemma-H sum/tail reversal budget, as one S-step. -/
theorem smonoStepCert_of_endpoint_sum_tail {S₀ S₁ : ℝ} {ι : Type*} (s : Finset ι)
    {C₀ δ extra paired tail ΔG W inc M response error : ℝ} (a : ι → ℝ)
    (hC₀ : 0 ≤ C₀) (hCsmall : C₀ ≤ (1 : ℝ) / 15)
    (hδ : 0 < δ) (hextra : 2 ≤ extra) (hpaired : 0 ≤ paired)
    (hcard : (s.card : ℝ) * δ ≤ 4)
    (ha : ∀ x ∈ s, a x ≤ 43 * C₀ ^ 2 * δ)
    (htail : tail ≤ 28 * C₀ ^ 2)
    (hΔG : ΔG = extra + paired - ((∑ x ∈ s, a x) + tail))
    (hWpos : 0 < W) (hW : W ≤ 40 / δ ^ 2)
    (hinc : inc = ΔG / (2 * W))
    (hM : 3136 ≤ M ^ 2 * δ ^ 2)
    (hresponse : (5 : ℝ) / (12 * δ ^ 2) ≤ response)
    (herror : error ≤ 16 / (M ^ 2 * δ ^ 2))
    (hΔS : S₁ - S₀ = inc * response - error) :
    SMonoStepCert S₀ S₁ := by
  exact corrected_endpoint_regime_of_sum_tail s a hC₀ hCsmall hδ hextra hpaired hcard ha htail
    hΔG hWpos hW hinc hM hresponse herror hΔS

/-- Deep-band ledger regime, using a per-carrier direct unit-margin evaluation, as one S-step. -/
theorem smonoStepCert_of_deep_direct_eval {S₀ S₁ : ℝ}
    {δ extra paired reversal ΔG γᵢ W inc M response error : ℝ}
    (hδ : 0 < δ) (hγᵢ : 1 ≤ γᵢ) (heval : γᵢ ≤ extra + paired - reversal)
    (hΔG : ΔG = extra + paired - reversal)
    (hWpos : 0 < W) (hW : W ≤ 40 / δ ^ 2)
    (hinc : inc = ΔG / (2 * W))
    (hM : 36 ≤ M ^ 2 * δ)
    (hresponse : ((189 : ℝ) / 5) / δ ^ 3 ≤ response)
    (herror : error ≤ 16 / (M ^ 2 * δ ^ 2))
    (hΔS : S₁ - S₀ = inc * response - error) :
    SMonoStepCert S₀ S₁ := by
  exact corrected_deep_regime_of_direct_eval hδ hγᵢ heval hΔG hWpos hW hinc hM hresponse
    herror hΔS

/-- Endpoint-band ledger regime, using a per-carrier direct unit-margin evaluation, as one S-step. -/
theorem smonoStepCert_of_endpoint_direct_eval {S₀ S₁ : ℝ}
    {δ extra paired reversal ΔG γᵢ W inc M response error : ℝ}
    (hδ : 0 < δ) (hγᵢ : 1 ≤ γᵢ) (heval : γᵢ ≤ extra + paired - reversal)
    (hΔG : ΔG = extra + paired - reversal)
    (hWpos : 0 < W) (hW : W ≤ 40 / δ ^ 2)
    (hinc : inc = ΔG / (2 * W))
    (hM : 3136 ≤ M ^ 2 * δ ^ 2)
    (hresponse : (5 : ℝ) / (12 * δ ^ 2) ≤ response)
    (herror : error ≤ 16 / (M ^ 2 * δ ^ 2))
    (hΔS : S₁ - S₀ = inc * response - error) :
    SMonoStepCert S₀ S₁ := by
  exact corrected_endpoint_regime_of_direct_eval hδ hγᵢ heval hΔG hWpos hW hinc hM hresponse
    herror hΔS

/-- Deep-response S″ closure as one S-mono step. -/
theorem smonoStepCert_of_sdouble_deep {S₀ S₁ : ℝ}
    {δ c₈ M ΔG W inc response swap : ℝ}
    (hδ : 0 < δ) (hΔG : 1 ≤ ΔG)
    (hWpos : 0 < W) (hW : W ≤ 40 / δ ^ 2)
    (hinc : inc = ΔG / (2 * W))
    (hband : 64 ≤ M ^ 2 * c₈ * δ)
    (hresponse : ((189 : ℝ) / 5) / δ ^ 3 ≤ response)
    (hswap : c₈ / (4 * δ) - 16 / (M ^ 2 * δ ^ 2) ≤ swap)
    (hΔS : S₁ - S₀ = inc * response + swap) :
    SMonoStepCert S₀ S₁ := by
  exact corrected_sdouble_deep_regime_of_unit_march hδ hΔG hWpos hW hinc hband
    hresponse hswap hΔS

/-- Endpoint-response S″ closure as one S-mono step. -/
theorem smonoStepCert_of_sdouble_endpoint {S₀ S₁ : ℝ}
    {δ c₈ M ΔG W inc response swap : ℝ}
    (hδ : 0 < δ) (hΔG : 1 ≤ ΔG)
    (hWpos : 0 < W) (hW : W ≤ 40 / δ ^ 2)
    (hinc : inc = ΔG / (2 * W))
    (hband : 64 ≤ M ^ 2 * c₈ * δ)
    (hresponse : (5 : ℝ) / (12 * δ ^ 2) ≤ response)
    (hswap : c₈ / (4 * δ) - 16 / (M ^ 2 * δ ^ 2) ≤ swap)
    (hΔS : S₁ - S₀ = inc * response + swap) :
    SMonoStepCert S₀ S₁ := by
  exact corrected_sdouble_endpoint_regime_of_unit_march hδ hΔG hWpos hW hinc hband
    hresponse hswap hΔS

/-- Extract the positive adjacent S-increment from a one-step regime certificate. -/
theorem stepPos_of_smonoStepCert {S₀ S₁ : ℝ} (h : SMonoStepCert S₀ S₁) :
    0 < S₁ - S₀ := h

/-- AMP reader input from ledger-certified regime steps and a monotone S-to-margin dressing. -/
theorem ampReaderInput_of_regime_dressing_le {S : List ℝ} {Z : ℕ} {dress : ℝ → ℝ}
    (hS : SMonoStepCerts S) (hdress : Monotone dress)
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound : Z ≤ 2 + copyFlipTransitions (ampMarginStates (S.map dress))) :
    AMPReaderInput (S.map dress) Z :=
  ampReaderInput_of_smono_dressing_le hS hdress hvisible heven hbound

/-- AMP reader input from ledger-certified regime steps and an antitone S-to-margin dressing. -/
theorem ampReaderInput_of_regime_dressing_ge {S : List ℝ} {Z : ℕ} {dress : ℝ → ℝ}
    (hS : SMonoStepCerts S) (hdress : Antitone dress)
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound : Z ≤ 2 + copyFlipTransitions (ampMarginStates (S.map dress))) :
    AMPReaderInput (S.map dress) Z :=
  ampReaderInput_of_smono_dressing_ge hS hdress hvisible heven hbound

/-- Exact reader pair from ledger-certified regime steps and a monotone S-to-margin dressing. -/
theorem amp_reader_exact_pair_of_regime_dressing_le {S : List ℝ} {Z : ℕ} {dress : ℝ → ℝ}
    (hS : SMonoStepCerts S) (hdress : Monotone dress)
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound : Z ≤ 2 + copyFlipTransitions (ampMarginStates (S.map dress))) :
    Z = 2 :=
  amp_reader_exact_pair_of_smono_dressing_le hS hdress hvisible heven hbound

/-- Exact reader pair from ledger-certified regime steps and an antitone S-to-margin dressing. -/
theorem amp_reader_exact_pair_of_regime_dressing_ge {S : List ℝ} {Z : ℕ} {dress : ℝ → ℝ}
    (hS : SMonoStepCerts S) (hdress : Antitone dress)
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound : Z ≤ 2 + copyFlipTransitions (ampMarginStates (S.map dress))) :
    Z = 2 :=
  amp_reader_exact_pair_of_smono_dressing_ge hS hdress hvisible heven hbound

end RHTower
