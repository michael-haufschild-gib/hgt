import GaloisForLFunctions.RHTower.VonMangoldtGammaBoundaryDisplacementThreshold
import GaloisForLFunctions.RHTower.VonMangoldtGammaCofinalStrictBianchiLaw

/-!
# Von Mangoldt--Gamma boundary displacement universality

The uniquely renormalized prime boundary coordinate and every cofinal pointed-Bianchi realization
have one sharp displacement chamber.  Positive displacement gives finite prime energy, all raw
moments and their Euler identification, entrywise finite-to-cofinal convergence, semidefinite
arbitrary packets, and definite injectively labelled packets.  Nonpositive displacement already
forces divergent prime energy.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Complete finite-energy, moment, convergence, and Gram realization of the positive
Gamma--Bianchi displacement chamber. -/
def VonMangoldtGammaBoundaryDisplacementUniversalCertificate (x : ℝ) : Prop :=
  Summable (fun p : Nat.Primes =>
    vonMangoldtGammaRenormalizedBoundaryCoordinate x p ^ (2 : ℕ)) ∧
  (∀ a : ℕ, Summable (infiniteVonMangoldtGammaRawAtom x a)) ∧
  (∀ a : ℕ, infiniteVonMangoldtGammaRawMoment x a =
    vonMangoldtLogMoment a (x + 1)) ∧
  (∀ (n : ℕ) (a : Fin n → ℕ) (i j : Fin n),
    Tendsto (fun M => finiteVonMangoldtGammaRawGram M x a i j) atTop
      (nhds (infiniteVonMangoldtGammaRawGram x a i j))) ∧
  (∀ (n : ℕ) (a : Fin n → ℕ),
    (vonMangoldtGammaCofinalBianchiGram x a).PosSemidef) ∧
  (∀ (n : ℕ) (a : Fin n → ℕ), Function.Injective a →
    (vonMangoldtGammaCofinalBianchiGram x a).PosDef ∧
      0 < (vonMangoldtGammaCofinalBianchiGram x a).det) ∧
  ∀ (n : ℕ) (a b : Fin n → ℕ)
      (hadm : ∀ i j, b i + b j < a i + a j) (i j : Fin n),
    Tendsto
      (fun M => finiteVonMangoldtGammaAnomalyBianchiMixedGram M x a b hadm i j)
      atTop (nhds (vonMangoldtGammaCofinalBianchiGram x a i j))

/-- **Von Mangoldt--Gamma boundary displacement universality law.** Positive displacement is
equivalent to simultaneous square-summability of the canonical renormalized prime boundary,
all-depth raw-source convergence and Euler identification, cofinal Gram positivity, strictness for
every injective depth packet, and convergence of every admissible Bianchi anomaly packet. -/
theorem positiveDisplacement_iff_vonMangoldtGammaBoundaryUniversalCertificate
    (x : ℝ) :
    0 < x ↔ VonMangoldtGammaBoundaryDisplacementUniversalCertificate x := by
  constructor
  · intro hx
    refine ⟨
      (summable_sq_vonMangoldtGammaRenormalizedBoundaryCoordinate_prime_iff x).2 hx,
      fun a => summable_infiniteVonMangoldtGammaRawAtom hx a,
      fun a => infiniteVonMangoldtGammaRawMoment_eq_vonMangoldtLogMoment hx a,
      fun _n a i j => tendsto_finiteVonMangoldtGammaRawGram_apply hx a i j,
      fun _n a => vonMangoldtGammaCofinalBianchiGram_posSemidef hx a,
      ?_, ?_⟩
    · intro _n a ha
      exact ⟨
        vonMangoldtGammaCofinalBianchiGram_posDef_of_injective hx a ha,
        det_vonMangoldtGammaCofinalBianchiGram_pos_of_injective hx a ha⟩
    · intro _n a b hadm i j
      exact tendsto_finiteVonMangoldtGammaAnomalyBianchiMixedGram_apply
        hx a b hadm i j
  · intro hcertificate
    exact
      (summable_sq_vonMangoldtGammaRenormalizedBoundaryCoordinate_prime_iff x).1
        hcertificate.1

end

end RHTower
