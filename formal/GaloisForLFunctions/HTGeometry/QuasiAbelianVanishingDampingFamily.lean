import GaloisForLFunctions.HTGeometry.QuasiAbelianDampedLiftConstruction

/-!
# The damping majorant from exact vanishing of the complement jets

`AbeDampingPacketData.majorant` bounds the *packet jets* of the complement Poincaré terms, not the
terms themselves.  So a seed whose complement translates vanish to the packet order satisfies it
exactly, with constant `0`: the bound is then `0 ≤ 0`, with no `B`-dependence at all.

This is worth isolating, because it changes the shape of the analytic obligation.  What has to be
constructed is not a damping multiplier — a `ΓH`-invariant entire multiplier is a holomorphic
function on the toroidal quotient `ℂ^d/ΓH`, hence constant when that quotient is toroidal, and
otherwise a character whose modulus is *linear* in the complement index and therefore grows on half
of the complement lattice — but a family of lower-automorphic seeds with the prescribed packet jets
whose complement translates vanish there.

* `abeDampingMajorant_of_jet_vanishing` — the majorant from vanishing;
* `AbeDampingPacketData.ofVanishing` — the packet datum from vanishing.
-/

open Filter Function Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

theorem abeDampingMajorant_of_jet_vanishing {d c : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    {upper : AutomorphicFactor d Γ}
    {I : Type u} [Fintype I] [DecidableEq I] {w : I → Fin d → ℂ} {m : I → ℕ}
    {comp : (Fin c → ℤ) →+ (Fin d → ℂ)} (comp_mem : ∀ z, comp z ∈ Γ)
    (seed : ℝ → FiniteJetPacketIndex d I m → MultivariateEntire d)
    (hvanish : ∀ (B : ℝ) (z : Fin c → ℤ) (i j : FiniteJetPacketIndex d I m), z ≠ 0 →
      multiIndexJetEvalCLM (w i.1) i.2.1
          (poincareTermEntire upper (seed B j) (complementEmbedding comp comp_mem z)) = 0) :
    ∃ (A : Fin c → ℕ) (sigma : Fin c → ℝ) (r : ℕ) (delta C : ℝ),
      (∀ i, 0 < sigma i) ∧ 0 < delta ∧ 0 ≤ C ∧
      ∀ B : ℝ, 0 ≤ B → ∀ (z : Fin c → ℤ) (i j : FiniteJetPacketIndex d I m), z ≠ 0 →
        ‖multiIndexJetEvalCLM (w i.1) i.2.1
            (poincareTermEntire upper (seed B j) (complementEmbedding comp comp_mem z))‖
          ≤ (C * (B ^ r * Real.exp (-(delta * B)))) *
              polynomialGaussianLatticeWeight (Fin c) A sigma z := by
  refine ⟨fun _ => 0, fun _ => 1, 0, 1, 0, fun _ => zero_lt_one, zero_lt_one, le_rfl, ?_⟩
  intro B _ z i j hz
  rw [hvanish B z i j hz, norm_zero, zero_mul, zero_mul]

/-- **A damping packet datum from exact vanishing of the complement packet jets.** -/
def AbeDampingPacketData.ofVanishing {d c : ℕ} {ΓH Γ : AddSubgroup (Fin d → ℂ)}
    {lower : AutomorphicFactor d ΓH} {upper : AutomorphicFactor d Γ}
    {I : Type u} [Fintype I] [DecidableEq I] {w : I → Fin d → ℂ} {m : I → ℕ}
    {lowerColumn : FiniteJetPacketIndex d I m → lower.forms}
    (le : ΓH ≤ Γ)
    (compat : ∀ (η : Fin d → ℂ) (hη : η ∈ ΓH),
      (upper.factor ⟨η, le hη⟩).1 = (lower.factor ⟨η, hη⟩).1)
    (comp : (Fin c → ℤ) →+ (Fin d → ℂ)) (comp_mem : ∀ z, comp z ∈ Γ)
    (decomp : ∀ δ ∈ Γ, ∃ η ∈ ΓH, ∃ z : Fin c → ℤ, δ = η + comp z)
    (seed : ℝ → FiniteJetPacketIndex d I m → MultivariateEntire d)
    (seed_mem : ∀ B j, seed B j ∈ lower.forms)
    (seed_jet : ∀ (B : ℝ) (i j : FiniteJetPacketIndex d I m),
      multiIndexJetEvalCLM (w i.1) i.2.1 (seed B j)
        = multiIndexJetEvalCLM (w i.1) i.2.1 (lowerColumn j).1)
    (normal : ∀ (B : ℝ) (j : FiniteJetPacketIndex d I m), SummableLocallyUniformlyOn
      (fun z : Fin c → ℤ =>
        poincareTerm upper (seed B j) (complementEmbedding comp comp_mem z)) Set.univ)
    (hvanish : ∀ (B : ℝ) (z : Fin c → ℤ) (i j : FiniteJetPacketIndex d I m), z ≠ 0 →
      multiIndexJetEvalCLM (w i.1) i.2.1
          (poincareTermEntire upper (seed B j) (complementEmbedding comp comp_mem z)) = 0) :
    AbeDampingPacketData (c := c) lower upper w m lowerColumn where
  le := le
  compat := compat
  comp := comp
  comp_mem := comp_mem
  decomp := decomp
  seed := seed
  seed_mem := seed_mem
  seed_jet := seed_jet
  normal := normal
  majorant := abeDampingMajorant_of_jet_vanishing comp_mem seed hvanish

end

end GaloisForLFunctions.HTGeometry
