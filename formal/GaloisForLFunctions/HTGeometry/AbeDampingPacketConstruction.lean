import GaloisForLFunctions.HTGeometry.AbeDampingBoundBridge
import GaloisForLFunctions.HTGeometry.AbePoincareLocalNormal
import GaloisForLFunctions.HTGeometry.QuasiAbelianFiniteVanishingDamping

/-!
# The damping datum for Appell--Humbert factors

Assembling every field of `AbeDampingPacketData` for a pair of Appell--Humbert factors.  The two
analytic fields are theorems: `normal` is the M-test through the Gaussian lattice weight, and
`majorant` is the finite-vanishing majorant fed by the Appell--Humbert bound.  The rest is the data
of the induction step itself — the two period groups and their complement, and the seed family
supplied by jet ampleness of the lower factor.

The seed hypothesis is a bound on the **normalised modulus**, the quantity that is periodic for the
lower period group; nothing is assumed about the seed at the complement translates.

* `abeDampingPacketDataAppellHumbert` — **the damping datum**;
* `hasAbeDampingFamily_appellHumbert` — the damping family, given the datum for every packet.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {d c : ℕ} {Hu Hl : (Fin d → ℂ) → (Fin d → ℂ) → ℂ} {χu χl : (Fin d → ℂ) → ℂ}

/-- **The damping datum for a pair of Appell--Humbert factors.** -/
def abeDampingPacketDataAppellHumbert
    {ΓH Γ : AddSubgroup (Fin d → ℂ)}
    (hHu : IsHermitianForm Hu) (hχu : ∀ γ, ‖χu γ‖ = 1)
    (hsemiu : IsSemicharacterOn Hu χu Γ)
    (hHl : IsHermitianForm Hl) (hχl : ∀ γ, ‖χl γ‖ = 1)
    (hsemil : IsSemicharacterOn Hl χl ΓH) (hle : ΓH ≤ Γ)
    (hH : ∀ η ∈ ΓH, ∀ x : Fin d → ℂ, Hu x η = Hl x η) (hχ : ∀ η ∈ ΓH, χu η = χl η)
    (hpos : ∀ y : Fin d → ℂ, 0 ≤ (Hu y y - Hl y y).re)
    (v : Fin c → (Fin d → ℂ))
    (hgram : (abeGram (fun x y => Hu x y - Hl x y) v).PosDef)
    (comp : (Fin c → ℤ) →+ (Fin d → ℂ)) (comp_mem : ∀ z, comp z ∈ Γ)
    (hcomp : ∀ z : Fin c → ℤ, comp z = ∑ i, ((z i : ℂ)) • v i)
    (hdecomp : ∀ δ ∈ Γ, ∃ η ∈ ΓH, ∃ z : Fin c → ℤ, δ = η + comp z)
    {I : Type u} [Fintype I] [DecidableEq I] {w : I → Fin d → ℂ} {m : I → ℕ}
    (lowerColumn : FiniteJetPacketIndex d I m →
      (appellHumbertAutomorphicFactor hHl hχl hsemil).forms)
    (seed : ℝ → FiniteJetPacketIndex d I m → MultivariateEntire d)
    (seed_mem : ∀ B j, seed B j ∈ (appellHumbertAutomorphicFactor hHl hχl hsemil).forms)
    (seed_jet : ∀ (B : ℝ) (i j : FiniteJetPacketIndex d I m),
      multiIndexJetEvalCLM (w i.1) i.2.1 (seed B j)
        = multiIndexJetEvalCLM (w i.1) i.2.1 (lowerColumn j).1)
    (seed_normalised : ∀ (B : ℝ) (j : FiniteJetPacketIndex d I m), ∃ M : ℝ,
      ∀ y : Fin d → ℂ, ‖(seed B j).1 y‖ ≤ M * Real.exp (Real.pi / 2 * (Hl y y).re))
    {Rad C₀ L Cs : ℝ} {r : ℕ} (hC₀ : 0 ≤ C₀) (hCs : 0 ≤ Cs)
    (hrad : ∀ i : FiniteJetPacketIndex d I m,
      ((Fintype.card (MultiIndexSlot i.2.1) : ℕ) : ℝ) ≤ Rad)
    (hDsup : ∀ (i : FiniteJetPacketIndex d I m) (y : Fin d → ℂ),
      ‖y - w i.1‖ ≤ Rad → (Hu y y - Hl y y).re ≤ C₀ ^ (2 : ℕ))
    (hLsup : ∀ (i : FiniteJetPacketIndex d I m) (y : Fin d → ℂ),
      ‖y - w i.1‖ ≤ Rad → (Hl y y).re ≤ L)
    (hseednorm : ∀ B : ℝ, 0 ≤ B → ∀ (j : FiniteJetPacketIndex d I m) (y : Fin d → ℂ),
      ‖(seed B j).1 y‖ ≤ Cs * B ^ r * Real.exp (Real.pi / 2 * (Hl y y).re))
    {kappa : ℝ} (hkappa : 0 < kappa) {Z : ℝ → ℝ} (hZ : ∀ B : ℝ, 0 ≤ B → kappa * B ≤ Z B)
    (hvanish : ∀ B : ℝ, 0 ≤ B → ∀ (z : Fin c → ℤ) (i j : FiniteJetPacketIndex d I m), z ≠ 0 →
      (∑ k, ((z k : ℝ)) ^ (2 : ℕ)) ≤ Z B →
      multiIndexJetEvalCLM (w i.1) i.2.1
          (poincareTermEntire (appellHumbertAutomorphicFactor hHu hχu hsemiu) (seed B j)
            (complementEmbedding comp comp_mem z)) = 0) :
    AbeDampingPacketData (c := c) (appellHumbertAutomorphicFactor hHl hχl hsemil)
      (appellHumbertAutomorphicFactor hHu hχu hsemiu) w m lowerColumn where
  le := hle
  compat := appellHumbertAutomorphicFactor_compat hHu hχu hsemiu hHl hχl hsemil hle hH hχ
  comp := comp
  comp_mem := comp_mem
  decomp := hdecomp
  seed := seed
  seed_mem := seed_mem
  seed_jet := seed_jet
  normal := by
    intro B j
    obtain ⟨M, hM⟩ := seed_normalised B j
    exact summableLocallyUniformlyOn_poincareTerm_appellHumbert hHu hHl hχu hpos hsemiu
      (seed B j) hM v hgram comp comp_mem hcomp
  majorant := by
    obtain ⟨sigma0, hsigma0, C0, hC0, hbound⟩ :=
      abeDampingBound_of_appellHumbert hHu hHl hχu hpos hsemiu seed v hgram comp comp_mem hcomp
        hC₀ hCs hrad hDsup hLsup hseednorm
    refine abeDampingMajorant_of_finite_vanishing comp_mem seed
      (sigma1 := sigma0 / 2) (sigma0 := sigma0) (delta := sigma0 / 2 * kappa)
      (by positivity) (by linarith) (by positivity) hC0 hbound hvanish ?_
    intro B hB
    have hZB := hZ B hB
    have hhalf : sigma0 - sigma0 / 2 = sigma0 / 2 := by ring
    rw [hhalf]
    calc sigma0 / 2 * kappa * B = sigma0 / 2 * (kappa * B) := by ring
      _ ≤ sigma0 / 2 * Z B := by
          refine mul_le_mul_of_nonneg_left hZB (by positivity)

end

end GaloisForLFunctions.HTGeometry
