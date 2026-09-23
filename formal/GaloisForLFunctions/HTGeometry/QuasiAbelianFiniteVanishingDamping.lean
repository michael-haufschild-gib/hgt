import GaloisForLFunctions.HTGeometry.QuasiAbelianVanishingDampingFamily

/-!
# The damping majorant from vanishing on a finite disc

Exact vanishing at *every* nonzero complement translate is more than the interface needs, and more
than a finite packet can supply: the induction hypothesis of the card gives jet ampleness of the
lower factor at a *finite* packet, so vanishing can only be prescribed on a finite set of
translates.

The Gaussian factor of the automorphy weight supplies the rest.  Split the decay exponent
`σ₀ = (σ₀ − σ₁) + σ₁`.  On the complement of a disc of squared radius `Z B` the first half already
costs `exp(−(σ₀ − σ₁)·Z B)`, so as soon as `δ·B ≤ (σ₀ − σ₁)·Z B` — that is, radius `≍ √(δB/σ)` —
the required `exp(−δB)` is available, and the second half is exactly the Gaussian lattice weight of
the majorant.  Vanishing is therefore needed only inside the disc, and the seed's own bound is
allowed to grow polynomially in `B`.

* `polynomialGaussianLatticeWeight_zero_exponent` — the weight with no polynomial factor;
* `abeDampingMajorant_of_finite_vanishing`;
* `AbeDampingPacketData.ofFiniteVanishing`.
-/

open Filter Function Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

theorem polynomialGaussianLatticeWeight_zero_exponent (ι : Type) [Fintype ι] (s : ℝ)
    (z : ι → ℤ) :
    polynomialGaussianLatticeWeight ι (fun _ => 0) (fun _ => s) z
      = Real.exp (-s * ∑ i, ((z i : ℝ)) ^ (2 : ℕ)) := by
  rw [polynomialGaussianLatticeWeight, Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [pow_zero, one_mul]

/-- **The damping majorant from vanishing on a disc of squared radius `Z B`.**  Outside the disc
the seed's Gaussian decay is split: the excess over the majorant's own Gaussian pays the required
`exp(−δB)` exactly when `δ·B ≤ (σ₀ − σ₁)·Z B`. -/
theorem abeDampingMajorant_of_finite_vanishing {d c : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    {upper : AutomorphicFactor d Γ}
    {I : Type u} [Fintype I] [DecidableEq I] {w : I → Fin d → ℂ} {m : I → ℕ}
    {comp : (Fin c → ℤ) →+ (Fin d → ℂ)} (comp_mem : ∀ z, comp z ∈ Γ)
    (seed : ℝ → FiniteJetPacketIndex d I m → MultivariateEntire d)
    {sigma0 sigma1 delta C0 : ℝ} {r : ℕ} {Z : ℝ → ℝ}
    (hsigma1 : 0 < sigma1) (hsigma : sigma1 < sigma0) (hdelta : 0 < delta) (hC0 : 0 ≤ C0)
    (hbound : ∀ B : ℝ, 0 ≤ B → ∀ (z : Fin c → ℤ) (i j : FiniteJetPacketIndex d I m),
      ‖multiIndexJetEvalCLM (w i.1) i.2.1
          (poincareTermEntire upper (seed B j) (complementEmbedding comp comp_mem z))‖
        ≤ C0 * B ^ r * Real.exp (-sigma0 * ∑ k, ((z k : ℝ)) ^ (2 : ℕ)))
    (hvanish : ∀ B : ℝ, 0 ≤ B → ∀ (z : Fin c → ℤ) (i j : FiniteJetPacketIndex d I m), z ≠ 0 →
      (∑ k, ((z k : ℝ)) ^ (2 : ℕ)) ≤ Z B →
      multiIndexJetEvalCLM (w i.1) i.2.1
          (poincareTermEntire upper (seed B j) (complementEmbedding comp comp_mem z)) = 0)
    (hZ : ∀ B : ℝ, 0 ≤ B → delta * B ≤ (sigma0 - sigma1) * Z B) :
    ∃ (A : Fin c → ℕ) (sigma : Fin c → ℝ) (r' : ℕ) (delta' C : ℝ),
      (∀ i, 0 < sigma i) ∧ 0 < delta' ∧ 0 ≤ C ∧
      ∀ B : ℝ, 0 ≤ B → ∀ (z : Fin c → ℤ) (i j : FiniteJetPacketIndex d I m), z ≠ 0 →
        ‖multiIndexJetEvalCLM (w i.1) i.2.1
            (poincareTermEntire upper (seed B j) (complementEmbedding comp comp_mem z))‖
          ≤ (C * (B ^ r' * Real.exp (-(delta' * B)))) *
              polynomialGaussianLatticeWeight (Fin c) A sigma z := by
  refine ⟨fun _ => 0, fun _ => sigma1, r, delta, C0, fun _ => hsigma1, hdelta, hC0, ?_⟩
  intro B hB z i j hz
  set s : ℝ := ∑ k, ((z k : ℝ)) ^ (2 : ℕ) with hs
  rw [polynomialGaussianLatticeWeight_zero_exponent]
  by_cases hin : s ≤ Z B
  · rw [hvanish B hB z i j hz hin, norm_zero]
    have h1 : (0 : ℝ) ≤ C0 * (B ^ r * Real.exp (-(delta * B))) :=
      mul_nonneg hC0 (mul_nonneg (pow_nonneg hB r) (Real.exp_nonneg _))
    exact mul_nonneg h1 (Real.exp_nonneg _)
  · push Not at hin
    have hsplit : -sigma0 * s = -((sigma0 - sigma1) * s) + -sigma1 * s := by ring
    have hexp : Real.exp (-sigma0 * s)
        = Real.exp (-((sigma0 - sigma1) * s)) * Real.exp (-sigma1 * s) := by
      rw [hsplit, Real.exp_add]
    have hgap : delta * B ≤ (sigma0 - sigma1) * s := by
      refine le_trans (hZ B hB) ?_
      exact mul_le_mul_of_nonneg_left (le_of_lt hin) (by linarith)
    have hkey : Real.exp (-((sigma0 - sigma1) * s)) ≤ Real.exp (-(delta * B)) :=
      Real.exp_le_exp.mpr (by linarith)
    calc ‖multiIndexJetEvalCLM (w i.1) i.2.1
            (poincareTermEntire upper (seed B j) (complementEmbedding comp comp_mem z))‖
        ≤ C0 * B ^ r * Real.exp (-sigma0 * s) := hbound B hB z i j
      _ = (C0 * B ^ r * Real.exp (-((sigma0 - sigma1) * s))) * Real.exp (-sigma1 * s) := by
          rw [hexp]; ring
      _ ≤ (C0 * B ^ r * Real.exp (-(delta * B))) * Real.exp (-sigma1 * s) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
          exact mul_le_mul_of_nonneg_left hkey (mul_nonneg hC0 (pow_nonneg hB r))
      _ = (C0 * (B ^ r * Real.exp (-(delta * B)))) * Real.exp (-sigma1 * s) := by ring

/-- **A damping packet datum from vanishing on a finite disc.** -/
def AbeDampingPacketData.ofFiniteVanishing {d c : ℕ} {ΓH Γ : AddSubgroup (Fin d → ℂ)}
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
    {sigma0 sigma1 delta C0 : ℝ} {r : ℕ} {Z : ℝ → ℝ}
    (hsigma1 : 0 < sigma1) (hsigma : sigma1 < sigma0) (hdelta : 0 < delta) (hC0 : 0 ≤ C0)
    (hbound : ∀ B : ℝ, 0 ≤ B → ∀ (z : Fin c → ℤ) (i j : FiniteJetPacketIndex d I m),
      ‖multiIndexJetEvalCLM (w i.1) i.2.1
          (poincareTermEntire upper (seed B j) (complementEmbedding comp comp_mem z))‖
        ≤ C0 * B ^ r * Real.exp (-sigma0 * ∑ k, ((z k : ℝ)) ^ (2 : ℕ)))
    (hvanish : ∀ B : ℝ, 0 ≤ B → ∀ (z : Fin c → ℤ) (i j : FiniteJetPacketIndex d I m), z ≠ 0 →
      (∑ k, ((z k : ℝ)) ^ (2 : ℕ)) ≤ Z B →
      multiIndexJetEvalCLM (w i.1) i.2.1
          (poincareTermEntire upper (seed B j) (complementEmbedding comp comp_mem z)) = 0)
    (hZ : ∀ B : ℝ, 0 ≤ B → delta * B ≤ (sigma0 - sigma1) * Z B) :
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
  majorant :=
    abeDampingMajorant_of_finite_vanishing comp_mem seed hsigma1 hsigma hdelta hC0 hbound
      hvanish hZ

end

end GaloisForLFunctions.HTGeometry
