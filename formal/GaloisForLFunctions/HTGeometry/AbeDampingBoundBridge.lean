import GaloisForLFunctions.HTGeometry.AbePoincareLocalNormal

/-!
# The damping bound in the shape the finite-vanishing majorant consumes

`abeDampingMajorant_of_finite_vanishing` asks for the packet jets of the complement Poincaré terms
to satisfy `‖jet‖ ≤ C₀·B^r·exp(−σ₀ ∑ z_k²)`.  For Appell--Humbert data that is now a theorem: the
Cauchy estimate at unit radius turns a sup bound on one ball into every packet jet, the difference
form supplies the Gaussian in the form value, and Abe positivity converts it into the Gaussian in
the lattice coordinates.

The seed family is only required to satisfy a sup bound `C_s·B^r` on a single ball around each
packet point — which is what the induction hypothesis supplies.

* `abeDampingBound_of_appellHumbert` — **the hypothesis `hbound` of the finite-vanishing majorant**;
* `appellHumbertAutomorphicFactor_compat` — the `compat` field of the damping datum.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {d c : ℕ}

/-- **The damping bound for Appell--Humbert data.** -/
theorem abeDampingBound_of_appellHumbert
    {Hu Hl : (Fin d → ℂ) → (Fin d → ℂ) → ℂ} {χu : (Fin d → ℂ) → ℂ}
    (hHu : IsHermitianForm Hu) (hHl : IsHermitianForm Hl)
    (hχu : ∀ γ, ‖χu γ‖ = 1)
    (hpos : ∀ y : Fin d → ℂ, 0 ≤ (Hu y y - Hl y y).re)
    {Γ : AddSubgroup (Fin d → ℂ)}
    (hsemiu : ∀ γ γ' : Fin d → ℂ, χu (γ + γ')
      = χu γ * χu γ' * Complex.exp (-((Real.pi : ℂ) * Complex.I * ((Hu γ γ').im : ℝ))))
    {I : Type*} [Fintype I] [DecidableEq I] {w : I → Fin d → ℂ} {m : I → ℕ}
    (seed : ℝ → FiniteJetPacketIndex d I m → MultivariateEntire d)
    (v : Fin c → (Fin d → ℂ))
    (hgram : (abeGram (fun x y => Hu x y - Hl x y) v).PosDef)
    (comp : (Fin c → ℤ) →+ (Fin d → ℂ)) (comp_mem : ∀ z, comp z ∈ Γ)
    (hcomp : ∀ z : Fin c → ℤ, comp z = ∑ i, ((z i : ℂ)) • v i)
    {Rad C₀ L Cs : ℝ} {r : ℕ} (hC₀ : 0 ≤ C₀) (hCs : 0 ≤ Cs)
    (hrad : ∀ i : FiniteJetPacketIndex d I m,
      ((Fintype.card (MultiIndexSlot i.2.1) : ℕ) : ℝ) ≤ Rad)
    (hDsup : ∀ (i : FiniteJetPacketIndex d I m) (y : Fin d → ℂ),
      ‖y - w i.1‖ ≤ Rad → (Hu y y - Hl y y).re ≤ C₀ ^ 2)
    (hLsup : ∀ (i : FiniteJetPacketIndex d I m) (y : Fin d → ℂ),
      ‖y - w i.1‖ ≤ Rad → (Hl y y).re ≤ L)
    (hseednorm : ∀ B : ℝ, 0 ≤ B → ∀ (j : FiniteJetPacketIndex d I m) (y : Fin d → ℂ),
      ‖(seed B j).1 y‖ ≤ Cs * B ^ r * Real.exp (Real.pi / 2 * (Hl y y).re)) :
    ∃ sigma0 : ℝ, 0 < sigma0 ∧ ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ B : ℝ, 0 ≤ B → ∀ (z : Fin c → ℤ) (i j : FiniteJetPacketIndex d I m),
        ‖multiIndexJetEvalCLM (w i.1) i.2.1
            (poincareTermEntire (appellHumbertAutomorphicFactor hHu hχu hsemiu Γ) (seed B j)
              (complementEmbedding comp comp_mem z))‖
          ≤ C0 * B ^ r * Real.exp (-sigma0 * ∑ k, ((z k : ℝ)) ^ 2) := by
  have hD : IsHermitianForm fun x y => Hu x y - Hl x y := hHu.sub hHl
  obtain ⟨sigma, hsigma, hgauss⟩ :=
    exists_gaussian_of_posDef hD v hgram (t := Real.pi / 4) (by positivity)
  refine ⟨sigma, hsigma, Cs * Real.exp (Real.pi / 2 * L) * Real.exp (Real.pi * C₀ ^ 2),
    by positivity, ?_⟩
  intro B hB z i j
  have hball : ∀ y : Fin d → ℂ,
      ‖y - w i.1‖ ≤ ((Fintype.card (MultiIndexSlot i.2.1) : ℕ) : ℝ) * 1 → ‖y - w i.1‖ ≤ Rad := by
    intro y hy
    rw [mul_one] at hy
    exact le_trans hy (hrad i)
  have hbase := norm_multiIndexJetEvalCLM_poincareTerm_appellHumbert_le hHu hHl hχu hpos hC₀
    hsemiu (seed B j) (hseednorm B hB j) (w i.1) i.2.1 (ρ := 1) one_pos
    (fun y hy => hDsup i y (hball y hy)) (fun y hy => hLsup i y (hball y hy))
    (complementEmbedding comp comp_mem z)
  rw [one_pow, div_one] at hbase
  set F : ℝ := Real.exp (-sigma * ∑ k, ((z k : ℝ)) ^ 2) with hFdef
  have hexp : Real.exp (-(Real.pi / 4)
      * (Hu (complementEmbedding comp comp_mem z).1 (complementEmbedding comp comp_mem z).1
          - Hl (complementEmbedding comp comp_mem z).1
              (complementEmbedding comp comp_mem z).1).re) ≤ F := by
    have h := hgauss z
    rw [show (∑ t, ((z t : ℂ)) • v t) = (complementEmbedding comp comp_mem z).1 from
      (hcomp z).symm] at h
    exact h
  have hnn : (0 : ℝ) ≤ Cs * B ^ r * Real.exp (Real.pi / 2 * L)
      * Real.exp (Real.pi * C₀ ^ 2) := by positivity
  refine le_trans hbase ?_
  calc Cs * B ^ r * Real.exp (Real.pi / 2 * L) * Real.exp (Real.pi * C₀ ^ 2)
        * Real.exp (-(Real.pi / 4)
          * (Hu (complementEmbedding comp comp_mem z).1 (complementEmbedding comp comp_mem z).1
            - Hl (complementEmbedding comp comp_mem z).1
                (complementEmbedding comp comp_mem z).1).re)
      ≤ Cs * B ^ r * Real.exp (Real.pi / 2 * L) * Real.exp (Real.pi * C₀ ^ 2) * F :=
        mul_le_mul_of_nonneg_left hexp hnn
    _ = Cs * Real.exp (Real.pi / 2 * L) * Real.exp (Real.pi * C₀ ^ 2) * B ^ r * F := by ring

/-- **The compatibility field of the damping datum, for Appell--Humbert factors.**  The upper factor
restricts to the lower one along `ΓH` exactly when the two forms and the two semicharacters agree
there. -/
theorem appellHumbertAutomorphicFactor_compat
    {Hu Hl : (Fin d → ℂ) → (Fin d → ℂ) → ℂ} {χu χl : (Fin d → ℂ) → ℂ}
    (hHu : IsHermitianForm Hu) (hχu : ∀ γ, ‖χu γ‖ = 1)
    (hsemiu : ∀ γ γ' : Fin d → ℂ, χu (γ + γ')
      = χu γ * χu γ' * Complex.exp (-((Real.pi : ℂ) * Complex.I * ((Hu γ γ').im : ℝ))))
    (hHl : IsHermitianForm Hl) (hχl : ∀ γ, ‖χl γ‖ = 1)
    (hsemil : ∀ γ γ' : Fin d → ℂ, χl (γ + γ')
      = χl γ * χl γ' * Complex.exp (-((Real.pi : ℂ) * Complex.I * ((Hl γ γ').im : ℝ))))
    {ΓH Γ : AddSubgroup (Fin d → ℂ)} (hle : ΓH ≤ Γ)
    (hH : ∀ η ∈ ΓH, ∀ x : Fin d → ℂ, Hu x η = Hl x η)
    (hχ : ∀ η ∈ ΓH, χu η = χl η) :
    ∀ (η : Fin d → ℂ) (hη : η ∈ ΓH),
      ((appellHumbertAutomorphicFactor hHu hχu hsemiu Γ).factor ⟨η, hle hη⟩).1
        = ((appellHumbertAutomorphicFactor hHl hχl hsemil ΓH).factor ⟨η, hη⟩).1 := by
  intro η hη
  ext x
  show appellHumbertFactor Hu χu η x = appellHumbertFactor Hl χl η x
  rw [appellHumbertFactor, appellHumbertFactor, hχ η hη, hH η hη x, hH η hη η]

end

end GaloisForLFunctions.HTGeometry
