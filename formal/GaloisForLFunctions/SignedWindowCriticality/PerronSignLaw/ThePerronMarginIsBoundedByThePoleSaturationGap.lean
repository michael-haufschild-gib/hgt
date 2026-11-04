import GaloisForLFunctions.SignedWindowCriticality.PerronSignLaw.TheEvenSectorIsMarkovUpToThePlasticThreshold
import GaloisForLFunctions.SignedWindowCriticality.PrimeThreeEntry.TheNewestPrimeEntersSoftly

/-!
# The Perron margin is bounded by the pole saturation gap

On the half-window `[−c, 0]` the even band is a pole family `E_s = E_0 + s·P`,
`P(f) = (∫ f h)²`, `h = 2cosh(·/2)` (pole `κ|ch⟩⟨ch|` with `κ = 4s`, arithmetic `s = 1`), and the
odd band is a kick family `O_t = O_0 + t·K`, `K(f) = w₂(f⋆f)(−log 2) + w₃(f⋆f)(−log 3)`
(arithmetic `t = 1`). An argument proving Perron robustly in the frustration strength proves it at
some `s₁ > s₀` (resp. `t₁ > t₀`). Variationally this costs:

* `margin_mul_le` — for any family `Q_t = Q₀ + tK`, a lower bound `λ` of `Q_{t₀}` and an
  `ε`-ground state `ψ` of `Q_{t₁}` measured against a competitor `g`:
  `(t₁ − t₀) K(ψ) ≤ Q_{t₁}(g) − λ + ε`. `positivity_margin_le` is the lower side.
* The pole saturates on the hyperplane `∫ g h = 0`: there `E_s(g) = E_1(g)` for every `s`
  (`evenPoleBand_of_poleHyperplane`), and every nonzero test there changes sign
  (`exists_neg_of_poleHyperplane`).
* `evenPerronMargin_le` — `(s₁ − s₀) P(ψ) ≤ E_1(g) − λ + ε`: the pole margin is the saturation gap
  over the pole moment of the ground state.
* Perron turns the pole moment into mass, `4(∫ψ)² ≤ P(ψ)`, and mass into height,
  `(∫ψ²)² ≤ M²(∫ψ)²` for `0 ≤ ψ ≤ M`. Hence `evenPerronMargin_le_sup`:
  `4(s₁ − s₀) ≤ M²(E_1(g) − λ + ε)` for a normalized Perron `ε`-ground state, and the no-go
  `exists_neg_of_evenMargin_gt`: past this margin the ground state changes sign.
* `evenPositivityMargin_le_sup` — positivity at a weaker pole `s_w` forces
  `4(s₀ − s_w) ≤ M² E_{s₀}(ψ)` at every normalized Perron test: the arithmetic pole lies within
  `O(λ₀)` of the positivity threshold.
* `oddPerronMargin_le` — against a kick-free competitor `(t₁ − t₀) K(ψ)` is at most the gap, and
  `K(ψ) ≥ 0` for Perron `ψ` (`kickEnergy_nonneg`): a robust kick margin forces the ground state to
  decouple the reflected pairs of the slivers.
-/

open Real MeasureTheory Set Filter

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality.PerronSignLaw

open GaloisForLFunctions.SignedWindowCriticality
open GaloisForLFunctions.SignedWindowCriticality.PrimeThreeEntry
open SpacingScaleHarmonicAnalysis

/-! ### 1. The margin law for a one-parameter family -/

/-- **The margin law.** For `Q_t = Q₀ + tK` with norm square `N`: if `λ N ≤ Q_{t₀}` at `ψ`,
`N ψ = 1`, and `ψ` is an `ε`-minimizer of `Q_{t₁}` against the competitor `g`, then
`(t₁ − t₀) K(ψ) ≤ Q_{t₁}(g) − λ + ε`. -/
theorem margin_mul_le {V : Type*} (Q₀ K N : V → ℝ) {t₀ t₁ lam ε : ℝ} {ψ g : V}
    (hlow : lam * N ψ ≤ Q₀ ψ + t₀ * K ψ) (hψ : N ψ = 1)
    (hmin : Q₀ ψ + t₁ * K ψ ≤ Q₀ g + t₁ * K g + ε) :
    (t₁ - t₀) * K ψ ≤ Q₀ g + t₁ * K g - lam + ε := by
  rw [hψ, mul_one] at hlow
  have e : (t₁ - t₀) * K ψ = (Q₀ ψ + t₁ * K ψ) - (Q₀ ψ + t₀ * K ψ) := by ring
  rw [e]
  linarith

/-- **The positivity margin.** If `Q_{t_w} ≥ 0` at `ψ`, then `(t₀ − t_w) K(ψ) ≤ Q_{t₀}(ψ)`. -/
theorem positivity_margin_le {V : Type*} (Q₀ K : V → ℝ) {tw t₀ : ℝ} {ψ : V}
    (hpos : 0 ≤ Q₀ ψ + tw * K ψ) : (t₀ - tw) * K ψ ≤ Q₀ ψ + t₀ * K ψ := by
  have e : (t₀ - tw) * K ψ = (Q₀ ψ + t₀ * K ψ) - (Q₀ ψ + tw * K ψ) := by ring
  rw [e]
  linarith

/-! ### 2. The even pole family -/

/-- The pole square `P(f) = (∫ f h)²`, `h(u) = 2cosh(u/2)`. -/
def poleSquare (f : ℝ → ℝ) : ℝ := (∫ u, f u * coshWeight u) ^ 2

/-- The even band at pole strength `s`:
`W + 𝓗₀ + (s − 1)P − w₂(f⋆f)(−log 2) − w₃(f⋆f)(−log 3)`. In kernel form (`evenSector_eq`) it is
`Γ‖f‖² + 𝒥(f) + s·P(f) − Σ_j ν_j(f)² − primes`; `s = 1` is the arithmetic pole `4|ch⟩⟨ch|`. -/
def evenPoleBand (w₂ w₃ s : ℝ) (f : ℝ → ℝ) : ℝ :=
  weilQuad f + collarHankel 0 f + (s - 1) * poleSquare f -
    w₂ * selfConv f (-Real.log 2) - w₃ * selfConv f (-Real.log 3)

/-- The pole family is affine in the strength: `E_s = E_0 + s·P`. -/
theorem evenPoleBand_eq_add (w₂ w₃ s : ℝ) (f : ℝ → ℝ) :
    evenPoleBand w₂ w₃ s f = evenPoleBand w₂ w₃ 0 f + s * poleSquare f := by
  unfold evenPoleBand; ring

/-- At the arithmetic strength the pole family is the even band. -/
theorem evenPoleBand_one (w₂ w₃ : ℝ) (f : ℝ → ℝ) :
    evenPoleBand w₂ w₃ 1 f = weilQuad f + collarHankel 0 f - w₂ * selfConv f (-Real.log 2) -
      w₃ * selfConv f (-Real.log 3) := by
  unfold evenPoleBand; ring

/-- The even weight set is the nonnegativity of the arithmetic pole band. -/
theorem mem_evenBandWeights_iff {c w₂ w₃ : ℝ} :
    (w₂, w₃) ∈ evenBandWeights c ↔
      ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -c → f u = 0) →
        0 ≤ evenPoleBand w₂ w₃ 1 f := by
  refine forall_congr' fun f => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => ?_
  dsimp only
  rw [evenPoleBand_one]
  constructor <;> intro h <;> linarith

/-- On the pole hyperplane `∫ g h = 0` the band does not see the pole strength. -/
theorem evenPoleBand_of_poleHyperplane {g : ℝ → ℝ} (hg : ∫ u, g u * coshWeight u = 0)
    (w₂ w₃ s : ℝ) : evenPoleBand w₂ w₃ s g = evenPoleBand w₂ w₃ 1 g := by
  have hP : poleSquare g = 0 := by rw [poleSquare, hg]; ring
  unfold evenPoleBand; rw [hP]; ring

/-- **The saturated level is not Perron**: a nonzero continuous compactly supported test on the
pole hyperplane is negative somewhere. -/
theorem exists_neg_of_poleHyperplane {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {u₀ : ℝ} (hu₀ : g u₀ ≠ 0) (h : ∫ u, g u * coshWeight u = 0) : ∃ u, g u < 0 := by
  by_contra hneg
  push Not at hneg
  have hcw0 : ∀ u, 0 < coshWeight u := fun u => by unfold coshWeight; positivity
  have hpos : 0 < ∫ u, g u * coshWeight u :=
    (hg.mul (by unfold coshWeight; fun_prop)).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hgc.mono fun u hu h0 => hu (by simp [h0]))
      (fun u => mul_nonneg (hneg u) (hcw0 u).le) (mul_ne_zero hu₀ (hcw0 u₀).ne')
  linarith

/-! ### 3. Perron turns the pole moment into mass and height -/

/-- `4(∫ψ)² ≤ P(ψ)` for `ψ ≥ 0`, since `h ≥ 2`. -/
theorem four_mul_sq_integral_le_poleSquare {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hψ0 : ∀ u, 0 ≤ ψ u) :
    4 * (∫ u, ψ u) ^ 2 ≤ poleSquare ψ := by
  have hI : Integrable ψ := hψ.integrable_of_hasCompactSupport hψc
  have hIh : Integrable fun u => ψ u * coshWeight u :=
    (hψ.mul (by unfold coshWeight; fun_prop)).integrable_of_hasCompactSupport
      (hψc.mono fun u hu h0 => hu (by simp [h0]))
  have h2 : 2 * (∫ u, ψ u) ≤ ∫ u, ψ u * coshWeight u := by
    rw [← integral_const_mul]
    refine integral_mono (hI.const_mul 2) hIh fun u => ?_
    show 2 * ψ u ≤ ψ u * coshWeight u
    have : 2 ≤ coshWeight u := by unfold coshWeight; linarith [Real.one_le_cosh (u / 2)]
    nlinarith [hψ0 u]
  have hI0 : 0 ≤ ∫ u, ψ u := integral_nonneg fun u => hψ0 u
  have h0 : 0 ≤ 2 * ∫ u, ψ u := by linarith
  have hsq := pow_le_pow_left₀ h0 h2 2
  have e : (2 * ∫ u, ψ u) ^ 2 = 4 * (∫ u, ψ u) ^ 2 := by ring
  unfold poleSquare
  linarith

/-- `(∫ψ²)² ≤ M²(∫ψ)²` for `0 ≤ ψ ≤ M`. -/
theorem sq_integral_sq_le {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψ0 : ∀ u, 0 ≤ ψ u) {M : ℝ} (hM : ∀ u, ψ u ≤ M) :
    (∫ u, ψ u ^ 2) ^ 2 ≤ M ^ 2 * (∫ u, ψ u) ^ 2 := by
  have hI : Integrable ψ := hψ.integrable_of_hasCompactSupport hψc
  have hI2 : Integrable fun u => ψ u ^ 2 :=
    (hψ.pow 2).integrable_of_hasCompactSupport (hψc.mono fun u hu h0 => hu (by simp [h0]))
  have h1 : (∫ u, ψ u ^ 2) ≤ M * ∫ u, ψ u := by
    rw [← integral_const_mul]
    exact integral_mono hI2 (hI.const_mul M) fun u => by
      show ψ u ^ 2 ≤ M * ψ u
      nlinarith [mul_nonneg (hψ0 u) (sub_nonneg.mpr (hM u))]
  have h0 : 0 ≤ ∫ u, ψ u ^ 2 := integral_nonneg fun u => sq_nonneg _
  calc (∫ u, ψ u ^ 2) ^ 2 ≤ (M * ∫ u, ψ u) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = M ^ 2 * (∫ u, ψ u) ^ 2 := by ring

/-! ### 4. The even sector: Perron margin and positivity margin -/

/-- **The even Perron margin.** If `λ ∫ψ² ≤ E_{s₀}(ψ)`, `∫ψ² = 1`, the competitor `g` lies on the
pole hyperplane and `ψ` is an `ε`-ground state of `E_{s₁}` against `g`, then
`(s₁ − s₀) P(ψ) ≤ E_1(g) − λ + ε`. -/
theorem evenPerronMargin_le {w₂ w₃ s₀ s₁ lam ε : ℝ} {ψ g : ℝ → ℝ}
    (hlow : lam * (∫ u, ψ u ^ 2) ≤ evenPoleBand w₂ w₃ s₀ ψ) (hψ : ∫ u, ψ u ^ 2 = 1)
    (hg : ∫ u, g u * coshWeight u = 0)
    (hmin : evenPoleBand w₂ w₃ s₁ ψ ≤ evenPoleBand w₂ w₃ s₁ g + ε) :
    (s₁ - s₀) * poleSquare ψ ≤ evenPoleBand w₂ w₃ 1 g - lam + ε := by
  rw [evenPoleBand_eq_add w₂ w₃ s₀] at hlow
  rw [evenPoleBand_eq_add w₂ w₃ s₁ ψ, evenPoleBand_eq_add w₂ w₃ s₁ g] at hmin
  have h := margin_mul_le (evenPoleBand w₂ w₃ 0) poleSquare (fun f => ∫ u, f u ^ 2) hlow hψ hmin
  rwa [← evenPoleBand_eq_add, evenPoleBand_of_poleHyperplane hg] at h

/-- **Robust Perron costs height (even sector).** For a normalized Perron `ε`-ground state
`0 ≤ ψ ≤ M` of `E_{s₁}` against a competitor on the pole hyperplane, with `λ ∫ψ² ≤ E_{s₀}(ψ)` and
`s₀ ≤ s₁`: `4(s₁ − s₀) ≤ M²(E_1(g) − λ + ε)`. -/
theorem evenPerronMargin_le_sup {w₂ w₃ s₀ s₁ lam ε M : ℝ} {ψ g : ℝ → ℝ}
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (hψ0 : ∀ u, 0 ≤ ψ u)
    (hψM : ∀ u, ψ u ≤ M) (hs : s₀ ≤ s₁)
    (hlow : lam * (∫ u, ψ u ^ 2) ≤ evenPoleBand w₂ w₃ s₀ ψ) (hψ : ∫ u, ψ u ^ 2 = 1)
    (hg : ∫ u, g u * coshWeight u = 0)
    (hmin : evenPoleBand w₂ w₃ s₁ ψ ≤ evenPoleBand w₂ w₃ s₁ g + ε) :
    4 * (s₁ - s₀) ≤ M ^ 2 * (evenPoleBand w₂ w₃ 1 g - lam + ε) := by
  have hm := evenPerronMargin_le hlow hψ hg hmin
  have hP := four_mul_sq_integral_le_poleSquare hψc hψs hψ0
  have hS := sq_integral_sq_le hψc hψs hψ0 hψM
  rw [hψ, one_pow] at hS
  have hd : 0 ≤ s₁ - s₀ := sub_nonneg.mpr hs
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  calc 4 * (s₁ - s₀) = 4 * (s₁ - s₀) * 1 := by ring
    _ ≤ 4 * (s₁ - s₀) * (M ^ 2 * (∫ u, ψ u) ^ 2) :=
        mul_le_mul_of_nonneg_left hS (by linarith)
    _ = M ^ 2 * ((s₁ - s₀) * (4 * (∫ u, ψ u) ^ 2)) := by ring
    _ ≤ M ^ 2 * ((s₁ - s₀) * poleSquare ψ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP hd) hM2
    _ ≤ M ^ 2 * (evenPoleBand w₂ w₃ 1 g - lam + ε) := mul_le_mul_of_nonneg_left hm hM2

/-- **No robust Perron (even sector).** If the pole margin exceeds the saturation gap,
`M²(E_1(g) − λ + ε) < 4(s₁ − s₀)`, then a normalized `ε`-ground state `ψ ≤ M` of `E_{s₁}` is
negative somewhere. -/
theorem exists_neg_of_evenMargin_gt {w₂ w₃ s₀ s₁ lam ε M : ℝ} {ψ g : ℝ → ℝ}
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (hψM : ∀ u, ψ u ≤ M) (hs : s₀ ≤ s₁)
    (hlow : lam * (∫ u, ψ u ^ 2) ≤ evenPoleBand w₂ w₃ s₀ ψ) (hψ : ∫ u, ψ u ^ 2 = 1)
    (hg : ∫ u, g u * coshWeight u = 0)
    (hmin : evenPoleBand w₂ w₃ s₁ ψ ≤ evenPoleBand w₂ w₃ s₁ g + ε)
    (hgap : M ^ 2 * (evenPoleBand w₂ w₃ 1 g - lam + ε) < 4 * (s₁ - s₀)) :
    ∃ u, ψ u < 0 := by
  by_contra h
  push Not at h
  exact absurd (evenPerronMargin_le_sup hψc hψs h hψM hs hlow hψ hg hmin) (not_le.mpr hgap)

/-- **The even positivity margin.** If the band at the weaker pole `s_w ≤ s₀` is nonnegative at a
normalized Perron test `0 ≤ ψ ≤ M`, then `4(s₀ − s_w) ≤ M² E_{s₀}(ψ)`. -/
theorem evenPositivityMargin_le_sup {w₂ w₃ sw s₀ M : ℝ} {ψ : ℝ → ℝ}
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (hψ0 : ∀ u, 0 ≤ ψ u)
    (hψM : ∀ u, ψ u ≤ M) (hs : sw ≤ s₀) (hψ : ∫ u, ψ u ^ 2 = 1)
    (hpos : 0 ≤ evenPoleBand w₂ w₃ sw ψ) :
    4 * (s₀ - sw) ≤ M ^ 2 * evenPoleBand w₂ w₃ s₀ ψ := by
  rw [evenPoleBand_eq_add w₂ w₃ sw] at hpos
  have hm := positivity_margin_le (evenPoleBand w₂ w₃ 0) poleSquare (t₀ := s₀) hpos
  rw [← evenPoleBand_eq_add] at hm
  have hP := four_mul_sq_integral_le_poleSquare hψc hψs hψ0
  have hS := sq_integral_sq_le hψc hψs hψ0 hψM
  rw [hψ, one_pow] at hS
  have hd : 0 ≤ s₀ - sw := sub_nonneg.mpr hs
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  calc 4 * (s₀ - sw) = 4 * (s₀ - sw) * 1 := by ring
    _ ≤ 4 * (s₀ - sw) * (M ^ 2 * (∫ u, ψ u) ^ 2) :=
        mul_le_mul_of_nonneg_left hS (by linarith)
    _ = M ^ 2 * ((s₀ - sw) * (4 * (∫ u, ψ u) ^ 2)) := by ring
    _ ≤ M ^ 2 * ((s₀ - sw) * poleSquare ψ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP hd) hM2
    _ ≤ M ^ 2 * evenPoleBand w₂ w₃ s₀ ψ := mul_le_mul_of_nonneg_left hm hM2

/-! ### 5. The odd kick family -/

/-- The kick energy `K(f) = w₂(f⋆f)(−log 2) + w₃(f⋆f)(−log 3)` of the first two primes. -/
def kickEnergy (w₂ w₃ : ℝ) (f : ℝ → ℝ) : ℝ :=
  w₂ * selfConv f (-Real.log 2) + w₃ * selfConv f (-Real.log 3)

/-- The odd band at kick strength `t`: `W − 𝓗₀ + t·K`; `t = 1` is the arithmetic odd band. -/
def oddKickBand (w₂ w₃ t : ℝ) (f : ℝ → ℝ) : ℝ :=
  weilQuad f - collarHankel 0 f + t * kickEnergy w₂ w₃ f

/-- The odd weight set is the nonnegativity of the arithmetic kick band. -/
theorem mem_oddBandWeights_iff {c w₂ w₃ : ℝ} :
    (w₂, w₃) ∈ oddBandWeights c ↔
      ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -c → f u = 0) →
        0 ≤ oddKickBand w₂ w₃ 1 f := by
  refine forall_congr' fun f => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => ?_
  dsimp only
  unfold oddKickBand kickEnergy
  constructor <;> intro h <;> linarith

/-- A Perron test has nonnegative kick energy under nonnegative weights. -/
theorem kickEnergy_nonneg {w₂ w₃ : ℝ} (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃) {ψ : ℝ → ℝ}
    (hψ0 : ∀ u, 0 ≤ ψ u) : 0 ≤ kickEnergy w₂ w₃ ψ := by
  have h (s : ℝ) : 0 ≤ selfConv ψ s :=
    integral_nonneg fun u => mul_nonneg (hψ0 u) (hψ0 _)
  exact add_nonneg (mul_nonneg hw₂ (h _)) (mul_nonneg hw₃ (h _))

/-- **The odd Perron margin.** If `λ ∫ψ² ≤ O_{t₀}(ψ)`, `∫ψ² = 1`, the competitor has `K(g) ≤ 0`,
`t₁ ≥ 0`, and `ψ` is an `ε`-ground state of `O_{t₁}` against `g`, then
`(t₁ − t₀) K(ψ) ≤ O_0(g) − λ + ε`. -/
theorem oddPerronMargin_le {w₂ w₃ t₀ t₁ lam ε : ℝ} {ψ g : ℝ → ℝ}
    (hlow : lam * (∫ u, ψ u ^ 2) ≤ oddKickBand w₂ w₃ t₀ ψ) (hψ : ∫ u, ψ u ^ 2 = 1)
    (ht₁ : 0 ≤ t₁) (hg : kickEnergy w₂ w₃ g ≤ 0)
    (hmin : oddKickBand w₂ w₃ t₁ ψ ≤ oddKickBand w₂ w₃ t₁ g + ε) :
    (t₁ - t₀) * kickEnergy w₂ w₃ ψ ≤ oddKickBand w₂ w₃ 0 g - lam + ε := by
  have h := margin_mul_le (fun f => weilQuad f - collarHankel 0 f) (kickEnergy w₂ w₃)
    (fun f => ∫ u, f u ^ 2) (t₀ := t₀) (t₁ := t₁) hlow hψ hmin
  beta_reduce at h
  have hgt : t₁ * kickEnergy w₂ w₃ g ≤ 0 := by
    nlinarith [mul_le_mul_of_nonneg_left hg ht₁]
  unfold oddKickBand
  linarith

end GaloisForLFunctions.SignedWindowCriticality.PerronSignLaw

end
