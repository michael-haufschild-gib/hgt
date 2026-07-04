/-
Doc 32 §1 (task #131): seam transport — dominated windows carry deck classes.

The ANNEAL reduction (doc 22) reads ζ-window parity off the finite truncation `g_N` on
dominated windows. The transport step is banked homotopy machinery: strict domination
`‖f − g‖ < ‖g‖` on the window charts keeps the segment homotopy nonvanishing, and
`deckClass_perturb` (DeckHomotopy, #117) transports the deck class of any level-`n`
root data — Rouché with no argument principle. This module packages the lane-named
statement and its ladder specialization `n = 2^k`.
-/
import GaloisForLFunctions.RHTower.DeckHomotopy

namespace RHTower

open Complex

/-- **Seam transport** (doc 32 §1). On a window whose charts carry the strict
domination `‖f − g‖ < ‖g‖`, every level-`n` root datum of `f` has the same deck class
as every level-`n` root datum of `g`: the window reading transports from the finite
truncation to the completed carrier. -/
theorem seam_transport {f g F₁ F₂ G₁ G₂ : ℂ → ℂ} {a : ℂ} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n)
    (hf : AnalyticOnNhd ℂ f (chartR a R ∪ chartL a R))
    (hF₁ : AnalyticOnNhd ℂ F₁ (chartR a R)) (hF₂ : AnalyticOnNhd ℂ F₂ (chartL a R))
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hpF₁ : ∀ z ∈ chartR a R, F₁ z ^ n = f z) (hpF₂ : ∀ z ∈ chartL a R, F₂ z ^ n = f z)
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ n = g z) (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ n = g z)
    (hdom : ∀ z ∈ chartR a R ∪ chartL a R, ‖f z - g z‖ < ‖g z‖) :
    deckClass F₁ F₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) =
      deckClass G₁ G₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) :=
  deckClass_perturb hR hn hf hF₁ hF₂ hG₁ hG₂ hpF₁ hpF₂ hpG₁ hpG₂ hdom

/-- **Ladder seam transport**: the level-`2^k` reading of a dominated window is the
same for the carrier and for the truncation — each rung of the RH ladder can be read
off the finite side wherever domination holds. -/
theorem seam_transport_ladder {f g F₁ F₂ G₁ G₂ : ℂ → ℂ} {a : ℂ} {R : ℝ} (k : ℕ)
    (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (chartR a R ∪ chartL a R))
    (hF₁ : AnalyticOnNhd ℂ F₁ (chartR a R)) (hF₂ : AnalyticOnNhd ℂ F₂ (chartL a R))
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hpF₁ : ∀ z ∈ chartR a R, F₁ z ^ 2 ^ k = f z)
    (hpF₂ : ∀ z ∈ chartL a R, F₂ z ^ 2 ^ k = f z)
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ 2 ^ k = g z)
    (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ 2 ^ k = g z)
    (hdom : ∀ z ∈ chartR a R ∪ chartL a R, ‖f z - g z‖ < ‖g z‖) :
    deckClass F₁ F₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) =
      deckClass G₁ G₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) :=
  seam_transport hR (pow_pos two_pos k) hf hF₁ hF₂ hG₁ hG₂ hpF₁ hpF₂ hpG₁ hpG₂ hdom

end RHTower
