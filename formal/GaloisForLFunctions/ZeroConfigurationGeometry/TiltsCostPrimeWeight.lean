import GaloisForLFunctions.ZeroConfigurationGeometry.FiniteCarriersAreRealAboveTheirHorizon
import GaloisForLFunctions.ZeroConfigurationGeometry.RamanujanIsRealityOfAnEulerColumn

/-!
# Tilts cost prime weight

The calibration of the domination step against the positive twins. Domination
(`FiniteCarriersAreRealAboveTheirHorizon`) read backwards is a price: a finite carrier has a zero
off the line at height `t` only if its prime weight pays for the archimedean speed there.

* **Tilts cost weight** (`log_le_carrierWeight_of_tilted_zero`). If the carrier with coefficients
  `a` and cutoff `X` vanishes at `σ + it` with `0 < |σ − ½| ≤ u₀ < ½` and `|t| ≥ 4`, then
  `W_a(X, u₀) ≥ log(|t|/2π) − 6/|t|`. Along the Euler depth the price is
  `|s| W_Λ(X, u₀) ≥ log(|t|/2π) − 6/|t|` (`log_le_eulerDepth_weight_of_tilted_zero`).
* **The twins are tilted at every height** (`localFactor_twin_tilted_zero`). The Euler factor at `p`
  with coefficient `A_δ = −2√p cosh(δ log p)` vanishes at `½ + δ + 2πik/log p` for every `k`.
* **The gap** (`twin_tilt_costs_weight`, `exists_twin_tilt_beyond_every_weight`). A finite carrier
  that reproduces the twin's tilted zero at height `t_k = 2πk/log p` has weight at least
  `log(|t_k|/2π) − 6/|t_k|`. For every bound `M` some tilted zero of the twin can be reproduced
  only by carriers of weight `> M`.

So domination and the twins are compatible in exactly one way: the tilted columns of a twin are
reached only by carriers whose prime weight grows like `log` of the height. Finite pieces of the
twin's data are on the line above their horizon, and the twin is tilted at every height. The
ζ-specific step of an RH route must therefore control how the prime sum cancels below the horizon,
since the size of the weight cannot separate `ζ` from the twins.
-/

open Complex Set

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open _root_.RHTower SelbergClass.PositiveFiniteEuler

/-- **Tilts cost weight.** A zero of a finite carrier at `σ + it`, `0 < |σ − ½| ≤ u₀ < ½`,
`|t| ≥ 4`, forces `W_a(X, u₀) ≥ log(|t|/2π) − 6/|t|`. -/
theorem log_le_carrierWeight_of_tilted_zero (a : ℕ → ℝ) (X : ℕ) {u₀ t σ : ℝ} (hu₀ : u₀ < 1 / 2)
    (ht : 4 ≤ |t|) (hσ : 0 < |σ - 1 / 2|) (hσu : |σ - 1 / 2| ≤ u₀)
    (hz : (carrierHalf a X).sym ((σ : ℂ) + t * I) = 0) :
    Real.log (|t| / (2 * Real.pi)) - 6 / |t| ≤ carrierWeight a X u₀ := by
  by_contra h
  exact carrier_ne_zero_near_line a X hu₀ ht (by linarith [not_le.mp h]) hσ hσu hz

/-- Along the Euler depth the price of a tilt is paid by `|s| W_Λ`. -/
theorem log_le_eulerDepth_weight_of_tilted_zero (s : ℝ) (X : ℕ) {u₀ t σ : ℝ}
    (hu₀ : u₀ < 1 / 2) (ht : 4 ≤ |t|) (hσ : 0 < |σ - 1 / 2|) (hσu : |σ - 1 / 2| ≤ u₀)
    (hz : (carrierHalf (eulerDepthCoeff s) X).sym ((σ : ℂ) + t * I) = 0) :
    Real.log (|t| / (2 * Real.pi)) - 6 / |t| ≤ |s| * eulerStageWeight X u₀ := by
  rw [← carrierWeight_eulerDepth]
  exact log_le_carrierWeight_of_tilted_zero _ X hu₀ ht hσ hσu hz

/-- The tilted zeros of the twin factor: `½ + δ + 2πik/log p`. -/
theorem verticalLatticePoint_eq (L δ : ℝ) (k : ℤ) :
    verticalLatticePoint L δ k =
      (((1 / 2 + δ : ℝ)) : ℂ) + (((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp [verticalLatticePoint]

/-- **The twins are tilted at every height.** -/
theorem localFactor_twin_tilted_zero {p : ℕ} (hp : 1 < p) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (k : ℤ) : localFactor p (eulerColumnCoeff p δ) (verticalLatticePoint (Real.log p) δ k) = 0 := by
  have h := (eulerColumn_mimics_onLineLattice hp hδ hδ').1
  have hmem : verticalLatticePoint (Real.log p) δ k ∈
      (offLineLatticeConfig (Real.log_pos (show (1 : ℝ) < p by exact_mod_cast hp)) hδ
        hδ').carrier :=
    Or.inl ⟨k, rfl⟩
  rw [h] at hmem
  exact hmem

/-- **The gap.** A finite carrier that vanishes at the twin's tilted zero of height
`t_k = 2πk/log p`, `|t_k| ≥ 4`, has weight `W_a(X, δ) ≥ log(|t_k|/2π) − 6/|t_k|`. -/
theorem twin_tilt_costs_weight {p : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (a : ℕ → ℝ) (X : ℕ) (k : ℤ) (ht : 4 ≤ |(k : ℝ) * (2 * Real.pi / Real.log p)|)
    (hz : (carrierHalf a X).sym (verticalLatticePoint (Real.log p) δ k) = 0) :
    Real.log (|(k : ℝ) * (2 * Real.pi / Real.log p)| / (2 * Real.pi)) -
        6 / |(k : ℝ) * (2 * Real.pi / Real.log p)| ≤ carrierWeight a X δ := by
  rw [verticalLatticePoint_eq] at hz
  refine log_le_carrierWeight_of_tilted_zero a X hδ' ht ?_ ?_ hz
  · rw [show (1 / 2 + δ) - 1 / 2 = δ by ring, abs_of_pos hδ]; exact hδ
  · rw [show (1 / 2 + δ) - 1 / 2 = δ by ring, abs_of_pos hδ]

/-- **The price is unbounded.** For every `M` there is a tilted zero of the twin that no finite
carrier of weight `W_a(X, δ) ≤ M` reproduces. -/
theorem exists_twin_tilt_beyond_every_weight {p : ℕ} (hp : 1 < p) {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ < 1 / 2) (M : ℝ) :
    ∃ k : ℤ, localFactor p (eulerColumnCoeff p δ) (verticalLatticePoint (Real.log p) δ k) = 0 ∧
      ∀ (a : ℕ → ℝ) (X : ℕ), (carrierHalf a X).sym (verticalLatticePoint (Real.log p) δ k) = 0 →
        M < carrierWeight a X δ := by
  have hL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  set h := 2 * Real.pi / Real.log p with hh
  have hh0 : 0 < h := by positivity
  -- a height `T` with `log(T/2π) − 6/T > M` and `T ≥ 4`
  set T := max 4 (2 * Real.pi * Real.exp (M + 2)) with hT
  have hT4 : 4 ≤ T := le_max_left _ _
  have hTexp : 2 * Real.pi * Real.exp (M + 2) ≤ T := le_max_right _ _
  obtain ⟨k, hk⟩ : ∃ k : ℕ, T / h < k := exists_nat_gt _
  have hkT : T ≤ (k : ℝ) * h := by
    have := (div_lt_iff₀ hh0).mp hk; linarith
  refine ⟨k, localFactor_twin_tilted_zero hp hδ hδ'.le k, fun a X hz => ?_⟩
  have hkpos : 0 ≤ ((k : ℤ) : ℝ) * h := by positivity
  have habs : |((k : ℤ) : ℝ) * h| = (k : ℝ) * h := by rw [abs_of_nonneg hkpos]; push_cast; ring
  have hge := twin_tilt_costs_weight hδ hδ' a X k (by rw [habs]; linarith)
    (by exact_mod_cast hz)
  rw [habs] at hge
  have hkh : 0 < (k : ℝ) * h := by linarith
  have hlog : M + 2 ≤ Real.log ((k : ℝ) * h / (2 * Real.pi)) := by
    rw [Real.le_log_iff_exp_le (div_pos hkh (by positivity))]
    rw [le_div_iff₀ (by positivity)]
    linarith [mul_comm (Real.exp (M + 2)) (2 * Real.pi)]
  have hsmall : 6 / ((k : ℝ) * h) ≤ 3 / 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  linarith

end GaloisForLFunctions.ZeroConfigurationGeometry
