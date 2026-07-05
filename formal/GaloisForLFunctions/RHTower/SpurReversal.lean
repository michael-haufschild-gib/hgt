/-
# SpurReversal — the doc 26 reversal identities (task #143 / #138 substrate)

Doc 26 (26-outer-reversal.md) `[PROVED HERE]` identities for the reversed section field,
formalized in reversed coordinates `y = 1/c`, `β_k = 1/α_k`. Flat grading: finite-sum and
one-variable-calculus algebra; the partial-fraction content is doc 26 §1–3, nothing here is
new mathematics.

* `transportedField y β s = ∑ (y − β_k)⁻¹` (the `F̂`), `reversedEnergy = ∑ (y − β_k)⁻²` (`ℰ̂`).
* `poleWeight y β = y/(y − β)` (the scale-invariant `ξ_k`).
* `weightSum_eq` / `weightSqSum_eq` — factoring the coordinate out: `Σξ = y·F̂`, `S = y²·ℰ̂`.
* `xiSum_eq_of_equilibrium` — **(ΞSUM)**: at a transported equilibrium `F̂ = d/y`, `Σξ_k = d`
  (the conserved `ℓ¹` budget of doc 26 §3).
* `participation_floor` — the localization floor `S ≥ d²/#s` from `Σξ = d` (Cauchy–Schwarz /
  Chebyshev): the participation-ratio reading of the copy→flip transition.
* `oscEnergy_hasDerivAt` — **(OSC)** the frequency-`b` oscillator energy `E_b = b²V² + V'²`
  has `E_b' = 2V'(V'' + b²V)`, so `E_b` and `V²` co-move iff `V'' + b²V` and `V'` share sign
  (doc 26 §2, theorem-m's ODE-energy monotonicity in the reversed coordinate; no ODE is used).
* `revTerm_eq` / `revEnergyTerm_eq` — the per-term partial-fraction identities of §1
  (`(c−α)⁻¹ = y − y²/(y−β)` and the `β²/(β−y)²` expansion) that generate the sum rules.
-/
import Mathlib

noncomputable section

namespace RHTower

open Finset

variable {ι : Type*}

/-- The transported equilibrium field `F̂(y) = Σ_k (y − β_k)⁻¹` (doc 26 §0). -/
def transportedField (y : ℝ) (β : ι → ℝ) (s : Finset ι) : ℝ := ∑ k ∈ s, (y - β k)⁻¹

/-- The reversed energy `ℰ̂(y) = Σ_k (y − β_k)⁻²` (doc 26 §0). -/
def reversedEnergy (y : ℝ) (β : ι → ℝ) (s : Finset ι) : ℝ := ∑ k ∈ s, ((y - β k)⁻¹) ^ 2

/-- The scale-invariant pole weight `ξ_k = y/(y − β_k)` (doc 26 §3). -/
def poleWeight (y β : ℝ) : ℝ := y / (y - β)

/-- `Σ_k ξ_k` (`= y F̂`). -/
def weightSum (y : ℝ) (β : ι → ℝ) (s : Finset ι) : ℝ := ∑ k ∈ s, poleWeight y (β k)

/-- `S = Σ_k ξ_k²` (`= y² ℰ̂`), the doc 26 §3 localization functional. -/
def weightSqSum (y : ℝ) (β : ι → ℝ) (s : Finset ι) : ℝ := ∑ k ∈ s, (poleWeight y (β k)) ^ 2

/-- **`Σξ = y·F̂`** — factor the coordinate out of the weight sum. -/
theorem weightSum_eq (y : ℝ) (β : ι → ℝ) (s : Finset ι) :
    weightSum y β s = y * transportedField y β s := by
  unfold weightSum transportedField poleWeight
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [div_eq_mul_inv]

/-- **`S = y²·ℰ̂`** — the doc 26 §3 identity `S = y² ℰ̂(y)`. -/
theorem weightSqSum_eq (y : ℝ) (β : ι → ℝ) (s : Finset ι) :
    weightSqSum y β s = y ^ 2 * reversedEnergy y β s := by
  unfold weightSqSum reversedEnergy poleWeight
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [div_pow, div_eq_mul_inv, inv_pow]

/-- **(ΞSUM)**: at a transported equilibrium `F̂(y) = d/y` (`y ≠ 0`) the pole weights sum to
`d` — the conserved `ℓ¹` budget along the whole outer critical-point sequence (doc 26 §3). -/
theorem xiSum_eq_of_equilibrium {y d : ℝ} (β : ι → ℝ) (s : Finset ι) (hy : y ≠ 0)
    (heq : transportedField y β s = d / y) : weightSum y β s = d := by
  rw [weightSum_eq, heq, mul_div_cancel₀ _ hy]

/-- **Localization floor**: from the conserved budget `Σξ = d`, Cauchy–Schwarz/Chebyshev gives
`S ≥ d²/#s`. Delocalized (spread weights) ⟹ `S` near the floor; flip = localization pushes
`S` up. The participation-ratio reading of the copy→flip transition (doc 26 §3). -/
theorem participation_floor {y d : ℝ} (β : ι → ℝ) (s : Finset ι) (hy : y ≠ 0)
    (heq : transportedField y β s = d / y) :
    d ^ 2 ≤ (s.card : ℝ) * weightSqSum y β s := by
  have hsum : weightSum y β s = d := xiSum_eq_of_equilibrium β s hy heq
  have hcs : (∑ k ∈ s, poleWeight y (β k)) ^ 2
      ≤ (s.card : ℝ) * ∑ k ∈ s, (poleWeight y (β k)) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [← weightSum, hsum] at hcs
  exact hcs

/-- **Per-term reversal identity (doc 26 §1.1)**: with `c = 1/y`, `α = 1/β`, the original-lane
term `(c − α)⁻¹` equals `y − y²/(y − β)` — the algebra that turns `Σ(c−α)⁻¹ = 0` into
`F̂(y) = d/y`. -/
theorem revTerm_eq {y β : ℝ} (hy : y ≠ 0) (hβ : β ≠ 0) (hyβ : y ≠ β) :
    (1 / y - 1 / β)⁻¹ = y - y ^ 2 / (y - β) := by
  have hyβ' : y - β ≠ 0 := sub_ne_zero.mpr hyβ
  field_simp
  ring

/-- **Per-term energy identity (doc 26 §1.2)**: `β²/(β − y)² = 1 + 2y/(β − y) + y²/(β − y)²`,
the expansion summed (with the equilibrium) to `c⁴ℰ(c) = ℰ̂(y) − d/y²`. -/
theorem revEnergyTerm_eq {y β : ℝ} (hβy : β ≠ y) :
    β ^ 2 / (β - y) ^ 2 = 1 + 2 * y / (β - y) + y ^ 2 / (β - y) ^ 2 := by
  have : β - y ≠ 0 := sub_ne_zero.mpr hβy
  field_simp
  ring

/-- **(OSC) oscillator energy (doc 26 §2)**: for `V` twice differentiable at `y` with
`V'(y) = v'` and `V''(y) = v''`, the frequency-`b` energy `E_b = b²V² + V'²` has derivative
`E_b'(y) = 2 v' (v'' + b² V(y))`. Hence `E_b` and `V²` co-move (`E_b' , (V²)'` same sign) iff
`v'' + b² V(y)` and `v'` share sign — copy ⟺ `V'' + b²V` co-signed with `V'`, theorem-m's ODE
energy monotonicity in the reversed coordinate. No ODE is assumed; the oscillator is the
comparison object. -/
theorem oscEnergy_hasDerivAt {V V' : ℝ → ℝ} {y v'' b : ℝ}
    (hV' : HasDerivAt V' v'' y) (hVd : ∀ z, HasDerivAt V (V' z) z) :
    HasDerivAt (fun z => b ^ 2 * V z ^ 2 + V' z ^ 2)
      (2 * V' y * (v'' + b ^ 2 * V y)) y := by
  have h1 : HasDerivAt (fun z => b ^ 2 * V z ^ 2) (b ^ 2 * (2 * V y * V' y)) y := by
    have := (hVd y).pow 2
    simpa using this.const_mul (b ^ 2)
  have h2 : HasDerivAt (fun z => V' z ^ 2) (2 * V' y * v'') y := by
    have := hV'.pow 2
    simpa [mul_comm, mul_left_comm] using this
  have := h1.add h2
  convert this using 1
  ring

end RHTower
