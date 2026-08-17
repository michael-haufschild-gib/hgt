import GaloisForLFunctions.RHTower.SuzukiMidpointReflectionInstantiation

/-!
# The parity forms and the domination of the Hankel carrier

The two half-interval parity forms are the common Toeplitz channel shifted below the floor, plus and
minus the arithmetic Hankel carrier:

`q_e = C_{a,λ} + H_a`,  `q_o = C_{a,λ} − H_a`,  `C_{a,λ} = T_a − λ⟨·,·⟩`.

Coercivity of *both* parity forms is the card's standing admissibility hypothesis, and it has two
immediate consequences that every later estimate uses: the common channel, being their average, is
itself coercive, and the Hankel carrier is dominated by it,

`|H_a(f,f)| ≤ C_{a,λ}(f,f)`.

Nothing analytic is involved — the domination is the statement that a number lying between `−c` and
`c` has absolute value at most `c`, applied to the half-difference of two nonnegative quantities.
-/

open MeasureTheory

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The `L²` pairing of the half-interval. -/
def l2Pairing (φ ψ : ℝ → ℝ) : ℝ := ∫ x : ℝ, φ x * ψ x

theorem l2Pairing_symm (φ ψ : ℝ → ℝ) : l2Pairing φ ψ = l2Pairing ψ φ := by
  rw [l2Pairing, l2Pairing]
  refine integral_congr_ae ?_
  filter_upwards with x
  ring

/-- The common channel: the Toeplitz form shifted by the spectral parameter. -/
def commonForm (K : ℝ → ℝ) (lam : ℝ) (φ ψ : ℝ → ℝ) : ℝ :=
  diffBilinForm K φ ψ - lam * l2Pairing φ ψ

/-- The even parity form. -/
def evenParityForm (K L : ℝ → ℝ) (lam : ℝ) (φ ψ : ℝ → ℝ) : ℝ :=
  commonForm K lam φ ψ + sumBilinForm L φ ψ

/-- The odd parity form. -/
def oddParityForm (K L : ℝ → ℝ) (lam : ℝ) (φ ψ : ℝ → ℝ) : ℝ :=
  commonForm K lam φ ψ - sumBilinForm L φ ψ

/-! ## The averaging identities -/

theorem commonForm_eq_avg (K L : ℝ → ℝ) (lam : ℝ) (φ ψ : ℝ → ℝ) :
    commonForm K lam φ ψ
      = (evenParityForm K L lam φ ψ + oddParityForm K L lam φ ψ) / 2 := by
  rw [evenParityForm, oddParityForm]
  ring

theorem sumBilinForm_eq_half_diff (K L : ℝ → ℝ) (lam : ℝ) (φ ψ : ℝ → ℝ) :
    sumBilinForm L φ ψ
      = (evenParityForm K L lam φ ψ - oddParityForm K L lam φ ψ) / 2 := by
  rw [evenParityForm, oddParityForm]
  ring

/-! ## Coercivity of the average and domination of the carrier -/

/-- **The common channel inherits coercivity from the two parity forms.** -/
theorem commonForm_nonneg_of_parity {K L : ℝ → ℝ} {lam : ℝ} {φ : ℝ → ℝ}
    (he : 0 ≤ evenParityForm K L lam φ φ) (ho : 0 ≤ oddParityForm K L lam φ φ) :
    0 ≤ commonForm K lam φ φ := by
  rw [commonForm_eq_avg K L lam]
  linarith

/-- **`(224)`: the Hankel carrier is dominated by the common channel.** -/
theorem abs_sumBilinForm_le_commonForm {K L : ℝ → ℝ} {lam : ℝ} {φ : ℝ → ℝ}
    (he : 0 ≤ evenParityForm K L lam φ φ) (ho : 0 ≤ oddParityForm K L lam φ φ) :
    |sumBilinForm L φ φ| ≤ commonForm K lam φ φ := by
  rw [sumBilinForm_eq_half_diff K L lam, commonForm_eq_avg K L lam, abs_le]
  constructor <;> linarith

/-- A coercive lower bound on both parity forms transfers to the common channel. -/
theorem commonForm_ge_of_parity {K L : ℝ → ℝ} {lam : ℝ} {φ : ℝ → ℝ} {δ : ℝ}
    (he : δ ≤ evenParityForm K L lam φ φ) (ho : δ ≤ oddParityForm K L lam φ φ) :
    δ ≤ commonForm K lam φ φ := by
  rw [commonForm_eq_avg K L lam]
  linarith

/-! ## Symmetry and homogeneity of the parity forms -/

theorem commonForm_symm (K : ℝ → ℝ) (lam : ℝ) (φ ψ : ℝ → ℝ) (hK : ∀ t, K (-t) = K t) :
    commonForm K lam φ ψ = commonForm K lam ψ φ := by
  rw [commonForm, commonForm, diffBilinForm_symm K φ ψ hK, l2Pairing_symm]

theorem evenParityForm_symm (K L : ℝ → ℝ) (lam : ℝ) (φ ψ : ℝ → ℝ) (hK : ∀ t, K (-t) = K t) :
    evenParityForm K L lam φ ψ = evenParityForm K L lam ψ φ := by
  rw [evenParityForm, evenParityForm, commonForm_symm K lam φ ψ hK, sumBilinForm_symm L φ ψ]

theorem oddParityForm_symm (K L : ℝ → ℝ) (lam : ℝ) (φ ψ : ℝ → ℝ) (hK : ∀ t, K (-t) = K t) :
    oddParityForm K L lam φ ψ = oddParityForm K L lam ψ φ := by
  rw [oddParityForm, oddParityForm, commonForm_symm K lam φ ψ hK, sumBilinForm_symm L φ ψ]

theorem l2Pairing_smul_left (c : ℝ) (φ ψ : ℝ → ℝ) :
    l2Pairing (c • φ) ψ = c * l2Pairing φ ψ := by
  rw [l2Pairing, l2Pairing, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards with x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem commonForm_smul_left (c : ℝ) (K : ℝ → ℝ) (lam : ℝ) (φ ψ : ℝ → ℝ) :
    commonForm K lam (c • φ) ψ = c * commonForm K lam φ ψ := by
  rw [commonForm, commonForm, diffBilinForm_smul_left, l2Pairing_smul_left]
  ring

theorem evenParityForm_smul_left (c : ℝ) (K L : ℝ → ℝ) (lam : ℝ) (φ ψ : ℝ → ℝ) :
    evenParityForm K L lam (c • φ) ψ = c * evenParityForm K L lam φ ψ := by
  rw [evenParityForm, evenParityForm, commonForm_smul_left, sumBilinForm_smul_left]
  ring

theorem oddParityForm_smul_left (c : ℝ) (K L : ℝ → ℝ) (lam : ℝ) (φ ψ : ℝ → ℝ) :
    oddParityForm K L lam (c • φ) ψ = c * oddParityForm K L lam φ ψ := by
  rw [oddParityForm, oddParityForm, commonForm_smul_left, sumBilinForm_smul_left]
  ring

end GaloisForLFunctions.RHTower
