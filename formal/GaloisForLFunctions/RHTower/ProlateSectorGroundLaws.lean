import GaloisForLFunctions.RHTower.ProlateSectorConstrainedGround
import GaloisForLFunctions.RHTower.ProlateParitySeparation

/-!
# The constrained-prolate floor laws, in the operator's own terms

`ProlateSectorConstrainedGround` identifies the secular ground root of a Fourier sector with the
constrained leakage ground value of the operator `B_a = I − T_a²` on that sector.  The value is
unique — a floor that is attained determines itself — so every asymptotic law proved for the
secular root is literally a law about the operator's constrained ground eigenvalue.

This module records that uniqueness and restates the constrained-prolate cards' floor laws in the
operator formulation: the two Fourier-sector ground values `mu_±(lambda)`, their normalizations by
the dominant leakages `d_4 = 1 − chi_4²` and `d_6 = 1 − chi_6²`, the complementary gaps, and the
parity separation.  Every statement here is unconditional; the only hypothesis is the naming
hypothesis that identifies the function `mu` with the operator's ground value.
-/

noncomputable section

open Filter Set Topology
open scoped InnerProduct InnerProductSpace

namespace RHTower

/-! ## Uniqueness of the constrained ground value -/

/-- **The constrained leakage ground value of a sector is unique.**  Each candidate is a floor for
the leakage form on the constrained sector, and each is attained by a nonzero vector there, so the
two floors bound each other. -/
theorem IsSectorConstrainedGround.unique {a : ℝ} {σ : ℕ → ℕ} {μ μ' : ℝ}
    (h : IsSectorConstrainedGround a σ μ) (h' : IsSectorConstrainedGround a σ μ') : μ = μ' := by
  obtain ⟨hfloor, f, ⟨x, hx⟩, hfne, hfcon, hfval, -⟩ := h
  obtain ⟨hfloor', g, ⟨y, hy⟩, hgne, hgcon, hgval, -⟩ := h'
  have hfpos : 0 < ‖f‖ ^ (2 : ℕ) := by
    have hf : 0 < ‖f‖ := norm_pos_iff.mpr hfne
    positivity
  have hgpos : 0 < ‖g‖ ^ (2 : ℕ) := by
    have hg : 0 < ‖g‖ := norm_pos_iff.mpr hgne
    positivity
  have h1 : μ' * ‖f‖ ^ (2 : ℕ) ≤ μ * ‖f‖ ^ (2 : ℕ) := by
    have hb := hfloor' x f hx hfcon
    rwa [hfval] at hb
  have h2 : μ * ‖g‖ ^ (2 : ℕ) ≤ μ' * ‖g‖ ^ (2 : ℕ) := by
    have hb := hfloor y g hy hgcon
    rwa [hgval] at hb
  have hle1 : μ' ≤ μ := le_of_mul_le_mul_right h1 hfpos
  have hle2 : μ ≤ μ' := le_of_mul_le_mul_right h2 hgpos
  linarith

/-- A function that is eventually the Fourier-even sector's constrained ground value is eventually
the sector's secular ground root. -/
theorem eventually_eq_infiniteSecularRoot_positive {μ : ℝ → ℝ}
    (hμ : ∀ᶠ a : ℝ in atTop, IsSectorConstrainedGround a positiveSectorIndex (μ a)) :
    ∀ᶠ a : ℝ in atTop, μ a
      = infiniteSecularRoot (fun j => evenProlateSignedLeakage a (2 * j))
          (fun j => ‖evenProlateConstraintCoord a (2 * j)‖) := by
  filter_upwards [hμ, eventually_isSectorConstrainedGround_positive] with a h1 h2
  exact h1.unique h2

/-- The same for the Fourier-odd sector. -/
theorem eventually_eq_infiniteSecularRoot_negative {μ : ℝ → ℝ}
    (hμ : ∀ᶠ a : ℝ in atTop, IsSectorConstrainedGround a negativeSectorIndex (μ a)) :
    ∀ᶠ a : ℝ in atTop, μ a
      = infiniteSecularRoot (fun j => evenProlateSignedLeakage a (2 * j + 1))
          (fun j => ‖evenProlateConstraintCoord a (2 * j + 1)‖) := by
  filter_upwards [hμ, eventually_isSectorConstrainedGround_negative] with a h1 h2
  exact h1.unique h2

/-! ## The two-mode ground-state card's constants, at the operator -/

/-- **Equation `(5)` of the two-mode ground-state card, in the operator's own terms.**  The
constrained leakage ground value of the Fourier-even sector, normalized by the leakage `d_4`, tends
to `8/11`. -/
theorem constrainedProlatePositive_operator_ground_ratio_tendsto {μ : ℝ → ℝ}
    (hμ : ∀ᶠ a : ℝ in atTop, IsSectorConstrainedGround a positiveSectorIndex (μ a)) :
    Tendsto (fun a : ℝ => μ a / evenProlateSignedLeakage a 2) atTop (𝓝 (8 / 11)) := by
  have h : Tendsto (fun lam : ℝ =>
      infiniteSecularRoot (fun j => evenProlateSignedLeakage lam (2 * j))
          (fun j => ‖evenProlateConstraintCoord lam (2 * j)‖)
        / evenProlateSignedLeakage lam (2 * 1)) atTop (𝓝 (8 / 11)) :=
    constrainedProlatePositive_ground_ratio_tendsto
  refine Filter.Tendsto.congr' ?_ h
  filter_upwards [eventually_eq_infiniteSecularRoot_positive hμ] with a ha
  rw [ha]

/-- **Equation `(6)` of the two-mode ground-state card, in the operator's own terms.**  The
complementary gap of the Fourier-even constrained ground value tends to `3/11`. -/
theorem constrainedProlatePositive_operator_gap_ratio_tendsto {μ : ℝ → ℝ}
    (hμ : ∀ᶠ a : ℝ in atTop, IsSectorConstrainedGround a positiveSectorIndex (μ a)) :
    Tendsto (fun a : ℝ =>
        (evenProlateSignedLeakage a 2 - μ a) / evenProlateSignedLeakage a 2)
      atTop (𝓝 (3 / 11)) := by
  have h : Tendsto (fun lam : ℝ =>
      (evenProlateSignedLeakage lam (2 * 1)
          - infiniteSecularRoot (fun j => evenProlateSignedLeakage lam (2 * j))
              (fun j => ‖evenProlateConstraintCoord lam (2 * j)‖))
        / evenProlateSignedLeakage lam (2 * 1)) atTop (𝓝 (3 / 11)) :=
    constrainedProlatePositive_gap_ratio_tendsto
  refine Filter.Tendsto.congr' ?_ h
  filter_upwards [eventually_eq_infiniteSecularRoot_positive hμ] with a ha
  rw [ha]

/-! ## The parity card's constants, at the operator -/

/-- **Equation `(6)` of the parity card, in the operator's own terms.**  The constrained leakage
ground value of the Fourier-odd sector, normalized by the leakage `d_6`, tends to `8/13`. -/
theorem constrainedProlateNegative_operator_ground_ratio_tendsto {μ : ℝ → ℝ}
    (hμ : ∀ᶠ a : ℝ in atTop, IsSectorConstrainedGround a negativeSectorIndex (μ a)) :
    Tendsto (fun a : ℝ => μ a / evenProlateSignedLeakage a 3) atTop (𝓝 (8 / 13)) := by
  have h : Tendsto (fun lam : ℝ =>
      infiniteSecularRoot (fun j => evenProlateSignedLeakage lam (2 * j + 1))
          (fun j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖)
        / evenProlateSignedLeakage lam (2 * 1 + 1)) atTop (𝓝 (8 / 13)) :=
    constrainedProlateNegative_ground_ratio_tendsto
  refine Filter.Tendsto.congr' ?_ h
  filter_upwards [eventually_eq_infiniteSecularRoot_negative hμ] with a ha
  rw [ha]

/-- **Equation `(10)` of the parity card, in the operator's own terms.**  The complementary gap of
the Fourier-odd constrained ground value tends to `5/13`; in particular its `liminf` is `5/13`. -/
theorem constrainedProlateNegative_operator_gap_ratio_tendsto {μ : ℝ → ℝ}
    (hμ : ∀ᶠ a : ℝ in atTop, IsSectorConstrainedGround a negativeSectorIndex (μ a)) :
    Tendsto (fun a : ℝ =>
        (evenProlateSignedLeakage a 3 - μ a) / evenProlateSignedLeakage a 3)
      atTop (𝓝 (5 / 13)) := by
  have h : Tendsto (fun lam : ℝ =>
      (evenProlateSignedLeakage lam (2 * 1 + 1)
          - infiniteSecularRoot (fun j => evenProlateSignedLeakage lam (2 * j + 1))
              (fun j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖))
        / evenProlateSignedLeakage lam (2 * 1 + 1)) atTop (𝓝 (5 / 13)) :=
    constrainedProlateNegative_gap_ratio_tendsto
  refine Filter.Tendsto.congr' ?_ h
  filter_upwards [eventually_eq_infiniteSecularRoot_negative hμ] with a ha
  rw [ha]

/-- **The leakage-normalized parity collapse, at the operator.**  The two Fourier-sector
constrained ground values, each normalized by its own dominant leakage, separate by `13/11`. -/
theorem constrainedProlateParity_operator_normalized_ratio_tendsto {μp μn : ℝ → ℝ}
    (hp : ∀ᶠ a : ℝ in atTop, IsSectorConstrainedGround a positiveSectorIndex (μp a))
    (hn : ∀ᶠ a : ℝ in atTop, IsSectorConstrainedGround a negativeSectorIndex (μn a)) :
    Tendsto (fun a : ℝ =>
        μp a / evenProlateSignedLeakage a 2 / (μn a / evenProlateSignedLeakage a 3))
      atTop (𝓝 (13 / 11)) := by
  have h := (constrainedProlatePositive_operator_ground_ratio_tendsto hp).div
    (constrainedProlateNegative_operator_ground_ratio_tendsto hn)
    (by norm_num : (8 : ℝ) / 13 ≠ 0)
  have hval : (8 : ℝ) / 11 / ((8 : ℝ) / 13) = 13 / 11 := by norm_num
  rw [hval] at h
  exact Filter.Tendsto.congr (fun _ => rfl) h

/-- **Equation `(8)` of the parity card, in the operator's own terms.**  The Fourier-even
constrained ground value is negligible against the Fourier-odd one. -/
theorem constrainedProlateParity_operator_ratio_tendsto_zero {μp μn : ℝ → ℝ}
    (hp : ∀ᶠ a : ℝ in atTop, IsSectorConstrainedGround a positiveSectorIndex (μp a))
    (hn : ∀ᶠ a : ℝ in atTop, IsSectorConstrainedGround a negativeSectorIndex (μn a)) :
    Tendsto (fun a : ℝ => μp a / μn a) atTop (𝓝 0) := by
  have h : Tendsto (fun lam : ℝ =>
      infiniteSecularRoot (fun j => evenProlateSignedLeakage lam (2 * j))
          (fun j => ‖evenProlateConstraintCoord lam (2 * j)‖)
        / infiniteSecularRoot (fun j => evenProlateSignedLeakage lam (2 * j + 1))
            (fun j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖))
      atTop (𝓝 0) := tendsto_constrainedProlateParity_ratio_zero
  refine Filter.Tendsto.congr' ?_ h
  filter_upwards [eventually_eq_infiniteSecularRoot_positive hp,
    eventually_eq_infiniteSecularRoot_negative hn] with a hpa hna
  rw [hpa, hna]

/-- **Equation `(9)` of the parity card, in the operator's own terms.**  Eventually the
Fourier-even constrained ground value is strictly below the Fourier-odd one, and the gap between
them is asymptotically the whole Fourier-odd ground value. -/
theorem constrainedProlateParity_operator_separation {μp μn : ℝ → ℝ}
    (hp : ∀ᶠ a : ℝ in atTop, IsSectorConstrainedGround a positiveSectorIndex (μp a))
    (hn : ∀ᶠ a : ℝ in atTop, IsSectorConstrainedGround a negativeSectorIndex (μn a)) :
    (∀ᶠ a : ℝ in atTop, μp a < μn a) ∧
      Tendsto (fun a : ℝ => (μn a - μp a) / μn a) atTop (𝓝 1) := by
  obtain ⟨hlt, hgap⟩ :
      (∀ᶠ lam : ℝ in atTop,
          infiniteSecularRoot (fun j => evenProlateSignedLeakage lam (2 * j))
              (fun j => ‖evenProlateConstraintCoord lam (2 * j)‖)
            < infiniteSecularRoot (fun j => evenProlateSignedLeakage lam (2 * j + 1))
                (fun j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖)) ∧
        Tendsto (fun lam : ℝ =>
            (infiniteSecularRoot (fun j => evenProlateSignedLeakage lam (2 * j + 1))
                (fun j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖)
              - infiniteSecularRoot (fun j => evenProlateSignedLeakage lam (2 * j))
                  (fun j => ‖evenProlateConstraintCoord lam (2 * j)‖))
              / infiniteSecularRoot (fun j => evenProlateSignedLeakage lam (2 * j + 1))
                  (fun j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖))
          atTop (𝓝 1) := constrainedProlateParity_separation
  constructor
  · filter_upwards [hlt, eventually_eq_infiniteSecularRoot_positive hp,
      eventually_eq_infiniteSecularRoot_negative hn] with a h hpa hna
    rw [hpa, hna]
    exact h
  · refine Filter.Tendsto.congr' ?_ hgap
    filter_upwards [eventually_eq_infiniteSecularRoot_positive hp,
      eventually_eq_infiniteSecularRoot_negative hn] with a hpa hna
    rw [hpa, hna]

end RHTower

end
