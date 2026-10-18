import GaloisForLFunctions.RHTower.FiniteDirichletPolynomialSelfReturn
import GaloisForLFunctions.RHTower.ZetaStrongRecurrenceReceiver

/-!
# The conditioned-tail gap after finite Dirichlet polynomial recurrence

The error needed to transfer self-return is the difference of the two tails,
including the tail at the starting point. The unconditional measure inequality
below isolates the bad part of the finite-head return set. A bound for a tail
averaged over all heights does not itself bound this conditioned loss.
-/

open Complex Filter Topology MeasureTheory Set

noncomputable section

namespace RHTower

/-- Tail increment relative to the same finite head at both endpoints. -/
def centeredZetaTail (a : ℕ → ℂ) (s : Finset ℕ) (z : ℂ) (τ : ℝ) : ℂ :=
  (riemannZeta (z + (τ : ℂ) * I) - edPoly a s (z + (τ : ℂ) * I)) -
    (riemannZeta z - edPoly a s z)

def centeredZetaTailReturnSet (a : ℕ → ℂ) (s : Finset ℕ)
    (K : Set ℂ) (ε : ℝ) : Set ℝ :=
  {τ | ∀ z ∈ K, ‖centeredZetaTail a s z τ‖ < ε}

/-- The exact head/tail decomposition retains the fixed base-point tail. -/
theorem zeta_self_difference_eq_head_add_centeredTail
    (a : ℕ → ℂ) (s : Finset ℕ) (z : ℂ) (τ : ℝ) :
    riemannZeta (z + (τ : ℂ) * I) - riemannZeta z =
      (edPoly a s (z + (τ : ℂ) * I) - edPoly a s z) +
        centeredZetaTail a s z τ := by
  unfold centeredZetaTail
  ring

theorem headReturn_inter_centeredTailReturn_subset_zetaReturn
    (a : ℕ → ℂ) (s : Finset ℕ) (K : Set ℂ) (ε η : ℝ) :
    edPolyReturnSet a s K ε ∩ centeredZetaTailReturnSet a s K η ⊆
      zetaReturnSet K (ε + η) := by
  rintro τ ⟨hhead, htail⟩ z hz
  rw [zeta_self_difference_eq_head_add_centeredTail a s z τ]
  exact (norm_add_le _ _).trans_lt (add_lt_add (hhead z hz) (htail z hz))

/-- Conversely, joint return of zeta and the head forces return of the
centered tail. This is a two-sided pointwise description of the gap. -/
theorem zetaReturn_inter_headReturn_subset_centeredTailReturn
    (a : ℕ → ℂ) (s : Finset ℕ) (K : Set ℂ) (ε η : ℝ) :
    zetaReturnSet K ε ∩ edPolyReturnSet a s K η ⊆
      centeredZetaTailReturnSet a s K (ε + η) := by
  rintro τ ⟨hzeta, hhead⟩ z hz
  have hid : centeredZetaTail a s z τ =
      (riemannZeta (z + (τ : ℂ) * I) - riemannZeta z) -
        (edPoly a s (z + (τ : ℂ) * I) - edPoly a s z) := by
    unfold centeredZetaTail
    ring
  rw [hid]
  exact (norm_sub_le _ _).trans_lt (add_lt_add (hzeta z hz) (hhead z hz))

/-- Unconditional loss accounting, valid without measurability assumptions on
the compact-set supremum. Only bad tails on head-return times are charged. -/
theorem measure_headReturn_le_zetaReturn_add_conditionedTailLoss
    (a : ℕ → ℂ) (s : Finset ℕ) (K : Set ℂ) (ε η T : ℝ) :
    volume (edPolyReturnSet a s K ε ∩ Icc 0 T) ≤
      volume (zetaReturnSet K (ε + η) ∩ Icc 0 T) +
        volume ((edPolyReturnSet a s K ε \ centeredZetaTailReturnSet a s K η) ∩ Icc 0 T) := by
  apply (measure_mono ?_).trans (measure_union_le _ _)
  rintro τ ⟨hhead, hT⟩
  by_cases htail : τ ∈ centeredZetaTailReturnSet a s K η
  · exact Or.inl ⟨headReturn_inter_centeredTailReturn_subset_zetaReturn
      a s K ε η ⟨hhead, htail⟩, hT⟩
  · exact Or.inr ⟨⟨hhead, htail⟩, hT⟩

/-- The finite theorem supplies a positive density. Losing at most half of
that density to the centered tail would transfer recurrence to zeta. The
conditioned loss remains an explicit premise, not a claimed analytic theorem. -/
theorem exists_density_with_conditionedTail_transfer (a : ℕ → ℂ)
    {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) {K : Set ℂ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ κ : ℝ, 0 < κ ∧
      (∀ᶠ T : ℝ in atTop,
        ENNReal.ofReal (κ * T) ≤ volume (edPolyReturnSet a s K ε ∩ Icc 0 T)) ∧
      ((∀ᶠ T : ℝ in atTop,
        volume ((edPolyReturnSet a s K ε \ centeredZetaTailReturnSet a s K ε) ∩ Icc 0 T) ≤
          ENNReal.ofReal (κ / 2 * T)) →
        ∀ᶠ T : ℝ in atTop,
          ENNReal.ofReal (κ / 2 * T) ≤ volume (zetaReturnSet K (2 * ε) ∩ Icc 0 T)) := by
  obtain ⟨κ, hκ, hhead⟩ := exists_pos_density_edPolyReturnSet a hs hK hε
  refine ⟨κ, hκ, hhead, fun htail => ?_⟩
  filter_upwards [hhead, htail, eventually_ge_atTop 0] with T hH hL hT
  have hsplit := measure_headReturn_le_zetaReturn_add_conditionedTailLoss a s K ε ε T
  have hsum := hH.trans (hsplit.trans (add_le_add le_rfl hL))
  have hnonneg : 0 ≤ κ / 2 * T := by positivity
  have hdouble : ENNReal.ofReal (κ * T) =
      ENNReal.ofReal (κ / 2 * T) + ENNReal.ofReal (κ / 2 * T) := by
    rw [← ENNReal.ofReal_add hnonneg hnonneg]
    congr 1
    ring
  rw [hdouble, show ε + ε = 2 * ε by ring] at hsum
  exact ENNReal.le_of_add_le_add_right (ENNReal.ofReal_ne_top) hsum

end RHTower
