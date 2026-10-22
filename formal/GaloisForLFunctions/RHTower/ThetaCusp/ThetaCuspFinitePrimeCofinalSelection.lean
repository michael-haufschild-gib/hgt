import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimeWeightedTail

/-!
# Cofinal diagonal selection for finite-prime theta sources

Smooth compact-local convergence is diagonalized into one strictly increasing sequence of prime
cutoffs.  At stage `j`, the selected cutoff simultaneously controls every derivative order
`m ≤ j` on `[-j-1,j+1]` with error below `exp(-j²)`.

The selection is source-defined: it uses only the established finite-prime convergence theorem,
not any zero or divisor data.
-/

open Filter Topology Set

noncomputable section

namespace RHTower

/-- Accuracy target for the first `j+1` logarithmic derivatives on the `j`-th compact interval. -/
def finitePrimeThetaCuspScreenAccuracy (j N : ℕ) : Prop :=
  ∀ m ≤ j, ∀ x ∈ Icc (-((j + 1 : ℕ) : ℝ)) ((j + 1 : ℕ) : ℝ),
    |iteratedDeriv m (finitePrimeThetaCuspSource N) x -
      iteratedDeriv m thetaCuspFullSource x| < Real.exp (-((j : ℝ) ^ (2 : ℕ)))

theorem exists_finitePrimeThetaCuspDerivativeThreshold (j m : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x ∈ Icc (-((j + 1 : ℕ) : ℝ)) ((j + 1 : ℕ) : ℝ),
      |iteratedDeriv m (finitePrimeThetaCuspSource N) x -
        iteratedDeriv m thetaCuspFullSource x| < Real.exp (-((j : ℝ) ^ (2 : ℕ))) := by
  have hconv := iteratedDeriv_finitePrimeThetaCuspSource_tendstoUniformlyOn_Icc
    m ((j + 1 : ℕ) : ℝ)
  have hev := (Metric.tendstoUniformlyOn_iff.mp hconv)
    (Real.exp (-((j : ℝ) ^ (2 : ℕ)))) (Real.exp_pos _)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  refine ⟨N₀, fun N hN x hx ↦ ?_⟩
  simpa [Real.dist_eq, abs_sub_comm] using hN₀ N hN x hx

/-- A threshold for one derivative and one screen stage. -/
noncomputable def finitePrimeThetaCuspDerivativeThreshold (j m : ℕ) : ℕ :=
  Classical.choose (exists_finitePrimeThetaCuspDerivativeThreshold j m)

theorem finitePrimeThetaCuspDerivativeThreshold_spec (j m : ℕ) {N : ℕ}
    (hN : finitePrimeThetaCuspDerivativeThreshold j m ≤ N) :
    ∀ x ∈ Icc (-((j + 1 : ℕ) : ℝ)) ((j + 1 : ℕ) : ℝ),
      |iteratedDeriv m (finitePrimeThetaCuspSource N) x -
        iteratedDeriv m thetaCuspFullSource x| < Real.exp (-((j : ℝ) ^ (2 : ℕ))) :=
  (Classical.choose_spec (exists_finitePrimeThetaCuspDerivativeThreshold j m)) N hN

/-- One threshold controlling every derivative order through `j`. -/
noncomputable def finitePrimeThetaCuspAccuracyThreshold (j : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (j + 1), finitePrimeThetaCuspDerivativeThreshold j m

theorem finitePrimeThetaCuspDerivativeThreshold_le_accuracyThreshold
    {j m : ℕ} (hm : m ≤ j) :
    finitePrimeThetaCuspDerivativeThreshold j m ≤
      finitePrimeThetaCuspAccuracyThreshold j := by
  unfold finitePrimeThetaCuspAccuracyThreshold
  exact Finset.single_le_sum (fun i _ ↦ Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hm))

theorem finitePrimeThetaCuspAccuracyThreshold_spec (j : ℕ) {N : ℕ}
    (hN : finitePrimeThetaCuspAccuracyThreshold j ≤ N) :
    finitePrimeThetaCuspScreenAccuracy j N := by
  intro m hm x hx
  exact finitePrimeThetaCuspDerivativeThreshold_spec j m
    ((finitePrimeThetaCuspDerivativeThreshold_le_accuracyThreshold hm).trans hN) x hx

/-- Strictly increasing cofinal choice of prime cutoffs satisfying every stage accuracy target. -/
noncomputable def finitePrimeThetaCuspScreenIndex : ℕ → ℕ
  | 0 => finitePrimeThetaCuspAccuracyThreshold 0
  | j + 1 => max (finitePrimeThetaCuspAccuracyThreshold (j + 1))
      (finitePrimeThetaCuspScreenIndex j + 1)

theorem finitePrimeThetaCuspScreenIndex_strictMono :
    StrictMono finitePrimeThetaCuspScreenIndex := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [finitePrimeThetaCuspScreenIndex]
  exact (Nat.lt_succ_self _).trans_le (le_max_right _ _)

theorem finitePrimeThetaCuspAccuracyThreshold_le_screenIndex (j : ℕ) :
    finitePrimeThetaCuspAccuracyThreshold j ≤ finitePrimeThetaCuspScreenIndex j := by
  cases j with
  | zero => rfl
  | succ j =>
      rw [finitePrimeThetaCuspScreenIndex]
      exact le_max_left _ _

theorem finitePrimeThetaCuspScreenIndex_accuracy (j : ℕ) :
    finitePrimeThetaCuspScreenAccuracy j (finitePrimeThetaCuspScreenIndex j) :=
  finitePrimeThetaCuspAccuracyThreshold_spec j
    (finitePrimeThetaCuspAccuracyThreshold_le_screenIndex j)

theorem finitePrimeThetaCuspScreenIndex_tendsto :
    Tendsto finitePrimeThetaCuspScreenIndex atTop atTop :=
  finitePrimeThetaCuspScreenIndex_strictMono.tendsto_atTop

end RHTower
