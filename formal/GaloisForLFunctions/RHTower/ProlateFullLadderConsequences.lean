import GaloisForLFunctions.RHTower.ProlateFullLadderEnvelope
import GaloisForLFunctions.RHTower.ProlateGroundDistance

/-!
# The step-one ladder, instantiated

With the full signed leakage sequence a ladder envelope, the constrained transfer machinery applies
at every corpus index rather than only on the Fourier-even sublattice.  The companion constraint
data is the untruncated one: summability and the Bessel bound hold for the whole family, and the
first two coordinates converge to the ground Hermite coordinate and the first negative-sector
coordinate respectively.
-/

noncomputable section

open Set Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

theorem fullProlateLadder_sum :
    ∀ᶠ lam : ℝ in atTop,
      Summable fun j : ℕ => ‖evenProlateConstraintCoord lam j‖ ^ 2 :=
  Eventually.of_forall fun lam => summable_evenProlateConstraintCoord_sq lam

theorem fullProlateLadder_bessel :
    ∀ᶠ lam : ℝ in atTop,
      (∑' j : ℕ, ‖evenProlateConstraintCoord lam j‖ ^ 2) ≤ 2 * lam := by
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with lam hlam
  exact tsum_evenProlateConstraintCoord_sq_le hlam

theorem tendsto_norm_evenProlateConstraintCoord_zero :
    Tendsto (fun lam : ℝ => ‖evenProlateConstraintCoord lam 0‖) atTop
      (𝓝 (constrainedProlateHermiteCoordinate 0)) := by
  have h := tendsto_norm_evenProlateConstraintCoord_atTop 0
  simpa using h

theorem tendsto_norm_evenProlateConstraintCoord_one :
    Tendsto (fun lam : ℝ => ‖evenProlateConstraintCoord lam 1‖) atTop
      (𝓝 (constrainedProlateNegativeCoordinate 0)) := by
  have h := tendsto_norm_evenProlateConstraintCoord_negative_atTop 0
  simpa using h

/-- **The exact constrained ground eigenvector of the step-one prolate ladder converges to its
two-mode seed.**  The full signed leakage sequence, not only its Fourier-even sublattice. -/
theorem constrainedProlateFull_ground_distance_tendsto_zero :
    let D : ℝ → ℕ → ℝ := fun a j => evenProlateSignedLeakage a j
    let ℓ : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam j‖
    Tendsto (fun lam : ℝ => min
        (‖(‖secularLp (D lam) (ℓ lam) (infiniteSecularRoot (D lam) (ℓ lam))‖)⁻¹
            • secularLp (D lam) (ℓ lam) (infiniteSecularRoot (D lam) (ℓ lam))
          - (‖twoModeSeedLp (ℓ lam)‖)⁻¹ • twoModeSeedLp (ℓ lam)‖ ^ 2)
        (‖(‖secularLp (D lam) (ℓ lam) (infiniteSecularRoot (D lam) (ℓ lam))‖)⁻¹
            • secularLp (D lam) (ℓ lam) (infiniteSecularRoot (D lam) (ℓ lam))
          + (‖twoModeSeedLp (ℓ lam)‖)⁻¹ • twoModeSeedLp (ℓ lam)‖ ^ 2))
      atTop (nhds 0) := by
  have ha0 : constrainedProlateHermiteCoordinate 0 ≠ 0 :=
    constrainedProlateHermiteCoordinate_ne_zero 0
  have ha1 : constrainedProlateNegativeCoordinate 0 ≠ 0 :=
    (constrainedProlateNegativeCoordinate_pos 0).ne'
  exact ladderEnvelope_evenProlateSignedLeakage_full.tendsto_min_norm_ground_distance
    ha0 ha1 fullProlateLadder_sum fullProlateLadder_bessel
    tendsto_norm_evenProlateConstraintCoord_zero
    tendsto_norm_evenProlateConstraintCoord_one


/-- **Adjacent corpus indices separate.**  The leakage of every index is eventually strictly below
that of its successor — the step-one strictness the Fourier-even ladder could not see. -/
theorem eventually_signedLeakage_lt_succ (j : ℕ) :
    ∀ᶠ a : ℝ in atTop, evenProlateSignedLeakage a j < evenProlateSignedLeakage a (j + 1) :=
  ladderEnvelope_evenProlateSignedLeakage_full.lt_succ j

/-- **The adjacent leakage ratio vanishes.**  Every leakage is negligible against its immediate
successor, not only against its successor two steps along. -/
theorem tendsto_signedLeakage_succ_ratio (j : ℕ) :
    Tendsto (fun a : ℝ =>
        evenProlateSignedLeakage a j / evenProlateSignedLeakage a (j + 1)) atTop (𝓝 0) :=
  ladderEnvelope_evenProlateSignedLeakage_full.ratio_tendsto_zero j

/-- **The parity separation at the ground index.**  The Fourier-even ground leakage is eventually
strictly below the first negative-sector leakage, and negligible against it. -/
theorem eventually_signedLeakage_parity_separation :
    (∀ᶠ a : ℝ in atTop, evenProlateSignedLeakage a 0 < evenProlateSignedLeakage a 1) ∧
      Tendsto (fun a : ℝ =>
          evenProlateSignedLeakage a 0 / evenProlateSignedLeakage a 1) atTop (𝓝 0) :=
  ⟨eventually_signedLeakage_lt_succ 0, tendsto_signedLeakage_succ_ratio 0⟩

/-- **The aperture-weighted tail is negligible at every step.**  This is the input the constrained
transfer consumes when the ladder step is one. -/
theorem tendsto_signedLeakage_weighted_tail (j : ℕ) :
    Tendsto (fun a : ℝ => a * evenProlateSignedLeakage a (j + 1)
        / (evenProlateSignedLeakage a (j + 2) - evenProlateSignedLeakage a (j + 1)))
      atTop (𝓝 0) :=
  ladderEnvelope_evenProlateSignedLeakage_full.tail_tendsto_zero j


/-! ## The interleaved coordinate sequence and the step-one depth ratio -/

/-- The limit of the constraint coordinate at index `j`: the Hermite coordinate on even indices and
the negative-sector coordinate on odd ones. -/
def fullLadderCoordinate (j : ℕ) : ℝ :=
  if j % 2 = 0 then constrainedProlateHermiteCoordinate (j / 2)
  else constrainedProlateNegativeCoordinate (j / 2)

theorem fullLadderCoordinate_ne_zero (j : ℕ) : fullLadderCoordinate j ≠ 0 := by
  rw [fullLadderCoordinate]
  by_cases h : j % 2 = 0
  · rw [if_pos h]
    exact constrainedProlateHermiteCoordinate_ne_zero (j / 2)
  · rw [if_neg h]
    exact (constrainedProlateNegativeCoordinate_pos (j / 2)).ne'

theorem tendsto_norm_evenProlateConstraintCoord_full (j : ℕ) :
    Tendsto (fun lam : ℝ => ‖evenProlateConstraintCoord lam j‖) atTop
      (𝓝 (fullLadderCoordinate j)) := by
  rcases Nat.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
  · have hj : j = 2 * i := by omega
    subst hj
    have hval : fullLadderCoordinate (2 * i) = constrainedProlateHermiteCoordinate i := by
      rw [fullLadderCoordinate, if_pos (by omega)]
      congr 1
      omega
    rw [hval]
    exact tendsto_norm_evenProlateConstraintCoord_atTop i
  · have hj : j = 2 * i + 1 := by omega
    subst hj
    have hval : fullLadderCoordinate (2 * i + 1) = constrainedProlateNegativeCoordinate i := by
      rw [fullLadderCoordinate, if_neg (by omega)]
      congr 1
      omega
    rw [hval]
    exact tendsto_norm_evenProlateConstraintCoord_negative_atTop i

theorem fullLadderCoordinate_squareSum_pos (k : ℕ) :
    0 < ∑ j ∈ Finset.range (k + 1), fullLadderCoordinate j ^ 2 := by
  have hmem : (0 : ℕ) ∈ Finset.range (k + 1) := Finset.mem_range.2 (by omega)
  have hnn : ∀ j ∈ Finset.range (k + 1), (0 : ℝ) ≤ fullLadderCoordinate j ^ 2 :=
    fun j _ => sq_nonneg _
  have h0 : (0 : ℝ) < fullLadderCoordinate 0 ^ 2 := by
    have := fullLadderCoordinate_ne_zero 0
    positivity
  have hle := Finset.single_le_sum (f := fun j => fullLadderCoordinate j ^ 2) hnn hmem
  linarith [hle, h0]

/-- The step-one contrast: the Hermite theta of the interleaved coordinate sequence. -/
def fullLadderTheta (k : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (k + 1), fullLadderCoordinate j ^ 2)
    / ((∑ j ∈ Finset.range (k + 1), fullLadderCoordinate j ^ 2)
      + fullLadderCoordinate (k + 1) ^ 2)

/-- **The step-one analogue of `(8)`.**  The depth-`k` constrained eigenvalue of the FULL signed
leakage ladder, normalized by the next leakage, converges to the contrast of the interleaved
coordinate sequence. -/
theorem constrainedProlateFull_depth_ratio_tendsto (k : ℕ) :
    Tendsto (fun lam : ℝ =>
      depthSecularRoot (fun j => evenProlateSignedLeakage lam j)
          (fun j => ‖evenProlateConstraintCoord lam j‖) k
        / evenProlateSignedLeakage lam (k + 1))
      atTop (𝓝 (fullLadderTheta k)) := by
  have h := depthSecularRoot_ratio_tendsto
    (d := fun lam j => evenProlateSignedLeakage lam j)
    (ℓ := fun lam j => ‖evenProlateConstraintCoord lam j‖)
    (k := k) (a := fullLadderCoordinate)
    (fullLadderCoordinate_squareSum_pos k) (fullLadderCoordinate_ne_zero (k + 1))
    (ladderEnvelope_evenProlateSignedLeakage_full.depth_struct k)
    fullProlateLadder_sum fullProlateLadder_bessel
    (ladderEnvelope_evenProlateSignedLeakage_full.ratio_tendsto_zero k)
    (ladderEnvelope_evenProlateSignedLeakage_full.tail_tendsto_zero k)
    (fun j _ => tendsto_norm_evenProlateConstraintCoord_full j)
  rwa [← fullLadderTheta] at h


theorem fullLadderTheta_pos (k : ℕ) : 0 < fullLadderTheta k := by
  have hS : 0 < ∑ j ∈ Finset.range (k + 1), fullLadderCoordinate j ^ 2 :=
    fullLadderCoordinate_squareSum_pos k
  have hA : (0 : ℝ) ≤ fullLadderCoordinate (k + 1) ^ 2 := sq_nonneg _
  rw [fullLadderTheta]
  exact div_pos hS (by linarith)

/-- **The step-one analogue of `(9)`.**  Two consecutive constrained eigenvalues of the full ladder,
each normalized by its own next leakage, separate by exactly the contrast quotient. -/
theorem constrainedProlateFull_adjacent_ratio_tendsto (k : ℕ) :
    Tendsto (fun lam : ℝ =>
        (depthSecularRoot (fun j => evenProlateSignedLeakage lam j)
            (fun j => ‖evenProlateConstraintCoord lam j‖) (k + 1)
          / evenProlateSignedLeakage lam (k + 2))
          / (depthSecularRoot (fun j => evenProlateSignedLeakage lam j)
              (fun j => ‖evenProlateConstraintCoord lam j‖) k
            / evenProlateSignedLeakage lam (k + 1)))
      atTop (𝓝 (fullLadderTheta (k + 1) / fullLadderTheta k)) := by
  have h1 := constrainedProlateFull_depth_ratio_tendsto (k + 1)
  have h2 := constrainedProlateFull_depth_ratio_tendsto k
  exact h1.div h2 (fullLadderTheta_pos k).ne'

end RHTower

end
