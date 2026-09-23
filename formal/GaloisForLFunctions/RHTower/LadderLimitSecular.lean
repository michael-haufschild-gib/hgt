import GaloisForLFunctions.RHTower.ConstrainedProlateHermiteContrast
import GaloisForLFunctions.RHTower.TwoModeFuchsLimit

/-!
# The limiting secular function of the fixed-mode ladder

At each rung of the fixed-mode spectral ladder the rescaled secular equation converges to the
two-pole limit `H(x) = −S/x + w/(1−x)` on `(0,1)`: the head modes coalesce into a single pole
of mass `S` at `0` and the next mode contributes the pole of mass `w` at `1`.  This limit is
strictly increasing on `(0,1)` (`ladderLimitSecular_strictMonoOn`), vanishes exactly at the
mass ratio `x = S/(S+w)` (`ladderLimitSecular_root`, `ladderLimitSecular_root_unique`), and
with the Hermite contrast weights of the radial prolate family the ratio is precisely the
ladder constant `θ_k = Q_k/Q_{k+1}` (`ladderLimitSecular_theta_root`,
`ladderLimitSecular_theta_unique`): the `k`-th constrained eigenvalue, normalized by the
`(k+1)`-st leakage, converges to the unique zero of this limit.
-/

namespace RHTower

/-- The two-pole limiting secular function `−S/x + w/(1−x)`. -/
noncomputable def ladderLimitSecular (S w x : ℝ) : ℝ := -S / x + w / (1 - x)

theorem ladderLimitSecular_strictMonoOn {S w : ℝ} (hS : 0 < S) (hw : 0 < w) :
    StrictMonoOn (ladderLimitSecular S w) (Set.Ioo 0 1) := by
  intro x hx y hy hxy
  unfold ladderLimitSecular
  have h1 : -S / x < -S / y := by
    rw [neg_div, neg_div, neg_lt_neg_iff]
    exact div_lt_div_of_pos_left hS hx.1 hxy
  have h2 : w / (1 - x) < w / (1 - y) :=
    div_lt_div_of_pos_left hw (by linarith [hy.2]) (by linarith)
  linarith

theorem ladderLimitSecular_root {S w : ℝ} (hS : 0 < S) (hw : 0 < w) :
    ladderLimitSecular S w (S / (S + w)) = 0 := by
  unfold ladderLimitSecular
  have hSw : S + w ≠ 0 := by positivity
  have h1 : (1 : ℝ) - S / (S + w) = w / (S + w) := by field_simp; ring
  rw [h1]
  field_simp
  ring

theorem ladderLimitSecular_root_unique {S w x : ℝ} (hS : 0 < S) (hw : 0 < w)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (h0 : ladderLimitSecular S w x = 0) :
    x = S / (S + w) := by
  have hmem : S / (S + w) ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨div_pos hS (by positivity), (div_lt_one (by positivity)).2 (by linarith)⟩
  exact (ladderLimitSecular_strictMonoOn hS hw).injOn hx hmem
    (h0.trans (ladderLimitSecular_root hS hw).symm)

/-- **The ladder constant is the zero of the limiting secular function**: with the Hermite
contrast weights, the two-pole limit at rung `k` vanishes at `θ_k = Q_k/Q_{k+1}`. -/
theorem ladderLimitSecular_theta_root (k : ℕ) :
    ladderLimitSecular (constrainedProlateHermiteWeightSum k)
      (constrainedProlateHermiteWeight (k + 1)) (constrainedProlateHermiteTheta k) = 0 := by
  rw [constrainedProlateHermiteTheta, constrainedProlateHermiteWeightSum_succ]
  exact ladderLimitSecular_root (constrainedProlateHermiteWeightSum_pos k)
    (constrainedProlateHermiteWeight_pos (k + 1))

/-- Uniqueness at rung `k`: any interior zero of the limiting secular function is `θ_k`. -/
theorem ladderLimitSecular_theta_unique {k : ℕ} {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (h0 : ladderLimitSecular (constrainedProlateHermiteWeightSum k)
      (constrainedProlateHermiteWeight (k + 1)) x = 0) :
    x = constrainedProlateHermiteTheta k := by
  rw [constrainedProlateHermiteTheta, constrainedProlateHermiteWeightSum_succ]
  exact ladderLimitSecular_root_unique (constrainedProlateHermiteWeightSum_pos k)
    (constrainedProlateHermiteWeight_pos (k + 1)) hx h0

/-- **Rung-`k` eigenvalue ratio under the Fuchs rate model.**  With head mass `Q_k`
(the coalesced first `k+1` contrast weights) and next weight `w_{k+1}`, the two-mode secular
root normalized by the dominant Fuchs rate converges to the ladder constant
`θ_k = Q_k/Q_{k+1}`. -/
theorem ladder_rung_ratio_tendsto (k : ℕ) {A₀ A₁ : ℝ} (hA₀ : 0 < A₀) (hA₁ : 0 < A₁)
    (n : ℕ) {m : ℕ} (hm : m ≠ 0) :
    Filter.Tendsto (fun lam : ℝ =>
        GaloisForLFunctions.twoModeSecularRoot
            (fuchsRate A₀ n lam) (fuchsRate A₁ (n + m) lam)
            (Real.sqrt (constrainedProlateHermiteWeightSum k))
            (Real.sqrt (constrainedProlateHermiteWeight (k + 1)))
          / fuchsRate A₁ (n + m) lam)
      Filter.atTop (nhds (constrainedProlateHermiteTheta k)) := by
  have hS := constrainedProlateHermiteWeightSum_pos k
  have hw := constrainedProlateHermiteWeight_pos (k + 1)
  have hsqS : Real.sqrt (constrainedProlateHermiteWeightSum k) ^ (2 : ℕ)
      = constrainedProlateHermiteWeightSum k := Real.sq_sqrt hS.le
  have hsqw : Real.sqrt (constrainedProlateHermiteWeight (k + 1)) ^ (2 : ℕ)
      = constrainedProlateHermiteWeight (k + 1) := Real.sq_sqrt hw.le
  have hl : Real.sqrt (constrainedProlateHermiteWeightSum k) ^ (2 : ℕ)
      + Real.sqrt (constrainedProlateHermiteWeight (k + 1)) ^ (2 : ℕ) ≠ 0 := by
    rw [hsqS, hsqw]; positivity
  have h := twoModeSecularRoot_fuchs_ratio_tendsto hA₀ hA₁ n hm hl
  rw [hsqS, hsqw, ← constrainedProlateHermiteWeightSum_succ,
    ← constrainedProlateHermiteTheta] at h
  exact h

end RHTower
