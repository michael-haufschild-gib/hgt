import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfMovingAnchorFlatnessNoGo
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCayleyLimit
import GaloisForLFunctions.RHTower.ThetaCuspHawkingFZZSchwarzschildCompletedResponseBoundedJetFiltrationNoGo

/-!
# Sharpness of moving-anchor compact escape

Increasing-order zeros are compatible with compact-open convergence to a nonzero holomorphic
limit when their anchors escape.  The explicit entire gauges

`Bₙ(s) = (1 - s / (n + 1)²)^(n + 1)`

converge locally uniformly to one, while their first `n + 1` jets vanish at the far-right anchor
`(n + 1)²`.  Those anchors lie in `rightHalf` and eventually avoid every compact set.

This proves that the compactness condition in the moving-anchor flatness no-go is sharp.  It does
not construct an arithmetic half-divisor: the zeros and coefficients here are inserted by hand.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Far-right anchor supporting an increasing-order zero. -/
def farRightFlatEscapeAnchor (n : ℕ) : ℂ := ((n + 1 : ℕ) : ℂ) ^ (2 : ℕ)

/-- Normalized entire gauge with a zero of order `n + 1` at `farRightFlatEscapeAnchor n`. -/
def farRightFlatEscapeGauge (n : ℕ) (s : ℂ) : ℂ :=
  (1 - s / farRightFlatEscapeAnchor n) ^ (n + 1)

private theorem farRightFlatEscape_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)))
      atTop (nhds 0) := by
  convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) using 1
  funext n
  push_cast
  field_simp

/-- Despite their increasing zero order, the escaping gauges converge compact-open to one. -/
theorem farRightFlatEscapeGauge_tendstoLocallyUniformly_one :
    TendstoLocallyUniformly farRightFlatEscapeGauge (fun _ : ℂ => 1) atTop := by
  have hbase := tendstoLocallyUniformly_one_add_div_pow
    (a := fun n : ℕ => ((n + 1 : ℕ) : ℝ))
    (d := fun n : ℕ => n + 1)
    (fun n => by positivity)
    farRightFlatEscape_ratio_tendsto_zero
  have hcomp := hbase.comp (fun s : ℂ => -s) (by fun_prop)
  convert hcomp using 1
  · funext n s
    change (1 - s / (((n + 1 : ℕ) : ℂ) ^ (2 : ℕ))) ^ (n + 1) =
      (1 + (-s) / (((((n + 1 : ℕ) : ℝ) : ℂ)) ^ (2 : ℕ))) ^ (n + 1)
    norm_num
    congr 1
    ring
  · funext s
    simp

/-- Every escaping gauge is entire. -/
theorem farRightFlatEscapeGauge_analyticOnNhd (n : ℕ) :
    AnalyticOnNhd ℂ (farRightFlatEscapeGauge n) Set.univ := by
  intro s _
  unfold farRightFlatEscapeGauge farRightFlatEscapeAnchor
  fun_prop

/-- All jets through order `n` vanish at the `n`-th escaping anchor. -/
theorem farRightFlatEscapeGauge_jet_zero
    (n j : ℕ) (hj : j ≤ n) :
    iteratedDeriv j (farRightFlatEscapeGauge n) (farRightFlatEscapeAnchor n) = 0 := by
  unfold farRightFlatEscapeGauge
  apply iteratedDeriv_pow_eq_zero_before_order
    (W := fun s : ℂ => 1 - s / farRightFlatEscapeAnchor n)
    (by fun_prop) (z := farRightFlatEscapeAnchor n) (by
      unfold farRightFlatEscapeAnchor
      have hnbase : (n : ℂ) + 1 ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      have hn : ((n : ℂ) + 1) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hnbase
      field_simp
      ring)
    (n + 1) j
  omega

/-- Every anchor lies in the strict right half-plane. -/
theorem farRightFlatEscapeAnchor_mem_rightHalf (n : ℕ) :
    farRightFlatEscapeAnchor n ∈ rightHalf := by
  rw [mem_rightHalf]
  have hre : (farRightFlatEscapeAnchor n).re = (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
    simp [farRightFlatEscapeAnchor, pow_two, Complex.mul_re]
  rw [hre]
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  nlinarith [sq_nonneg (((n + 1 : ℕ) : ℝ))]

/-- Real parts of the anchors tend to positive infinity. -/
theorem farRightFlatEscapeAnchor_re_tendsto_atTop :
    Tendsto (fun n => (farRightFlatEscapeAnchor n).re) atTop atTop := by
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hsq := hbase.atTop_mul_atTop₀ hbase
  convert hsq using 1
  funext n
  simp [farRightFlatEscapeAnchor, pow_two, Complex.mul_re]

/-- The anchors eventually avoid every compact subset of the plane. -/
theorem farRightFlatEscapeAnchor_eventually_avoid_compact
    {K : Set ℂ} (hK : IsCompact K) :
    ∀ᶠ n in atTop, farRightFlatEscapeAnchor n ∉ K := by
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  filter_upwards [farRightFlatEscapeAnchor_re_tendsto_atTop.eventually_gt_atTop R] with n hn
  intro hmem
  have hnorm := Metric.mem_closedBall.mp (hKR hmem)
  rw [dist_zero_right] at hnorm
  exact (not_lt_of_ge (Complex.re_le_norm (farRightFlatEscapeAnchor n)))
    (lt_of_le_of_lt hnorm hn)

end

end RHTower
