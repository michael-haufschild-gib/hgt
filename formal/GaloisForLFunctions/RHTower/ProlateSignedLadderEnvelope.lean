import GaloisForLFunctions.RHTower.ProlateLeakageLadderRatio
import GaloisForLFunctions.RHTower.ProlateConstrainedClockCapstone
import GaloisForLFunctions.RHTower.ConstrainedProlateDepthVectorLimit

/-!
# The actual signed prolate leakages form a ladder envelope

The Fourier-even renumbering `j ↦ 2j` of the actual signed prolate leakage family satisfies every
hypothesis the constrained transfer consumes: the family is nonnegative and index-monotone, each
step is eventually strict, each leakage is negligible against its successor, and even the
aperture-weighted leakage is negligible against the next gap.

The last two are the exponent bookkeeping of the two explicit bounds.  One Fourier-even step moves
the corpus index by two, hence the separation constant `c·s` by `8`, hence the bandwidth exponent by
`4`; the explicit bounds lose only `1` above and `2` below, and the phase split can be made to lose
as little as one likes.  So a step buys `4 - 3 = 1` power of the bandwidth, and half of that pays
for the aperture weight of the tail.

With the envelope in hand the clock-universal exact-eigenpair and raw-defect law holds for the true
prolate family with no hypothesis at all.
-/

noncomputable section

open Set MeasureTheory Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

/-- The bandwidth exponent of one Fourier-even ladder step is strictly favourable: the phase split
at height `Q` loses less than the step gains. -/
theorem ladder_gap_aux {Q : ℝ} (hQ : 2 ≤ Q) :
    (Q - 1) / Real.sqrt (1 - 1 / Q ^ 2) < Q := by
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hQsq : (0 : ℝ) < Q ^ 2 := by positivity
  have hQ4 : (4 : ℝ) ≤ Q ^ 2 := by nlinarith
  have hpos : (0 : ℝ) < 1 - 1 / Q ^ 2 := by
    have h : 1 / Q ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ hQsq (by norm_num : (0 : ℝ) < 4)]
      linarith
    linarith
  have hr0 : (0 : ℝ) < Real.sqrt (1 - 1 / Q ^ 2) := Real.sqrt_pos.2 hpos
  have hrsq : Real.sqrt (1 - 1 / Q ^ 2) ^ 2 = 1 - 1 / Q ^ 2 := Real.sq_sqrt hpos.le
  have hkey : (Q * Real.sqrt (1 - 1 / Q ^ 2)) ^ 2 = Q ^ 2 - 1 := by
    rw [mul_pow, hrsq]
    field_simp
  rw [div_lt_iff₀ hr0]
  have hprod : (0 : ℝ) < Q * Real.sqrt (1 - 1 / Q ^ 2) := mul_pos hQ0 hr0
  refine lt_of_pow_lt_pow_left₀ 2 hprod.le ?_
  rw [hkey]
  nlinarith

theorem eventually_evenProlateSignedLeakage_pos (n : ℕ) (hn : 1 ≤ n) :
    ∀ᶠ a : ℝ in atTop, 0 < evenProlateSignedLeakage a n := by
  filter_upwards [eventually_signedLeakage_ge_pow n hn,
    tendsto_signedModeRadialBandwidth_atTop.eventually_ge_atTop (1 : ℝ)] with a hlow hc1
  have hc0 : (0 : ℝ) < signedModeRadialBandwidth a := by linarith
  refine lt_of_lt_of_le ?_ hlow
  have h1 : (0 : ℝ) < signedModeRadialBandwidth a ^ (-2 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have h2 : (0 : ℝ) < signedModeRadialBandwidth a
      ^ (signedModeRadialBandwidth a * (signedModeRadialData a n).s / 2) :=
    Real.rpow_pos_of_pos hc0 _
  have h3 := leakageLadderLowerConst_pos hn
  exact mul_pos (mul_pos (mul_pos (mul_pos h3 h1) (Real.exp_pos _)) (Real.exp_pos _)) h2

/-- **One Fourier-even ladder step separates the leakages.** -/
theorem tendsto_evenProlateSignedLeakage_step_ratio (j : ℕ) :
    Tendsto (fun a : ℝ =>
      evenProlateSignedLeakage a (2 * j) / evenProlateSignedLeakage a (2 * j + 2))
      atTop (𝓝 0) := by
  have hn : 1 ≤ 2 * j + 2 := by omega
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hK : (2 : ℝ) ≤ 8 * (j : ℝ) + 3 := by linarith
  have haux := ladder_gap_aux (Q := 8 * (j : ℝ) + 3) hK
  have hr0 : (0 : ℝ) < Real.sqrt (1 - 1 / (8 * (j : ℝ) + 3) ^ 2) := by
    refine Real.sqrt_pos.2 ?_
    have h : 1 / (8 * (j : ℝ) + 3) ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
      nlinarith
    linarith
  have hmono : (8 * (j : ℝ) + 1) / Real.sqrt (1 - 1 / (8 * (j : ℝ) + 3) ^ 2)
      ≤ (8 * (j : ℝ) + 3 - 1) / Real.sqrt (1 - 1 / (8 * (j : ℝ) + 3) ^ 2) := by
    rw [← sub_nonneg, ← sub_div]
    exact div_nonneg (by linarith) hr0.le
  have hgap : (0 : ℝ) + 3 + (4 * ((2 * j : ℕ) : ℝ) + 1)
        / (2 * Real.sqrt (1 - 1 / (8 * (j : ℝ) + 3) ^ 2))
      - (4 * ((2 * j + 2 : ℕ) : ℝ) + 1) / 2 < 0 := by
    push_cast
    have hsplit : (4 * (2 * (j : ℝ)) + 1) / (2 * Real.sqrt (1 - 1 / (8 * (j : ℝ) + 3) ^ 2))
        = (8 * (j : ℝ) + 1) / Real.sqrt (1 - 1 / (8 * (j : ℝ) + 3) ^ 2) / 2 := by
      rw [div_div]
      congr 1
      · ring
      · ring
    rw [hsplit]
    linarith [hmono, haux]
  have h := tendsto_signedLeakage_ratio_pow (2 * j) (2 * j + 2) hn 0 (8 * (j : ℝ) + 3) hK hgap
  simpa [Real.rpow_zero] using h

/-- **The aperture-weighted leakage is negligible against the next ladder gap.** -/
theorem tendsto_evenProlateSignedLeakage_step_tail (j : ℕ) :
    Tendsto (fun a : ℝ => a * evenProlateSignedLeakage a (2 * j + 2)
      / (evenProlateSignedLeakage a (2 * j + 4) - evenProlateSignedLeakage a (2 * j + 2)))
      atTop (𝓝 0) := by
  have hn : 1 ≤ 2 * j + 4 := by omega
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hK : (2 : ℝ) ≤ 8 * (j : ℝ) + 10 := by linarith
  have haux := ladder_gap_aux (Q := 8 * (j : ℝ) + 10) hK
  have hgap : (1 : ℝ) / 2 + 3 + (4 * ((2 * j + 2 : ℕ) : ℝ) + 1)
        / (2 * Real.sqrt (1 - 1 / (8 * (j : ℝ) + 10) ^ 2))
      - (4 * ((2 * j + 4 : ℕ) : ℝ) + 1) / 2 < 0 := by
    push_cast
    have hsplit : (4 * (2 * (j : ℝ) + 2) + 1) / (2 * Real.sqrt (1 - 1 / (8 * (j : ℝ) + 10) ^ 2))
        = (8 * (j : ℝ) + 10 - 1) / Real.sqrt (1 - 1 / (8 * (j : ℝ) + 10) ^ 2) / 2 := by
      rw [div_div]
      congr 1
      · ring
      · ring
    rw [hsplit]
    linarith [haux]
  have hmain := tendsto_signedLeakage_ratio_pow (2 * j + 2) (2 * j + 4) hn (1 / 2)
    (8 * (j : ℝ) + 10) hK hgap
  have hmaj : Tendsto (fun a : ℝ => 2 * (signedModeRadialBandwidth a ^ ((1 : ℝ) / 2)
      * (evenProlateSignedLeakage a (2 * j + 2) / evenProlateSignedLeakage a (2 * j + 4))))
      atTop (𝓝 0) := by
    simpa using hmain.const_mul (2 : ℝ)
  have hratio := tendsto_evenProlateSignedLeakage_step_ratio (j + 1)
  simp only [show 2 * (j + 1) = 2 * j + 2 from by ring,
    show 2 * j + 2 + 2 = 2 * j + 4 from by ring] at hratio
  have hhalf : ∀ᶠ a : ℝ in atTop,
      evenProlateSignedLeakage a (2 * j + 2) / evenProlateSignedLeakage a (2 * j + 4) < 1 / 2 :=
    hratio.eventually (eventually_lt_nhds (by norm_num))
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [hhalf, eventually_evenProlateSignedLeakage_pos (2 * j + 4) hn,
      eventually_ge_atTop (0 : ℝ)] with a hlt hpos ha0
    have hstep : evenProlateSignedLeakage a (2 * j + 2)
        < 1 / 2 * evenProlateSignedLeakage a (2 * j + 4) := by
      rw [div_lt_iff₀ hpos] at hlt
      linarith
    have hden : (0 : ℝ) < evenProlateSignedLeakage a (2 * j + 4)
        - evenProlateSignedLeakage a (2 * j + 2) := by linarith
    exact div_nonneg (mul_nonneg ha0 (evenProlateSignedLeakage_nonneg a (2 * j + 2))) hden.le
  · filter_upwards [hhalf, eventually_evenProlateSignedLeakage_pos (2 * j + 4) hn,
      eventually_ge_atTop (1 : ℝ)] with a hlt hpos ha1
    have ha0 : (0 : ℝ) ≤ a := by linarith
    have hstep : evenProlateSignedLeakage a (2 * j + 2)
        < 1 / 2 * evenProlateSignedLeakage a (2 * j + 4) := by
      rw [div_lt_iff₀ hpos] at hlt
      linarith
    have hden : (0 : ℝ) < evenProlateSignedLeakage a (2 * j + 4)
        - evenProlateSignedLeakage a (2 * j + 2) := by linarith
    have hbig : evenProlateSignedLeakage a (2 * j + 4) / 2
        ≤ evenProlateSignedLeakage a (2 * j + 4) - evenProlateSignedLeakage a (2 * j + 2) := by
      linarith
    have hc : signedModeRadialBandwidth a = 2 * Real.pi * a ^ 2 := rfl
    have hcpos : (0 : ℝ) < signedModeRadialBandwidth a := by
      rw [hc]
      have := Real.pi_pos
      positivity
    have hasq : a ^ 2 ≤ signedModeRadialBandwidth a := by
      rw [hc]
      nlinarith [Real.pi_gt_three, sq_nonneg a, ha1]
    have hale : a ≤ signedModeRadialBandwidth a ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow]
      exact (Real.le_sqrt ha0 hcpos.le).mpr hasq
    have hnumnn : (0 : ℝ) ≤ evenProlateSignedLeakage a (2 * j + 2) :=
      evenProlateSignedLeakage_nonneg a (2 * j + 2)
    calc a * evenProlateSignedLeakage a (2 * j + 2)
          / (evenProlateSignedLeakage a (2 * j + 4) - evenProlateSignedLeakage a (2 * j + 2))
        ≤ signedModeRadialBandwidth a ^ ((1 : ℝ) / 2)
            * evenProlateSignedLeakage a (2 * j + 2)
            / (evenProlateSignedLeakage a (2 * j + 4) / 2) := by
          apply div_le_div₀ (by positivity) (by nlinarith [hale, hnumnn])
            (by linarith) hbig
      _ = 2 * (signedModeRadialBandwidth a ^ ((1 : ℝ) / 2)
            * (evenProlateSignedLeakage a (2 * j + 2)
              / evenProlateSignedLeakage a (2 * j + 4))) := by
          field_simp

/-- **The Fourier-even signed prolate leakage ladder is a ladder envelope.** -/
theorem ladderEnvelope_evenProlateSignedLeakage :
    LadderEnvelope (fun a j => evenProlateSignedLeakage a (2 * j)) where
  nonneg := fun a j => evenProlateSignedLeakage_nonneg a (2 * j)
  mono := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha i j hij
    exact evenProlateSignedLeakage_monotone a ha (by omega)
  lt_succ := by
    intro j
    have hratio := tendsto_evenProlateSignedLeakage_step_ratio j
    have hhalf : ∀ᶠ a : ℝ in atTop,
        evenProlateSignedLeakage a (2 * j) / evenProlateSignedLeakage a (2 * j + 2) < 1 / 2 :=
      hratio.eventually (eventually_lt_nhds (by norm_num))
    have hidx : 2 * (j + 1) = 2 * j + 2 := by ring
    filter_upwards [hhalf,
      eventually_evenProlateSignedLeakage_pos (2 * j + 2) (by omega)] with a hlt hpos
    rw [hidx]
    rw [div_lt_iff₀ hpos] at hlt
    linarith
  ratio_tendsto_zero := by
    intro j
    have h := tendsto_evenProlateSignedLeakage_step_ratio j
    have hidx : 2 * (j + 1) = 2 * j + 2 := by ring
    rw [hidx]
    exact h
  tail_tendsto_zero := by
    intro j
    have h := tendsto_evenProlateSignedLeakage_step_tail j
    have hidx1 : 2 * (j + 1) = 2 * j + 2 := by ring
    have hidx2 : 2 * (j + 2) = 2 * j + 4 := by ring
    rw [hidx1, hidx2]
    exact h

/-- **The constrained-prolate clock law, unconditionally.**  For the true signed prolate leakage
ladder and the true Fourier-even constraint coordinates, an eventual genuine constrained eigenpair
annihilates its full constraint exactly and makes every preceding raw contrast asymptotically
invisible — with no hypothesis whatsoever. -/
theorem constrainedProlateEven_exactEigenpair_and_allRawDefects (k : ℕ) :
    let D : ℝ → ℕ → ℝ := fun a j => evenProlateSignedLeakage a (2 * j)
    let ℓ : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam (2 * j)‖
    (∀ᶠ lam in atTop,
      depthSecularRoot (D lam) (ℓ lam) k ∈ Ioo (D lam k) (D lam (k + 1)) ∧
      depthSecular (D lam) (ℓ lam) k (depthSecularRoot (D lam) (ℓ lam) k) = 0 ∧
      (∑' j : ℕ,
        ℓ lam j * secularVector (D lam) (ℓ lam)
          (depthSecularRoot (D lam) (ℓ lam) k) j) = 0 ∧
      secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) ≠ 0) ∧
    ∀ m, m ≤ k →
      Tendsto (fun lam =>
        (secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) m * ℓ lam 0
          - secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0 * ℓ lam m)
          / (secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0
              * ℓ lam 0)) atTop (nhds 0) :=
  ladderEnvelope_evenProlateSignedLeakage.constrainedProlateEven_exactEigenpair_and_allRawDefects k

/-- **Equation `(8)` of the constrained-prolate ladder, unconditionally.**  The depth-`k`
constrained eigenvalue, normalized by the next Fourier-even leakage, converges to the exact
Hermite contrast `theta_k` — for the true signed prolate spectrum and the true constraint
coordinates, with no hypothesis. -/
theorem constrainedProlateEven_depth_ratio_tendsto (k : ℕ) :
    Tendsto (fun lam : ℝ =>
      depthSecularRoot (fun j => evenProlateSignedLeakage lam (2 * j))
          (fun j => ‖evenProlateConstraintCoord lam (2 * j)‖) k
        / evenProlateSignedLeakage lam (2 * (k + 1)))
      atTop (nhds (constrainedProlateHermiteTheta k)) := by
  refine ladderEnvelope_evenProlateSignedLeakage.ccm_depth_ratio_tendsto k ?_ ?_ ?_
  · refine Eventually.of_forall fun lam => ?_
    exact (summable_evenProlateConstraintCoord_sq lam).comp_injective injective_two_mul
  · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with lam hlam
    exact tsum_evenProlateConstraintCoord_comp_sq_le hlam injective_two_mul
  · intro j _
    exact tendsto_norm_evenProlateConstraintCoord_atTop j

/-- The Bessel-side inputs of the constrained transfer, at the true Fourier-even coordinates. -/
theorem evenProlateLadder_sum :
    ∀ᶠ lam : ℝ in atTop,
      Summable fun j : ℕ => ‖evenProlateConstraintCoord lam (2 * j)‖ ^ 2 :=
  Eventually.of_forall fun lam =>
    (summable_evenProlateConstraintCoord_sq lam).comp_injective injective_two_mul

theorem evenProlateLadder_bessel :
    ∀ᶠ lam : ℝ in atTop,
      (∑' j : ℕ, ‖evenProlateConstraintCoord lam (2 * j)‖ ^ 2) ≤ 2 * lam := by
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with lam hlam
  exact tsum_evenProlateConstraintCoord_comp_sq_le hlam injective_two_mul

/-- **Equation `(9)`, unconditionally.**  Two consecutive constrained eigenvalues, corrected by the
ratio of their dominant leakages, separate by exactly the Hermite quotient
`theta_{k+1}/theta_k = Q_{k+1}²/(Q_k Q_{k+2})`. -/
theorem constrainedProlateEven_adjacent_ratio_tendsto (k : ℕ) :
    let D : ℝ → ℕ → ℝ := fun a j => evenProlateSignedLeakage a (2 * j)
    let ℓ : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam (2 * j)‖
    Tendsto (fun lam : ℝ =>
      depthSecularRoot (D lam) (ℓ lam) (k + 1) / depthSecularRoot (D lam) (ℓ lam) k
        * (evenProlateSignedLeakage lam (2 * (k + 1))
            / evenProlateSignedLeakage lam (2 * (k + 2))))
      atTop (nhds (constrainedProlateHermiteTheta (k + 1)
        / constrainedProlateHermiteTheta k)) := by
  intro D ℓ
  have h1 := constrainedProlateEven_depth_ratio_tendsto (k + 1)
  have h2 := constrainedProlateEven_depth_ratio_tendsto k
  have hθ : constrainedProlateHermiteTheta k ≠ 0 :=
    (constrainedProlateHermiteTheta_mem_Ioo k).1.ne'
  have h := h1.div h2 hθ
  have h' : Tendsto (fun lam : ℝ =>
      depthSecularRoot (D lam) (ℓ lam) (k + 1) / evenProlateSignedLeakage lam (2 * (k + 2))
        / (depthSecularRoot (D lam) (ℓ lam) k / evenProlateSignedLeakage lam (2 * (k + 1))))
      atTop (nhds (constrainedProlateHermiteTheta (k + 1)
        / constrainedProlateHermiteTheta k)) := by
    have hh : Tendsto ((fun lam : ℝ =>
        depthSecularRoot (D lam) (ℓ lam) (k + 1)
          / evenProlateSignedLeakage lam (2 * (k + 1 + 1))) /
      fun lam : ℝ =>
        depthSecularRoot (D lam) (ℓ lam) k
          / evenProlateSignedLeakage lam (2 * (k + 1)))
      atTop (nhds (constrainedProlateHermiteTheta (k + 1)
        / constrainedProlateHermiteTheta k)) := h
    exact Tendsto.congr (fun _ => rfl) hh
  refine h'.congr' ?_
  have hroot :=
    (ladderEnvelope_evenProlateSignedLeakage.ccm_depth_ratio_and_exactEigenpair_eventually
      k evenProlateLadder_sum evenProlateLadder_bessel
      (fun j _ => tendsto_norm_evenProlateConstraintCoord_atTop j)).2
  filter_upwards [hroot,
    eventually_evenProlateSignedLeakage_pos (2 * (k + 1)) (by omega),
    eventually_evenProlateSignedLeakage_pos (2 * (k + 2)) (by omega)]
    with lam hbr hd1 hd2
  have hrootpos : 0 < depthSecularRoot (D lam) (ℓ lam) k :=
    lt_of_le_of_lt (evenProlateSignedLeakage_nonneg lam (2 * k)) hbr.1.1
  have hrootne : depthSecularRoot (D lam) (ℓ lam) k ≠ 0 := hrootpos.ne'
  have hd1ne : evenProlateSignedLeakage lam (2 * (k + 1)) ≠ 0 := hd1.ne'
  have hd2ne : evenProlateSignedLeakage lam (2 * (k + 2)) ≠ 0 := hd2.ne'
  field_simp

/-- **Equations `(10)`--`(11)`, unconditionally.**  The exact depth-`k` constrained eigenvector,
oriented by its zeroth coordinate and normalized, converges in `ell²` to the canonical Hermite
contrast unit. -/
theorem constrainedProlateEven_normalized_eigenvector_tendsto (k : ℕ) :
    let D : ℝ → ℕ → ℝ := fun a j => evenProlateSignedLeakage a (2 * j)
    let ℓ : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam (2 * j)‖
    Tendsto (fun lam : ℝ =>
      let V := (secularVector (D lam) (ℓ lam)
          (depthSecularRoot (D lam) (ℓ lam) k) 0)⁻¹ •
        secularLp (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k)
      (‖V‖)⁻¹ • V) atTop (nhds (-hermiteContrastUnit k)) :=
  ladderEnvelope_evenProlateSignedLeakage.ccm_depth_normalized_rescaled_secularLp_tendsto_hermiteContrastUnit
    k evenProlateLadder_sum evenProlateLadder_bessel
    (fun j _ => tendsto_norm_evenProlateConstraintCoord_atTop j)

/-! ## The first two constants -/

/-- **`mu_0/d_1 → 8/11`, unconditionally.** -/
theorem constrainedProlateEven_ground_ratio_tendsto :
    let D : ℝ → ℕ → ℝ := fun a j => evenProlateSignedLeakage a (2 * j)
    let ℓ : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam (2 * j)‖
    Tendsto (fun lam : ℝ =>
      depthSecularRoot (D lam) (ℓ lam) 0 / evenProlateSignedLeakage lam 2)
      atTop (nhds (8 / 11)) := by
  have h := constrainedProlateEven_depth_ratio_tendsto 0
  rw [constrainedProlateHermiteTheta_zero] at h
  simpa using h

/-- **`mu_1/d_2 → 176/211`, unconditionally.** -/
theorem constrainedProlateEven_first_ratio_tendsto :
    let D : ℝ → ℕ → ℝ := fun a j => evenProlateSignedLeakage a (2 * j)
    let ℓ : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam (2 * j)‖
    Tendsto (fun lam : ℝ =>
      depthSecularRoot (D lam) (ℓ lam) 1 / evenProlateSignedLeakage lam 4)
      atTop (nhds (176 / 211)) := by
  have h := constrainedProlateEven_depth_ratio_tendsto 1
  rw [constrainedProlateHermiteTheta_one] at h
  simpa using h

/-- **The first adjacent coefficient `242/211` of `(13)`, unconditionally.** -/
theorem constrainedProlateEven_adjacent_ground_ratio_tendsto :
    let D : ℝ → ℕ → ℝ := fun a j => evenProlateSignedLeakage a (2 * j)
    let ℓ : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam (2 * j)‖
    Tendsto (fun lam : ℝ =>
      depthSecularRoot (D lam) (ℓ lam) 1 / depthSecularRoot (D lam) (ℓ lam) 0
        * (evenProlateSignedLeakage lam 2 / evenProlateSignedLeakage lam 4))
      atTop (nhds (242 / 211)) := by
  have h := constrainedProlateEven_adjacent_ratio_tendsto 0
  rw [constrainedProlateHermiteTheta_zero, constrainedProlateHermiteTheta_one] at h
  norm_num at h
  simpa using h

end RHTower

end
