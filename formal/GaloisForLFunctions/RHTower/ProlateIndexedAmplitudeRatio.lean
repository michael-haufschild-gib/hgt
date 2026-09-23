import GaloisForLFunctions.RHTower.ProlatePairAnchor
import GaloisForLFunctions.RHTower.ProlateBarrierRatioSharp
import GaloisForLFunctions.RHTower.ProlateLeakageLadderRatio

/-!
# The amplitude ratio of two rungs at the common anchor

Every hypothesis of `prolateBand_sq_ratio_le` holds eventually at the canonical radial family, with
the pair anchor as the common band point and the leakage collar as the collar.  The `4 ≤ c s`
hypothesis is needed only by the *upper* half, hence only at the larger index, where `c s_n → 4n+1`
exceeds four as soon as `n ≥ 1`; the lower half has no such hypothesis, so the ground index is
unobstructed.

The result is a bandwidth-free comparison of the two squared amplitudes at a single point:

```text
R_n(y₀)²  ≤  324 sqrt 2 π³ · C_n · exp( 2c (Ξ_{s_n}(y₀) - Ξ_{s_m}(y₀)) + Λ_n
                                        - 12 (log(1-α) - log(1-y₀)) ) · R_m(y₀)² .
```
-/

noncomputable section

open Set Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

/-- The common anchor of two rungs, in the band variable. -/
def pairAnchorPoint (m n : ℕ) (a : ℝ) : ℝ :=
  prolatePairAnchor m n / Real.sqrt (signedModeRadialBandwidth a)

theorem pairAnchorPoint_sq {m n : ℕ} {a : ℝ} (hc : 0 < signedModeRadialBandwidth a) :
    pairAnchorPoint m n a ^ (2 : ℕ) = prolatePairAnchor m n ^ (2 : ℕ) / signedModeRadialBandwidth a := by
  rw [pairAnchorPoint, div_pow, Real.sq_sqrt hc.le]

theorem pairAnchorPoint_pos {m n : ℕ} {a : ℝ} (hc : 0 < signedModeRadialBandwidth a) :
    0 < pairAnchorPoint m n a := by
  rw [pairAnchorPoint]
  exact div_pos (prolatePairAnchor_pos m n) (Real.sqrt_pos.2 hc)

/-- The collar phase constant: a positive lower bound for the phase at the collar, uniform over the
admissible separations. -/
def collarPhaseFloor : ℝ :=
  Real.sqrt (prolateLeakageCollar ^ (2 : ℕ) - 1 / 8) * Real.arccos prolateLeakageCollar

theorem collarPhaseFloor_pos : 0 < collarPhaseFloor := by
  have hα1 : prolateLeakageCollar < 1 := prolateLeakageCollar_lt_one
  have hαh : (1 : ℝ) / 2 < prolateLeakageCollar := prolateLeakageCollar_gt_half
  have h1 : (0 : ℝ) < prolateLeakageCollar ^ (2 : ℕ) - 1 / 8 := by
    rw [prolateLeakageCollar]; norm_num
  have h2 : 0 < Real.arccos prolateLeakageCollar := by
    rw [Real.arccos_pos]
    exact hα1
  rw [collarPhaseFloor]
  exact mul_pos (Real.sqrt_pos.2 h1) h2

theorem collarPhaseFloor_le {s : ℝ} (hs : s ≤ 1 / 8) :
    collarPhaseFloor ≤ bandEndpointPhase s prolateLeakageCollar := by
  have hα1 : prolateLeakageCollar < 1 := prolateLeakageCollar_lt_one
  have hαh : (1 : ℝ) / 2 < prolateLeakageCollar := prolateLeakageCollar_gt_half
  have hα0 : (0 : ℝ) ≤ prolateLeakageCollar := by linarith
  have hlow := sqrt_mul_arccos_le_bandEndpointPhase (s := s) (y := prolateLeakageCollar)
    hα0 hα1.le
  refine le_trans ?_ hlow
  rw [collarPhaseFloor]
  refine mul_le_mul_of_nonneg_right ?_ (Real.arccos_nonneg _)
  exact Real.sqrt_le_sqrt (by linarith)

/-- **The two rungs are compared at the common anchor, eventually.** -/
theorem eventually_prolateBand_sq_ratio_le (m n : ℕ) (hn : 1 ≤ n) :
    ∀ᶠ a : ℝ in atTop,
      (signedModeRadialData a n).R (pairAnchorPoint m n a) ^ (2 : ℕ)
        ≤ 324 * Real.sqrt 2 * Real.pi ^ (3 : ℕ)
            * (1 + (1 - prolateLeakageCollar ^ (2 : ℕ))
                * (prolateRadialBarrier (signedModeRadialBandwidth a)
                      (signedModeRadialData a n).s prolateLeakageCollar
                    + 6 / (1 - prolateLeakageCollar)) ^ (2 : ℕ)
                / (signedModeRadialBandwidth a ^ (2 : ℕ)
                    * (prolateLeakageCollar ^ (2 : ℕ) - (signedModeRadialData a n).s)))
            * Real.exp (2 * signedModeRadialBandwidth a
                  * (bandEndpointPhase (signedModeRadialData a n).s (pairAnchorPoint m n a)
                    - bandEndpointPhase (signedModeRadialData a m).s (pairAnchorPoint m n a))
                + prolateScaleLog (signedModeRadialData a n).s (pairAnchorPoint m n a)
                    prolateLeakageCollar
                - 12 * (Real.log (1 - prolateLeakageCollar)
                    - Real.log (1 - pairAnchorPoint m n a)))
            * (signedModeRadialData a m).R (pairAnchorPoint m n a) ^ (2 : ℕ) := by
  set x₀ : ℝ := prolatePairAnchor m n with hx₀def
  have hx₀ : 0 < x₀ := prolatePairAnchor_pos m n
  have hxn : 4 * (4 * (n : ℝ) + 1) < x₀ ^ (2 : ℕ) := prolatePairAnchor_sq_gt m n n (Or.inr rfl)
  have hxm : 4 * (4 * (m : ℝ) + 1) < x₀ ^ (2 : ℕ) := prolatePairAnchor_sq_gt m n m (Or.inl rfl)
  have hα1 : prolateLeakageCollar < 1 := prolateLeakageCollar_lt_one
  have hαh : (1 : ℝ) / 2 < prolateLeakageCollar := prolateLeakageCollar_gt_half
  have hcollar : 600 * (1 - prolateLeakageCollar) ≤ 1 / 4 := prolateLeakageCollar_collar
  -- eventual data
  have hcTop := tendsto_signedModeRadialBandwidth_atTop
  have hc1 : ∀ᶠ a : ℝ in atTop, (1 : ℝ) ≤ signedModeRadialBandwidth a :=
    hcTop.eventually_ge_atTop 1
  have hclarge : ∀ᶠ a : ℝ in atTop,
      x₀ ^ (2 : ℕ) / prolateLeakageCollar ^ (2 : ℕ) ≤ signedModeRadialBandwidth a :=
    hcTop.eventually_ge_atTop _
  have hcfloor : ∀ᶠ a : ℝ in atTop, 1 / collarPhaseFloor ≤ signedModeRadialBandwidth a :=
    hcTop.eventually_ge_atTop _
  have hsn := tendsto_signedModeRadialBandwidth_mul_s_atTop n
  have hsm := tendsto_signedModeRadialBandwidth_mul_s_atTop m
  have hcsn : ∀ᶠ a : ℝ in atTop,
      4 < signedModeRadialBandwidth a * (signedModeRadialData a n).s := by
    refine hsn.eventually (eventually_gt_nhds ?_)
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hcsnhi : ∀ᶠ a : ℝ in atTop,
      signedModeRadialBandwidth a * (signedModeRadialData a n).s < x₀ ^ (2 : ℕ) := by
    refine hsn.eventually (eventually_lt_nhds ?_)
    linarith
  have hcsmhi : ∀ᶠ a : ℝ in atTop,
      signedModeRadialBandwidth a * (signedModeRadialData a m).s < x₀ ^ (2 : ℕ) := by
    refine hsm.eventually (eventually_lt_nhds ?_)
    linarith
  filter_upwards [eventually_gt_atTop (0 : ℝ), hc1, hclarge, hcfloor, hcsn, hcsnhi, hcsmhi,
    eventually_signedModeRadialData_s_pos n,
    eventually_signedModeRadialData_s_le n (by norm_num : (0 : ℝ) < 1 / 8),
    eventually_signedModeRadialData_s_nonneg m,
    eventually_signedModeRadialData_s_le m (by norm_num : (0 : ℝ) < 1 / 8)]
    with a hapos hc1a hclargea hcfloora hcsna hcsnhia hcsmhia hsn0 hsn8 hsm0 hsm8
  set c : ℝ := signedModeRadialBandwidth a with hcdef
  have hc0 : 0 < c := by linarith
  set y₀ : ℝ := pairAnchorPoint m n a with hy₀def
  have hy₀0 : 0 < y₀ := pairAnchorPoint_pos hc0
  have hy₀sq : y₀ ^ (2 : ℕ) = x₀ ^ (2 : ℕ) / c := pairAnchorPoint_sq hc0
  have hy₀α : y₀ ≤ prolateLeakageCollar := by
    have hsq : y₀ ^ (2 : ℕ) ≤ prolateLeakageCollar ^ (2 : ℕ) := by
      rw [hy₀sq, div_le_iff₀ hc0]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < prolateLeakageCollar ^ (2 : ℕ))] at hclargea
      linarith [hclargea]
    nlinarith [hy₀0, hαh]
  have hy₀1 : y₀ < 1 := lt_of_le_of_lt hy₀α hα1
  have hsy0n : (signedModeRadialData a n).s < y₀ ^ (2 : ℕ) := by
    rw [hy₀sq, lt_div_iff₀ hc0]
    linarith [hcsnhia]
  have hsy0m : (signedModeRadialData a m).s < y₀ ^ (2 : ℕ) := by
    rw [hy₀sq, lt_div_iff₀ hc0]
    linarith [hcsmhia]
  -- the exactness bundles
  have hExn := signedModeRadialData_isExact_of_pos hapos n
  have hExm := signedModeRadialData_isExact_of_pos hapos m
  have hsmn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (signedModeRadialData a n).R :=
    hExn.2.2.2.2.2.1
  have hsmm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (signedModeRadialData a m).R :=
    hExm.2.2.2.2.2.1
  have hRn1 : (signedModeRadialData a n).R 1 = 1 := hExn.2.2.2.2.2.2.2.1
  have hRm1 : (signedModeRadialData a m).R 1 = 1 := hExm.2.2.2.2.2.2.2.1
  have heign : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c (signedModeRadialData a n).R y
        = -((signedModeRadialData a n).s * c ^ (2 : ℕ)) * (signedModeRadialData a n).R y := by
    have hchi : (signedModeRadialData a n).chi = -((signedModeRadialData a n).s * c ^ (2 : ℕ)) := by
      have hs := hExn.2.2.2.2.2.2.2.2.2.2.1
      rw [← hcdef] at hs
      have hcne : c ≠ 0 := hc0.ne'
      rw [hs, radialSeparationRatio]
      field_simp
    intro y _
    rw [hExn.2.2.2.2.2.2.2.2.2.1 y, hchi]
  have heigm : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c (signedModeRadialData a m).R y
        = -((signedModeRadialData a m).s * c ^ (2 : ℕ)) * (signedModeRadialData a m).R y := by
    have hchi : (signedModeRadialData a m).chi = -((signedModeRadialData a m).s * c ^ (2 : ℕ)) := by
      have hs := hExm.2.2.2.2.2.2.2.2.2.2.1
      rw [← hcdef] at hs
      have hcne : c ≠ 0 := hc0.ne'
      rw [hs, radialSeparationRatio]
      field_simp
    intro y _
    rw [hExm.2.2.2.2.2.2.2.2.2.1 y, hchi]
  -- positivity on the band
  have hsqrtn : Real.sqrt (signedModeRadialData a n).s ≤ y₀ := by
    have := Real.sqrt_le_sqrt hsy0n.le
    rwa [Real.sqrt_sq hy₀0.le] at this
  have hsqrtm : Real.sqrt (signedModeRadialData a m).s ≤ y₀ := by
    have := Real.sqrt_le_sqrt hsy0m.le
    rwa [Real.sqrt_sq hy₀0.le] at this
  have hposn : ∀ t ∈ Icc y₀ 1, 0 < (signedModeRadialData a n).R t := by
    intro t ht
    exact prolate_pos_on_right_of_radial_turning hsn0.le hsmn heign hRn1 t
      ⟨le_trans hsqrtn ht.1, ht.2⟩
  have hposm : ∀ t ∈ Icc y₀ 1, 0 < (signedModeRadialData a m).R t := by
    intro t ht
    exact prolate_pos_on_right_of_radial_turning hsm0 hsmm heigm hRm1 t
      ⟨le_trans hsqrtm ht.1, ht.2⟩
  -- derivatives
  have hdiffn : Differentiable ℝ (signedModeRadialData a n).R :=
    (contDiff_infty_iff_deriv.mp hsmn).1
  have hdiff2n : Differentiable ℝ (deriv (signedModeRadialData a n).R) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hsmn).2).1
  have hΦnd : ∀ t : ℝ, HasDerivAt (signedModeRadialData a n).R
      (deriv (signedModeRadialData a n).R t) t := fun t => (hdiffn t).hasDerivAt
  have hDRn : ∀ t : ℝ, HasDerivAt (deriv (signedModeRadialData a n).R)
      (deriv (deriv (signedModeRadialData a n).R) t) t := fun t => (hdiff2n t).hasDerivAt
  have hoden : ∀ x : ℝ, (x ^ (2 : ℕ) - 1) * deriv (deriv (signedModeRadialData a n).R) x
      + 2 * x * deriv (signedModeRadialData a n).R x
      - ((signedModeRadialData a n).s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (2 : ℕ))
        * (signedModeRadialData a n).R x = 0 := hExn.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hfluxn : ∀ t ∈ Icc y₀ prolateLeakageCollar,
      HasDerivAt (fun u => (1 - u ^ (2 : ℕ)) * deriv (signedModeRadialData a n).R u)
        (-(c ^ (2 : ℕ) * ((signedModeRadialData a n).s - t ^ (2 : ℕ))
          * (signedModeRadialData a n).R t)) t := by
    intro t _
    have h1 : HasDerivAt (fun u : ℝ => 1 - u ^ (2 : ℕ)) (-(2 * t)) t := by
      have h0 := (hasDerivAt_pow 2 t).const_sub 1
      refine h0.congr_deriv ?_
      push_cast
      ring
    have h := h1.mul (hDRn t)
    refine h.congr_deriv ?_
    have ho := hoden t
    linear_combination -ho
  -- the collar phase
  have hzn : 0 < c * bandEndpointPhase (signedModeRadialData a n).s prolateLeakageCollar := by
    have hpos := collarPhaseFloor_le (s := (signedModeRadialData a n).s) hsn8
    have := collarPhaseFloor_pos
    nlinarith [hpos, hc0]
  have hzm : 1 ≤ c * bandEndpointPhase (signedModeRadialData a m).s prolateLeakageCollar := by
    have hpos := collarPhaseFloor_le (s := (signedModeRadialData a m).s) hsm8
    have hκ := collarPhaseFloor_pos
    have hone : 1 ≤ c * collarPhaseFloor := by
      rw [div_le_iff₀ hκ] at hcfloora
      linarith [hcfloora]
    nlinarith [hone, hpos, hc0]
  exact prolateBand_sq_ratio_le hc0 hsn0 hsn8 (le_of_lt hcsna) hsm0 hsm8 hsmn heign hRn1
    hsmm heigm hRm1 hsy0n hsy0m hy₀0 hy₀α hαh hα1 hcollar hzn hzm hposn hposm hΦnd hfluxn

end RHTower

end
