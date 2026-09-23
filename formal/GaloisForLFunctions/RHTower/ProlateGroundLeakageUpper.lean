import GaloisForLFunctions.RHTower.ProlateGroundBarrier
import GaloisForLFunctions.RHTower.ProlateIndexedLeakageTwoSided

/-!
# The explicit leakage upper bound at every index, ground included

The two-sided estimate excludes the ground index only through the hypothesis `4 ≤ c·s`, which the
lifted Riccati barrier removes.  Redoing the upper half with that barrier gives the same explicit
bound with the transport constant `c·b + 12` replaced by `c·b + 12 + 2 sqrt c`.

At the cut `b = 2 sqrt s + 1/c` the extra transport loss is
`exp(4 sqrt c · (1/c) / (1 - b²)) = exp(4 / (sqrt c (1 - b²)))`, which is at most `e` once
`c ≥ 64` and `s ≤ 1/64`.  So the ground leakage obeys the excited-index bound up to one factor `e`,
and the whole leakage ladder — ground index included — is bounded above by a power of the bandwidth
times `e^{-2c}`.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

end RHTower

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- **The explicit leakage upper bound at every separation.**  Only the lifted barrier is used, so
no lower bound on `c·s` appears. -/
theorem prolate_leakage_le_shifted {c s α b : ℝ} {Φ R DR DDR : ℝ → ℝ} {value leakage : ℝ}
    (hc : 8 ≤ c) (hs0 : 0 < s) (hs8 : s ≤ 1 / 8)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1)
    (h2sα : 2 * Real.sqrt s ≤ α)
    (hα : 1 / 2 < α) (hα1 : α < 1) (hcollar : 600 * (1 - α) ≤ 1 / 4)
    (hz : 1 ≤ c * bandEndpointPhase s α)
    (hposΦ : ∀ t ∈ Icc (2 * Real.sqrt s) 1, 0 < Φ t)
    (hb : 2 * Real.sqrt s < b) (hb1 : b < 1)
    (hR1 : R 1 = 1) (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0)
    (hvalue : value ^ (2 : ℕ) ≤ 1) (hv : value ≠ 0) (hleak : 0 ≤ leakage)
    (hmass : (∫ x in Ioi (1 : ℝ), R x ^ (2 : ℕ))
      = (∫ y in (-1 : ℝ)..1, Φ y ^ (2 : ℕ)) * leakage / value ^ (2 : ℕ)) :
    leakage ≤ radialProlateExteriorMassConstant / c
      * ((6 * Real.pi * Real.sqrt (c * bandEndpointPhase s α)) ^ (2 : ℕ)
          * Real.exp (2 * ((c * b + 12 + 2 * Real.sqrt c)
              * (b - 2 * Real.sqrt s) / (1 - b ^ (2 : ℕ))))
          / (b - 2 * Real.sqrt s))
      * Real.exp (-(2 * (c * bandEndpointPhase s (2 * Real.sqrt s)
          + 6 * (Real.log (1 - α) - Real.log (1 - 2 * Real.sqrt s))))) := by
  have hcpos : (0 : ℝ) < c := by linarith
  have hsqrt : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hy00 : (0 : ℝ) < 2 * Real.sqrt s := by linarith
  have hsq : (2 * Real.sqrt s) ^ (2 : ℕ) = 4 * s := by
    rw [mul_pow, Real.sq_sqrt hs0.le]
    ring
  have hsy0 : s < (2 * Real.sqrt s) ^ (2 : ℕ) := by rw [hsq]; linarith
  have hin := prolate_aperture_mass_lower_shifted (c := c) (s := s) (y₀ := 2 * Real.sqrt s)
    (b := b) hcpos hs0.le (by linarith) hsm heig hΦ1 hy00 hsy0 hb.le hb1 hposΦ
  have hw : (0 : ℝ) < b - 2 * Real.sqrt s := by linarith
  exact prolate_leakage_le_exp_action (c := c) (s := s) (α := α) (y₀ := 2 * Real.sqrt s)
    (w := b - 2 * Real.sqrt s)
    (E := (c * b + 12 + 2 * Real.sqrt c) * (b - 2 * Real.sqrt s) / (1 - b ^ (2 : ℕ)))
    (inside := ∫ y in (-1 : ℝ)..1, Φ y ^ (2 : ℕ)) (value := value) (leakage := leakage)
    hs0.le hs8 (by linarith) hα hα1 hcollar hsm heig hΦ1 hy00.le h2sα hsy0 hposΦ hz
    hR1 hR hDR hode hw hin hvalue hv hleak hmass

end GaloisForLFunctions.RHTower

namespace RHTower

open GaloisForLFunctions.RHTower

/-- The explicit upper leakage bound of the lifted barrier, at the fixed collar and cut. -/
def prolateLeakageUpperShift (c s : ℝ) : ℝ :=
  radialProlateExteriorMassConstant / c
    * ((6 * Real.pi * Real.sqrt (c * bandEndpointPhase s prolateLeakageCollar)) ^ (2 : ℕ)
        * Real.exp (2 * ((c * prolateLeakageCut c s + 12 + 2 * Real.sqrt c)
            * (prolateLeakageCut c s - 2 * Real.sqrt s) / (1 - prolateLeakageCut c s ^ (2 : ℕ))))
        / (prolateLeakageCut c s - 2 * Real.sqrt s))
    * Real.exp (-(2 * (c * bandEndpointPhase s (2 * Real.sqrt s)
        + 6 * (Real.log (1 - prolateLeakageCollar) - Real.log (1 - 2 * Real.sqrt s)))))

/-- **The lifted bound costs at most one factor `e`.**  The extra transport loss over the window of
width `1/c` is `exp(4/(sqrt c (1 - b²)))`. -/
theorem prolateLeakageUpperShift_le {c s : ℝ} (hc : 64 ≤ c) (hs0 : 0 < s) (hs : s ≤ 1 / 64) :
    prolateLeakageUpperShift c s ≤ Real.exp 1 * prolateLeakageUpper c s := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hsqs0 : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hsqs : Real.sqrt s ≤ 1 / 8 := by
    have h := Real.sqrt_le_sqrt hs
    have h8 : Real.sqrt ((1 : ℝ) / 64) = 1 / 8 := by
      rw [show (1 : ℝ) / 64 = (1 / 8) ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [h8] at h
  have hcut : prolateLeakageCut c s = 2 * Real.sqrt s + 1 / c := rfl
  have hcinv : 1 / c ≤ 1 / 64 := by
    rw [div_le_div_iff₀ hc0 (by norm_num : (0 : ℝ) < 64)]
    linarith
  have hcinv0 : (0 : ℝ) < 1 / c := by positivity
  have hcutlt : prolateLeakageCut c s ≤ 1 / 2 := by
    rw [hcut]; linarith
  have hcut0 : (0 : ℝ) < prolateLeakageCut c s := by
    rw [hcut]; linarith
  have hQ : (3 : ℝ) / 4 ≤ 1 - prolateLeakageCut c s ^ (2 : ℕ) := by nlinarith
  have hQ0 : (0 : ℝ) < 1 - prolateLeakageCut c s ^ (2 : ℕ) := by linarith
  have hw : prolateLeakageCut c s - 2 * Real.sqrt s = 1 / c := by rw [hcut]; ring
  have hw0 : (0 : ℝ) < prolateLeakageCut c s - 2 * Real.sqrt s := by rw [hw]; exact hcinv0
  have hsqc : (8 : ℝ) ≤ Real.sqrt c := by
    have h := Real.sqrt_le_sqrt hc
    have h8 : Real.sqrt (64 : ℝ) = 8 := by
      rw [show (64 : ℝ) = 8 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [h8] at h
  have hsqc0 : (0 : ℝ) < Real.sqrt c := by linarith
  have hsqcsq : Real.sqrt c ^ (2 : ℕ) = c := Real.sq_sqrt hc0.le
  -- the exponent splits
  have hsplit : 2 * ((c * prolateLeakageCut c s + 12 + 2 * Real.sqrt c)
        * (prolateLeakageCut c s - 2 * Real.sqrt s) / (1 - prolateLeakageCut c s ^ (2 : ℕ)))
      = 2 * ((c * prolateLeakageCut c s + 12)
          * (prolateLeakageCut c s - 2 * Real.sqrt s) / (1 - prolateLeakageCut c s ^ (2 : ℕ)))
        + 2 * (2 * Real.sqrt c * (prolateLeakageCut c s - 2 * Real.sqrt s)
            / (1 - prolateLeakageCut c s ^ (2 : ℕ))) := by
    field_simp
  have hloss : 2 * (2 * Real.sqrt c * (prolateLeakageCut c s - 2 * Real.sqrt s)
      / (1 - prolateLeakageCut c s ^ (2 : ℕ))) ≤ 1 := by
    rw [hw]
    have hval : 2 * (2 * Real.sqrt c * (1 / c) / (1 - prolateLeakageCut c s ^ (2 : ℕ)))
        = 4 * Real.sqrt c / c / (1 - prolateLeakageCut c s ^ (2 : ℕ)) := by
      field_simp
      ring
    rw [hval, div_le_one hQ0]
    have hkey : 4 * Real.sqrt c / c ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hc0 (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hsqcsq, hsqc, hsqc0]
    linarith
  have hfactor : prolateLeakageUpperShift c s
      = Real.exp (2 * (2 * Real.sqrt c * (prolateLeakageCut c s - 2 * Real.sqrt s)
            / (1 - prolateLeakageCut c s ^ (2 : ℕ)))) * prolateLeakageUpper c s := by
    rw [prolateLeakageUpperShift, prolateLeakageUpper, hsplit, Real.exp_add]
    ring
  have hUnn : 0 ≤ prolateLeakageUpper c s := by
    rw [prolateLeakageUpper]
    have h1 : (0 : ℝ) ≤ radialProlateExteriorMassConstant :=
      radialProlateExteriorMassConstant_nonneg
    have h2 : (0 : ℝ) < prolateLeakageCut c s - 2 * Real.sqrt s := hw0
    positivity
  rw [hfactor]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hloss) hUnn

/-- **The upper leakage estimate at the canonical indexed family, at every index.**  The ground
index is included: the lifted barrier needs no lower bound on `c·s`. -/
theorem eventually_signedLeakage_upper (n : ℕ) :
    ∀ᶠ a : ℝ in atTop,
      evenProlateSignedLeakage a n / 2
        ≤ prolateLeakageUpperShift (signedModeRadialBandwidth a) (signedModeRadialData a n).s := by
  set α : ℝ := prolateLeakageCollar with hα
  have hα1 : α < 1 := prolateLeakageCollar_lt_one
  have hαhalf : (1 : ℝ) / 2 < α := prolateLeakageCollar_gt_half
  have hαcollar : 600 * (1 - α) ≤ 1 / 4 := prolateLeakageCollar_collar
  have hα0 : 0 < α := prolateLeakageCollar_pos
  have hαsq : (1 : ℝ) / 64 < α ^ (2 : ℕ) := by
    rw [hα, prolateLeakageCollar]
    norm_num
  set κ : ℝ := Real.sqrt (α ^ (2 : ℕ) - 1 / 64) * Real.arccos α with hκ
  have hκpos : 0 < κ := by
    refine mul_pos (Real.sqrt_pos.2 (by linarith)) ?_
    exact Real.arccos_pos.2 hα1
  have hlimit : Tendsto (fun a : ℝ =>
      signedModeRadialBandwidth a * (signedModeRadialData a n).s) atTop (𝓝 (4 * (n : ℝ) + 1)) :=
    tendsto_signedModeRadialBandwidth_mul_s_atTop n
  have hn1 : (0 : ℝ) < 4 * (n : ℝ) + 1 := by positivity
  have hcs_lo : ∀ᶠ a : ℝ in atTop, 0 < signedModeRadialBandwidth a * (signedModeRadialData a n).s :=
    hlimit.eventually (eventually_gt_nhds hn1)
  have hcs_hi : ∀ᶠ a : ℝ in atTop,
      signedModeRadialBandwidth a * (signedModeRadialData a n).s < 4 * (n : ℝ) + 2 :=
    hlimit.eventually (eventually_lt_nhds (by linarith))
  set C₀ : ℝ := max 8 (max (64 * (4 * (n : ℝ) + 2)) (1 / κ)) with hC₀
  have hcbig : ∀ᶠ a : ℝ in atTop, C₀ ≤ signedModeRadialBandwidth a :=
    tendsto_signedModeRadialBandwidth_atTop.eventually_ge_atTop C₀
  have hσlim := evenProlateSignedValue_sq_tendsto_one n
  have hσ : ∀ᶠ a : ℝ in atTop, 1 / 2 < evenProlateSignedValue a n ^ (2 : ℕ) :=
    hσlim.eventually (eventually_gt_nhds (by norm_num))
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_signedModeRadialData_isExact n,
    eventually_evenProlateSignedValue_ne_zero n, hcs_lo, hcs_hi, hcbig, hσ]
    with a hapos hex hvne hlo hhi hcb hsig
  set c : ℝ := signedModeRadialBandwidth a with hcdef
  set s : ℝ := (signedModeRadialData a n).s with hsdef
  set R : ℝ → ℝ := (signedModeRadialData a n).R with hRdef
  have hc0 : 0 < c := by
    rw [hcdef, signedModeRadialBandwidth]
    positivity
  have hc8 : (8 : ℝ) ≤ c := le_trans (le_max_left _ _) hcb
  have hc64 : 64 * (4 * (n : ℝ) + 2) ≤ c :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hcb
  have hcκ : 1 / κ ≤ c := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hcb
  have hs0 : 0 < s := by
    by_contra hcon
    have hcon' : s ≤ 0 := not_lt.1 hcon
    nlinarith [hlo, hc0]
  have hs64 : s ≤ 1 / 64 := by
    have hn2 : (0 : ℝ) < 4 * (n : ℝ) + 2 := by positivity
    nlinarith [hhi, hc64, hs0]
  have hsqs : Real.sqrt s ≤ 1 / 8 := by
    have h := Real.sqrt_le_sqrt hs64
    have h8 : Real.sqrt ((1 : ℝ) / 64) = 1 / 8 := by
      rw [show (1 : ℝ) / 64 = (1 / 8) ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [h8] at h
  have hsqs0 : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have h2sα : 2 * Real.sqrt s ≤ α := by
    have h : 2 * Real.sqrt s ≤ 1 / 4 := by linarith
    rw [hα, prolateLeakageCollar]
    linarith
  have hs8 : s ≤ 1 / 8 := by linarith
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R := hex.2.2.2.2.2.1
  have hR1 : R 1 = 1 := hex.2.2.2.2.2.2.2.1
  have heigchi : ∀ x : ℝ, prolateSLAction c R x = (signedModeRadialData a n).chi * R x :=
    hex.2.2.2.2.2.2.2.2.2.1
  have hsratio : s = radialSeparationRatio c (signedModeRadialData a n).chi :=
    hex.2.2.2.2.2.2.2.2.2.2.1
  have hode : ∀ x : ℝ, (x ^ (2 : ℕ) - 1) * deriv (deriv R) x + 2 * x * deriv R x
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (2 : ℕ)) * R x = 0 := hex.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hchi : (signedModeRadialData a n).chi = -(s * c ^ (2 : ℕ)) := by
    rw [hsratio, radialSeparationRatio]
    field_simp
  have heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c R y = -(s * c ^ (2 : ℕ)) * R y := by
    intro y _
    rw [heigchi y, hchi]
  have hdiff : Differentiable ℝ R := (contDiff_infty_iff_deriv.mp hsm).1
  have hdiff2 : Differentiable ℝ (deriv R) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hsm).2).1
  have hΦd : ∀ t : ℝ, HasDerivAt R (deriv R t) t := fun t => (hdiff t).hasDerivAt
  have hDR : ∀ t : ℝ, HasDerivAt (deriv R) (deriv (deriv R) t) t := fun t => (hdiff2 t).hasDerivAt
  have hpos : ∀ y ∈ Icc (Real.sqrt s) 1, 0 < R y :=
    prolate_pos_on_right_of_radial_turning hs0.le hsm heig hR1
  have hposΦ : ∀ t ∈ Icc (2 * Real.sqrt s) 1, 0 < R t := by
    intro t ht
    exact hpos t ⟨le_trans (by linarith) ht.1, ht.2⟩
  have hleak0 : 0 ≤ 1 - evenProlateSignedValue a n ^ (2 : ℕ) :=
    one_sub_evenProlateSignedValue_sq_nonneg a n
  have hv2 : evenProlateSignedValue a n ^ (2 : ℕ) ≤ 1 := by linarith
  have hleak : 0 ≤ evenProlateSignedLeakage a n / 2 := by
    rw [evenProlateSignedLeakage]
    linarith
  have hmass : (∫ x in Ioi (1 : ℝ), R x ^ (2 : ℕ))
      = (∫ y in (-1 : ℝ)..1, R y ^ (2 : ℕ)) * (evenProlateSignedLeakage a n / 2)
        / evenProlateSignedValue a n ^ (2 : ℕ) :=
    integral_Ioi_sq_signedModeRadialData hapos n hvne
  have hz : 1 ≤ c * bandEndpointPhase s α := by
    have hlow := sqrt_mul_arccos_le_bandEndpointPhase (s := s) (y := α) hα0.le hα1.le
    have hmono : Real.sqrt (α ^ (2 : ℕ) - 1 / 64) ≤ Real.sqrt (α ^ (2 : ℕ) - s) :=
      Real.sqrt_le_sqrt (by linarith)
    have hκle : κ ≤ bandEndpointPhase s α := by
      refine le_trans ?_ hlow
      rw [hκ]
      exact mul_le_mul_of_nonneg_right hmono (Real.arccos_nonneg α)
    have hone : 1 ≤ c * κ := (div_le_iff₀ hκpos).mp hcκ
    nlinarith [hone, hκle, hc0]
  have hcinv : 1 / c ≤ 1 / 8 := by
    rw [div_le_div_iff₀ hc0 (by norm_num : (0 : ℝ) < 8)]
    linarith
  have hb : 2 * Real.sqrt s < prolateLeakageCut c s := by
    rw [prolateLeakageCut]
    have : 0 < 1 / c := by positivity
    linarith
  have hb1 : prolateLeakageCut c s < 1 := by
    rw [prolateLeakageCut]
    have h2s : 2 * Real.sqrt s ≤ 1 / 4 := by linarith
    linarith
  exact prolate_leakage_le_shifted hc8 hs0 hs8 hsm heig hR1 h2sα hαhalf hα1 hαcollar hz
    hposΦ hb hb1 hR1 hΦd hDR hode hv2 hvne hleak hmass

end RHTower

end
