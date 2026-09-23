import GaloisForLFunctions.RHTower.ProlateLeakageTwoSided
import GaloisForLFunctions.RHTower.ProlateCanonicalBandMass
import GaloisForLFunctions.RHTower.ProlateCanonicalOscillatorLower
import GaloisForLFunctions.RHTower.ConstrainedProlateSignedTrial
import GaloisForLFunctions.RHTower.ProlateTurningLayer

/-!
# The two-sided leakage estimate at the canonical indexed family

`prolate_leakage_two_sided` is stated for a mode presented by explicit data.  The canonical
indexed even prolate family supplies every one of those data at all large apertures: its radial
datum is smooth, even, endpoint-normalized, solves the prolate equation with separation constant
`−s c²`, is positive from its turning point outwards, has square-integrable exterior mass, and
carries the exact leakage mass identity.

The numerical side conditions are eventual because `c = 2πa² → ∞` while `c·s → 4n+1`: a fixed
collar `α = 1 − 1/2400` satisfies the collar inequality with equality, and every remaining
inequality is a consequence of `s → 0` together with `c·s → 4n+1`.  The condition `4 ≤ c·s` is what
excludes the ground index, where `c·s → 1`.

The exterior mass identity of the corpus is stated on the complement of the band, which is twice the
half-line mass; the leakage that the estimate bounds is therefore half the signed leakage.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

/-- The fixed collar of the leakage instantiation: `600·(1 − α) = 1/4` exactly. -/
def prolateLeakageCollar : ℝ := 1 - 1 / 2400

theorem prolateLeakageCollar_lt_one : prolateLeakageCollar < 1 := by
  rw [prolateLeakageCollar]; norm_num

theorem prolateLeakageCollar_gt_half : (1 : ℝ) / 2 < prolateLeakageCollar := by
  rw [prolateLeakageCollar]; norm_num

theorem prolateLeakageCollar_collar : 600 * (1 - prolateLeakageCollar) ≤ 1 / 4 := by
  rw [prolateLeakageCollar]; norm_num

theorem prolateLeakageCollar_pos : 0 < prolateLeakageCollar := by
  rw [prolateLeakageCollar]; norm_num

/-- The half-line exterior mass of the canonical radial datum. -/
theorem integral_Ioi_sq_signedModeRadialData {a : ℝ} (ha : 0 < a) (n : ℕ)
    (hvalue : evenProlateSignedValue a n ≠ 0) :
    (∫ x in Ioi (1 : ℝ), (signedModeRadialData a n).R x ^ (2 : ℕ))
      = (∫ x in (-1 : ℝ)..1, (signedModeRadialData a n).R x ^ (2 : ℕ))
        * (evenProlateSignedLeakage a n / 2) / evenProlateSignedValue a n ^ (2 : ℕ) := by
  have hD := signedModeRadialData_isExact ha n hvalue
  have hEven : Function.Even (signedModeRadialData a n).R := hD.2.2.2.2.2.2.1
  have hint : Integrable (fun x : ℝ => (signedModeRadialData a n).R x ^ (2 : ℕ)) :=
    integrable_sq_signedModeRadialData ha n hvalue
  have hcompl : (Icc (-1 : ℝ) 1)ᶜ = Iio (-1) ∪ Ioi 1 := by
    ext x
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le, mem_union, mem_Iio, mem_Ioi]
  have hrefl : (∫ x in Iio (-1 : ℝ), (signedModeRadialData a n).R x ^ (2 : ℕ))
      = ∫ x in Ioi (1 : ℝ), (signedModeRadialData a n).R x ^ (2 : ℕ) := by
    have h := integral_comp_neg_Ioi (1 : ℝ) fun x : ℝ => (signedModeRadialData a n).R x ^ (2 : ℕ)
    have hfun : (fun x : ℝ => (signedModeRadialData a n).R (-x) ^ (2 : ℕ))
        = fun x : ℝ => (signedModeRadialData a n).R x ^ (2 : ℕ) := by
      funext x
      rw [hEven x]
    rw [hfun] at h
    have hIic : (∫ x in Iic (-1 : ℝ), (signedModeRadialData a n).R x ^ (2 : ℕ))
        = ∫ x in Iio (-1 : ℝ), (signedModeRadialData a n).R x ^ (2 : ℕ) := by
      rw [← MeasureTheory.integral_Iic_eq_integral_Iio]
    rw [hIic] at h
    exact h.symm
  have hsplit : (∫ x in (Icc (-1 : ℝ) 1)ᶜ, (signedModeRadialData a n).R x ^ (2 : ℕ))
      = 2 * ∫ x in Ioi (1 : ℝ), (signedModeRadialData a n).R x ^ (2 : ℕ) := by
    rw [hcompl, setIntegral_union (by
        rw [Set.disjoint_left]
        intro x hx hx'
        exact absurd (lt_trans hx (by norm_num : (-1 : ℝ) < 1)) (not_lt.2 (le_of_lt hx')))
      measurableSet_Ioi hint.integrableOn hint.integrableOn, hrefl]
    ring
  have hmass := integral_outside_sq_signedModeRadialData_eq_leakage_ratio ha n hvalue
  rw [hsplit] at hmass
  have hσ : evenProlateSignedValue a n ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hvalue
  field_simp at hmass ⊢
  linarith [hmass]

/-! ## The two bounds, with the collar and cut fixed -/

/-- The lower leakage bound of the two-sided estimate at the fixed collar. -/
def prolateLeakageLower (c s : ℝ) : ℝ :=
  besselEnergyFloor / 864 / c
    / (2 * (2 * (3 * (1 + (1 - prolateLeakageCollar ^ (2 : ℕ))
          * (prolateRadialBarrier c s prolateLeakageCollar + 6 / (1 - prolateLeakageCollar)) ^ (2 : ℕ)
          / (c ^ (2 : ℕ) * (prolateLeakageCollar ^ (2 : ℕ) - s))) + 1)
      * Real.exp (2 * c * (1 + s / 4 * Real.log s)
          + ((Real.log (prolateLeakageCollar ^ (2 : ℕ) - s) - Real.log (3 * s))
            + (Real.log (1 - 4 * s) - Real.log (1 - prolateLeakageCollar ^ (2 : ℕ))))
          + 10 * (c * s))))

/-- The cut of the two-sided estimate: one inverse bandwidth above the turning scale.  The
transport loss across `[2√s, b]` is then bounded, and the reciprocal width costs one power of the
bandwidth. -/
def prolateLeakageCut (c s : ℝ) : ℝ := 2 * Real.sqrt s + 1 / c

/-- The upper leakage bound of the two-sided estimate at the fixed collar and the cut above. -/
def prolateLeakageUpper (c s : ℝ) : ℝ :=
  radialProlateExteriorMassConstant / c
    * ((6 * Real.pi * Real.sqrt (c * bandEndpointPhase s prolateLeakageCollar)) ^ (2 : ℕ)
        * Real.exp (2 * ((c * prolateLeakageCut c s + 12)
            * (prolateLeakageCut c s - 2 * Real.sqrt s) / (1 - prolateLeakageCut c s ^ (2 : ℕ))))
        / (prolateLeakageCut c s - 2 * Real.sqrt s))
    * Real.exp (-(2 * (c * bandEndpointPhase s (2 * Real.sqrt s)
        + 6 * (Real.log (1 - prolateLeakageCollar) - Real.log (1 - 2 * Real.sqrt s)))))

/-- **The two-sided leakage estimate at the canonical indexed family.**  Every hypothesis of
`prolate_leakage_two_sided` holds at all large apertures for the canonical radial datum of the
`n`-th signed even mode, once `n ≥ 1` so that `c·s → 4n+1 > 4`. -/
theorem eventually_signedLeakage_two_sided (n : ℕ) (hn : 1 ≤ n) :
    ∀ᶠ a : ℝ in atTop,
      prolateLeakageLower (signedModeRadialBandwidth a) (signedModeRadialData a n).s
          ≤ evenProlateSignedLeakage a n / 2 ∧
        evenProlateSignedLeakage a n / 2
          ≤ prolateLeakageUpper (signedModeRadialBandwidth a) (signedModeRadialData a n).s := by
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
  have hn1 : (4 : ℝ) < 4 * (n : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hcs_lo : ∀ᶠ a : ℝ in atTop, 4 < signedModeRadialBandwidth a * (signedModeRadialData a n).s :=
    hlimit.eventually (eventually_gt_nhds hn1)
  have hcs_hi : ∀ᶠ a : ℝ in atTop,
      signedModeRadialBandwidth a * (signedModeRadialData a n).s < 4 * (n : ℝ) + 2 :=
    hlimit.eventually (eventually_lt_nhds (by linarith))
  set C₀ : ℝ := max (max 8 (1728 * radialProlateDensityTransferConstant / besselEnergyFloor))
    (max (64 * (4 * (n : ℝ) + 2)) (1 / κ)) with hC₀
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
  have hc8 : (8 : ℝ) ≤ c := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hcb
  have hcK : 1728 * radialProlateDensityTransferConstant / besselEnergyFloor ≤ c :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hcb
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
  have hcs : 4 ≤ c * s := le_of_lt hlo
  -- structural data of the canonical radial datum
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R := hex.2.2.2.2.2.1
  have hR1 : R 1 = 1 := hex.2.2.2.2.2.2.2.1
  have heven : Function.Even R := hex.2.2.2.2.2.2.1
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
  have hfluxd : ∀ t ∈ Icc (0 : ℝ) α, HasDerivAt (fun u => (1 - u ^ (2 : ℕ)) * deriv R u)
      (-(c ^ (2 : ℕ) * (s - t ^ (2 : ℕ)) * R t)) t := by
    intro t _
    have h1 : HasDerivAt (fun u : ℝ => 1 - u ^ (2 : ℕ)) (-(2 * t)) t := by
      have h0 := (hasDerivAt_pow 2 t).const_sub 1
      refine h0.congr_deriv ?_
      push_cast
      ring
    have h := h1.mul (hDR t)
    refine h.congr_deriv ?_
    have ho := hode t
    linear_combination -ho
  have hIntR : IntegrableOn (fun x => R x ^ (2 : ℕ)) (Ioi (1 : ℝ)) :=
    (integrable_sq_signedModeRadialData hapos n hvne).integrableOn
  have hleak0 : 0 ≤ 1 - evenProlateSignedValue a n ^ (2 : ℕ) :=
    one_sub_evenProlateSignedValue_sq_nonneg a n
  have hvalue : 1 / 2 ≤ evenProlateSignedValue a n ^ (2 : ℕ) := le_of_lt hsig
  have hv2 : evenProlateSignedValue a n ^ (2 : ℕ) ≤ 1 := by linarith
  have hleak : 0 ≤ evenProlateSignedLeakage a n / 2 := by
    rw [evenProlateSignedLeakage]
    linarith
  have hmass : (∫ x in Ioi (1 : ℝ), R x ^ (2 : ℕ))
      = (∫ y in (-1 : ℝ)..1, R y ^ (2 : ℕ)) * (evenProlateSignedLeakage a n / 2)
        / evenProlateSignedValue a n ^ (2 : ℕ) :=
    integral_Ioi_sq_signedModeRadialData hapos n hvne
  have hα2 : (1 : ℝ) / 64 ≤ 2 * α ^ (2 : ℕ) - 1 := by
    rw [hα, prolateLeakageCollar]
    norm_num
  have houter : ∀ t ∈ Icc α 1, c ^ (2 : ℕ) * (1 - 2 * t ^ (2 : ℕ)) ≤ -(s * c ^ (2 : ℕ)) := by
    intro t ht
    have htsq : α ^ (2 : ℕ) ≤ t ^ (2 : ℕ) := by nlinarith [ht.1, hα0]
    nlinarith [hα2, hs64, htsq, sq_nonneg c, hc0]
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
    rw [div_le_div_iff₀ hc0 (by norm_num : (0:ℝ) < 8)]
    linarith
  have hb : 2 * Real.sqrt s < prolateLeakageCut c s := by
    rw [prolateLeakageCut]
    have : 0 < 1 / c := by positivity
    linarith
  have hb1 : prolateLeakageCut c s < 1 := by
    rw [prolateLeakageCut]
    have h2s : 2 * Real.sqrt s ≤ 1 / 4 := by linarith
    linarith
  exact prolate_leakage_two_sided hc8 hs0 hs8 hcs hcK hsm heig hR1 heven h2sα hαhalf hα1
    hαcollar hz houter hposΦ hΦd hfluxd hb hb1 hR1 hΦd hDR hode hIntR hvalue hv2
    hvne hleak hmass

end RHTower

end
