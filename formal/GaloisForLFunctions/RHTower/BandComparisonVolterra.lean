import GaloisForLFunctions.RHTower.BandLiouvilleWeight
import GaloisForLFunctions.RHTower.BandDefectMass
import GaloisForLFunctions.HTGeometry.VolterraContraction
import GaloisForLFunctions.HTGeometry.AbstractComparisonTransport
import GaloisForLFunctions.HTGeometry.InteriorIntegrationByParts

/-!
# The band comparison, transported to the endpoint

The drift Wronskian of a band solution against the modified-Bessel model,

```text
W = m̃ (U V' - U' V) ,      m̃ = Ξ/P ,   V = I₀(cΞ) ,
```

has derivative exactly `m̃ a U V` with `a` the comparison defect, and it *vanishes at the endpoint* —
not because of any cancellation, but because `m̃` vanishes there while `m̃ V' = -c Ξ I₀'(cΞ)` stays
bounded.  Written that way the Wronskian is manifestly continuous up to `y = 1`, so the transport is
an ordinary fundamental-theorem statement on a closed interval; no improper integral and no limiting
argument are needed.

The density that the transport integrates is bounded outright:

```text
m̃ |a| ≤ 6(1-y) · 100/(1-y²) ≤ 600 ,
```

the linear vanishing of the Liouville weight exactly cancelling the simple pole of the defect.
-/

noncomputable section

open Set MeasureTheory

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- The drift Wronskian of a band solution against the modified-Bessel model. -/
def bandWronskian (s c : ℝ) (U DU : ℝ → ℝ) : ℝ → ℝ :=
  driftWronskian (bandLiouvilleWeight s) U DU (bandModel s c) (bandModelDerivFn s c)

/-- The comparison ratio. -/
def bandRatio (s c : ℝ) (U : ℝ → ℝ) (y : ℝ) : ℝ := U y / bandModel s c y

theorem continuous_besselI0Deriv : Continuous besselI0Deriv :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_besselI0Deriv u).continuousAt

section

variable {s c y α : ℝ} {U DU : ℝ → ℝ}

/-- **The transport law on the band.**  The Wronskian moves exactly by the defect density. -/
theorem hasDerivAt_bandWronskian (hs1 : s ≤ 1 / 8) (hc : 0 < c)
    (hy0 : 1 / 2 < y) (hy1 : y < 1)
    (hU : HasDerivAt U (DU y) y)
    (hDU : HasDerivAt DU (-(bandFirstOrderCoeff s y) * DU y
      - (-(c ^ 2 * prolateWKBProfile s y ^ 2) + bandComparisonDefect s y) * U y) y) :
    HasDerivAt (bandWronskian s c U DU)
      (bandLiouvilleWeight s y * bandComparisonDefect s y * (U y * bandModel s c y)) y := by
  have hys : s < y ^ 2 := by nlinarith
  have hm := hasDerivAt_bandLiouvilleWeight (s := s) (by linarith) hy1 hys
  have hV := hasDerivAt_bandModel (s := s) (c := c) (by linarith) hy1 hys.le
  have hDV : HasDerivAt (bandModelDerivFn s c)
      (-(bandFirstOrderCoeff s y) * bandModelDerivFn s c y
        - (-(c ^ 2 * prolateWKBProfile s y ^ 2) + 0) * bandModel s c y) y := by
    have h := hasDerivAt_bandModelDerivFn (s := s) (c := c) (by linarith) hy1 hys
    refine h.congr_deriv ?_
    have hode := bandModel_ode (s := s) (c := c) hc (by linarith) hy1 hys
    linarith [hode]
  have h := hasDerivAt_driftWronskian (m := bandLiouvilleWeight s)
    (B := bandFirstOrderCoeff s) (κ := -(c ^ 2 * prolateWKBProfile s y ^ 2))
    (a := bandComparisonDefect s y) (b := 0) hm hU hDU hV hDV
  refine h.congr_deriv ?_
  ring

/-- **The transported density is bounded.**  The linear vanishing of the Liouville weight cancels the
simple pole of the defect. -/
theorem bandLiouvilleWeight_mul_abs_defect_le (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8)
    (hy0 : 1 / 2 ≤ y) (hy1 : y < 1) :
    bandLiouvilleWeight s y * |bandComparisonDefect s y| ≤ 600 := by
  have hy2 : y ^ 2 < 1 := by nlinarith
  have h1y2 : (0 : ℝ) < 1 - y ^ 2 := by linarith
  have hm := bandLiouvilleWeight_le hs0 hs1 hy0 hy1.le
  have hmnn : 0 ≤ bandLiouvilleWeight s y := by
    have hys : s < y ^ 2 := by nlinarith
    exact (bandLiouvilleWeight_pos (by linarith) hy1 hys).le
  have ha := abs_bandComparisonDefect_le hs0 hs1 hy0 hy1
  have hanb : |bandComparisonDefect s y| * (1 - y ^ 2) ≤ 100 := (le_div_iff₀ h1y2).mp ha
  have hkey : |bandComparisonDefect s y| * (1 - y) ≤ 100 := by
    nlinarith [hanb, abs_nonneg (bandComparisonDefect s y), hy0]
  nlinarith [hm, hkey, hmnn, abs_nonneg (bandComparisonDefect s y),
    (by linarith : (0:ℝ) ≤ 1 - y)]

/-- The Liouville weight is continuous up to the endpoint, where it vanishes. -/
theorem continuousOn_bandLiouvilleWeight (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8) (hα : 1 / 2 ≤ α) :
    ContinuousOn (bandLiouvilleWeight s) (Icc α 1) := by
  intro t ht
  have ht0 : (1 : ℝ) / 2 ≤ t := le_trans hα ht.1
  rcases eq_or_lt_of_le ht.2 with rfl | hlt
  · rw [ContinuousWithinAt, bandLiouvilleWeight_one]
    refine squeeze_zero_norm' (a := fun u : ℝ => 6 * (1 - u)) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with u hu
      have hu1 : u ≤ 1 := hu.2
      have hu0 : α ≤ u := hu.1
      have hnn : 0 ≤ bandLiouvilleWeight s u := by
        rcases eq_or_lt_of_le hu1 with rfl | hult
        · rw [bandLiouvilleWeight_one]
        · have hys : s < u ^ 2 := by nlinarith
          exact (bandLiouvilleWeight_pos (by linarith) hult hys).le
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact bandLiouvilleWeight_le hs0 hs1 (by linarith) hu1
    · have h0 : Filter.Tendsto (fun u : ℝ => 6 * (1 - u)) (nhds (1:ℝ)) (nhds (6 * (1 - 1))) :=
        (continuous_const.mul (continuous_const.sub continuous_id)).tendsto (1:ℝ)
      simp only [sub_self, mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
  · have hys : s < t ^ 2 := by nlinarith
    have hy : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
    have hP : 0 < prolateWKBProfile s t := prolateWKBProfile_pos hy hys
    have hcXi : ContinuousWithinAt (bandEndpointPhase s) (Icc α 1) t :=
      (continuous_bandEndpointPhase s).continuousWithinAt
    have hcP : ContinuousWithinAt (prolateWKBProfile s) (Icc α 1) t :=
      ((hasDerivAt_prolateWKBProfile hy.ne' (by positivity)).continuousAt).continuousWithinAt
    exact hcXi.div hcP hP.ne'

/-- `m̃ V' = -c Ξ I₀'(cΞ)`: the Liouville weight kills the endpoint singularity of the model's
derivative. -/
theorem bandLiouvilleWeight_mul_modelDeriv (hs1 : s ≤ 1 / 8) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 1) :
    bandLiouvilleWeight s y * bandModelDerivFn s c y
      = -(c * besselI0Deriv (c * bandEndpointPhase s y) * bandEndpointPhase s y) := by
  rcases eq_or_lt_of_le hy1 with rfl | hlt
  · rw [bandLiouvilleWeight_one, bandEndpointPhase_one]
    ring
  · have hys : s < y ^ 2 := by nlinarith
    have hy : (0 : ℝ) < 1 - y ^ 2 := by nlinarith
    have hP : 0 < prolateWKBProfile s y := prolateWKBProfile_pos hy hys
    rw [bandLiouvilleWeight, bandModelDerivFn, besselIModelDeriv, bandPhaseDeriv]
    field_simp

theorem bandWronskian_one (s c : ℝ) (U DU : ℝ → ℝ) : bandWronskian s c U DU 1 = 0 := by
  rw [bandWronskian, driftWronskian, bandLiouvilleWeight_one, zero_mul]

theorem bandWronskian_eqOn (hs1 : s ≤ 1 / 8) (hα : 1 / 2 ≤ α) :
    EqOn (bandWronskian s c U DU)
      (fun t : ℝ => -(c * besselI0Deriv (c * bandEndpointPhase s t) * bandEndpointPhase s t) * U t
        - bandLiouvilleWeight s t * DU t * bandModel s c t) (Icc α 1) := by
  intro t ht
  have ht0 : (1 : ℝ) / 2 ≤ t := le_trans hα ht.1
  have h := bandLiouvilleWeight_mul_modelDeriv (s := s) (c := c) (y := t) hs1 ht0 ht.2
  show bandLiouvilleWeight s t * (U t * bandModelDerivFn s c t - DU t * bandModel s c t)
      = -(c * besselI0Deriv (c * bandEndpointPhase s t) * bandEndpointPhase s t) * U t
        - bandLiouvilleWeight s t * DU t * bandModel s c t
  linear_combination U t * h

theorem continuousOn_bandWronskian (hs1 : s ≤ 1 / 8) (hα : 1 / 2 ≤ α)
    (hUc : ContinuousOn U (Icc α 1)) (hDUc : ContinuousOn (fun t : ℝ => bandLiouvilleWeight s t * DU t) (Icc α 1)) :
    ContinuousOn (bandWronskian s c U DU) (Icc α 1) := by
  have hXi : ContinuousOn (bandEndpointPhase s) (Icc α 1) :=
    (continuous_bandEndpointPhase s).continuousOn
  have h1 : ContinuousOn
      (fun t : ℝ => -(c * besselI0Deriv (c * bandEndpointPhase s t) * bandEndpointPhase s t) * U t)
      (Icc α 1) := by
    refine ContinuousOn.mul (ContinuousOn.neg (ContinuousOn.mul (continuousOn_const.mul ?_) hXi))
      hUc
    exact continuous_besselI0Deriv.comp_continuousOn (continuousOn_const.mul hXi)
  have h2 : ContinuousOn
      (fun t : ℝ => bandLiouvilleWeight s t * DU t * bandModel s c t) (Icc α 1) :=
    hDUc.mul (continuous_bandModel s c).continuousOn
  exact (h1.sub h2).congr (bandWronskian_eqOn (c := c) (U := U) (DU := DU) hs1 hα)

theorem bandModel_le_of_le (hc : 0 ≤ c) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    bandModel s c t₂ ≤ bandModel s c t₁ := antitone_bandModel hc h

/-- **The endpoint-anchored transport.**  The Wronskian is the improper defect integral, but with no
improper integral: it is an ordinary fundamental-theorem statement on a closed interval. -/
theorem bandWronskian_eq_neg_integral (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8) (hc : 0 < c)
    (hα : 1 / 2 < α)
    (hUc : ContinuousOn U (Icc α 1)) (hDUc : ContinuousOn (fun t : ℝ => bandLiouvilleWeight s t * DU t) (Icc α 1))
    (hU : ∀ x ∈ Ioo α 1, HasDerivAt U (DU x) x)
    (hDU : ∀ x ∈ Ioo α 1, HasDerivAt DU (-(bandFirstOrderCoeff s x) * DU x
      - (-(c ^ 2 * prolateWKBProfile s x ^ 2) + bandComparisonDefect s x) * U x) x)
    {K : ℝ} (hK : ∀ x ∈ Ioo α 1,
      |bandLiouvilleWeight s x * bandComparisonDefect s x
        * (U x * bandModel s c x)| ≤ K)
    {τ : ℝ} (hτ : τ ∈ Icc α 1) :
    bandWronskian s c U DU τ
      = -∫ t in τ..1, bandLiouvilleWeight s t * bandComparisonDefect s t
          * (U t * bandModel s c t) := by
  have hτ1 : τ ≤ 1 := hτ.2
  have hsub : Icc τ 1 ⊆ Icc α 1 := Icc_subset_Icc hτ.1 le_rfl
  have hcont : ContinuousOn (bandWronskian s c U DU) (Icc τ 1) :=
    (continuousOn_bandWronskian hs1 hα.le hUc hDUc).mono hsub
  have hderiv : ∀ x ∈ Ioo τ 1, HasDerivWithinAt (bandWronskian s c U DU)
      (bandLiouvilleWeight s x * bandComparisonDefect s x * (U x * bandModel s c x))
      (Ioi x) x := by
    intro x hx
    have hx' : x ∈ Ioo α 1 := ⟨lt_of_le_of_lt hτ.1 hx.1, hx.2⟩
    exact (hasDerivAt_bandWronskian hs1 hc (lt_of_lt_of_le hα hx'.1.le) hx'.2
      (hU x hx') (hDU x hx')).hasDerivWithinAt
  have hint : IntervalIntegrable
      (fun t : ℝ => bandLiouvilleWeight s t * bandComparisonDefect s t
        * (U t * bandModel s c t)) volume τ 1 := by
    refine intervalIntegrable_of_continuousOn_Ioo_of_bounded (M := K) hτ1 ?_ ?_
    · have hsub' : Ioo τ 1 ⊆ Ioo (1 / 2 : ℝ) 1 :=
        fun x hx => ⟨lt_of_lt_of_le hα (le_trans hτ.1 hx.1.le), hx.2⟩
      have hsub'' : Ioo τ 1 ⊆ Icc α 1 :=
        fun x hx => ⟨le_trans hτ.1 hx.1.le, hx.2.le⟩
      exact (((continuousOn_bandLiouvilleWeight hs0 hs1 hα.le).mono hsub'').mul
        ((continuousOn_bandComparisonDefect hs1).mono hsub')).mul
        ((hUc.mono hsub'').mul (continuous_bandModel s c).continuousOn)
    · intro x hx
      exact hK x ⟨lt_of_le_of_lt hτ.1 hx.1, hx.2⟩
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hτ1 hcont hderiv hint
  rw [hFTC, bandWronskian_one]
  ring

theorem bandLiouvilleWeight_mul_abs_defect_le' (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8)
    (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 1) :
    bandLiouvilleWeight s y * |bandComparisonDefect s y| ≤ 600 := by
  rcases eq_or_lt_of_le hy1 with rfl | hlt
  · rw [bandLiouvilleWeight_one, zero_mul]
    norm_num
  · exact bandLiouvilleWeight_mul_abs_defect_le hs0 hs1 hy0 hlt

theorem abs_U_mul_bandModel_le {M : ℝ} (hM : |bandRatio s c U y| ≤ M) :
    |U y| * bandModel s c y ≤ M * bandModel s c y ^ 2 := by
  have hV : 0 < bandModel s c y := bandModel_pos
  have hU : U y = bandRatio s c U y * bandModel s c y := by
    rw [bandRatio, div_mul_cancel₀ _ hV.ne']
  rw [hU, abs_mul, abs_of_pos hV]
  nlinarith [hM, abs_nonneg (bandRatio s c U y), hV]

/-- **The Wronskian is quadratically small at the endpoint.**  The bounded density and the vanishing
Liouville weight give `|W| ≤ 600 M V² (1-y)`. -/
theorem abs_bandWronskian_le (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8) (hc : 0 < c) (hα : 1 / 2 < α)
    (hUc : ContinuousOn U (Icc α 1)) (hDUc : ContinuousOn (fun t : ℝ => bandLiouvilleWeight s t * DU t) (Icc α 1))
    (hU : ∀ x ∈ Ioo α 1, HasDerivAt U (DU x) x)
    (hDU : ∀ x ∈ Ioo α 1, HasDerivAt DU (-(bandFirstOrderCoeff s x) * DU x
      - (-(c ^ 2 * prolateWKBProfile s x ^ 2) + bandComparisonDefect s x) * U x) x)
    {M : ℝ} (hM : ∀ t ∈ Icc α 1, |bandRatio s c U t| ≤ M)
    {τ : ℝ} (hτ : τ ∈ Icc α 1) :
    |bandWronskian s c U DU τ| ≤ 600 * M * bandModel s c τ ^ 2 * (1 - τ) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM τ hτ)
  have hdens : ∀ t ∈ Icc α 1, |bandLiouvilleWeight s t * bandComparisonDefect s t
      * (U t * bandModel s c t)| ≤ 600 * M * bandModel s c t ^ 2 := by
    intro t ht
    have ht0 : (1 : ℝ) / 2 ≤ t := le_trans hα.le ht.1
    have h1 := bandLiouvilleWeight_mul_abs_defect_le' hs0 hs1 ht0 ht.2
    have h2 := abs_U_mul_bandModel_le (s := s) (c := c) (U := U) (hM t ht)
    have hmnn : 0 ≤ bandLiouvilleWeight s t := by
      rcases eq_or_lt_of_le ht.2 with rfl | hlt
      · rw [bandLiouvilleWeight_one]
      · have hys : s < t ^ 2 := by nlinarith
        exact (bandLiouvilleWeight_pos (by linarith) hlt hys).le
    have hV : 0 < bandModel s c t := bandModel_pos
    rw [abs_mul, abs_mul, abs_of_nonneg hmnn, abs_mul, abs_of_pos hV]
    have hA : bandLiouvilleWeight s t * |bandComparisonDefect s t| * (|U t| * bandModel s c t)
        ≤ 600 * (|U t| * bandModel s c t) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have hB : 600 * (|U t| * bandModel s c t) ≤ 600 * M * bandModel s c t ^ 2 := by
      nlinarith [h2]
    linarith [hA, hB]
  have hKbd : ∀ x ∈ Ioo α 1, |bandLiouvilleWeight s x * bandComparisonDefect s x
      * (U x * bandModel s c x)| ≤ 600 * M * bandModel s c α ^ 2 := by
    intro x hx
    refine le_trans (hdens x ⟨hx.1.le, hx.2.le⟩) ?_
    have hVle : bandModel s c x ≤ bandModel s c α := antitone_bandModel hc.le hx.1.le
    have hV : 0 < bandModel s c x := bandModel_pos
    have hsq : bandModel s c x ^ 2 ≤ bandModel s c α ^ 2 := by nlinarith [hV.le, hVle]
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ) ≤ 600 * M)]
  have heq := bandWronskian_eq_neg_integral hs0 hs1 hc hα hUc hDUc hU hDU hKbd hτ
  have hconst : ∀ t ∈ Set.uIoc τ 1, ‖bandLiouvilleWeight s t * bandComparisonDefect s t
      * (U t * bandModel s c t)‖ ≤ 600 * M * bandModel s c τ ^ 2 := by
    intro t ht
    rw [Set.uIoc_of_le hτ.2] at ht
    have htmem : t ∈ Icc α 1 := ⟨le_trans hτ.1 ht.1.le, ht.2⟩
    refine le_trans (hdens t htmem) ?_
    have hVle : bandModel s c t ≤ bandModel s c τ := antitone_bandModel hc.le ht.1.le
    have hV : 0 < bandModel s c t := bandModel_pos
    have hsq : bandModel s c t ^ 2 ≤ bandModel s c τ ^ 2 := by nlinarith [hV.le, hVle]
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ) ≤ 600 * M)]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hconst
  rw [heq, abs_neg]
  have habs : |1 - τ| = 1 - τ := abs_of_nonneg (by linarith [hτ.2])
  rw [Real.norm_eq_abs] at hnorm
  rw [habs] at hnorm
  exact hnorm

/-- The comparison ratio differentiates to the transported Wronskian. -/
theorem hasDerivAt_bandRatio (hs1 : s ≤ 1 / 8) (hy0 : 1 / 2 < y) (hy1 : y < 1)
    (hU : HasDerivAt U (DU y) y) :
    HasDerivAt (bandRatio s c U)
      (-(bandWronskian s c U DU y / (bandLiouvilleWeight s y * bandModel s c y ^ 2))) y := by
  have hys : s < y ^ 2 := by nlinarith
  have hV : 0 < bandModel s c y := bandModel_pos
  have hm : 0 < bandLiouvilleWeight s y := bandLiouvilleWeight_pos (by linarith) hy1 hys
  have hVd := hasDerivAt_bandModel (s := s) (c := c) (by linarith) hy1 hys.le
  have h := hU.fun_div hVd hV.ne'
  refine h.congr_deriv ?_
  rw [bandWronskian, driftWronskian]
  field_simp
  ring

theorem bandRatio_one (hU1 : U 1 = 1) : bandRatio s c U 1 = 1 := by
  rw [bandRatio, hU1, bandModel_one, div_one]

theorem continuousOn_bandRatio (hUc : ContinuousOn U (Icc α 1)) :
    ContinuousOn (bandRatio s c U) (Icc α 1) :=
  hUc.div (continuous_bandModel s c).continuousOn fun _ _ => bandModel_pos.ne'

/-- **The Volterra estimate.**  Every uniform bound on the ratio reproduces itself, contracted by the
total kernel mass `600(1-α)`. -/
theorem abs_bandRatio_sub_one_le_of_bound (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8) (hc : 0 < c)
    (hα : 1 / 2 < α) (hα1 : α < 1)
    (hUc : ContinuousOn U (Icc α 1)) (hDUc : ContinuousOn (fun t : ℝ => bandLiouvilleWeight s t * DU t) (Icc α 1))
    (hU : ∀ x ∈ Ioo α 1, HasDerivAt U (DU x) x)
    (hDU : ∀ x ∈ Ioo α 1, HasDerivAt DU (-(bandFirstOrderCoeff s x) * DU x
      - (-(c ^ 2 * prolateWKBProfile s x ^ 2) + bandComparisonDefect s x) * U x) x)
    (hU1 : U 1 = 1)
    {M : ℝ} (hM : ∀ t ∈ Icc α 1, |bandRatio s c U t| ≤ M)
    {y : ℝ} (hy : y ∈ Icc α 1) :
    |bandRatio s c U y - 1| ≤ M * (600 * (1 - α)) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM y hy)
  have hy1 : y ≤ 1 := hy.2
  have hsub : Icc y 1 ⊆ Icc α 1 := Icc_subset_Icc hy.1 le_rfl
  -- the pointwise bound on the derivative of the ratio
  have hderivbd : ∀ x ∈ Ioo y 1,
      |-(bandWronskian s c U DU x
        / (bandLiouvilleWeight s x * bandModel s c x ^ 2))| ≤ 600 * M := by
    intro x hx
    have hxmem : x ∈ Icc α 1 := ⟨le_trans hy.1 hx.1.le, hx.2.le⟩
    have hx0 : (1 : ℝ) / 2 < x := lt_of_lt_of_le hα hxmem.1
    have hys : s < x ^ 2 := by nlinarith
    have hm : 0 < bandLiouvilleWeight s x := bandLiouvilleWeight_pos (by linarith) hx.2 hys
    have hV : 0 < bandModel s c x := bandModel_pos
    have hmlow : 1 - x ≤ bandLiouvilleWeight s x :=
      one_sub_le_bandLiouvilleWeight (by linarith) hx.2.le hys
    have hW := abs_bandWronskian_le hs0 hs1 hc hα hUc hDUc hU hDU hM hxmem
    rw [abs_neg, abs_div, abs_of_pos (by positivity : (0:ℝ) < bandLiouvilleWeight s x
      * bandModel s c x ^ 2), div_le_iff₀ (by positivity)]
    have hstep : 600 * M * bandModel s c x ^ 2 * (1 - x)
        ≤ 600 * M * (bandLiouvilleWeight s x * bandModel s c x ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hmlow
        (by positivity : (0:ℝ) ≤ 600 * M * bandModel s c x ^ 2)]
    linarith [hW, hstep]
  -- the derivative of the ratio, on the open interval
  have hRd : ∀ x ∈ Ioo y 1, HasDerivWithinAt (bandRatio s c U)
      (-(bandWronskian s c U DU x
        / (bandLiouvilleWeight s x * bandModel s c x ^ 2))) (Ioi x) x := by
    intro x hx
    have hxmem : x ∈ Ioo α 1 := ⟨lt_of_le_of_lt hy.1 hx.1, hx.2⟩
    have hx0 : (1 : ℝ) / 2 < x := lt_of_lt_of_le hα hxmem.1.le
    exact (hasDerivAt_bandRatio hs1 hx0 hx.2 (hU x hxmem)).hasDerivWithinAt
  -- integrability
  have hint : IntervalIntegrable
      (fun x : ℝ => -(bandWronskian s c U DU x
        / (bandLiouvilleWeight s x * bandModel s c x ^ 2))) volume y 1 := by
    refine intervalIntegrable_of_continuousOn_Ioo_of_bounded (M := 600 * M) hy1 ?_ hderivbd
    have hsub' : Ioo y 1 ⊆ Icc α 1 := fun x hx => ⟨le_trans hy.1 hx.1.le, hx.2.le⟩
    refine ContinuousOn.neg (ContinuousOn.div
      ((continuousOn_bandWronskian hs1 hα.le hUc hDUc).mono hsub')
      (((continuousOn_bandLiouvilleWeight hs0 hs1 hα.le).mono hsub').mul
        (((continuous_bandModel s c).continuousOn).pow 2)) ?_)
    intro x hx
    have hxmem : x ∈ Icc α 1 := hsub' hx
    have hx0 : (1 : ℝ) / 2 < x := lt_of_lt_of_le hα hxmem.1
    have hys : s < x ^ 2 := by nlinarith
    have hm : 0 < bandLiouvilleWeight s x := bandLiouvilleWeight_pos (by linarith) hx.2 hys
    have hV : 0 < bandModel s c x := bandModel_pos
    positivity
  have hRc : ContinuousOn (bandRatio s c U) (Icc y 1) :=
    (continuousOn_bandRatio (s := s) (c := c) hUc).mono hsub
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hy1 hRc hRd hint
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ => -(bandWronskian s c U DU x
      / (bandLiouvilleWeight s x * bandModel s c x ^ 2)))
    (a := y) (b := 1) (C := 600 * M) (by
      intro t ht
      rw [Set.uIoc_of_le hy1] at ht
      rw [Real.norm_eq_abs]
      rcases eq_or_lt_of_le ht.2 with rfl | hlt
      · rw [bandWronskian_one, bandLiouvilleWeight_one, zero_mul, div_zero, neg_zero, abs_zero]
        linarith [hM0]
      · exact hderivbd t ⟨ht.1, hlt⟩)
  rw [hFTC, bandRatio_one hU1] at hnorm
  have habs : |(1 : ℝ) - y| = 1 - y := abs_of_nonneg (by linarith)
  rw [habs] at hnorm
  have hyα : 1 - y ≤ 1 - α := by linarith [hy.1]
  have hfin : 600 * M * (1 - y) ≤ M * (600 * (1 - α)) := by nlinarith [hM0, hyα]
  calc |bandRatio s c U y - 1| = |1 - bandRatio s c U y| := by rw [abs_sub_comm]
    _ ≤ 600 * M * (1 - y) := hnorm
    _ ≤ M * (600 * (1 - α)) := hfin

/-- **The band comparison is two-sided with absolute constants.**  On a collar of width `1/2400` the
solution normalised at the endpoint is pinned to the modified-Bessel model within a third. -/
theorem abs_bandRatio_sub_one_le (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8) (hc : 0 < c)
    (hα : 1 / 2 < α) (hα1 : α < 1) (hcollar : 600 * (1 - α) ≤ 1 / 4)
    (hUc : ContinuousOn U (Icc α 1)) (hDUc : ContinuousOn (fun t : ℝ => bandLiouvilleWeight s t * DU t) (Icc α 1))
    (hU : ∀ x ∈ Ioo α 1, HasDerivAt U (DU x) x)
    (hDU : ∀ x ∈ Ioo α 1, HasDerivAt DU (-(bandFirstOrderCoeff s x) * DU x
      - (-(c ^ 2 * prolateWKBProfile s x ^ 2) + bandComparisonDefect s x) * U x) x)
    (hU1 : U 1 = 1) :
    ∀ y ∈ Icc α 1, |bandRatio s c U y - 1| ≤ 1 / 3 := by
  have hκ0 : (0 : ℝ) ≤ 600 * (1 - α) := by nlinarith [hα1]
  have hκ1 : 600 * (1 - α) < 1 := by linarith
  have h := abs_sub_one_le_of_self_bound (α := α) (β := 1) (κ := 600 * (1 - α))
    (R := bandRatio s c U) hα1.le (continuousOn_bandRatio (s := s) (c := c) hUc) hκ0 hκ1
    (fun y hy M hM => abs_bandRatio_sub_one_le_of_bound hs0 hs1 hc hα hα1 hUc hDUc hU hDU hU1
      hM hy)
  intro y hy
  refine le_trans (h y hy) ?_
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- The two-sided form: the solution is trapped between fixed multiples of the model. -/
theorem bandModel_le_and_le_bandModel (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8) (hc : 0 < c)
    (hα : 1 / 2 < α) (hα1 : α < 1) (hcollar : 600 * (1 - α) ≤ 1 / 4)
    (hUc : ContinuousOn U (Icc α 1)) (hDUc : ContinuousOn (fun t : ℝ => bandLiouvilleWeight s t * DU t) (Icc α 1))
    (hU : ∀ x ∈ Ioo α 1, HasDerivAt U (DU x) x)
    (hDU : ∀ x ∈ Ioo α 1, HasDerivAt DU (-(bandFirstOrderCoeff s x) * DU x
      - (-(c ^ 2 * prolateWKBProfile s x ^ 2) + bandComparisonDefect s x) * U x) x)
    (hU1 : U 1 = 1) :
    ∀ y ∈ Icc α 1, 2 / 3 * bandModel s c y ≤ U y ∧ U y ≤ 4 / 3 * bandModel s c y := by
  intro y hy
  have h := abs_bandRatio_sub_one_le hs0 hs1 hc hα hα1 hcollar hUc hDUc hU hDU hU1 y hy
  have hV : 0 < bandModel s c y := bandModel_pos
  have hbounds := abs_le.1 h
  have hU' : U y = bandRatio s c U y * bandModel s c y := by
    rw [bandRatio, div_mul_cancel₀ _ hV.ne']
  constructor
  · rw [hU']
    nlinarith [hbounds.1, hV]
  · rw [hU']
    nlinarith [hbounds.2, hV]

end

end GaloisForLFunctions.RHTower

end
