import GaloisForLFunctions.RHTower.RadialSymbolTwoBranchBound
import GaloisForLFunctions.RHTower.RadialPSWFAmplitudeVariation
import GaloisForLFunctions.RHTower.XiAmplitudeDecay
import GaloisForLFunctions.RHTower.RadialNormalFormPotentialDecay
import GaloisForLFunctions.RHTower.ExteriorDunsterPrimitive

/-!
# The symbol record of the actual exterior radial PSWF solutions

Everything the exterior two-index estimate consumes is already formal: the exact interaction-picture
decomposition, the `O(1/c)` amplitude variation, the Liouville amplitude's half-power symbol bounds,
the `1/x²` decay of the normal-form potential, the growth `x ≤ ξ_s(rx)` of the dilated phase, the
two-index phase separation and the phase curvature.

This file performs the instantiation those pieces were built for: it produces, for a genuine
solution of the exterior normal form `W'' + (c² − ψ)W = 0`, the `SymbolTwoBranch` record of the
dilated profile `x ↦ A_s(rx)·(amplitudes at ξ_s(rx))`, with the explicit constants

```text
M  = (4/√r)·K ,      M' = (4/√r)·K + (4/√r)·K' ,      K' = κ K_W (4r/3)/c ,
```

`K` bounding the interaction amplitudes along the phase, `K_W` the solution, and `κ` the potential
symbol constant.  Feeding two such records into `abs_integral_radial_twoBranch_symbol_le'` gives the
card's off-diagonal entry estimate for the actual solutions.
-/

open Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-! ## The dilated exterior Liouville amplitude -/

/-- The Liouville amplitude of the `r`-fold dilate. -/
def dilatedXiAmplitude (s r x : ℝ) : ℝ := xiAmplitude s (r * x)

/-- Its derivative. -/
def dilatedXiAmplitudeDeriv (s r x : ℝ) : ℝ := r * xiAmplitudeDeriv s (r * x)

theorem two_le_dilate {r x : ℝ} (hr : 2 ≤ r) (hx : 1 ≤ x) : (2 : ℝ) ≤ r * x := by nlinarith

theorem one_lt_dilate {r x : ℝ} (hr : 2 ≤ r) (hx : 1 ≤ x) : (1 : ℝ) < r * x :=
  lt_of_lt_of_le one_lt_two (two_le_dilate hr hx)

theorem hasDerivAt_dilatedXiAmplitude {s r x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hr : 2 ≤ r) (hx : 1 ≤ x) :
    HasDerivAt (dilatedXiAmplitude s r) (dilatedXiAmplitudeDeriv s r x) x := by
  have hlin : HasDerivAt (fun t : ℝ => r * t) r x := by
    simpa using (hasDerivAt_id x).const_mul r
  have h : HasDerivAt (fun t : ℝ => xiAmplitude s (r * t))
      (xiAmplitudeDeriv s (r * x) * r) x :=
    (hasDerivAt_xiAmplitude hs0 hs1 (one_lt_dilate hr hx)).comp x hlin
  have hval : xiAmplitudeDeriv s (r * x) * r = dilatedXiAmplitudeDeriv s r x := by
    unfold dilatedXiAmplitudeDeriv; ring
  rw [hval] at h
  exact h

theorem continuousOn_dilatedXiAmplitude {s r a b : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hr : 2 ≤ r) (ha : 1 ≤ a) :
    ContinuousOn (dilatedXiAmplitude s r) (Icc a b) := by
  refine (continuousOn_xiAmplitude hs0 hs1).comp
    (continuous_const.mul continuous_id).continuousOn ?_
  intro x hx
  exact one_lt_dilate hr (le_trans ha hx.1)

theorem continuousOn_dilatedXiAmplitudeDeriv {s r a b : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hr : 2 ≤ r) (ha : 1 ≤ a) :
    ContinuousOn (dilatedXiAmplitudeDeriv s r) (Icc a b) := by
  have h : ContinuousOn (fun x : ℝ => xiAmplitudeDeriv s (r * x)) (Icc a b) := by
    refine (continuousOn_xiAmplitudeDeriv hs0 hs1).comp
      (continuous_const.mul continuous_id).continuousOn ?_
    intro x hx
    exact one_lt_dilate hr (le_trans ha hx.1)
  exact continuousOn_const.mul h

theorem abs_dilatedXiAmplitude_le {s r x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hr : 2 ≤ r) (hx : 1 ≤ x) :
    |dilatedXiAmplitude s r x| ≤ 4 / Real.sqrt r / Real.sqrt x := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) hr
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hsr : (0 : ℝ) < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hbase := abs_xiAmplitude_le_four hs0 hs1 (two_le_dilate hr hx)
  have hsplit : Real.sqrt (r * x) = Real.sqrt r * Real.sqrt x := Real.sqrt_mul hr0.le x
  refine le_trans hbase (le_of_eq ?_)
  rw [hsplit]
  field_simp

theorem abs_dilatedXiAmplitudeDeriv_le {s r x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hr : 2 ≤ r) (hx : 1 ≤ x) :
    |dilatedXiAmplitudeDeriv s r x| ≤ 4 / Real.sqrt r / (x * Real.sqrt x) := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) hr
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hsr : (0 : ℝ) < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hbase := abs_xiAmplitudeDeriv_le hs0 hs1 (two_le_dilate hr hx)
  have hsplit : Real.sqrt (r * x) = Real.sqrt r * Real.sqrt x := Real.sqrt_mul hr0.le x
  have habs : |dilatedXiAmplitudeDeriv s r x| = r * |xiAmplitudeDeriv s (r * x)| := by
    unfold dilatedXiAmplitudeDeriv
    rw [abs_mul, abs_of_pos hr0]
  rw [habs]
  have hstep : r * |xiAmplitudeDeriv s (r * x)|
      ≤ r * (4 / (r * x * Real.sqrt (r * x))) :=
    mul_le_mul_of_nonneg_left hbase hr0.le
  refine le_trans hstep (le_of_eq ?_)
  rw [hsplit]
  field_simp

/-! ## A local composition lemma for symbol records -/

/-- **Building a symbol record by composition, with the amplitude bound needed only along the
phase.**  This is `symbolTwoBranch_of_composition` with `|P| ≤ K` required only at the points
`Φ x`, which is the form an interaction amplitude controlled by a Grönwall estimate on a finite
ray actually provides. -/
theorem symbolTwoBranch_of_composition_on {a b C C' K K' : ℝ}
    (ha : 1 ≤ a) (hC : 0 ≤ C) (hC' : 0 ≤ C') (hK' : 0 ≤ K')
    {A A' P P' Q Q' Φ Φ' : ℝ → ℝ}
    (hAd : ∀ x ∈ Icc a b, HasDerivAt A (A' x) x)
    (hPd : ∀ t, HasDerivAt P (P' t) t) (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hΦd : ∀ x ∈ Icc a b, HasDerivAt Φ (Φ' x) x)
    (hAc : ContinuousOn A (Icc a b)) (hA'c : ContinuousOn A' (Icc a b))
    (hPc : Continuous P) (hP'c : Continuous P') (hQc : Continuous Q) (hQ'c : Continuous Q')
    (hΦc : ContinuousOn Φ (Icc a b)) (hΦ'c : ContinuousOn Φ' (Icc a b))
    (hA : ∀ x ∈ Icc a b, |A x| ≤ C / Real.sqrt x)
    (hA'b : ∀ x ∈ Icc a b, |A' x| ≤ C' / (x * Real.sqrt x))
    (hPb : ∀ x ∈ Icc a b, |P (Φ x)| ≤ K) (hQb : ∀ x ∈ Icc a b, |Q (Φ x)| ≤ K)
    (hP'b : ∀ x ∈ Icc a b, |P' (Φ x) * Φ' x| ≤ K' / x ^ 2)
    (hQ'b : ∀ x ∈ Icc a b, |Q' (Φ x) * Φ' x| ≤ K' / x ^ 2) :
    SymbolTwoBranch a b (C * K) (C' * K + C * K')
      (fun x => A x * P (Φ x)) (fun x => A x * Q (Φ x))
      (fun x => A' x * P (Φ x) + A x * (P' (Φ x) * Φ' x))
      (fun x => A' x * Q (Φ x) + A x * (Q' (Φ x) * Φ' x)) := by
  have hxpos : ∀ x ∈ Icc a b, (0 : ℝ) < x := fun x hx => lt_of_lt_of_le zero_lt_one
    (le_trans ha hx.1)
  have hbound : ∀ (R R' : ℝ → ℝ), (∀ x ∈ Icc a b, |R (Φ x)| ≤ K) →
      (∀ x ∈ Icc a b, |R' (Φ x) * Φ' x| ≤ K' / x ^ 2) →
      (∀ x ∈ Icc a b, |A x * R (Φ x)| ≤ C * K / Real.sqrt x) ∧
      (∀ x ∈ Icc a b, |A' x * R (Φ x) + A x * (R' (Φ x) * Φ' x)|
        ≤ (C' * K + C * K') / (x * Real.sqrt x)) := by
    intro R R' hRb hR'b
    constructor
    · intro x hx
      have hx0 := hxpos x hx
      have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
      rw [abs_mul]
      calc |A x| * |R (Φ x)| ≤ (C / Real.sqrt x) * K :=
            mul_le_mul (hA x hx) (hRb x hx) (abs_nonneg _) (div_nonneg hC hs.le)
        _ = C * K / Real.sqrt x := by ring
    · intro x hx
      have hx0 := hxpos x hx
      have hx1 : (1 : ℝ) ≤ x := le_trans ha hx.1
      have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
      have h1 : |A' x * R (Φ x)| ≤ C' * K / (x * Real.sqrt x) := by
        rw [abs_mul]
        calc |A' x| * |R (Φ x)| ≤ (C' / (x * Real.sqrt x)) * K :=
              mul_le_mul (hA'b x hx) (hRb x hx) (abs_nonneg _)
                (div_nonneg hC' (by positivity))
          _ = C' * K / (x * Real.sqrt x) := by ring
      have h2 : |A x * (R' (Φ x) * Φ' x)| ≤ C * K' / (x * Real.sqrt x) := by
        rw [abs_mul]
        have hstep : |A x| * |R' (Φ x) * Φ' x| ≤ (C / Real.sqrt x) * (K' / x ^ 2) :=
          mul_le_mul (hA x hx) (hR'b x hx) (abs_nonneg _) (div_nonneg hC hs.le)
        have hval : (C / Real.sqrt x) * (K' / x ^ 2) = C * K' / (x ^ 2 * Real.sqrt x) := by
          ring
        have hmono : C * K' / (x ^ 2 * Real.sqrt x) ≤ C * K' / (x * Real.sqrt x) := by
          refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
          have hxx : x ≤ x ^ 2 := by nlinarith
          nlinarith [hs, hxx]
        rw [hval] at hstep
        exact hstep.trans hmono
      have hsum : C' * K / (x * Real.sqrt x) + C * K' / (x * Real.sqrt x)
          = (C' * K + C * K') / (x * Real.sqrt x) := by ring
      calc |A' x * R (Φ x) + A x * (R' (Φ x) * Φ' x)|
          ≤ |A' x * R (Φ x)| + |A x * (R' (Φ x) * Φ' x)| := abs_add_le _ _
        _ ≤ C' * K / (x * Real.sqrt x) + C * K' / (x * Real.sqrt x) := add_le_add h1 h2
        _ = (C' * K + C * K') / (x * Real.sqrt x) := hsum
  obtain ⟨hPval, hPder⟩ := hbound P P' hPb hP'b
  obtain ⟨hQval, hQder⟩ := hbound Q Q' hQb hQ'b
  refine ⟨fun x hx => (hAd x hx).mul ((hPd (Φ x)).comp x (hΦd x hx)),
    fun x hx => (hAd x hx).mul ((hQd (Φ x)).comp x (hΦd x hx)),
    hAc.mul (hPc.comp_continuousOn hΦc), ?_, hAc.mul (hQc.comp_continuousOn hΦc), ?_,
    hPval, hPder, hQval, hQder⟩
  · exact (hA'c.mul (hPc.comp_continuousOn hΦc)).add
      (hAc.mul ((hP'c.comp_continuousOn hΦc).mul hΦ'c))
  · exact (hA'c.mul (hQc.comp_continuousOn hΦc)).add
      (hAc.mul ((hQ'c.comp_continuousOn hΦc).mul hΦ'c))

/-! ## The transported amplitude derivatives -/

/-- The exact derivative of the cosine amplitude, from the transport law. -/
def radialAmpCosDeriv (c : ℝ) (W psi : ℝ → ℂ) (t : ℝ) : ℝ :=
  2 * (Complex.exp (-Complex.I * (c : ℂ) * (t : ℂ)) * psi t * W t
    / (2 * Complex.I * (c : ℂ))).re

/-- The exact derivative of the sine amplitude. -/
def radialAmpSinDeriv (c : ℝ) (W psi : ℝ → ℂ) (t : ℝ) : ℝ :=
  -(2 * (Complex.exp (-Complex.I * (c : ℂ) * (t : ℂ)) * psi t * W t
    / (2 * Complex.I * (c : ℂ))).im)

theorem continuous_transportKernel {c : ℝ} {W psi : ℝ → ℂ}
    (hWc : Continuous W) (hpsic : Continuous psi) :
    Continuous fun t : ℝ => Complex.exp (-Complex.I * (c : ℂ) * (t : ℂ)) * psi t * W t
      / (2 * Complex.I * (c : ℂ)) := by
  have h1 : Continuous fun t : ℝ => Complex.exp (-Complex.I * (c : ℂ) * (t : ℂ)) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  exact ((h1.mul hpsic).mul hWc).div_const _

theorem continuous_radialAmpCosDeriv {c : ℝ} {W psi : ℝ → ℂ}
    (hWc : Continuous W) (hpsic : Continuous psi) :
    Continuous (radialAmpCosDeriv c W psi) :=
  (Complex.continuous_re.comp (continuous_transportKernel hWc hpsic)).const_mul 2

theorem continuous_radialAmpSinDeriv {c : ℝ} {W psi : ℝ → ℂ}
    (hWc : Continuous W) (hpsic : Continuous psi) :
    Continuous (radialAmpSinDeriv c W psi) :=
  ((Complex.continuous_im.comp (continuous_transportKernel hWc hpsic)).const_mul 2).neg

/-! ## The instantiation -/

/-- **The symbol record of the actual exterior radial solutions.**  The dilated Liouville amplitude
`A_s(rx)` times the interaction amplitudes evaluated at the dilated phase `ξ_s(rx)` is a half-power
symbol pair with the explicit constants `(4/√r)K` and `(4/√r)K + (4/√r)K'`. -/
theorem symbolTwoBranch_radialPSWF
    {s r a b c K K' : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 2 ≤ r)
    (ha : 1 ≤ a) (hc : 0 < c) (hK' : 0 ≤ K')
    {W V psi : ℝ → ℂ}
    (hW : ∀ x, HasDerivAt W (V x) x)
    (hV : ∀ x, HasDerivAt V ((psi x - (c : ℂ) ^ 2) * W x) x)
    (hWc : Continuous W) (hpsic : Continuous psi)
    (hPb : ∀ x ∈ Icc a b, |radialAmpCos c W V (dilatedRadialPhase s r x)| ≤ K)
    (hQb : ∀ x ∈ Icc a b, |radialAmpSin c W V (dilatedRadialPhase s r x)| ≤ K)
    (hP'b : ∀ x ∈ Icc a b,
      |radialAmpCosDeriv c W psi (dilatedRadialPhase s r x) * dilatedPhaseSpeed s r x|
        ≤ K' / x ^ 2)
    (hQ'b : ∀ x ∈ Icc a b,
      |radialAmpSinDeriv c W psi (dilatedRadialPhase s r x) * dilatedPhaseSpeed s r x|
        ≤ K' / x ^ 2) :
    SymbolTwoBranch a b (4 / Real.sqrt r * K) (4 / Real.sqrt r * K + 4 / Real.sqrt r * K')
      (fun x => dilatedXiAmplitude s r x * radialAmpCos c W V (dilatedRadialPhase s r x))
      (fun x => dilatedXiAmplitude s r x * radialAmpSin c W V (dilatedRadialPhase s r x))
      (fun x => dilatedXiAmplitudeDeriv s r x * radialAmpCos c W V (dilatedRadialPhase s r x)
        + dilatedXiAmplitude s r x
          * (radialAmpCosDeriv c W psi (dilatedRadialPhase s r x) * dilatedPhaseSpeed s r x))
      (fun x => dilatedXiAmplitudeDeriv s r x * radialAmpSin c W V (dilatedRadialPhase s r x)
        + dilatedXiAmplitude s r x
          * (radialAmpSinDeriv c W psi (dilatedRadialPhase s r x) * dilatedPhaseSpeed s r x)) := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) hr
  have hsr : (0 : ℝ) < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hC : (0 : ℝ) ≤ 4 / Real.sqrt r := by positivity
  have hΦd : ∀ x ∈ Icc a b, HasDerivAt (dilatedRadialPhase s r) (dilatedPhaseSpeed s r x) x :=
    fun x hx => hasDerivAt_dilatedRadialPhase hs0 (one_lt_dilate hr (le_trans ha hx.1))
  have hΦc : ContinuousOn (dilatedRadialPhase s r) (Icc a b) :=
    fun x hx => ((hΦd x hx).continuousAt).continuousWithinAt
  exact symbolTwoBranch_of_composition_on ha hC hC hK'
    (fun x hx => hasDerivAt_dilatedXiAmplitude hs0 hs1 hr (le_trans ha hx.1))
    (fun t => hasDerivAt_radialAmpCos hc.ne' (hW t) (hV t))
    (fun t => hasDerivAt_radialAmpSin hc.ne' (hW t) (hV t))
    hΦd
    (continuousOn_dilatedXiAmplitude hs0 hs1 hr ha)
    (continuousOn_dilatedXiAmplitudeDeriv hs0 hs1 hr ha)
    ((Complex.continuous_re.comp (continuous_radialInteractionPlus hc hW hV)).const_mul 2)
    (continuous_radialAmpCosDeriv hWc hpsic)
    (((Complex.continuous_im.comp (continuous_radialInteractionPlus hc hW hV)).const_mul 2).neg)
    (continuous_radialAmpSinDeriv hWc hpsic)
    hΦc (continuousOn_dilatedPhaseSpeed hr ha)
    (fun x hx => abs_dilatedXiAmplitude_le hs0 hs1 hr (le_trans ha hx.1))
    (fun x hx => abs_dilatedXiAmplitudeDeriv_le hs0 hs1 hr (le_trans ha hx.1))
    hPb hQb hP'b hQ'b

/-! ## Discharging the amplitude hypotheses -/

/-- The interaction amplitudes are bounded by the total, hence by the Grönwall envelope. -/
theorem abs_radialAmp_le_total (c : ℝ) (W V : ℝ → ℂ) (t : ℝ) :
    |radialAmpCos c W V t| ≤ 2 * radialInteractionTotal c W V t
      ∧ |radialAmpSin c W V t| ≤ 2 * radialInteractionTotal c W V t := by
  have hle : ‖radialInteractionPlus c W V t‖ ≤ radialInteractionTotal c W V t := by
    unfold radialInteractionTotal
    have := norm_nonneg (radialInteractionMinus c W V t)
    linarith
  constructor
  · exact (abs_radialAmpCos_le c W V t).trans (by linarith)
  · exact (abs_radialAmpSin_le c W V t).trans (by linarith)

/-- **The symbol record with the amplitude hypotheses discharged.**  A uniform bound `Kt` on the
interaction total along the phase, together with the potential's `κ/x²` symbol decay, produces the
record with `K = 2 Kt` and `K' = κ·Kt·(4r/3)/c`. -/
theorem symbolTwoBranch_radialPSWF_of_bounds
    {s r a b c κ Kt : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 2 ≤ r)
    (ha : 1 ≤ a) (hc : 0 < c) (hκ : 0 ≤ κ) (hKt : 0 ≤ Kt)
    {W V psi : ℝ → ℂ}
    (hW : ∀ x, HasDerivAt W (V x) x)
    (hV : ∀ x, HasDerivAt V ((psi x - (c : ℂ) ^ 2) * W x) x)
    (hWc : Continuous W) (hpsic : Continuous psi)
    (hAmp : ∀ x ∈ Icc a b, radialInteractionTotal c W V (dilatedRadialPhase s r x) ≤ Kt)
    (hDecay : ∀ x ∈ Icc a b, ‖psi (dilatedRadialPhase s r x)‖ ≤ κ / x ^ 2) :
    SymbolTwoBranch a b (4 / Real.sqrt r * (2 * Kt))
      (4 / Real.sqrt r * (2 * Kt) + 4 / Real.sqrt r * (κ * Kt * (4 / 3 * r) / c))
      (fun x => dilatedXiAmplitude s r x * radialAmpCos c W V (dilatedRadialPhase s r x))
      (fun x => dilatedXiAmplitude s r x * radialAmpSin c W V (dilatedRadialPhase s r x))
      (fun x => dilatedXiAmplitudeDeriv s r x * radialAmpCos c W V (dilatedRadialPhase s r x)
        + dilatedXiAmplitude s r x
          * (radialAmpCosDeriv c W psi (dilatedRadialPhase s r x) * dilatedPhaseSpeed s r x))
      (fun x => dilatedXiAmplitudeDeriv s r x * radialAmpSin c W V (dilatedRadialPhase s r x)
        + dilatedXiAmplitude s r x
          * (radialAmpSinDeriv c W psi (dilatedRadialPhase s r x) * dilatedPhaseSpeed s r x)) := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) hr
  have hWb : ∀ x ∈ Icc a b, ‖W (dilatedRadialPhase s r x)‖ ≤ Kt := by
    intro x hx
    exact le_trans (norm_le_radialInteractionTotal hc.ne' W V _) (hAmp x hx)
  have hspeed : ∀ x ∈ Icc a b, |dilatedPhaseSpeed s r x| ≤ 4 / 3 * r := by
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := le_trans ha hx.1
    have hlow : r ≤ dilatedPhaseSpeed s r x := le_dilatedPhaseSpeed hs1 hr hx1
    have hup : dilatedPhaseSpeed s r x ≤ 4 / 3 * r := dilatedPhaseSpeed_le hs0 hr hx1
    rw [abs_of_nonneg (le_trans hr0.le hlow)]
    exact hup
  refine symbolTwoBranch_radialPSWF hs0 hs1 hr ha hc (by positivity) hW hV hWc hpsic
    (fun x hx => le_trans (abs_radialAmp_le_total c W V _).1 (by linarith [hAmp x hx]))
    (fun x hx => le_trans (abs_radialAmp_le_total c W V _).2 (by linarith [hAmp x hx]))
    (fun x hx => ?_) (fun x hx => ?_)
  · have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one (le_trans ha hx.1)
    exact abs_transport_deriv_comp_le hc hκ hKt hx0 (hDecay x hx) (hWb x hx) (hspeed x hx)
  · have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one (le_trans ha hx.1)
    have hbase := abs_transport_deriv_im_le hc psi W (dilatedRadialPhase s r x)
    have hmul : ‖psi (dilatedRadialPhase s r x)‖ * ‖W (dilatedRadialPhase s r x)‖
        ≤ (κ / x ^ 2) * Kt :=
      mul_le_mul (hDecay x hx) (hWb x hx) (norm_nonneg _) (by positivity)
    rw [radialAmpSinDeriv, abs_mul]
    have hstep : |(-(2 * (Complex.exp (-Complex.I * (c : ℂ)
          * ((dilatedRadialPhase s r x : ℝ) : ℂ)) * psi (dilatedRadialPhase s r x)
          * W (dilatedRadialPhase s r x) / (2 * Complex.I * (c : ℂ))).im))|
        * |dilatedPhaseSpeed s r x| ≤ ((κ / x ^ 2) * Kt / c) * (4 / 3 * r) := by
      refine mul_le_mul ?_ (hspeed x hx) (abs_nonneg _) (by positivity)
      refine hbase.trans ?_
      gcongr
    have hval : ((κ / x ^ 2) * Kt / c) * (4 / 3 * r)
        = (κ * Kt * (4 / 3 * r) / c) / x ^ 2 := by
      field_simp
    linarith [hstep, hval.le, hval.ge]

/-! ## The off-diagonal entry estimate for the actual solutions -/

/-- **Equation (8) for the actual exterior radial solutions.**  Two dilates of a genuine solution of
the exterior normal form, with the interaction total bounded by `Kt` along each dilated phase and
the potential a `κ/x²` symbol, satisfy the off-diagonal estimate with every constant explicit and
uniform in the radius, the turning parameter and both indices. -/
theorem abs_integral_radial_entry_le
    {s j k a b c κ Kt : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hk2 : 2 ≤ k) (hkj : k < j) (ha : 1 ≤ a) (hab : a ≤ b) (hc : 0 < c)
    (hκ : 0 ≤ κ) (hKt : 0 ≤ Kt)
    {W V psi : ℝ → ℂ}
    (hW : ∀ x, HasDerivAt W (V x) x)
    (hV : ∀ x, HasDerivAt V ((psi x - (c : ℂ) ^ 2) * W x) x)
    (hWc : Continuous W) (hpsic : Continuous psi)
    (hAmpJ : ∀ x ∈ Icc a b, radialInteractionTotal c W V (dilatedRadialPhase s j x) ≤ Kt)
    (hAmpK : ∀ x ∈ Icc a b, radialInteractionTotal c W V (dilatedRadialPhase s k x) ≤ Kt)
    (hDecayJ : ∀ x ∈ Icc a b, ‖psi (dilatedRadialPhase s j x)‖ ≤ κ / x ^ 2)
    (hDecayK : ∀ x ∈ Icc a b, ‖psi (dilatedRadialPhase s k x)‖ ≤ κ / x ^ 2) :
    |∫ x in a..b,
        (dilatedXiAmplitude s j x * radialAmpCos c W V (dilatedRadialPhase s j x)
              * Real.cos (c * dilatedRadialPhase s j x)
            + dilatedXiAmplitude s j x * radialAmpSin c W V (dilatedRadialPhase s j x)
              * Real.sin (c * dilatedRadialPhase s j x))
          * (dilatedXiAmplitude s k x * radialAmpCos c W V (dilatedRadialPhase s k x)
              * Real.cos (c * dilatedRadialPhase s k x)
            + dilatedXiAmplitude s k x * radialAmpSin c W V (dilatedRadialPhase s k x)
              * Real.sin (c * dilatedRadialPhase s k x))|
      ≤ 4 * (2 * (4 / Real.sqrt j * (2 * Kt) * (4 / Real.sqrt k * (2 * Kt)))
              / (2 / 3 * (j - k))
          + ((4 / Real.sqrt j * (2 * Kt) + 4 / Real.sqrt j * (κ * Kt * (4 / 3 * j) / c))
                * (4 / Real.sqrt k * (2 * Kt))
              + 4 / Real.sqrt j * (2 * Kt)
                * (4 / Real.sqrt k * (2 * Kt) + 4 / Real.sqrt k * (κ * Kt * (4 / 3 * k) / c)))
            / (2 / 3 * (j - k))
          + (4 / Real.sqrt j * (2 * Kt) * (4 / Real.sqrt k * (2 * Kt))) * (16 / 9)
            / (3 * (2 / 3 * (j - k)) ^ 2)) / c := by
  have hjge : (2 : ℝ) ≤ j := le_trans hk2 hkj.le
  have hj0 : (0 : ℝ) < j := lt_of_lt_of_le (by norm_num) hjge
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (by norm_num) hk2
  have hsj : (0 : ℝ) < Real.sqrt j := Real.sqrt_pos.mpr hj0
  have hsk : (0 : ℝ) < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hrecJ := symbolTwoBranch_radialPSWF_of_bounds hs0 hs1 hjge ha hc hκ hKt hW hV hWc hpsic
    hAmpJ hDecayJ
  have hrecK := symbolTwoBranch_radialPSWF_of_bounds hs0 hs1 hk2 ha hc hκ hKt hW hV hWc hpsic
    hAmpK hDecayK
  exact abs_integral_radial_twoBranch_symbol_le' hs0 hs1 hk2 hkj ha hab hc
    (by positivity) (by positivity) (by positivity) (by positivity) hrecJ hrecK

end GaloisForLFunctions.RHTower

end
