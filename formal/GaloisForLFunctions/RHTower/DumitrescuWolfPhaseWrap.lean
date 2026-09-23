import GaloisForLFunctions.HTGeometry.HausdorffCDDPhaseKernel
import GaloisForLFunctions.HTGeometry.HarmonicOrdinateDivergence
import GaloisForLFunctions.HTGeometry.TangentPhaseWrapObstruction

/-!
# The paired vertical Riccati channels cannot be quantised at their endpoints

Fix `1/2 < α < β < 1` and `T > 0`, put

```
A = (α - 1/2)(β - 1/2) > 0,      c = β - α > 0,
```

and let `γ : ℕ → ℝ` be the positive ordinates used to quantise the vertical zero contribution.
The two channels carry the increments

```
h₋ k = c (γ k - T) / (A + (γ k - T)²),      h₊ k = -c (T + γ k) / (A + (T + γ k)²),
```

each fed into the tangent-addition recurrence `F 0 = 0`,
`F (k+1) = (F k + h k)/(1 - F k · h k)`.

This module proves:

* both channels vanish in the deep-ordinate limit, the lower one positively and the upper one
  negatively;
* each channel dominates a fixed multiple of `1/γ k` in absolute value once the ordinate is large,
  so a divergent harmonic ordinate sum forces the accumulated arctangent phases to `+∞` and `-∞`;
* consequently neither recurrence can reach its asserted endpoint: the lower iteration does not
  tend to `+∞` and the upper one does not tend to `-∞`; each returns to zero along a subsequence.

The obstruction is the phase-wrap theorem of
`GaloisForLFunctions.HTGeometry.TangentPhaseWrapObstruction`.  The only arithmetic input is
divergence of `∑ 1/γ k`, which for the ordinates of the nontrivial zeros is the
Riemann--von Mangoldt counting law.
-/

open Filter Topology GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The quadratic offset `A = (α - 1/2)(β - 1/2)` of the paired vertical channel. -/
def verticalChannelOffset (α β : ℝ) : ℝ := (α - 1 / 2) * (β - 1 / 2)

/-- The abscissa gap `c = β - α` of the paired vertical channel. -/
def verticalChannelGap (α β : ℝ) : ℝ := β - α

/-- The incoming (`γ - T`) channel increment `h₋ k = c (γ k - T)/(A + (γ k - T)²)`. -/
def verticalLowerIncrement (α β T : ℝ) (γ : ℕ → ℝ) (k : ℕ) : ℝ :=
  verticalChannelGap α β * (γ k - T) / (verticalChannelOffset α β + (γ k - T) ^ (2 : ℕ))

/-- The outgoing (`T + γ`) channel increment `h₊ k = -c (T + γ k)/(A + (T + γ k)²)`. -/
def verticalUpperIncrement (α β T : ℝ) (γ : ℕ → ℝ) (k : ℕ) : ℝ :=
  -(verticalChannelGap α β * (T + γ k)) / (verticalChannelOffset α β + (T + γ k) ^ (2 : ℕ))

variable {α β T : ℝ} {γ : ℕ → ℝ}

theorem verticalChannelOffset_pos (hα : 1 / 2 < α) (hαβ : α < β) :
    0 < verticalChannelOffset α β := by
  have h1 : 0 < α - 1 / 2 := by linarith
  have h2 : 0 < β - 1 / 2 := by linarith
  exact mul_pos h1 h2

theorem verticalChannelGap_pos (hαβ : α < β) : 0 < verticalChannelGap α β := by
  simp only [verticalChannelGap]
  linarith

/-! ## Elementary channel estimates -/

/-- A Cauchy-type channel term is bounded by `c/x`. -/
theorem abs_channelTerm_le {A c x : ℝ} (hA : 0 < A) (hc : 0 < c) (hx : 0 < x) :
    |c * x / (A + x ^ (2 : ℕ))| ≤ c / x := by
  have hden : 0 < A + x ^ (2 : ℕ) := by positivity
  rw [abs_of_nonneg (by positivity)]
  rw [div_le_div_iff₀ hden hx]
  nlinarith [hA, hx.le, sq_nonneg x]

/-- A Cauchy-type channel term is at least `c/(4 y)` once `y/2 ≤ x ≤ y` and `A ≤ y²`. -/
theorem channelTerm_ge {A c x y : ℝ} (hA : 0 < A) (hc : 0 < c) (hy : 0 < y)
    (hAy : A ≤ y ^ (2 : ℕ)) (hlow : y / 2 ≤ x) (hhigh : x ≤ y) :
    c / (4 * y) ≤ c * x / (A + x ^ (2 : ℕ)) := by
  have hx : 0 < x := by linarith
  have hden : 0 < A + x ^ (2 : ℕ) := by positivity
  have hx2 : x ^ (2 : ℕ) ≤ y ^ (2 : ℕ) := by nlinarith
  have hxy : 2 * y ^ (2 : ℕ) ≤ 4 * x * y := by nlinarith
  rw [div_le_div_iff₀ (by positivity) hden]
  nlinarith [hc.le, hAy, hx2, hxy]

/-! ## Signs and limits of the two channels -/

theorem verticalLowerIncrement_pos (hα : 1 / 2 < α) (hαβ : α < β)
    {k : ℕ} (hk : T < γ k) :
    0 < verticalLowerIncrement α β T γ k := by
  have hA := verticalChannelOffset_pos hα hαβ
  have hc := verticalChannelGap_pos hαβ
  have hx : 0 < γ k - T := by linarith
  simp only [verticalLowerIncrement]
  positivity

theorem verticalUpperIncrement_neg (hα : 1 / 2 < α) (hαβ : α < β)
    (hT : 0 < T) {k : ℕ} (hk : 0 < γ k) :
    verticalUpperIncrement α β T γ k < 0 := by
  have hA := verticalChannelOffset_pos hα hαβ
  have hc := verticalChannelGap_pos hαβ
  have hx : 0 < T + γ k := by linarith
  have hden : 0 < verticalChannelOffset α β + (T + γ k) ^ (2 : ℕ) := by positivity
  simp only [verticalUpperIncrement]
  apply div_neg_of_neg_of_pos _ hden
  nlinarith

theorem tendsto_verticalLowerIncrement (hα : 1 / 2 < α) (hαβ : α < β)
    (hγ : Tendsto γ atTop atTop) :
    Tendsto (verticalLowerIncrement α β T γ) atTop (𝓝 0) := by
  have hA := verticalChannelOffset_pos hα hαβ
  have hc := verticalChannelGap_pos hαβ
  have hshift : Tendsto (fun k => γ k - T) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-T) hγ
  refine squeeze_zero_norm' (a := fun k => verticalChannelGap α β / (γ k - T)) ?_ ?_
  · filter_upwards [hshift.eventually_gt_atTop 0] with k hk
    rw [Real.norm_eq_abs]
    exact abs_channelTerm_le hA hc hk
  · have hinv : Tendsto (fun k => (γ k - T)⁻¹) atTop (𝓝 0) := hshift.inv_tendsto_atTop
    have hmul := hinv.const_mul (verticalChannelGap α β)
    simpa [div_eq_mul_inv] using hmul

theorem tendsto_verticalUpperIncrement (hα : 1 / 2 < α) (hαβ : α < β)
    (hγ : Tendsto γ atTop atTop) :
    Tendsto (verticalUpperIncrement α β T γ) atTop (𝓝 0) := by
  have hA := verticalChannelOffset_pos hα hαβ
  have hc := verticalChannelGap_pos hαβ
  have hshift : Tendsto (fun k => T + γ k) atTop atTop :=
    tendsto_atTop_add_const_left atTop T hγ
  refine squeeze_zero_norm' (a := fun k => verticalChannelGap α β / (T + γ k)) ?_ ?_
  · filter_upwards [hshift.eventually_gt_atTop 0] with k hk
    have hbound := abs_channelTerm_le (A := verticalChannelOffset α β)
      (c := verticalChannelGap α β) (x := T + γ k) hA hc hk
    rw [Real.norm_eq_abs]
    simpa [verticalUpperIncrement, abs_div, abs_neg] using hbound
  · have hinv : Tendsto (fun k => (T + γ k)⁻¹) atTop (𝓝 0) := hshift.inv_tendsto_atTop
    have hmul := hinv.const_mul (verticalChannelGap α β)
    simpa [div_eq_mul_inv] using hmul

/-! ## Harmonic minorants -/

/-- Once `γ k ≥ 2T` and `A ≤ γ k²` the lower channel dominates `c/(4 γ k)`. -/
theorem verticalLowerIncrement_ge (hα : 1 / 2 < α) (hαβ : α < β) (hT : 0 < T)
    {k : ℕ} (hk : 2 * T ≤ γ k) (hAk : verticalChannelOffset α β ≤ γ k ^ (2 : ℕ)) :
    verticalChannelGap α β / (4 * γ k) ≤ verticalLowerIncrement α β T γ k := by
  have hA := verticalChannelOffset_pos hα hαβ
  have hc := verticalChannelGap_pos hαβ
  have hγpos : 0 < γ k := by linarith
  exact channelTerm_ge hA hc hγpos hAk (by linarith) (by linarith)

/-- Once `γ k ≥ T` and `A ≤ γ k²` the negated upper channel dominates `c/(8 γ k)`. -/
theorem neg_verticalUpperIncrement_ge (hα : 1 / 2 < α) (hαβ : α < β) (hT : 0 < T)
    {k : ℕ} (hk : T ≤ γ k) (hAk : verticalChannelOffset α β ≤ γ k ^ (2 : ℕ)) :
    verticalChannelGap α β / (8 * γ k) ≤ -verticalUpperIncrement α β T γ k := by
  have hA := verticalChannelOffset_pos hα hαβ
  have hc := verticalChannelGap_pos hαβ
  have hγpos : 0 < γ k := by linarith
  have hneg : -verticalUpperIncrement α β T γ k
      = verticalChannelGap α β * (T + γ k)
        / (verticalChannelOffset α β + (T + γ k) ^ (2 : ℕ)) := by
    simp only [verticalUpperIncrement, neg_div, neg_neg]
  have hAk2 : verticalChannelOffset α β ≤ (2 * γ k) ^ (2 : ℕ) := by nlinarith
  have hstep := channelTerm_ge (A := verticalChannelOffset α β) (c := verticalChannelGap α β)
    (x := T + γ k) (y := 2 * γ k) hA hc (by linarith) hAk2 (by linarith) (by linarith)
  rw [hneg]
  calc verticalChannelGap α β / (8 * γ k)
      = verticalChannelGap α β / (4 * (2 * γ k)) := by ring_nf
    _ ≤ _ := hstep

/-! ## Divergence of the accumulated phases -/

/-- Divergence of the harmonic ordinate sum forces the lower accumulated arctangent phase to
`+∞`. -/
theorem tendsto_arctanPartialSum_verticalLower
    (hα : 1 / 2 < α) (hαβ : α < β) (hT : 0 < T)
    (hγpos : ∀ k, 0 < γ k) (hγ : Tendsto γ atTop atTop)
    (hharm : Tendsto (fun N => ∑ k ∈ Finset.range N, (γ k)⁻¹) atTop atTop) :
    Tendsto (arctanPartialSum (verticalLowerIncrement α β T γ)) atTop atTop := by
  have hA := verticalChannelOffset_pos hα hαβ
  have hc := verticalChannelGap_pos hαβ
  have hzero := tendsto_verticalLowerIncrement (T := T) hα hαβ hγ
  have hev : ∀ᶠ k in atTop, verticalChannelGap α β / 8 * (γ k)⁻¹
      ≤ Real.arctan (verticalLowerIncrement α β T γ k) := by
    filter_upwards [hγ.eventually_ge_atTop (2 * T),
      hγ.eventually_ge_atTop (Real.sqrt (verticalChannelOffset α β)),
      hzero.eventually_lt_const (by norm_num : (0:ℝ) < 1)] with k hk1 hk2 hk3
    have hγk : 0 < γ k := hγpos k
    have hAk : verticalChannelOffset α β ≤ γ k ^ (2 : ℕ) := by
      have hs : Real.sqrt (verticalChannelOffset α β) ^ (2 : ℕ) = verticalChannelOffset α β :=
        Real.sq_sqrt hA.le
      nlinarith [Real.sqrt_nonneg (verticalChannelOffset α β)]
    have hlow := verticalLowerIncrement_ge hα hαβ hT hk1 hAk
    have hposk : 0 ≤ verticalLowerIncrement α β T γ k := by
      have : 0 < verticalChannelGap α β / (4 * γ k) := by positivity
      linarith
    have harc : verticalLowerIncrement α β T γ k / 2
        ≤ Real.arctan (verticalLowerIncrement α β T γ k) := by
      have hcube := sub_arctan_le_cube_div_three hposk
      have hx2 : verticalLowerIncrement α β T γ k ^ (2 : ℕ) ≤ 1 := by nlinarith [hposk, hk3.le]
      have hx3 : verticalLowerIncrement α β T γ k ^ (3 : ℕ) ≤ verticalLowerIncrement α β T γ k := by
        nlinarith [mul_nonneg hposk (sub_nonneg.mpr hx2)]
      linarith
    have hhalf : verticalChannelGap α β / 8 * (γ k)⁻¹
        = (verticalChannelGap α β / (4 * γ k)) / 2 := by
      field_simp
      ring
    rw [hhalf]
    linarith
  refine tendsto_arctanPartialSum_atTop_of_eventually_ge hev ?_
  have hmul := hharm.const_mul_atTop (by positivity : (0:ℝ) < verticalChannelGap α β / 8)
  exact hmul.congr fun N => Finset.mul_sum _ _ _

/-- Divergence of the harmonic ordinate sum forces the upper accumulated arctangent phase to
`-∞`. -/
theorem tendsto_arctanPartialSum_verticalUpper
    (hα : 1 / 2 < α) (hαβ : α < β) (hT : 0 < T)
    (hγpos : ∀ k, 0 < γ k) (hγ : Tendsto γ atTop atTop)
    (hharm : Tendsto (fun N => ∑ k ∈ Finset.range N, (γ k)⁻¹) atTop atTop) :
    Tendsto (arctanPartialSum (verticalUpperIncrement α β T γ)) atTop atBot := by
  have hA := verticalChannelOffset_pos hα hαβ
  have hc := verticalChannelGap_pos hαβ
  have hzero := tendsto_verticalUpperIncrement (T := T) hα hαβ hγ
  have hzeroneg : Tendsto (fun k => -verticalUpperIncrement α β T γ k) atTop (𝓝 0) := by
    simpa using hzero.neg
  have hev : ∀ᶠ k in atTop, Real.arctan (verticalUpperIncrement α β T γ k)
      ≤ -(verticalChannelGap α β / 16) * (γ k)⁻¹ := by
    filter_upwards [hγ.eventually_ge_atTop T,
      hγ.eventually_ge_atTop (Real.sqrt (verticalChannelOffset α β)),
      hzeroneg.eventually_lt_const (by norm_num : (0:ℝ) < 1)] with k hk1 hk2 hk3
    have hγk : 0 < γ k := hγpos k
    have hAk : verticalChannelOffset α β ≤ γ k ^ (2 : ℕ) := by
      have hs : Real.sqrt (verticalChannelOffset α β) ^ (2 : ℕ) = verticalChannelOffset α β :=
        Real.sq_sqrt hA.le
      nlinarith [Real.sqrt_nonneg (verticalChannelOffset α β)]
    have hlow := neg_verticalUpperIncrement_ge hα hαβ hT hk1 hAk
    have hposk : 0 ≤ -verticalUpperIncrement α β T γ k := by
      have : 0 < verticalChannelGap α β / (8 * γ k) := by positivity
      linarith
    have hle1 : -verticalUpperIncrement α β T γ k ≤ 1 := by
      simpa using hk3.le
    have harc : (-verticalUpperIncrement α β T γ k) / 2
        ≤ Real.arctan (-verticalUpperIncrement α β T γ k) := by
      have hcube := sub_arctan_le_cube_div_three hposk
      have hy2 : (-verticalUpperIncrement α β T γ k) ^ (2 : ℕ) ≤ 1 := by nlinarith [hposk, hle1]
      have hy3 : (-verticalUpperIncrement α β T γ k) ^ (3 : ℕ)
          ≤ -verticalUpperIncrement α β T γ k := by
        nlinarith [mul_nonneg hposk (sub_nonneg.mpr hy2)]
      linarith
    have hhalf : verticalChannelGap α β / 16 * (γ k)⁻¹
        = (verticalChannelGap α β / (8 * γ k)) / 2 := by
      field_simp
      ring
    have hneg : Real.arctan (-verticalUpperIncrement α β T γ k)
        = -Real.arctan (verticalUpperIncrement α β T γ k) := Real.arctan_neg _
    rw [hneg] at harc
    have : verticalChannelGap α β / 16 * (γ k)⁻¹
        ≤ -Real.arctan (verticalUpperIncrement α β T γ k) := by
      rw [hhalf]; linarith
    linarith
  refine tendsto_arctanPartialSum_atBot_of_eventually_le hev ?_
  have hmul := hharm.const_mul_atTop (by positivity : (0:ℝ) < verticalChannelGap α β / 16)
  have hpos : Tendsto (fun N => ∑ k ∈ Finset.range N,
      verticalChannelGap α β / 16 * (γ k)⁻¹) atTop atTop :=
    hmul.congr fun N => Finset.mul_sum _ _ _
  have hneg := tendsto_neg_atBot_iff (f := fun N => ∑ k ∈ Finset.range N,
    verticalChannelGap α β / 16 * (γ k)⁻¹) |>.mpr hpos
  refine hneg.congr fun N => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ## The endpoint obstruction -/

/-- **The incoming channel cannot reach `+∞`.**  It returns to zero along a subsequence. -/
theorem not_tendsto_atTop_verticalLowerRiccati
    (hα : 1 / 2 < α) (hαβ : α < β) (hT : 0 < T)
    (hγpos : ∀ k, 0 < γ k) (hγ : Tendsto γ atTop atTop)
    (hharm : Tendsto (fun N => ∑ k ∈ Finset.range N, (γ k)⁻¹) atTop atTop)
    (hden : ∀ k, 1 - tangentIterate (verticalLowerIncrement α β T γ) k
      * verticalLowerIncrement α β T γ k ≠ 0) :
    ¬ Tendsto (tangentIterate (verticalLowerIncrement α β T γ)) atTop atTop :=
  not_tendsto_atTop_tangentIterate
    (tendsto_verticalLowerIncrement hα hαβ hγ)
    (tendsto_arctanPartialSum_verticalLower hα hαβ hT hγpos hγ hharm) hden

/-- **The outgoing channel cannot reach `-∞`.**  It returns to zero along a subsequence. -/
theorem not_tendsto_atBot_verticalUpperRiccati
    (hα : 1 / 2 < α) (hαβ : α < β) (hT : 0 < T)
    (hγpos : ∀ k, 0 < γ k) (hγ : Tendsto γ atTop atTop)
    (hharm : Tendsto (fun N => ∑ k ∈ Finset.range N, (γ k)⁻¹) atTop atTop)
    (hden : ∀ k, 1 - tangentIterate (verticalUpperIncrement α β T γ) k
      * verticalUpperIncrement α β T γ k ≠ 0) :
    ¬ Tendsto (tangentIterate (verticalUpperIncrement α β T γ)) atTop atBot :=
  not_tendsto_atBot_tangentIterate
    (tendsto_verticalUpperIncrement hα hαβ hγ)
    (tendsto_arctanPartialSum_verticalUpper hα hαβ hT hγpos hγ hharm) hden

/-- **Recurrent return of the incoming channel.** -/
theorem exists_subseq_verticalLowerRiccati_tendsto_zero
    (hα : 1 / 2 < α) (hαβ : α < β) (hT : 0 < T)
    (hγpos : ∀ k, 0 < γ k) (hγ : Tendsto γ atTop atTop)
    (hharm : Tendsto (fun N => ∑ k ∈ Finset.range N, (γ k)⁻¹) atTop atTop)
    (hden : ∀ k, 1 - tangentIterate (verticalLowerIncrement α β T γ) k
      * verticalLowerIncrement α β T γ k ≠ 0) :
    ∃ n : ℕ → ℕ, Tendsto n atTop atTop ∧
      Tendsto (fun m => tangentIterate (verticalLowerIncrement α β T γ) (n m)) atTop (𝓝 0) :=
  exists_subseq_tangentIterate_tendsto_zero
    (tendsto_verticalLowerIncrement hα hαβ hγ)
    (tendsto_arctanPartialSum_verticalLower hα hαβ hT hγpos hγ hharm) hden

/-! ## Discharging the harmonic hypothesis from a linear ordinate bound -/

/-- **Sharpest available reduction, incoming channel.**  A linear upper bound on the ordinates —
equivalently a counting lower bound `N(T) ≫ T` — already forbids the asserted `+∞` endpoint. -/
theorem not_tendsto_atTop_verticalLowerRiccati_of_le_linear
    (hα : 1 / 2 < α) (hαβ : α < β) (hT : 0 < T)
    (hγpos : ∀ k, 0 < γ k) (hγ : Tendsto γ atTop atTop)
    {c : ℝ} (hc : 0 < c) (hlin : ∀ᶠ k in atTop, γ k ≤ c * ((k : ℝ) + 1))
    (hden : ∀ k, 1 - tangentIterate (verticalLowerIncrement α β T γ) k
      * verticalLowerIncrement α β T γ k ≠ 0) :
    ¬ Tendsto (tangentIterate (verticalLowerIncrement α β T γ)) atTop atTop :=
  not_tendsto_atTop_verticalLowerRiccati hα hαβ hT hγpos hγ
    (tendsto_sum_inv_atTop_of_le_linear hc hγpos hlin) hden

/-- **Sharpest available reduction, outgoing channel.** -/
theorem not_tendsto_atBot_verticalUpperRiccati_of_le_linear
    (hα : 1 / 2 < α) (hαβ : α < β) (hT : 0 < T)
    (hγpos : ∀ k, 0 < γ k) (hγ : Tendsto γ atTop atTop)
    {c : ℝ} (hc : 0 < c) (hlin : ∀ᶠ k in atTop, γ k ≤ c * ((k : ℝ) + 1))
    (hden : ∀ k, 1 - tangentIterate (verticalUpperIncrement α β T γ) k
      * verticalUpperIncrement α β T γ k ≠ 0) :
    ¬ Tendsto (tangentIterate (verticalUpperIncrement α β T γ)) atTop atBot :=
  not_tendsto_atBot_verticalUpperRiccati hα hαβ hT hγpos hγ
    (tendsto_sum_inv_atTop_of_le_linear hc hγpos hlin) hden

end

end RHTower
