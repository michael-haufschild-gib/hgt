import GaloisForLFunctions.HTGeometry.StieltjesMomentDetermination

/-!
# Clark–screw spectral rigidity

The movable-anchor Clark kernel differs from the fixed Stieltjes kernel by a term that is uniformly
small in the collapse parameter:

`(u + c²)/(u + s) - u/(u + s) = c²/(u + s) ≤ c²/s`.

So an anchor-collapsing family of Clark transforms and the fixed Stieltjes transforms of the same
sources have the same limits, and the interval law is a statement about Stieltjes transforms alone.

In the compactified coordinate `x = 1/(1+u)` the fixed kernel is
`u/(u+s) = 1 - s·x/(1 + (s-1)x)`, so for probability sources the interval law is exactly the
equality of the Stieltjes transforms `∫ x/(1+tx)`, and the moment determination identifies the two
sources.  Weak convergence of the squared Clark probabilities is therefore not an additional
hypothesis: it is equivalent to the interval law.
-/

open MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## The movable-anchor Clark kernel -/

/-- The movable-anchor Clark kernel in the squared ordinate. -/
def clarkSquaredKernel (c s u : ℝ) : ℝ := (u + c ^ (2 : ℕ)) / (u + s)

/-- The fixed Stieltjes kernel in the squared ordinate. -/
def stieltjesSquaredKernel (s u : ℝ) : ℝ := u / (u + s)

/-- **`(116)`: the movable kernel is uniformly close to the fixed one.** -/
theorem abs_clarkSquaredKernel_sub_le {c s u : ℝ} (hs : 0 < s) (hu : 0 ≤ u) :
    |clarkSquaredKernel c s u - stieltjesSquaredKernel s u| ≤ c ^ (2 : ℕ) / s := by
  have hus : (0 : ℝ) < u + s := by linarith
  have hval : clarkSquaredKernel c s u - stieltjesSquaredKernel s u = c ^ (2 : ℕ) / (u + s) := by
    rw [clarkSquaredKernel, stieltjesSquaredKernel, div_sub_div_same]
    congr 1
    ring
  rw [hval, abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_left (by positivity) hs (by linarith)

/-! ## The compactified coordinate -/

/-- **The fixed kernel in the compactified coordinate.**  Writing `x = 1/(1+u)`, the fixed
Stieltjes kernel is one minus `s` times the compactified Stieltjes kernel. -/
theorem stieltjesSquaredKernel_compactified {s x : ℝ} (hs : 0 < s) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    stieltjesSquaredKernel s ((1 - x) / x) = 1 - s * (x / (1 + (s - 1) * x)) := by
  have hden : (0 : ℝ) < 1 + (s - 1) * x := by nlinarith
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hdne : (1 : ℝ) + (s - 1) * x ≠ 0 := ne_of_gt hden
  have hsum : (1 - x) / x + s = (1 + (s - 1) * x) / x := by
    field_simp
    ring
  have hden2 : (1 - x) / x + s ≠ 0 := by
    rw [hsum]
    exact ne_of_gt (by positivity)
  have hL : stieltjesSquaredKernel s ((1 - x) / x) = (1 - x) / (1 + (s - 1) * x) := by
    rw [stieltjesSquaredKernel, div_eq_div_iff hden2 hdne]
    field_simp
    ring
  have hR : 1 - s * (x / (1 + (s - 1) * x)) = (1 - x) / (1 + (s - 1) * x) := by
    have hstep : s * (x / (1 + (s - 1) * x)) = (s * x) / (1 + (s - 1) * x) := by
      rw [mul_div_assoc]
    rw [hstep, eq_div_iff hdne, sub_mul, div_mul_cancel₀ _ hdne, one_mul]
    ring
  rw [hL, hR]

/-! ## Rigidity -/

/-- **Theorem J's determination half.**  Two finite sources on the compactified ordinate with the
same total mass and the same Stieltjes transform on a neighbourhood of the base point are equal;
so the interval law forces the whole squared Clark probability, not merely its transform values. -/
theorem clarkSource_eq_of_interval_law {μ ν : Measure HausdorffSourceSpace}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hmass : hausdorffMoment μ 0 = hausdorffMoment ν 0)
    (hlaw : ∀ t : ℝ, 0 < |t| → |t| < r →
      ∫ y, stieltjesKernel t y ∂μ = ∫ y, stieltjesKernel t y ∂ν) :
    μ = ν :=
  hausdorffSource_eq_of_stieltjes_eq hr hr1 hmass hlaw

/-- The interval law in the card's normalisation: for probability sources, agreement of the fixed
transforms `∫ u/(u+s)` near the base point is agreement of the compactified Stieltjes transforms. -/
theorem stieltjes_eq_of_fixedKernel_eq {μ ν : Measure HausdorffSourceSpace}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {t : ℝ} (hs : 0 < t + 1)
    (hmass : hausdorffMoment μ 0 = hausdorffMoment ν 0)
    (hfix : ∫ y, (1 - (t + 1) * stieltjesKernel t y) ∂μ
      = ∫ y, (1 - (t + 1) * stieltjesKernel t y) ∂ν) :
    ∫ y, stieltjesKernel t y ∂μ = ∫ y, stieltjesKernel t y ∂ν := by
  have hcont : Continuous fun y : HausdorffSourceSpace => stieltjesKernel t y := by
    have hden : ∀ y : HausdorffSourceSpace, 1 + t * (y : ℝ) ≠ 0 := by
      intro y
      have hy0 : (0 : ℝ) ≤ (y : ℝ) := y.property.1
      have hy1 : (y : ℝ) ≤ 1 := y.property.2
      have hkey : t ≤ t * (y : ℝ) ∨ 0 ≤ t * (y : ℝ) := by
        rcases le_or_gt 0 t with h | h
        · exact Or.inr (mul_nonneg h hy0)
        · exact Or.inl (by nlinarith)
      have hpos : (0 : ℝ) < 1 + t * (y : ℝ) := by
        rcases hkey with h | h <;> linarith
      exact ne_of_gt hpos
    exact (continuous_subtype_val).div
      (continuous_const.add (continuous_const.mul continuous_subtype_val)) hden
  have hintμ : Integrable (fun y : HausdorffSourceSpace => stieltjesKernel t y) μ :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hintν : Integrable (fun y : HausdorffSourceSpace => stieltjesKernel t y) ν :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsplitμ : ∫ y, (1 - (t + 1) * stieltjesKernel t y) ∂μ
      = hausdorffMoment μ 0 - (t + 1) * ∫ y, stieltjesKernel t y ∂μ := by
    rw [integral_sub (integrable_const 1) (hintμ.const_mul _), integral_const_mul]
    simp [hausdorffMoment, measureReal_def]
  have hsplitν : ∫ y, (1 - (t + 1) * stieltjesKernel t y) ∂ν
      = hausdorffMoment ν 0 - (t + 1) * ∫ y, stieltjesKernel t y ∂ν := by
    rw [integral_sub (integrable_const 1) (hintν.const_mul _), integral_const_mul]
    simp [hausdorffMoment, measureReal_def]
  rw [hsplitμ, hsplitν, hmass] at hfix
  have hne : (t + 1) ≠ 0 := ne_of_gt hs
  have heq : (t + 1) * ∫ y, stieltjesKernel t y ∂μ
      = (t + 1) * ∫ y, stieltjesKernel t y ∂ν := by linarith
  exact mul_left_cancel₀ hne heq

end RHTower

namespace RHTower

open MeasureTheory GaloisForLFunctions.HTGeometry

/-! ## The reciprocal transform of Theorem T -/

/-- The reciprocal kernel of `(207)` is one minus the parameter times the Stieltjes kernel. -/
theorem reciprocalKernel_eq {t : ℝ} {y : HausdorffSourceSpace} (hden : 1 + t * (y : ℝ) ≠ 0) :
    1 / (1 + t * (y : ℝ)) = 1 - t * stieltjesKernel t y := by
  rw [stieltjesKernel]
  field_simp
  ring

/-- **Theorem T's uniqueness.**  A finite source on the compactified ordinate is determined by its
reciprocal transform `∫ 1/(1 + t x)` on a punctured neighbourhood of the base point, together with
its total mass. -/
theorem clarkSource_eq_of_reciprocal_transform_eq {μ ν : Measure HausdorffSourceSpace}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hmass : hausdorffMoment μ 0 = hausdorffMoment ν 0)
    (hrec : ∀ t : ℝ, 0 < |t| → |t| < r →
      ∫ y, (1 : ℝ) / (1 + t * (y : ℝ)) ∂μ = ∫ y, (1 : ℝ) / (1 + t * (y : ℝ)) ∂ν) :
    μ = ν := by
  refine clarkSource_eq_of_interval_law hr hr1 hmass ?_
  intro t ht0 htr
  have ht1 : |t| < 1 := lt_of_lt_of_le htr hr1
  have hden : ∀ y : HausdorffSourceSpace, 1 + t * (y : ℝ) ≠ 0 := by
    intro y
    have hy0 : (0 : ℝ) ≤ (y : ℝ) := y.property.1
    have hy1 : (y : ℝ) ≤ 1 := y.property.2
    have habs : |t * (y : ℝ)| < 1 := by
      rw [abs_mul, abs_of_nonneg hy0]
      calc |t| * (y : ℝ) ≤ |t| * 1 := mul_le_mul_of_nonneg_left hy1 (abs_nonneg t)
        _ = |t| := mul_one _
        _ < 1 := ht1
    rcases abs_lt.mp habs with ⟨hlow, -⟩
    intro h
    linarith
  have hcont : Continuous fun y : HausdorffSourceSpace => stieltjesKernel t y := by
    exact (continuous_subtype_val).div
      (continuous_const.add (continuous_const.mul continuous_subtype_val)) hden
  have hintμ : Integrable (fun y : HausdorffSourceSpace => stieltjesKernel t y) μ :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hintν : Integrable (fun y : HausdorffSourceSpace => stieltjesKernel t y) ν :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsplit : ∀ (ρ : Measure HausdorffSourceSpace), ∀ _ : IsFiniteMeasure ρ,
      Integrable (fun y : HausdorffSourceSpace => stieltjesKernel t y) ρ →
      ∫ y, (1 : ℝ) / (1 + t * (y : ℝ)) ∂ρ
        = hausdorffMoment ρ 0 - t * ∫ y, stieltjesKernel t y ∂ρ := by
    intro ρ _ hint
    have hcongr : ∀ y : HausdorffSourceSpace,
        (1 : ℝ) / (1 + t * (y : ℝ)) = 1 - t * stieltjesKernel t y :=
      fun y => reciprocalKernel_eq (hden y)
    rw [integral_congr_ae (Filter.Eventually.of_forall hcongr)]
    rw [integral_sub (integrable_const 1) (hint.const_mul _), integral_const_mul]
    simp [hausdorffMoment, measureReal_def]
  have hμ := hsplit μ inferInstance hintμ
  have hν := hsplit ν inferInstance hintν
  have heq := hrec t ht0 htr
  rw [hμ, hν, hmass] at heq
  have htne : t ≠ 0 := by
    intro h
    rw [h] at ht0
    simp at ht0
  have hstep : t * ∫ y, stieltjesKernel t y ∂μ = t * ∫ y, stieltjesKernel t y ∂ν := by linarith
  exact mul_left_cancel₀ htne hstep

/-- **Theorem U's hierarchy bookkeeping.**  The trace differences converge exactly when the
occupancy moments do. -/
theorem tendsto_traceHierarchy_iff {c : ℕ → ℝ} {cXi : ℝ} (j : ℕ) :
    Filter.Tendsto (fun n => 2 * ((j : ℝ) + 1) * c n - 1) Filter.atTop
        (nhds (2 * ((j : ℝ) + 1) * cXi - 1))
      ↔ Filter.Tendsto c Filter.atTop (nhds cXi) := by
  constructor
  · intro h
    have hne : (2 * ((j : ℝ) + 1)) ≠ 0 := by positivity
    have hadd := h.add_const 1
    simp only [sub_add_cancel] at hadd
    have hmul := hadd.const_mul (2 * ((j : ℝ) + 1))⁻¹
    have hval : (2 * ((j : ℝ) + 1))⁻¹ * (2 * ((j : ℝ) + 1) * cXi) = cXi := by
      field_simp
    rw [hval] at hmul
    refine hmul.congr fun n => ?_
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  · intro h
    exact (h.const_mul (2 * ((j : ℝ) + 1))).sub_const 1

end RHTower
