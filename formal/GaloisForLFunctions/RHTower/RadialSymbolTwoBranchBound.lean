import GaloisForLFunctions.HTGeometry.OscBudgetSymbolBound
import GaloisForLFunctions.RHTower.RadialTwoIndexOscillatoryBound

/-!
# The `1/(c j k |j−k|)` shape of an exterior radial off-diagonal entry

Bundling the regularity and the symbol decay of a two-branch amplitude pair into one predicate turns
the two-index oscillatory bound into a single numerical statement.  For indices `j > k ≥ 2`, a radius
ray starting at `1`, symbol decay `|g| ≤ M/√x`, `|g'| ≤ M'/(x√x)` for both pairs, and phase curvature
`≤ N/x³`,

```text
|∫_a^b U_j U_k| ≤ 4 (2 M_j M_k + (M_j' M_k + M_j M_k') + M_j M_k N/(3m)) / (m c) ,
m = (2/3)(j − k) .
```

Every constant is absolute and the bound does not grow with the right endpoint, so it survives the
passage to the whole exterior ray.  When the amplitudes carry the geometric prefactor `√d₁/r`, the
products `M_j M_k` carry `d₁/(jk)` and the entry is `O(d₁/(c j k |j−k|))`.
-/

open Set MeasureTheory intervalIntegral

open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- A two-branch amplitude pair on `[a,b]` in the half-power symbol class:
`|g| ≤ M/√x`, `|g'| ≤ M'/(x√x)`.  This is the decay a Liouville-transformed solution has; the
*product* of two such pairs lands in the `1/x` class the budget bound consumes. -/
structure SymbolTwoBranch (a b M M' : ℝ) (g₁ g₂ g₁' g₂' : ℝ → ℝ) : Prop where
  deriv₁ : ∀ x ∈ Icc a b, HasDerivAt g₁ (g₁' x) x
  deriv₂ : ∀ x ∈ Icc a b, HasDerivAt g₂ (g₂' x) x
  cont₁ : ContinuousOn g₁ (Icc a b)
  cont₁' : ContinuousOn g₁' (Icc a b)
  cont₂ : ContinuousOn g₂ (Icc a b)
  cont₂' : ContinuousOn g₂' (Icc a b)
  bound₁ : ∀ x ∈ Icc a b, |g₁ x| ≤ M / Real.sqrt x
  bound₁' : ∀ x ∈ Icc a b, |g₁' x| ≤ M' / (x * Real.sqrt x)
  bound₂ : ∀ x ∈ Icc a b, |g₂ x| ≤ M / Real.sqrt x
  bound₂' : ∀ x ∈ Icc a b, |g₂' x| ≤ M' / (x * Real.sqrt x)

/-- The budget of a product weight, in the form the four branches share. -/
theorem oscBudget_le_of_product_symbol {a b m P Q N : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hm : 0 < m) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hN : 0 ≤ N)
    {w w' Θ'' : ℝ → ℝ}
    (hwc : ContinuousOn w (Icc a b)) (hw'c : ContinuousOn w' (Icc a b))
    (hΘc : ContinuousOn Θ'' (Icc a b))
    (hw : ∀ x ∈ Icc a b, |w x| ≤ P / x) (hw' : ∀ x ∈ Icc a b, |w' x| ≤ Q / x ^ 2)
    (hΘ : ∀ x ∈ Icc a b, |Θ'' x| ≤ N / x ^ 3) :
    oscBudget a b m w w' Θ'' ≤ 2 * P / m + Q / m + P * N / (3 * m ^ 2) :=
  oscBudget_le_of_symbolBounds ha hab hm hP hQ hN hwc hw'c hΘc hw hw' hΘ

/-- **Building a symbol record by composition.**  A Liouville amplitude with `|A| ≤ C/√x`,
`|A'| ≤ C'/(x√x)` multiplied by interaction amplitudes bounded by `K` whose transported derivatives
decay like `K'/x²` produces a half-power symbol pair with constants `C K` and `C' K + C K'`. -/
theorem symbolTwoBranch_of_composition {a b C C' K K' : ℝ}
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
    (hPb : ∀ t, |P t| ≤ K) (hQb : ∀ t, |Q t| ≤ K)
    (hP'b : ∀ x ∈ Icc a b, |P' (Φ x) * Φ' x| ≤ K' / x ^ 2)
    (hQ'b : ∀ x ∈ Icc a b, |Q' (Φ x) * Φ' x| ≤ K' / x ^ 2) :
    SymbolTwoBranch a b (C * K) (C' * K + C * K')
      (fun x => A x * P (Φ x)) (fun x => A x * Q (Φ x))
      (fun x => A' x * P (Φ x) + A x * (P' (Φ x) * Φ' x))
      (fun x => A' x * Q (Φ x) + A x * (Q' (Φ x) * Φ' x)) := by
  have hxpos : ∀ x ∈ Icc a b, (0 : ℝ) < x := fun x hx => lt_of_lt_of_le zero_lt_one
    (le_trans ha hx.1)
  have hbound : ∀ (R R' : ℝ → ℝ), (∀ t, HasDerivAt R (R' t) t) → (∀ t, |R t| ≤ K) →
      (∀ x ∈ Icc a b, |R' (Φ x) * Φ' x| ≤ K' / x ^ 2) →
      (∀ x ∈ Icc a b, |A x * R (Φ x)| ≤ C * K / Real.sqrt x) ∧
      (∀ x ∈ Icc a b, |A' x * R (Φ x) + A x * (R' (Φ x) * Φ' x)|
        ≤ (C' * K + C * K') / (x * Real.sqrt x)) := by
    intro R R' _ hRb hR'b
    constructor
    · intro x hx
      have hx0 := hxpos x hx
      have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
      rw [abs_mul]
      calc |A x| * |R (Φ x)| ≤ (C / Real.sqrt x) * K :=
            mul_le_mul (hA x hx) (hRb _) (abs_nonneg _) (div_nonneg hC hs.le)
        _ = C * K / Real.sqrt x := by ring
    · intro x hx
      have hx0 := hxpos x hx
      have hx1 : (1 : ℝ) ≤ x := le_trans ha hx.1
      have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
      have h1 : |A' x * R (Φ x)| ≤ C' * K / (x * Real.sqrt x) := by
        rw [abs_mul]
        calc |A' x| * |R (Φ x)| ≤ (C' / (x * Real.sqrt x)) * K :=
              mul_le_mul (hA'b x hx) (hRb _) (abs_nonneg _)
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
  obtain ⟨hPval, hPder⟩ := hbound P P' hPd hPb hP'b
  obtain ⟨hQval, hQder⟩ := hbound Q Q' hQd hQb hQ'b
  refine ⟨fun x hx => (hAd x hx).mul ((hPd (Φ x)).comp x (hΦd x hx)),
    fun x hx => (hAd x hx).mul ((hQd (Φ x)).comp x (hΦd x hx)),
    hAc.mul (hPc.comp_continuousOn hΦc), ?_, hAc.mul (hQc.comp_continuousOn hΦc), ?_,
    hPval, hPder, hQval, hQder⟩
  · exact (hA'c.mul (hPc.comp_continuousOn hΦc)).add
      (hAc.mul ((hP'c.comp_continuousOn hΦc).mul hΦ'c))
  · exact (hA'c.mul (hQc.comp_continuousOn hΦc)).add
      (hAc.mul ((hQ'c.comp_continuousOn hΦc).mul hΦ'c))

/-- **The exterior radial off-diagonal entry, with all constants explicit.** -/
theorem abs_integral_radial_twoBranch_symbol_le
    {s j k a b c : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hk2 : 2 ≤ k) (hkj : k < j) (ha : 1 ≤ a) (hab : a ≤ b) (hc : 0 < c)
    {Mj Mj' Mk Mk' N : ℝ} (hMj : 0 ≤ Mj) (hMj' : 0 ≤ Mj') (hMk : 0 ≤ Mk) (hMk' : 0 ≤ Mk')
    (hN : 0 ≤ N)
    {g₁ g₂ g₁' g₂' g₃ g₄ g₃' g₄' : ℝ → ℝ}
    (hj : SymbolTwoBranch a b Mj Mj' g₁ g₂ g₁' g₂')
    (hkk : SymbolTwoBranch a b Mk Mk' g₃ g₄ g₃' g₄')
    (hND : ∀ x ∈ Icc a b,
      |dilatedRadialPhaseAccel s j x - dilatedRadialPhaseAccel s k x| ≤ N / x ^ 3)
    (hNS : ∀ x ∈ Icc a b,
      |dilatedRadialPhaseAccel s j x + dilatedRadialPhaseAccel s k x| ≤ N / x ^ 3) :
    |∫ x in a..b,
        (g₁ x * Real.cos (c * dilatedRadialPhase s j x)
            + g₂ x * Real.sin (c * dilatedRadialPhase s j x))
          * (g₃ x * Real.cos (c * dilatedRadialPhase s k x)
            + g₄ x * Real.sin (c * dilatedRadialPhase s k x))|
      ≤ 4 * (2 * (Mj * Mk) / (2 / 3 * (j - k)) + (Mj' * Mk + Mj * Mk') / (2 / 3 * (j - k))
        + (Mj * Mk) * N / (3 * (2 / 3 * (j - k)) ^ 2)) / c := by
  set m : ℝ := 2 / 3 * (j - k) with hmdef
  have hjge : (2 : ℝ) ≤ j := le_trans hk2 hkj.le
  have hm : (0 : ℝ) < m := by
    have : (0 : ℝ) < j - k := by linarith
    rw [hmdef]
    positivity
  have hP : (0 : ℝ) ≤ Mj * Mk := by positivity
  have hQ : (0 : ℝ) ≤ Mj' * Mk + Mj * Mk' := by positivity
  have haIcc : ∀ x ∈ Icc a b, (1 : ℝ) ≤ x := fun x hx => le_trans ha hx.1
  have hΘD : ContinuousOn
      (fun x => dilatedRadialPhaseAccel s j x - dilatedRadialPhaseAccel s k x) (Icc a b) :=
    (continuousOn_dilatedRadialPhaseAccel hs1 hjge ha).sub
      (continuousOn_dilatedRadialPhaseAccel hs1 hk2 ha)
  have hΘS : ContinuousOn
      (fun x => dilatedRadialPhaseAccel s j x + dilatedRadialPhaseAccel s k x) (Icc a b) :=
    (continuousOn_dilatedRadialPhaseAccel hs1 hjge ha).add
      (continuousOn_dilatedRadialPhaseAccel hs1 hk2 ha)
  -- the four weights and their derivatives
  have hw₁ : ContinuousOn (fun x => 1 / 2 * (g₁ x * g₃ x + g₂ x * g₄ x)) (Icc a b) :=
    ((hj.cont₁.mul hkk.cont₁).add (hj.cont₂.mul hkk.cont₂)).const_smul (1 / 2 : ℝ)
  have hw₂ : ContinuousOn (fun x => 1 / 2 * (g₁ x * g₃ x - g₂ x * g₄ x)) (Icc a b) :=
    ((hj.cont₁.mul hkk.cont₁).sub (hj.cont₂.mul hkk.cont₂)).const_smul (1 / 2 : ℝ)
  have hw₃ : ContinuousOn (fun x => 1 / 2 * (g₂ x * g₃ x - g₁ x * g₄ x)) (Icc a b) :=
    ((hj.cont₂.mul hkk.cont₁).sub (hj.cont₁.mul hkk.cont₂)).const_smul (1 / 2 : ℝ)
  have hw₄ : ContinuousOn (fun x => 1 / 2 * (g₂ x * g₃ x + g₁ x * g₄ x)) (Icc a b) :=
    ((hj.cont₂.mul hkk.cont₁).add (hj.cont₁.mul hkk.cont₂)).const_smul (1 / 2 : ℝ)
  have hw₁' : ContinuousOn
      (fun x => 1 / 2 * (g₁' x * g₃ x + g₁ x * g₃' x + (g₂' x * g₄ x + g₂ x * g₄' x)))
      (Icc a b) :=
    (((hj.cont₁'.mul hkk.cont₁).add (hj.cont₁.mul hkk.cont₁')).add
      ((hj.cont₂'.mul hkk.cont₂).add (hj.cont₂.mul hkk.cont₂'))).const_smul (1 / 2 : ℝ)
  have hw₂' : ContinuousOn
      (fun x => 1 / 2 * (g₁' x * g₃ x + g₁ x * g₃' x - (g₂' x * g₄ x + g₂ x * g₄' x)))
      (Icc a b) :=
    (((hj.cont₁'.mul hkk.cont₁).add (hj.cont₁.mul hkk.cont₁')).sub
      ((hj.cont₂'.mul hkk.cont₂).add (hj.cont₂.mul hkk.cont₂'))).const_smul (1 / 2 : ℝ)
  have hw₃' : ContinuousOn
      (fun x => 1 / 2 * (g₂' x * g₃ x + g₂ x * g₃' x - (g₁' x * g₄ x + g₁ x * g₄' x)))
      (Icc a b) :=
    (((hj.cont₂'.mul hkk.cont₁).add (hj.cont₂.mul hkk.cont₁')).sub
      ((hj.cont₁'.mul hkk.cont₂).add (hj.cont₁.mul hkk.cont₂'))).const_smul (1 / 2 : ℝ)
  have hw₄' : ContinuousOn
      (fun x => 1 / 2 * (g₂' x * g₃ x + g₂ x * g₃' x + (g₁' x * g₄ x + g₁ x * g₄' x)))
      (Icc a b) :=
    (((hj.cont₂'.mul hkk.cont₁).add (hj.cont₂.mul hkk.cont₁')).add
      ((hj.cont₁'.mul hkk.cont₂).add (hj.cont₁.mul hkk.cont₂'))).const_smul (1 / 2 : ℝ)
  have hb₁ := oscBudget_le_of_product_symbol (m := m) ha hab hm hP hQ hN hw₁ hw₁' hΘD
    (fun x hx => abs_half_add_halfSymbol (haIcc x hx) (hj.bound₁ x hx) (hkk.bound₁ x hx)
      (hj.bound₂ x hx) (hkk.bound₂ x hx))
    (fun x hx => abs_half_deriv_add_halfSymbol (haIcc x hx)
      (hj.bound₁ x hx) (hj.bound₁' x hx) (hkk.bound₁ x hx) (hkk.bound₁' x hx)
      (hj.bound₂ x hx) (hj.bound₂' x hx) (hkk.bound₂ x hx) (hkk.bound₂' x hx)) hND
  have hb₂ := oscBudget_le_of_product_symbol (m := m) ha hab hm hP hQ hN hw₂ hw₂' hΘS
    (fun x hx => abs_half_sub_halfSymbol (haIcc x hx) (hj.bound₁ x hx) (hkk.bound₁ x hx)
      (hj.bound₂ x hx) (hkk.bound₂ x hx))
    (fun x hx => abs_half_deriv_sub_halfSymbol (haIcc x hx)
      (hj.bound₁ x hx) (hj.bound₁' x hx) (hkk.bound₁ x hx) (hkk.bound₁' x hx)
      (hj.bound₂ x hx) (hj.bound₂' x hx) (hkk.bound₂ x hx) (hkk.bound₂' x hx)) hNS
  have hb₃ := oscBudget_le_of_product_symbol (m := m) ha hab hm hP hQ hN hw₃ hw₃' hΘD
    (fun x hx => abs_half_sub_halfSymbol (haIcc x hx) (hj.bound₂ x hx) (hkk.bound₁ x hx)
      (hj.bound₁ x hx) (hkk.bound₂ x hx))
    (fun x hx => abs_half_deriv_sub_halfSymbol (haIcc x hx)
      (hj.bound₂ x hx) (hj.bound₂' x hx) (hkk.bound₁ x hx) (hkk.bound₁' x hx)
      (hj.bound₁ x hx) (hj.bound₁' x hx) (hkk.bound₂ x hx) (hkk.bound₂' x hx)) hND
  have hb₄ := oscBudget_le_of_product_symbol (m := m) ha hab hm hP hQ hN hw₄ hw₄' hΘS
    (fun x hx => abs_half_add_halfSymbol (haIcc x hx) (hj.bound₂ x hx) (hkk.bound₁ x hx)
      (hj.bound₁ x hx) (hkk.bound₂ x hx))
    (fun x hx => abs_half_deriv_add_halfSymbol (haIcc x hx)
      (hj.bound₂ x hx) (hj.bound₂' x hx) (hkk.bound₁ x hx) (hkk.bound₁' x hx)
      (hj.bound₁ x hx) (hj.bound₁' x hx) (hkk.bound₂ x hx) (hkk.bound₂' x hx)) hNS
  have hmain := abs_integral_radial_twoBranch_product_le hs hs1 hk2 hkj ha hab hc
    hj.deriv₁ hj.cont₁ hj.cont₁' hj.deriv₂ hj.cont₂ hj.cont₂'
    hkk.deriv₁ hkk.cont₁ hkk.cont₁' hkk.deriv₂ hkk.cont₂ hkk.cont₂'
  refine hmain.trans ?_
  have hbudget : (oscBudget a b m (fun x => 1 / 2 * (g₁ x * g₃ x + g₂ x * g₄ x))
        (fun x => 1 / 2 * (g₁' x * g₃ x + g₁ x * g₃' x + (g₂' x * g₄ x + g₂ x * g₄' x)))
        (fun x => dilatedRadialPhaseAccel s j x - dilatedRadialPhaseAccel s k x)
      + oscBudget a b m (fun x => 1 / 2 * (g₁ x * g₃ x - g₂ x * g₄ x))
        (fun x => 1 / 2 * (g₁' x * g₃ x + g₁ x * g₃' x - (g₂' x * g₄ x + g₂ x * g₄' x)))
        (fun x => dilatedRadialPhaseAccel s j x + dilatedRadialPhaseAccel s k x)
      + oscBudget a b m (fun x => 1 / 2 * (g₂ x * g₃ x - g₁ x * g₄ x))
        (fun x => 1 / 2 * (g₂' x * g₃ x + g₂ x * g₃' x - (g₁' x * g₄ x + g₁ x * g₄' x)))
        (fun x => dilatedRadialPhaseAccel s j x - dilatedRadialPhaseAccel s k x)
      + oscBudget a b m (fun x => 1 / 2 * (g₂ x * g₃ x + g₁ x * g₄ x))
        (fun x => 1 / 2 * (g₂' x * g₃ x + g₂ x * g₃' x + (g₁' x * g₄ x + g₁ x * g₄' x)))
        (fun x => dilatedRadialPhaseAccel s j x + dilatedRadialPhaseAccel s k x))
      ≤ 4 * (2 * (Mj * Mk) / m + (Mj' * Mk + Mj * Mk') / m
        + (Mj * Mk) * N / (3 * m ^ 2)) := by
    linarith [hb₁, hb₂, hb₃, hb₄]
  gcongr


/-- **The exterior radial off-diagonal entry, with the phase curvature discharged.**  Nothing about
the phase is assumed: its curvature bound `|j²ξ''(jx) ∓ k²ξ''(kx)| ≤ (16/9)/x³` is proved, so the
only inputs are the two symbol records. -/
theorem abs_integral_radial_twoBranch_symbol_le'
    {s j k a b c : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hk2 : 2 ≤ k) (hkj : k < j) (ha : 1 ≤ a) (hab : a ≤ b) (hc : 0 < c)
    {Mj Mj' Mk Mk' : ℝ} (hMj : 0 ≤ Mj) (hMj' : 0 ≤ Mj') (hMk : 0 ≤ Mk) (hMk' : 0 ≤ Mk')
    {g₁ g₂ g₁' g₂' g₃ g₄ g₃' g₄' : ℝ → ℝ}
    (hj : SymbolTwoBranch a b Mj Mj' g₁ g₂ g₁' g₂')
    (hkk : SymbolTwoBranch a b Mk Mk' g₃ g₄ g₃' g₄') :
    |∫ x in a..b,
        (g₁ x * Real.cos (c * dilatedRadialPhase s j x)
            + g₂ x * Real.sin (c * dilatedRadialPhase s j x))
          * (g₃ x * Real.cos (c * dilatedRadialPhase s k x)
            + g₄ x * Real.sin (c * dilatedRadialPhase s k x))|
      ≤ 4 * (2 * (Mj * Mk) / (2 / 3 * (j - k)) + (Mj' * Mk + Mj * Mk') / (2 / 3 * (j - k))
        + (Mj * Mk) * (16 / 9) / (3 * (2 / 3 * (j - k)) ^ 2)) / c := by
  have hjge : (2 : ℝ) ≤ j := le_trans hk2 hkj.le
  exact abs_integral_radial_twoBranch_symbol_le hs hs1 hk2 hkj ha hab hc hMj hMj' hMk hMk'
    (by norm_num) hj hkk
    (fun x hx => abs_dilatedRadialPhaseAccel_sub_le hs hs1 hjge hk2 (le_trans ha hx.1))
    (fun x hx => abs_dilatedRadialPhaseAccel_add_le hs hs1 hjge hk2 (le_trans ha hx.1))

end GaloisForLFunctions.RHTower

end
