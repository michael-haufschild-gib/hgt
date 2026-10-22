import GaloisForLFunctions.RHTower.FirstRowModelSymbol
import GaloisForLFunctions.RHTower.CCM.CCMHighRadialFirstRowBV

/-!
# The high radial first-row entry

The weight of a high radial first-row Gram entry is

```text
V(x) = U(x) · A(x) / x ,
```

with `U = A_s·J₀(c ξ_s)` the leading first-row factor and `A` one exterior amplitude of the second
factor.  Both are half-power symbols beyond the second dilation, so `V` lies in the symbol class of
`bvWeight_of_symbol`, its endpoint-plus-variation budget is `O(c)`, and the nonstationary estimate
against the dilated exterior oscillation of index `r` returns `O(1/r)`.  Multiplied by the `1/r`
normalization the exterior expansion carries, that is the `r^{-2}` law of the card.
-/

open Set MeasureTheory intervalIntegral

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The weight of a first-row entry: the leading factor times one exterior amplitude, over `x`. -/
def firstRowWeight (s c : ℝ) (A : ℝ → ℝ) (x : ℝ) : ℝ := firstRowModel s c x * A x / x

/-- Its derivative. -/
def firstRowWeightDeriv (s c : ℝ) (A A' : ℝ → ℝ) (x : ℝ) : ℝ :=
  (firstRowModelDeriv s c x * A x + firstRowModel s c x * A' x) / x
    - firstRowModel s c x * A x / x ^ (2 : ℕ)

theorem hasDerivAt_firstRowWeight {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x)
    {A A' : ℝ → ℝ} (hA : HasDerivAt A (A' x) x) :
    HasDerivAt (firstRowWeight s c A) (firstRowWeightDeriv s c A A' x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have h := ((hasDerivAt_firstRowModel (s := s) (c := c) hs0 hs1 hx).mul hA).div
    (hasDerivAt_id x) hx0
  refine h.congr_deriv ?_
  rw [firstRowWeightDeriv]
  simp only [id_eq, Pi.mul_apply]
  field_simp

theorem continuousOn_firstRowModel {s c a b : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (ha : 1 < a) : ContinuousOn (firstRowModel s c) (Icc a b) := fun _x hx =>
  ((hasDerivAt_firstRowModel hs0 hs1 (lt_of_lt_of_le ha hx.1)).continuousAt).continuousWithinAt

theorem continuousOn_firstRowModelDeriv {s c a b : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (ha : 1 < a) : ContinuousOn (firstRowModelDeriv s c) (Icc a b) := by
  have hsub : Icc a b ⊆ Ioi (1 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
  have hbesselCont : Continuous besselJ0 :=
    continuous_iff_continuousAt.mpr fun u => (hasDerivAt_besselJ0 u).continuousAt
  have hbesselDCont : Continuous besselJ0Deriv :=
    continuous_iff_continuousAt.mpr fun u => (hasDerivAt_besselJ0Deriv u).continuousAt
  have hphase : ContinuousOn (fun x => c * xiEndpointPhase s x) (Icc a b) :=
    continuousOn_const.mul ((continuousOn_xiEndpointPhase hs0).mono hsub)
  have hspeed : ContinuousOn (xiSpeed s) (Icc a b) := fun x hx =>
    ((continuousAt_xiSpeed (s := s) (lt_of_lt_of_le ha hx.1)).continuousWithinAt)
  have h1 : ContinuousOn (fun x => xiAmplitudeDeriv s x * lgBesselModel s c x) (Icc a b) :=
    ((continuousOn_xiAmplitudeDeriv hs0 hs1).mono hsub).mul (hbesselCont.comp_continuousOn hphase)
  have h2 : ContinuousOn (fun x => xiAmplitude s x * lgBesselModelDeriv s c x) (Icc a b) :=
    ((continuousOn_xiAmplitude hs0 hs1).mono hsub).mul
      ((hbesselDCont.comp_continuousOn hphase).mul (continuousOn_const.mul hspeed))
  exact h1.add h2

/-- **The endpoint-plus-variation budget of a high radial first-row weight.** -/
theorem bvWeight_firstRowWeight {s c a b R R' : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 ≤ c)
    (ha : 2 ≤ a) (hab : a ≤ b) {A A' : ℝ → ℝ}
    (hA : ∀ x ∈ Icc a b, HasDerivAt A (A' x) x)
    (hAc : ContinuousOn A (Icc a b)) (hA'c : ContinuousOn A' (Icc a b))
    (hR : ∀ x ∈ Icc a b, |A x| ≤ R / Real.sqrt x)
    (hR' : ∀ x ∈ Icc a b, |A' x| ≤ R' / (x * Real.sqrt x)) :
    BVWeight a b (2 * (2 * R) + ((4 + 16 * c / (3 * Real.pi)) * R + 2 * R' + 2 * R))
        (firstRowWeight s c A) (firstRowWeightDeriv s c A A')
      ∧ (∫ x in a..b, |firstRowWeight s c A x|) ≤ 2 * (2 * R) := by
  have ha1 : (1 : ℝ) < a := by linarith
  have hlt : ∀ x ∈ Icc a b, (1 : ℝ) < x := fun x hx => lt_of_lt_of_le ha1 hx.1
  have hge : ∀ x ∈ Icc a b, (2 : ℝ) ≤ x := fun x hx => le_trans ha hx.1
  have hUc : ContinuousOn (firstRowModel s c) (Icc a b) := continuousOn_firstRowModel hs0 hs1 ha1
  have hU'c : ContinuousOn (firstRowModelDeriv s c) (Icc a b) :=
    continuousOn_firstRowModelDeriv hs0 hs1 ha1
  have hxne : ∀ x ∈ Icc a b, x ≠ 0 := fun x hx => ne_of_gt (lt_trans zero_lt_one (hlt x hx))
  have hVc : ContinuousOn (firstRowWeight s c A) (Icc a b) :=
    (hUc.mul hAc).div continuousOn_id hxne
  have hV'c : ContinuousOn (firstRowWeightDeriv s c A A') (Icc a b) := by
    refine ContinuousOn.sub (((hU'c.mul hAc).add (hUc.mul hA'c)).div continuousOn_id hxne) ?_
    exact (hUc.mul hAc).div (continuousOn_pow 2) (fun x hx => pow_ne_zero 2 (hxne x hx))
  refine bvWeight_of_symbol (by linarith : (1 : ℝ) ≤ a) hab
    (fun x hx => hasDerivAt_firstRowWeight hs0 hs1 (hlt x hx) (hA x hx)) hVc hV'c ?_ ?_
  · intro x hx
    exact (firstRowWeight_symbol_bounds (U := firstRowModel s c) (U' := firstRowModelDeriv s c)
      (A := A) (A' := A') (hlt x hx).le
      (abs_firstRowModel_le hs0 hs1 (hlt x hx))
      (abs_firstRowModelDeriv_le hs0 hs1 hc (hge x hx))
      (hR x hx) (hR' x hx)).1
  · intro x hx
    exact (firstRowWeight_symbol_bounds (U := firstRowModel s c) (U' := firstRowModelDeriv s c)
      (A := A) (A' := A') (hlt x hx).le
      (abs_firstRowModel_le hs0 hs1 (hlt x hx))
      (abs_firstRowModelDeriv_le hs0 hs1 hc (hge x hx))
      (hR x hx) (hR' x hx)).2

/-- **The high radial first-row entry.**  Every constant is absolute and the bandwidth enters only
through `Q′ = 4 + 16c/(3π)`, so the estimate is `O(1/r)` uniformly in the endpoint. -/
theorem abs_integral_highRadial_firstRowEntry_le {s c r a b R R' φ : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hr : 2 ≤ r) (ha : 2 ≤ a) (hab : a ≤ b)
    {A A' : ℝ → ℝ}
    (hA : ∀ x ∈ Icc a b, HasDerivAt A (A' x) x)
    (hAc : ContinuousOn A (Icc a b)) (hA'c : ContinuousOn A' (Icc a b))
    (hR : ∀ x ∈ Icc a b, |A x| ≤ R / Real.sqrt x)
    (hR' : ∀ x ∈ Icc a b, |A' x| ≤ R' / (x * Real.sqrt x)) :
    |∫ x in a..b, firstRowWeight s c A x * Real.cos (c * dilatedRadialPhase s r x + φ)|
      ≤ ((2 * (2 * R) + ((4 + 16 * c / (3 * Real.pi)) * R + 2 * R' + 2 * R)) / r
          + 16 * (2 * (2 * R)) / (9 * r ^ (3 : ℕ))) / c := by
  obtain ⟨hbv, hmass⟩ :=
    bvWeight_firstRowWeight hs0 hs1 hc.le ha hab hA hAc hA'c hR hR'
  exact abs_integral_highRadial_firstRow_le hs0 hs1 hr hc (by linarith : (1 : ℝ) ≤ a) hab hbv hmass

end GaloisForLFunctions.RHTower

end
