import GaloisForLFunctions.HTGeometry.OscBudgetSymbolBound
import GaloisForLFunctions.RHTower.RadialTwoIndexOscillatoryBound

/-!
# The `1/(c j k |j−k|)` shape of an exterior radial off-diagonal entry

Bundling the regularity and the symbol decay of a two-branch representation into one predicate turns
the two-index oscillatory bound into a single numerical statement: for indices `j > k ≥ 2` and a
radius ray starting at `1`,

```text
|∫_a^b U_j U_k| ≤ 4 (2 M_j M_k + (M_j' M_k + M_j M_k') + M_j M_k N/(3m)) / (m c) ,
m = (2/3)(j − k) .
```

Every constant is absolute and the bound does not grow with the right endpoint, so it survives the
passage to the whole ray.  When the amplitudes carry the geometric prefactor `√d₁/r`, the constants
`M_j M_k` carry `d₁/(jk)` and the whole entry is `O(d₁/(c j k |j−k|))`.
-/

open Set MeasureTheory intervalIntegral

open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- A two-branch amplitude pair on `[a,b]` with symbol decay `|g| ≤ M/x`, `|g'| ≤ M'/x²`. -/
structure SymbolTwoBranch (a b M M' : ℝ) (g₁ g₂ g₁' g₂' : ℝ → ℝ) : Prop where
  deriv₁ : ∀ x ∈ Icc a b, HasDerivAt g₁ (g₁' x) x
  deriv₂ : ∀ x ∈ Icc a b, HasDerivAt g₂ (g₂' x) x
  cont₁ : ContinuousOn g₁ (Icc a b)
  cont₁' : ContinuousOn g₁' (Icc a b)
  cont₂ : ContinuousOn g₂ (Icc a b)
  cont₂' : ContinuousOn g₂' (Icc a b)
  bound₁ : ∀ x ∈ Icc a b, |g₁ x| ≤ M / x
  bound₁' : ∀ x ∈ Icc a b, |g₁' x| ≤ M' / x ^ 2
  bound₂ : ∀ x ∈ Icc a b, |g₂ x| ≤ M / x
  bound₂' : ∀ x ∈ Icc a b, |g₂' x| ≤ M' / x ^ 2

/-- The budget bound satisfied by each of the four product weights. -/
theorem oscBudget_product_le {a b m Mj Mj' Mk Mk' N : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hm : 0 < m)
    (hMj : 0 ≤ Mj) (hMj' : 0 ≤ Mj') (hMk : 0 ≤ Mk) (hMk' : 0 ≤ Mk') (hN : 0 ≤ N)
    {g₁ g₂ g₁' g₂' g₃ g₄ g₃' g₄' : ℝ → ℝ}
    (hj : SymbolTwoBranch a b Mj Mj' g₁ g₂ g₁' g₂')
    (hk : SymbolTwoBranch a b Mk Mk' g₃ g₄ g₃' g₄')
    {Θ'' : ℝ → ℝ} (hΘc : ContinuousOn Θ'' (Icc a b))
    (hΘ : ∀ x ∈ Icc a b, |Θ'' x| ≤ N / x ^ 3)
    {p q r t p' q' r' t' : ℝ → ℝ}
    (hp : ∀ x ∈ Icc a b, |p x| ≤ Mj / x) (hq : ∀ x ∈ Icc a b, |q x| ≤ Mk / x)
    (hr : ∀ x ∈ Icc a b, |r x| ≤ Mj / x) (ht : ∀ x ∈ Icc a b, |t x| ≤ Mk / x)
    (hp' : ∀ x ∈ Icc a b, |p' x| ≤ Mj' / x ^ 2) (hq' : ∀ x ∈ Icc a b, |q' x| ≤ Mk' / x ^ 2)
    (hr' : ∀ x ∈ Icc a b, |r' x| ≤ Mj' / x ^ 2) (ht' : ∀ x ∈ Icc a b, |t' x| ≤ Mk' / x ^ 2)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hwc : ContinuousOn (fun x => 1 / 2 * (p x * q x + ε * (r x * t x))) (Icc a b))
    (hw'c : ContinuousOn
      (fun x => 1 / 2 * (p' x * q x + p x * q' x + ε * (r' x * t x + r x * t' x))) (Icc a b)) :
    oscBudget a b m (fun x => 1 / 2 * (p x * q x + ε * (r x * t x)))
        (fun x => 1 / 2 * (p' x * q x + p x * q' x + ε * (r' x * t x + r x * t' x))) Θ''
      ≤ 2 * (Mj * Mk) / m + (Mj' * Mk + Mj * Mk') / m
        + (Mj * Mk) * N / (3 * m ^ 2) := by
  refine oscBudget_le_of_symbolBounds ha hab hm (by positivity) (by positivity) hN
    hwc hw'c hΘc (fun x hx => ?_) (fun x hx => ?_) hΘ
  · have hx : (1 : ℝ) ≤ x := le_trans ha hx.1
    exact abs_half_mul_add_le hx hMj hMk (hp _ ‹_›) (hq _ ‹_›) (hr _ ‹_›) (ht _ ‹_›) ε hε
  · have hx : (1 : ℝ) ≤ x := le_trans ha hx.1
    exact abs_half_mul_deriv_le hx hMj hMj' hMk hMk'
      (hp _ ‹_›) (hp' _ ‹_›) (hq _ ‹_›) (hq' _ ‹_›)
      (hr _ ‹_›) (hr' _ ‹_›) (ht _ ‹_›) (ht' _ ‹_›) ε hε

end GaloisForLFunctions.RHTower

end
