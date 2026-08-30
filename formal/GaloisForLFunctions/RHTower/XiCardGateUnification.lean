import GaloisForLFunctions.RHTower.XiCensusVonMangoldtBridge
import GaloisForLFunctions.RHTower.XiSimpleCriticalSuperlinearConsumer

/-!
# The two zero-divisor-geometry cards share one gate

The bounded-support Weil uniqueness theorem needs a *superlinear* count of simple critical zeros;
the horizontal-singleton density theorem needs a *positive proportion* of them.  Through the
Riemann–von Mangoldt asymptotic these are the same requirement, so the uniqueness theorem can be
stated directly in density form:

```text
c ≤ liminf N₀,s(T)/N(T),  c > 0
  ⟹  a compactly supported source whose Fourier transform vanishes at all but finitely many
     simple critical ordinates is itself zero.
```

In particular the Pratt–Robles–Zaharescu–Zeindler constant `0.407511457` discharges it.
-/

open Filter Topology Complex

noncomputable section

namespace RHTower

/-- **The bounded-support Weil uniqueness theorem in density form.**  Any positive lower density of
simple critical zeros suffices. -/
theorem suzukiCutoff_eq_zero_of_le_liminf_xiSimpleCriticalRatio
    {c : ℝ} (hc : 0 < c) (h : c ≤ liminf xiSimpleCriticalRatio atTop)
    {a : ℝ} (ha : 0 ≤ a) (f : SoninL2) (E : Finset ℝ)
    (hvanish : ∀ t : ℝ, t ∉ E → 0 < t → xi (linePt t) = 0 →
      (analyticOrderAt xi (linePt t)).toNat = 1 →
        suzukiCompactL2Fourier a f (t : ℂ) = 0) :
    suzukiCutoff a f = 0 := by
  obtain ⟨c', hc', hsuper⟩ := exists_superlinear_of_le_liminf_xiSimpleCriticalRatio hc h
  exact suzukiCutoff_eq_zero_of_superlinear_simpleCritical hc' hsuper ha f E hvanish

/-- The Pratt–Robles–Zaharescu–Zeindler simple-critical density discharges the uniqueness theorem. -/
theorem suzukiCutoff_eq_zero_of_prattRoblesZaharescuZeindler
    (hκs : (0.407511457 : ℝ) ≤ liminf xiSimpleCriticalRatio atTop)
    {a : ℝ} (ha : 0 ≤ a) (f : SoninL2) (E : Finset ℝ)
    (hvanish : ∀ t : ℝ, t ∉ E → 0 < t → xi (linePt t) = 0 →
      (analyticOrderAt xi (linePt t)).toNat = 1 →
        suzukiCompactL2Fourier a f (t : ℂ) = 0) :
    suzukiCutoff a f = 0 :=
  suzukiCutoff_eq_zero_of_le_liminf_xiSimpleCriticalRatio (by norm_num) hκs ha f E hvanish

/-- Levinson's own constant already discharges it: the uniqueness theorem does not need the sharp
Pratt–Robles–Zaharescu–Zeindler density, only *some* positive one. -/
theorem suzukiCutoff_eq_zero_of_levinson
    (hκs : (0.3474 : ℝ) ≤ liminf xiSimpleCriticalRatio atTop)
    {a : ℝ} (ha : 0 ≤ a) (f : SoninL2) (E : Finset ℝ)
    (hvanish : ∀ t : ℝ, t ∉ E → 0 < t → xi (linePt t) = 0 →
      (analyticOrderAt xi (linePt t)).toNat = 1 →
        suzukiCompactL2Fourier a f (t : ℂ) = 0) :
    suzukiCutoff a f = 0 :=
  suzukiCutoff_eq_zero_of_le_liminf_xiSimpleCriticalRatio (by norm_num) hκs ha f E hvanish

end RHTower
