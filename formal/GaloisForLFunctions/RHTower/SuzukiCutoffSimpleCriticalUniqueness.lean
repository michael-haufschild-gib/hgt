import GaloisForLFunctions.RHTower.XiCardGateUnification
import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity

/-!
# Suzuki cutoff uniqueness from the simple critical zeros, unconditionally

`suzukiCutoff_eq_zero_of_le_liminf_xiSimpleCriticalRatio` (and its Levinson and
Pratt–Robles–Zaharescu–Zeindler specialisations) assumed a positive lower density of simple
critical zeros.  `two_thirds_le_liminf_xiSimpleCriticalRatio` supplies density `2/3`.
-/

open Filter Topology Complex

namespace RHTower

/-- If the compact `L²` Fourier transform of `f` vanishes at every simple critical-line zero of
`ξ` of positive ordinate outside a finite set, the Suzuki cutoff of `f` is zero. -/
theorem suzukiCutoff_eq_zero_of_simpleCritical_vanish
    {a : ℝ} (ha : 0 ≤ a) (f : SoninL2) (E : Finset ℝ)
    (hvanish : ∀ t : ℝ, t ∉ E → 0 < t → xi (linePt t) = 0 →
      (analyticOrderAt xi (linePt t)).toNat = 1 →
        suzukiCompactL2Fourier a f (t : ℂ) = 0) :
    suzukiCutoff a f = 0 :=
  suzukiCutoff_eq_zero_of_le_liminf_xiSimpleCriticalRatio (by norm_num : (0 : ℝ) < 2 / 3)
    two_thirds_le_liminf_xiSimpleCriticalRatio ha f E hvanish

end RHTower
