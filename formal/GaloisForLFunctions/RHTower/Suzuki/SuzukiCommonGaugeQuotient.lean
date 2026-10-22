import GaloisForLFunctions.RHTower.Suzuki.SuzukiDonoghueSpectralMeasure

/-!
# The common gauge cancels in the meromorphic carrier

Entire-pair normality is convergence of the two parity functions *after* a common zero-free gauge,

`(g_n W_{n,1}, g_n W_{n,-1}) -> (W_1, W_{-1})`.

The carrier is their ratio, and the gauge cancels there because it is zero-free.  So the carrier
converges to the ratio of the limits wherever the limiting denominator does not vanish, with no
hypothesis on the gauge beyond being zero-free — in particular no convergence of the gauge itself.

This is what lets the pair converge before the ratio is taken, retaining zeros and poles instead of
passing to a malformed entire-to-meromorphic limit.
-/

namespace GaloisForLFunctions.RHTower

open Filter Topology

/-- **The common gauge cancels in a quotient limit.**  If a zero-free gauge makes both numerator and
denominator converge, the ungauged quotient converges to the quotient of the limits. -/
theorem tendsto_commonGauge_quotient {ι : Type*} {l : Filter ι}
    {F G g : ι → ℂ} {Flim Glim : ℂ}
    (hg : ∀ i, g i ≠ 0)
    (hF : Tendsto (fun i => g i * F i) l (nhds Flim))
    (hG : Tendsto (fun i => g i * G i) l (nhds Glim))
    (hGne : Glim ≠ 0) :
    Tendsto (fun i => F i / G i) l (nhds (Flim / Glim)) := by
  have hEq : (fun i => F i / G i) = fun i => (g i * F i) / (g i * G i) := by
    funext i
    rw [mul_div_mul_left _ _ (hg i)]
  rw [hEq]
  exact hF.div hG hGne

/-- **`(13)`.**  The Suzuki meromorphic carrier is the gauged pair's ratio times `-i`, so
common-gauge entire-pair convergence gives carrier convergence away from the limiting poles. -/
theorem tendsto_suzukiMeromorphicCarrier {ι : Type*} {l : Filter ι}
    {Wodd Weven g : ι → ℂ} {Woddlim Wevenlim : ℂ}
    (hg : ∀ i, g i ≠ 0)
    (hodd : Tendsto (fun i => g i * Wodd i) l (nhds Woddlim))
    (heven : Tendsto (fun i => g i * Weven i) l (nhds Wevenlim))
    (hne : Wevenlim ≠ 0) :
    Tendsto (fun i => -Complex.I * (Wodd i / Weven i)) l
      (nhds (-Complex.I * (Woddlim / Wevenlim))) :=
  (tendsto_commonGauge_quotient hg hodd heven hne).const_mul _

/-- Pointwise form on a spectral parameter: the same statement for families of functions evaluated
at a point off the limiting pole set. -/
theorem tendsto_suzukiMeromorphicCarrier_at {ι : Type*} {l : Filter ι} {z : ℂ}
    {Wodd Weven g : ι → ℂ → ℂ} {Woddlim Wevenlim : ℂ → ℂ}
    (hg : ∀ i, g i z ≠ 0)
    (hodd : Tendsto (fun i => g i z * Wodd i z) l (nhds (Woddlim z)))
    (heven : Tendsto (fun i => g i z * Weven i z) l (nhds (Wevenlim z)))
    (hne : Wevenlim z ≠ 0) :
    Tendsto (fun i => -Complex.I * (Wodd i z / Weven i z)) l
      (nhds (-Complex.I * (Woddlim z / Wevenlim z))) :=
  tendsto_suzukiMeromorphicCarrier hg hodd heven hne

/-- The gauge need not converge, and no relation between the two gauged limits is used: only that
the gauge is zero-free.  Recorded as the invariance of the ungauged ratio. -/
theorem quotient_eq_gauged_quotient {ι : Type*} {F G g : ι → ℂ} (hg : ∀ i, g i ≠ 0) (i : ι) :
    F i / G i = (g i * F i) / (g i * G i) := by
  rw [mul_div_mul_left _ _ (hg i)]

end GaloisForLFunctions.RHTower
