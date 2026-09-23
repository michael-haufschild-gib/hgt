import GaloisForLFunctions.RHTower.ProlateApertureMassSharp
import GaloisForLFunctions.RHTower.BandBarrierRatio

/-!
# The barrier ratio, two-sided, at the sharp action

The card's stated bottleneck for the Fuchs asymptotic is the barrier ratio `Phi(y₀)/Phi(1)` to
relative precision `c^(±3/2)`.  Both directions are now available at the sharp exponential rate with
polynomial prefactors:

```text
exp(c Xi_s(y₀) + 6 log((1−alpha)/(1−y₀))) / (6 pi sqrt(c Xi_s(alpha)))
      <=  Phi(y₀)  <=  sqrt(C · exp(Lambda)) · exp(c Xi_s(y₀))
```

with `C = 1 + (1−alpha²)(barrier(alpha) + 6/(1−alpha))²/(c²(alpha²−s))` bounded and
`Lambda = prolateScaleLog s y₀ alpha` the logarithm of the band-scale ratio.  Both exponentials are
the *same* `exp(c Xi_s(y₀))`, so the ratio of the two bounds is the product of the two prefactors —
`sqrt(exp Lambda)` and `sqrt(c Xi_s(alpha))`, each `O(sqrt c)` for a fixed mode, hence `O(c)` in
total, comfortably inside `c^(3/2)`.

The upper bound is the loss-free endpoint transport composed with the variable-scale amplitude
envelope; the lower bound is the corpus's `I₀`-model collar comparison composed with the Riccati
transport corrected by `6/(1−y)`.
-/

noncomputable section

open Set MeasureTheory

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

open GaloisForLFunctions.HTGeometry

/-- **The barrier ratio from above at a band point.**  The amplitude at the band scale carries the
value from the collar anchor down to any point of the band; the anchor value is the loss-free
endpoint bound. -/
theorem prolateBand_sq_le_exp_bandPhase {c s y₀ α : ℝ} {Φ DΦ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 < s) (hs1 : s < 1) (hcs : 4 ≤ c * s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1)
    (hsy0 : s < y₀ ^ (2 : ℕ)) (hy00 : 0 < y₀) (hy0α : y₀ ≤ α) (hα1 : α < 1)
    (houter : ∀ t ∈ Icc α 1, c ^ (2 : ℕ) * (1 - 2 * t ^ (2 : ℕ)) ≤ -(s * c ^ (2 : ℕ)))
    (hposΦ : ∀ t ∈ Icc y₀ 1, 0 < Φ t)
    (hΦd : ∀ t, HasDerivAt Φ (DΦ t) t)
    (hfluxd : ∀ t ∈ Icc y₀ α, HasDerivAt (fun u => (1 - u ^ (2 : ℕ)) * DΦ u)
      (-(c ^ (2 : ℕ) * (s - t ^ (2 : ℕ)) * Φ t)) t) :
    Φ y₀ ^ (2 : ℕ)
      ≤ (1 + (1 - α ^ (2 : ℕ)) * (prolateRadialBarrier c s α + 6 / (1 - α)) ^ (2 : ℕ)
            / (c ^ (2 : ℕ) * (α ^ (2 : ℕ) - s)))
        * Real.exp (2 * c * bandEndpointPhase s y₀ + prolateScaleLog s y₀ α) := by
  have hα0 : 0 < α := lt_of_lt_of_le hy00 hy0α
  have hsα : s < α ^ (2 : ℕ) := by nlinarith [hy0α, hy00]
  have hαpos : ∀ u ∈ Icc α 1, 0 < Φ u := fun u hu =>
    hposΦ u ⟨le_trans hy0α hu.1, hu.2⟩
  have hQα : ∀ t ∈ Icc α 1, 0 < -(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * t ^ (2 : ℕ) := by
    intro t ht
    have hsqt : α ^ (2 : ℕ) ≤ t ^ (2 : ℕ) := by nlinarith [ht.1, hα0]
    nlinarith [mul_pos (pow_pos hc 2) (sub_pos.2 hsα)]
  -- the anchor value
  have hΦα : Φ α ≤ Real.exp (c * bandEndpointPhase s α) := by
    have := prolate_anchor_le_exp_bandPhase hsm heig hc hs1 hsα.le hα0.le hα1 hαpos hQα houter
    rwa [hΦ1, one_mul] at this
  have hB := abs_prolateLogDeriv_le_band hc hs0.le hs1 hcs hsm heig hΦ1 hα0 hα1 hsα hαpos
  have hGα := prolateBandAmplitude_anchor_le (c := c) (s := s) (α := α)
    (B := prolateRadialBarrier c s α + 6 / (1 - α)) hc hα0.le hα1 hsα
    (hαpos α ⟨le_rfl, hα1.le⟩) hΦd hB
  set C : ℝ := 1 + (1 - α ^ (2 : ℕ)) * (prolateRadialBarrier c s α + 6 / (1 - α)) ^ (2 : ℕ)
      / (c ^ (2 : ℕ) * (α ^ (2 : ℕ) - s)) with hCdef
  have hCnn : 0 ≤ C := by
    have h1 : (0 : ℝ) < α ^ (2 : ℕ) - s := by linarith
    have h2 : (0 : ℝ) < 1 - α ^ (2 : ℕ) := by nlinarith
    rw [hCdef]
    positivity
  have hΦαnn : 0 ≤ Φ α := (hαpos α ⟨le_rfl, hα1.le⟩).le
  have hZ : Φ α ^ (2 : ℕ) ≤ Real.exp (2 * (c * bandEndpointPhase s α)) := by
    have hsq := pow_le_pow_left₀ hΦαnn hΦα 2
    have hval : Real.exp (c * bandEndpointPhase s α) ^ (2 : ℕ)
        = Real.exp (2 * (c * bandEndpointPhase s α)) := by
      rw [two_mul, Real.exp_add, sq]
    rwa [hval] at hsq
  have hGZ : prolateBandAmplitude c s Φ DΦ α
      ≤ C * Real.exp (2 * (c * bandEndpointPhase s α)) := by
    refine le_trans hGα ?_
    have := mul_le_mul_of_nonneg_right hZ hCnn
    linarith [this]
  -- the transport to `y₀`
  have hposband : ∀ t ∈ Icc y₀ α, Φ t ≠ 0 := fun t ht =>
    (hposΦ t ⟨ht.1, le_trans ht.2 hα1.le⟩).ne'
  have hband := prolateBandAmplitude_le_uniform (c := c) (s := s) (y := y₀) hc hy00 hsy0
    le_rfl hy0α hα1 hΦd hfluxd hposband
  have hsq : Φ y₀ ^ (2 : ℕ) ≤ prolateBandAmplitude c s Φ DΦ y₀ := by
    have hK : 0 < prolateBandScale c s y₀ :=
      prolateBandScale_pos hc hsy0 (by nlinarith [hy0α, hα1, hy00])
    exact sq_le_sturmAmplitudeVar hK
  -- assemble the exponents
  set X : ℝ := 2 * c * (bandEndpointPhase s y₀ - bandEndpointPhase s α)
      + prolateScaleLog s y₀ α with hXdef
  set Z : ℝ := 2 * (c * bandEndpointPhase s α) with hZdef
  have hsum : Z + X = 2 * c * bandEndpointPhase s y₀ + prolateScaleLog s y₀ α := by
    rw [hZdef, hXdef]
    ring
  have hexpX : (0 : ℝ) < Real.exp X := Real.exp_pos _
  clear_value X Z
  calc Φ y₀ ^ (2 : ℕ) ≤ prolateBandAmplitude c s Φ DΦ y₀ := hsq
    _ ≤ prolateBandAmplitude c s Φ DΦ α * Real.exp X := hband
    _ ≤ (C * Real.exp Z) * Real.exp X := mul_le_mul_of_nonneg_right hGZ hexpX.le
    _ = C * (Real.exp Z * Real.exp X) := mul_assoc _ _ _
    _ = C * Real.exp (Z + X) := by rw [← Real.exp_add]
    _ = C * Real.exp (2 * c * bandEndpointPhase s y₀ + prolateScaleLog s y₀ α) := by rw [hsum]

/-- **The barrier ratio, two-sided.**  Both bounds carry the same sharp exponential
`exp(c Xi_s(y₀))`; the gap between them is the product of the two polynomial prefactors. -/
theorem prolateBand_barrier_ratio_two_sided {c s y₀ α : ℝ} {Φ DΦ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 < s) (hs8 : s ≤ 1 / 8) (hcs : 4 ≤ c * s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1)
    (hsy0 : s < y₀ ^ (2 : ℕ)) (hy00 : 0 < y₀) (hy0α : y₀ ≤ α)
    (hα : 1 / 2 < α) (hα1 : α < 1) (hcollar : 600 * (1 - α) ≤ 1 / 4)
    (hz : 1 ≤ c * bandEndpointPhase s α)
    (houter : ∀ t ∈ Icc α 1, c ^ (2 : ℕ) * (1 - 2 * t ^ (2 : ℕ)) ≤ -(s * c ^ (2 : ℕ)))
    (hposΦ : ∀ t ∈ Icc y₀ 1, 0 < Φ t)
    (hΦd : ∀ t, HasDerivAt Φ (DΦ t) t)
    (hfluxd : ∀ t ∈ Icc y₀ α, HasDerivAt (fun u => (1 - u ^ (2 : ℕ)) * DΦ u)
      (-(c ^ (2 : ℕ) * (s - t ^ (2 : ℕ)) * Φ t)) t) :
    Real.exp (c * bandEndpointPhase s y₀ + 6 * (Real.log (1 - α) - Real.log (1 - y₀)))
          / (6 * Real.pi * Real.sqrt (c * bandEndpointPhase s α)) ≤ Φ y₀ ∧
      Φ y₀ ^ (2 : ℕ)
        ≤ (1 + (1 - α ^ (2 : ℕ)) * (prolateRadialBarrier c s α + 6 / (1 - α)) ^ (2 : ℕ)
              / (c ^ (2 : ℕ) * (α ^ (2 : ℕ) - s)))
          * Real.exp (2 * c * bandEndpointPhase s y₀ + prolateScaleLog s y₀ α) := by
  refine ⟨?_, prolateBand_sq_le_exp_bandPhase hc hs0 (by linarith) hcs hsm heig hΦ1 hsy0 hy00
    hy0α hα1 houter hposΦ hΦd hfluxd⟩
  exact prolateBand_barrier_ratio_lower (s := s) (c := c) (α := α) (y₀ := y₀) (Φ := Φ)
    hs0.le hs8 hc hα hα1 hcollar hsm heig hΦ1 hy00.le hy0α hsy0 hposΦ hz

end GaloisForLFunctions.RHTower

end
