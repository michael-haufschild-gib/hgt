/-
# The reduced energy `W` is convex on a pole-free gap

The deviation identity `½ − θ*(i) = g(i)/(W(ξ)·δ)` (`cothField_theta_deviation`) carries a mean-value
point `ξ` strictly between the equilibrium `x*` and the midpoint `m`. Replacing `W(ξ)` by the clean
`W(m)` — whose limit is the near-pole steepness `π²/c` — needs `W(ξ)/W(m) → 1`. The structural fact
that makes this possible is that `W` is **convex** on the gap: it is slowly varying near its minimum,
where both `x*` and `m` sit as `i → ∞`.

* `rcsch_sq_convexOn` : `rcsch² = 1/sinh²` is convex on `[a,∞)` (`a > 0`), from its derivative
  `−2·rphi` being monotone (`rphi` antitone on `Ioi 0`).
* `rphi_neg`, `rphi_antitoneOn_Iio` : `rphi = rcsch²·rcoth` is odd, hence antitone on `Iio 0` too.
* `spurLatticeEnergy_convexOn` : the field energy `W = ¼Σ_k rcsch²((x−t_k)/2)` is convex on the
  pole-free gap `(a,b)`. Its derivative `W′ = −¼Σ_k rphi((x−t_k)/2)` (`spurLatticeEnergy_hasDerivAt`)
  is monotone because each `rphi((x−t_k)/2)` is antitone on the gap (behind poles keep the argument in
  `Ioi 0`, ahead poles in `Iio 0`; `rphi` is antitone on each).
-/
import GaloisForLFunctions.RHTower.SpurLattice
open Real Set
noncomputable section
namespace RHTower

/-- `rcsch² = 1/sinh²` is convex on `[a,∞)` for `a > 0`: its derivative `−2·rphi` is monotone since
`rphi` is antitone on the positive reals. -/
theorem rcsch_sq_convexOn {a : ℝ} (ha : 0 < a) :
    ConvexOn ℝ (Ici a) (fun x => (rcsch x)^2) := by
  apply MonotoneOn.convexOn_of_deriv (convex_Ici a)
  · apply ContinuousOn.pow
    apply ContinuousOn.div continuousOn_const (Real.continuous_sinh.continuousOn)
    intro x hx
    rw [mem_Ici] at hx
    exact (Real.sinh_pos_iff.mpr (by linarith)).ne'
  · rw [interior_Ici]
    intro x hx
    rw [mem_Ioi] at hx
    exact (rcsch_sq_hasDerivAt (by linarith : x ≠ 0)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro x hx y hy hxy
    rw [mem_Ioi] at hx hy
    rw [(rcsch_sq_hasDerivAt (by linarith : x ≠ 0)).deriv,
        (rcsch_sq_hasDerivAt (by linarith : y ≠ 0)).deriv]
    have hanti := rphi_strictAntiOn_pos.antitoneOn (mem_Ioi.mpr (by linarith : (0:ℝ) < x))
      (mem_Ioi.mpr (by linarith : (0:ℝ) < y)) hxy
    linarith

/-- `rphi = rcsch²·rcoth` is odd. -/
theorem rphi_neg (x : ℝ) : rphi (-x) = - rphi x := by
  simp only [rphi, rcsch, rcoth, Real.sinh_neg, Real.cosh_neg]
  field_simp

/-- `rphi` is antitone on the negative reals (odd, and antitone on the positives). -/
theorem rphi_antitoneOn_Iio : AntitoneOn rphi (Iio 0) := by
  intro u hu v hv huv
  rw [mem_Iio] at hu hv
  have h := rphi_strictAntiOn_pos.antitoneOn (mem_Ioi.mpr (by linarith : (0:ℝ) < -v))
    (mem_Ioi.mpr (by linarith : (0:ℝ) < -u)) (by linarith)
  have eu : rphi u = -rphi (-u) := by have := rphi_neg (-u); simpa using this
  have ev : rphi v = -rphi (-v) := by have := rphi_neg (-v); simpa using this
  rw [eu, ev]; linarith

/-- **The reduced energy `W` is convex on a pole-free gap.** `W′ = −¼Σ rphi((x−t_k)/2)` is monotone
because each `rphi((x−t_k)/2)` is antitone on the gap (behind poles: argument in `Ioi 0`; ahead poles:
`Iio 0`). Convexity is what makes `W` slowly varying near its minimum, where the equilibrium and the
midpoint both sit. -/
theorem spurLatticeEnergy_convexOn {ι : Type*} (s : Finset ι) (t : ι → ℝ) {a b : ℝ}
    (hpoles : ∀ k ∈ s, t k ≤ a ∨ b ≤ t k) :
    ConvexOn ℝ (Ioo a b) (spurLatticeEnergy s t) := by
  apply MonotoneOn.convexOn_of_deriv (convex_Ioo a b)
  · intro x hx
    exact (spurLatticeEnergy_hasDerivAt s t hpoles hx).continuousAt.continuousWithinAt
  · rw [interior_Ioo]
    intro x hx
    exact (spurLatticeEnergy_hasDerivAt s t hpoles hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo]
    intro x hx y hy hxy
    rw [(spurLatticeEnergy_hasDerivAt s t hpoles hx).deriv,
        (spurLatticeEnergy_hasDerivAt s t hpoles hy).deriv]
    rw [mem_Ioo] at hx hy
    have hsum : ∑ k ∈ s, rphi ((y - t k) / 2) ≤ ∑ k ∈ s, rphi ((x - t k) / 2) := by
      apply Finset.sum_le_sum
      intro k hk
      rcases hpoles k hk with h | h
      · have hxp : (0:ℝ) < (x - t k)/2 := by linarith [hx.1]
        have hyp : (0:ℝ) < (y - t k)/2 := by linarith [hy.1]
        exact rphi_strictAntiOn_pos.antitoneOn (mem_Ioi.mpr hxp) (mem_Ioi.mpr hyp) (by linarith)
      · have hxn : (x - t k)/2 < 0 := by linarith [hx.2]
        have hyn : (y - t k)/2 < 0 := by linarith [hy.2]
        exact rphi_antitoneOn_Iio (mem_Iio.mpr hxn) (mem_Iio.mpr hyn) (by linarith)
    linarith

end RHTower
end
