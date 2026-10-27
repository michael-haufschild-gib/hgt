import GaloisForLFunctions.ConjugateDiagonalGeometry.ZetaDepthDistribution

/-!
# The Hecke defect is the moment of inertia

The collided form `D(f) = Σ m_ρ |f̂(ρ)|²` is the energy of the zero divisor weighted by `|f̂|²`.
A Hecke translation by `L` reweights each charge by `e^{2δL}`, `δ = Re ρ − ½`, and the symmetric
equivariance defect is `E_f(L) = Σ m (2 cosh(2δL) − 2)|f̂(ρ)|²` (`heckeDefect`). Its electrostatic
content is one number: the **transverse moment of inertia** of the weighted divisor about the
critical line, `M_f = Σ m δ² |f̂(ρ)|²` (`depthSecondMoment`).

* **Scale comparison** (`depthKernel_le_mul_half`): on the strip, `|δ| ≤ ½`,
  `2 cosh(2δL) − 2 ≤ 4δ² (2 cosh L − 2)`, termwise from the cosine-hyperbolic series.
* **The defect is the moment of inertia at every scale** (`heckeDefect_le_moment`,
  `moment_le_heckeDefect`): `4L² M_f ≤ E_f(L) ≤ 8(cosh L − 1) M_f`.
* **The infinitesimal defect** (`tendsto_heckeDefect_div_sq`): `E_f(L)/L² → 4 M_f` as `L → 0`.

So a bound on the equivariance defect of `D` at one scale is, up to the explicit factor between
`4L²` and `8(cosh L − 1)`, a bound on the transverse moment of inertia of the divisor seen by the
test: the defect question (B3.33) is a second-moment question about the charges. RH is the
vanishing of every moment of inertia.
-/

noncomputable section

open Filter
open scoped Topology

namespace GaloisForLFunctions.ArithmeticElectrostatics

open GaloisForLFunctions.ConjugateDiagonalGeometry Zeta23 ArithmeticPolarization

/-- `cosh(a y) − 1 ≤ a² (cosh y − 1)` for `a² ≤ 1`: every term of the series of `cosh(ay) − 1`
carries a power `a^{2n}`, `n ≥ 1`. -/
theorem cosh_mul_sub_one_le {a : ℝ} (ha : a ^ 2 ≤ 1) (y : ℝ) :
    Real.cosh (a * y) - 1 ≤ a ^ 2 * (Real.cosh y - 1) := by
  have hf := Real.hasSum_cosh (a * y)
  have hg := ((Real.hasSum_cosh y).mul_left (a ^ 2)).add (hasSum_ite_eq 0 (1 - a ^ 2))
  have hle : ∀ n : ℕ, (a * y) ^ (2 * n) / ((2 * n).factorial : ℝ) ≤
      a ^ 2 * (y ^ (2 * n) / ((2 * n).factorial : ℝ)) + (if n = 0 then 1 - a ^ 2 else 0) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [if_neg hn.ne', add_zero, mul_pow, pow_mul, ← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
      have hy : 0 ≤ y ^ (2 * n) := by rw [pow_mul]; positivity
      refine mul_le_mul_of_nonneg_right ?_ hy
      calc (a ^ 2) ^ n ≤ (a ^ 2) ^ 1 := pow_le_pow_of_le_one (sq_nonneg a) ha hn
        _ = a ^ 2 := pow_one _
  have := hasSum_le hle hf hg
  linarith

/-- **Scale comparison**: on the strip `2 cosh(2δL) − 2 ≤ 4δ² (2 cosh L − 2)`. -/
theorem depthKernel_le_mul_half {d : ℝ} (hd : |d| ≤ 1 / 2) (L : ℝ) :
    depthKernel L d ≤ 4 * d ^ 2 * depthKernel L (1 / 2) := by
  have ha : (2 * d) ^ 2 ≤ 1 := by
    have h := abs_le.mp hd
    nlinarith
  have := cosh_mul_sub_one_le ha L
  unfold depthKernel
  rw [show 2 * (1 / 2 : ℝ) * L = L by ring, show 2 * d * L = (2 * d) * L by ring]
  nlinarith

/-- **Upper bound**: `E_f(L) ≤ 4 (2 cosh L − 2) M_f`. -/
theorem heckeDefect_le_moment (f : CompactTest) (L : ℝ) :
    heckeDefect f L ≤ 4 * depthKernel L (1 / 2) * depthSecondMoment f := by
  rw [depthSecondMoment, ← tsum_mul_left]
  refine (summable_heckeDefect f L).tsum_le_tsum (fun ρ => ?_)
    ((summable_depthSecondMoment f).mul_left _)
  calc zetaWeight f ρ * depthKernel L (zetaDepth ρ)
      ≤ zetaWeight f ρ * (4 * zetaDepth ρ ^ 2 * depthKernel L (1 / 2)) :=
        mul_le_mul_of_nonneg_left (depthKernel_le_mul_half (abs_zetaDepth_le ρ) L)
          (zetaWeight_nonneg f ρ)
    _ = 4 * depthKernel L (1 / 2) * (zetaWeight f ρ * zetaDepth ρ ^ 2) := by ring

/-- **Lower bound** (from `ConjugateDiagonalGeometry`): `4L² M_f ≤ E_f(L)`. -/
theorem moment_le_heckeDefect (f : CompactTest) (L : ℝ) :
    4 * L ^ 2 * depthSecondMoment f ≤ heckeDefect f L :=
  four_mul_secondMoment_le f L

/-- `cosh L − 1 ≤ (L²/2) e^{L²/2}`. -/
theorem cosh_sub_one_le (L : ℝ) : Real.cosh L - 1 ≤ L ^ 2 / 2 * Real.exp (L ^ 2 / 2) := by
  have h1 := Real.cosh_le_exp_half_sq L
  -- `e^u − 1 ≤ u e^u` from `1 − u ≤ e^{−u}`
  have h2 := Real.add_one_le_exp (-(L ^ 2 / 2))
  have hexp : Real.exp (-(L ^ 2 / 2)) * Real.exp (L ^ 2 / 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hpos := Real.exp_pos (L ^ 2 / 2)
  nlinarith

theorem pow_pos_of_ne_zero_sq {L : ℝ} (hL : L ∈ ({0} : Set ℝ)ᶜ) : 0 < L ^ 2 := by
  have : L ≠ 0 := hL
  positivity

/-- **The infinitesimal defect is four times the moment of inertia**: `E_f(L)/L² → 4 M_f`. -/
theorem tendsto_heckeDefect_div_sq (f : CompactTest) :
    Tendsto (fun L => heckeDefect f L / L ^ 2) (𝓝[≠] 0) (𝓝 (4 * depthSecondMoment f)) := by
  have hM : 0 ≤ depthSecondMoment f :=
    tsum_nonneg fun ρ => mul_nonneg (zetaWeight_nonneg f ρ) (sq_nonneg (zetaDepth ρ))
  have hup : Tendsto (fun L : ℝ => 4 * depthSecondMoment f * Real.exp (L ^ 2 / 2)) (𝓝[≠] 0)
      (𝓝 (4 * depthSecondMoment f)) := by
    have hc : Continuous fun L : ℝ => 4 * depthSecondMoment f * Real.exp (L ^ 2 / 2) := by
      fun_prop
    have := hc.tendsto 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, Real.exp_zero,
      mul_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with L hL
    have hL2 : 0 < L ^ 2 := pow_pos_of_ne_zero_sq hL
    rw [le_div_iff₀ hL2]
    linarith [moment_le_heckeDefect f L]
  · filter_upwards [self_mem_nhdsWithin] with L hL
    have hL2 : 0 < L ^ 2 := pow_pos_of_ne_zero_sq hL
    rw [div_le_iff₀ hL2]
    have h1 := heckeDefect_le_moment f L
    have h2 := cosh_sub_one_le L
    have hk : depthKernel L (1 / 2) = 2 * (Real.cosh L - 1) := by
      unfold depthKernel; rw [show 2 * (1 / 2 : ℝ) * L = L by ring]; ring
    rw [hk] at h1
    nlinarith [mul_le_mul_of_nonneg_left h2 hM]

end GaloisForLFunctions.ArithmeticElectrostatics
