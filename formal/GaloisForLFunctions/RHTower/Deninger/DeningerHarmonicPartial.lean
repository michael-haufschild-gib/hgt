import GaloisForLFunctions.RHTower.Deninger.DeningerMobiusHarmonic
import GaloisForLFunctions.RHTower.Deninger.DeningerAbelianLimit

/-!
# The Möbius harmonic partial sums as an Abel input

The partial sums `A_N = ∑_{n ≤ N} μ(n)/n` converge, hence are bounded, hence the Abel boundary term
`A_N N^{-σ}` vanishes for every positive exponent.  Shifting the index by one — which is what Abel
summation produces when the `n = 0` term is dropped — does not change the limit.

These are the inputs that turn the Dirichlet series `∑ μ(n) n^{-1-σ}` into an Abel average of the
partial sums, to which the Abelian limit theorem applies.

* `deningerHarmonicPartial` : the partial sums `A_N`.
* `deningerHarmonicPartial_bounded` : they are bounded.
* `deningerHarmonicBoundary_tendsto_zero` : **the Abel boundary term vanishes.**
* `deningerHarmonicShift_tendsto` : the shifted partial sums have the same limit.
-/

namespace RHTower

open ArithmeticFunction Filter Topology

noncomputable section

/-- The Möbius harmonic partial sums. -/
def deningerHarmonicPartial (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), ((moebius n : ℤ) : ℝ) / (n : ℝ)

/-- The limit of the Möbius harmonic partial sums. -/
def deningerHarmonicLimit : ℝ :=
  ∑' i : ℕ, Sieve.mertensM i / ((i : ℝ) * ((i : ℝ) + 1))

theorem deningerHarmonicPartial_tendsto :
    Tendsto deningerHarmonicPartial atTop (𝓝 deningerHarmonicLimit) :=
  deningerMobiusHarmonic_tendsto

/-- The partial sums are bounded, being convergent. -/
theorem deningerHarmonicPartial_bounded :
    ∃ C : ℝ, ∀ N, |deningerHarmonicPartial N| ≤ C :=
  deningerBounded_of_tendsto deningerHarmonicPartial_tendsto

/-- **The Abel boundary term vanishes** for every positive exponent. -/
theorem deningerHarmonicBoundary_tendsto_zero {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun N : ℕ => deningerHarmonicPartial N * ((N : ℝ) ^ (-σ))) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := deningerHarmonicPartial_bounded
  have hCnn : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  have hpow : Tendsto (fun N : ℕ => ((N : ℝ) ^ (-σ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hσ).comp tendsto_natCast_atTop_atTop
  have hmaj : Tendsto (fun N : ℕ => C * ((N : ℝ) ^ (-σ))) atTop (𝓝 0) := by
    have := hpow.const_mul C
    rwa [mul_zero] at this
  refine squeeze_zero_norm (fun N => ?_) hmaj
  rw [Real.norm_eq_abs, abs_mul]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hz : ((0 : ℕ) : ℝ) ^ (-σ) = 0 := by
      rw [Nat.cast_zero, Real.zero_rpow (ne_of_lt (by linarith : -σ < 0))]
    rw [hz]
    simp
  · have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hpn : (0 : ℝ) < ((N : ℝ) ^ (-σ)) := Real.rpow_pos_of_pos hNr _
    rw [abs_of_pos hpn]
    exact mul_le_mul_of_nonneg_right (hC N) hpn.le

/-- Shifting the index by one does not change the limit. -/
theorem deningerHarmonicShift_tendsto :
    Tendsto (fun m : ℕ => deningerHarmonicPartial (m + 1)) atTop (𝓝 deningerHarmonicLimit) :=
  deningerHarmonicPartial_tendsto.comp (tendsto_add_atTop_nat 1)

/-- **The Abel average of the shifted partial sums converges to the same limit.**  This is the
Abelian limit theorem applied to the Möbius harmonic partial sums; combining it with the Dirichlet
series identity is what pins the value of `∑ μ(n)/n`. -/
theorem deningerHarmonicAbel_tendsto :
    Tendsto (fun σ : ℝ => ∑' m : ℕ, deningerHarmonicPartial (m + 1) * deningerAbelWeight σ m)
      (𝓝[>] 0) (𝓝 deningerHarmonicLimit) :=
  deningerAbelian_tendsto deningerHarmonicShift_tendsto

end

end RHTower
