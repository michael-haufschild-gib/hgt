import GaloisForLFunctions.HTGeometry.AccretiveSemigroupDecay
import GaloisForLFunctions.HTGeometry.LaplaceSuperpositionBound

/-!
# The two factors of a Laplace slice

Each slice of the Laplace representation of a block resolvent carries two exponential gains, and
both are elementary once the pieces are separated.

*The physical weight sees only the block.*  A profile supported in `[m, m+1]` satisfies
`e^{-sL} ≤ e^{-sm}` there for `s ≥ 0`, so weighting by `e^{-sL}` costs at most `e^{-sm}` in `L²` —
the block index enters the decay rate linearly.

*The semigroup sees only the floor.*  A frequency-dependent generator with a uniform numerical floor
`μ₀` gives `‖e^{-sB(x)}‖ ≤ e^{-μ₀ s}` for every frequency at once, so applying it costs `e^{-μ₀ s}`
in `L²` uniformly.

Multiplying, the slice decays at rate `μ₀ + m`: the floor and the block index *add*, which is why
the constant produced by the superposition bound is `(μ₀ + m)^{-1}` and is uniform once the
threshold `X_m` is chosen so that the floor grows with the block.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- **The block weight costs `e^{-sm}`.** -/
theorem lintegral_sq_exp_weight_block_le {g : ℝ → X} {m s : ℝ} (hs : 0 ≤ s)
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) :
    (∫⁻ L : ℝ, ‖Real.exp (-s * L) • g L‖ₑ ^ 2)
      ≤ ENNReal.ofReal (Real.exp (-(2 * s * m))) * ∫⁻ L : ℝ, ‖g L‖ₑ ^ 2 := by
  have hpt : ∀ L : ℝ, ‖Real.exp (-s * L) • g L‖ₑ ^ 2
      ≤ ENNReal.ofReal (Real.exp (-(2 * s * m))) * ‖g L‖ₑ ^ 2 := by
    intro L
    by_cases hL : L ∈ Icc m (m + 1)
    · have hLm : m ≤ L := hL.1
      have hexp : Real.exp (-s * L) ≤ Real.exp (-s * m) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith [hs, hLm]
      have hnn : (0 : ℝ) ≤ Real.exp (-s * L) := (Real.exp_pos _).le
      have hnorm : ‖Real.exp (-s * L) • g L‖ₑ
          ≤ ENNReal.ofReal (Real.exp (-s * m)) * ‖g L‖ₑ := by
        rw [enorm_smul, Real.enorm_eq_ofReal hnn]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal hexp) le_rfl
      calc ‖Real.exp (-s * L) • g L‖ₑ ^ 2
          ≤ (ENNReal.ofReal (Real.exp (-s * m)) * ‖g L‖ₑ) ^ 2 := pow_le_pow_left' hnorm 2
        _ = ENNReal.ofReal (Real.exp (-(2 * s * m))) * ‖g L‖ₑ ^ 2 := by
            have hexp2 : Real.exp (-s * m) ^ 2 = Real.exp (-(2 * s * m)) := by
              rw [← Real.exp_nat_mul]
              congr 1
              push_cast
              ring
            rw [mul_pow, ← ENNReal.ofReal_pow (Real.exp_pos _).le, hexp2]
    · rw [hsupp L hL]
      simp
  exact le_trans (lintegral_mono hpt)
    (le_of_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top))

/-- **The semigroup costs `e^{-μ₀ s}` wherever the floor holds.**  The profile is required to vanish
off the region where the floor is available, which is what lets a frequency threshold enter: below it
the profile is not seen at all. -/
theorem lintegral_sq_semigroup_apply_le {B : ℝ → (X →L[ℂ] X)} {μ₀ s : ℝ} {A : Set ℝ}
    (hB : ∀ x ∈ A, ∀ u : X, μ₀ * ‖u‖ ^ 2 ≤ (inner ℂ (B x u) u).re) (hs : 0 ≤ s) (v : ℝ → X)
    (hsupp : ∀ x, x ∉ A → v x = 0) :
    (∫⁻ x : ℝ, ‖accretiveSemigroup (B x) s (v x)‖ₑ ^ 2)
      ≤ ENNReal.ofReal (Real.exp (-(2 * μ₀ * s))) * ∫⁻ x : ℝ, ‖v x‖ₑ ^ 2 := by
  have hpt : ∀ x : ℝ, ‖accretiveSemigroup (B x) s (v x)‖ₑ ^ 2
      ≤ ENNReal.ofReal (Real.exp (-(2 * μ₀ * s))) * ‖v x‖ₑ ^ 2 := by
    intro x
    by_cases hx : x ∈ A
    swap
    · rw [hsupp x hx]
      simp
    have hbase := norm_accretiveSemigroup_apply_le (hB x hx) (v x) hs
    have hnn : (0 : ℝ) ≤ Real.exp (-(μ₀ * s)) := (Real.exp_pos _).le
    have hnorm : ‖accretiveSemigroup (B x) s (v x)‖ₑ
        ≤ ENNReal.ofReal (Real.exp (-(μ₀ * s))) * ‖v x‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hnn]
      exact ENNReal.ofReal_le_ofReal hbase
    calc ‖accretiveSemigroup (B x) s (v x)‖ₑ ^ 2
        ≤ (ENNReal.ofReal (Real.exp (-(μ₀ * s))) * ‖v x‖ₑ) ^ 2 := pow_le_pow_left' hnorm 2
      _ = ENNReal.ofReal (Real.exp (-(2 * μ₀ * s))) * ‖v x‖ₑ ^ 2 := by
          have hexp2 : Real.exp (-(μ₀ * s)) ^ 2 = Real.exp (-(2 * μ₀ * s)) := by
            rw [← Real.exp_nat_mul]
            congr 1
            push_cast
            ring
          rw [mul_pow, ← ENNReal.ofReal_pow (Real.exp_pos _).le, hexp2]
  exact le_trans (lintegral_mono hpt)
    (le_of_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top))

/-- **The two gains multiply.**  A slice built from a block profile and the semigroup decays at the
sum of the two rates. -/
theorem lintegral_sq_slice_le {B : ℝ → (X →L[ℂ] X)} {μ₀ s m : ℝ} {A : Set ℝ}
    (hB : ∀ x ∈ A, ∀ u : X, μ₀ * ‖u‖ ^ 2 ≤ (inner ℂ (B x u) u).re) (hs : 0 ≤ s)
    {w : ℝ → X} {E : ℝ≥0∞} (hsupp : ∀ x, x ∉ A → w x = 0)
    (hw : (∫⁻ x : ℝ, ‖w x‖ₑ ^ 2) ≤ ENNReal.ofReal (Real.exp (-(2 * s * m))) * E) :
    (∫⁻ x : ℝ, ‖accretiveSemigroup (B x) s (w x)‖ₑ ^ 2)
      ≤ ENNReal.ofReal (Real.exp (-(2 * (μ₀ + m) * s))) * E := by
  have hstep := lintegral_sq_semigroup_apply_le hB hs w hsupp
  refine hstep.trans ?_
  refine le_trans (mul_le_mul' le_rfl hw) (le_of_eq ?_)
  have hadd : Real.exp (-(2 * μ₀ * s)) * Real.exp (-(2 * s * m))
      = Real.exp (-(2 * (μ₀ + m) * s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, hadd]

/-! ## `(22)` in block form -/

/-- **`(22)`: the block boundary term is `L²`-bounded with the block-independent constant.**  The
numerical floor and the block index add in the slice decay rate, so the superposition constant is
`(μ₀ + m)^{-1}`; choosing the frequency threshold so that the floor grows with the block makes it
uniform in the block. -/
theorem lintegral_sq_blockLaplace_le {B : ℝ → (X →L[ℂ] X)} {μ₀ m K : ℝ} {A : Set ℝ}
    (hB : ∀ x ∈ A, ∀ u : X, μ₀ * ‖u‖ ^ 2 ≤ (inner ℂ (B x u) u).re)
    (hgap : 0 < μ₀ + m) (hK : 0 ≤ K)
    {Φ : ℝ → X} {Ψ : ℝ → ℝ → X} (hsupp : ∀ s : ℝ, ∀ x, x ∉ A → Ψ x s = 0)
    (hmeas : Measurable
      (Function.uncurry fun (x : ℝ) (s : ℝ) => ‖accretiveSemigroup (B x) s (Ψ x s)‖ₑ))
    (hΦ : ∀ x : ℝ, ‖Φ x‖ₑ ≤ ∫⁻ s in Ioi (0 : ℝ), ‖accretiveSemigroup (B x) s (Ψ x s)‖ₑ)
    (hslice : ∀ s : ℝ, 0 < s →
      (∫⁻ x : ℝ, ‖Ψ x s‖ₑ ^ 2) ≤ ENNReal.ofReal (Real.exp (-(2 * s * m))) * ENNReal.ofReal (K ^ 2)) :
    (∫⁻ x : ℝ, ‖Φ x‖ₑ ^ 2) ^ ((1 : ℝ) / 2) ≤ ENNReal.ofReal (K / (μ₀ + m)) := by
  refine GaloisForLFunctions.HTGeometry.lintegral_sq_laplaceSuperposition_le_ray
    hK hgap hmeas hΦ fun s hs => ?_
  have hsq := lintegral_sq_slice_le hB hs.le (hsupp s) (hslice s hs)
  have hval : ENNReal.ofReal (Real.exp (-(2 * (μ₀ + m) * s))) * ENNReal.ofReal (K ^ 2)
      = ENNReal.ofReal (K * Real.exp (-(μ₀ + m) * s)) ^ 2 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ K * Real.exp (-(μ₀ + m) * s))]
    congr 1
    have hexp : Real.exp (-(μ₀ + m) * s) ^ 2 = Real.exp (-(2 * (μ₀ + m) * s)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [mul_pow, hexp]
    ring
  calc (∫⁻ x : ℝ, ‖accretiveSemigroup (B x) s (Ψ x s)‖ₑ ^ 2) ^ ((1 : ℝ) / 2)
      ≤ (ENNReal.ofReal (Real.exp (-(2 * (μ₀ + m) * s))) * ENNReal.ofReal (K ^ 2)) ^
          ((1 : ℝ) / 2) := ENNReal.rpow_le_rpow hsq (by norm_num)
    _ = (ENNReal.ofReal (K * Real.exp (-(μ₀ + m) * s)) ^ 2) ^ ((1 : ℝ) / 2) := by rw [hval]
    _ = ENNReal.ofReal (K * Real.exp (-(μ₀ + m) * s)) := by
        rw [← ENNReal.rpow_natCast (ENNReal.ofReal (K * Real.exp (-(μ₀ + m) * s))) 2,
          ← ENNReal.rpow_mul]
        norm_num

end GaloisForLFunctions.RHTower
