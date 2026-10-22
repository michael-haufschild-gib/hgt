import GaloisForLFunctions.RHTower.XiMassPrimeMaskBoundaryQuotient

/-!
# Dilation masks: prime-power layers as rescaled prime layers

The mass test `g_{a,τ}(x) = exp(-τ √(x² + a²))` satisfies the dilation law
`g_{a,τ}(x) = g_{a/q, qτ}(x/q)` for `q > 0`, so its Fourier transform obeys
`ĝ_{a,τ}(w) = q ĝ_{a/q, qτ}(q w)`. Since `log p^r = r log p`, multiplying the prime atom at `p` by
the dilation mask `m_r(p) = Λ(p^r) p^{-r/2} / (Λ(p) p^{-1/2}) = p^{-(r-1)/2}` produces `r` times
the atom at `p^r` for the rescaled parameters `(a/r, rτ)`. Thus each dilation-masked prime layer is
a rescaled prime-power layer. Every prime-power layer with `r ≥ 2` is bounded on positive vertical
lines (the case `r = 2` uses the prime-square boundary residue; `r ≥ 3` is absolutely summable),
hence so is every dilation-masked layer with `r ≥ 2`.

## Main results

- `stripFourier_xiMassAnalyticTest_dilation`: `ĝ_{a,τ}(w) = q ĝ_{a/q, qτ}(q w)` for `a, q > 0`.
- `xiMassPrimeDilationLayer_eq_primePowerLayer`: for `r > 0`, the `m_r`-masked prime layer at
  `(a, τ)` equals `r` times the `p^r` layer at `(a/r, rτ)`.
- `exists_norm_xiMassPrimePowerLayer_vertical_bound`: for `r ≥ 2`, the prime-power layer
  `∑_p atom(p^r)` is bounded on `Re τ = σ`.
- `exists_norm_xiMassPrimeDilationLayer_vertical_bound`: for `r ≥ 2`, the dilation-masked layer is
  bounded on `Re τ = σ`.
- `norm_xiMassPrimeDilationMask_eq`: `‖m_r(p)‖ = p^{-(r-1)/2}`.
- `summable_norm_xiMassPrimeDilationMask_mul_criticalWeight_high`: for `r ≥ 3`, the mask is
  summable against the critical weights `log p · p^{-1/2}`.

## Hypotheses

All results are unconditional. They use only parameter ranges such as `0 < a`, `0 < q`,
`0 < σ`, `0 < Re τ` and integer constraints `0 < r`, `2 ≤ r` or `3 ≤ r`.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Dilation law of the mass test on the real line: for `a, q > 0`,
`g_{a,τ}(x) = g_{a/q, qτ}(x/q)`. -/
theorem xiMassAnalyticTest_real_dilation
    {a q : ℝ} (ha : 0 < a) (hq : 0 < q)
    (τ : ℂ) (x : ℝ) :
    xiMassAnalyticTest a τ (x : ℂ) =
      xiMassAnalyticTest (a / q) (q * τ) ((x / q : ℝ) : ℂ) := by
  have haq : 0 < a / q := div_pos ha hq
  rw [xiMassAnalyticTest, xiMassAnalyticTest,
    xiMassAnalyticSqrt_ofReal_eq ha,
    xiMassAnalyticSqrt_ofReal_eq haq]
  have hbig : 0 ≤ x ^ 2 + a ^ 2 := by positivity
  have hscale : (x / q) ^ 2 + (a / q) ^ 2 =
      (x ^ 2 + a ^ 2) / q ^ 2 := by field_simp
  have hsqrt : Real.sqrt ((x / q) ^ 2 + (a / q) ^ 2) =
      Real.sqrt (x ^ 2 + a ^ 2) / q := by
    rw [hscale, Real.sqrt_div hbig, Real.sqrt_sq_eq_abs,
      abs_of_pos hq]
  rw [hsqrt]
  congr 1
  push_cast
  field_simp [hq.ne']

/-- Fourier form of the dilation law: for `a, q > 0`, `ĝ_{a,τ}(w) = q ĝ_{a/q, qτ}(q w)`. -/
theorem stripFourier_xiMassAnalyticTest_dilation
    {a q : ℝ} (ha : 0 < a) (hq : 0 < q)
    (τ w : ℂ) :
    stripFourier (xiMassAnalyticTest a τ) w =
      q * stripFourier (xiMassAnalyticTest (a / q) (q * τ)) (q * w) := by
  unfold stripFourier
  let G : ℝ → ℂ := fun y =>
    xiMassAnalyticTest (a / q) (q * τ) (y : ℂ) *
      Complex.exp (-(I * (q * w) * (y : ℂ)))
  have hpoint (x : ℝ) :
      xiMassAnalyticTest a τ (x : ℂ) *
          Complex.exp (-(I * w * (x : ℂ))) =
        G (q⁻¹ * x) := by
    rw [xiMassAnalyticTest_real_dilation ha hq τ x]
    dsimp only [G]
    congr 1
    · congr 1
      push_cast
      field_simp [hq.ne']
    · congr 1
      push_cast
      field_simp [hq.ne']
  rw [show (∫ x : ℝ, xiMassAnalyticTest a τ (x : ℂ) *
        Complex.exp (-(I * w * (x : ℂ)))) =
      ∫ x : ℝ, G (q⁻¹ * x) by
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [MeasureTheory.Measure.integral_comp_inv_mul_left G q,
    abs_of_pos hq]
  simp only [Complex.real_smul]
  rfl

/-- The `r`-th prime-power layer `∑_p atom(p^r)`. -/
def xiMassPrimePowerLayer (r : ℕ) (a : ℝ) (τ : ℂ) : ℂ :=
  ∑' p : Nat.Primes,
    xiMassCenteredPrimeAtom a τ ((p : ℕ) ^ r)

/-- The dilation mask `m_r(p)`: ratio of the critical von Mangoldt terms at `p^r` and at `p`. -/
def xiMassPrimeDilationMask (r : ℕ) (p : Nat.Primes) : ℂ :=
  LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      (1 / 2 : ℂ) ((p : ℕ) ^ r) /
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      (1 / 2 : ℂ) (p : ℕ)

/-- The dilation-masked prime layer `∑_p m_r(p) · atom(p)`. -/
def xiMassPrimeDilationLayer (r : ℕ) (a : ℝ) (τ : ℂ) : ℂ :=
  ∑' p : Nat.Primes,
    xiMassPrimeDilationMask r p *
      xiMassCenteredPrimeAtom a τ (p : ℕ)

/-- For `r > 0` and `a > 0`, `m_r(p) · atom_{a,τ}(p) = r · atom_{a/r, rτ}(p^r)`. -/
theorem xiMassPrimeDilationMask_mul_centeredAtom_eq
    {r : ℕ} (hr : 0 < r) {a : ℝ} (ha : 0 < a)
    (τ : ℂ) (p : Nat.Primes) :
    xiMassPrimeDilationMask r p *
        xiMassCenteredPrimeAtom a τ (p : ℕ) =
      ((r : ℝ) : ℂ) * xiMassCenteredPrimeAtom (a / (r : ℝ))
        (((r : ℝ) : ℂ) * τ) ((p : ℕ) ^ r) := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hF := stripFourier_xiMassAnalyticTest_dilation
    ha hrR τ (Real.log (p : ℕ) : ℂ)
  have hlogpow : Real.log ((((p : ℕ) ^ r : ℕ)) : ℝ) =
      (r : ℝ) * Real.log (p : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  have hlogpowC :
      (Real.log ((((p : ℕ) ^ r : ℕ)) : ℝ) : ℂ) =
        ((r : ℝ) : ℂ) * (Real.log (p : ℝ) : ℂ) := by
    exact_mod_cast hlogpow
  unfold xiMassPrimeDilationMask xiMassCenteredPrimeAtom
  calc
    (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (1 / 2 : ℂ) ((p : ℕ) ^ r) /
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (1 / 2 : ℂ) (p : ℕ)) *
        (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (1 / 2 : ℂ) (p : ℕ) *
          stripFourier (xiMassAnalyticTest a τ)
            (Real.log (p : ℕ) : ℂ)) =
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (1 / 2 : ℂ) ((p : ℕ) ^ r) *
        stripFourier (xiMassAnalyticTest a τ)
          (Real.log (p : ℕ) : ℂ) :=
      div_mul_mul_eq_mul (xiMassPrimeCriticalTerm_ne_zero p)
    _ = LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (1 / 2 : ℂ) ((p : ℕ) ^ r) *
        (((r : ℝ) : ℂ) * stripFourier
          (xiMassAnalyticTest (a / (r : ℝ)) (((r : ℝ) : ℂ) * τ))
          (((r : ℝ) : ℂ) * (Real.log (p : ℕ) : ℂ))) := by rw [hF]
    _ = ((r : ℝ) : ℂ) *
        (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (1 / 2 : ℂ) ((p : ℕ) ^ r) *
          stripFourier
            (xiMassAnalyticTest (a / (r : ℝ)) (((r : ℝ) : ℂ) * τ))
            (Real.log ((((p : ℕ) ^ r : ℕ)) : ℝ) : ℂ)) := by
      rw [hlogpowC]
      ring

/-- For `r > 0` and `a > 0`, the dilation-masked layer at `(a, τ)` equals `r` times the `r`-th
prime-power layer at `(a/r, rτ)`. -/
theorem xiMassPrimeDilationLayer_eq_primePowerLayer
    {r : ℕ} (hr : 0 < r) {a : ℝ} (ha : 0 < a) (τ : ℂ) :
    xiMassPrimeDilationLayer r a τ =
      ((r : ℝ) : ℂ) * xiMassPrimePowerLayer r (a / (r : ℝ))
        (((r : ℝ) : ℂ) * τ) := by
  unfold xiMassPrimeDilationLayer xiMassPrimePowerLayer
  rw [← tsum_mul_left]
  exact tsum_congr
    (xiMassPrimeDilationMask_mul_centeredAtom_eq hr ha τ)

/-- For `r ≥ 3`, `∑_p log p · p^{-r/2} < ∞`. -/
theorem summable_xiMassPrimePowerCriticalWeight_fixed_high
    {r : ℕ} (hr : 3 ≤ r) :
    Summable (fun p : Nat.Primes =>
      xiMassPrimePowerCriticalWeight p (r - 1)) := by
  have hinj : Function.Injective
      (fun p : Nat.Primes => (p, r - 3)) := by
    intro p q hpq
    exact congrArg Prod.fst hpq
  have h := summable_xiMassPrimePowerCriticalWeight_high.comp_injective hinj
  have hk : r - 3 + 2 = r - 1 := by omega
  exact h.congr (fun p => by
    simp only [Function.comp_apply, hk])

theorem summable_norm_xiMassPrimePowerLayerAtom_high
    {r : ℕ} (hr : 3 ≤ r) {a σ : ℝ}
    (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    Summable (fun p : Nat.Primes =>
      ‖xiMassCenteredPrimeAtom a ((σ : ℂ) + u * I)
        ((p : ℕ) ^ r)‖) := by
  have hmajor : Summable (fun p : Nat.Primes =>
      xiMassPrimePowerCriticalWeight p (r - 1) *
        (∫ x : ℝ, Real.exp (-(σ * |x|)))) :=
    (summable_xiMassPrimePowerCriticalWeight_fixed_high hr).mul_right _
  exact hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => by
    have h := norm_xiMassCenteredPrimeAtom_primePower_le
      ha hσ u p (r - 1)
    have hexp : r - 1 + 1 = r := by omega
    simpa only [hexp] using h)

theorem summable_xiMassPrimePowerLayerAtom_high
    {r : ℕ} (hr : 3 ≤ r) {a σ : ℝ}
    (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    Summable (fun p : Nat.Primes =>
      xiMassCenteredPrimeAtom a ((σ : ℂ) + u * I)
        ((p : ℕ) ^ r)) :=
  summable_norm_iff.mp
    (summable_norm_xiMassPrimePowerLayerAtom_high hr ha hσ u)

/-- For `r ≥ 3` and `a, σ > 0`, the `r`-th prime-power layer on `Re τ = σ` is bounded by
`(∑_p log p · p^{-r/2}) · ∫ e^{-σ|x|} dx`. -/
theorem norm_xiMassPrimePowerLayer_vertical_le_high
    {r : ℕ} (hr : 3 ≤ r) {a σ : ℝ}
    (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    ‖xiMassPrimePowerLayer r a ((σ : ℂ) + u * I)‖ ≤
      (∑' p : Nat.Primes,
        xiMassPrimePowerCriticalWeight p (r - 1)) *
          (∫ x : ℝ, Real.exp (-(σ * |x|))) := by
  have hnorm := summable_norm_xiMassPrimePowerLayerAtom_high hr ha hσ u
  have hmajor : Summable (fun p : Nat.Primes =>
      xiMassPrimePowerCriticalWeight p (r - 1) *
        (∫ x : ℝ, Real.exp (-(σ * |x|)))) :=
    (summable_xiMassPrimePowerCriticalWeight_fixed_high hr).mul_right _
  calc
    ‖xiMassPrimePowerLayer r a ((σ : ℂ) + u * I)‖ ≤
        ∑' p : Nat.Primes,
          ‖xiMassCenteredPrimeAtom a ((σ : ℂ) + u * I)
            ((p : ℕ) ^ r)‖ := by
      exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' p : Nat.Primes,
        xiMassPrimePowerCriticalWeight p (r - 1) *
          (∫ x : ℝ, Real.exp (-(σ * |x|))) := by
      apply hnorm.tsum_le_tsum
      · intro p
        have h := norm_xiMassCenteredPrimeAtom_primePower_le
          ha hσ u p (r - 1)
        have hexp : r - 1 + 1 = r := by omega
        simpa only [hexp] using h
      · exact hmajor
    _ = _ := tsum_mul_right

theorem exists_norm_xiMassPrimePowerLayer_vertical_bound_high
    {r : ℕ} (hr : 3 ≤ r) {a σ : ℝ}
    (ha : 0 < a) (hσ : 0 < σ) :
    ∃ B : ℝ, ∀ u : ℝ,
      ‖xiMassPrimePowerLayer r a ((σ : ℂ) + u * I)‖ ≤ B := by
  exact ⟨(∑' p : Nat.Primes,
      xiMassPrimePowerCriticalWeight p (r - 1)) *
        (∫ x : ℝ, Real.exp (-(σ * |x|))),
    norm_xiMassPrimePowerLayer_vertical_le_high hr ha hσ⟩

/-- For `r ≥ 2`, `a > 0` and `0 < Re τ`, the atoms at `p^r` are absolutely summable over primes. -/
theorem summable_norm_xiMassPrimePowerLayerAtom
    {r : ℕ} (hr : 2 ≤ r) {a : ℝ} (ha : 0 < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (fun p : Nat.Primes =>
      ‖xiMassCenteredPrimeAtom a τ ((p : ℕ) ^ r)‖) := by
  rcases eq_or_lt_of_le hr with rfl | hr3
  · exact summable_norm_xiMassPrimeSquareCenteredAtom ha hτ
  · have hτform : ((τ.re : ℂ) + τ.im * I) = τ := by
      apply Complex.ext <;> simp
    simpa only [hτform] using
      summable_norm_xiMassPrimePowerLayerAtom_high
        (r := r) (by omega) ha hτ τ.im

theorem summable_xiMassPrimePowerLayerAtom
    {r : ℕ} (hr : 2 ≤ r) {a : ℝ} (ha : 0 < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (fun p : Nat.Primes =>
      xiMassCenteredPrimeAtom a τ ((p : ℕ) ^ r)) :=
  summable_norm_iff.mp
    (summable_norm_xiMassPrimePowerLayerAtom hr ha hτ)

/-- For `r ≥ 2` and `a, σ > 0`, the `r`-th prime-power layer is bounded on the vertical line
`Re τ = σ`; the case `r = 2` is the prime-square boundary residue bound. -/
theorem exists_norm_xiMassPrimePowerLayer_vertical_bound
    {r : ℕ} (hr : 2 ≤ r) {a σ : ℝ}
    (ha : 0 < a) (hσ : 0 < σ) :
    ∃ B : ℝ, ∀ u : ℝ,
      ‖xiMassPrimePowerLayer r a ((σ : ℂ) + u * I)‖ ≤ B := by
  rcases eq_or_lt_of_le hr with rfl | hr3
  · simpa only [xiMassPrimePowerLayer, xiMassPrimeSquareLayer] using
      exists_norm_xiMassPrimeSquareLayer_vertical_bound ha hσ
  · exact exists_norm_xiMassPrimePowerLayer_vertical_bound_high
      (r := r) (by omega) ha hσ

/-- For `r ≥ 2`, `a > 0` and `0 < Re τ`, the dilation-masked prime atoms are summable. -/
theorem summable_xiMassPrimeDilationMaskedAtom
    {r : ℕ} (hr : 2 ≤ r) {a : ℝ} (ha : 0 < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (fun p : Nat.Primes =>
      xiMassPrimeDilationMask r p *
        xiMassCenteredPrimeAtom a τ (p : ℕ)) := by
  have hr0 : 0 < r := by omega
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  have hτscaled : 0 < ((((r : ℝ) : ℂ) * τ).re) := by
    simpa [mul_re] using mul_pos hrR hτ
  have hpow := summable_xiMassPrimePowerLayerAtom hr
    (a := a / (r : ℝ)) (div_pos ha hrR)
    (τ := ((r : ℝ) : ℂ) * τ) hτscaled
  exact (hpow.mul_left ((r : ℝ) : ℂ)).congr (fun p =>
    (xiMassPrimeDilationMask_mul_centeredAtom_eq hr0 ha τ p).symm)

/-- For `r ≥ 2` and `a, σ > 0`, the dilation-masked prime layer is bounded on the vertical line
`Re τ = σ`, via its identification with a rescaled prime-power layer. -/
theorem exists_norm_xiMassPrimeDilationLayer_vertical_bound
    {r : ℕ} (hr : 2 ≤ r) {a σ : ℝ}
    (ha : 0 < a) (hσ : 0 < σ) :
    ∃ B : ℝ, ∀ u : ℝ,
      ‖xiMassPrimeDilationLayer r a ((σ : ℂ) + u * I)‖ ≤ B := by
  have hr0 : 0 < r := by omega
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  obtain ⟨B, hB⟩ := exists_norm_xiMassPrimePowerLayer_vertical_bound hr
    (a := a / (r : ℝ)) (σ := (r : ℝ) * σ)
    (div_pos ha hrR) (mul_pos hrR hσ)
  refine ⟨(r : ℝ) * B, fun u => ?_⟩
  have harg : ((r : ℝ) : ℂ) * ((σ : ℂ) + u * I) =
      ((((r : ℝ) * σ : ℝ) : ℂ) +
        (((r : ℝ) * u : ℝ) : ℂ) * I) := by
    push_cast
    ring
  rw [xiMassPrimeDilationLayer_eq_primePowerLayer hr0 ha,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrR, harg]
  exact mul_le_mul_of_nonneg_left (hB ((r : ℝ) * u)) hrR.le

/-- For `r > 0`, the dilation mask has modulus `‖m_r(p)‖ = p^{-(r-1)/2}`. -/
theorem norm_xiMassPrimeDilationMask_eq
    {r : ℕ} (hr : 0 < r) (p : Nat.Primes) :
    ‖xiMassPrimeDilationMask r p‖ =
      (p : ℝ) ^ (-(((r - 1 : ℕ) : ℝ) / 2)) := by
  rw [xiMassPrimeDilationMask, norm_div]
  have hrpred : r - 1 + 1 = r := by omega
  have hnum :
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (1 / 2 : ℂ) ((p : ℕ) ^ r)‖ =
        xiMassPrimePowerCriticalWeight p (r - 1) := by
    rw [xiMassPrimePowerCriticalWeight, hrpred]
  have hden :
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (1 / 2 : ℂ) (p : ℕ)‖ =
        xiMassPrimePowerCriticalWeight p 0 := by
    rw [xiMassPrimePowerCriticalWeight]
    norm_num
  rw [hnum, hden, xiMassPrimePowerCriticalWeight_eq,
    xiMassPrimePowerCriticalWeight_eq]
  have hp : 0 < ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.pos
  have hlog : Real.log ((p : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast p.prop.one_lt))
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_zero]
  rw [mul_div_mul_left _ _ hlog, ← Real.rpow_sub hp]
  congr 1
  ring

/-- For `r > 0`, `‖m_r(p)‖ · log p · p^{-1/2} = log p · p^{-r/2}`, the critical weight of `p^r`. -/
theorem norm_xiMassPrimeDilationMask_mul_criticalWeight_eq
    {r : ℕ} (hr : 0 < r) (p : Nat.Primes) :
    ‖xiMassPrimeDilationMask r p‖ *
        xiMassPrimePowerCriticalWeight p 0 =
      xiMassPrimePowerCriticalWeight p (r - 1) := by
  rw [xiMassPrimeDilationMask, norm_div]
  have hrpred : r - 1 + 1 = r := by omega
  have hnum :
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (1 / 2 : ℂ) ((p : ℕ) ^ r)‖ =
        xiMassPrimePowerCriticalWeight p (r - 1) := by
    rw [xiMassPrimePowerCriticalWeight, hrpred]
  have hden :
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (1 / 2 : ℂ) (p : ℕ)‖ =
        xiMassPrimePowerCriticalWeight p 0 := by
    rw [xiMassPrimePowerCriticalWeight]
    norm_num
  rw [hnum, hden]
  have hw0 : xiMassPrimePowerCriticalWeight p 0 ≠ 0 := by
    rw [xiMassPrimePowerCriticalWeight]
    exact norm_ne_zero_iff.mpr (by
      simpa using xiMassPrimeCriticalTerm_ne_zero p)
  exact div_mul_cancel₀ _ hw0

/-- For `r ≥ 3`, the dilation mask is summable against the critical weights:
`∑_p ‖m_r(p)‖ · log p · p^{-1/2} < ∞`. -/
theorem summable_norm_xiMassPrimeDilationMask_mul_criticalWeight_high
    {r : ℕ} (hr : 3 ≤ r) :
    Summable (fun p : Nat.Primes =>
      ‖xiMassPrimeDilationMask r p‖ *
        xiMassPrimePowerCriticalWeight p 0) := by
  have h := summable_xiMassPrimePowerCriticalWeight_fixed_high hr
  exact h.congr (fun p =>
    (norm_xiMassPrimeDilationMask_mul_criticalWeight_eq
      (by omega : 0 < r) p).symm)

end

end RHTower
