import GaloisForLFunctions.RHTower.XiMassValuationFilterQuotient

/-!
# Prime masks with critically summable deviation from a constant

A prime mask `w : Primes → ℂ` reweights the prime layer to `∑_p w p · atom(p)`, where
`atom(p) = Λ(p) p^{-1/2} ĝ(log p)` is the centered mass atom. If `w` differs from a constant `c`
by a deviation that is summable against the critical weights, i.e.
`∑_p ‖w p - c‖ · log p · p^{-1/2} < ∞`, then the masked layer is `c` times the prime layer plus a
residual that is bounded on every positive vertical line. Consequently, when `c = 0` the masked
layer is bounded, and when `c ≠ 0` its boundedness on one vertical line is equivalent to the
Riemann Hypothesis.

## Main results

- `norm_xiMassPrimeMaskResidual_vertical_le`: the residual is bounded on `Re τ = σ` by
  `(∑_p ‖w p - c‖ log p · p^{-1/2}) · ∫ e^{-σ|x|} dx`.
- `xiMassPrimeMaskedLayer_eq_scalar_add_residual`: masked layer `= c ·` prime layer `+` residual.
- `xiMassPrimeMaskedLineBound_of_scalar_eq_zero`: for `c = 0` the masked layer is bounded on
  the line.
- `xiMassPrimeMaskedLineBound_iff_valuationOne`: for `c ≠ 0`, masked boundedness is equivalent to
  prime-layer boundedness.
- `riemannHypothesis_iff_xiMassPrimeMaskedLineBound`: for `c ≠ 0`, RH is equivalent to the masked
  layer being bounded on `Re τ = σ`.

## Hypotheses

All results are unconditional. The substantive hypothesis on the mask is critical summability of
its deviation, `∑_p ‖w p - c‖ · log p · p^{-1/2} < ∞` (named `hdev`); the equivalences also need
`c ≠ 0`. Parameter ranges are `0 < a`, `0 < σ` and `1/2 < d < a`. The line-bound predicates occur
only as conclusions or as sides of the equivalences.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Residual of a prime mask about the constant `c`: `∑_p (w p - c) · atom(p)`. -/
def xiMassPrimeMaskResidual
    (w : Nat.Primes → ℂ) (c : ℂ) (a : ℝ) (τ : ℂ) : ℂ :=
  ∑' p : Nat.Primes,
    (w p - c) * xiMassCenteredPrimeAtom a τ (p : ℕ)

/-- The masked prime layer `∑_p w p · atom(p)`. -/
def xiMassPrimeMaskedLayer
    (w : Nat.Primes → ℂ) (a : ℝ) (τ : ℂ) : ℂ :=
  ∑' p : Nat.Primes, w p * xiMassCenteredPrimeAtom a τ (p : ℕ)

/-- The masked prime layer is bounded along the vertical line `τ = σ + iu`, `u ∈ ℝ`. -/
def XiMassPrimeMaskedLineBound
    (w : Nat.Primes → ℂ) (a σ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ,
    ‖xiMassPrimeMaskedLayer w a ((σ : ℂ) + u * I)‖ ≤ C

theorem summable_norm_xiMassPrimeMaskResidualAtom
    {w : Nat.Primes → ℂ} {c : ℂ} {a σ : ℝ}
    (hdev : Summable (fun p : Nat.Primes =>
      ‖w p - c‖ * xiMassPrimePowerCriticalWeight p 0))
    (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    Summable (fun p : Nat.Primes =>
      ‖(w p - c) *
        xiMassCenteredPrimeAtom a ((σ : ℂ) + u * I) (p : ℕ)‖) := by
  have hmajor := hdev.mul_right (∫ x : ℝ, Real.exp (-(σ * |x|)))
  exact hmajor.of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun p => by
      rw [norm_mul]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left
          (by simpa using
            norm_xiMassCenteredPrimeAtom_primePower_le ha hσ u p 0)
          (norm_nonneg (w p - c)))

theorem summable_xiMassPrimeMaskResidualAtom
    {w : Nat.Primes → ℂ} {c : ℂ} {a σ : ℝ}
    (hdev : Summable (fun p : Nat.Primes =>
      ‖w p - c‖ * xiMassPrimePowerCriticalWeight p 0))
    (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    Summable (fun p : Nat.Primes =>
      (w p - c) *
        xiMassCenteredPrimeAtom a ((σ : ℂ) + u * I) (p : ℕ)) :=
  summable_norm_iff.mp
    (summable_norm_xiMassPrimeMaskResidualAtom hdev ha hσ u)

/-- Assuming `∑_p ‖w p - c‖ log p · p^{-1/2} < ∞` and `a, σ > 0`, the residual on `Re τ = σ`
is bounded by that sum times `∫ e^{-σ|x|} dx`, uniformly in `Im τ`. -/
theorem norm_xiMassPrimeMaskResidual_vertical_le
    {w : Nat.Primes → ℂ} {c : ℂ} {a σ : ℝ}
    (hdev : Summable (fun p : Nat.Primes =>
      ‖w p - c‖ * xiMassPrimePowerCriticalWeight p 0))
    (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    ‖xiMassPrimeMaskResidual w c a ((σ : ℂ) + u * I)‖ ≤
      (∑' p : Nat.Primes,
        ‖w p - c‖ * xiMassPrimePowerCriticalWeight p 0) *
          (∫ x : ℝ, Real.exp (-(σ * |x|))) := by
  have hnorm := summable_norm_xiMassPrimeMaskResidualAtom hdev ha hσ u
  have hmajor := hdev.mul_right (∫ x : ℝ, Real.exp (-(σ * |x|)))
  calc
    ‖xiMassPrimeMaskResidual w c a ((σ : ℂ) + u * I)‖ ≤
        ∑' p : Nat.Primes,
          ‖(w p - c) *
            xiMassCenteredPrimeAtom a ((σ : ℂ) + u * I) (p : ℕ)‖ := by
      exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' p : Nat.Primes,
        (‖w p - c‖ * xiMassPrimePowerCriticalWeight p 0) *
          (∫ x : ℝ, Real.exp (-(σ * |x|))) := by
      apply hnorm.tsum_le_tsum
      · intro p
        rw [norm_mul]
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left
            (by simpa using
              norm_xiMassCenteredPrimeAtom_primePower_le ha hσ u p 0)
            (norm_nonneg (w p - c))
      · exact hmajor
    _ = _ := tsum_mul_right

/-- For `1/2 < d < a` and `0 < Re τ`, the centered atoms at primes are summable. -/
theorem summable_xiMassValuationOnePrimeAtom
    {a d : ℝ} (hhalf : 1 / 2 < d) (hda : d < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (fun p : Nat.Primes =>
      xiMassCenteredPrimeAtom a τ (p : ℕ)) := by
  have h := (summable_xiMassCenteredPrimeAtom hhalf hda hτ).comp_injective
    (i := fun p : Nat.Primes => (p : ℕ)) Subtype.coe_injective
  simpa only [Function.comp_apply] using! h

theorem summable_xiMassPrimeMaskedAtom
    {w : Nat.Primes → ℂ} {c : ℂ} {a d : ℝ}
    (hhalf : 1 / 2 < d) (hda : d < a)
    {τ : ℂ} (hτ : 0 < τ.re)
    (hdev : Summable (fun p : Nat.Primes =>
      ‖w p - c‖ * xiMassPrimePowerCriticalWeight p 0)) :
    Summable (fun p : Nat.Primes =>
      w p * xiMassCenteredPrimeAtom a τ (p : ℕ)) := by
  have ha : 0 < a := by linarith
  have hprime := summable_xiMassValuationOnePrimeAtom hhalf hda hτ
  have hτform : ((τ.re : ℂ) + τ.im * I) = τ := by
    apply Complex.ext <;> simp
  have hres : Summable (fun p : Nat.Primes =>
      (w p - c) * xiMassCenteredPrimeAtom a τ (p : ℕ)) := by
    simpa only [hτform] using
      summable_xiMassPrimeMaskResidualAtom hdev ha hτ τ.im
  exact ((hprime.mul_left c).add hres).congr (fun p => by ring)

/-- Assuming critical summability of `w - c`, `1/2 < d < a` and `0 < Re τ`, the masked layer
equals `c` times the prime layer plus the residual. -/
theorem xiMassPrimeMaskedLayer_eq_scalar_add_residual
    {w : Nat.Primes → ℂ} {c : ℂ} {a d : ℝ}
    (hhalf : 1 / 2 < d) (hda : d < a)
    {τ : ℂ} (hτ : 0 < τ.re)
    (hdev : Summable (fun p : Nat.Primes =>
      ‖w p - c‖ * xiMassPrimePowerCriticalWeight p 0)) :
    xiMassPrimeMaskedLayer w a τ =
      c * xiMassValuationOnePrimeLayer a τ +
        xiMassPrimeMaskResidual w c a τ := by
  have ha : 0 < a := by linarith
  have hprime := summable_xiMassValuationOnePrimeAtom hhalf hda hτ
  have hτform : ((τ.re : ℂ) + τ.im * I) = τ := by
    apply Complex.ext <;> simp
  have hres : Summable (fun p : Nat.Primes =>
      (w p - c) * xiMassCenteredPrimeAtom a τ (p : ℕ)) := by
    simpa only [hτform] using
      summable_xiMassPrimeMaskResidualAtom hdev ha hτ τ.im
  unfold xiMassPrimeMaskedLayer xiMassValuationOnePrimeLayer
    xiMassPrimeMaskResidual
  calc
    (∑' p : Nat.Primes,
        w p * xiMassCenteredPrimeAtom a τ (p : ℕ)) =
      ∑' p : Nat.Primes,
        (c * xiMassCenteredPrimeAtom a τ (p : ℕ) +
          (w p - c) * xiMassCenteredPrimeAtom a τ (p : ℕ)) := by
      apply tsum_congr
      intro p
      ring
    _ = (∑' p : Nat.Primes,
        c * xiMassCenteredPrimeAtom a τ (p : ℕ)) +
      ∑' p : Nat.Primes,
        (w p - c) * xiMassCenteredPrimeAtom a τ (p : ℕ) :=
      (hprime.mul_left c).tsum_add hres
    _ = _ := by rw [tsum_mul_left]

/-- Assuming critical summability of `w - c` and `a, σ > 0`, the residual is bounded on the
vertical line `Re τ = σ`. -/
theorem exists_norm_xiMassPrimeMaskResidual_vertical_bound
    {w : Nat.Primes → ℂ} {c : ℂ} {a σ : ℝ}
    (hdev : Summable (fun p : Nat.Primes =>
      ‖w p - c‖ * xiMassPrimePowerCriticalWeight p 0))
    (ha : 0 < a) (hσ : 0 < σ) :
    ∃ B : ℝ, ∀ u : ℝ,
      ‖xiMassPrimeMaskResidual w c a ((σ : ℂ) + u * I)‖ ≤ B := by
  exact ⟨(∑' p : Nat.Primes,
      ‖w p - c‖ * xiMassPrimePowerCriticalWeight p 0) *
        (∫ x : ℝ, Real.exp (-(σ * |x|))),
    norm_xiMassPrimeMaskResidual_vertical_le hdev ha hσ⟩

/-- A mask that is itself critically summable (`c = 0`) gives a masked layer bounded on every
positive vertical line, assuming `1/2 < d < a`. -/
theorem xiMassPrimeMaskedLineBound_of_scalar_eq_zero
    {w : Nat.Primes → ℂ} {c : ℂ} {a d σ : ℝ}
    (hhalf : 1 / 2 < d) (hda : d < a) (hσ : 0 < σ)
    (hc : c = 0)
    (hdev : Summable (fun p : Nat.Primes =>
      ‖w p - c‖ * xiMassPrimePowerCriticalWeight p 0)) :
    XiMassPrimeMaskedLineBound w a σ := by
  subst c
  have ha : 0 < a := by linarith
  obtain ⟨B, hB⟩ :=
    exists_norm_xiMassPrimeMaskResidual_vertical_bound hdev ha hσ
  refine ⟨B, fun u => ?_⟩
  rw [xiMassPrimeMaskedLayer_eq_scalar_add_residual hhalf hda
    (τ := ((σ : ℂ) + u * I)) (by simpa using hσ) hdev, zero_mul, zero_add]
  exact hB u

/-- Assuming critical summability of `w - c` with `c ≠ 0`, `1/2 < d < a` and `0 < σ`, the masked
layer is bounded on `Re τ = σ` iff the prime layer is. -/
theorem xiMassPrimeMaskedLineBound_iff_valuationOne
    {w : Nat.Primes → ℂ} {c : ℂ} {a d σ : ℝ}
    (hhalf : 1 / 2 < d) (hda : d < a) (hσ : 0 < σ)
    (hc : c ≠ 0)
    (hdev : Summable (fun p : Nat.Primes =>
      ‖w p - c‖ * xiMassPrimePowerCriticalWeight p 0)) :
    XiMassPrimeMaskedLineBound w a σ ↔
      XiMassValuationOnePrimeLineBound a σ := by
  have ha : 0 < a := by linarith
  obtain ⟨B, hB⟩ :=
    exists_norm_xiMassPrimeMaskResidual_vertical_bound hdev ha hσ
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨‖c⁻¹‖ * (C + B), fun u => ?_⟩
    have hdecomp := xiMassPrimeMaskedLayer_eq_scalar_add_residual
      hhalf hda (τ := ((σ : ℂ) + u * I)) (by simpa using hσ) hdev
    have heq :
        xiMassValuationOnePrimeLayer a ((σ : ℂ) + u * I) =
          c⁻¹ * (xiMassPrimeMaskedLayer w a ((σ : ℂ) + u * I) -
            xiMassPrimeMaskResidual w c a ((σ : ℂ) + u * I)) := by
      rw [hdecomp]
      field_simp
      ring
    rw [heq, norm_mul]
    exact mul_le_mul_of_nonneg_left
      ((norm_sub_le _ _).trans (add_le_add (hC u) (hB u))) (norm_nonneg _)
  · rintro ⟨C, hC⟩
    refine ⟨‖c‖ * C + B, fun u => ?_⟩
    rw [xiMassPrimeMaskedLayer_eq_scalar_add_residual hhalf hda
      (τ := ((σ : ℂ) + u * I)) (by simpa using hσ) hdev]
    exact (norm_add_le _ _).trans
      (add_le_add (by rw [norm_mul]; exact
        mul_le_mul_of_nonneg_left (hC u) (norm_nonneg _)) (hB u))

/-- RH criterion: if `w - c` is critically summable with `c ≠ 0`, `1/2 < d < a` and `0 < σ`,
the Riemann Hypothesis is equivalent to the masked prime layer being bounded on `Re τ = σ`. -/
theorem riemannHypothesis_iff_xiMassPrimeMaskedLineBound
    {w : Nat.Primes → ℂ} {c : ℂ} {a d σ : ℝ}
    (hhalf : 1 / 2 < d) (hda : d < a) (hσ : 0 < σ)
    (hc : c ≠ 0)
    (hdev : Summable (fun p : Nat.Primes =>
      ‖w p - c‖ * xiMassPrimePowerCriticalWeight p 0)) :
    RiemannHypothesis ↔ XiMassPrimeMaskedLineBound w a σ := by
  exact (riemannHypothesis_iff_xiMassValuationOnePrimeLineBound
    hhalf hda hσ).trans
      (xiMassPrimeMaskedLineBound_iff_valuationOne
        hhalf hda hσ hc hdev).symm

end

end RHTower
