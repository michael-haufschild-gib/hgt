import GaloisForLFunctions.RHTower.XiMassPrimeSqrtBoundaryResidue

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Prime-square atoms are absolutely summable for every positive mass. -/
theorem summable_norm_xiMassPrimeSquareCenteredAtom
    {a : ℝ} (ha : 0 < a) {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (fun p : Nat.Primes =>
      ‖xiMassCenteredPrimeAtom a τ ((p : ℕ) ^ (2 : ℕ))‖) := by
  let d : ℝ := a / 2
  have hd : 0 < d := by dsimp only [d]; linarith
  have hda : d < a := by dsimp only [d]; linarith
  have hnorm : Summable (fun p : Nat.Primes =>
      ‖∫ x : ℝ,
        xiMassBottomPrimeAtomIntegrand a d τ ((p : ℕ) ^ (2 : ℕ)) x‖) :=
    Summable.of_nonneg_of_le
      (fun _ => norm_nonneg _)
      (fun _ => norm_integral_le_integral_norm _)
      (summable_integral_norm_xiMassBottomPrimeSquareAtomIntegrand hd hda hτ)
  exact hnorm.congr (fun p => by
    rw [integral_xiMassBottomPrimeAtom_eq_centered_of_nonneg
      hd.le hda hτ])

theorem summable_xiMassPrimeSquareCenteredAtom
    {a : ℝ} (ha : 0 < a) {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (fun p : Nat.Primes =>
      xiMassCenteredPrimeAtom a τ ((p : ℕ) ^ (2 : ℕ))) :=
  summable_norm_iff.mp
    (summable_norm_xiMassPrimeSquareCenteredAtom ha hτ)

theorem xiMassPrimeSqrtMask_mul_centeredAtom_eq_two_mul_squareAtom
    {a : ℝ} (ha : 0 < a) (τ : ℂ) (p : Nat.Primes) :
    xiMassPrimeSqrtMask p * xiMassCenteredPrimeAtom a τ (p : ℕ) =
      2 * xiMassCenteredPrimeAtom (a / 2) (2 * τ) ((p : ℕ) ^ (2 : ℕ)) := by
  calc
    xiMassPrimeSqrtMask p * xiMassCenteredPrimeAtom a τ (p : ℕ) =
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (1 / 2 : ℂ) ((p : ℕ) ^ (2 : ℕ)) *
          stripFourier (xiMassAnalyticTest a τ)
            (Real.log (p : ℕ) : ℂ) :=
      xiMassPrimeSqrtMask_mul_centeredAtom_eq_boundaryTerm a τ p
    _ = 2 * xiMassCenteredPrimeAtom (a / 2) (2 * τ)
          ((p : ℕ) ^ (2 : ℕ)) :=
      xiMassPrimeSqrtBoundaryTerm_eq_two_mul_squareAtom ha τ p

theorem summable_xiMassPrimeSqrtMaskedAtom
    {a : ℝ} (ha : 0 < a) {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (fun p : Nat.Primes =>
      xiMassPrimeSqrtMask p *
        xiMassCenteredPrimeAtom a τ (p : ℕ)) := by
  have hsquare := summable_xiMassPrimeSquareCenteredAtom
    (a := a / 2) (by linarith : 0 < a / 2)
    (τ := 2 * τ) (by simpa [mul_re] using (mul_pos (by norm_num : (0 : ℝ) < 2) hτ))
  exact (hsquare.mul_left (2 : ℂ)).congr (fun p =>
    (xiMassPrimeSqrtMask_mul_centeredAtom_eq_two_mul_squareAtom
      ha τ p).symm)

def xiMassPrimeBoundaryResidual
    (w : Nat.Primes → ℂ) (c b : ℂ) (a : ℝ) (τ : ℂ) : ℂ :=
  xiMassPrimeMaskResidual
    (fun p => w p - b * xiMassPrimeSqrtMask p) c a τ

theorem summable_xiMassPrimeBoundaryMaskedAtom
    {w : Nat.Primes → ℂ} {c b : ℂ} {a q : ℝ}
    (hhalf : 1 / 2 < q) (hqa : q < a)
    {τ : ℂ} (hτ : 0 < τ.re)
    (hdev : Summable (fun p : Nat.Primes =>
      ‖(w p - b * xiMassPrimeSqrtMask p) - c‖ *
        xiMassPrimePowerCriticalWeight p 0)) :
    Summable (fun p : Nat.Primes =>
      w p * xiMassCenteredPrimeAtom a τ (p : ℕ)) := by
  have ha : 0 < a := by linarith
  have hprime := summable_xiMassValuationOnePrimeAtom hhalf hqa hτ
  have hsqrt := summable_xiMassPrimeSqrtMaskedAtom ha hτ
  have hτform : ((τ.re : ℂ) + τ.im * I) = τ := by
    apply Complex.ext <;> simp
  have hres : Summable (fun p : Nat.Primes =>
      ((w p - b * xiMassPrimeSqrtMask p) - c) *
        xiMassCenteredPrimeAtom a τ (p : ℕ)) := by
    simpa only [hτform] using
      summable_xiMassPrimeMaskResidualAtom
        (w := fun p => w p - b * xiMassPrimeSqrtMask p)
        hdev ha hτ τ.im
  exact (((hprime.mul_left c).add (hsqrt.mul_left b)).add hres).congr
    (fun p => by ring)

theorem xiMassPrimeMaskedLayer_eq_scalar_add_boundary_add_residual
    {w : Nat.Primes → ℂ} {c b : ℂ} {a q : ℝ}
    (hhalf : 1 / 2 < q) (hqa : q < a)
    {τ : ℂ} (hτ : 0 < τ.re)
    (hdev : Summable (fun p : Nat.Primes =>
      ‖(w p - b * xiMassPrimeSqrtMask p) - c‖ *
        xiMassPrimePowerCriticalWeight p 0)) :
    xiMassPrimeMaskedLayer w a τ =
      c * xiMassValuationOnePrimeLayer a τ +
        b * xiMassPrimeSqrtMaskLayer a τ +
          xiMassPrimeBoundaryResidual w c b a τ := by
  have ha : 0 < a := by linarith
  have hprime := summable_xiMassValuationOnePrimeAtom hhalf hqa hτ
  have hsqrt := summable_xiMassPrimeSqrtMaskedAtom ha hτ
  have hτform : ((τ.re : ℂ) + τ.im * I) = τ := by
    apply Complex.ext <;> simp
  have hres : Summable (fun p : Nat.Primes =>
      ((w p - b * xiMassPrimeSqrtMask p) - c) *
        xiMassCenteredPrimeAtom a τ (p : ℕ)) := by
    simpa only [hτform] using
      summable_xiMassPrimeMaskResidualAtom
        (w := fun p => w p - b * xiMassPrimeSqrtMask p)
        hdev ha hτ τ.im
  unfold xiMassPrimeMaskedLayer xiMassValuationOnePrimeLayer
    xiMassPrimeSqrtMaskLayer xiMassPrimeBoundaryResidual
    xiMassPrimeMaskResidual
  calc
    (∑' p : Nat.Primes,
        w p * xiMassCenteredPrimeAtom a τ (p : ℕ)) =
      ∑' p : Nat.Primes, (
        (c * xiMassCenteredPrimeAtom a τ (p : ℕ) +
          b * (xiMassPrimeSqrtMask p *
            xiMassCenteredPrimeAtom a τ (p : ℕ))) +
          ((w p - b * xiMassPrimeSqrtMask p) - c) *
            xiMassCenteredPrimeAtom a τ (p : ℕ)) := by
      exact tsum_congr fun p => by ring
    _ = (∑' p : Nat.Primes,
          c * xiMassCenteredPrimeAtom a τ (p : ℕ)) +
        (∑' p : Nat.Primes,
          b * (xiMassPrimeSqrtMask p *
            xiMassCenteredPrimeAtom a τ (p : ℕ))) +
        ∑' p : Nat.Primes,
          ((w p - b * xiMassPrimeSqrtMask p) - c) *
            xiMassCenteredPrimeAtom a τ (p : ℕ) := by
      rw [((hprime.mul_left c).add (hsqrt.mul_left b)).tsum_add hres,
        (hprime.mul_left c).tsum_add (hsqrt.mul_left b)]
    _ = _ := by rw [tsum_mul_left, tsum_mul_left]

theorem exists_norm_xiMassPrimeBoundaryResidual_vertical_bound
    {w : Nat.Primes → ℂ} {c b : ℂ} {a σ : ℝ}
    (hdev : Summable (fun p : Nat.Primes =>
      ‖(w p - b * xiMassPrimeSqrtMask p) - c‖ *
        xiMassPrimePowerCriticalWeight p 0))
    (ha : 0 < a) (hσ : 0 < σ) :
    ∃ B : ℝ, ∀ u : ℝ,
      ‖xiMassPrimeBoundaryResidual w c b a
        ((σ : ℂ) + u * I)‖ ≤ B := by
  simpa only [xiMassPrimeBoundaryResidual] using
    exists_norm_xiMassPrimeMaskResidual_vertical_bound
      (w := fun p => w p - b * xiMassPrimeSqrtMask p)
      (c := c) hdev ha hσ

theorem xiMassPrimeBoundaryMaskedLineBound_of_scalar_eq_zero
    {w : Nat.Primes → ℂ} {c b : ℂ} {a q σ : ℝ}
    (hhalf : 1 / 2 < q) (hqa : q < a) (hσ : 0 < σ)
    (hc : c = 0)
    (hdev : Summable (fun p : Nat.Primes =>
      ‖(w p - b * xiMassPrimeSqrtMask p) - c‖ *
        xiMassPrimePowerCriticalWeight p 0)) :
    XiMassPrimeMaskedLineBound w a σ := by
  subst c
  have ha : 0 < a := by linarith
  obtain ⟨S, hS⟩ :=
    exists_norm_xiMassPrimeSqrtMaskLayer_vertical_bound ha hσ
  obtain ⟨R, hR⟩ :=
    exists_norm_xiMassPrimeBoundaryResidual_vertical_bound hdev ha hσ
  refine ⟨‖b‖ * S + R, fun u => ?_⟩
  rw [xiMassPrimeMaskedLayer_eq_scalar_add_boundary_add_residual
    hhalf hqa (τ := ((σ : ℂ) + u * I)) (by simpa using hσ) hdev,
    zero_mul, zero_add]
  exact (norm_add_le _ _).trans
    (add_le_add
      (by rw [norm_mul]; exact
        mul_le_mul_of_nonneg_left (hS u) (norm_nonneg _))
      (hR u))

theorem xiMassPrimeBoundaryMaskedLineBound_iff_valuationOne
    {w : Nat.Primes → ℂ} {c b : ℂ} {a q σ : ℝ}
    (hhalf : 1 / 2 < q) (hqa : q < a) (hσ : 0 < σ)
    (hc : c ≠ 0)
    (hdev : Summable (fun p : Nat.Primes =>
      ‖(w p - b * xiMassPrimeSqrtMask p) - c‖ *
        xiMassPrimePowerCriticalWeight p 0)) :
    XiMassPrimeMaskedLineBound w a σ ↔
      XiMassValuationOnePrimeLineBound a σ := by
  have ha : 0 < a := by linarith
  obtain ⟨S, hS⟩ :=
    exists_norm_xiMassPrimeSqrtMaskLayer_vertical_bound ha hσ
  obtain ⟨R, hR⟩ :=
    exists_norm_xiMassPrimeBoundaryResidual_vertical_bound hdev ha hσ
  have hboundary (u : ℝ) :
      ‖b * xiMassPrimeSqrtMaskLayer a ((σ : ℂ) + u * I) +
          xiMassPrimeBoundaryResidual w c b a ((σ : ℂ) + u * I)‖ ≤
        ‖b‖ * S + R := by
    exact (norm_add_le _ _).trans
      (add_le_add
        (by rw [norm_mul]; exact
          mul_le_mul_of_nonneg_left (hS u) (norm_nonneg _))
        (hR u))
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨‖c⁻¹‖ * (C + (‖b‖ * S + R)), fun u => ?_⟩
    have hdecomp :=
      xiMassPrimeMaskedLayer_eq_scalar_add_boundary_add_residual
        hhalf hqa (τ := ((σ : ℂ) + u * I))
          (by simpa using hσ) hdev
    have heq :
        xiMassValuationOnePrimeLayer a ((σ : ℂ) + u * I) =
          c⁻¹ * (xiMassPrimeMaskedLayer w a ((σ : ℂ) + u * I) -
            (b * xiMassPrimeSqrtMaskLayer a ((σ : ℂ) + u * I) +
              xiMassPrimeBoundaryResidual w c b a
                ((σ : ℂ) + u * I))) := by
      rw [hdecomp]
      field_simp
      ring
    rw [heq, norm_mul]
    exact mul_le_mul_of_nonneg_left
      ((norm_sub_le _ _).trans
        (add_le_add (hC u) (hboundary u)))
      (norm_nonneg _)
  · rintro ⟨C, hC⟩
    refine ⟨‖c‖ * C + (‖b‖ * S + R), fun u => ?_⟩
    rw [xiMassPrimeMaskedLayer_eq_scalar_add_boundary_add_residual
      hhalf hqa (τ := ((σ : ℂ) + u * I))
        (by simpa using hσ) hdev]
    rw [add_assoc]
    exact (norm_add_le _ _).trans
      (add_le_add
        (by rw [norm_mul]; exact
          mul_le_mul_of_nonneg_left (hC u) (norm_nonneg _))
        (hboundary u))

theorem riemannHypothesis_iff_xiMassPrimeBoundaryMaskedLineBound
    {w : Nat.Primes → ℂ} {c b : ℂ} {a q σ : ℝ}
    (hhalf : 1 / 2 < q) (hqa : q < a) (hσ : 0 < σ)
    (hc : c ≠ 0)
    (hdev : Summable (fun p : Nat.Primes =>
      ‖(w p - b * xiMassPrimeSqrtMask p) - c‖ *
        xiMassPrimePowerCriticalWeight p 0)) :
    RiemannHypothesis ↔ XiMassPrimeMaskedLineBound w a σ := by
  exact (riemannHypothesis_iff_xiMassValuationOnePrimeLineBound
    hhalf hqa hσ).trans
      (xiMassPrimeBoundaryMaskedLineBound_iff_valuationOne
        hhalf hqa hσ hc hdev).symm

end

end RHTower
