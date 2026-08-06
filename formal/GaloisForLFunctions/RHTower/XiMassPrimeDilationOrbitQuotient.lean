import GaloisForLFunctions.RHTower.XiMassPrimeDilationSemigroup

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

def xiMassPrimeDilationOrbitMask
    (R : Finset ℕ) (b : ℕ → ℂ) (p : Nat.Primes) : ℂ :=
  ∑ r ∈ R, b r * xiMassPrimeDilationMask r p

def xiMassPrimeDilationOrbitLayer
    (R : Finset ℕ) (b : ℕ → ℂ) (a : ℝ) (τ : ℂ) : ℂ :=
  xiMassPrimeMaskedLayer (xiMassPrimeDilationOrbitMask R b) a τ

theorem summable_xiMassPrimeDilationOrbitMaskedAtom
    {R : Finset ℕ} {b : ℕ → ℂ}
    (hr : ∀ r ∈ R, 2 ≤ r) {a : ℝ} (ha : 0 < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (fun p : Nat.Primes =>
      xiMassPrimeDilationOrbitMask R b p *
        xiMassCenteredPrimeAtom a τ (p : ℕ)) := by
  classical
  have hsum : Summable (fun p : Nat.Primes =>
      ∑ r ∈ R, b r * (xiMassPrimeDilationMask r p *
        xiMassCenteredPrimeAtom a τ (p : ℕ))) := by
    exact summable_sum fun r hrR =>
      (summable_xiMassPrimeDilationMaskedAtom (hr r hrR) ha hτ).mul_left (b r)
  exact hsum.congr (fun p => by
    unfold xiMassPrimeDilationOrbitMask
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun r _ => by ring))

theorem xiMassPrimeDilationOrbitLayer_eq_sum
    {R : Finset ℕ} {b : ℕ → ℂ}
    (hr : ∀ r ∈ R, 2 ≤ r) {a : ℝ} (ha : 0 < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    xiMassPrimeDilationOrbitLayer R b a τ =
      ∑ r ∈ R, b r * xiMassPrimeDilationLayer r a τ := by
  classical
  have hterm : ∀ r ∈ R, Summable (fun p : Nat.Primes =>
      b r * (xiMassPrimeDilationMask r p *
        xiMassCenteredPrimeAtom a τ (p : ℕ))) := fun r hrR =>
    (summable_xiMassPrimeDilationMaskedAtom (hr r hrR) ha hτ).mul_left (b r)
  unfold xiMassPrimeDilationOrbitLayer xiMassPrimeMaskedLayer
    xiMassPrimeDilationOrbitMask xiMassPrimeDilationLayer
  calc
    (∑' p : Nat.Primes,
        (∑ r ∈ R, b r * xiMassPrimeDilationMask r p) *
          xiMassCenteredPrimeAtom a τ (p : ℕ)) =
      ∑' p : Nat.Primes, ∑ r ∈ R,
        b r * (xiMassPrimeDilationMask r p *
          xiMassCenteredPrimeAtom a τ (p : ℕ)) := by
      exact tsum_congr fun p => by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun r _ => by ring)
    _ = ∑ r ∈ R, ∑' p : Nat.Primes,
        b r * (xiMassPrimeDilationMask r p *
          xiMassCenteredPrimeAtom a τ (p : ℕ)) :=
      Summable.tsum_finsetSum hterm
    _ = ∑ r ∈ R, b r * (∑' p : Nat.Primes,
        xiMassPrimeDilationMask r p *
          xiMassCenteredPrimeAtom a τ (p : ℕ)) := by
      exact Finset.sum_congr rfl (fun r _ => tsum_mul_left)

theorem exists_norm_xiMassPrimeDilationOrbitLayer_vertical_bound
    {R : Finset ℕ} {b : ℕ → ℂ}
    (hr : ∀ r ∈ R, 2 ≤ r) {a σ : ℝ}
    (ha : 0 < a) (hσ : 0 < σ) :
    ∃ B : ℝ, ∀ u : ℝ,
      ‖xiMassPrimeDilationOrbitLayer R b a ((σ : ℂ) + u * I)‖ ≤ B := by
  classical
  let B : ℕ → ℝ := fun r =>
    if h : 2 ≤ r then
      Classical.choose
        (exists_norm_xiMassPrimeDilationLayer_vertical_bound h ha hσ)
    else 0
  have hB {r : ℕ} (h : 2 ≤ r) (u : ℝ) :
      ‖xiMassPrimeDilationLayer r a ((σ : ℂ) + u * I)‖ ≤ B r := by
    dsimp only [B]
    rw [dif_pos h]
    exact Classical.choose_spec
      (exists_norm_xiMassPrimeDilationLayer_vertical_bound h ha hσ) u
  refine ⟨∑ r ∈ R, ‖b r‖ * B r, fun u => ?_⟩
  rw [xiMassPrimeDilationOrbitLayer_eq_sum hr ha (by simpa using hσ)]
  calc
    ‖∑ r ∈ R, b r *
        xiMassPrimeDilationLayer r a ((σ : ℂ) + u * I)‖ ≤
      ∑ r ∈ R, ‖b r *
        xiMassPrimeDilationLayer r a ((σ : ℂ) + u * I)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r ∈ R, ‖b r‖ * B r := by
      exact Finset.sum_le_sum fun r hrR => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hB (hr r hrR) u) (norm_nonneg _)

def xiMassPrimeDilationOrbitResidual
    (R : Finset ℕ) (b : ℕ → ℂ) (w : Nat.Primes → ℂ)
    (c : ℂ) (a : ℝ) (τ : ℂ) : ℂ :=
  xiMassPrimeMaskResidual
    (fun p => w p - xiMassPrimeDilationOrbitMask R b p) c a τ

theorem xiMassPrimeMaskedLayer_eq_scalar_add_dilationOrbit_add_residual
    {R : Finset ℕ} {b : ℕ → ℂ} (hr : ∀ r ∈ R, 2 ≤ r)
    {w : Nat.Primes → ℂ} {c : ℂ} {a q : ℝ}
    (hhalf : 1 / 2 < q) (hqa : q < a)
    {τ : ℂ} (hτ : 0 < τ.re)
    (hdev : Summable (fun p : Nat.Primes =>
      ‖(w p - xiMassPrimeDilationOrbitMask R b p) - c‖ *
        xiMassPrimePowerCriticalWeight p 0)) :
    xiMassPrimeMaskedLayer w a τ =
      c * xiMassValuationOnePrimeLayer a τ +
        xiMassPrimeDilationOrbitLayer R b a τ +
          xiMassPrimeDilationOrbitResidual R b w c a τ := by
  have ha : 0 < a := by linarith
  have hbase := summable_xiMassPrimeMaskedAtom
    (w := fun p => w p - xiMassPrimeDilationOrbitMask R b p)
    hhalf hqa hτ hdev
  have horbit := summable_xiMassPrimeDilationOrbitMaskedAtom
    (b := b) hr ha hτ
  have hbaseDecomp := xiMassPrimeMaskedLayer_eq_scalar_add_residual
    (w := fun p => w p - xiMassPrimeDilationOrbitMask R b p)
    hhalf hqa hτ hdev
  calc
    xiMassPrimeMaskedLayer w a τ =
        xiMassPrimeMaskedLayer
            (fun p => w p - xiMassPrimeDilationOrbitMask R b p) a τ +
          xiMassPrimeDilationOrbitLayer R b a τ := by
      change (∑' p : Nat.Primes,
          w p * xiMassCenteredPrimeAtom a τ (p : ℕ)) =
        (∑' p : Nat.Primes,
          (w p - xiMassPrimeDilationOrbitMask R b p) *
            xiMassCenteredPrimeAtom a τ (p : ℕ)) +
        ∑' p : Nat.Primes,
          xiMassPrimeDilationOrbitMask R b p *
            xiMassCenteredPrimeAtom a τ (p : ℕ)
      rw [← hbase.tsum_add horbit]
      exact tsum_congr fun p => by ring
    _ = (c * xiMassValuationOnePrimeLayer a τ +
          xiMassPrimeMaskResidual
            (fun p => w p - xiMassPrimeDilationOrbitMask R b p) c a τ) +
        xiMassPrimeDilationOrbitLayer R b a τ := by rw [hbaseDecomp]
    _ = _ := by
      unfold xiMassPrimeDilationOrbitResidual
      ring

theorem exists_norm_xiMassPrimeDilationOrbitResidual_vertical_bound
    {R : Finset ℕ} {b : ℕ → ℂ}
    {w : Nat.Primes → ℂ} {c : ℂ} {a σ : ℝ}
    (hdev : Summable (fun p : Nat.Primes =>
      ‖(w p - xiMassPrimeDilationOrbitMask R b p) - c‖ *
        xiMassPrimePowerCriticalWeight p 0))
    (ha : 0 < a) (hσ : 0 < σ) :
    ∃ B : ℝ, ∀ u : ℝ,
      ‖xiMassPrimeDilationOrbitResidual R b w c a
        ((σ : ℂ) + u * I)‖ ≤ B := by
  simpa only [xiMassPrimeDilationOrbitResidual] using
    exists_norm_xiMassPrimeMaskResidual_vertical_bound
      (w := fun p => w p - xiMassPrimeDilationOrbitMask R b p)
      (c := c) hdev ha hσ

theorem xiMassPrimeDilationOrbitMaskedLineBound_of_scalar_eq_zero
    {R : Finset ℕ} {b : ℕ → ℂ} (hr : ∀ r ∈ R, 2 ≤ r)
    {w : Nat.Primes → ℂ} {c : ℂ} {a q σ : ℝ}
    (hhalf : 1 / 2 < q) (hqa : q < a) (hσ : 0 < σ)
    (hc : c = 0)
    (hdev : Summable (fun p : Nat.Primes =>
      ‖(w p - xiMassPrimeDilationOrbitMask R b p) - c‖ *
        xiMassPrimePowerCriticalWeight p 0)) :
    XiMassPrimeMaskedLineBound w a σ := by
  subst c
  have ha : 0 < a := by linarith
  obtain ⟨O, hO⟩ :=
    exists_norm_xiMassPrimeDilationOrbitLayer_vertical_bound hr ha hσ
  obtain ⟨E, hE⟩ :=
    exists_norm_xiMassPrimeDilationOrbitResidual_vertical_bound hdev ha hσ
  refine ⟨O + E, fun u => ?_⟩
  rw [xiMassPrimeMaskedLayer_eq_scalar_add_dilationOrbit_add_residual
    hr hhalf hqa (τ := ((σ : ℂ) + u * I))
      (by simpa using hσ) hdev, zero_mul, zero_add]
  exact (norm_add_le _ _).trans (add_le_add (hO u) (hE u))

theorem xiMassPrimeDilationOrbitMaskedLineBound_iff_valuationOne
    {R : Finset ℕ} {b : ℕ → ℂ} (hr : ∀ r ∈ R, 2 ≤ r)
    {w : Nat.Primes → ℂ} {c : ℂ} {a q σ : ℝ}
    (hhalf : 1 / 2 < q) (hqa : q < a) (hσ : 0 < σ)
    (hc : c ≠ 0)
    (hdev : Summable (fun p : Nat.Primes =>
      ‖(w p - xiMassPrimeDilationOrbitMask R b p) - c‖ *
        xiMassPrimePowerCriticalWeight p 0)) :
    XiMassPrimeMaskedLineBound w a σ ↔
      XiMassValuationOnePrimeLineBound a σ := by
  have ha : 0 < a := by linarith
  obtain ⟨O, hO⟩ :=
    exists_norm_xiMassPrimeDilationOrbitLayer_vertical_bound hr ha hσ
  obtain ⟨E, hE⟩ :=
    exists_norm_xiMassPrimeDilationOrbitResidual_vertical_bound hdev ha hσ
  have hboundary (u : ℝ) :
      ‖xiMassPrimeDilationOrbitLayer R b a ((σ : ℂ) + u * I) +
          xiMassPrimeDilationOrbitResidual R b w c a
            ((σ : ℂ) + u * I)‖ ≤ O + E :=
    (norm_add_le _ _).trans (add_le_add (hO u) (hE u))
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨‖c⁻¹‖ * (C + (O + E)), fun u => ?_⟩
    have hdecomp :=
      xiMassPrimeMaskedLayer_eq_scalar_add_dilationOrbit_add_residual
        hr hhalf hqa (τ := ((σ : ℂ) + u * I))
          (by simpa using hσ) hdev
    have heq :
        xiMassValuationOnePrimeLayer a ((σ : ℂ) + u * I) =
          c⁻¹ * (xiMassPrimeMaskedLayer w a ((σ : ℂ) + u * I) -
            (xiMassPrimeDilationOrbitLayer R b a ((σ : ℂ) + u * I) +
              xiMassPrimeDilationOrbitResidual R b w c a
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
    refine ⟨‖c‖ * C + (O + E), fun u => ?_⟩
    rw [xiMassPrimeMaskedLayer_eq_scalar_add_dilationOrbit_add_residual
      hr hhalf hqa (τ := ((σ : ℂ) + u * I))
        (by simpa using hσ) hdev]
    rw [add_assoc]
    exact (norm_add_le _ _).trans
      (add_le_add
        (by rw [norm_mul]; exact
          mul_le_mul_of_nonneg_left (hC u) (norm_nonneg _))
        (hboundary u))

theorem riemannHypothesis_iff_xiMassPrimeDilationOrbitMaskedLineBound
    {R : Finset ℕ} {b : ℕ → ℂ} (hr : ∀ r ∈ R, 2 ≤ r)
    {w : Nat.Primes → ℂ} {c : ℂ} {a q σ : ℝ}
    (hhalf : 1 / 2 < q) (hqa : q < a) (hσ : 0 < σ)
    (hc : c ≠ 0)
    (hdev : Summable (fun p : Nat.Primes =>
      ‖(w p - xiMassPrimeDilationOrbitMask R b p) - c‖ *
        xiMassPrimePowerCriticalWeight p 0)) :
    RiemannHypothesis ↔ XiMassPrimeMaskedLineBound w a σ := by
  exact (riemannHypothesis_iff_xiMassValuationOnePrimeLineBound
    hhalf hqa hσ).trans
      (xiMassPrimeDilationOrbitMaskedLineBound_iff_valuationOne
        hr hhalf hqa hσ hc hdev).symm

end

end RHTower
