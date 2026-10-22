import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorDensityPolylog

/-!
# Uniform zero-density estimate with polylogarithmic loss for `7/10 ≤ σ < 1`

This module converts the weighted zeta-zero mass bound at the uniform Gabriel center
`c_σ = σ - (1 - σ)/1000` into a zero-density estimate. Zeros with `Re w ≥ σ` carry weight
`Re w - c_σ ≥ (1 - σ)/1000`, so the multiplicity count of zeros of `(s-1)ζ(s)` in
`[c_σ, 4] × [-(X-2), X-2]` with `Re w ≥ σ` is at most
`K (1 + X^{e(σ)} (1 + log X)^{2θ(σ)} + (1 + log X)^2)` for all large `X`, where
`e(σ) = inghamUniformGabrielConservativeExponent σ` and `θ(σ) = inghamUniformGabrielCriticalShare σ`.

## Main results

- `zetaLittlewoodZeroCountAbove_mul_le_selectedRectangleMass`: `(σ - c)` times the count of zeros
  with `Re w ≥ σ` in `[c, d] × [-T, T]` is at most the weighted zero mass of any taller rectangle
  `[c, d] × [T₁, T₂]` with `T₁ ≤ -T`, `T ≤ T₂`.
- `exists_eventually_zetaLittlewoodZeroCountAbove_le_uniformGabrielPolylog`: for `7/10 ≤ σ < 1`
  there is `K ≥ 0` with zero count above `σ` in `[c_σ, 4] × [-(X-2), X-2]` at most
  `K (1 + X^{e(σ)} (1 + log X)^{2θ(σ)} + (1 + log X)^2)` for all large `X`.

## Hypotheses

The results are unconditional. The density estimate assumes only `7/10 ≤ σ < 1` and holds
eventually in `X`; the comparison lemma assumes `c ≤ d`, `0 ≤ T`, `T₁ ≤ -T` and `T ≤ T₂`.
-/

open Complex Filter Metric Set ArithmeticFunction Finset

namespace RHTower.Sieve

noncomputable section

/-- For `c ≤ d`, `0 ≤ T`, `T₁ ≤ -T`, `T ≤ T₂`: `(σ - c)` times the multiplicity count of zeros of
`(s-1)ζ(s)` in `[c, d] × [-T, T]` with `Re w ≥ σ` is at most `∑ ord_w (Re w - c)` over the zeros
in `[c, d] × [T₁, T₂]`. -/
theorem zetaLittlewoodZeroCountAbove_mul_le_selectedRectangleMass
    {c d T T₁ T₂ sigma : ℝ} (hcd : c ≤ d) (hT : 0 ≤ T)
    (hbot : T₁ ≤ -T) (htop : T ≤ T₂) :
    (sigma - c) * zetaLittlewoodZeroCountAbove c d T sigma ≤
      ∑ w ∈ zetaResidueUnitClosedRectangleZeros
          ((c : ℂ) + (T₁ : ℂ) * I) ((d : ℂ) + (T₂ : ℂ) * I),
        ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) * (w.re - c) := by
  let Zsmall : Finset ℂ := zetaResidueUnitClosedRectangleZeros
    ((c : ℂ) + (-T : ℝ) * I) ((d : ℂ) + T * I)
  let Zlarge : Finset ℂ := zetaResidueUnitClosedRectangleZeros
    ((c : ℂ) + (T₁ : ℂ) * I) ((d : ℂ) + (T₂ : ℂ) * I)
  have hsub : Zsmall ⊆ Zlarge := by
    intro w hw
    have hw' := (mem_zetaResidueUnitClosedRectangleZeros.mp hw)
    apply mem_zetaResidueUnitClosedRectangleZeros.mpr
    refine ⟨?_, hw'.2⟩
    rw [Complex.mem_reProdIm] at hw' ⊢
    constructor
    · simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.neg_im, Complex.ofReal_im, I_re, I_im, mul_zero, zero_mul,
        mul_one, sub_zero, add_zero] using hw'.1.1
    · have him := hw'.1.2
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add] at him ⊢
      rw [Set.uIcc_of_le (by linarith)] at him ⊢
      constructor <;> linarith [him.1, him.2]
  have hmono : zetaLittlewoodZeroMass c d T ≤
      ∑ w ∈ Zlarge,
        ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) * (w.re - c) := by
    dsimp only [zetaLittlewoodZeroMass, Zsmall]
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro w hwlarge _
    have hwK := (mem_zetaResidueUnitClosedRectangleZeros.mp hwlarge).1
    have hwre := (Complex.mem_reProdIm.mp hwK).1
    have hwre' : w.re ∈ Set.Icc c d := by
      simpa [Zlarge, Set.uIcc_of_le hcd] using hwre
    exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hwre'.1)
  calc
    _ ≤ zetaLittlewoodZeroMass c d T :=
      zetaLittlewoodZeroCountAbove_mul_le_zeroMass hcd
    _ ≤ ∑ w ∈ Zlarge,
        ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) * (w.re - c) := hmono
    _ = _ := rfl

/-- Zero density for `7/10 ≤ σ < 1`: some `K ≥ 0` bounds the multiplicity count of zeta zeros in
`[c_σ, 4] × [-(X-2), X-2]` with `Re w ≥ σ` by `K (1 + X^{e(σ)} (1 + log X)^{2θ(σ)} + (1 + log X)^2)`
for all large `X`. -/
theorem exists_eventually_zetaLittlewoodZeroCountAbove_le_uniformGabrielPolylog
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ X : ℕ in Filter.atTop,
      zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter sigma) 4
          ((X : ℝ) - 2) sigma ≤
        K * (1 +
          (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
            (1 + Real.log (X : ℝ)) ^
              (2 * inghamUniformGabrielCriticalShare sigma) +
          (1 + Real.log (X : ℝ)) ^ (2 : ℕ)) := by
  obtain ⟨K₀, hK₀, hmass⟩ :=
    exists_eventually_zetaZeroMass_le_uniformGabrielPolylog hsigma0 hsigma1
  let q : ℝ := 2 * Real.pi * (1 - sigma) / 1000
  let K : ℝ := K₀ / q
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [hmass, eventually_ge_atTop (10 : ℕ)] with X hselected hX
  obtain ⟨T₁, hT₁, T₂, hT₂, hmassX⟩ := hselected
  have hXR : (10 : ℝ) ≤ X := by exact_mod_cast hX
  have hTnonneg : 0 ≤ (X : ℝ) - 2 := by linarith
  have hbot : T₁ ≤ -((X : ℝ) - 2) := by linarith [hT₁.2]
  have htop : (X : ℝ) - 2 ≤ T₂ := le_of_lt hT₂.1
  have hcenter4 : inghamUniformGabrielCenter sigma ≤ 4 := by
    unfold inghamUniformGabrielCenter
    linarith
  have hcountMass :=
    zetaLittlewoodZeroCountAbove_mul_le_selectedRectangleMass
      (c := inghamUniformGabrielCenter sigma) (d := 4) (T := (X : ℝ) - 2)
      (T₁ := T₁) (T₂ := T₂) (sigma := sigma)
      hcenter4 hTnonneg hbot htop
  have hgap : sigma - inghamUniformGabrielCenter sigma = (1 - sigma) / 1000 := by
    unfold inghamUniformGabrielCenter
    ring
  rw [hgap] at hcountMass
  have hscaled :
      q * zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter sigma) 4
          ((X : ℝ) - 2) sigma ≤
        K₀ * (1 +
          (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
            (1 + Real.log (X : ℝ)) ^
              (2 * inghamUniformGabrielCriticalShare sigma) +
          (1 + Real.log (X : ℝ)) ^ (2 : ℕ)) := by
    calc
      _ = 2 * Real.pi * (((1 - sigma) / 1000) *
          zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter sigma) 4
            ((X : ℝ) - 2) sigma) := by dsimp only [q]; ring
      _ ≤ 2 * Real.pi *
          (∑ w ∈ zetaResidueUnitClosedRectangleZeros
              ((inghamUniformGabrielCenter sigma : ℂ) + (T₁ : ℂ) * I)
              ((4 : ℂ) + (T₂ : ℂ) * I),
            ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) *
              (w.re - inghamUniformGabrielCenter sigma)) :=
        mul_le_mul_of_nonneg_left hcountMass (by positivity)
      _ ≤ _ := hmassX
  apply le_of_mul_le_mul_left (a := q) (a0 := hq)
  calc
    q * zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter sigma) 4
          ((X : ℝ) - 2) sigma ≤
        K₀ * (1 +
          (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
            (1 + Real.log (X : ℝ)) ^
              (2 * inghamUniformGabrielCriticalShare sigma) +
          (1 + Real.log (X : ℝ)) ^ (2 : ℕ)) := hscaled
    _ = q * (K * (1 +
          (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
            (1 + Real.log (X : ℝ)) ^
              (2 * inghamUniformGabrielCriticalShare sigma) +
          (1 + Real.log (X : ℝ)) ^ (2 : ℕ))) := by
      dsimp only [K]
      field_simp [hq.ne']

end

end RHTower.Sieve
