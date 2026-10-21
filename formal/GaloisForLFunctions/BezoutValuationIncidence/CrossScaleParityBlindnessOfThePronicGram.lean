import GaloisForLFunctions.BezoutValuationIncidence.FlatLargeScaleRowsAndTheTypeIGain

/-!
# Cross-scale parity blindness of the pronic Gram

The Bernoulli kernel depends on the large modulus only through its residue: `𝔅(d, n) = 𝔅(d, n mod d)`.
In the second-order law the large-scale row therefore enters only through the weighted residue masses

`ρ_{c'}(d, r) = Σ_{n ≡ r (mod d)} c'(n)/n²`

and through the two readouts `R(c')`, `H(c')`. Precisely,

`Σ_{n, d} c'(n) c(d) 𝔅(d, n)/(d n²) = Σ_d (c(d)/d) Σ_{r < d} 𝔅(d, r) ρ_{c'}(d, r)`,

and for two large-scale rows `c'₁, c'₂` with the same residue masses modulo every small modulus of `c`,

`|B(c, c'₁) - B(c, c'₂) + m(c)(R(c'₁) - R(c'₂)) + β(c)(H(c'₁) - H(c'₂))|
  ≤ ¾ Σ_d |c(d)| d² (Σ_n |c'₁(n)|/n³ + Σ_n |c'₂(n)|/n³)`.

The cross-scale pronic Gram cannot distinguish two large-scale coefficient sequences with the same local
distribution modulo the small moduli. Examples are primes and products of two large primes with matched
residue statistics, or the Liouville function and the constant row on integers free of small primes.
Any input that separates them, such as parity, must come from elsewhere: from the large-scale rows'
own Gram, or from the interaction near the diagonal of scales.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- The weighted residue mass `ρ_{c'}(d, r) = Σ_{n ≤ N, n ≡ r (d)} c'(n)/n²`. -/
def residueMass (N : ℕ) (c' : ℕ → ℝ) (d r : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => n % d = r), c' n / (n : ℝ) ^ 2

/-- The kernel term in residue form: `Σ_n c'(n) 𝔅(d, n)/n² = Σ_{r < d} 𝔅(d, r) ρ_{c'}(d, r)`. -/
theorem sum_mul_bernoulliKernel_eq_residueMass {d : ℕ} (hd : 0 < d) (N : ℕ) (c' : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, c' n * (bernoulliKernel d n / (n : ℝ) ^ 2) =
      ∑ r ∈ range d, bernoulliKernel d r * residueMass N c' d r := by
  simp only [residueMass, mul_sum]
  rw [← sum_fiberwise_of_maps_to (g := fun n => n % d) (t := range d)
    (fun n _ => mem_range.mpr (Nat.mod_lt n hd))]
  refine sum_congr rfl fun r _ => sum_congr rfl fun n hn => ?_
  rw [bernoulliKernel_mod d n, (mem_filter.mp hn).2]
  ring

/-- **Cross-scale parity blindness.** If `c'₁, c'₂` have the same weighted residue masses modulo every
modulus of `c`, their cross-scale Grams with `c` differ only through the readouts `R, H`, up to
`¾ Σ|c|d² (Σ|c'₁|/n³ + Σ|c'₂|/n³)`. -/
theorem abs_rowBilinear_sub_of_residueMass_eq (N : ℕ) {c c'₁ c'₂ : ℕ → ℝ}
    (hmass : ∀ d ∈ Icc 1 N, c d ≠ 0 → ∀ r < d, residueMass N c'₁ d r = residueMass N c'₂ d r) :
    |rowBilinear N c c'₁ - rowBilinear N c c'₂ +
        rowMean N c * (vonMangoldtReadout N c'₁ - vonMangoldtReadout N c'₂) +
        rowBeta N c * (finiteHarmonicSum N c'₁ - finiteHarmonicSum N c'₂)| ≤
      3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) *
        (∑ n ∈ Icc 1 N, |c'₁ n| / (n : ℝ) ^ 3 + ∑ n ∈ Icc 1 N, |c'₂ n| / (n : ℝ) ^ 3) := by
  have h1 := abs_rowBilinear_add_mean_add_beta_sub_bernoulli_le N c c'₁
  have h2 := abs_rowBilinear_add_mean_add_beta_sub_bernoulli_le N c c'₂
  set M₁ := ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c'₁ n * (c d / d) * (bernoulliKernel d n / (n : ℝ) ^ 2)
  set M₂ := ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c'₂ n * (c d / d) * (bernoulliKernel d n / (n : ℝ) ^ 2)
  have hM : M₁ = M₂ := by
    simp only [M₁, M₂]
    rw [sum_comm, sum_comm (s := Icc 1 N) (t := Icc 1 N) (f := fun n d =>
      c'₂ n * (c d / d) * (bernoulliKernel d n / (n : ℝ) ^ 2))]
    refine sum_congr rfl fun d hd => ?_
    by_cases hcd : c d = 0
    · simp [hcd]
    have hd0 : 0 < d := (mem_Icc.mp hd).1
    have e : ∀ c' : ℕ → ℝ, ∑ n ∈ Icc 1 N, c' n * (c d / d) * (bernoulliKernel d n / (n : ℝ) ^ 2) =
        c d / d * ∑ r ∈ range d, bernoulliKernel d r * residueMass N c' d r := fun c' => by
      rw [← sum_mul_bernoulliKernel_eq_residueMass hd0, mul_sum]
      exact sum_congr rfl fun n _ => by ring
    rw [e, e]
    congr 1
    exact sum_congr rfl fun r hr => by rw [hmass d hd hcd r (mem_range.mp hr)]
  have heq : rowBilinear N c c'₁ - rowBilinear N c c'₂ +
      rowMean N c * (vonMangoldtReadout N c'₁ - vonMangoldtReadout N c'₂) +
      rowBeta N c * (finiteHarmonicSum N c'₁ - finiteHarmonicSum N c'₂) =
      (rowBilinear N c c'₁ + rowMean N c * vonMangoldtReadout N c'₁ +
        rowBeta N c * finiteHarmonicSum N c'₁ - M₁) -
      (rowBilinear N c c'₂ + rowMean N c * vonMangoldtReadout N c'₂ +
        rowBeta N c * finiteHarmonicSum N c'₂ - M₂) := by rw [hM]; ring
  rw [heq]
  calc |_ - _| ≤ |_| + |_| := abs_sub _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

end

end GaloisForLFunctions.BezoutValuationIncidence
