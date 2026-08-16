import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Even-seam finite parts: no logarithm, cutoff independence, Hankel shape

The seam expansion of a singular reciprocal pullback pairs a Laurent monomial `t^{-2n-2}` with an
even local jet `t^{2r}`, so every seam exponent is **even**.  Three consequences, all
distribution-free:

* an even exponent is never `-1`, so the punctured-seam integral of a seam monomial is a pure power
  of the regulator with **no logarithm** — the logarithm appears exactly at the excluded exponent
  `-1`;
* consequently the Hadamard finite part of a seam monomial is the cutoff-independent constant
  `1/(a+1)`;
* the difference of two seam cutoffs, after the substitution `t = ε u`, contributes exactly the
  factor `ε^{a+1}`, hence no constant when `a ≠ -1` — this is the cutoff independence of the finite
  part;
* the resulting bilinear form is Hankel, because it sees `p` and `q` only through the coefficients
  of the product `p q`.

## Main results

* `evenSeamExponent_ne_neg_one` — the parity obstruction;
* `integral_seamMonomial`, `finitePart_seamMonomial` — no logarithm, cutoff-independent constant;
* `integral_seamLog` — the contrasting logarithmic case at exponent `-1`;
* `seamCutoffScaling` — the cutoff-difference is a pure power of the regulator;
* `hankel_of_productCoeff` — the bilinear form is Hankel.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

/-! ### The parity obstruction -/

/-- The seam exponent produced by pairing the Laurent monomial `t^{-2n-2}` with the even local jet
`t^{2r}`. -/
def seamExponent (r n : ℕ) : ℤ := 2 * (r : ℤ) - 2 * (n : ℤ) - 2

/-- **Every seam exponent is even.** -/
theorem even_seamExponent (r n : ℕ) : Even (seamExponent r n) := by
  refine ⟨(r : ℤ) - (n : ℤ) - 1, ?_⟩
  unfold seamExponent
  ring

/-- **No logarithmic seam term.**  An even exponent is never `-1`, so the seam expansion of an even
source has no `t^{-1}` term and therefore no logarithm. -/
theorem evenSeamExponent_ne_neg_one (r n : ℕ) : seamExponent r n ≠ -1 := by
  intro h
  have hev := even_seamExponent r n
  rw [h] at hev
  obtain ⟨k, hk⟩ := hev
  omega

/-! ### The punctured-seam integral -/

/-- **The punctured-seam integral of a seam monomial.**  For any exponent other than `-1` the
regulated integral is an explicit pure power of the regulator: no logarithm appears. -/
theorem integral_seamMonomial {a : ℤ} (ha : a ≠ -1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ t in ε..(1 : ℝ), t ^ a) = (1 - ε ^ (a + 1)) / ((a : ℝ) + 1) := by
  have hzero : (0 : ℝ) ∉ Set.uIcc ε 1 := by
    rw [Set.uIcc_of_le hε1]
    intro hmem
    exact absurd hmem.1 (not_le.mpr hε)
  rw [integral_zpow (Or.inr ⟨ha, hzero⟩), one_zpow]

/-- The Hadamard finite part of a seam monomial: the regulator-independent constant obtained after
subtracting the pure-power counterterm. -/
theorem finitePart_seamMonomial {a : ℤ} (ha : a ≠ -1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ t in ε..(1 : ℝ), t ^ a) + (ε ^ (a + 1)) / ((a : ℝ) + 1) = 1 / ((a : ℝ) + 1) := by
  rw [integral_seamMonomial ha hε hε1]
  ring

/-- **The contrasting logarithmic case.**  At the excluded exponent `-1` the regulated integral is a
logarithm — which is exactly what the even seam normalization forbids. -/
theorem integral_seamLog {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ t in ε..(1 : ℝ), t ⁻¹) = -Real.log ε := by
  have hzero : (0 : ℝ) ∉ Set.uIcc ε 1 := by
    rw [Set.uIcc_of_le hε1]
    intro hmem
    exact absurd hmem.1 (not_le.mpr hε)
  rw [integral_inv hzero, one_div, Real.log_inv]

/-! ### Cutoff independence -/

/-- **Seam cutoff scaling.**  The substitution `t = ε u` turns a cutoff-profile integral of a seam
monomial into `ε^{a+1}` times a regulator-free integral.  Since `a + 1 ≠ 0` for an even `a`, the
difference of two seam cutoffs contributes only a pure power and never a constant: the Hadamard
finite part does not depend on the seam cutoff. -/
theorem seamCutoffScaling (a : ℤ) {ε : ℝ} (hε : 0 < ε) (g : ℝ → ℝ) (s S : ℝ) :
    (∫ t in s..S, t ^ a * g (t / ε)) = ε ^ (a + 1) * ∫ u in (s / ε)..(S / ε), u ^ a * g u := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hcomp := intervalIntegral.integral_comp_div
    (f := fun u : ℝ => (ε * u) ^ a * g u) (a := s) (b := S) hεne
  have hlhs : (∫ t in s..S, ((ε * (t / ε)) ^ a * g (t / ε)))
      = ∫ t in s..S, t ^ a * g (t / ε) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have hcancel : ε * (t / ε) = t := by field_simp
    rw [hcancel]
  rw [← hlhs, hcomp]
  have hpull : (∫ u in (s / ε)..(S / ε), (ε * u) ^ a * g u)
      = ε ^ a * ∫ u in (s / ε)..(S / ε), u ^ a * g u := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    rw [mul_zpow]
    ring
  rw [hpull, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [zpow_add₀ hεne, zpow_one]
  ring

/-! ### The Hankel shape -/

/-- **The seam bilinear form is Hankel.**  A functional that sees the two coefficient sequences only
through the coefficients of their convolution is the Hankel form `Σ_{i,j} c_i d_j f_{i+j}`. -/
theorem hankel_of_productCoeff {R : Type*} [CommSemiring R] (f c d : ℕ → R) (N : ℕ)
    (hc : ∀ i, N < i → c i = 0) (hd : ∀ j, N < j → d j = 0) :
    ∑ n ∈ Finset.range (2 * N + 1),
        f n * (∑ ij ∈ Finset.antidiagonal n, c ij.1 * d ij.2)
      = ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
          c i * d j * f (i + j) := by
  classical
  have hbox : ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), c i * d j * f (i + j)
      = ∑ ij ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
          c ij.1 * d ij.2 * f (ij.1 + ij.2) := by
    rw [Finset.sum_product]
  rw [hbox]
  have hmaps : ∀ ij ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
      ij.1 + ij.2 ∈ Finset.range (2 * N + 1) := by
    intro ij hij
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hij
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun ij => c ij.1 * d ij.2 * f (ij.1 + ij.2))]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have hsub : (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
      (fun ij => ij.1 + ij.2 = n) ⊆ Finset.antidiagonal n := by
    intro ij hij
    rw [Finset.mem_filter] at hij
    exact Finset.mem_antidiagonal.mpr hij.2
  have hvanish : ∀ ij ∈ Finset.antidiagonal n,
      ij ∉ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter (fun ij => ij.1 + ij.2 = n) →
      c ij.1 * d ij.2 * f (ij.1 + ij.2) = 0 := by
    intro ij hij hnot
    have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
    have hbig : N < ij.1 ∨ N < ij.2 := by
      by_contra hcon
      push Not at hcon
      exact hnot (Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
          Finset.mem_range.mpr (by omega)⟩, hsum⟩)
    rcases hbig with h | h
    · rw [hc ij.1 h, zero_mul, zero_mul]
    · rw [hd ij.2 h, mul_zero, zero_mul]
  rw [Finset.mul_sum]
  have hL : ∑ ij ∈ Finset.antidiagonal n, f n * (c ij.1 * d ij.2)
      = ∑ ij ∈ Finset.antidiagonal n, c ij.1 * d ij.2 * f (ij.1 + ij.2) := by
    refine Finset.sum_congr rfl (fun ij hij => ?_)
    rw [Finset.mem_antidiagonal.mp hij]
    ring
  rw [hL]
  exact (Finset.sum_subset hsub hvanish).symm

end GaloisForLFunctions.HTGeometry
