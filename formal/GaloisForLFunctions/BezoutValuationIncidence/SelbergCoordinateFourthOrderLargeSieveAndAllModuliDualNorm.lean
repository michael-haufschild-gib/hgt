import GaloisForLFunctions.BezoutValuationIncidence.FourierFormOfTheCubicKernelAndFourthOrderLargeSieve
import GaloisForLFunctions.BezoutValuationIncidence.LargeSieveDispersionForBoundedRows

/-!
# Fourth-order large-sieve dispersion in Selberg coordinates and the all-moduli dual norm

This module connects five parts of the `BezoutValuationIncidence` library at Wall 17:
1. the filtered cyclotomic Fourier representations of the centred quadratic and cubic Bernoulli
   kernels at all moduli (`FourierFormOfTheCubicKernelAndFourthOrderLargeSieve`),
2. the canonical primitive spectral decomposition and Selberg multiples coordinates
   `Y_{N,c}(e) = Σ_{e ∣ d} c(d)/d` (`CanonicalPrimitiveSpectralFormAndJordanWindowEnergy`,
   `LargeSieveDispersionInSelbergCoordinates`),
3. the harmonic-sum Selberg-coordinate bounds for bounded small-scale rows `|c| ≤ 1`
   (`LargeSieveDispersionForBoundedRows`),
4. the all-moduli residue mean `m_d` and fourth-order dual-norm reduction
   (`KernelMeanAtCompositeModuliAndTheAllRowsLaws`), and
5. the residue-discrepancy law (`ResidueDiscrepancyIsTheExactCrossScaleLoss`) and the sharp
   Montgomery–Vaughan large sieve (`LargeSieveWithTheMontgomeryVaughanConstant`).

## Main results

* **§1. All-moduli residue discrepancy laws at third and fourth order (zero hypotheses).**
  `abs_sum_mul_bernoulliKernel_sub_kernelMean_le_discrepancy` and
  `abs_sum_mul_cubicKernel_le_discrepancy` bound the quadratic and cubic kernel pairings at every
  modulus `d ≥ 1` (prime or composite) by the `ℓ¹` residue discrepancies `Δ_d(c')` and
  `Δ_{d,3}(c')`. This removes the primality hypothesis from
  `abs_rowBilinear_add_mean_add_beta_sub_equidistributed_le` in
  `ResidueDiscrepancyIsTheExactCrossScaleLoss`, yielding the unconditional all-moduli laws
  `abs_rowBilinear_sub_kernelMeanMain_le_discrepancy` and
  `abs_rowBilinear_sub_kernelMeanMain_le_fourthOrder_discrepancy`.

* **§2. The cyclotomic–Selberg bridge at all moduli (zero hypotheses).**
  For `d ∈ [1, N]`, a complex root `η` lies in `nontrivialRoots d` iff `η ∈ primitiveRoots' N` and
  `orderOf η ∣ d`. Interchanging the modulus sum `Σ_{d ≤ N} (c(d)/d)` with the cyclotomic sum over
  `nontrivialRoots d` collapses the divisor-overlapping moduli into the disjoint primitive-root
  families `primitiveRoots e ℂ` (`2 ≤ e ≤ N`) weighted by the Selberg coordinates `Y_{N,c}(e)`
  (`sum_mul_sum_nontrivialRoots_eq_primitiveRoots'`, `sum_mul_sum_nontrivialRoots_eq_selberg`).
  Applying this bridge to both layers of `kernelStatisticAll` gives exact Selberg-coordinate
  spectral identities (`sum_mul_residuePotential_sub_gcd_eq_selberg`,
  `sum_mul_cubicDiff_eq_selberg`).

* **§3. Fourth-order large-sieve dispersion in Selberg coordinates.**
  Combining the Selberg-coordinate spectral identities with the fourth- and sixth-order Farey
  moment bounds and the sharp Montgomery–Vaughan dilated large sieve (`L + Q₀² - 1`) disperses
  both the quadratic and cubic cross-scale layers for every small-scale row `c`
  (`abs_sum_mul_kernelStatisticAll_le_selberg`,
  `abs_rowBilinear_sub_kernelMeanMain_le_selberg_fourthOrder`, and the hypothesis-free all-inputs
  law `abs_rowBilinear_sub_kernelMeanMain_le_selberg_all`). This upgrades
  `LargeSieveDispersionInSelbergCoordinates` from third order and `L + 2Q₀² - 1` to fourth order
  and `L + Q₀² - 1`.

* **§4. The all-moduli dual-norm large sieve and fourth-order dispersion for bounded rows.**
  Forcomposite moduli `d ∈ S`, the sets `nontrivialRoots d` overlap across common divisors.
  Linearizing the strong `ℓ¹` dual norm `Σ_{d ∈ S} |Λ_d^{all}(c')|/d` by the sign witness
  `c(d) = ±1` on `S` and passing through the cyclotomic–Selberg bridge resolves the divisor
  overlap via `|Y_{N,c}(e)| ≤ 2√(Q₀/e)/e`. This proves the all-moduli fourth-order dual-norm large
  sieve (`dual_norm_kernelStatisticAll_le_largeSieve`,
  `dual_norm_kernelStatisticAll_all_le_largeSieve`) and upgrades
  `LargeSieveDispersionForBoundedRows` to fourth order with the sharp Montgomery–Vaughan constant
  (`abs_rowBilinear_sub_kernelMeanMain_le_bounded_fourthOrder`).
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. All-moduli residue discrepancy laws at third and fourth order -/

/-- At every modulus `d ≥ 1`, `Σ_{r < d} 𝔅(d, r) = d · m_d`. -/
theorem sum_range_bernoulliKernel_eq_mul_kernelMean (d : ℕ) :
    ∑ r ∈ range d, bernoulliKernel d r = (d : ℝ) * kernelMean d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [kernelMean]
  · have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    unfold kernelMean
    field_simp

/-- **Quadratic residue discrepancy bound at every modulus.** For every `d ≥ 1` (prime or
composite), `|Σ_n (c'(n)/n²)(𝔅(d, n) - m_d)| ≤ (π²(d² - 1)/72) Δ_d(c')`. -/
theorem abs_sum_mul_bernoulliKernel_sub_kernelMean_le_discrepancy {d : ℕ} (hd : 0 < d) (N : ℕ)
    (c' : ℕ → ℝ) :
    |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * (bernoulliKernel d n - kernelMean d)| ≤
      Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 72 * residueDiscrepancy N c' d := by
  set S' := ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hsplit1 : ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * (bernoulliKernel d n - kernelMean d) =
      ∑ n ∈ Icc 1 N, c' n * (bernoulliKernel d n / (n : ℝ) ^ 2) - kernelMean d * S' := by
    simp only [S', mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [hsplit1, sum_mul_bernoulliKernel_eq_residueMass hd]
  have hsplit2 : ∑ r ∈ range d, bernoulliKernel d r * residueMass N c' d r - kernelMean d * S' =
      ∑ r ∈ range d, bernoulliKernel d r * (residueMass N c' d r - S' / d) := by
    have e : ∑ r ∈ range d, bernoulliKernel d r * (residueMass N c' d r - S' / d) =
        ∑ r ∈ range d, bernoulliKernel d r * residueMass N c' d r -
          (∑ r ∈ range d, bernoulliKernel d r) * (S' / d) := by
      rw [sum_mul, ← sum_sub_distrib]
      exact sum_congr rfl fun r _ => by ring
    rw [e, sum_range_bernoulliKernel_eq_mul_kernelMean]
    field_simp
  rw [hsplit2, residueDiscrepancy, mul_sum]
  rcases Nat.lt_or_ge d 2 with hd1 | hd2
  · have : d = 1 := by omega
    subst this
    simp [bernoulliKernel_one]
  · refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_bernoulliKernel_le_sharp hd2 r) (abs_nonneg _)

/-- The cubic weighted residue mass `ρ_{c',3}(d, r) = Σ_{n ≤ N, n ≡ r (mod d)} c'(n)/n³`. -/
def cubicResidueMass (N : ℕ) (c' : ℕ → ℝ) (d r : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => n % d = r), c' n / (n : ℝ) ^ 3

/-- The cubic `ℓ¹` residue discrepancy `Δ_{d,3}(c') = Σ_{r < d} |ρ_{c',3}(d, r) - S'_3/d|`. -/
def cubicResidueDiscrepancy (N : ℕ) (c' : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ r ∈ range d, |cubicResidueMass N c' d r - (∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3) / d|

/-- The cubic kernel pairing in residue form:
`Σ_n (c'(n)/n³) 𝔅₃(d, n) = Σ_{r < d} 𝔅₃(d, r) ρ_{c',3}(d, r)`. -/
theorem sum_mul_cubicKernel_eq_cubicResidueMass {d : ℕ} (hd : 0 < d) (N : ℕ) (c' : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 * cubicKernel d n =
      ∑ r ∈ range d, cubicKernel d r * cubicResidueMass N c' d r := by
  simp only [cubicResidueMass, mul_sum]
  rw [← sum_fiberwise_of_maps_to (g := fun n => n % d) (t := range d)
    (fun n _ => mem_range.mpr (Nat.mod_lt n hd))]
  refine sum_congr rfl fun r _ => sum_congr rfl fun n hn => ?_
  rw [cubicKernel_mod d n, (mem_filter.mp hn).2]
  ring

/-- **Cubic residue discrepancy bound at every modulus.** For every `d ≥ 1`,
`|Σ_n (c'(n)/n³) 𝔅₃(d, n)| ≤ d³ Δ_{d,3}(c')`. -/
theorem abs_sum_mul_cubicKernel_le_discrepancy {d : ℕ} (hd : 0 < d) (N : ℕ) (c' : ℕ → ℝ) :
    |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 * cubicKernel d n| ≤
      (d : ℝ) ^ 3 * cubicResidueDiscrepancy N c' d := by
  set S₃ := ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3
  rw [sum_mul_cubicKernel_eq_cubicResidueMass hd]
  have hsplit : ∑ r ∈ range d, cubicKernel d r * cubicResidueMass N c' d r =
      ∑ r ∈ range d, cubicKernel d r * (cubicResidueMass N c' d r - S₃ / d) := by
    have e : ∑ r ∈ range d, cubicKernel d r * (cubicResidueMass N c' d r - S₃ / d) =
        ∑ r ∈ range d, cubicKernel d r * cubicResidueMass N c' d r -
          (∑ r ∈ range d, cubicKernel d r) * (S₃ / d) := by
      rw [sum_mul, ← sum_sub_distrib]
      exact sum_congr rfl fun r _ => by ring
    rw [e, sum_range_cubicKernel hd, zero_mul, sub_zero]
  rw [hsplit, cubicResidueDiscrepancy, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_cubicKernel_le hd r) (abs_nonneg _)

/-- **Combined kernel statistic bound via residue discrepancies at every modulus.** -/
theorem abs_kernelStatisticAll_le_discrepancy {d : ℕ} (hd : 0 < d) (N : ℕ) (c' : ℕ → ℝ) :
    |kernelStatisticAll N c' d| ≤
      Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 72 * residueDiscrepancy N c' d +
        (d : ℝ) ^ 3 * cubicResidueDiscrepancy N c' d := by
  unfold kernelStatisticAll
  rw [sum_add_distrib]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_sum_mul_bernoulliKernel_sub_kernelMean_le_discrepancy hd N c')
    (abs_sum_mul_cubicKernel_le_discrepancy hd N c'))

/-- **Unconditional all-moduli third-order residue discrepancy law (zero hypotheses).**
Removes the primality hypothesis `(hc : ∀ d, c d ≠ 0 → d.Prime)` from
`abs_rowBilinear_add_mean_add_beta_sub_equidistributed_le`. -/
theorem abs_rowBilinear_sub_kernelMeanMain_le_discrepancy (N : ℕ) (c c' : ℕ → ℝ) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' - kernelMeanMain N c c'| ≤
      Real.pi ^ 2 / 72 * ∑ d ∈ Icc 1 N, |c d| * (((d : ℝ) ^ 2 - 1) / d) * residueDiscrepancy N c' d +
        3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 := by
  have hlaw := abs_rowBilinear_add_mean_add_beta_sub_bernoulli_le N c c'
  set E := rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
    rowBeta N c * finiteHarmonicSum N c'
  set K := ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) * (bernoulliKernel d n / (n : ℝ) ^ 2)
  set S' := ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2
  have hK : K - kernelMeanMain N c c' =
      ∑ d ∈ Icc 1 N, c d / d *
        ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * (bernoulliKernel d n - kernelMean d) := by
    have e1 : kernelMeanMain N c c' = ∑ d ∈ Icc 1 N, S' * (c d * kernelMean d / d) := by
      rw [kernelMeanMain]; exact mul_sum _ _ _
    simp only [K]
    rw [sum_comm, e1, ← sum_sub_distrib]
    refine sum_congr rfl fun d _ => ?_
    have e2 : S' * (c d * kernelMean d / d) =
        ∑ n ∈ Icc 1 N, c d / d * (c' n / (n : ℝ) ^ 2 * kernelMean d) := by
      simp only [S', sum_mul]
      exact sum_congr rfl fun n _ => by ring
    rw [e2, ← sum_sub_distrib, mul_sum]
    exact sum_congr rfl fun n _ => by ring
  have hmain : |K - kernelMeanMain N c c'| ≤
      Real.pi ^ 2 / 72 *
        ∑ d ∈ Icc 1 N, |c d| * (((d : ℝ) ^ 2 - 1) / d) * residueDiscrepancy N c' d := by
    rw [hK, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
    have hd0 : 0 < d := (mem_Icc.mp hd).1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    rw [abs_mul, abs_div, abs_of_pos hdR]
    calc |c d| / d * |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * (bernoulliKernel d n - kernelMean d)|
        ≤ |c d| / d * (Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 72 * residueDiscrepancy N c' d) :=
          mul_le_mul_of_nonneg_left
            (abs_sum_mul_bernoulliKernel_sub_kernelMean_le_discrepancy hd0 N c') (by positivity)
      _ = Real.pi ^ 2 / 72 * (|c d| * (((d : ℝ) ^ 2 - 1) / d) * residueDiscrepancy N c' d) := by
          ring
  calc |E - kernelMeanMain N c c'| ≤ |E - K| + |K - kernelMeanMain N c c'| := abs_sub_le _ _ _
    _ ≤ 3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 +
          Real.pi ^ 2 / 72 *
            ∑ d ∈ Icc 1 N, |c d| * (((d : ℝ) ^ 2 - 1) / d) * residueDiscrepancy N c' d :=
        add_le_add hlaw hmain
    _ = _ := by ring

/-- **Unconditional all-moduli fourth-order residue discrepancy law (zero hypotheses).** -/
theorem abs_rowBilinear_sub_kernelMeanMain_le_fourthOrder_discrepancy (N : ℕ) (c c' : ℕ → ℝ) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' - kernelMeanMain N c c'| ≤
      ∑ d ∈ Icc 1 N, |c d| / d *
          (Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 72 * residueDiscrepancy N c' d +
            (d : ℝ) ^ 3 * cubicResidueDiscrepancy N c' d) +
        6 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 := by
  have hlaw := abs_rowBilinear_sub_kernelStatisticAll_le N c c'
  set E := rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
    rowBeta N c * finiteHarmonicSum N c' - kernelMeanMain N c c'
  set K := ∑ d ∈ Icc 1 N, c d / d * kernelStatisticAll N c' d
  have hK : |K| ≤ ∑ d ∈ Icc 1 N, |c d| / d *
      (Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 72 * residueDiscrepancy N c' d +
        (d : ℝ) ^ 3 * cubicResidueDiscrepancy N c' d) := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
    have hd0 : 0 < d := (mem_Icc.mp hd).1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    rw [abs_mul, abs_div, abs_of_pos hdR]
    exact mul_le_mul_of_nonneg_left (abs_kernelStatisticAll_le_discrepancy hd0 N c') (by positivity)
  have hsplit := abs_sub_abs_le_abs_sub E K
  linarith

/-! ## §2. The cyclotomic–Selberg bridge at all moduli -/

/-- For `d ∈ [1, N]`, a root `η` lies in `nontrivialRoots d` iff `η ∈ primitiveRoots' N` and
`orderOf η ∣ d`. -/
theorem mem_nontrivialRoots_iff_mem_primitiveRoots'_and_orderOf_dvd {N d : ℕ} (hd : d ∈ Icc 1 N)
    (η : ℂ) :
    η ∈ nontrivialRoots d ↔ η ∈ primitiveRoots' N ∧ orderOf η ∣ d := by
  have hd0 : 0 < d := (mem_Icc.mp hd).1
  rw [mem_nontrivialRoots hd0, primitiveRoots', mem_erase]
  constructor
  · rintro ⟨h1, hpow⟩
    exact ⟨⟨h1, mem_biUnion.mpr ⟨d, hd, (Polynomial.mem_nthRootsFinset hd0 1).mpr hpow⟩⟩,
      orderOf_dvd_iff_pow_eq_one.mpr hpow⟩
  · rintro ⟨⟨h1, _⟩, hdvd⟩
    exact ⟨h1, orderOf_dvd_iff_pow_eq_one.mp hdvd⟩

/-- `nontrivialRoots d` as the `orderOf η ∣ d` slice of `primitiveRoots' N`. -/
theorem nontrivialRoots_eq_filter_primitiveRoots' {N d : ℕ} (hd : d ∈ Icc 1 N) :
    nontrivialRoots d = (primitiveRoots' N).filter (fun η => orderOf η ∣ d) := by
  ext η
  rw [mem_filter, mem_nontrivialRoots_iff_mem_primitiveRoots'_and_orderOf_dvd hd]

/-- **The cyclotomic–Selberg bridge on `primitiveRoots' N` (zero hypotheses).**
Interchanging `Σ_{d ≤ N} (c(d)/d)` with `Σ_{η ∈ nontrivialRoots d}` groups every nontrivial root
with the Selberg coordinate `Y_{N,c}(ord η)` of its primitive order. -/
theorem sum_mul_sum_nontrivialRoots_eq_primitiveRoots' (N : ℕ) (c : ℕ → ℝ) (F : ℂ → ℂ) :
    ∑ d ∈ Icc 1 N, ((c d / d : ℝ) : ℂ) * ∑ η ∈ nontrivialRoots d, F η =
      ∑ η ∈ primitiveRoots' N, ((selbergMultiplesCoord N c (orderOf η) : ℝ) : ℂ) * F η := by
  classical
  have hrew : ∀ d ∈ Icc 1 N, ((c d / d : ℝ) : ℂ) * ∑ η ∈ nontrivialRoots d, F η =
      ∑ η ∈ primitiveRoots' N,
        (if orderOf η ∣ d then ((c d / d : ℝ) : ℂ) * F η else 0) := by
    intro d hd
    rw [nontrivialRoots_eq_filter_primitiveRoots' hd, mul_sum, sum_filter]
  rw [sum_congr rfl hrew, sum_comm]
  refine sum_congr rfl fun η _ => ?_
  unfold selbergMultiplesCoord
  rw [Complex.ofReal_sum, sum_mul, sum_filter]

/-- Disjoint decomposition of complex sums over `primitiveRoots' Q` by primitive order. -/
theorem sum_primitiveRoots'_complex_eq (Q : ℕ) (f : ℂ → ℂ) :
    ∑ ζ ∈ primitiveRoots' Q, f ζ = ∑ e ∈ Icc 2 Q, ∑ ζ ∈ primitiveRoots e ℂ, f ζ := by
  rw [primitiveRoots'_eq_biUnion, sum_biUnion fun e _ e' _ hne => IsPrimitiveRoot.disjoint hne]

/-- **The cyclotomic–Selberg bridge by primitive order `2 ≤ e ≤ N` (zero hypotheses).** -/
theorem sum_mul_sum_nontrivialRoots_eq_selberg (N : ℕ) (c : ℕ → ℝ) (F : ℂ → ℂ) :
    ∑ d ∈ Icc 1 N, ((c d / d : ℝ) : ℂ) * ∑ η ∈ nontrivialRoots d, F η =
      ∑ e ∈ Icc 2 N, ((selbergMultiplesCoord N c e : ℝ) : ℂ) * ∑ η ∈ primitiveRoots e ℂ, F η := by
  rw [sum_mul_sum_nontrivialRoots_eq_primitiveRoots', sum_primitiveRoots'_complex_eq]
  refine sum_congr rfl fun e he => ?_
  have he0 : 0 < e := by have := (mem_Icc.mp he).1; omega
  rw [mul_sum]
  refine sum_congr rfl fun η hη => ?_
  rw [((mem_primitiveRoots he0).mp hη).eq_orderOf.symm]

/-- Support truncation of `primitiveRoots' N` to `primitiveRoots' Q₀` when `c` is supported on
`[1, Q₀]`. -/
theorem sum_primitiveRoots'_selberg_eq_cutoff {N Q₀ : ℕ} (hQN : Q₀ ≤ N) {c : ℕ → ℝ}
    (hsupp : ∀ d, c d ≠ 0 → d ≤ Q₀) (F : ℂ → ℂ) :
    ∑ η ∈ primitiveRoots' N, ((selbergMultiplesCoord N c (orderOf η) : ℝ) : ℂ) * F η =
      ∑ η ∈ primitiveRoots' Q₀, ((selbergMultiplesCoord N c (orderOf η) : ℝ) : ℂ) * F η := by
  have hY0 : ∀ e, Q₀ < e → selbergMultiplesCoord N c e = 0 := fun e he =>
    sum_eq_zero fun d hd => by
      obtain ⟨hd1, hed⟩ := mem_filter.mp hd
      have : c d = 0 := by
        by_contra h
        have := hsupp d h
        have := Nat.le_of_dvd (mem_Icc.mp hd1).1 hed
        omega
      rw [this, zero_div]
  have hmono : responseRoots Q₀ ⊆ responseRoots N := fun ζ hζ => by
    obtain ⟨d, hd, h⟩ := mem_biUnion.mp hζ
    exact mem_biUnion.mpr ⟨d, mem_Icc.mpr ⟨(mem_Icc.mp hd).1, (mem_Icc.mp hd).2.trans hQN⟩, h⟩
  refine (sum_subset (erase_subset_erase 1 hmono) fun η hηN hηQ => ?_).symm
  have hord : Q₀ < orderOf η := by
    by_contra h
    apply hηQ
    have hηN' := mem_of_mem_erase hηN
    have he := orderOf_mem_Icc_of_mem_responseRoots hηN'
    exact mem_erase.mpr ⟨ne_of_mem_erase hηN, primitiveRoot_mem_responseRoots
      (mem_Icc.mpr ⟨(mem_Icc.mp he).1, not_lt.mp h⟩) (IsPrimitiveRoot.orderOf η)⟩
  rw [hY0 _ hord, Complex.ofReal_zero, zero_mul]

/-- **Exact Selberg-coordinate spectral identity for the centred quadratic potential layer
(zero hypotheses).** -/
theorem sum_mul_residuePotential_sub_gcd_eq_selberg (N j : ℕ) (c c' : ℕ → ℝ) :
    ((∑ d ∈ Icc 1 N, c d / d * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
        (residuePotential d (j * n) - (((Nat.gcd j d : ℕ) : ℝ) ^ 2 - 1) / 12) : ℝ) : ℂ) =
      ∑ η ∈ (primitiveRoots' N).filter (fun η => η ^ j ≠ 1),
        ((selbergMultiplesCoord N c (orderOf η) : ℝ) : ℂ) *
          (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * rowTransform N c' (η ^ j) := by
  classical
  rw [Complex.ofReal_sum]
  have hrew : ∀ d ∈ Icc 1 N,
      ((c d / d * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
        (residuePotential d (j * n) - (((Nat.gcd j d : ℕ) : ℝ) ^ 2 - 1) / 12) : ℝ) : ℂ) =
      ((c d / d : ℝ) : ℂ) * ∑ η ∈ nontrivialRoots d,
        (if η ^ j ≠ 1 then (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * rowTransform N c' (η ^ j) else 0) := by
    intro d hd
    rw [Complex.ofReal_mul, sum_mul_residuePotential_sub_gcd_eq_spectral (mem_Icc.mp hd).1 N j c',
      sum_filter]
  rw [sum_congr rfl hrew, sum_mul_sum_nontrivialRoots_eq_primitiveRoots', sum_filter]
  exact sum_congr rfl fun η _ => by split_ifs <;> ring

/-- **Exact Selberg-coordinate spectral identity for the cubic potential difference layer
(zero hypotheses).** -/
theorem sum_mul_cubicDiff_eq_selberg (N j : ℕ) (c c' : ℕ → ℝ) :
    ((∑ d ∈ Icc 1 N, c d / d * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 *
        (2 * cubicPotential d (j * n) - residuePotential d (j * n)) : ℝ) : ℂ) =
      ∑ η ∈ (primitiveRoots' N).filter (fun η => η ^ j ≠ 1),
        ((selbergMultiplesCoord N c (orderOf η) : ℝ) : ℂ) *
          cubicSpectralWeight η * cubicRowTransform N c' (η ^ j) := by
  classical
  rw [Complex.ofReal_sum]
  have hrew : ∀ d ∈ Icc 1 N,
      ((c d / d * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 *
        (2 * cubicPotential d (j * n) - residuePotential d (j * n)) : ℝ) : ℂ) =
      ((c d / d : ℝ) : ℂ) * ∑ η ∈ nontrivialRoots d,
        (if η ^ j ≠ 1 then cubicSpectralWeight η * cubicRowTransform N c' (η ^ j) else 0) := by
    intro d hd
    rw [Complex.ofReal_mul, sum_mul_cubicDiff_eq_spectral (mem_Icc.mp hd).1 N j c', sum_filter]
  rw [sum_congr rfl hrew, sum_mul_sum_nontrivialRoots_eq_primitiveRoots', sum_filter]
  exact sum_congr rfl fun η _ => by split_ifs <;> ring

/-- Cutoff version of `sum_mul_residuePotential_sub_gcd_eq_selberg` for `c` supported on `[1, Q₀]`. -/
theorem sum_mul_residuePotential_sub_gcd_eq_selberg_cutoff {N Q₀ : ℕ} (hQN : Q₀ ≤ N) (j : ℕ)
    {c : ℕ → ℝ} (hsupp : ∀ d, c d ≠ 0 → d ≤ Q₀) (c' : ℕ → ℝ) :
    ((∑ d ∈ Icc 1 N, c d / d * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
        (residuePotential d (j * n) - (((Nat.gcd j d : ℕ) : ℝ) ^ 2 - 1) / 12) : ℝ) : ℂ) =
      ∑ η ∈ (primitiveRoots' Q₀).filter (fun η => η ^ j ≠ 1),
        ((selbergMultiplesCoord N c (orderOf η) : ℝ) : ℂ) *
          (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * rowTransform N c' (η ^ j) := by
  classical
  rw [sum_mul_residuePotential_sub_gcd_eq_selberg, sum_filter, sum_filter]
  have h := sum_primitiveRoots'_selberg_eq_cutoff hQN hsupp
    (fun η => if η ^ j ≠ 1 then (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * rowTransform N c' (η ^ j) else 0)
  simpa only [mul_ite, mul_zero, mul_assoc] using h

/-- Cutoff version of `sum_mul_cubicDiff_eq_selberg` for `c` supported on `[1, Q₀]`. -/
theorem sum_mul_cubicDiff_eq_selberg_cutoff {N Q₀ : ℕ} (hQN : Q₀ ≤ N) (j : ℕ)
    {c : ℕ → ℝ} (hsupp : ∀ d, c d ≠ 0 → d ≤ Q₀) (c' : ℕ → ℝ) :
    ((∑ d ∈ Icc 1 N, c d / d * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 *
        (2 * cubicPotential d (j * n) - residuePotential d (j * n)) : ℝ) : ℂ) =
      ∑ η ∈ (primitiveRoots' Q₀).filter (fun η => η ^ j ≠ 1),
        ((selbergMultiplesCoord N c (orderOf η) : ℝ) : ℂ) *
          cubicSpectralWeight η * cubicRowTransform N c' (η ^ j) := by
  classical
  rw [sum_mul_cubicDiff_eq_selberg, sum_filter, sum_filter]
  have h := sum_primitiveRoots'_selberg_eq_cutoff hQN hsupp
    (fun η => if η ^ j ≠ 1 then cubicSpectralWeight η * cubicRowTransform N c' (η ^ j) else 0)
  simpa only [mul_ite, mul_zero, mul_assoc] using h

/-! ## §3. Fourth-order large-sieve dispersion in Selberg coordinates -/

/-- **Fourth-order Farey moment in Selberg coordinates (zero hypotheses).** -/
theorem sum_primitiveRoots'_selberg_inv_norm_pow_four_le (N Q₀ : ℕ) (c : ℕ → ℝ) :
    ∑ η ∈ primitiveRoots' Q₀,
        selbergMultiplesCoord N c (orderOf η) ^ 2 * ((‖η - 1‖ ^ 2)⁻¹) ^ 2 ≤
      1 / 64 * ∑ e ∈ Icc 2 Q₀, selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 4 := by
  rw [sum_primitiveRoots'_eq, mul_sum]
  refine sum_le_sum fun e he => ?_
  have he2 : 2 ≤ e := (mem_Icc.mp he).1
  have he0 : 0 < e := by omega
  have hrew : ∀ η ∈ primitiveRoots e ℂ,
      selbergMultiplesCoord N c (orderOf η) ^ 2 * ((‖η - 1‖ ^ 2)⁻¹) ^ 2 =
        selbergMultiplesCoord N c e ^ 2 * (1 / ‖η - 1‖ ^ (2 + 2)) := by
    intro η hη
    have hprim := (mem_primitiveRoots he0).mp hη
    rw [← hprim.eq_orderOf]
    ring
  rw [sum_congr rfl hrew, ← mul_sum]
  calc selbergMultiplesCoord N c e ^ 2 * ∑ η ∈ primitiveRoots e ℂ, 1 / ‖η - 1‖ ^ (2 + 2)
      ≤ selbergMultiplesCoord N c e ^ 2 * (((e : ℝ) / 4) ^ 2 * ((e : ℝ) ^ 2 / 4)) :=
        mul_le_mul_of_nonneg_left (sum_primitiveRoots_inv_norm_sub_one_pow_le he2 2) (sq_nonneg _)
    _ = 1 / 64 * (selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 4) := by ring

/-- **Sixth-order Farey moment in Selberg coordinates (zero hypotheses).** -/
theorem sum_primitiveRoots'_selberg_norm_cubicSpectralWeight_sq_le (N Q₀ : ℕ) (c : ℕ → ℝ) :
    ∑ η ∈ primitiveRoots' Q₀,
        selbergMultiplesCoord N c (orderOf η) ^ 2 * ‖cubicSpectralWeight η‖ ^ 2 ≤
      1 / 256 * ∑ e ∈ Icc 2 Q₀, selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 6 := by
  rw [sum_primitiveRoots'_eq, mul_sum]
  refine sum_le_sum fun e he => ?_
  have he2 : 2 ≤ e := (mem_Icc.mp he).1
  have he0 : 0 < e := by omega
  have hterm : ∀ η ∈ primitiveRoots e ℂ,
      selbergMultiplesCoord N c (orderOf η) ^ 2 * ‖cubicSpectralWeight η‖ ^ 2 ≤
        4 * selbergMultiplesCoord N c e ^ 2 * (1 / ‖η - 1‖ ^ (4 + 2)) := by
    intro η hη
    have hprim := (mem_primitiveRoots he0).mp hη
    have hw := norm_cubicSpectralWeight_le (hprim.norm'_eq_one he0.ne')
    have hw2 : ‖cubicSpectralWeight η‖ ^ 2 ≤ (2 / ‖η - 1‖ ^ 3) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hw 2
    rw [← hprim.eq_orderOf]
    calc selbergMultiplesCoord N c e ^ 2 * ‖cubicSpectralWeight η‖ ^ 2
        ≤ selbergMultiplesCoord N c e ^ 2 * (2 / ‖η - 1‖ ^ 3) ^ 2 :=
          mul_le_mul_of_nonneg_left hw2 (sq_nonneg _)
      _ = 4 * selbergMultiplesCoord N c e ^ 2 * (1 / ‖η - 1‖ ^ (4 + 2)) := by ring
  calc ∑ η ∈ primitiveRoots e ℂ,
        selbergMultiplesCoord N c (orderOf η) ^ 2 * ‖cubicSpectralWeight η‖ ^ 2
      ≤ ∑ η ∈ primitiveRoots e ℂ,
          4 * selbergMultiplesCoord N c e ^ 2 * (1 / ‖η - 1‖ ^ (4 + 2)) := sum_le_sum hterm
    _ = 4 * selbergMultiplesCoord N c e ^ 2 *
          ∑ η ∈ primitiveRoots e ℂ, 1 / ‖η - 1‖ ^ (4 + 2) := by rw [← mul_sum]
    _ ≤ 4 * selbergMultiplesCoord N c e ^ 2 * (((e : ℝ) / 4) ^ 4 * ((e : ℝ) ^ 2 / 4)) :=
        mul_le_mul_of_nonneg_left (sum_primitiveRoots_inv_norm_sub_one_pow_le he2 4) (by positivity)
    _ = 1 / 256 * (selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 6) := by ring

/-- **Selberg-coordinate large-sieve bound for the centred quadratic Bernoulli kernel.** -/
theorem abs_sum_mul_bernoulliKernel_sub_kernelMean_le_selberg {N Q₀ A L : ℕ}
    (hQ₀ : 2 ≤ Q₀) (hQN : Q₀ ≤ N) {c c' : ℕ → ℝ} (hsupp : ∀ d, c d ≠ 0 → d ≤ Q₀)
    (hsupp' : ∀ n, c' n ≠ 0 → n ∈ Icc (A + 1) (A + L)) (hAL : A + L ≤ N) :
    |∑ d ∈ Icc 1 N, c d / d *
        ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * (bernoulliKernel d n - kernelMean d)| ≤
      1 / 2 * Real.sqrt (∑ e ∈ Icc 2 Q₀, selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 4) *
        Real.sqrt ((L : ℝ) + (Q₀ : ℝ) ^ 2 - 1) *
        Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 4) := by
  classical
  set W := Icc (A + 1) (A + L)
  have hWN : W ⊆ Icc 1 N := Icc_subset_Icc (by omega) hAL
  set X : ℝ := (L : ℝ) + (Q₀ : ℝ) ^ 2 - 1
  set Y₂ : ℝ := ∑ n ∈ W, c' n ^ 2 / (n : ℝ) ^ 4
  set P₂ : ℝ := ∑ e ∈ Icc 2 Q₀, selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 4
  have hX : 0 ≤ X := by
    have : (2 : ℝ) ≤ Q₀ := by exact_mod_cast hQ₀
    simp only [X]; nlinarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hY₂ : 0 ≤ Y₂ := sum_nonneg fun n _ => by positivity
  have hP₂ : 0 ≤ P₂ := sum_nonneg fun e _ => by positivity
  have hrowW : ∀ ζ : ℂ, rowTransform N c' ζ =
      ∑ n ∈ W, ((c' n / (n : ℝ) ^ 2 : ℝ) : ℂ) * ζ ^ n := by
    intro ζ
    unfold rowTransform
    rw [← sum_subset hWN fun n _ hn => by
      have : c' n = 0 := by by_contra h; exact hn (hsupp' n h)
      simp [this]]
  have hlayer : ∀ m : ℕ, 0 < m →
      |∑ d ∈ Icc 1 N, c d / d * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
          (residuePotential d (m * n) - (((Nat.gcd m d : ℕ) : ℝ) ^ 2 - 1) / 12)| ≤
        1 / 8 * Real.sqrt P₂ * Real.sqrt X * Real.sqrt Y₂ * Real.sqrt m := by
    intro m hm
    set Tm := (primitiveRoots' Q₀).filter (fun η => η ^ m ≠ 1)
    have hTm_sub : Tm ⊆ primitiveRoots' Q₀ := filter_subset _ _
    have hTm_resp : Tm ⊆ responseRoots Q₀ := hTm_sub.trans (erase_subset _ _)
    rw [← Real.norm_eq_abs, ← Complex.norm_real,
      sum_mul_residuePotential_sub_gcd_eq_selberg_cutoff hQN m hsupp c']
    have hcs : ‖∑ η ∈ Tm, ((selbergMultiplesCoord N c (orderOf η) : ℝ) : ℂ) *
          (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * rowTransform N c' (η ^ m)‖ ≤
        Real.sqrt (∑ η ∈ Tm, (selbergMultiplesCoord N c (orderOf η) ^ 2 * ((‖η - 1‖ ^ 2)⁻¹) ^ 2)) *
          Real.sqrt (∑ η ∈ Tm, ‖rowTransform N c' (η ^ m)‖ ^ 2) := by
      refine (norm_sum_le _ _).trans ?_
      have hnorm : ∀ η ∈ Tm,
          ‖((selbergMultiplesCoord N c (orderOf η) : ℝ) : ℂ) *
              (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * rowTransform N c' (η ^ m)‖ =
            (|selbergMultiplesCoord N c (orderOf η)| * (‖η - 1‖ ^ 2)⁻¹) *
              ‖rowTransform N c' (η ^ m)‖ := by
        intro η _
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
      rw [sum_congr rfl hnorm]
      refine (Real.sum_mul_le_sqrt_mul_sqrt Tm _ _).trans ?_
      gcongr with η
      rw [mul_pow, sq_abs]
    have hK₂ : ∑ η ∈ Tm, (selbergMultiplesCoord N c (orderOf η) ^ 2 * ((‖η - 1‖ ^ 2)⁻¹) ^ 2) ≤
        1 / 64 * P₂ :=
      (sum_le_sum_of_subset_of_nonneg hTm_sub fun _ _ _ => by positivity).trans
        (sum_primitiveRoots'_selberg_inv_norm_pow_four_le N Q₀ c)
    have hK₂_sqrt : Real.sqrt (∑ η ∈ Tm,
        (selbergMultiplesCoord N c (orderOf η) ^ 2 * ((‖η - 1‖ ^ 2)⁻¹) ^ 2)) ≤
        1 / 8 * Real.sqrt P₂ := by
      calc Real.sqrt _ ≤ Real.sqrt (1 / 64 * P₂) := Real.sqrt_le_sqrt hK₂
        _ = 1 / 8 * Real.sqrt P₂ := by
          rw [Real.sqrt_mul (by norm_num), show (1 : ℝ) / 64 = (1 / 8) ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
    have hls : ∑ η ∈ Tm, ‖rowTransform N c' (η ^ m)‖ ^ 2 ≤ m * (X * Y₂) := by
      simp_rw [hrowW]
      have h := sum_norm_sq_dilated_sharp_le hQ₀ hTm_resp hm A L
        (fun n => ((c' n / (n : ℝ) ^ 2 : ℝ) : ℂ))
      have hy : ∑ k ∈ W, ‖((c' k / (k : ℝ) ^ 2 : ℝ) : ℂ)‖ ^ 2 = Y₂ := by
        refine sum_congr rfl fun k _ => ?_
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, ← pow_mul]
      rwa [hy] at h
    have hls_sqrt : Real.sqrt (∑ η ∈ Tm, ‖rowTransform N c' (η ^ m)‖ ^ 2) ≤
        Real.sqrt m * (Real.sqrt X * Real.sqrt Y₂) := by
      calc Real.sqrt _ ≤ Real.sqrt (m * (X * Y₂)) := Real.sqrt_le_sqrt hls
        _ = Real.sqrt m * (Real.sqrt X * Real.sqrt Y₂) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_mul hX]
    calc ‖∑ η ∈ Tm, ((selbergMultiplesCoord N c (orderOf η) : ℝ) : ℂ) *
          (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * rowTransform N c' (η ^ m)‖
        ≤ (1 / 8 * Real.sqrt P₂) * (Real.sqrt m * (Real.sqrt X * Real.sqrt Y₂)) :=
          hcs.trans (mul_le_mul hK₂_sqrt hls_sqrt (Real.sqrt_nonneg _) (by positivity))
      _ = 1 / 8 * Real.sqrt P₂ * Real.sqrt X * Real.sqrt Y₂ * Real.sqrt m := by ring
  set t : ℕ → ℝ := fun j => ∑ d ∈ Icc 1 N, c d / d *
    ((∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
      (residuePotential d ((j + 1) * n) - (((Nat.gcd (j + 1) d : ℕ) : ℝ) ^ 2 - 1) / 12)) *
      (1 / ((j : ℝ) + 1) ^ 2))
  have ht : HasSum t (∑ d ∈ Icc 1 N, c d / d *
      ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * (bernoulliKernel d n - kernelMean d)) :=
    hasSum_sum fun d hd =>
      (hasSum_sum_mul_bernoulliKernel_sub_kernelMean (mem_Icc.mp hd).1 N c').mul_left (c d / d)
  have hbound : ∀ K : ℕ, |∑ j ∈ range K, t j| ≤
      1 / 2 * Real.sqrt P₂ * Real.sqrt X * Real.sqrt Y₂ := by
    intro K
    have hpt : ∀ j ∈ range K, |t j| ≤
        (1 / 8 * Real.sqrt P₂ * Real.sqrt X * Real.sqrt Y₂) *
          (Real.sqrt ((j + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2) := by
      intro j _
      have hrw : t j = (∑ d ∈ Icc 1 N, c d / d * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
          (residuePotential d ((j + 1) * n) - (((Nat.gcd (j + 1) d : ℕ) : ℝ) ^ 2 - 1) / 12)) /
          ((j + 1 : ℕ) : ℝ) ^ 2 := by
        simp only [t, sum_div]
        refine sum_congr rfl fun d _ => ?_
        push_cast
        ring
      rw [hrw, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) ^ 2)]
      have hl := hlayer (j + 1) (Nat.succ_pos j)
      calc |∑ d ∈ Icc 1 N, c d / d * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
            (residuePotential d ((j + 1) * n) - (((Nat.gcd (j + 1) d : ℕ) : ℝ) ^ 2 - 1) / 12)| /
            ((j + 1 : ℕ) : ℝ) ^ 2
          ≤ (1 / 8 * Real.sqrt P₂ * Real.sqrt X * Real.sqrt Y₂ * Real.sqrt ((j + 1 : ℕ) : ℝ)) /
              ((j + 1 : ℕ) : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right hl (by positivity)
        _ = (1 / 8 * Real.sqrt P₂ * Real.sqrt X * Real.sqrt Y₂) *
              (Real.sqrt ((j + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2) := by ring
    have hsum_j : ∑ j ∈ range K, Real.sqrt ((j + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2 ≤ 4 := by
      have hre : ∑ j ∈ range K, Real.sqrt ((j + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2 =
          ∑ m ∈ Icc 1 K, Real.sqrt (m : ℝ) / (m : ℝ) ^ 2 := by
        clear hpt
        induction K with
        | zero => simp
        | succ K ih => rw [Finset.sum_range_succ, ih, sum_Icc_succ_top (by omega)]
      rw [hre]
      exact sum_Icc_sqrt_div_sq_le K
    calc |∑ j ∈ range K, t j| ≤ ∑ j ∈ range K, |t j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range K, (1 / 8 * Real.sqrt P₂ * Real.sqrt X * Real.sqrt Y₂) *
            (Real.sqrt ((j + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2) := sum_le_sum hpt
      _ = (1 / 8 * Real.sqrt P₂ * Real.sqrt X * Real.sqrt Y₂) *
            ∑ j ∈ range K, Real.sqrt ((j + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2 := by rw [← mul_sum]
      _ ≤ (1 / 8 * Real.sqrt P₂ * Real.sqrt X * Real.sqrt Y₂) * 4 :=
          mul_le_mul_of_nonneg_left hsum_j (by positivity)
      _ = 1 / 2 * Real.sqrt P₂ * Real.sqrt X * Real.sqrt Y₂ := by ring
  exact le_of_tendsto' ht.tendsto_sum_nat.abs hbound

/-- **Selberg-coordinate large-sieve bound for the cubic Bernoulli kernel.** -/
theorem abs_sum_mul_cubicKernel_le_selberg {N Q₀ A L : ℕ}
    (hQ₀ : 2 ≤ Q₀) (hQN : Q₀ ≤ N) {c c' : ℕ → ℝ} (hsupp : ∀ d, c d ≠ 0 → d ≤ Q₀)
    (hsupp' : ∀ n, c' n ≠ 0 → n ∈ Icc (A + 1) (A + L)) (hAL : A + L ≤ N) :
    |∑ d ∈ Icc 1 N, c d / d * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 * cubicKernel d n| ≤
      1 / 8 * Real.sqrt (∑ e ∈ Icc 2 Q₀, selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 6) *
        Real.sqrt ((L : ℝ) + (Q₀ : ℝ) ^ 2 - 1) *
        Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 6) := by
  classical
  set W := Icc (A + 1) (A + L)
  have hWN : W ⊆ Icc 1 N := Icc_subset_Icc (by omega) hAL
  set X : ℝ := (L : ℝ) + (Q₀ : ℝ) ^ 2 - 1
  set Y₃ : ℝ := ∑ n ∈ W, c' n ^ 2 / (n : ℝ) ^ 6
  set P₃ : ℝ := ∑ e ∈ Icc 2 Q₀, selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 6
  have hX : 0 ≤ X := by
    have : (2 : ℝ) ≤ Q₀ := by exact_mod_cast hQ₀
    simp only [X]; nlinarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hY₃ : 0 ≤ Y₃ := sum_nonneg fun n _ => by positivity
  have hP₃ : 0 ≤ P₃ := sum_nonneg fun e _ => by positivity
  have hrowW : ∀ ζ : ℂ, cubicRowTransform N c' ζ =
      ∑ n ∈ W, ((c' n / (n : ℝ) ^ 3 : ℝ) : ℂ) * ζ ^ n := by
    intro ζ
    unfold cubicRowTransform
    rw [← sum_subset hWN fun n _ hn => by
      have : c' n = 0 := by by_contra h; exact hn (hsupp' n h)
      simp [this]]
  have hlayer : ∀ m : ℕ, 0 < m →
      |∑ d ∈ Icc 1 N, c d / d * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 *
          (2 * cubicPotential d (m * n) - residuePotential d (m * n))| ≤
        1 / 16 * Real.sqrt P₃ * Real.sqrt X * Real.sqrt Y₃ * Real.sqrt m := by
    intro m hm
    set Tm := (primitiveRoots' Q₀).filter (fun η => η ^ m ≠ 1)
    have hTm_sub : Tm ⊆ primitiveRoots' Q₀ := filter_subset _ _
    have hTm_resp : Tm ⊆ responseRoots Q₀ := hTm_sub.trans (erase_subset _ _)
    rw [← Real.norm_eq_abs, ← Complex.norm_real,
      sum_mul_cubicDiff_eq_selberg_cutoff hQN m hsupp c']
    have hcs : ‖∑ η ∈ Tm, ((selbergMultiplesCoord N c (orderOf η) : ℝ) : ℂ) *
          cubicSpectralWeight η * cubicRowTransform N c' (η ^ m)‖ ≤
        Real.sqrt (∑ η ∈ Tm, (selbergMultiplesCoord N c (orderOf η) ^ 2 * ‖cubicSpectralWeight η‖ ^ 2)) *
          Real.sqrt (∑ η ∈ Tm, ‖cubicRowTransform N c' (η ^ m)‖ ^ 2) := by
      refine (norm_sum_le _ _).trans ?_
      have hnorm : ∀ η ∈ Tm,
          ‖((selbergMultiplesCoord N c (orderOf η) : ℝ) : ℂ) *
              cubicSpectralWeight η * cubicRowTransform N c' (η ^ m)‖ =
            (|selbergMultiplesCoord N c (orderOf η)| * ‖cubicSpectralWeight η‖) *
              ‖cubicRowTransform N c' (η ^ m)‖ := by
        intro η _
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [sum_congr rfl hnorm]
      refine (Real.sum_mul_le_sqrt_mul_sqrt Tm _ _).trans ?_
      gcongr with η
      rw [mul_pow, sq_abs]
    have hK₃ : ∑ η ∈ Tm, (selbergMultiplesCoord N c (orderOf η) ^ 2 * ‖cubicSpectralWeight η‖ ^ 2) ≤
        1 / 256 * P₃ :=
      (sum_le_sum_of_subset_of_nonneg hTm_sub fun _ _ _ => by positivity).trans
        (sum_primitiveRoots'_selberg_norm_cubicSpectralWeight_sq_le N Q₀ c)
    have hK₃_sqrt : Real.sqrt (∑ η ∈ Tm,
        (selbergMultiplesCoord N c (orderOf η) ^ 2 * ‖cubicSpectralWeight η‖ ^ 2)) ≤
        1 / 16 * Real.sqrt P₃ := by
      calc Real.sqrt _ ≤ Real.sqrt (1 / 256 * P₃) := Real.sqrt_le_sqrt hK₃
        _ = 1 / 16 * Real.sqrt P₃ := by
          rw [Real.sqrt_mul (by norm_num), show (1 : ℝ) / 256 = (1 / 16) ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
    have hls : ∑ η ∈ Tm, ‖cubicRowTransform N c' (η ^ m)‖ ^ 2 ≤ m * (X * Y₃) := by
      simp_rw [hrowW]
      have h := sum_norm_sq_dilated_sharp_le hQ₀ hTm_resp hm A L
        (fun n => ((c' n / (n : ℝ) ^ 3 : ℝ) : ℂ))
      have hy : ∑ k ∈ W, ‖((c' k / (k : ℝ) ^ 3 : ℝ) : ℂ)‖ ^ 2 = Y₃ := by
        refine sum_congr rfl fun k _ => ?_
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, ← pow_mul]
      rwa [hy] at h
    have hls_sqrt : Real.sqrt (∑ η ∈ Tm, ‖cubicRowTransform N c' (η ^ m)‖ ^ 2) ≤
        Real.sqrt m * (Real.sqrt X * Real.sqrt Y₃) := by
      calc Real.sqrt _ ≤ Real.sqrt (m * (X * Y₃)) := Real.sqrt_le_sqrt hls
        _ = Real.sqrt m * (Real.sqrt X * Real.sqrt Y₃) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_mul hX]
    calc ‖∑ η ∈ Tm, ((selbergMultiplesCoord N c (orderOf η) : ℝ) : ℂ) *
          cubicSpectralWeight η * cubicRowTransform N c' (η ^ m)‖
        ≤ (1 / 16 * Real.sqrt P₃) * (Real.sqrt m * (Real.sqrt X * Real.sqrt Y₃)) :=
          hcs.trans (mul_le_mul hK₃_sqrt hls_sqrt (Real.sqrt_nonneg _) (by positivity))
      _ = 1 / 16 * Real.sqrt P₃ * Real.sqrt X * Real.sqrt Y₃ * Real.sqrt m := by ring
  set t : ℕ → ℝ := fun j => ∑ d ∈ Icc 1 N, c d / d *
    ((∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 *
      (2 * cubicPotential d ((j + 1) * n) - residuePotential d ((j + 1) * n))) *
      (1 / ((j : ℝ) + 1) ^ 3))
  have ht : HasSum t (∑ d ∈ Icc 1 N, c d / d *
      ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 * cubicKernel d n) :=
    hasSum_sum fun d hd =>
      (hasSum_sum_mul_cubicKernel (mem_Icc.mp hd).1 N c').mul_left (c d / d)
  have hbound : ∀ K : ℕ, |∑ j ∈ range K, t j| ≤
      1 / 8 * Real.sqrt P₃ * Real.sqrt X * Real.sqrt Y₃ := by
    intro K
    have hpt : ∀ j ∈ range K, |t j| ≤
        (1 / 16 * Real.sqrt P₃ * Real.sqrt X * Real.sqrt Y₃) *
          (Real.sqrt ((j + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 3) := by
      intro j _
      have hrw : t j = (∑ d ∈ Icc 1 N, c d / d * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 *
          (2 * cubicPotential d ((j + 1) * n) - residuePotential d ((j + 1) * n))) /
          ((j + 1 : ℕ) : ℝ) ^ 3 := by
        simp only [t, sum_div]
        refine sum_congr rfl fun d _ => ?_
        push_cast
        ring
      rw [hrw, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) ^ 3)]
      have hl := hlayer (j + 1) (Nat.succ_pos j)
      calc |∑ d ∈ Icc 1 N, c d / d * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 *
            (2 * cubicPotential d ((j + 1) * n) - residuePotential d ((j + 1) * n))| /
            ((j + 1 : ℕ) : ℝ) ^ 3
          ≤ (1 / 16 * Real.sqrt P₃ * Real.sqrt X * Real.sqrt Y₃ * Real.sqrt ((j + 1 : ℕ) : ℝ)) /
              ((j + 1 : ℕ) : ℝ) ^ 3 :=
            div_le_div_of_nonneg_right hl (by positivity)
        _ = (1 / 16 * Real.sqrt P₃ * Real.sqrt X * Real.sqrt Y₃) *
              (Real.sqrt ((j + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 3) := by ring
    have hsum_j : ∑ j ∈ range K, Real.sqrt ((j + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 3 ≤ 2 := by
      have hre : ∑ j ∈ range K, Real.sqrt ((j + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 3 =
          ∑ m ∈ Icc 1 K, Real.sqrt (m : ℝ) / (m : ℝ) ^ 3 := by
        clear hpt
        induction K with
        | zero => simp
        | succ K ih => rw [Finset.sum_range_succ, ih, sum_Icc_succ_top (by omega)]
      rw [hre]
      exact sum_Icc_sqrt_div_cube_le K
    calc |∑ j ∈ range K, t j| ≤ ∑ j ∈ range K, |t j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range K, (1 / 16 * Real.sqrt P₃ * Real.sqrt X * Real.sqrt Y₃) *
            (Real.sqrt ((j + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 3) := sum_le_sum hpt
      _ = (1 / 16 * Real.sqrt P₃ * Real.sqrt X * Real.sqrt Y₃) *
            ∑ j ∈ range K, Real.sqrt ((j + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 3 := by rw [← mul_sum]
      _ ≤ (1 / 16 * Real.sqrt P₃ * Real.sqrt X * Real.sqrt Y₃) * 2 :=
          mul_le_mul_of_nonneg_left hsum_j (by positivity)
      _ = 1 / 8 * Real.sqrt P₃ * Real.sqrt X * Real.sqrt Y₃ := by ring
  exact le_of_tendsto' ht.tendsto_sum_nat.abs hbound

/-- **Selberg-coordinate large-sieve bound for the combined kernel statistics at all moduli.** -/
theorem abs_sum_mul_kernelStatisticAll_le_selberg {N Q₀ A L : ℕ}
    (hQ₀ : 2 ≤ Q₀) (hQN : Q₀ ≤ N) {c c' : ℕ → ℝ} (hsupp : ∀ d, c d ≠ 0 → d ≤ Q₀)
    (hsupp' : ∀ n, c' n ≠ 0 → n ∈ Icc (A + 1) (A + L)) (hAL : A + L ≤ N) :
    |∑ d ∈ Icc 1 N, c d / d * kernelStatisticAll N c' d| ≤
      1 / 2 * Real.sqrt (∑ e ∈ Icc 2 Q₀, selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 4) *
          Real.sqrt ((L : ℝ) + (Q₀ : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 4) +
        1 / 8 * Real.sqrt (∑ e ∈ Icc 2 Q₀, selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 6) *
          Real.sqrt ((L : ℝ) + (Q₀ : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 6) := by
  have hsplit : ∑ d ∈ Icc 1 N, c d / d * kernelStatisticAll N c' d =
      (∑ d ∈ Icc 1 N, c d / d *
        ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * (bernoulliKernel d n - kernelMean d)) +
      (∑ d ∈ Icc 1 N, c d / d *
        ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 * cubicKernel d n) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun d _ => ?_
    unfold kernelStatisticAll
    rw [sum_add_distrib, mul_add]
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_sum_mul_bernoulliKernel_sub_kernelMean_le_selberg hQ₀ hQN hsupp hsupp' hAL)
    (abs_sum_mul_cubicKernel_le_selberg hQ₀ hQN hsupp hsupp' hAL))

/-- **Fourth-order large-sieve dispersion in Selberg coordinates with the Montgomery–Vaughan
constant.** Upgrades `abs_rowBilinear_add_mean_add_beta_le_selberg` from third order and
`L + 2Q₀² - 1` to fourth order and `L + Q₀² - 1`. -/
theorem abs_rowBilinear_sub_kernelMeanMain_le_selberg_fourthOrder {N Q₀ A L : ℕ}
    (hQ₀ : 2 ≤ Q₀) (hQN : Q₀ ≤ N) {c c' : ℕ → ℝ} (hsupp : ∀ d, c d ≠ 0 → d ≤ Q₀)
    (hsupp' : ∀ n, c' n ≠ 0 → n ∈ Icc (A + 1) (A + L)) (hAL : A + L ≤ N) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' - kernelMeanMain N c c'| ≤
      1 / 2 * Real.sqrt (∑ e ∈ Icc 2 Q₀, selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 4) *
          Real.sqrt ((L : ℝ) + (Q₀ : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 4) +
        1 / 8 * Real.sqrt (∑ e ∈ Icc 2 Q₀, selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 6) *
          Real.sqrt ((L : ℝ) + (Q₀ : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 6) +
        6 * (∑ d ∈ Icc 1 Q₀, |c d| * (d : ℝ) ^ 3) *
          ∑ n ∈ Icc (A + 1) (A + L), |c' n| / (n : ℝ) ^ 4 := by
  have hlaw := abs_rowBilinear_sub_kernelStatisticAll_le N c c'
  have hls := abs_sum_mul_kernelStatisticAll_le_selberg hQ₀ hQN hsupp hsupp' hAL
  have hQsub : Icc 1 Q₀ ⊆ Icc 1 N := Icc_subset_Icc le_rfl hQN
  have hWsub : Icc (A + 1) (A + L) ⊆ Icc 1 N := Icc_subset_Icc (by omega) hAL
  have hcd : ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3 = ∑ d ∈ Icc 1 Q₀, |c d| * (d : ℝ) ^ 3 := by
    rw [← sum_subset hQsub fun d hd hdQ => by
      have : c d = 0 := by
        by_contra h
        exact hdQ (mem_Icc.mpr ⟨(mem_Icc.mp hd).1, hsupp d h⟩)
      simp [this]]
  have hcn : ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 =
      ∑ n ∈ Icc (A + 1) (A + L), |c' n| / (n : ℝ) ^ 4 := by
    rw [← sum_subset hWsub fun n _ hnW => by
      have : c' n = 0 := by by_contra h; exact hnW (hsupp' n h)
      simp [this]]
  rw [hcd, hcn] at hlaw
  have key := abs_sub_abs_le_abs_sub
    (rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
      rowBeta N c * finiteHarmonicSum N c' - kernelMeanMain N c c')
    (∑ d ∈ Icc 1 N, c d / d * kernelStatisticAll N c' d)
  linarith

/-- At modulus `d = 1`, `cubicKernel 1 n = 0`. -/
theorem cubicKernel_one (n : ℕ) : cubicKernel 1 n = 0 := by
  simp [cubicKernel, cubicPotential, residuePotential, Nat.mod_one]

/-- At modulus `d = 1`, `kernelStatisticAll N c' 1 = 0`. -/
theorem kernelStatisticAll_one (N : ℕ) (c' : ℕ → ℝ) : kernelStatisticAll N c' 1 = 0 := by
  unfold kernelStatisticAll
  have hm1 : kernelMean 1 = 0 := by simp [kernelMean, bernoulliKernel_one]
  simp [bernoulliKernel_one, cubicKernel_one, hm1]

/-- **Unconditional all-inputs fourth-order Selberg-coordinate large-sieve law (zero hypotheses).** -/
theorem abs_rowBilinear_sub_kernelMeanMain_le_selberg_all (N : ℕ) (c c' : ℕ → ℝ) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' - kernelMeanMain N c c'| ≤
      1 / 2 * Real.sqrt (∑ e ∈ Icc 2 N, selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 4) *
          Real.sqrt ((N : ℝ) + (N : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc 1 N, c' n ^ 2 / (n : ℝ) ^ 4) +
        1 / 8 * Real.sqrt (∑ e ∈ Icc 2 N, selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 6) *
          Real.sqrt ((N : ℝ) + (N : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc 1 N, c' n ^ 2 / (n : ℝ) ^ 6) +
        6 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3) *
          ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 := by
  classical
  have hlaw := abs_rowBilinear_sub_kernelStatisticAll_le N c c'
  rcases Nat.lt_or_ge N 2 with hN2 | hN2
  · have hI2 : Icc 2 N = ∅ := Icc_eq_empty (by omega)
    have hK0 : ∑ d ∈ Icc 1 N, c d / d * kernelStatisticAll N c' d = 0 := by
      refine sum_eq_zero fun d hd => ?_
      have hd1 : d = 1 := by have := mem_Icc.mp hd; omega
      subst hd1
      rw [kernelStatisticAll_one, mul_zero]
    simp only [hI2, sum_empty, Real.sqrt_zero, mul_zero, zero_mul, zero_add]
    rw [hK0, sub_zero] at hlaw
    exact hlaw
  · set c₀ : ℕ → ℝ := fun d => if d ∈ Icc 1 N then c d else 0
    set c'₀ : ℕ → ℝ := fun n => if n ∈ Icc 1 N then c' n else 0
    have hsupp : ∀ d, c₀ d ≠ 0 → d ≤ N := fun d h => by
      by_contra hd; exact h (if_neg fun hmem => hd (mem_Icc.mp hmem).2)
    have hsupp' : ∀ n, c'₀ n ≠ 0 → n ∈ Icc (0 + 1) (0 + N) := fun n h => by
      rw [zero_add, zero_add]
      by_contra hn; exact h (if_neg hn)
    have hsel : ∀ e, selbergMultiplesCoord N c₀ e = selbergMultiplesCoord N c e := fun e => by
      unfold selbergMultiplesCoord
      exact sum_congr rfl fun d hd => by simp only [c₀, if_pos (mem_filter.mp hd).1]
    have hstat : ∀ d, kernelStatisticAll N c'₀ d = kernelStatisticAll N c' d := fun d => by
      unfold kernelStatisticAll
      exact sum_congr rfl fun n hn => by simp only [c'₀, if_pos hn]
    have hK : ∑ d ∈ Icc 1 N, c₀ d / d * kernelStatisticAll N c'₀ d =
        ∑ d ∈ Icc 1 N, c d / d * kernelStatisticAll N c' d :=
      sum_congr rfl fun d hd => by simp only [c₀, if_pos hd, hstat]
    have hls := abs_sum_mul_kernelStatisticAll_le_selberg hN2 le_rfl hsupp hsupp'
      (by omega : 0 + N ≤ N)
    simp only [zero_add, hK, hsel] at hls
    have hY4 : ∑ n ∈ Icc 1 N, c'₀ n ^ 2 / (n : ℝ) ^ 4 = ∑ n ∈ Icc 1 N, c' n ^ 2 / (n : ℝ) ^ 4 :=
      sum_congr rfl fun n hn => by simp only [c'₀, if_pos hn]
    have hY6 : ∑ n ∈ Icc 1 N, c'₀ n ^ 2 / (n : ℝ) ^ 6 = ∑ n ∈ Icc 1 N, c' n ^ 2 / (n : ℝ) ^ 6 :=
      sum_congr rfl fun n hn => by simp only [c'₀, if_pos hn]
    rw [hY4, hY6] at hls
    have key := abs_sub_abs_le_abs_sub
      (rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' - kernelMeanMain N c c')
      (∑ d ∈ Icc 1 N, c d / d * kernelStatisticAll N c' d)
    linarith

/-! ## §4. The all-moduli dual-norm large sieve and fourth-order dispersion for bounded rows -/

/-- For a row bounded by `1` on `[1, Q₀]`, `Σ_{2 ≤ e ≤ Q₀} Y_c(e)² e⁶ ≤ 2 Q₀⁴ (Q₀ + 1)`. -/
theorem sum_selberg_sq_mul_pow_six_le {N Q₀ : ℕ} {c : ℕ → ℝ} (hc : ∀ d, |c d| ≤ 1)
    (hsupp : ∀ d, c d ≠ 0 → d ≤ Q₀) :
    ∑ e ∈ Icc 2 Q₀, selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 6 ≤
      2 * (Q₀ : ℝ) ^ 4 * ((Q₀ : ℝ) + 1) := by
  have hterm : ∀ e ∈ Icc 2 Q₀,
      selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 6 ≤ 4 * (Q₀ : ℝ) ^ 3 * (e : ℝ) := by
    intro e he
    have he' := mem_Icc.mp he
    have heQ : (e : ℝ) ≤ Q₀ := by exact_mod_cast he'.2
    have hY := abs_selbergMultiplesCoord_le (N := N) (e := e) (by omega) hc hsupp
    have hm : ((Q₀ / e : ℕ) : ℝ) * e ≤ Q₀ := by exact_mod_cast Nat.div_mul_le_self Q₀ e
    have hsq : selbergMultiplesCoord N c e ^ 2 ≤ 4 * ((Q₀ / e : ℕ) : ℝ) / (e : ℝ) ^ 2 := by
      have h0 : 0 ≤ |selbergMultiplesCoord N c e| := abs_nonneg _
      have := pow_le_pow_left₀ h0 hY 2
      rw [sq_abs, div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at this
      linarith
    have he0 : (0 : ℝ) < e := by exact_mod_cast (by omega : 0 < e)
    have he2Q : (e : ℝ) ^ 2 ≤ (Q₀ : ℝ) ^ 2 := pow_le_pow_left₀ he0.le heQ 2
    calc selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 6
        ≤ 4 * ((Q₀ / e : ℕ) : ℝ) / (e : ℝ) ^ 2 * (e : ℝ) ^ 6 :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = 4 * (((Q₀ / e : ℕ) : ℝ) * e) * (e : ℝ) ^ 2 * (e : ℝ) := by field_simp
      _ ≤ 4 * (Q₀ : ℝ) * (Q₀ : ℝ) ^ 2 * (e : ℝ) := by gcongr
      _ = 4 * (Q₀ : ℝ) ^ 3 * (e : ℝ) := by ring
  calc ∑ e ∈ Icc 2 Q₀, selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 6
      ≤ ∑ e ∈ Icc 2 Q₀, 4 * (Q₀ : ℝ) ^ 3 * (e : ℝ) := sum_le_sum hterm
    _ ≤ ∑ e ∈ Icc 1 Q₀, 4 * (Q₀ : ℝ) ^ 3 * (e : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc (by norm_num) le_rfl)
          fun _ _ _ => by positivity
    _ = 2 * (Q₀ : ℝ) ^ 4 * ((Q₀ : ℝ) + 1) := by rw [← mul_sum, sum_Icc_cast_eq]; ring

/-- **Bounded-row large-sieve estimate for the combined kernel statistics at all moduli.** -/
theorem abs_sum_mul_kernelStatisticAll_le_bounded {N Q₀ A L : ℕ}
    (hQ₀ : 2 ≤ Q₀) (hQN : Q₀ ≤ N) {c c' : ℕ → ℝ} (hc : ∀ d, |c d| ≤ 1)
    (hsupp : ∀ d, c d ≠ 0 → d ≤ Q₀)
    (hsupp' : ∀ n, c' n ≠ 0 → n ∈ Icc (A + 1) (A + L)) (hAL : A + L ≤ N) :
    |∑ d ∈ Icc 1 N, c d / d * kernelStatisticAll N c' d| ≤
      1 / 2 * Real.sqrt (2 * (Q₀ : ℝ) ^ 2 * ((Q₀ : ℝ) + 1)) *
          Real.sqrt ((L : ℝ) + (Q₀ : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 4) +
        1 / 8 * Real.sqrt (2 * (Q₀ : ℝ) ^ 4 * ((Q₀ : ℝ) + 1)) *
          Real.sqrt ((L : ℝ) + (Q₀ : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 6) := by
  refine (abs_sum_mul_kernelStatisticAll_le_selberg hQ₀ hQN hsupp hsupp' hAL).trans ?_
  have h1 := sum_selberg_sq_mul_pow_four_le (N := N) hc hsupp
  have h2 := sum_selberg_sq_mul_pow_six_le (N := N) hc hsupp
  gcongr

/-- **The all-moduli dual-norm large-sieve theorem.**
For any set `S ⊆ [1, Q₀]` of moduli (prime or composite), linearizing `Σ_{d ∈ S} |Λ_d^{all}(c')|/d`
by the sign witness `c(d) = ±1` on `S` and passing through the cyclotomic–Selberg bridge resolves
divisor overlap between composite moduli and yields the fourth-order Montgomery–Vaughan large-sieve
bound. -/
theorem dual_norm_kernelStatisticAll_le_largeSieve {N Q₀ A L : ℕ} {S : Finset ℕ}
    (hQ₀ : 2 ≤ Q₀) (hQN : Q₀ ≤ N) (hS : S ⊆ Icc 1 Q₀) (c' : ℕ → ℝ)
    (hsupp' : ∀ n, c' n ≠ 0 → n ∈ Icc (A + 1) (A + L)) (hAL : A + L ≤ N) :
    ∑ d ∈ S, |kernelStatisticAll N c' d| / d ≤
      1 / 2 * Real.sqrt (2 * (Q₀ : ℝ) ^ 2 * ((Q₀ : ℝ) + 1)) *
          Real.sqrt ((L : ℝ) + (Q₀ : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 4) +
        1 / 8 * Real.sqrt (2 * (Q₀ : ℝ) ^ 4 * ((Q₀ : ℝ) + 1)) *
          Real.sqrt ((L : ℝ) + (Q₀ : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 6) := by
  classical
  set c : ℕ → ℝ := fun d => if d ∈ S then (if 0 ≤ kernelStatisticAll N c' d then 1 else -1) else 0
  have hc1 : ∀ d, |c d| ≤ 1 := fun d => by simp only [c]; split_ifs <;> norm_num
  have hsupp : ∀ d, c d ≠ 0 → d ≤ Q₀ := fun d h => by
    have hdS : d ∈ S := by by_contra hd; exact h (by simp [c, hd])
    exact (mem_Icc.mp (hS hdS)).2
  have hSN : S ⊆ Icc 1 N := hS.trans (Icc_subset_Icc le_rfl hQN)
  have heq : ∑ d ∈ S, |kernelStatisticAll N c' d| / d =
      ∑ d ∈ Icc 1 N, c d / d * kernelStatisticAll N c' d := by
    rw [← sum_subset hSN fun d _ hd => by simp [c, hd]]
    refine sum_congr rfl fun d hd => ?_
    simp only [c, if_pos hd]
    split_ifs with h0
    · rw [abs_of_nonneg h0]; ring
    · rw [abs_of_neg (not_le.mp h0)]; ring
  rw [heq]
  exact (le_abs_self _).trans
    (abs_sum_mul_kernelStatisticAll_le_bounded hQ₀ hQN hc1 hsupp hsupp' hAL)

/-- **Fourth-order large-sieve dispersion for bounded rows at all moduli.**
Upgrades `abs_rowBilinear_add_mean_add_beta_le_bounded` from third order and `L + 2Q₀² - 1` to
fourth order, centred by `kernelMeanMain`, with the sharp Montgomery–Vaughan constant
`L + Q₀² - 1`. -/
theorem abs_rowBilinear_sub_kernelMeanMain_le_bounded_fourthOrder {N Q₀ A L : ℕ} {S : Finset ℕ}
    (hQ₀ : 2 ≤ Q₀) (hQN : Q₀ ≤ N) (hS : S ⊆ Icc 1 Q₀) {c c' : ℕ → ℝ}
    (hc1 : ∀ d, |c d| ≤ 1) (hsupp : ∀ d, c d ≠ 0 → d ∈ S)
    (hsupp' : ∀ n, c' n ≠ 0 → n ∈ Icc (A + 1) (A + L)) (hAL : A + L ≤ N) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' - kernelMeanMain N c c'| ≤
      1 / 2 * Real.sqrt (2 * (Q₀ : ℝ) ^ 2 * ((Q₀ : ℝ) + 1)) *
          Real.sqrt ((L : ℝ) + (Q₀ : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 4) +
        1 / 8 * Real.sqrt (2 * (Q₀ : ℝ) ^ 4 * ((Q₀ : ℝ) + 1)) *
          Real.sqrt ((L : ℝ) + (Q₀ : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 6) +
        6 * (∑ d ∈ S, (d : ℝ) ^ 3) *
          ∑ n ∈ Icc (A + 1) (A + L), |c' n| / (n : ℝ) ^ 4 := by
  have hSN : S ⊆ Icc 1 N := hS.trans (Icc_subset_Icc le_rfl hQN)
  have hdual := abs_rowBilinear_sub_kernelMeanMain_le_dual N hSN c' hc1 hsupp
  have hls := dual_norm_kernelStatisticAll_le_largeSieve hQ₀ hQN hS c' hsupp' hAL
  have hWsub : Icc (A + 1) (A + L) ⊆ Icc 1 N := Icc_subset_Icc (by omega) hAL
  have hcn : ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 =
      ∑ n ∈ Icc (A + 1) (A + L), |c' n| / (n : ℝ) ^ 4 := by
    rw [← sum_subset hWsub fun n _ hnW => by
      have : c' n = 0 := by by_contra h; exact hnW (hsupp' n h)
      simp [this]]
  rw [hcn] at hdual
  linarith

/-- **Unconditional all-inputs dual-norm large-sieve theorem at all moduli (zero hypotheses).** -/
theorem dual_norm_kernelStatisticAll_all_le_largeSieve (N : ℕ) (c' : ℕ → ℝ) :
    ∑ d ∈ Icc 1 N, |kernelStatisticAll N c' d| / d ≤
      1 / 2 * Real.sqrt (2 * (N : ℝ) ^ 2 * ((N : ℝ) + 1)) *
          Real.sqrt ((N : ℝ) + (N : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc 1 N, c' n ^ 2 / (n : ℝ) ^ 4) +
        1 / 8 * Real.sqrt (2 * (N : ℝ) ^ 4 * ((N : ℝ) + 1)) *
          Real.sqrt ((N : ℝ) + (N : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc 1 N, c' n ^ 2 / (n : ℝ) ^ 6) := by
  classical
  rcases Nat.lt_or_ge N 2 with hN2 | hN2
  · have h0 : ∑ d ∈ Icc 1 N, |kernelStatisticAll N c' d| / d = 0 := by
      refine sum_eq_zero fun d hd => ?_
      have hd1 : d = 1 := by have := mem_Icc.mp hd; omega
      subst hd1
      rw [kernelStatisticAll_one, abs_zero, zero_div]
    rw [h0]
    positivity
  · set c'₀ : ℕ → ℝ := fun n => if n ∈ Icc 1 N then c' n else 0
    have hsupp' : ∀ n, c'₀ n ≠ 0 → n ∈ Icc (0 + 1) (0 + N) := fun n h => by
      rw [zero_add, zero_add]
      by_contra hn; exact h (if_neg hn)
    have hstat : ∀ d, kernelStatisticAll N c'₀ d = kernelStatisticAll N c' d := fun d => by
      unfold kernelStatisticAll
      exact sum_congr rfl fun n hn => by simp only [c'₀, if_pos hn]
    have hls := dual_norm_kernelStatisticAll_le_largeSieve hN2 le_rfl (Subset.refl (Icc 1 N))
      c'₀ hsupp' (by omega : 0 + N ≤ N)
    simp only [zero_add, hstat] at hls
    have hY4 : ∑ n ∈ Icc 1 N, c'₀ n ^ 2 / (n : ℝ) ^ 4 = ∑ n ∈ Icc 1 N, c' n ^ 2 / (n : ℝ) ^ 4 :=
      sum_congr rfl fun n hn => by simp only [c'₀, if_pos hn]
    have hY6 : ∑ n ∈ Icc 1 N, c'₀ n ^ 2 / (n : ℝ) ^ 6 = ∑ n ∈ Icc 1 N, c' n ^ 2 / (n : ℝ) ^ 6 :=
      sum_congr rfl fun n hn => by simp only [c'₀, if_pos hn]
    rwa [hY4, hY6] at hls

end

end GaloisForLFunctions.BezoutValuationIncidence
