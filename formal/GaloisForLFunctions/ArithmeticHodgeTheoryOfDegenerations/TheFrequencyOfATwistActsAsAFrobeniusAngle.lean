import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheSecondOrderTermIsTheDirichletSeriesOfTheSpectrum

/-!
# The frequency of a twist acts as a Frobenius angle

Over a pure curve the rescaled limit of the family of lattice tests is the Hurwitz form of the
fractional Frobenius angles, `ζ(β+1, u) + ζ(β+1, 1 − u)` (`tendsto_rpow_mul_curveBulk`). Over `ℤ`
the same form appears for a single frequency:

* **The spectrum of a cosine** (`twistCoeff_cosTwist`, `twistPower_cosTwist`): the twist
  `n ↦ cos(2π a n/M)`, `0 < a < M`, has `S_k = (M/2)([M ∣ k + a] + [M ∣ k − a])`: power `1/4` at the
  two modes `k = a` and `k = M − a`.
* **The second order of a frequency** (`twistSpectralSum_cosTwist`, `cosTwist_layer_criticalCurve`):
  for `2a ≠ M`, the window `h(log(n/N)) cos(2πan/M)/√n` has second-order coefficient
  `(βA_φ/(K∫φ²)) · ½ (ζ(β+1, u) + ζ(β+1, 1 − u))`, `u = a/M`.

The coefficient depends on the frequency `u` only, not on the period, and it is the Hurwitz form
that a Frobenius angle `u` contributes over `𝔽_q`: the angle of Frobenius acts on the complete
family over `𝔽_q` exactly as a twist frequency acts on the horizon layer over `ℤ`. As `u → 0` the
form grows like `u^{−(β+1)}`: the frequency approaches the untwisted conductor-one direction, whose
second order carries Weil's form.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ h : ℝ → ℝ} {A : ℝ}

/-- The cosine twist `n ↦ cos(2π a n/M)` of frequency `a/M`. -/
def cosTwist (a M : ℕ) (n : ℕ) : ℝ := Real.cos (2 * Real.pi * a * n / M)

/-- `cos(2π a n/M) = Re e(n a/M)`. -/
theorem cosTwist_eq_re (a M n : ℕ) :
    cosTwist a M n = (Complex.exp (2 * Real.pi * Complex.I * (n * (a : ℤ) / M))).re := by
  unfold cosTwist
  rw [← Complex.exp_ofReal_mul_I_re]
  congr 2
  push_cast
  ring

/-- A cosine of frequency `a/M`, `0 < a < M`, is a mean-zero twist of period `M`. -/
theorem meanZeroTwist_cosTwist {a M : ℕ} (ha : 0 < a) (haM : a < M) :
    MeanZeroTwist (cosTwist a M) M := by
  have hM : 0 < M := by omega
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  refine ⟨hM, fun n => ?_, ?_⟩
  · unfold cosTwist
    rw [show 2 * Real.pi * a * ((n + M : ℕ) : ℝ) / M = 2 * Real.pi * a * n / M + a * (2 * Real.pi)
      by push_cast; field_simp]
    exact Real.cos_add_nat_mul_two_pi _ a
  · simp_rw [cosTwist_eq_re]
    rw [← Complex.re_sum, sum_range_cexp_int hM (a : ℤ)]
    have hnd : ¬ (M : ℤ) ∣ (a : ℤ) := by
      intro hd
      have := Int.le_of_dvd (by exact_mod_cast ha) hd
      omega
    rw [if_neg hnd, Complex.zero_re]

/-- **The spectrum of a cosine**: `S_k = (M/2)([M ∣ k + a] + [M ∣ k − a])`. -/
theorem twistCoeff_cosTwist {a M : ℕ} (hM : 0 < M) (k : ℕ) :
    twistCoeff (cosTwist a M) M k =
      ((M : ℂ) / 2) * ((if (M : ℤ) ∣ (k : ℤ) + a then 1 else 0) +
        (if (M : ℤ) ∣ (k : ℤ) - a then 1 else 0)) := by
  unfold twistCoeff cosTwist
  have hsplit : ∀ n ∈ range M, ((Real.cos (2 * Real.pi * a * n / M) : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (k * n / M)) =
      (Complex.exp (2 * Real.pi * Complex.I * (n * (((k : ℤ) + a : ℤ) : ℂ) / M)) +
        Complex.exp (2 * Real.pi * Complex.I * (n * (((k : ℤ) - a : ℤ) : ℂ) / M))) / 2 := by
    intro n _
    have hx1 : ((2 * Real.pi * a * n / M : ℝ) : ℂ) * Complex.I +
        2 * Real.pi * Complex.I * (k * n / M) =
        2 * Real.pi * Complex.I * (n * (((k : ℤ) + a : ℤ) : ℂ) / M) := by push_cast; ring
    have hx2 : -((2 * Real.pi * a * n / M : ℝ) : ℂ) * Complex.I +
        2 * Real.pi * Complex.I * (k * n / M) =
        2 * Real.pi * Complex.I * (n * (((k : ℤ) - a : ℤ) : ℂ) / M) := by push_cast; ring
    rw [Complex.ofReal_cos, Complex.cos, div_mul_eq_mul_div, add_mul, ← Complex.exp_add,
      ← Complex.exp_add, hx1, hx2]
  rw [sum_congr rfl hsplit, ← Finset.sum_div, Finset.sum_add_distrib,
    sum_range_cexp_int hM, sum_range_cexp_int hM]
  split_ifs <;> ring

/-- The two modes of a cosine: for `0 < a < M` and `k < M`, `[M ∣ k + a] = [k = M − a]` and
`[M ∣ k − a] = [k = a]`. -/
theorem dvd_add_iff_eq {a M k : ℕ} (ha : 0 < a) (haM : a < M) (hk : k < M) :
    (M : ℤ) ∣ (k : ℤ) + a ↔ k = M - a := by
  constructor
  · rintro ⟨t, ht⟩
    have h1 : 0 < t := by
      by_contra h; push Not at h
      have : (M : ℤ) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
      omega
    have h2 : t < 2 := by
      by_contra h; push Not at h
      have : (M : ℤ) * 2 ≤ M * t := mul_le_mul_of_nonneg_left h (by positivity)
      omega
    have : t = 1 := by omega
    subst this
    omega
  · intro h
    exact ⟨1, by omega⟩

theorem dvd_sub_iff_eq {a M k : ℕ} (haM : a < M) (hk : k < M) :
    (M : ℤ) ∣ (k : ℤ) - a ↔ k = a := by
  constructor
  · rintro ⟨t, ht⟩
    have h1 : t = 0 := by
      by_contra h
      rcases lt_or_gt_of_ne h with h | h
      · have : (M : ℤ) * t ≤ -M := by nlinarith
        omega
      · have : (M : ℤ) ≤ M * t := by nlinarith
        omega
    subst h1
    omega
  · intro h
    exact ⟨0, by omega⟩

/-- **The power spectrum of a cosine**: `1/4` at `k = a` and at `k = M − a` (`2a ≠ M`). -/
theorem twistPower_cosTwist {a M : ℕ} (ha : 0 < a) (haM : a < M) (h2a : 2 * a ≠ M) {k : ℕ}
    (hk : k < M) :
    twistPower (cosTwist a M) M k = if k = a ∨ k = M - a then 1 / 4 else 0 := by
  have hM : 0 < M := by omega
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  unfold twistPower
  rw [twistCoeff_cosTwist hM k]
  simp only [dvd_add_iff_eq ha haM hk, dvd_sub_iff_eq haM hk]
  by_cases h1 : k = a
  · have h2 : ¬ k = M - a := by omega
    rw [if_neg h2, if_pos h1, if_pos (Or.inl h1)]
    rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_ofNat]
    norm_num
    field_simp
    norm_num
  · by_cases h2 : k = M - a
    · rw [if_pos h2, if_neg h1, if_pos (Or.inr h2)]
      rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_ofNat]
      norm_num
      field_simp
      norm_num
    · rw [if_neg h2, if_neg h1, if_neg (by tauto)]
      simp

/-- **The second order of a frequency**: the spectral sum of a cosine of frequency `u = a/M`,
`2a ≠ M`, is `½ (ζ(s, u) + ζ(s, 1 − u))`. -/
theorem twistSpectralSum_cosTwist {a M : ℕ} (ha : 0 < a) (haM : a < M) (h2a : 2 * a ≠ M)
    (s : ℝ) :
    twistSpectralSum s (cosTwist a M) M =
      (hurwitzSum s ((a : ℝ) / M) + hurwitzSum s (1 - (a : ℝ) / M)) / 2 := by
  have hM : 0 < M := by omega
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  unfold twistSpectralSum
  have hpt : ∀ k ∈ Ico 1 M, twistPower (cosTwist a M) M k *
      (hurwitzSum s ((k : ℝ) / M) + hurwitzSum s (1 - (k : ℝ) / M)) =
      if k = a ∨ k = M - a then (hurwitzSum s ((k : ℝ) / M) +
        hurwitzSum s (1 - (k : ℝ) / M)) / 4 else 0 := by
    intro k hk
    rw [twistPower_cosTwist ha haM h2a (Finset.mem_Ico.mp hk).2]
    split_ifs <;> ring
  rw [sum_congr rfl hpt, ← Finset.sum_filter]
  have hfil : (Ico 1 M).filter (fun k => k = a ∨ k = M - a) = {a, M - a} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hne : a ≠ M - a := by omega
  rw [hfil, Finset.sum_pair hne]
  have e : (((M - a : ℕ) : ℝ) / M) = 1 - (a : ℝ) / M := by
    rw [Nat.cast_sub haM.le]; field_simp
  rw [e, sub_sub_cancel]
  ring

/-- **The second-order term of a cosine window.** Along `c^{β+1}/log N → K` the window
`h(log(n/N)) cos(2πan/M)/√n`, `0 < a < M`, `2a ≠ M`, has second-order term
`(βA_φ/(K∫φ²)) · ½ (ζ(β+1, a/M) + ζ(β+1, 1 − a/M)) ∫ e^{−(β+1)y} H²`. -/
theorem cosTwist_layer_criticalCurve (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 4 < p)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {β Aφ : ℝ} (hβ : 0 < β)
    (hT : Tendsto (fun x => x ^ β * ArithmeticDegenerationTheory.spectralTail φ x) atTop (𝓝 Aφ))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    {a M : ℕ} (ha : 0 < a) (haM : a < M) (h2a : 2 * a ≠ M) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h (cosTwist a M) N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2)) atTop
      (𝓝 (β * Aφ / (K * ∫ u, φ u ^ 2) *
        ((hurwitzSum (β + 1) ((a : ℝ) / M) + hurwitzSum (β + 1) (1 - (a : ℝ) / M)) / 2) *
        ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2)) := by
  have h := periodicTwist_layer_criticalCurve_of_regularTail hφ hφsupp hφ2 hp hCφ hdecay hβ hT hh hA
    hsupp hc1 hK hcrit (meanZeroTwist_cosTwist ha haM)
  rwa [twistSpectralSum_cosTwist ha haM h2a] at h

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
