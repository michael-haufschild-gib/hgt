import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheRamanujanWindowCountsEveryConductor

/-!
# The energy of a twist is its spectrum

For a horizon window twisted by a mean-zero `M`-periodic weight `χ`, the energy law of periodic
twists computes the block energy through the autocorrelation `C_χ`. This file diagonalizes that law
by the discrete Fourier transform of the twist, `S_k = Σ_{n<M} χ(n) e(kn/M)`, `χ̂(k) = S_k/M`.

* **Spectral form of the autocorrelation** (`sum_normSq_twistCoeff_mul_cexp`):
  `Σ_{k<M} |S_k|² e(kδ/M) = M² C_χ(δ)`; at `δ = 0` this is Parseval,
  `Σ_{0<k<M} |χ̂(k)|² = M⁻¹ Σ_{n<M} χ(n)²` (`sum_twistPower`).
* **Poisson summation on a shifted lattice** (`hasSum_shellSpectrum_shift`):
  `Σ_{j∈ℤ} |φ̂(2πa(j + θ))|² = a⁻¹ Σ_m e(θm) G(m/a)`, `G` the autocorrelation of the profile. The
  left side splits into the two one-sided **shifted densities** `D_θ(a) + D_{1−θ}(a)`,
  `D_u(a) = Σ_{n≥0} |φ̂(2πa(n + u))|²` (`hasSum_shellSpectrum_shift_split`).
* **The energy of a periodic twist** (`abs_twistEnergy_sub_le`):
  `E_N = 2π Σ_{0<k<M} |χ̂(k)|² (𝒜^{(k/M)}_N + 𝒜^{(1−k/M)}_N) + O(c/N)`,
  `𝒜^{(u)}_N = N⁻¹ Σ_n h(log(n/N))² D_u(cn/N)`.

The mode `k/M` of the twist meets the harmonics of the atom grid at the shifted frequencies
`j + k/M`, with weight its power `|χ̂(k)|²`. The mean-zero condition removes the mode `k = 0`, the
only one carrying the frequency `0` (the Riemann sum of Weil's form).
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ h : ℝ → ℝ} {A : ℝ}

/-- The discrete Fourier coefficient `S_k = Σ_{n<M} χ(n) e(kn/M)` of a twist. -/
def twistCoeff (χ : ℕ → ℝ) (M k : ℕ) : ℂ :=
  ∑ n ∈ range M, (χ n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (k * n / M))

/-- The power `|χ̂(k)|² = |S_k|²/M²` of the mode `k/M` of a twist. -/
def twistPower (χ : ℕ → ℝ) (M k : ℕ) : ℝ := ‖twistCoeff χ M k‖ ^ 2 / (M : ℝ) ^ 2

/-- The shifted density `D_u(s) = Σ_{n ≥ 0} |φ̂(2πs(n + u))|²`. -/
def twistDensity (φ : ℝ → ℝ) (u s : ℝ) : ℝ := ∑' n : ℕ, shellSpectrum φ (s * ((n : ℝ) + u))

/-- The window average `N⁻¹ Σ_{n ≤ N} h(log(n/N))² a(cn/N)` of a density `a`. -/
def densityAlias (a : ℝ → ℝ) (h : ℝ → ℝ) (c : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Icc 1 N, h (Real.log n - Real.log N) ^ 2 * a (c * n / N)

/-- The spectral aliasing of a twisted window, `Σ_{0<k<M} |χ̂(k)|² (𝒜^{(k/M)} + 𝒜^{(1−k/M)})`. -/
def twistAlias (φ h : ℝ → ℝ) (χ : ℕ → ℝ) (M : ℕ) (c : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Ico 1 M, twistPower χ M k *
    (densityAlias (twistDensity φ ((k : ℝ) / M)) h c N +
      densityAlias (twistDensity φ (1 - (k : ℝ) / M)) h c N)

theorem twistPower_nonneg (χ : ℕ → ℝ) (M k : ℕ) : 0 ≤ twistPower χ M k := by
  unfold twistPower; positivity

theorem twistCoeff_zero {χ : ℕ → ℝ} {M : ℕ} (hχ : MeanZeroTwist χ M) : twistCoeff χ M 0 = 0 := by
  unfold twistCoeff
  simp only [Nat.cast_zero, zero_mul, zero_div, mul_zero, Complex.exp_zero, mul_one]
  exact_mod_cast hχ.mean_zero

/-! ### The spectral form of the autocorrelation -/

/-- Orthogonality of the characters of `ℤ/M`: `Σ_{k<M} e(kt/M) = M [M ∣ t]`. -/
theorem sum_range_cexp_int {M : ℕ} (hM : 0 < M) (t : ℤ) :
    ∑ k ∈ range M, Complex.exp (2 * Real.pi * Complex.I * (k * t / M)) =
      if (M : ℤ) ∣ t then (M : ℂ) else 0 := by
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  set ω := Complex.exp (2 * Real.pi * Complex.I * (t / M)) with hω
  have hpow : ∀ k : ℕ, Complex.exp (2 * Real.pi * Complex.I * (k * t / M)) = ω ^ k := fun k => by
    rw [hω, ← Complex.exp_nat_mul]; congr 1; ring
  have hωM : ω ^ M = 1 := by
    rw [← hpow M, mul_div_cancel_left₀ _ hM0,
      show 2 * (Real.pi : ℂ) * Complex.I * t = t * (2 * Real.pi * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I t
  simp_rw [hpow]
  rw [sum_range_pow_root hωM]
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hiff : ω = 1 ↔ (M : ℤ) ∣ t := by
    rw [hω, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      have h1 : (t : ℂ) / M = n := mul_left_cancel₀ h2 (by rw [hn]; ring)
      have h3 : (t : ℂ) = ((M * n : ℤ) : ℂ) := by
        rw [(div_eq_iff hM0).mp h1]; push_cast; ring
      exact ⟨n, by exact_mod_cast h3⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, by push_cast; field_simp⟩
  by_cases hd : (M : ℤ) ∣ t
  · rw [if_pos (hiff.mpr hd), if_pos hd]
  · rw [if_neg (fun h' => hd (hiff.mp h')), if_neg hd]

/-- Among `n' < M`, exactly `n' ≡ n + δ (mod M)` has `M ∣ n − n' + δ`. -/
theorem sum_range_ite_dvd {M : ℕ} (hM : 0 < M) (n : ℕ) (δ : ℤ) (f : ℕ → ℂ) :
    ∑ n' ∈ range M, (if (M : ℤ) ∣ (n : ℤ) - n' + δ then f n' else 0) =
      f (((n : ℤ) + δ) % M).toNat := by
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  set r := ((n : ℤ) + δ) % M with hr
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hM'.ne'
  have hrM : r < M := Int.emod_lt_of_pos _ hM'
  have hrr : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg hr0
  have hiff : ∀ n' : ℕ, n' < M → ((M : ℤ) ∣ (n : ℤ) - n' + δ ↔ n' = r.toNat) := by
    intro n' hn'
    constructor
    · intro hd
      have h1 : ((n : ℤ) + δ) % M = (n' : ℤ) % M := by
        rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]
        convert hd using 1; ring
      rw [Int.emod_eq_of_lt (Nat.cast_nonneg _) (by exact_mod_cast hn')] at h1
      omega
    · rintro rfl
      rw [hrr]
      have := Int.emod_def ((n : ℤ) + δ) M
      exact ⟨((n : ℤ) + δ) / M, by rw [← hr] at this; linarith⟩
  rw [Finset.sum_eq_single r.toNat]
  · rw [if_pos ((hiff _ (by omega)).mpr rfl)]
  · intro b hb hne
    rw [if_neg (fun hd => hne ((hiff b (Finset.mem_range.mp hb)).mp hd))]
  · intro hn
    exact absurd (Finset.mem_range.mpr (by omega)) hn

/-- **The spectral form of the autocorrelation**: `Σ_{k<M} |S_k|² e(kδ/M) = M² C_χ(δ)`. -/
theorem sum_normSq_twistCoeff_mul_cexp {χ : ℕ → ℝ} {M : ℕ} (hM : 0 < M) (δ : ℤ) :
    ∑ k ∈ range M, ((‖twistCoeff χ M k‖ ^ 2 : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (k * δ / M)) =
      (((M : ℝ) ^ 2 * autoCorr χ M δ : ℝ) : ℂ) := by
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hterm : ∀ k : ℕ, ((‖twistCoeff χ M k‖ ^ 2 : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (k * δ / M)) =
      ∑ n ∈ range M, ∑ n' ∈ range M, ((χ n * χ n' : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (k * (((n : ℤ) - n' + δ : ℤ) : ℂ) / M)) := by
    intro k
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, twistCoeff, map_sum, Finset.sum_mul,
      Finset.sum_mul]
    refine sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine sum_congr rfl fun n' _ => ?_
    have hc : (starRingEnd ℂ) ((χ n' : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (k * n' / M))) =
        (χ n' : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (k * n' / M))) := by
      rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
      congr 2
      simp only [map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
      ring
    rw [hc]
    have he : 2 * (Real.pi : ℂ) * Complex.I * (k * n / M) +
        -(2 * Real.pi * Complex.I * (k * n' / M)) + 2 * Real.pi * Complex.I * (k * δ / M) =
        2 * Real.pi * Complex.I * (k * (((n : ℤ) - n' + δ : ℤ) : ℂ) / M) := by
      push_cast; ring
    calc (χ n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (k * n / M)) *
          ((χ n' : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (k * n' / M)))) *
          Complex.exp (2 * Real.pi * Complex.I * (k * δ / M)) =
        ((χ n : ℂ) * χ n') * (Complex.exp (2 * Real.pi * Complex.I * (k * n / M)) *
          Complex.exp (-(2 * Real.pi * Complex.I * (k * n' / M))) *
          Complex.exp (2 * Real.pi * Complex.I * (k * δ / M))) := by ring
      _ = _ := by
        rw [← Complex.exp_add, ← Complex.exp_add, he]
        push_cast; ring
  simp_rw [hterm]
  rw [Finset.sum_comm]
  have hinner : ∀ n ∈ range M, ∑ k ∈ range M, ∑ n' ∈ range M, ((χ n * χ n' : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (k * (((n : ℤ) - n' + δ : ℤ) : ℂ) / M)) =
      (M : ℂ) * ((χ n * periodicExt χ M (n + δ) : ℝ) : ℂ) := by
    intro n _
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp_rw [sum_range_cexp_int hM]
    have e : ∀ n' ∈ range M, ((χ n * χ n' : ℝ) : ℂ) *
        (if (M : ℤ) ∣ (n : ℤ) - n' + δ then (M : ℂ) else 0) =
        (M : ℂ) * (χ n : ℂ) * (if (M : ℤ) ∣ (n : ℤ) - n' + δ then (χ n' : ℂ) else 0) :=
      fun n' _ => by split_ifs <;> push_cast <;> ring
    rw [sum_congr rfl e, ← Finset.mul_sum, sum_range_ite_dvd hM n δ (fun j => (χ j : ℂ)),
      periodicExt]
    push_cast; ring
  rw [sum_congr rfl hinner, ← Finset.mul_sum, autoCorr, periodMean]
  push_cast
  rw [pow_two, mul_assoc, mul_inv_cancel_left₀ hM0]

/-- **Parseval for a twist**: `Σ_{0<k<M} |χ̂(k)|² = M⁻¹ Σ_{n<M} χ(n)²`. -/
theorem sum_twistPower {χ : ℕ → ℝ} {M : ℕ} (hχ : MeanZeroTwist χ M) :
    ∑ k ∈ Ico 1 M, twistPower χ M k = (M : ℝ)⁻¹ * ∑ n ∈ range M, χ n ^ 2 := by
  have hM := hχ.pos
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have h0 := sum_normSq_twistCoeff_mul_cexp (χ := χ) hM 0
  simp only [Int.cast_zero, mul_zero, zero_div, Complex.exp_zero, mul_one] at h0
  have hreal : ∑ k ∈ range M, ‖twistCoeff χ M k‖ ^ 2 = (M : ℝ) ^ 2 * autoCorr χ M 0 := by
    exact_mod_cast h0
  have hC0 : autoCorr χ M 0 = (M : ℝ)⁻¹ * ∑ n ∈ range M, χ n ^ 2 := by
    rw [autoCorr, periodMean]
    congr 1
    refine sum_congr rfl fun n _ => ?_
    rw [add_zero, periodicExt_natCast hχ.periodic, sq]
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hM, twistCoeff_zero hχ, norm_zero,
    hC0] at hreal
  unfold twistPower
  rw [← Finset.sum_div, div_eq_iff (pow_ne_zero 2 hM0)]
  have : (0 : ℝ) ^ 2 = 0 := by norm_num
  rw [this, zero_add] at hreal
  rw [hreal]
  field_simp

/-! ### Poisson summation on a shifted lattice -/

theorem paperFT_modulate_shift (c : ℝ → ℂ) (γ : ℝ) (z : ℂ) :
    paperFT (fun u => Complex.exp (-(Complex.I * γ * u)) * c u) z = paperFT c (z - γ) := by
  rw [paperFT_def, paperFT_def]
  congr 1 with u
  rw [mul_comm (Complex.exp _) (c u), mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- **Poisson summation on a shifted lattice**: `Σ_j |φ̂(2πa(j + θ))|² = a⁻¹ Σ_m e(θm) G(m/a)`. -/
theorem hasSum_shellSpectrum_shift (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {a : ℝ} (ha : 0 < a) (θ : ℝ) :
    HasSum (fun j : ℤ => ((shellSpectrum φ (a * (j + θ)) : ℝ) : ℂ))
      (((a⁻¹ : ℝ) : ℂ) * ∑' m : ℤ, Complex.exp (2 * Real.pi * Complex.I * (θ * m)) *
        ((shellAutocorr φ (m * a⁻¹) : ℝ) : ℂ)) := by
  have ha0 := ha.ne'
  set Gc : ℝ → ℂ := fun u => ((shellAutocorr φ u : ℝ) : ℂ) with hGc
  have hG : ContDiff ℝ 2 Gc := Complex.ofRealCLM.contDiff.comp (contDiff_shellAutocorr hφ hφsupp)
  set γ : ℝ := -(2 * Real.pi * a * θ) with hγ
  set cf : ℝ → ℂ := fun u => Complex.exp (-(Complex.I * γ * u)) * Gc u with hcf
  have hc : ContDiff ℝ 2 cf := by
    refine ContDiff.mul ?_ hG
    exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff).neg
  have hcs : ∀ u, cf u ≠ 0 → |u| ≤ 1 := by
    intro u hu
    by_contra hlt
    apply hu
    simp only [hcf, hGc]
    rw [shellAutocorr_eq_zero_of_one_le_abs hφ hφsupp (le_of_lt (not_le.mp hlt)),
      Complex.ofReal_zero, mul_zero]
  have h := RHTower.hasSum_paperFT_lattice (inv_pos.mpr ha) hc hcs
  have hl : ∀ k : ℤ, paperFT cf (((k : ℝ) * (2 * Real.pi / a⁻¹) : ℝ) : ℂ) =
      ((shellSpectrum φ (a * (k + θ)) : ℝ) : ℂ) := by
    intro k
    rw [hcf, paperFT_modulate_shift]
    have e : ((((k : ℝ) * (2 * Real.pi / a⁻¹) : ℝ) : ℂ) - (γ : ℂ)) =
        (((2 * Real.pi * (a * (k + θ)) : ℝ)) : ℂ) := by
      rw [hγ]; push_cast; field_simp; ring
    rw [e, hGc]
    exact paperFT_shellAutocorr hφ hφsupp _
  have hr : ∀ m : ℤ, cf (m * a⁻¹) = Complex.exp (2 * Real.pi * Complex.I * (θ * m)) *
      ((shellAutocorr φ (m * a⁻¹) : ℝ) : ℂ) := by
    intro m
    have ha0' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0
    simp only [hcf, hGc, hγ]
    congr 2
    push_cast
    field_simp
  simp_rw [hl, hr] at h
  exact h

/-- The shifted lattice spectrum is the sum of the two shifted densities:
`Σ_{j∈ℤ} |φ̂(2πa(j + θ))|² = D_θ(a) + D_{1−θ}(a)`. -/
theorem hasSum_shellSpectrum_shift_split (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {a : ℝ} (ha : 0 < a) (θ : ℝ) :
    HasSum (fun j : ℤ => shellSpectrum φ (a * (j + θ)))
      (twistDensity φ θ a + twistDensity φ (1 - θ) a) := by
  have hc := hasSum_shellSpectrum_shift hφ hφsupp ha θ
  have hs : Summable fun j : ℤ => shellSpectrum φ (a * (j + θ)) :=
    Complex.summable_ofReal.mp hc.summable
  have hpair := hs.hasSum.nat_add_neg_add_one
  simp only [Int.cast_natCast, Int.cast_neg, Int.cast_add, Int.cast_one] at hpair
  have hneg : ∀ n : ℕ, shellSpectrum φ (a * (-((n : ℝ) + 1) + θ)) =
      shellSpectrum φ (a * ((n : ℝ) + (1 - θ))) := fun n => by
    rw [← shellSpectrum_neg]; congr 1; ring
  simp_rw [hneg] at hpair
  have h1 : Summable fun n : ℕ => shellSpectrum φ (a * ((n : ℝ) + θ)) :=
    hpair.summable.of_nonneg_of_le (fun n => shellSpectrum_nonneg _)
      (fun n => le_add_of_nonneg_right (shellSpectrum_nonneg _))
  have h2 : Summable fun n : ℕ => shellSpectrum φ (a * ((n : ℝ) + (1 - θ))) :=
    hpair.summable.of_nonneg_of_le (fun n => shellSpectrum_nonneg _)
      (fun n => le_add_of_nonneg_left (shellSpectrum_nonneg _))
  have heq : ∑' j : ℤ, shellSpectrum φ (a * (j + θ)) =
      twistDensity φ θ a + twistDensity φ (1 - θ) a := by
    rw [← hpair.tsum_eq, h1.tsum_add h2]; rfl
  rw [← heq]
  exact hs.hasSum

/-! ### The energy of a periodic twist -/

/-- **The offset sum of a periodic twist is its spectrum**: for `a ≤ D`,
`Σ_{|δ| ≤ D} C_χ(δ) G(δ/a) = a Σ_{0<k<M} |χ̂(k)|² (D_{k/M}(a) + D_{1−k/M}(a))`. -/
theorem sum_offset_twist_eq (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {χ : ℕ → ℝ} {M : ℕ} (hχ : MeanZeroTwist χ M) {a : ℝ} (ha : 0 < a) {D : ℕ} (haD : a ≤ D) :
    ∑ δ ∈ Finset.Icc (-(D : ℤ)) D, autoCorr χ M δ * shellAutocorr φ (δ * a⁻¹) =
      a * ∑ k ∈ Ico 1 M, twistPower χ M k *
        (twistDensity φ ((k : ℝ) / M) a + twistDensity φ (1 - (k : ℝ) / M) a) := by
  have hM := hχ.pos
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hG1 : ∀ t, 1 ≤ |t| → shellAutocorr φ t = 0 := fun t ht =>
    shellAutocorr_eq_zero_of_one_le_abs hφ hφsupp ht
  have hmode : ∀ k : ℕ, ∑ δ ∈ Finset.Icc (-(D : ℤ)) D,
      Complex.exp (2 * Real.pi * Complex.I * (k * δ / M)) * ((shellAutocorr φ (δ * a⁻¹) : ℝ) : ℂ) =
      (a : ℂ) * (((twistDensity φ ((k : ℝ) / M) a + twistDensity φ (1 - (k : ℝ) / M) a : ℝ)) :
        ℂ) := by
    intro k
    have hP := hasSum_shellSpectrum_shift hφ hφsupp ha ((k : ℝ) / M)
    have hS := (Complex.hasSum_ofReal.mpr
      (hasSum_shellSpectrum_shift_split hφ hφsupp ha ((k : ℝ) / M))).tsum_eq
    rw [← hS, hP.tsum_eq, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ ha.ne',
      Complex.ofReal_one, one_mul]
    rw [tsum_eq_sum (s := Finset.Icc (-(D : ℤ)) D)]
    · refine sum_congr rfl fun δ _ => ?_
      congr 2; push_cast; ring
    · intro m hm
      rw [hG1 _ ?_, Complex.ofReal_zero, mul_zero]
      rw [abs_mul, abs_inv, abs_of_pos ha, le_mul_inv_iff₀ ha, one_mul]
      rw [Finset.mem_Icc, not_and_or] at hm
      rcases hm with hm | hm
      · push Not at hm
        have : (m : ℝ) < -D := by exact_mod_cast hm
        rw [abs_of_neg (by linarith)]; linarith
      · push Not at hm
        have : (D : ℝ) < m := by exact_mod_cast hm
        rw [abs_of_pos (by linarith)]; linarith
  apply Complex.ofReal_injective
  have hC : ∀ δ : ℤ, ((autoCorr χ M δ : ℝ) : ℂ) = ((M : ℂ) ^ 2)⁻¹ *
      ∑ k ∈ range M, ((‖twistCoeff χ M k‖ ^ 2 : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (k * δ / M)) := by
    intro δ
    rw [sum_normSq_twistCoeff_mul_cexp hM δ]
    push_cast
    field_simp
  push_cast
  simp_rw [hC]
  calc ∑ δ ∈ Finset.Icc (-(D : ℤ)) D, ((M : ℂ) ^ 2)⁻¹ *
        (∑ k ∈ range M, ((‖twistCoeff χ M k‖ ^ 2 : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (k * δ / M))) *
        ((shellAutocorr φ (δ * a⁻¹) : ℝ) : ℂ) =
      ∑ k ∈ range M, ((M : ℂ) ^ 2)⁻¹ * ((‖twistCoeff χ M k‖ ^ 2 : ℝ) : ℂ) *
        ∑ δ ∈ Finset.Icc (-(D : ℤ)) D, Complex.exp (2 * Real.pi * Complex.I * (k * δ / M)) *
          ((shellAutocorr φ (δ * a⁻¹) : ℝ) : ℂ) := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact sum_congr rfl fun k _ => sum_congr rfl fun δ _ => by ring
    _ = ∑ k ∈ range M, ((M : ℂ) ^ 2)⁻¹ * ((‖twistCoeff χ M k‖ ^ 2 : ℝ) : ℂ) *
        ((a : ℂ) * (((twistDensity φ ((k : ℝ) / M) a +
          twistDensity φ (1 - (k : ℝ) / M) a : ℝ)) : ℂ)) :=
        sum_congr rfl fun k _ => by rw [hmode k]
    _ = _ := by
        rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hM, twistCoeff_zero hχ, norm_zero]
        simp only [twistPower]
        push_cast
        rw [zero_pow two_ne_zero, mul_zero, zero_mul, zero_add, Finset.mul_sum]
        refine sum_congr rfl fun k _ => ?_
        field_simp

/-- **The energy of a periodic twist is its spectrum**: for a mean-zero `M`-periodic twist and
`1 ≤ c ≤ N/4`, `E_N = 2π Σ_{0<k<M} |χ̂(k)|² (𝒜^{(k/M)}_N + 𝒜^{(1−k/M)}_N) + O(c/N)`. -/
theorem abs_twistEnergy_sub_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {χ : ℕ → ℝ} {M : ℕ} (hχ : MeanZeroTwist χ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 4 * c ≤ N →
      |(∫ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (twistedWeights h χ N) τ‖ ^ 2 / N)) -
        2 * Real.pi * twistAlias φ h χ M c N| ≤ K * c / N := by
  obtain ⟨K, hK0, hK⟩ := periodicEnergy_le hφ hφsupp hh hA hsupp hχ.pos hχ.periodic
  refine ⟨K, hK0, fun c hc N hcN => ?_⟩
  have hc0 : 0 < c := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have e : ∀ n ∈ Icc 1 N, horizonWeights h N n ^ 2 *
      ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊, autoCorr χ M δ * shellAutocorr φ (δ * (c * n / N)⁻¹) =
      ∑ k ∈ Ico 1 M, c / N * twistPower χ M k *
        (h (Real.log n - Real.log N) ^ 2 * twistDensity φ ((k : ℝ) / M) (c * n / N) +
          h (Real.log n - Real.log N) ^ 2 * twistDensity φ (1 - (k : ℝ) / M) (c * n / N)) :=
    fun n hn => by
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
      have ha0 : 0 < c * n / N := by positivity
      have haD : c * n / N ≤ ⌈c⌉₊ := by
        refine le_trans ?_ (Nat.le_ceil c)
        rw [div_le_iff₀ hN0]; exact mul_le_mul_of_nonneg_left hnN hc0.le
      rw [sum_offset_twist_eq hφ hφsupp hχ ha0 haD, Finset.mul_sum, Finset.mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [horizonWeights, div_pow, Real.sq_sqrt hn0.le]
      field_simp
  have hR : 2 * Real.pi * twistAlias φ h χ M c N = ∑ k ∈ Ico 1 M, ∑ n ∈ Icc 1 N,
      2 * Real.pi / c * (c / N * twistPower χ M k *
        (h (Real.log n - Real.log N) ^ 2 * twistDensity φ ((k : ℝ) / M) (c * n / N) +
          h (Real.log n - Real.log N) ^ 2 * twistDensity φ (1 - (k : ℝ) / M) (c * n / N))) := by
    unfold twistAlias densityAlias
    rw [Finset.mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [← mul_add, ← Finset.sum_add_distrib]
    simp only [Finset.mul_sum]
    refine sum_congr rfl fun n _ => ?_
    field_simp
  have hmain : 2 * Real.pi / c * ∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2 *
      ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊, autoCorr χ M δ * shellAutocorr φ (δ * (c * n / N)⁻¹) =
      2 * Real.pi * twistAlias φ h χ M c N := by
    rw [sum_congr rfl e, Finset.sum_comm, hR]
    simp only [Finset.mul_sum]
  rw [← hmain]
  exact hK c hc N hcN

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
