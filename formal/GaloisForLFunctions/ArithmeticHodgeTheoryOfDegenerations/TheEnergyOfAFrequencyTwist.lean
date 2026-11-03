import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheFrequencyTwistIsQuietBelowItsResonance
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheRescaledLimitOfACurveIsTheHurwitzFormOfItsAngles

/-!
# The energy of a frequency twist

The energy law of a periodic twist organizes the block energy by offsets `δ`, each contributing
the autocorrelation `C_χ(δ)` by periodic equidistribution (`periodicEnergy_le`). For the twist
`cos(2πnα)` of a real frequency the products `χ(n)χ(n + δ) = ½cos(2πδα) + ½cos(2π(2n + δ)α)` split
into the autocorrelation `½cos(2πδα)` and an oscillation whose partial sums are bounded by
`1/|sin 2πα|`; summation by parts replaces periodicity.

* **Oscillations against Lipschitz profiles** (`abs_sum_cos_mul_le`):
  `|Σ_{n ≤ N} cos(2πnβ + θ) f(n/N)| ≤ (|f(1)| + L)/|sin πβ|`.
* **The offset sum is the shifted spectrum** (`sum_offset_freq_eq`):
  `Σ_{|δ| ≤ D} ½cos(2πδα) G(δ/a) = (a/2)(D_u(a) + D_{1−u}(a))`, `u = {α}`, by Poisson summation on
  the shifted lattice `ℤ + α`.
* **The energy law** (`freqEnergy_le`): for `2α ∉ ℤ` and `1 ≤ c ≤ N/4` the block energy of the
  window twisted by `cos(2πnα)` is `2π · ½(𝒜^{(u)}_N(c) + 𝒜^{(1−u)}_N(c)) + O(c/N)`, the same form as
  the periodic energy law at the two modes `±α`.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ h : ℝ → ℝ} {A : ℝ}

/-- **Oscillations equidistribute against Lipschitz profiles**: for `sin πβ ≠ 0`,
`|Σ_{n ≤ N} cos(2πnβ + θ) f(n/N)| ≤ (|f(1)| + L)/|sin πβ|`. -/
theorem abs_sum_cos_mul_le {β : ℝ} (hβ : Real.sin (Real.pi * β) ≠ 0) (θ : ℝ) {f : ℝ → ℝ}
    {L : ℝ} (hL : ∀ x y, |f x - f y| ≤ L * |x - y|) {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Icc 1 N, Real.cos (2 * Real.pi * n * β + θ) * f (n / N)| ≤
      (|f 1| + L) / |Real.sin (Real.pi * β)| := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 ≤ L := by
    have := hL 1 0; norm_num at this; linarith [abs_nonneg (f 1 - f 0)]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  set e : ℕ → ℂ := fun m => Complex.exp (((2 * Real.pi * ((m + 1 : ℕ) : ℝ) * β + θ : ℝ) : ℂ) *
    Complex.I) with he
  set a : ℕ → ℝ := fun m => f (((m + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ)) with ha
  have hre : ∑ n ∈ Icc 1 (M + 1), Real.cos (2 * Real.pi * n * β + θ) * f (n / ((M + 1 : ℕ) : ℝ)) =
      (∑ m ∈ range (M + 1), (a m : ℂ) * e m).re := by
    rw [show Icc 1 (M + 1) = Finset.Ico 1 (M + 2) by ext; simp; omega, Finset.sum_Ico_eq_sum_range,
      show M + 2 - 1 = M + 1 by omega, Complex.re_sum]
    refine sum_congr rfl fun m _ => ?_
    simp only [ha, he]
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, add_comm 1 m]
    push_cast
    ring
  have hpart : ∀ k ≤ M, ‖∑ m ∈ range (k + 1), e m‖ ≤ 1 / |Real.sin (Real.pi * β)| := by
    intro k _
    have hb := RHTower.Sieve.norm_sum_exp_le (cexp_two_pi_ne_one hβ) (k + 1)
    rw [show 2 * Real.pi * β / 2 = Real.pi * β by ring] at hb
    have hfac : ∑ m ∈ range (k + 1), e m = Complex.exp (((2 * Real.pi * β + θ : ℝ) : ℂ) *
        Complex.I) * ∑ m ∈ range (k + 1), Complex.exp (((m * (2 * Real.pi * β) : ℝ) : ℂ) *
          Complex.I) := by
      rw [Finset.mul_sum]
      refine sum_congr rfl fun m _ => ?_
      simp only [he]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact hb
  have hab := norm_sum_mul_le_of_partial a e M hpart
  have hvar : ∑ m ∈ range M, |a (m + 1) - a m| ≤ L := by
    have hcell : ∀ m ∈ range M, |a (m + 1) - a m| ≤ L / ((M + 1 : ℕ) : ℝ) := fun m _ => by
      simp only [ha]
      refine (hL _ _).trans (le_of_eq ?_)
      rw [← sub_div]
      push_cast
      rw [show (m : ℝ) + 1 + 1 - (m + 1) = 1 by ring, abs_of_pos (by positivity)]
      ring
    refine (Finset.sum_le_sum hcell).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_assoc', div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  have haM : a M = f 1 := by
    simp only [ha]
    rw [div_self (by positivity)]
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans (hab.trans ?_)
  rw [haM, one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right (by linarith) (abs_nonneg _)

/-- `χ(n)χ(n + δ) = ½cos(2πδα) + ½cos(2π(2n + δ)α)`. -/
theorem cos_mul_cos_shift (α : ℝ) (n δ : ℝ) :
    Real.cos (2 * Real.pi * n * α) * Real.cos (2 * Real.pi * (n + δ) * α) =
      Real.cos (2 * Real.pi * δ * α) / 2 +
        Real.cos (2 * Real.pi * n * (2 * α) + 2 * Real.pi * δ * α) / 2 := by
  have e1 : 2 * Real.pi * δ * α = -(2 * Real.pi * n * α - 2 * Real.pi * (n + δ) * α) := by ring
  have e2 : 2 * Real.pi * n * (2 * α) + 2 * Real.pi * δ * α =
      2 * Real.pi * n * α + 2 * Real.pi * (n + δ) * α := by ring
  rw [e2, e1, Real.cos_neg, Real.cos_add, Real.cos_sub]
  ring

/-- **The offset sum of a frequency twist is its shifted spectrum**: for `a ≤ D`,
`Σ_{|δ| ≤ D} ½cos(2πδα) G(δ/a) = (a/2)(D_u(a) + D_{1−u}(a))`, `u = {α}`. -/
theorem sum_offset_freq_eq (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (α : ℝ) {a : ℝ} (ha : 0 < a) {D : ℕ} (haD : a ≤ D) :
    ∑ δ ∈ Finset.Icc (-(D : ℤ)) D, Real.cos (2 * Real.pi * δ * α) / 2 *
        shellAutocorr φ (δ * a⁻¹) =
      a / 2 * (twistDensity φ (Int.fract α) a + twistDensity φ (1 - Int.fract α) a) := by
  have hG1 : ∀ t, 1 ≤ |t| → shellAutocorr φ t = 0 := fun t ht =>
    shellAutocorr_eq_zero_of_one_le_abs hφ hφsupp ht
  have hP := hasSum_shellSpectrum_shift hφ hφsupp ha α
  have hS := tsum_shellSpectrum_shift_eq_fract hφ hφsupp ha α
  -- the full lattice sum of the modulated autocorrelation
  have hfull : ∑ δ ∈ Finset.Icc (-(D : ℤ)) D, Complex.exp (2 * Real.pi * Complex.I * (α * δ)) *
      ((shellAutocorr φ (δ * a⁻¹) : ℝ) : ℂ) =
      ((a * (twistDensity φ (Int.fract α) a + twistDensity φ (1 - Int.fract α) a) : ℝ) : ℂ) := by
    have h1 := hP.tsum_eq
    rw [← Complex.ofReal_tsum, hS] at h1
    rw [tsum_eq_sum (s := Finset.Icc (-(D : ℤ)) D)] at h1
    · have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
      rw [Complex.ofReal_mul, h1, ← mul_assoc, Complex.ofReal_inv, mul_inv_cancel₀ ha0, one_mul]
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
  have hre := congrArg Complex.re hfull
  rw [Complex.re_sum, Complex.ofReal_re] at hre
  have e : ∀ δ : ℤ, (Complex.exp (2 * Real.pi * Complex.I * (α * δ)) *
      ((shellAutocorr φ (δ * a⁻¹) : ℝ) : ℂ)).re =
      Real.cos (2 * Real.pi * δ * α) * shellAutocorr φ (δ * a⁻¹) := fun δ => by
    rw [Complex.re_mul_ofReal, show 2 * Real.pi * Complex.I * (α * δ) =
      ((2 * Real.pi * δ * α : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_ofReal_mul_I_re]
  simp_rw [e] at hre
  rw [show ∑ δ ∈ Finset.Icc (-(D : ℤ)) D, Real.cos (2 * Real.pi * δ * α) / 2 *
      shellAutocorr φ (δ * a⁻¹) = (∑ δ ∈ Finset.Icc (-(D : ℤ)) D,
        Real.cos (2 * Real.pi * δ * α) * shellAutocorr φ (δ * a⁻¹)) / 2 by
      rw [Finset.sum_div]; exact sum_congr rfl fun δ _ => by ring, hre]
  ring

/-- The frequency twist on the integers, `z ↦ cos(2πzα)`. -/
def freqTwistZ (α : ℝ) (z : ℤ) : ℝ := Real.cos (2 * Real.pi * z * α)

theorem freqTwistZ_natCast (α : ℝ) (n : ℕ) : freqTwistZ α n = freqTwist α n := by
  simp [freqTwistZ, freqTwist]

/-- **The offsets of a frequency twist equidistribute**: `Σ_n χ(n) y_n² Σ_δ χ(n+δ) G(δ/a_n)` is
`Σ_n y_n² Σ_δ ½cos(2πδα) G(δ/a_n)` up to `O(c/N)`. -/
theorem abs_offsetSum_freq_sub_le {G : ℝ → ℝ} {BG LG : ℝ} (hG : ∀ t, |G t| ≤ BG)
    (hGL : ∀ s t, |G s - G t| ≤ LG * |s - t|) (hBG : 0 ≤ BG) {Bu Lu : ℝ}
    (hBu : ∀ x, |invWindow h x| ≤ Bu) (hLu : ∀ x y, |invWindow h x - invWindow h y| ≤ Lu * |x - y|)
    (hu0 : ∀ x, x < Real.exp (-A) → invWindow h x = 0) (hu1 : invWindow h 1 = 0)
    {α : ℝ} (hα2 : Real.sin (Real.pi * (2 * α)) ≠ 0) {c : ℝ} (hc : 1 ≤ c)
    {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Icc 1 N, freqTwist α n * horizonWeights h N n ^ 2 * ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊,
        freqTwistZ α (n + δ) * G (δ * (c * n / N)⁻¹) -
      ∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2 * ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊,
        Real.cos (2 * Real.pi * δ * α) / 2 * G (δ * (c * n / N)⁻¹)| ≤
      5 * c * ((Lu * BG + Bu * (2 * LG * Real.exp A ^ 2)) /
        (2 * |Real.sin (Real.pi * (2 * α))|)) / N := by
  have hc0 : 0 < c := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hBu0 : 0 ≤ Bu := (abs_nonneg _).trans (hBu 0)
  have hLu0 : 0 ≤ Lu := by
    have := hLu 1 0; norm_num at this; linarith [abs_nonneg (invWindow h 1 - invWindow h 0)]
  have hLG0 : 0 ≤ LG := by
    have := hGL 1 0; norm_num at this; linarith [abs_nonneg (G 1 - G 0)]
  obtain ⟨D, hD⟩ : ∃ D, D = ⌈c⌉₊ := ⟨_, rfl⟩
  rw [← hD]
  have hDc : (D : ℝ) ≤ 2 * c := by
    rw [hD]; linarith [Nat.ceil_lt_add_one hc0.le]
  obtain ⟨Lf, hLf⟩ : ∃ Lf, Lf = Lu * BG + Bu * (2 * LG * Real.exp A ^ 2) := ⟨_, rfl⟩
  rw [← hLf]
  have hLf0 : 0 ≤ Lf := by rw [hLf]; positivity
  set f : ℤ → ℝ → ℝ := fun δ x => invWindow h x * G (δ * (c * x)⁻¹) with hf
  set ψ : ℤ → ℕ → ℝ := fun δ n => freqTwist α n * freqTwistZ α (n + δ) with hψ
  set C : ℤ → ℝ := fun δ => Real.cos (2 * Real.pi * δ * α) / 2 with hCdef
  have hrw1 : ∀ n ∈ Icc 1 N, freqTwist α n * horizonWeights h N n ^ 2 *
      ∑ δ ∈ Finset.Icc (-(D : ℤ)) D,
      freqTwistZ α (n + δ) * G (δ * (c * n / N)⁻¹) =
      ∑ δ ∈ Finset.Icc (-(D : ℤ)) D, (N : ℝ)⁻¹ * (ψ δ n * f δ (n / N)) := fun n hn => by
    rw [horizonWeights_sq_eq h hN (Finset.mem_Icc.mp hn).1, mul_sum]
    refine sum_congr rfl fun δ _ => ?_
    simp only [hψ, hf]
    rw [show c * n / N = c * (n / N) by ring]
    ring
  have hrw2 : ∀ n ∈ Icc 1 N, horizonWeights h N n ^ 2 * ∑ δ ∈ Finset.Icc (-(D : ℤ)) D,
      Real.cos (2 * Real.pi * δ * α) / 2 * G (δ * (c * n / N)⁻¹) =
      ∑ δ ∈ Finset.Icc (-(D : ℤ)) D, (N : ℝ)⁻¹ * (C δ * f δ (n / N)) := fun n hn => by
    rw [horizonWeights_sq_eq h hN (Finset.mem_Icc.mp hn).1, mul_sum]
    refine sum_congr rfl fun δ _ => ?_
    simp only [hf, hCdef]
    rw [show c * n / N = c * (n / N) by ring]
    ring
  rw [sum_congr rfl hrw1, sum_congr rfl hrw2, Finset.sum_comm, Finset.sum_comm (s := Icc 1 N),
    ← sum_sub_distrib]
  have hδ : ∀ δ ∈ Finset.Icc (-(D : ℤ)) D,
      |∑ n ∈ Icc 1 N, (N : ℝ)⁻¹ * (ψ δ n * f δ (n / N)) -
        ∑ n ∈ Icc 1 N, (N : ℝ)⁻¹ * (C δ * f δ (n / N))| ≤
      (N : ℝ)⁻¹ * (Lf / (2 * |Real.sin (Real.pi * (2 * α))|)) := fun δ hδ => by
    have hδ' : |(δ : ℝ)| ≤ 2 * c := by
      have h1 := Finset.mem_Icc.mp hδ
      have : |(δ : ℝ)| ≤ D := by
        rw [abs_le]; constructor
        · have : ((-(D : ℤ) : ℤ) : ℝ) ≤ (δ : ℝ) := by exact_mod_cast h1.1
          push_cast at this; linarith
        · exact_mod_cast h1.2
      linarith
    have hfL : ∀ x y, |f δ x - f δ y| ≤ Lf * |x - y| := fun x y => by
      rw [hLf]; exact abs_offsetProfile_sub_le hG hGL hBG hBu hLu hu0 hc0 hδ' x y
    have hf1 : f δ 1 = 0 := by simp only [hf]; rw [hu1, zero_mul]
    have hosc := abs_sum_cos_mul_le hα2 (2 * Real.pi * δ * α) hfL hN
    rw [hf1, abs_zero, zero_add] at hosc
    have hsplit : ∑ n ∈ Icc 1 N, (N : ℝ)⁻¹ * (ψ δ n * f δ (n / N)) -
        ∑ n ∈ Icc 1 N, (N : ℝ)⁻¹ * (C δ * f δ (n / N)) =
        (N : ℝ)⁻¹ * ((∑ n ∈ Icc 1 N, Real.cos (2 * Real.pi * n * (2 * α) + 2 * Real.pi * δ * α) *
          f δ (n / N)) / 2) := by
      rw [← mul_sum, ← mul_sum, ← mul_sub, ← sum_sub_distrib, Finset.sum_div]
      congr 1
      refine sum_congr rfl fun n _ => ?_
      simp only [hψ, hCdef, freqTwist, freqTwistZ]
      push_cast
      rw [cos_mul_cos_shift]
      ring
    rw [hsplit, abs_mul, abs_of_pos (inv_pos.mpr hN0), abs_div, abs_two]
    refine mul_le_mul_of_nonneg_left ?_ (inv_pos.mpr hN0).le
    rw [div_le_div_iff₀ (by norm_num) (by positivity : (0 : ℝ) < 2 * |Real.sin (Real.pi * (2 * α))|)]
    have hs0 : 0 < |Real.sin (Real.pi * (2 * α))| := abs_pos.mpr hα2
    rw [le_div_iff₀ hs0] at hosc
    nlinarith
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hδ).trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.Icc (-(D : ℤ)) D).card : ℝ) ≤ 5 * c := by
    rw [Int.card_Icc]
    have : ((D : ℤ) + 1 - -(D : ℤ)).toNat = 2 * D + 1 := by omega
    rw [this]
    push_cast
    linarith [Nat.ceil_lt_add_one hc0.le, hD ▸ (Nat.ceil_lt_add_one hc0.le)]
  calc ((Finset.Icc (-(D : ℤ)) D).card : ℝ) * ((N : ℝ)⁻¹ * (Lf / (2 * |Real.sin (Real.pi * (2 * α))|)))
      ≤ 5 * c * ((N : ℝ)⁻¹ * (Lf / (2 * |Real.sin (Real.pi * (2 * α))|))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 5 * c * (Lf / (2 * |Real.sin (Real.pi * (2 * α))|)) / N := by ring

/-- **The energy of a frequency twist**: for `2α ∉ ℤ` and `1 ≤ c ≤ N/4`,
`E_N = (2π/c) Σ_n y_n² Σ_{|δ| ≤ ⌈c⌉} ½cos(2πδα) G(δ/a_n) + O(c/N)`. -/
theorem freqEnergy_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {α : ℝ} (hα2 : Real.sin (Real.pi * (2 * α)) ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 4 * c ≤ N →
      |(∫ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (twistedWeights h (freqTwist α) N) τ‖ ^ 2 / N)) -
        2 * Real.pi / c * ∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2 *
          ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊,
            Real.cos (2 * Real.pi * δ * α) / 2 * shellAutocorr φ (δ * (c * n / N)⁻¹)| ≤
        K * c / N := by
  obtain ⟨Bk, Lk, hk, hkL⟩ := exists_bound_lipschitz (contDiff_taperedProfile hh)
    (A := A) fun y hy => taperedProfile_eq_zero hsupp hy
  have hG2 := contDiff_shellAutocorr hφ hφsupp
  have hG1 : ∀ t, 1 ≤ |t| → shellAutocorr φ t = 0 := fun t ht =>
    shellAutocorr_eq_zero_of_one_le_abs hφ hφsupp ht
  have hGc : HasCompactSupport (shellAutocorr φ) :=
    HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) fun t ht => by
      refine hG1 t ?_
      by_contra hlt
      exact ht (abs_le.mp (not_le.mp hlt).le)
  obtain ⟨BG, hBG⟩ := hGc.exists_bound_of_continuous hG2.continuous
  obtain ⟨LG, hLG⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hGc hG2 (by norm_num)
  have hGb : ∀ t, |shellAutocorr φ t| ≤ |BG| := fun t =>
    (by simpa [Real.norm_eq_abs] using hBG t : |shellAutocorr φ t| ≤ BG).trans (le_abs_self _)
  have hGL : ∀ s t, |shellAutocorr φ s - shellAutocorr φ t| ≤ (LG : ℝ) * |s - t| := fun s t => by
    simpa [Real.dist_eq] using hLG.dist_le_mul s t
  have hkb : ∀ y, |taperedProfile h y| ≤ |Bk| := fun y => (hk y).trans (le_abs_self _)
  have hkL' : ∀ u v, |taperedProfile h u - taperedProfile h v| ≤ |Lk| * |u - v| := fun u v =>
    (hkL u v).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _))
  have hk0 : ∀ y, 0 < y → taperedProfile h y = 0 := fun y hy =>
    taperedProfile_eq_zero hsupp fun hm => by linarith [hm.2]
  obtain ⟨Bu, Lu, hBu0, hLu0, hBu, hLu, hu0⟩ := exists_invWindow_bounds hh hA hsupp
  have hu1 : invWindow h 1 = 0 := by
    obtain ⟨-, Lh0, -, hLh0⟩ := exists_bound_lipschitz hh hsupp
    rw [invWindow, sqWindow, if_pos one_pos, Real.log_one, horizon_zero_at_zero hsupp hLh0]
    simp
  obtain ⟨Mχ, hMχ⟩ : ∃ Mχ : ℝ, Mχ = 1 := ⟨_, rfl⟩
  have hMχ0 : 0 ≤ Mχ := by rw [hMχ]; norm_num
  have hχb : ∀ n, |freqTwist α n| ≤ Mχ := fun n => hMχ ▸ abs_freqTwist_le α n
  have hχZb : ∀ z, |freqTwistZ α z| ≤ Mχ := fun z => hMχ ▸ Real.abs_cos_le_one _
  obtain ⟨X, hX⟩ : ∃ X, X = 5 * (|Lk| * |BG| + 8 * |Bk| * (LG : ℝ)) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 5 * ((Lu * |BG| + Bu * (2 * (LG : ℝ) * Real.exp A ^ 2)) /
      (2 * |Real.sin (Real.pi * (2 * α))|)) := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  refine ⟨2 * Real.pi * (Mχ ^ 2 * |Bk| * X) + 2 * Real.pi * Q, by positivity,
    fun c hc N hcN => ?_⟩
  have hc0 : 0 < c := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hN : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hxw : ∀ m, 1 ≤ m → horizonWeights h N m =
      taperedProfile h (Real.log m - Real.log N) / Real.sqrt N := fun m hm =>
    horizonWeights_eq_tapered h hN hm
  rw [atomEnergy_eq hφ hφsupp _ hc0 hN]
  set G := shellAutocorr φ with hGdef
  set tw := twistedWeights h (freqTwist α) N with htw
  set R : ℕ → ℝ := fun n => ∑ m ∈ Icc 1 N, tw m * G (N * (Real.log m - Real.log n) / c) with hR
  set L : ℕ → ℝ := fun n => ∑ m ∈ Icc 1 (2 * N), freqTwistZ α m *
    G (((m : ℝ) - n) * (c * n / N)⁻¹) with hL
  have hswap : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, tw m * tw n *
      G (N * (Real.log m - Real.log n) / c) = ∑ n ∈ Icc 1 N, tw n * R n := by
    rw [Finset.sum_comm]
    refine sum_congr rfl fun n _ => ?_
    simp only [hR]
    rw [mul_sum]
    exact sum_congr rfl fun m _ => by ring
  rw [hswap]
  -- the rows
  set ε := X * c ^ 2 / (N * Real.sqrt N) with hε
  have hrows : |∑ n ∈ Icc 1 N, tw n * R n - ∑ n ∈ Icc 1 N, tw n * (horizonWeights h N n * L n)| ≤
      N * (Mχ * |Bk| / Real.sqrt N * (Mχ * ε)) :=
    abs_sum_mul_sub_sum_le fun n hn => by
      have hn1 := (Finset.mem_Icc.mp hn).1
      have hnN := (Finset.mem_Icc.mp hn).2
      have hr := abs_twistRow_sub_le hkb hkL' hGb hGL hG1 hk0 (abs_nonneg _) (abs_nonneg _)
        (NNReal.coe_nonneg _) (abs_nonneg _) hχZb hc hcN hn1 hnN
      have hRn : R n = ∑ m ∈ Icc 1 N, freqTwistZ α m *
          (taperedProfile h (Real.log m - Real.log N) / Real.sqrt N) *
            G (N * (Real.log m - Real.log n) / c) := by
        simp only [hR, htw]
        refine sum_congr rfl fun m hm => ?_
        rw [twistedWeights, hxw m (Finset.mem_Icc.mp hm).1, freqTwistZ_natCast]
        ring
      rw [← mul_sub, abs_mul]
      refine mul_le_mul ?_ ?_ (abs_nonneg _) (by positivity)
      · simp only [htw]
        rw [twistedWeights, abs_mul, hxw n hn1, abs_div, abs_of_pos hsN, mul_comm, mul_div_assoc]
        exact mul_le_mul (hχb n) (div_le_div_of_nonneg_right (hkb _) hsN.le)
          (by positivity) hMχ0
      · rw [hRn, hxw n hn1]
        refine hr.trans (le_of_eq ?_)
        rw [hε, hX]
  -- the offsets
  have hoff : ∑ n ∈ Icc 1 N, tw n * (horizonWeights h N n * L n) =
      ∑ n ∈ Icc 1 N, freqTwist α n * horizonWeights h N n ^ 2 *
        ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊, freqTwistZ α (n + δ) * G (δ * (c * n / N)⁻¹) := by
    refine sum_congr rfl fun n hn => ?_
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have ha0 : 0 < c * n / N := by positivity
    have hac : c * n / N ≤ c := by
      rw [div_le_iff₀ hN0]; exact mul_le_mul_of_nonneg_left hnN hc0.le
    have han : 4 * (c * n / N) ≤ n := by
      rw [show 4 * (c * n / N) = 4 * c / N * n by ring]
      exact mul_le_of_le_one_left hn0.le ((div_le_one hN0).mpr hcN)
    have hDN : n + ⌈c⌉₊ ≤ 2 * N := by
      have : ⌈c⌉₊ ≤ N := Nat.ceil_le.mpr (by linarith)
      have : n ≤ N := (Finset.mem_Icc.mp hn).2
      omega
    have hL' : L n = ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊,
        freqTwistZ α (n + δ) * G (δ * (c * n / N)⁻¹) :=
      sum_offset_eq hG1 (freqTwistZ α) ha0 han (hac.trans (Nat.le_ceil c)) hDN
    rw [hL']
    simp only [htw]
    rw [twistedWeights]
    ring
  have hoffeq := abs_offsetSum_freq_sub_le hGb hGL (abs_nonneg _) hBu hLu hu0 hu1 hα2 hc hN
    (G := G)
  rw [← hoff] at hoffeq
  have htot : |2 * Real.pi / c * ∑ n ∈ Icc 1 N, tw n * R n -
      2 * Real.pi / c * ∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2 *
        ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊, Real.cos (2 * Real.pi * δ * α) / 2 *
          G (δ * (c * n / N)⁻¹)| ≤
      2 * Real.pi / c * (N * (Mχ * |Bk| / Real.sqrt N * (Mχ * ε)) +
        5 * c * ((Lu * |BG| + Bu * (2 * (LG : ℝ) * Real.exp A ^ 2)) /
          (2 * |Real.sin (Real.pi * (2 * α))|)) / N) := by
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi / c)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := abs_sub_le (∑ n ∈ Icc 1 N, tw n * R n)
      (∑ n ∈ Icc 1 N, tw n * (horizonWeights h N n * L n))
      (∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2 *
        ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊, Real.cos (2 * Real.pi * δ * α) / 2 *
          G (δ * (c * n / N)⁻¹))
    linarith
  refine htot.trans ?_
  rw [hε]
  have e1 : 2 * Real.pi / c * (N * (Mχ * |Bk| / Real.sqrt N * (Mχ * (X * c ^ 2 /
      (N * Real.sqrt N))))) = 2 * Real.pi * (Mχ ^ 2 * |Bk| * X) * c / N := by
    field_simp
    rw [Real.sq_sqrt hN0.le]
    ring
  have e2 : 2 * Real.pi / c * (5 * c * ((Lu * |BG| + Bu * (2 * (LG : ℝ) * Real.exp A ^ 2)) /
      (2 * |Real.sin (Real.pi * (2 * α))|)) / N) = 2 * Real.pi * Q / N := by
    rw [hQ]; field_simp
  rw [mul_add, e1, e2]
  have hQc : 2 * Real.pi * Q / N ≤ 2 * Real.pi * Q * c / N := by
    rw [div_le_div_iff_of_pos_right hN0]
    exact le_mul_of_one_le_right (by positivity) hc
  have : (2 * Real.pi * (Mχ ^ 2 * |Bk| * X) + 2 * Real.pi * Q) * c / N =
      2 * Real.pi * (Mχ ^ 2 * |Bk| * X) * c / N + 2 * Real.pi * Q * c / N := by ring
  linarith

/-- The spectral aliasing of a frequency twist, `½(𝒜^{(u)}_N(c) + 𝒜^{(1−u)}_N(c))`, `u = {α}`. -/
def freqAlias (φ h : ℝ → ℝ) (α c : ℝ) (N : ℕ) : ℝ :=
  (densityAlias (twistDensity φ (Int.fract α)) h c N +
    densityAlias (twistDensity φ (1 - Int.fract α)) h c N) / 2

/-- **The energy of a frequency twist is its shifted spectrum**: for `2α ∉ ℤ` and `1 ≤ c ≤ N/4`,
`E_N = 2π · ½(𝒜^{(u)}_N(c) + 𝒜^{(1−u)}_N(c)) + O(c/N)`. -/
theorem abs_freqEnergy_sub_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {α : ℝ} (hα2 : Real.sin (Real.pi * (2 * α)) ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 4 * c ≤ N →
      |(∫ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (twistedWeights h (freqTwist α) N) τ‖ ^ 2 / N)) -
        2 * Real.pi * freqAlias φ h α c N| ≤ K * c / N := by
  obtain ⟨K, hK0, hK⟩ := freqEnergy_le hφ hφsupp hh hA hsupp hα2
  refine ⟨K, hK0, fun c hc N hcN => ?_⟩
  have hc0 : 0 < c := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have e : ∀ n ∈ Icc 1 N, horizonWeights h N n ^ 2 *
      ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊, Real.cos (2 * Real.pi * δ * α) / 2 *
        shellAutocorr φ (δ * (c * n / N)⁻¹) =
      c / N * (h (Real.log n - Real.log N) ^ 2 *
        (twistDensity φ (Int.fract α) (c * n / N) +
          twistDensity φ (1 - Int.fract α) (c * n / N))) / 2 := fun n hn => by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have ha0 : 0 < c * n / N := by positivity
    have haD : c * n / N ≤ ⌈c⌉₊ := by
      refine le_trans ?_ (Nat.le_ceil c)
      rw [div_le_iff₀ hN0]; exact mul_le_mul_of_nonneg_left hnN hc0.le
    rw [sum_offset_freq_eq hφ hφsupp α ha0 haD, horizonWeights, div_pow, Real.sq_sqrt hn0.le]
    field_simp
  have hmain : 2 * Real.pi / c * ∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2 *
      ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊, Real.cos (2 * Real.pi * δ * α) / 2 *
        shellAutocorr φ (δ * (c * n / N)⁻¹) = 2 * Real.pi * freqAlias φ h α c N := by
    rw [sum_congr rfl e]
    unfold freqAlias densityAlias
    rw [← mul_add, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, Finset.sum_div,
      Finset.mul_sum]
    refine sum_congr rfl fun n _ => ?_
    field_simp
  rw [← hmain]
  exact hK c hc N hcN

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
