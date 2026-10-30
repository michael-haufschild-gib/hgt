import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheNonRatioPrimeRowsSplitIntoDownwardAndUpward
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheWeightedAffinePrimeShellsHaveTheirSignedMean
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheNearGammaAndDownwardPrimeRowsCancel
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.WeightedAffinePrimeWindowsAreUniform
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeEnergyHasFiniteRamanujanCoordinates

/-!
# The upward prime windows carry the shell correction

On a normalized Ramanujan mode of conductor `m`, the upward non-ratio prime row at overlap `c`
is, row by row, the affine reciprocal-shell reading of the mode,

`√(n log N) √φ(m) · Up_n / G₀ ≈ (1/M) Σ_h [shell(n, h) + shell(n, (m-1)h)]`,

with an error `O(1/N)` from linearizing `log(1 ± h/kn)` and `√(kn/j)`, plus the `O(log X / X)`
boundary terms where `kn` lies within a bounded distance of `N`, `X = N/n`. The weighted affine
prime theorem identifies the shell reading with `c_m(n) κ_m(c)` uniformly once `X` is large.
Rows with bounded `X` have bounded normalized size and harmonic mass `O(1/log N)`. Hence the
upward rows act as the shell correction `κ_m(c)` in `ℓ²` norm.
-/

noncomputable section

open MeasureTheory Finset Filter Topology
open scoped Real

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis BezoutValuationIncidence CompletedShell
  CriticalArithmeticCorrelationTheory
open _root_.RHTower (vonMangoldtAtom)

local notation "Λ" => ArithmeticFunction.vonMangoldt

section Profile

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
include hφ hsupp

/-- The autocorrelation is bounded by the profile mass. -/
theorem abs_shellAutocorr_le (x : ℝ) : |shellAutocorr φ x| ≤ ∫ u, φ u ^ 2 := by
  have hc : Continuous φ := hφ.continuous
  have hcs : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hsupp u hu
  have hsq : Integrable fun u => φ u ^ 2 := by
    have h : Integrable (fun u => φ u * φ u) :=
      (hc.mul hc).integrable_of_hasCompactSupport hcs.mul_right
    simpa only [sq] using h
  have hsq' : Integrable fun u => φ (u + x) ^ 2 := hsq.comp_add_right x
  have hprod : Integrable fun u => φ u * φ (u + x) :=
    (hc.mul (hc.comp (continuous_add_const x))).integrable_of_hasCompactSupport hcs.mul_right
  change |∫ u, φ u * φ (u + x)| ≤ _
  have htr : (∫ u, φ (u + x) ^ 2) = ∫ u, φ u ^ 2 := integral_add_right_eq_self (fun u => φ u ^ 2) x
  have hpt : ∀ u, |φ u * φ (u + x)| ≤ (φ u ^ 2 + φ (u + x) ^ 2) / 2 := fun u => by
    rw [abs_mul]
    have h := two_mul_le_add_sq |φ u| |φ (u + x)|
    rw [sq_abs, sq_abs] at h
    linarith
  calc |∫ u, φ u * φ (u + x)| ≤ ∫ u, |φ u * φ (u + x)| := abs_integral_le_integral_abs
    _ ≤ ∫ u, (φ u ^ 2 + φ (u + x) ^ 2) / 2 :=
        integral_mono hprod.abs ((hsq.add hsq').div_const 2) hpt
    _ = ∫ u, φ u ^ 2 := by
        rw [integral_div, integral_add hsq hsq', htr]
        ring

/-- The autocorrelation is Lipschitz. -/
theorem exists_shellAutocorr_lipschitz :
    ∃ ℓ : ℝ, 0 ≤ ℓ ∧ ∀ x y : ℝ, |shellAutocorr φ x - shellAutocorr φ y| ≤ ℓ * |x - y| := by
  have hcs : HasCompactSupport (shellAutocorr φ) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) fun x hx => ?_
    apply shellAutocorr_eq_zero_of_one_le_abs hφ hsupp
    by_contra h
    push Not at h
    exact hx ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcs
    (contDiff_shellAutocorr hφ hsupp) (by norm_num)
  refine ⟨C, C.2, fun x y => ?_⟩
  have h := hC.dist_le_mul x y
  simpa only [Real.dist_eq] using h

end Profile

/-! ### The two log-linearizations -/

/-- Upward shift: `|log(1+δ) - δ| ≤ δ²` for `δ ≥ 0`. -/
theorem abs_log_one_add_sub_le {δ : ℝ} (hδ : 0 ≤ δ) : |Real.log (1 + δ) - δ| ≤ δ ^ 2 := by
  have h1 : Real.log (1 + δ) ≤ δ := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + δ); linarith
  have h2 : δ / (1 + δ) ≤ Real.log (1 + δ) := by
    have := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < 1 + δ)
    have hne : 1 + δ ≠ 0 := by linarith
    have he : 1 - (1 + δ)⁻¹ = δ / (1 + δ) := by field_simp; ring
    linarith
  have h3 : δ - δ ^ 2 ≤ δ / (1 + δ) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [sq_nonneg δ, mul_nonneg hδ (sq_nonneg δ)]
  rw [abs_le]
  constructor <;> nlinarith

/-- Downward shift: `|-log(1-δ) - δ| ≤ 2δ²` for `δ ≤ 1/2`. -/
theorem abs_neg_log_one_sub_sub_le {δ : ℝ} (hδ2 : δ ≤ 1 / 2) :
    |-Real.log (1 - δ) - δ| ≤ 2 * δ ^ 2 := by
  have h1 : Real.log (1 - δ) ≤ -δ := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 - δ); linarith
  have h2 : -δ / (1 - δ) ≤ Real.log (1 - δ) := by
    have := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < 1 - δ)
    have hne : 1 - δ ≠ 0 := by linarith
    have he : 1 - (1 - δ)⁻¹ = -δ / (1 - δ) := by field_simp; ring
    linarith
  have h3 : -δ - 2 * δ ^ 2 ≤ -δ / (1 - δ) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [mul_nonneg (sq_nonneg δ) (by linarith : (0 : ℝ) ≤ 1 - 2 * δ)]
  rw [abs_le]
  constructor <;> nlinarith

/-! ### The row on a Ramanujan mode -/

/-- The normalized pair term of the upward row on the mode of conductor `m`. -/
def upwardModePair (φ : ℝ → ℝ) (c : ℝ) (N m n k j : ℕ) : ℝ :=
  vonMangoldtAtom k * (Real.sqrt n / Real.sqrt j) * ramanujanLagCoefficient m j *
    (shellAutocorr φ (|Real.log k - (Real.log j - Real.log n)| * N / c) / ∫ u, φ u ^ 2)

/-- Prime powers beyond this cutoff cannot reach the horizon. -/
def upwardRowCutoff (c : ℝ) (N : ℕ) : ℕ := ⌈(N : ℝ) * Real.exp c⌉₊ + 1

/-- The upward row on the mode of conductor `m`, in the scale `√(n log N) √φ(m)`. -/
def upwardModeRow (φ : ℝ → ℝ) (c : ℝ) (N m n : ℕ) : ℝ :=
  ∑ k ∈ range (upwardRowCutoff c N), ∑ j ∈ Icc 1 N,
    if j = k * n then 0 else upwardModePair φ c N m n k j

theorem primeHorizonExtension_normalizedRamanujan {m N j : ℕ} (hj : j ∈ Icc 1 N) :
    primeHorizonExtension (normalizedRamanujanHorizonVector m N) j =
      (Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile m j := by
  rw [primeHorizonExtension, dif_pos hj]
  rfl

theorem primeHorizonExtension_normalizedRamanujan_of_not {m N j : ℕ} (hj : j ∉ Icc 1 N) :
    primeHorizonExtension (normalizedRamanujanHorizonVector m N) j = 0 := by
  rw [primeHorizonExtension, dif_neg hj]

/-- Every relevant prime power lies below the cutoff. -/
theorem shellAutocorr_far_eq_zero {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0) {c : ℝ} (hc : 0 < c) {N n k j : ℕ}
    (hn : 1 ≤ n) (hj : j ∈ Icc 1 N) (hk : upwardRowCutoff c N ≤ k) :
    shellAutocorr φ (|Real.log k - (Real.log j - Real.log n)| * N / c) = 0 := by
  apply shellAutocorr_eq_zero_of_one_le_abs hφ hsupp
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (mem_Icc.mp hj).1 (mem_Icc.mp hj).2
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
  have hjN : (j : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hj).2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hkR : (N : ℝ) * Real.exp c < k := by
    have h1 : (N : ℝ) * Real.exp c ≤ ⌈(N : ℝ) * Real.exp c⌉₊ := Nat.le_ceil _
    have h2 : ((⌈(N : ℝ) * Real.exp c⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    push_cast at h2
    linarith
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (by positivity) hkR
  have hs : c ≤ Real.log k - (Real.log j - Real.log n) := by
    have h1 : Real.log ((N : ℝ) * Real.exp c) ≤ Real.log k := Real.log_le_log (by positivity) hkR.le
    rw [Real.log_mul (by positivity) (Real.exp_pos c).ne', Real.log_exp] at h1
    have h2 : Real.log j ≤ Real.log N := Real.log_le_log hj0 hjN
    have h3 : 0 ≤ Real.log n := Real.log_nonneg hn1
    linarith
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by linarith)]
  rw [le_div_iff₀ hc]
  nlinarith

/-- **Row identity.** The upward non-ratio row on a normalized Ramanujan mode is the normalized
mode row divided by `√(n log N) √φ(m)`. -/
theorem upwardPrimeRow_normalizedRamanujan_eq {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m)
    {N n : ℕ} (hN : 2 ≤ N) (hn : n ∈ Icc 1 N) :
    upwardPrimeRow (atomDilate φ (c / N)) N
        (primeHorizonExtension (normalizedRamanujanHorizonVector m N)) n /
        (∫ u, atomDilate φ (c / N) u ^ 2) =
      upwardModeRow φ c N m n /
        (Real.sqrt n * Real.sqrt (Real.log N) * Real.sqrt m.totient) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hw : 0 < c / N := div_pos hc hN0
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  have hG0 : (∫ u, atomDilate φ (c / N) u ^ 2) = c / N * ∫ u, φ u ^ 2 := integral_atomDilate_sq hw
  have hG0pos : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by rw [hG0]; exact mul_pos hw hM
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hφm : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hsL : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hlogN
  have hsφ : 0 < Real.sqrt m.totient := Real.sqrt_pos.mpr hφm
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn1)
  -- each bump correlation is the mass times the normalized autocorrelation
  have hbump (k j : ℕ) : bumpCorr (atomDilate φ (c / N))
      (Real.log k - (Real.log j - Real.log n)) =
      (∫ u, atomDilate φ (c / N) u ^ 2) *
        (shellAutocorr φ (|Real.log k - (Real.log j - Real.log n)| * N / c) / ∫ u, φ u ^ 2) := by
    have h := normalized_bumpCorr_atomDilate (φ := φ) hw (Real.log k - (Real.log j - Real.log n))
    rw [div_eq_iff hG0pos.ne'] at h
    rw [h, mul_comm]
    congr 3
    field_simp
  -- the row term of one prime power
  have hRzero : ∀ k ∉ range (upwardRowCutoff c N), vonMangoldtAtom k * ∑ j ∈ Icc 1 N,
      primeHorizonExtension (normalizedRamanujanHorizonVector m N) j *
        (if j = k * n then 0 else bumpCorr (atomDilate φ (c / N))
          (Real.log k - (Real.log j - Real.log n))) = 0 := by
    intro k hk
    have hk' : upwardRowCutoff c N ≤ k := by simpa using hk
    rw [sum_eq_zero fun j hj => ?_, mul_zero]
    split_ifs
    · exact mul_zero _
    · rw [hbump, shellAutocorr_far_eq_zero hφ hsupp hc hn1 hj hk', zero_div, mul_zero, mul_zero]
  unfold upwardPrimeRow
  rw [tsum_eq_sum hRzero, sum_div, upwardModeRow, sum_div]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum, sum_div, sum_div]
  refine sum_congr rfl fun j hj => ?_
  rw [primeHorizonExtension_normalizedRamanujan hj, ramanujanPoleProfile,
    normalizedRamanujanMode_eq_coefficient hm]
  have hsj : 0 < Real.sqrt j := Real.sqrt_pos.mpr (by exact_mod_cast (mem_Icc.mp hj).1)
  split_ifs
  · simp
  · rw [hbump, upwardModePair]
    field_simp

/-! ### Arithmetic and counting tools -/

theorem vonMangoldtAtom_eq (k : ℕ) : vonMangoldtAtom k = (Λ k : ℝ) / Real.sqrt k := by
  unfold vonMangoldtAtom
  split_ifs with hk
  · rfl
  · interval_cases k <;> simp

/-- Ramanujan coefficients only see the residue of a downward shift. -/
theorem ramanujanLagCoefficient_add_sub_shift (m p h : ℕ) (hh : h ≤ p) :
    ramanujanLagCoefficient m (p + (m - 1) * h) = ramanujanLagCoefficient m (p - h) := by
  unfold ramanujanLagCoefficient
  refine sum_congr rfl fun d hd => ?_
  have hdm := Nat.dvd_of_mem_divisors hd
  have hm : 1 ≤ m := Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2
  have heq : p + (m - 1) * h = (p - h) + m * h := by
    have : (m - 1) * h + h = m * h := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hm]
    omega
  have hiff : d ∣ p + (m - 1) * h ↔ d ∣ p - h := by
    rw [heq]
    exact Nat.dvd_add_left (Dvd.dvd.mul_right hdm h)
  simp only [hiff]

/-- The reflected shift has the Ramanujan value of the shift. -/
theorem ramanujanLagCoefficient_reflect (m h : ℕ) :
    ramanujanLagCoefficient m ((m - 1) * h) = ramanujanLagCoefficient m h := by
  unfold ramanujanLagCoefficient
  refine sum_congr rfl fun d hd => ?_
  have hdm := Nat.dvd_of_mem_divisors hd
  have hm : 1 ≤ m := Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2
  have heq : (m - 1) * h + h = m * h := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hm]
  have hmh : d ∣ (m - 1) * h + h := heq ▸ Dvd.dvd.mul_right hdm h
  have hiff : d ∣ (m - 1) * h ↔ d ∣ h :=
    ⟨fun h1 => (Nat.dvd_add_right h1).mp hmh, fun h1 => (Nat.dvd_add_left h1).mp hmh⟩
  simp only [hiff]

/-- A real multiplicative window of prime powers costs at most `log(2/a)` plus a constant. -/
theorem sum_vonMangoldt_div_real_window_le {X a : ℝ} (hX : 1 ≤ X) (ha : 0 < a) (ha1 : a ≤ 1) :
    ∑ k ∈ (Icc 1 ⌊X⌋₊).filter (fun k : ℕ => a * X < (k : ℝ)), (Λ k : ℝ) / k ≤
      Real.log (2 / a) + mertensWindowConstant := by
  have hC := mertensWindowConstant_nonneg
  set U := ⌊a * X⌋₊ with hU
  set V := ⌊X⌋₊ with hV
  have hV1 : 1 ≤ V := Nat.le_floor (by simpa using hX)
  have hUV : U ≤ V := Nat.floor_le_floor (by nlinarith)
  have hsub : (Icc 1 V).filter (fun k : ℕ => a * X < (k : ℝ)) ⊆ Ioc U V := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := mem_filter.mp hk
    refine mem_Ioc.mpr ⟨?_, (mem_Icc.mp hk1).2⟩
    exact Nat.floor_lt (by positivity) |>.mpr hk2
  have hmono := sum_le_sum_of_subset_of_nonneg (f := fun k : ℕ => (Λ k : ℝ) / k) hsub
    fun k _ _ => div_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := k)) (Nat.cast_nonneg k)
  refine hmono.trans ?_
  have hlog2 : 0 ≤ Real.log (2 / a) := Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
  rcases Nat.eq_zero_or_pos U with hU0 | hU0
  · -- `aX < 1`: the whole initial segment up to `X < 1/a`
    rw [hU0]
    have hm := (abs_le.mp (RHTower.Mertens.mertens_first V hV1)).2
    have hIcc : Icc 1 V = Ioc 0 V := rfl
    rw [hIcc] at hm
    have haX : a * X < 1 := by
      by_contra h
      push Not at h
      have : 1 ≤ U := Nat.le_floor (by simpa using h)
      omega
    have hVX : (V : ℝ) ≤ X := Nat.floor_le (by linarith)
    have hV0 : (0 : ℝ) < V := by exact_mod_cast hV1
    have hlogV : Real.log V ≤ Real.log (2 / a) := by
      apply Real.log_le_log hV0
      rw [le_div_iff₀ ha]
      nlinarith
    unfold mertensWindowConstant at *
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    linarith
  · have hw := sum_Ioc_vonMangoldt_div_le hU0 hUV
    have hU0R : (0 : ℝ) < U := by exact_mod_cast hU0
    have hUhalf : a * X / 2 ≤ U := by
      have h1 : a * X - 1 < U := Nat.sub_one_lt_floor _
      have h2 : (1 : ℝ) ≤ U := by exact_mod_cast hU0
      linarith
    have hVX : (V : ℝ) ≤ X := Nat.floor_le (by linarith)
    have hratio : Real.log V - Real.log U ≤ Real.log (2 / a) := by
      rw [← Real.log_div (by positivity) hU0R.ne']
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ hU0R ha]
      nlinarith
    linarith

/-- Reindexing a punctured window around `p` by its signed shifts. -/
theorem sum_Icc_punctured_eq_shifts (N p H : ℕ) (f : ℕ → ℝ)
    (hf : ∀ j ∈ Icc 1 N, j ≠ p → (j + H < p ∨ p + H < j) → f j = 0) :
    (∑ j ∈ Icc 1 N, if j = p then 0 else f j) =
      ∑ h ∈ Icc 1 H, ((if p + h ≤ N then f (p + h) else 0) +
        (if h < p ∧ p - h ≤ N then f (p - h) else 0)) := by
  rw [sum_add_distrib]
  -- the upward part
  have hup : (∑ h ∈ Icc 1 H, if p + h ≤ N then f (p + h) else 0) =
      ∑ j ∈ Icc 1 N, if p < j ∧ j ≤ p + H then f j else 0 := by
    rw [← sum_filter, ← sum_filter]
    refine sum_nbij' (fun h => p + h) (fun j => j - p) ?_ ?_ ?_ ?_ ?_
    · intro h hh
      simp only [mem_filter, mem_Icc] at hh ⊢
      omega
    · intro j hj
      simp only [mem_filter, mem_Icc] at hj ⊢
      omega
    · intro h hh; simp
    · intro j hj
      simp only [mem_filter, mem_Icc] at hj
      omega
    · intro h hh; rfl
  -- the downward part
  have hdown : (∑ h ∈ Icc 1 H, if h < p ∧ p - h ≤ N then f (p - h) else 0) =
      ∑ j ∈ Icc 1 N, if j < p ∧ p ≤ j + H then f j else 0 := by
    rw [← sum_filter, ← sum_filter]
    refine sum_nbij' (fun h => p - h) (fun j => p - j) ?_ ?_ ?_ ?_ ?_
    · intro h hh
      simp only [mem_filter, mem_Icc] at hh ⊢
      omega
    · intro j hj
      simp only [mem_filter, mem_Icc] at hj ⊢
      omega
    · intro h hh
      simp only [mem_filter, mem_Icc] at hh
      omega
    · intro j hj
      simp only [mem_filter, mem_Icc] at hj
      omega
    · intro h hh; rfl
  rw [hup, hdown, ← sum_add_distrib]
  refine sum_congr rfl fun j hj => ?_
  by_cases hjp : j = p
  · subst hjp
    simp
  · rw [if_neg hjp]
    by_cases h1 : p < j ∧ j ≤ p + H
    · rw [if_pos h1, if_neg (by omega), add_zero]
    · by_cases h2 : j < p ∧ p ≤ j + H
      · rw [if_neg h1, if_pos h2, zero_add]
      · rw [if_neg h1, if_neg h2, add_zero]
        exact hf j hj hjp (by omega)

/-! ### Pointwise comparison of a pair with its affine-shell model -/

theorem abs_sqrt_sub_one_le {x : ℝ} (hx : 0 ≤ x) : |Real.sqrt x - 1| ≤ |x - 1| := by
  have hs := Real.sqrt_nonneg x
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hfac : x - 1 = (Real.sqrt x - 1) * (Real.sqrt x + 1) := by
    linear_combination (-1 : ℝ) * hsq
  rw [hfac, abs_mul, abs_of_pos (by linarith : 0 < Real.sqrt x + 1)]
  nlinarith [mul_nonneg (abs_nonneg (Real.sqrt x - 1)) hs]

/-- The log-gap of a pair at distance `h ≤ p/2` from `p` is `h/p` up to `2(h/p)²`. -/
theorem abs_abs_log_sub_sub_le {p j h : ℝ} (hp : 0 < p) (hh : 0 ≤ h) (hhp : 2 * h ≤ p)
    (hjp : j = p + h ∨ j = p - h) :
    |(|Real.log p - Real.log j|) - h / p| ≤ 2 * (h / p) ^ 2 := by
  set δ := h / p with hδ
  have hδ0 : 0 ≤ δ := div_nonneg hh hp.le
  have hδ2 : δ ≤ 1 / 2 := by rw [hδ, div_le_iff₀ hp]; linarith
  have hpδ : p * δ = h := by rw [hδ]; field_simp
  rcases hjp with hjp | hjp
  · have hjδ : j = p * (1 + δ) := by linear_combination hjp - hpδ
    have hlog : |Real.log p - Real.log j| = Real.log (1 + δ) := by
      rw [hjδ, Real.log_mul hp.ne' (by linarith), abs_sub_comm, add_sub_cancel_left]
      exact abs_of_nonneg (Real.log_nonneg (by linarith))
    rw [hlog]
    have := abs_log_one_add_sub_le hδ0
    nlinarith [sq_nonneg δ]
  · have hjδ : j = p * (1 - δ) := by linear_combination hjp + hpδ
    have hlog : |Real.log p - Real.log j| = -Real.log (1 - δ) := by
      rw [hjδ, Real.log_mul hp.ne' (by linarith), sub_add_cancel_left]
      exact abs_of_nonneg (by
        linarith [Real.log_nonpos (by linarith : (0 : ℝ) ≤ 1 - δ) (by linarith : 1 - δ ≤ 1)])
    rw [hlog]
    exact abs_neg_log_one_sub_sub_le hδ2

/-- A pair at distance `h` from `p` has log-gap at least `h/(p+h)`. -/
theorem div_add_le_abs_log_sub {p j h : ℝ} (hp : 0 < p) (hh : 0 ≤ h) (hj : 0 < j)
    (hjp : j = p + h ∨ j = p - h) : h / (p + h) ≤ |Real.log p - Real.log j| := by
  rcases hjp with hjp | hjp
  · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hj hp)
    rw [Real.log_div hj.ne' hp.ne', inv_div] at h1
    have h2 : 1 - p / j = h / (p + h) := by
      rw [hjp]; field_simp; ring
    rw [abs_sub_comm, abs_of_nonneg (by linarith [div_nonneg hh (by linarith : (0 : ℝ) ≤ p + h)])]
    linarith
  · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hp hj)
    rw [Real.log_div hp.ne' hj.ne', inv_div] at h1
    have h2 : 1 - j / p = h / p := by
      rw [hjp]; field_simp; ring
    have h3 : h / (p + h) ≤ h / p := by
      rw [div_le_div_iff₀ (by linarith) hp]; nlinarith
    rw [abs_of_nonneg (by linarith [div_nonneg hh hp.le])]
    linarith

/-- A pair at integer distance `h` from `p`, compared with its affine-shell model. Below
`p ≤ N/(2c)` both vanish; above it the log-gap and the square-root weight linearize with
error `O(1/N)`. -/
theorem abs_pair_sub_shell_le {G : ℝ → ℝ} {M ℓ : ℝ} (hGb : ∀ x, |G x| ≤ M)
    (hGl : ∀ x y, |G x - G y| ≤ ℓ * |x - y|) (hG0 : ∀ x, 1 ≤ |x| → G x = 0) (hℓ : 0 ≤ ℓ)
    {c H N p j h : ℝ} (hc : 0 < c) (hh1 : 1 ≤ h) (hhH : h ≤ H) (hN : 4 * c * H ≤ N)
    (hp : 1 ≤ p) (hj : 0 < j) (hjp : j = p + h ∨ j = p - h) :
    |Real.sqrt (p / j) * G (|Real.log p - Real.log j| * N / c) - G (h * N / (c * p))| ≤
      (if N / (2 * c) < p then (4 * c * H * M + 8 * c * H ^ 2 * ℓ) / N else 0) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hGb 0)
  have hp0 : 0 < p := by linarith
  have hH : 1 ≤ H := hh1.trans hhH
  have hN0 : 0 < N := by nlinarith
  split_ifs with hpN
  · -- linear regime: `h/p ≤ 2cH/N ≤ 1/2`
    have h2cp : N < p * (2 * c) := (div_lt_iff₀ (by positivity)).mp hpN
    have hδ : h / p ≤ 2 * c * H / N := by
      rw [div_le_div_iff₀ hp0 hN0]; nlinarith
    have hD : 2 * c * H / N ≤ 1 / 2 := by rw [div_le_iff₀ hN0]; linarith
    have hhp : 2 * h ≤ p := by
      have := hδ.trans hD
      rw [div_le_iff₀ hp0] at this; linarith
    have hδ0 : 0 ≤ h / p := div_nonneg (by linarith) hp0.le
    have hsq : |Real.sqrt (p / j) - 1| ≤ 2 * (h / p) := by
      refine (abs_sqrt_sub_one_le (div_nonneg hp0.le hj.le)).trans ?_
      have hpj : |p - j| = h := by
        rcases hjp with rfl | rfl
        · rw [show p - (p + h) = -h by ring, abs_neg, abs_of_nonneg (by linarith)]
        · rw [show p - (p - h) = h by ring, abs_of_nonneg (by linarith)]
      have hj2 : p ≤ 2 * j := by rcases hjp with rfl | rfl <;> linarith
      rw [div_sub_one hj.ne', abs_div, abs_of_pos hj, hpj, div_le_iff₀ hj]
      rw [show 2 * (h / p) * j = h * (2 * j) / p by ring, le_div_iff₀ hp0]
      nlinarith
    have hlg : |(|Real.log p - Real.log j| * N / c) - h * N / (c * p)| ≤
        2 * (h / p) ^ 2 * (N / c) := by
      have hAB : |Real.log p - Real.log j| * N / c - h * N / (c * p) =
          (|Real.log p - Real.log j| - h / p) * (N / c) := by
        field_simp
      rw [hAB, abs_mul, abs_of_pos (div_pos hN0 hc)]
      exact mul_le_mul_of_nonneg_right
        (abs_abs_log_sub_sub_le hp0 (by linarith) hhp hjp) (div_pos hN0 hc).le
    calc |Real.sqrt (p / j) * G (|Real.log p - Real.log j| * N / c) - G (h * N / (c * p))|
        = |(Real.sqrt (p / j) - 1) * G (|Real.log p - Real.log j| * N / c) +
            (G (|Real.log p - Real.log j| * N / c) - G (h * N / (c * p)))| := by ring_nf
      _ ≤ |Real.sqrt (p / j) - 1| * M + ℓ * (2 * (h / p) ^ 2 * (N / c)) := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hGb _) (abs_nonneg _)
          · exact (hGl _ _).trans (mul_le_mul_of_nonneg_left hlg hℓ)
      _ ≤ 2 * (h / p) * M + ℓ * (2 * (h / p) ^ 2 * (N / c)) := by gcongr
      _ ≤ 2 * (2 * c * H / N) * M + ℓ * (2 * (2 * c * H / N) ^ 2 * (N / c)) := by gcongr
      _ = (4 * c * H * M + 8 * c * H ^ 2 * ℓ) / N := by field_simp; ring
  · -- vanishing regime: both arguments are at least one
    push Not at hpN
    have h2cp : p * (2 * c) ≤ N := (le_div_iff₀ (by positivity)).mp hpN
    have hB : 1 ≤ h * N / (c * p) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have hA : 1 ≤ |Real.log p - Real.log j| * N / c := by
      have hlog := div_add_le_abs_log_sub hp0 (by linarith) hj hjp
      have h1 : 1 ≤ h / (p + h) * (2 * p) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; nlinarith
      have h2 : 2 * p ≤ N / c := by rw [le_div_iff₀ hc]; linarith
      rw [mul_div_assoc]
      exact h1.trans (mul_le_mul hlog h2 (by positivity) (abs_nonneg _))
    rw [hG0 _ (by rw [abs_of_nonneg (by linarith)]; exact hA),
      hG0 _ (by rw [abs_of_nonneg (by linarith)]; exact hB)]
    simp

/-- Pairs farther than `H ≥ 2c` from `p` carry no autocorrelation. -/
theorem shell_far_eq_zero {G : ℝ → ℝ} (hG0 : ∀ x, 1 ≤ |x| → G x = 0) {c H N p j : ℝ}
    (hc : 0 < c) (hH : 2 * c ≤ H) (hN : 2 * c ≤ N) (hp : 0 < p) (hj : 0 < j) (hjN : j ≤ N)
    (hfar : j + H < p ∨ p + H < j) : G (|Real.log p - Real.log j| * N / c) = 0 := by
  apply hG0
  have hN0 : 0 < N := by linarith
  rcases hfar with hfar | hfar
  · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hp hj)
    rw [Real.log_div hp.ne' hj.ne', inv_div] at h1
    have hjp : j / p < 1 := by rw [div_lt_one hp]; linarith
    have key : c * p ≤ (p - j) * N := by
      rcases le_or_gt p (2 * N) with h | h <;> nlinarith
    have h2 : 1 ≤ (1 - j / p) * N / c := by
      rw [show (1 - j / p) * N / c = (p - j) * N / (c * p) by field_simp, le_div_iff₀ (by positivity),
        one_mul]
      exact key
    have h3 : (1 - j / p) * N / c ≤ (Real.log p - Real.log j) * N / c := by gcongr
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by linarith)]
    linarith
  · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hj hp)
    rw [Real.log_div hj.ne' hp.ne', inv_div] at h1
    have hpj : p / j < 1 := by rw [div_lt_one hj]; linarith
    have key : c * j ≤ (j - p) * N := by nlinarith
    have h2 : 1 ≤ (1 - p / j) * N / c := by
      rw [show (1 - p / j) * N / c = (j - p) * N / (c * j) by field_simp, le_div_iff₀ (by positivity),
        one_mul]
      exact key
    have h3 : (1 - p / j) * N / c ≤ (Real.log j - Real.log p) * N / c := by gcongr
    rw [abs_of_nonneg (by positivity), abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith

/-! ### The row as a sum of punctured windows -/

/-- A pair term around `p`: Ramanujan weight, square-root weight and normalized autocorrelation
of the log-gap. -/
def upwardPairTerm (φ : ℝ → ℝ) (c : ℝ) (N m p j : ℕ) : ℝ :=
  ramanujanLagCoefficient m j *
    (Real.sqrt ((p : ℝ) / j) * shellAutocorr φ (|Real.log p - Real.log j| * N / c)) /
      ∫ u, φ u ^ 2

/-- The punctured window of half-width `H` around `p`, read by its signed shifts. -/
def upwardInner (φ : ℝ → ℝ) (c : ℝ) (N m H p : ℕ) : ℝ :=
  ∑ h ∈ Icc 1 H, ((if p + h ≤ N then upwardPairTerm φ c N m p (p + h) else 0) +
    (if h < p ∧ p - h ≤ N then upwardPairTerm φ c N m p (p - h) else 0))

/-- The affine-shell model of the window around `p`. -/
def upwardShellModel (φ : ℝ → ℝ) (c : ℝ) (N m H p : ℕ) : ℝ :=
  ∑ h ∈ Icc 1 H, (ramanujanLagCoefficient m (p + h) + ramanujanLagCoefficient m (p + (m - 1) * h)) *
    shellAutocorr φ (h * N / (c * p)) / ∫ u, φ u ^ 2

theorem upwardModePair_eq {φ : ℝ → ℝ} {c : ℝ} {N m n k j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) :
    upwardModePair φ c N m n k j = (Λ k : ℝ) / k * upwardPairTerm φ c N m (k * n) j := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [upwardModePair, vonMangoldtAtom_eq]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hlog : Real.log k - (Real.log j - Real.log n) = Real.log ((k * n : ℕ) : ℝ) - Real.log j := by
    push_cast; rw [Real.log_mul hk0.ne' hn0.ne']; ring
  have hA : (Λ k : ℝ) / Real.sqrt k = Λ k / k * Real.sqrt k := by
    rw [eq_comm, div_mul_eq_mul_div, div_eq_div_iff hk0.ne' hsk.ne', mul_assoc,
      Real.mul_self_sqrt hk0.le]
  unfold upwardModePair upwardPairTerm
  rw [vonMangoldtAtom_eq, hlog, hA]
  push_cast
  rw [Real.sqrt_div' _ hj0.le, Real.sqrt_mul hk0.le]
  ring

/-- Outside the window the pair terms vanish, so the punctured row is the window sum. -/
theorem sum_punctured_upwardPairTerm_eq {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0) {c : ℝ} (hc : 0 < c) {N m H p : ℕ}
    (hH : 2 * c ≤ H) (hN : 2 * c ≤ N) (hp : 1 ≤ p) :
    (∑ j ∈ Icc 1 N, if j = p then 0 else upwardPairTerm φ c N m p j) =
      upwardInner φ c N m H p := by
  unfold upwardInner
  apply sum_Icc_punctured_eq_shifts
  intro j hj _ hfar
  have hj' := mem_Icc.mp hj
  have hfar' : (j : ℝ) + H < p ∨ (p : ℝ) + H < j := by
    rcases hfar with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  unfold upwardPairTerm
  rw [shell_far_eq_zero (fun x hx => shellAutocorr_eq_zero_of_one_le_abs hφ hsupp hx) hc hH hN
    (Nat.cast_pos.mpr hp) (Nat.cast_pos.mpr hj'.1) (by exact_mod_cast hj'.2) hfar']
  simp

/-- The upward mode row is the Mangoldt-weighted sum of the punctured windows. -/
theorem upwardModeRow_eq_sum_inner {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0) {c : ℝ} (hc : 0 < c) {N m n H : ℕ}
    (hH : 2 * c ≤ H) (hN : 2 * c ≤ N) (hn : 1 ≤ n) :
    upwardModeRow φ c N m n = ∑ k ∈ range (upwardRowCutoff c N),
      (Λ k : ℝ) / k * upwardInner φ c N m H (k * n) := by
  unfold upwardModeRow
  refine sum_congr rfl fun k _ => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [upwardModePair, vonMangoldtAtom_eq]
  rw [← sum_punctured_upwardPairTerm_eq hφ hsupp hc hH hN (Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero hk.ne' (by omega))), mul_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [upwardModePair_eq hn (mem_Icc.mp hj).1]
  split_ifs <;> simp

/-! ### Window-level comparison -/

/-- The linearization constant of a window of half-width `H`. -/
def upwardLinearError (φ : ℝ → ℝ) (c ℓ : ℝ) (H : ℕ) : ℝ :=
  4 * c * H * (∫ u, φ u ^ 2) + 8 * c * H ^ 2 * ℓ

theorem abs_mul_div_sub_mul_div_le {M C cj x y e : ℝ} (hM : 0 < M) (hC : 0 ≤ C) (hcj : |cj| ≤ C)
    (hxy : |x - y| ≤ e) : |cj * x / M - cj * y / M| ≤ C * e / M := by
  rw [← sub_div, ← mul_sub, abs_div, abs_mul, abs_of_pos hM]
  gcongr

/-- A window below the horizon agrees with its affine-shell model up to the linearization error,
plus a unit boundary cost when the window reaches past `N`. -/
theorem abs_upwardInner_sub_model_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c ℓ : ℝ} (hc : 0 < c) (hℓ : 0 ≤ ℓ)
    (hGl : ∀ x y, |shellAutocorr φ x - shellAutocorr φ y| ≤ ℓ * |x - y|)
    {N m H p : ℕ} (hH : 1 ≤ H) (hN : 4 * c * H ≤ N) (hp : 1 ≤ p) (hpN : p ≤ N) :
    |upwardInner φ c N m H p - upwardShellModel φ c N m H p| ≤
      H * ((m.totient : ℝ) * (2 * (if (N : ℝ) / (2 * c) < p then upwardLinearError φ c ℓ H / N else 0) /
        (∫ u, φ u ^ 2) + if N < p + H then 1 else 0)) := by
  set M := ∫ u, φ u ^ 2 with hMdef
  set C : ℝ := (m.totient : ℝ)
  set err : ℝ := if (N : ℝ) / (2 * c) < p then upwardLinearError φ c ℓ H / N else 0
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hcm : ∀ j, |ramanujanLagCoefficient m j| ≤ C := fun j =>
    BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m j
  have hGb : ∀ x, |shellAutocorr φ x| ≤ M := abs_shellAutocorr_le hφ hsupp
  have hG0 : ∀ x, 1 ≤ |x| → shellAutocorr φ x = 0 :=
    fun x hx => shellAutocorr_eq_zero_of_one_le_abs hφ hsupp hx
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hN0 : (0 : ℝ) < N := by nlinarith
  have herr0 : 0 ≤ err := by
    simp only [err]
    split_ifs
    · unfold upwardLinearError; positivity
    · exact le_rfl
  have hkey : ∀ {h : ℕ} {j : ℝ}, h ∈ Icc 1 H → 0 < j → (j = p + h ∨ j = p - h) →
      |Real.sqrt (p / j) * shellAutocorr φ (|Real.log p - Real.log j| * N / c) -
        shellAutocorr φ (h * N / (c * p))| ≤ err := by
    intro h j hh hj hjp
    have hh' := mem_Icc.mp hh
    exact abs_pair_sub_shell_le hGb hGl hG0 hℓ hc (by exact_mod_cast hh'.1)
      (by exact_mod_cast hh'.2) hN hp1 hj hjp
  unfold upwardInner upwardShellModel
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ h ∈ Icc 1 H, |_| ≤ ∑ _h ∈ Icc 1 H, C * (2 * err / M + if N < p + H then 1 else 0) := by
        refine sum_le_sum fun h hh => ?_
        have hh' := mem_Icc.mp hh
        rw [show ∀ a b x y g : ℝ, a + b - (x + y) * g / M = (a - x * g / M) + (b - y * g / M) by
          intro a b x y g; ring]
        refine (abs_add_le _ _).trans ?_
        have hup : |(if p + h ≤ N then upwardPairTerm φ c N m p (p + h) else 0) -
            ramanujanLagCoefficient m (p + h) * shellAutocorr φ (h * N / (c * p)) / M| ≤
            C * err / M + C * (if N < p + H then 1 else 0) := by
          by_cases hup : p + h ≤ N
          · rw [if_pos hup]
            have h1 := abs_mul_div_sub_mul_div_le hM hC (hcm (p + h))
              (hkey (j := ((p + h : ℕ) : ℝ)) hh (by positivity) (Or.inl (by push_cast; ring)))
            unfold upwardPairTerm
            have h2 : 0 ≤ C * (if N < p + H then 1 else 0 : ℝ) := by
              split_ifs <;> simp [hC]
            linarith
          · rw [if_neg hup, if_pos (by omega), zero_sub, abs_neg, mul_one]
            have h1 : |ramanujanLagCoefficient m (p + h) * shellAutocorr φ (h * N / (c * p)) / M|
                ≤ C := by
              rw [abs_div, abs_mul, abs_of_pos hM, div_le_iff₀ hM]
              exact mul_le_mul (hcm _) (hGb _) (abs_nonneg _) hC
            have h2 : 0 ≤ C * err / M := div_nonneg (mul_nonneg hC herr0) hM.le
            linarith
        have hdown : |(if h < p ∧ p - h ≤ N then upwardPairTerm φ c N m p (p - h) else 0) -
            ramanujanLagCoefficient m (p + (m - 1) * h) * shellAutocorr φ (h * N / (c * p)) / M| ≤
            C * err / M := by
          by_cases hdn : h < p
          · rw [if_pos ⟨hdn, by omega⟩, ramanujanLagCoefficient_add_sub_shift m p h hdn.le]
            have hj : (0 : ℝ) < ((p - h : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < p - h)
            have h1 := abs_mul_div_sub_mul_div_le hM hC (hcm (p - h))
              (hkey (j := ((p - h : ℕ) : ℝ)) hh hj (Or.inr (by rw [Nat.cast_sub hdn.le])))
            unfold upwardPairTerm
            exact h1
          · rw [if_neg (by omega), zero_sub, abs_neg]
            have hz : shellAutocorr φ (h * N / (c * p)) = 0 := by
              apply hG0
              have hhp : (p : ℝ) ≤ h := by exact_mod_cast (by omega : p ≤ h)
              have hp0 : (0 : ℝ) < p := by linarith
              rw [abs_of_nonneg (by positivity), le_div_iff₀ (by positivity), one_mul]
              have hcN : c ≤ N := by nlinarith
              nlinarith
            rw [hz, mul_zero, zero_div, abs_zero]
            exact div_nonneg (mul_nonneg hC herr0) hM.le
        have hsplit : C * (2 * err / M + if N < p + H then 1 else 0) =
            C * err / M + C * (if N < p + H then 1 else 0) + C * err / M := by ring
        rw [hsplit]
        linarith
    _ = H * (C * (2 * err / M + if N < p + H then 1 else 0)) := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp

/-- A window beyond the horizon costs at most `2φ(m)` per shift, and nothing once it no longer
reaches back below `N`. -/
theorem abs_upwardInner_le_of_lt {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ}
    {N m H p : ℕ} (hH : 2 * H ≤ N) (hNp : N < p) :
    |upwardInner φ c N m H p| ≤ H * (2 * (m.totient : ℝ) * if p ≤ N + H then 1 else 0) := by
  set M := ∫ u, φ u ^ 2 with hMdef
  set C : ℝ := (m.totient : ℝ)
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hGb : ∀ x, |shellAutocorr φ x| ≤ M := abs_shellAutocorr_le hφ hsupp
  unfold upwardInner
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ h ∈ Icc 1 H, |_| ≤ ∑ _h ∈ Icc 1 H, (2 * C * if p ≤ N + H then 1 else 0) := by
        refine sum_le_sum fun h hh => ?_
        have hh' := mem_Icc.mp hh
        rw [if_neg (by omega), zero_add]
        split_ifs with hdn hpN
        · have hj : (0 : ℝ) < ((p - h : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < p - h)
          have hsq : Real.sqrt ((p : ℝ) / ((p - h : ℕ) : ℝ)) ≤ 2 := by
            have h4 : (p : ℝ) / ((p - h : ℕ) : ℝ) ≤ 2 ^ 2 := by
              rw [div_le_iff₀ hj, Nat.cast_sub (by omega)]
              have : (2 * h : ℝ) ≤ N := by exact_mod_cast (by omega : 2 * h ≤ N)
              have : (N : ℝ) < p := by exact_mod_cast hNp
              linarith
            calc Real.sqrt _ ≤ Real.sqrt (2 ^ 2) := Real.sqrt_le_sqrt h4
              _ = 2 := Real.sqrt_sq (by norm_num)
          unfold upwardPairTerm
          rw [mul_one, abs_div, abs_mul, abs_mul, abs_of_pos hM,
            abs_of_nonneg (Real.sqrt_nonneg _), div_le_iff₀ hM]
          calc |ramanujanLagCoefficient m (p - h)| * (Real.sqrt _ * |shellAutocorr φ _|)
              ≤ C * (2 * M) := mul_le_mul
                (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m _)
                (mul_le_mul hsq (hGb _) (abs_nonneg _) (by norm_num)) (by positivity) hC
            _ = 2 * C * M := by ring
        · exfalso; omega
        · rw [abs_zero]; linarith [hC]
        · rw [abs_zero]; linarith [hC]
    _ = H * (2 * C * if p ≤ N + H then 1 else 0) := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp

/-! ### Row-level comparison -/

/-- The affine-shell model of a whole row: windows around `kn ≤ N`. -/
def upwardModel (φ : ℝ → ℝ) (c : ℝ) (N m H n : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 (N / n), (Λ k : ℝ) / k * upwardShellModel φ c N m H (k * n)

/-- Prime powers whose multiple of `n` lies within `H` of the horizon. -/
def upwardBoundaryMass (N n H : ℕ) : ℝ :=
  ∑ k ∈ (Icc 1 (2 * N)).filter (fun k => N < k * n + H ∧ k * n ≤ N + H), (Λ k : ℝ) / k

theorem vonMangoldt_div_nonneg (k : ℕ) : 0 ≤ (Λ k : ℝ) / k :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)

/-- **Row comparison.** A row differs from its affine-shell model by the linearization error
over a bounded multiplicative window plus the boundary mass. -/
theorem abs_upwardModeRow_sub_model_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c ℓ : ℝ} (hc : 0 < c) (hℓ : 0 ≤ ℓ)
    (hGl : ∀ x y, |shellAutocorr φ x - shellAutocorr φ y| ≤ ℓ * |x - y|)
    {N m n H : ℕ} (hH1 : 1 ≤ H) (hH : 2 * c ≤ H) (hN : 4 * c * H ≤ N) (hNH : 2 * H ≤ N)
    (hn : n ∈ Icc 1 N) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hac : a * (2 * c) ≤ 1) :
    |upwardModeRow φ c N m n - upwardModel φ c N m H n| ≤
      H * m.totient * (2 * upwardLinearError φ c ℓ H / ((∫ u, φ u ^ 2) * N)) *
          (Real.log (2 / a) + mertensWindowConstant) +
        3 * H * m.totient * upwardBoundaryMass N n H := by
  set M := ∫ u, φ u ^ 2 with hMdef
  set C : ℝ := (m.totient : ℝ)
  set E := upwardLinearError φ c ℓ H
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hE : 0 ≤ E := by unfold E upwardLinearError; positivity
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  have hH1R : (1 : ℝ) ≤ H := by exact_mod_cast hH1
  have hN0 : (0 : ℝ) < N := by nlinarith
  have hN2c : 2 * c ≤ N := by nlinarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set X : ℝ := (N : ℝ) / n with hXdef
  have hfl : ⌊X⌋₊ = N / n := Nat.floor_div_eq_div N n
  have hX1 : 1 ≤ X := by rw [hXdef, le_div_iff₀ hn0, one_mul]; exact_mod_cast hnN
  set K := upwardRowCutoff c N
  have hNK : N < K := by
    have h1 : (N : ℝ) ≤ N * Real.exp c := le_mul_of_one_le_right hN0.le (Real.one_le_exp hc.le)
    have h2 : (N : ℝ) * Real.exp c ≤ ⌈(N : ℝ) * Real.exp c⌉₊ := Nat.le_ceil _
    have h3 : N ≤ ⌈(N : ℝ) * Real.exp c⌉₊ := by exact_mod_cast h1.trans h2
    simp only [K, upwardRowCutoff]; omega
  have hdivN : N / n ≤ N := Nat.div_le_self N n
  -- the model as a sum over the same prime-power range
  have hmodel : upwardModel φ c N m H n = ∑ k ∈ range K,
      if 1 ≤ k ∧ k ≤ N / n then (Λ k : ℝ) / k * upwardShellModel φ c N m H (k * n) else 0 := by
    rw [← sum_filter]
    unfold upwardModel
    congr 1
    ext k
    simp only [mem_Icc, mem_filter, mem_range]
    omega
  rw [upwardModeRow_eq_sum_inner hφ hsupp hc hH hN2c hn1, hmodel, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  -- the two weight families
  set w1 : ℕ → ℝ := fun k => if k ∈ Icc 1 ⌊X⌋₊ ∧ a * X < k then (Λ k : ℝ) / k else 0
  set w2 : ℕ → ℝ := fun k =>
    if k ∈ Icc 1 (2 * N) ∧ (N < k * n + H ∧ k * n ≤ N + H) then (Λ k : ℝ) / k else 0
  have hw1 : ∀ k, 0 ≤ w1 k := fun k => by
    simp only [w1]; split_ifs
    · exact vonMangoldt_div_nonneg k
    · exact le_rfl
  have hw2 : ∀ k, 0 ≤ w2 k := fun k => by
    simp only [w2]; split_ifs
    · exact vonMangoldt_div_nonneg k
    · exact le_rfl
  have hpt : ∀ k ∈ range K, |(Λ k : ℝ) / k * upwardInner φ c N m H (k * n) -
      (if 1 ≤ k ∧ k ≤ N / n then (Λ k : ℝ) / k * upwardShellModel φ c N m H (k * n) else 0)| ≤
      H * C * (2 * E / (M * N)) * w1 k + 3 * H * C * w2 k := by
    intro k _
    have hlam := vonMangoldt_div_nonneg k
    have hA : 0 ≤ H * C * (2 * E / (M * N)) := by positivity
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [Nat.cast_zero, div_zero, zero_mul, ArithmeticFunction.map_zero]
      rw [if_neg (by omega), sub_zero, abs_zero]
      exact add_nonneg (mul_nonneg hA (hw1 0)) (by positivity)
    by_cases hkX : k ≤ N / n
    · -- a window below the horizon
      rw [if_pos ⟨hk, hkX⟩, ← mul_sub, abs_mul, abs_of_nonneg hlam]
      have hkn : k * n ≤ N := (Nat.le_div_iff_mul_le hn1).mp hkX
      have hbd := abs_upwardInner_sub_model_le hφ hsupp hM hc hℓ hGl (m := m) hH1 hN
        (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hk.ne' (by omega))) hkn
      have h1 : (Λ k : ℝ) / k * (if (N : ℝ) / (2 * c) < ((k * n : ℕ) : ℝ) then E / N else 0) ≤
          E / N * w1 k := by
        split_ifs with hlt
        · have hw : w1 k = (Λ k : ℝ) / k := by
            simp only [w1]
            rw [if_pos]
            refine ⟨mem_Icc.mpr ⟨hk, hfl ▸ hkX⟩, ?_⟩
            push_cast at hlt
            rw [hXdef, mul_div_assoc', div_lt_iff₀ hn0]
            rw [div_lt_iff₀ (by positivity)] at hlt
            nlinarith
          rw [hw]; ring_nf; exact le_rfl
        · rw [mul_zero]; exact mul_nonneg (div_nonneg hE hN0.le) (hw1 k)
      have h2 : (Λ k : ℝ) / k * (if N < k * n + H then 1 else 0) ≤ w2 k := by
        split_ifs with hlt
        · have hw : w2 k = (Λ k : ℝ) / k := by
            simp only [w2]
            rw [if_pos]
            refine ⟨mem_Icc.mpr ⟨hk, ?_⟩, hlt, by omega⟩
            have : k ≤ k * n := Nat.le_mul_of_pos_right k hn1
            omega
          rw [hw, mul_one]
        · rw [mul_zero]; exact hw2 k
      calc (Λ k : ℝ) / k * |upwardInner φ c N m H (k * n) - upwardShellModel φ c N m H (k * n)|
          ≤ (Λ k : ℝ) / k * (H * (C * (2 * (if (N : ℝ) / (2 * c) < ((k * n : ℕ) : ℝ)
              then E / N else 0) / M + if N < k * n + H then 1 else 0))) :=
            mul_le_mul_of_nonneg_left hbd hlam
        _ = H * C * (2 / M) * ((Λ k : ℝ) / k * (if (N : ℝ) / (2 * c) < ((k * n : ℕ) : ℝ)
              then E / N else 0)) + H * C * ((Λ k : ℝ) / k * (if N < k * n + H then 1 else 0)) := by
            ring
        _ ≤ H * C * (2 / M) * (E / N * w1 k) + H * C * w2 k := by
            have hHC : 0 ≤ H * C := by positivity
            have hHCM : 0 ≤ H * C * (2 / M) := by positivity
            exact add_le_add (mul_le_mul_of_nonneg_left h1 hHCM) (mul_le_mul_of_nonneg_left h2 hHC)
        _ ≤ H * C * (2 * E / (M * N)) * w1 k + 3 * H * C * w2 k := by
            have hHC : 0 ≤ H * C * w2 k := mul_nonneg (by positivity) (hw2 k)
            have heq : H * C * (2 / M) * (E / N * w1 k) = H * C * (2 * E / (M * N)) * w1 k := by
              field_simp
            rw [heq]
            linarith
    · -- a window beyond the horizon
      rw [if_neg (by omega), sub_zero, abs_mul, abs_of_nonneg hlam]
      have hkn : N < k * n := (Nat.div_lt_iff_lt_mul hn1).mp (by omega)
      have hbd := abs_upwardInner_le_of_lt hφ hsupp hM (c := c) (m := m) hNH hkn
      have h2 : (Λ k : ℝ) / k * (if k * n ≤ N + H then 1 else 0) ≤ w2 k := by
        split_ifs with hle
        · have hw : w2 k = (Λ k : ℝ) / k := by
            simp only [w2]
            rw [if_pos]
            refine ⟨mem_Icc.mpr ⟨hk, ?_⟩, by omega, hle⟩
            have : k ≤ k * n := Nat.le_mul_of_pos_right k hn1
            omega
          rw [hw, mul_one]
        · rw [mul_zero]; exact hw2 k
      calc (Λ k : ℝ) / k * |upwardInner φ c N m H (k * n)|
          ≤ (Λ k : ℝ) / k * (H * (2 * C * if k * n ≤ N + H then 1 else 0)) :=
            mul_le_mul_of_nonneg_left hbd hlam
        _ = 2 * H * C * ((Λ k : ℝ) / k * if k * n ≤ N + H then 1 else 0) := by ring
        _ ≤ 2 * H * C * w2 k := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ H * C * (2 * E / (M * N)) * w1 k + 3 * H * C * w2 k := by
            have h3 : 0 ≤ H * C * (2 * E / (M * N)) * w1 k :=
              mul_nonneg (by positivity) (hw1 k)
            have h4 : 0 ≤ H * C * w2 k := mul_nonneg (by positivity) (hw2 k)
            linarith
  -- sum the two weight families
  have hS1 : ∑ k ∈ range K, w1 k ≤ Real.log (2 / a) + mertensWindowConstant := by
    simp only [w1]
    rw [← sum_filter]
    refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => vonMangoldt_div_nonneg k)
      (sum_vonMangoldt_div_real_window_le hX1 ha ha1)
    intro k hk
    rw [mem_filter] at hk ⊢
    exact ⟨hk.2.1, hk.2.2⟩
  have hS2 : ∑ k ∈ range K, w2 k ≤ upwardBoundaryMass N n H := by
    simp only [w2]
    rw [← sum_filter]
    unfold upwardBoundaryMass
    refine sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => vonMangoldt_div_nonneg k
    intro k hk
    rw [mem_filter] at hk ⊢
    exact ⟨hk.2.1, hk.2.2⟩
  calc ∑ k ∈ range K, |_| ≤ ∑ k ∈ range K, (H * C * (2 * E / (M * N)) * w1 k + 3 * H * C * w2 k) :=
        sum_le_sum hpt
    _ = H * C * (2 * E / (M * N)) * ∑ k ∈ range K, w1 k + 3 * H * C * ∑ k ∈ range K, w2 k := by
        rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ H * C * (2 * E / (M * N)) * (Real.log (2 / a) + mertensWindowConstant) +
        3 * H * C * upwardBoundaryMass N n H := by
        gcongr

/-- The boundary mass is at most `4H log(2X)/X` at `X = N/n`. -/
theorem upwardBoundaryMass_le {N n H : ℕ} (hNH : 2 * H ≤ N) (hn : n ∈ Icc 1 N) :
    upwardBoundaryMass N n H ≤
      2 * H * (2 * Real.log (2 * ((N : ℝ) / n)) / ((N : ℝ) / n)) := by
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set X : ℝ := (N : ℝ) / n with hXdef
  have hX0 : 0 < X := div_pos hN0 hn0
  have hX1 : 1 ≤ X := by rw [hXdef, le_div_iff₀ hn0, one_mul]; exact_mod_cast hnN
  have hlog : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
  unfold upwardBoundaryMass
  set S := (Icc 1 (2 * N)).filter (fun k => N < k * n + H ∧ k * n ≤ N + H)
  have hcard : S.card ≤ 2 * H := by
    calc S.card ≤ (Ioc (N - H) (N + H)).card := by
          refine card_le_card_of_injOn (fun k => k * n) ?_ ?_
          · intro k hk
            rw [mem_coe, mem_filter, mem_Icc] at hk
            simp only [mem_coe, mem_Ioc]
            generalize k * n = q at hk ⊢
            omega
          · intro k₁ _ k₂ _ h
            exact Nat.eq_of_mul_eq_mul_right hn1 h
      _ = 2 * H := by rw [Nat.card_Ioc]; omega
  have hterm : ∀ k ∈ S, (Λ k : ℝ) / k ≤ 2 * Real.log (2 * X) / X := by
    intro k hk
    rw [mem_filter, mem_Icc] at hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.1.1
    have hkn1 : (N : ℝ) < k * n + H := by exact_mod_cast hk.2.1
    have hkn2 : (k : ℝ) * n ≤ N + H := by exact_mod_cast hk.2.2
    have hHN : (2 * H : ℝ) ≤ N := by exact_mod_cast hNH
    have hk2X : (k : ℝ) ≤ 2 * X := by
      rw [hXdef, ← mul_div_assoc, le_div_iff₀ hn0]; linarith
    have hXk : X / 2 ≤ k := by
      rw [hXdef, div_div, div_le_iff₀ (by positivity)]; linarith
    calc (Λ k : ℝ) / k ≤ Real.log (2 * X) / k := by
          gcongr
          exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hk0 hk2X)
      _ ≤ Real.log (2 * X) / (X / 2) := by gcongr
      _ = 2 * Real.log (2 * X) / X := by rw [div_div_eq_mul_div]; ring
  calc ∑ k ∈ S, (Λ k : ℝ) / k ≤ S.card • (2 * Real.log (2 * X) / X) :=
        sum_le_card_nsmul _ _ _ hterm
    _ = S.card * (2 * Real.log (2 * X) / X) := nsmul_eq_mul _ _
    _ ≤ 2 * H * (2 * Real.log (2 * X) / X) := by
        gcongr
        exact_mod_cast hcard

/-- The window model is bounded by `2Hφ(m)`. -/
theorem abs_upwardShellModel_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ}
    (N m H p : ℕ) : |upwardShellModel φ c N m H p| ≤ 2 * H * m.totient := by
  have hC : (0 : ℝ) ≤ m.totient := Nat.cast_nonneg _
  have hcm : ∀ j, |ramanujanLagCoefficient m j| ≤ m.totient := fun j =>
    BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m j
  unfold upwardShellModel
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ h ∈ Icc 1 H, |_| ≤ ∑ _h ∈ Icc 1 H, (2 * (m.totient : ℝ)) := by
        refine sum_le_sum fun h _ => ?_
        rw [abs_div, abs_mul, abs_of_pos hM, div_le_iff₀ hM]
        have h1 := abs_add_le (ramanujanLagCoefficient m (p + h))
          (ramanujanLagCoefficient m (p + (m - 1) * h))
        calc |_ + _| * |shellAutocorr φ _| ≤ (m.totient + m.totient) * ∫ u, φ u ^ 2 :=
              mul_le_mul (h1.trans (add_le_add (hcm _) (hcm _))) (abs_shellAutocorr_le hφ hsupp _)
                (abs_nonneg _) (by positivity)
          _ = 2 * m.totient * ∫ u, φ u ^ 2 := by ring
    _ = 2 * H * m.totient := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp only [add_tsub_cancel_right]
        ring

/-- The row model is the reciprocal-shell reading of the affine prime shells. -/
theorem upwardModel_eq_shells {φ : ℝ → ℝ} {c : ℝ} {N m H n : ℕ} (hn : 1 ≤ n) :
    upwardModel φ c N m H n = (∫ u, φ u ^ 2)⁻¹ * ∑ h ∈ Icc 1 H,
      (affineRamanujanPrimeShell m n h φ c h ((N : ℝ) / n) +
        affineRamanujanPrimeShell m n ((m - 1) * h) φ c h ((N : ℝ) / n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold upwardModel upwardShellModel affineRamanujanPrimeShell
  rw [Nat.floor_div_eq_div]
  simp only [mul_sum, ← sum_add_distrib]
  rw [sum_comm]
  refine sum_congr rfl fun h _ => sum_congr rfl fun k _ => ?_
  have harg : (h : ℝ) * ((N : ℝ) / n) / (c * k) = h * N / (c * ((k * n : ℕ) : ℝ)) := by
    push_cast; field_simp
  rw [harg]
  ring

/-- On `[a, 1]` with `a ≥ 1` the reciprocal shell integral vanishes. -/
theorem integral_shellAutocorr_div_eq_zero {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0) {a : ℝ} (ha : 1 ≤ a) :
    ∫ u in a..1, shellAutocorr φ u / u = 0 := by
  rw [intervalIntegral.integral_symm, neg_eq_zero]
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
  · simp
  intro u hu
  rw [Set.uIcc_of_le ha] at hu
  have h1 : 1 ≤ |u| := by rw [abs_of_nonneg (by linarith [hu.1])]; exact hu.1
  simp [shellAutocorr_eq_zero_of_one_le_abs hφ hsupp h1]

/-- The shell correction against a Ramanujan coefficient, as the mean of the reciprocal shells. -/
theorem shellCorrection_mul_eq {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0) {c : ℝ} (hc : 0 < c) {m H : ℕ}
    (hH : ⌈c⌉₊ ≤ H + 1) (n : ℕ) :
    shellCorrection φ c m * ramanujanLagCoefficient m n = (∫ u, φ u ^ 2)⁻¹ * ∑ h ∈ Icc 1 H,
      (ramanujanLagCoefficient m n * ramanujanLagCoefficient m h / (m.totient : ℝ) *
          (∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u) +
        ramanujanLagCoefficient m n * ramanujanLagCoefficient m ((m - 1) * h) /
          (m.totient : ℝ) * (∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u)) := by
  have hsub : ∑ h ∈ Ico 1 ⌈c⌉₊, ramanujanLagCoefficient m h *
      ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u =
      ∑ h ∈ Icc 1 H, ramanujanLagCoefficient m h *
        ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u := by
    refine sum_subset (fun h hh => ?_) fun h hh hnot => ?_
    · rw [mem_Ico] at hh; rw [mem_Icc]; omega
    · rw [mem_Icc] at hh
      rw [mem_Ico] at hnot
      have hch : ⌈c⌉₊ ≤ h := by omega
      have hc1 : c ≤ h := (Nat.le_ceil c).trans (by exact_mod_cast hch)
      rw [integral_shellAutocorr_div_eq_zero hφ hsupp (by rw [le_div_iff₀ hc]; linarith), mul_zero]
  unfold shellCorrection
  rw [hsub]
  simp only [ramanujanLagCoefficient_reflect, mul_sum, sum_mul]
  refine sum_congr rfl fun h _ => ?_
  ring

/-- `log(2X)/X` is eventually below any positive level. -/
theorem exists_log_two_mul_div_le {η : ℝ} (hη : 0 < η) :
    ∃ X₁ : ℝ, ∀ X : ℝ, X₁ ≤ X → Real.log (2 * X) / X ≤ η := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop (1 / 2) 0 1 (by norm_num)).comp
    (tendsto_id.const_mul_atTop (show (0 : ℝ) < 2 by norm_num))
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp ((tendsto_order.1 h).2 η hη)
  refine ⟨X₁, fun X hX => ?_⟩
  have := hX₁ X hX
  simp only [Function.comp, id, pow_one] at this
  have heq : 1 / 2 * (2 * X) + 0 = X := by ring
  rw [heq] at this
  exact this.le

/-! ### Rows converge to the shell correction -/

/-- The window half-width used for overlap `c`. -/
def upwardWindow (c : ℝ) : ℕ := ⌈2 * c⌉₊ + 1

theorem two_mul_le_upwardWindow (c : ℝ) : 2 * c ≤ upwardWindow c := by
  unfold upwardWindow; push_cast; linarith [Nat.le_ceil (2 * c)]

theorem ceil_le_upwardWindow_add_one {c : ℝ} (hc : 0 < c) : ⌈c⌉₊ ≤ upwardWindow c + 1 := by
  unfold upwardWindow
  have : ⌈c⌉₊ ≤ ⌈2 * c⌉₊ := Nat.ceil_mono (by linarith)
  omega

/-- Interior and boundary errors of a row against its shell model, at window `H = upwardWindow c`
and multiplicative cutoff `a = min 1 (1/(2c))`. -/
theorem abs_upwardModeRow_sub_model_le_log {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c ℓ : ℝ} (hc : 0 < c) (hℓ : 0 ≤ ℓ)
    (hGl : ∀ x y, |shellAutocorr φ x - shellAutocorr φ y| ≤ ℓ * |x - y|)
    {N m n : ℕ} (hN : 4 * c * upwardWindow c ≤ N) (hNH : 2 * upwardWindow c ≤ N)
    (hn : n ∈ Icc 1 N) :
    |upwardModeRow φ c N m n - upwardModel φ c N m (upwardWindow c) n| ≤
      upwardWindow c * m.totient *
          (2 * upwardLinearError φ c ℓ (upwardWindow c) / ((∫ u, φ u ^ 2) * N)) *
          (Real.log (2 / min 1 (1 / (2 * c))) + mertensWindowConstant) +
        3 * upwardWindow c * m.totient * (2 * upwardWindow c *
          (2 * Real.log (2 * ((N : ℝ) / n)) / ((N : ℝ) / n))) := by
  have ha : 0 < min 1 (1 / (2 * c)) := lt_min one_pos (by positivity)
  have hac : min 1 (1 / (2 * c)) * (2 * c) ≤ 1 := by
    calc min 1 (1 / (2 * c)) * (2 * c) ≤ 1 / (2 * c) * (2 * c) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = 1 := by field_simp
  refine (abs_upwardModeRow_sub_model_le hφ hsupp hM hc hℓ hGl (by unfold upwardWindow; omega)
    (two_mul_le_upwardWindow c) hN hNH hn ha (min_le_left _ _) hac).trans ?_
  gcongr
  exact upwardBoundaryMass_le hNH hn

/-- **Rows far below the horizon.** For every `ε > 0` there is `J` such that, eventually, every
upward mode row with `Jn ≤ N` is within `ε` of `κ_m(c) c_m(n)`. -/
theorem exists_upwardModeRow_near_shellCorrection {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, 0 < J ∧ ∀ᶠ N : ℕ in atTop, ∀ n ∈ Icc 1 N, J * n ≤ N →
      |upwardModeRow φ c N m n - shellCorrection φ c m * ramanujanLagCoefficient m n| ≤ ε := by
  obtain ⟨ℓ, hℓ, hGl⟩ := exists_shellAutocorr_lipschitz hφ hsupp
  set M := ∫ u, φ u ^ 2 with hMdef
  set H := upwardWindow c
  set C : ℝ := (m.totient : ℝ)
  set E := upwardLinearError φ c ℓ H
  set W := Real.log (2 / min 1 (1 / (2 * c))) + mertensWindowConstant
  have hC : 0 < C := Nat.cast_pos.mpr (Nat.totient_pos.mpr hm)
  have hH : (0 : ℝ) < H := by unfold H upwardWindow; positivity
  -- the affine shells, uniformly in `n` and the residue, for each shift
  set ε' := ε * M / (6 * H)
  have hε' : 0 < ε' := by positivity
  have hshell : ∀ᶠ X : ℝ in atTop, ∀ h ∈ Icc 1 H, ∀ n b : ℕ,
      |affineRamanujanPrimeShell m n b φ c h X -
        (ramanujanLagCoefficient m n * ramanujanLagCoefficient m b / (m.totient : ℝ)) *
          ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u| ≤ ε' :=
    (eventually_all_finset _).2 fun h hh =>
      eventually_affineRamanujanPrimeShell_uniform hm hφ hsupp hc (mem_Icc.mp hh).1 hε'
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hshell
  -- the boundary mass
  set η := ε / (36 * H ^ 2 * C)
  obtain ⟨X₁, hX₁⟩ := exists_log_two_mul_div_le (η := η) (by positivity)
  -- the interior linearization error
  have hint : ∀ᶠ N : ℕ in atTop, H * C * (2 * E / (M * N)) * W < ε / 3 := by
    have h := (tendsto_order.1 (tendsto_const_div_atTop_nhds_zero_nat (H * C * 2 * E * W / M))).2
      (ε / 3) (by positivity)
    filter_upwards [h] with N hN
    have heq : H * C * (2 * E / (M * N)) * W = H * C * 2 * E * W / M / N := by ring
    rw [heq]; exact hN
  refine ⟨⌈max X₀ X₁⌉₊ + 1, by omega, ?_⟩
  filter_upwards [hint, eventually_ge_atTop ⌈4 * c * H⌉₊, eventually_ge_atTop (2 * H)]
    with N hNint hN4 hN2 n hn hJn
  have hN4' : 4 * c * H ≤ N := Nat.ceil_le.mp hN4
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set X : ℝ := (N : ℝ) / n with hXdef
  have hJX : max X₀ X₁ ≤ X := by
    have h1 : max X₀ X₁ ≤ (⌈max X₀ X₁⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈max X₀ X₁⌉₊ + 1 : ℕ) : ℝ) * n ≤ N := by exact_mod_cast hJn
    rw [hXdef, le_div_iff₀ hn0]
    push_cast at h2
    nlinarith
  -- row against model
  have hrow : |upwardModeRow φ c N m n - upwardModel φ c N m H n| ≤
      H * C * (2 * E / (M * N)) * W + 3 * H * C * (2 * H * (2 * Real.log (2 * X) / X)) :=
    abs_upwardModeRow_sub_model_le_log hφ hsupp hM hc hℓ hGl hN4' hN2 hn
  have hlog := hX₁ X ((le_max_right _ _).trans hJX)
  have hbd : 3 * H * C * (2 * H * (2 * Real.log (2 * X) / X)) ≤ ε / 3 := by
    have h1 : 2 * Real.log (2 * X) / X = 2 * (Real.log (2 * X) / X) := by ring
    rw [h1]
    calc 3 * H * C * (2 * H * (2 * (Real.log (2 * X) / X))) ≤ 3 * H * C * (2 * H * (2 * η)) := by
          gcongr
      _ = ε / 3 := by simp only [η]; field_simp; ring
  -- model against the shell correction
  have hmodel : |upwardModel φ c N m H n - shellCorrection φ c m * ramanujanLagCoefficient m n|
      ≤ ε / 3 := by
    rw [upwardModel_eq_shells hn1, shellCorrection_mul_eq hφ hsupp hc
      (ceil_le_upwardWindow_add_one hc) n, ← mul_sub, ← sum_sub_distrib, abs_mul,
      abs_of_pos (inv_pos.mpr hM)]
    have hX0 := hX₀ X ((le_max_left _ _).trans hJX)
    calc M⁻¹ * |∑ h ∈ Icc 1 H, _| ≤ M⁻¹ * ∑ _h ∈ Icc 1 H, (ε' + ε') := by
          gcongr
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun h hh => ?_)
          rw [show ∀ a b x y : ℝ, a + b - (x + y) = (a - x) + (b - y) by intros; ring]
          exact (abs_add_le _ _).trans (add_le_add (hX0 h hh n h) (hX0 h hh n ((m - 1) * h)))
      _ = ε / 3 := by
          rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
          simp only [add_tsub_cancel_right, ε']
          field_simp
          ring
  calc |upwardModeRow φ c N m n - shellCorrection φ c m * ramanujanLagCoefficient m n|
      ≤ |upwardModeRow φ c N m n - upwardModel φ c N m H n| +
          |upwardModel φ c N m H n - shellCorrection φ c m * ramanujanLagCoefficient m n| :=
        abs_sub_le _ _ _
    _ ≤ ε := by linarith

/-- **Rows near the horizon** are uniformly bounded once `N/n` is bounded. -/
theorem exists_upwardModeRow_bound {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) (m J : ℕ) :
    ∃ B : ℝ, ∀ᶠ N : ℕ in atTop, ∀ n ∈ Icc 1 N, N < J * n →
      |upwardModeRow φ c N m n - shellCorrection φ c m * ramanujanLagCoefficient m n| ≤ B := by
  obtain ⟨ℓ, hℓ, hGl⟩ := exists_shellAutocorr_lipschitz hφ hsupp
  set M := ∫ u, φ u ^ 2 with hMdef
  set H := upwardWindow c
  set C : ℝ := (m.totient : ℝ)
  set E := upwardLinearError φ c ℓ H
  set W := Real.log (2 / min 1 (1 / (2 * c))) + mertensWindowConstant
  set S := ∑ k ∈ Icc 1 J, (Λ k : ℝ) / k
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have hint : ∀ᶠ N : ℕ in atTop, H * C * (2 * E / (M * N)) * W < 1 := by
    have h := (tendsto_order.1 (tendsto_const_div_atTop_nhds_zero_nat (H * C * 2 * E * W / M))).2
      1 one_pos
    filter_upwards [h] with N hN
    have heq : H * C * (2 * E / (M * N)) * W = H * C * 2 * E * W / M / N := by ring
    rw [heq]; exact hN
  refine ⟨1 + 3 * H * C * (2 * H * 4) + 2 * H * C * S + |shellCorrection φ c m| * C, ?_⟩
  filter_upwards [hint, eventually_ge_atTop ⌈4 * c * H⌉₊, eventually_ge_atTop (2 * H)]
    with N hNint hN4 hN2 n hn hJn
  have hN4' : 4 * c * H ≤ N := Nat.ceil_le.mp hN4
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set X : ℝ := (N : ℝ) / n with hXdef
  have hX1 : 1 ≤ X := by rw [hXdef, le_div_iff₀ hn0, one_mul]; exact_mod_cast hnN
  have hrow : |upwardModeRow φ c N m n - upwardModel φ c N m H n| ≤
      H * C * (2 * E / (M * N)) * W + 3 * H * C * (2 * H * (2 * Real.log (2 * X) / X)) :=
    abs_upwardModeRow_sub_model_le_log hφ hsupp hM hc hℓ hGl hN4' hN2 hn
  have hlog : 2 * Real.log (2 * X) / X ≤ 4 := by
    rw [div_le_iff₀ (by linarith)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * X by linarith)
    linarith
  have hbd : 3 * H * C * (2 * H * (2 * Real.log (2 * X) / X)) ≤ 3 * H * C * (2 * H * 4) := by
    gcongr
  -- the model is bounded through the bounded prime-power range
  have hmodel : |upwardModel φ c N m H n| ≤ 2 * H * C * S := by
    unfold upwardModel
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hsub : Icc 1 (N / n) ⊆ Icc 1 J := by
      intro k hk
      rw [mem_Icc] at hk ⊢
      have : N / n < J := (Nat.div_lt_iff_lt_mul hn1).mpr hJn
      omega
    calc ∑ k ∈ Icc 1 (N / n), |(Λ k : ℝ) / k * upwardShellModel φ c N m H (k * n)|
        ≤ ∑ k ∈ Icc 1 (N / n), (Λ k : ℝ) / k * (2 * H * C) := by
          refine sum_le_sum fun k _ => ?_
          rw [abs_mul, abs_of_nonneg (vonMangoldt_div_nonneg k)]
          exact mul_le_mul_of_nonneg_left (abs_upwardShellModel_le hφ hsupp hM _ _ _ _)
            (vonMangoldt_div_nonneg k)
      _ ≤ ∑ k ∈ Icc 1 J, (Λ k : ℝ) / k * (2 * H * C) :=
          sum_le_sum_of_subset_of_nonneg hsub fun k _ _ =>
            mul_nonneg (vonMangoldt_div_nonneg k) (by positivity)
      _ = 2 * H * C * S := by rw [← sum_mul]; ring
  have hκ : |shellCorrection φ c m * ramanujanLagCoefficient m n| ≤ |shellCorrection φ c m| * C := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m n) (abs_nonneg _)
  calc |upwardModeRow φ c N m n - shellCorrection φ c m * ramanujanLagCoefficient m n|
      ≤ |upwardModeRow φ c N m n - upwardModel φ c N m H n| + |upwardModel φ c N m H n| +
          |shellCorrection φ c m * ramanujanLagCoefficient m n| := by
        have := abs_sub_le (upwardModeRow φ c N m n) (upwardModel φ c N m H n)
          (shellCorrection φ c m * ramanujanLagCoefficient m n)
        have := abs_sub (upwardModel φ c N m H n) (shellCorrection φ c m * ramanujanLagCoefficient m n)
        linarith
    _ ≤ _ := by linarith

/-- The squared row defect in mode coordinates. -/
theorem upwardRow_defect_sq_eq {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) {N n : ℕ} (hN : 2 ≤ N) (hn : n ∈ Icc 1 N) :
    (upwardPrimeRow (atomDilate φ (c / N)) N
          (primeHorizonExtension (normalizedRamanujanHorizonVector m N)) n /
          (∫ u, atomDilate φ (c / N) u ^ 2) -
        shellCorrection φ c m * primeHorizonExtension (normalizedRamanujanHorizonVector m N) n) ^ 2 =
      (upwardModeRow φ c N m n - shellCorrection φ c m * ramanujanLagCoefficient m n) ^ 2 /
        (n * Real.log N * m.totient) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hφm : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hsn := Real.sqrt_pos.mpr hn0
  have hsL := Real.sqrt_pos.mpr hlogN
  have hsφ := Real.sqrt_pos.mpr hφm
  rw [upwardPrimeRow_normalizedRamanujan_eq hφ hsupp hM hc hm hN hn,
    primeHorizonExtension_normalizedRamanujan hn, ramanujanPoleProfile,
    normalizedRamanujanMode_eq_coefficient hm]
  have heq : upwardModeRow φ c N m n / (Real.sqrt n * Real.sqrt (Real.log N) * Real.sqrt m.totient) -
      shellCorrection φ c m * ((Real.sqrt (Real.log N))⁻¹ *
        (ramanujanLagCoefficient m n / Real.sqrt m.totient / Real.sqrt n)) =
      (upwardModeRow φ c N m n - shellCorrection φ c m * ramanujanLagCoefficient m n) /
        (Real.sqrt n * Real.sqrt (Real.log N) * Real.sqrt m.totient) := by
    field_simp
  rw [heq, div_pow, mul_pow, mul_pow, Real.sq_sqrt hn0.le, Real.sq_sqrt hlogN.le,
    Real.sq_sqrt hφm.le]

/-- **The upward rows carry the shell correction.** On the normalized Ramanujan mode of
conductor `m`, the upward non-ratio prime rows at overlap `c` converge in `ℓ²` to `κ_m(c)` times
the mode. -/
theorem tendsto_sum_sq_upwardPrimeRow_sub_shellCorrection {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
      (upwardPrimeRow (atomDilate φ (c / N)) N
          (primeHorizonExtension (normalizedRamanujanHorizonVector m N)) n /
          (∫ u, atomDilate φ (c / N) u ^ 2) -
        shellCorrection φ c m * primeHorizonExtension (normalizedRamanujanHorizonVector m N) n) ^ 2)
      atTop (𝓝 0) := by
  have hφm : (1 : ℝ) ≤ m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun N =>
    lt_of_lt_of_le ha (sum_nonneg fun n _ => sq_nonneg _), fun δ hδ => ?_⟩
  set ε := min 1 (δ / 8)
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hε2 : ε ^ 2 ≤ δ / 8 := by
    have h1 : ε ≤ 1 := min_le_left _ _
    have h2 : ε ≤ δ / 8 := min_le_right _ _
    nlinarith
  obtain ⟨J, hJ, hnear⟩ := exists_upwardModeRow_near_shellCorrection hφ hsupp hM hc hm hε
  obtain ⟨B, hfar⟩ := exists_upwardModeRow_bound hφ hsupp hM hc m J
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (max 1 (4 * B ^ 2 * J / δ + 1))
  filter_upwards [hnear, hfar, hlog, eventually_ge_atTop 2] with N hN1 hN2 hNlog hN
  have hNlog' : max 1 (4 * B ^ 2 * J / δ + 1) ≤ Real.log N := hNlog
  set L := Real.log N
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hNlog'
  have hLB : 4 * B ^ 2 * J / δ + 1 ≤ L := (le_max_right _ _).trans hNlog'
  have hL0 : 0 < L := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  -- pointwise bound on each row
  have hpt : ∀ n ∈ Icc 1 N,
      (upwardModeRow φ c N m n - shellCorrection φ c m * ramanujanLagCoefficient m n) ^ 2 /
        (n * L * m.totient) ≤ ε ^ 2 / L * (1 / n) + B ^ 2 * J / L / N := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    set D := upwardModeRow φ c N m n - shellCorrection φ c m * ramanujanLagCoefficient m n
    have hden : n * L ≤ n * L * m.totient := le_mul_of_one_le_right (by positivity) hφm
    by_cases hJn : J * n ≤ N
    · have hD : D ^ 2 ≤ ε ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hN1 n hn hJn) 2
      have h1 : D ^ 2 / (n * L * m.totient) ≤ ε ^ 2 / (n * L) :=
        div_le_div₀ (by positivity) hD (by positivity) hden
      have h2 : 0 ≤ B ^ 2 * J / L / N := by positivity
      have h3 : ε ^ 2 / (n * L) = ε ^ 2 / L * (1 / n) := by field_simp
      linarith
    · have hJn' : N < J * n := by omega
      have hD : D ^ 2 ≤ B ^ 2 := by
        have h := hN2 n hn hJn'
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
      have hnJ : (N : ℝ) < J * n := by exact_mod_cast hJn'
      have h1 : D ^ 2 / (n * L * m.totient) ≤ B ^ 2 / (n * L) :=
        div_le_div₀ (sq_nonneg B) hD (by positivity) hden
      have h2 : B ^ 2 / (n * L) ≤ B ^ 2 * J / L / N := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have : 0 ≤ B ^ 2 * L := by positivity
        nlinarith
      have h3 : 0 ≤ ε ^ 2 / L * (1 / n) := by positivity
      linarith
  calc ∑ n ∈ Icc 1 N, _ = ∑ n ∈ Icc 1 N,
        (upwardModeRow φ c N m n - shellCorrection φ c m * ramanujanLagCoefficient m n) ^ 2 /
          (n * L * m.totient) :=
        sum_congr rfl fun n hn => upwardRow_defect_sq_eq hφ hsupp hM hc hm hN hn
    _ ≤ ∑ n ∈ Icc 1 N, (ε ^ 2 / L * (1 / n) + B ^ 2 * J / L / N) := sum_le_sum hpt
    _ = ε ^ 2 / L * ∑ n ∈ Icc 1 N, (1 / (n : ℝ)) + B ^ 2 * J / L := by
        rw [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp only [add_tsub_cancel_right]
        field_simp
    _ ≤ ε ^ 2 / L * (1 + L) + B ^ 2 * J / L := by
        gcongr
        exact RHTower.harmonic_Icc_le_one_add_log N (by omega)
    _ < δ := by
        have h1 : ε ^ 2 / L * (1 + L) ≤ 2 * ε ^ 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hL0]; nlinarith [sq_nonneg ε]
        have h2 : B ^ 2 * J / L ≤ δ / 4 := by
          rw [div_le_iff₀ hL0]
          have h3 : 4 * B ^ 2 * J / δ ≤ L := by linarith
          rw [div_le_iff₀ hδ] at h3
          nlinarith
        linarith

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
