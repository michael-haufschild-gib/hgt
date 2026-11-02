import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAliasingIsCoercive
import GaloisForLFunctions.ArithmeticDegenerationTheory.TheTiltedSplineHasARegularTail

/-!
# The energy of a horizon block

The total energy of a horizon block against the atom spectrum,
`E_N = ∫ |φ̂(wτ)|² |D_x(τ)|²/N dτ`, `w = c/N`, is computed exactly up to `O(c/N)`:

* **Plancherel** (`blockEnergy_eq`): `E_N = (2π/c) Σ_{m,n ≤ N} x_m x_n G(N log(m/n)/c)`, with
  `G(t) = ∫ φ(u) φ(u + t) du` the autocorrelation of the profile.
* **Poisson** (`tsum_shellAutocorr_eq`): on the lattice `ℤ/a`,
  `Σ_j G(j/a) = a ((∫φ)² + 2 a_φ(a))`, where the **aliasing density**
  `a_φ(s) = Σ_{k ≥ 1} |φ̂(2πks)|²` collects the harmonics of the atom grid.
* **Linearization** (`abs_row_sub_le`): `N log(m/n)/c` differs from `(m − n)/a_n`, `a_n = cn/N`,
  by `O(c/N)` on the `O(c)` neighbours of `n` that the autocorrelation sees, and the weights
  `x_m = k(log(m/N))/√N` vary by `O(c N^{−3/2})` there.

Together (`abs_blockEnergy_sub_le`):

`E_N = 2π (∫φ)² N⁻¹ Σ_n h(log(n/N))² + 2π 𝒜_N + O(c/N)`,
`𝒜_N = (2/N) Σ_n h(log(n/N))² a_φ(cn/N)`.

The first term is the Riemann sum of the synthesized test `∫ H²`; the second is the aliasing of
the block: at depth `y = log(n/N)` the atoms have local overlap `c e^y`, and every harmonic `k ≥ 1`
of their grid contributes `|φ̂(2πk c e^y)|²`.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ h : ℝ → ℝ} {A : ℝ}

/-- The aliasing density `a_φ(s) = Σ_{k ≥ 1} |φ̂(2πks)|²` of the atom grid at overlap `s`. -/
def aliasDensity (φ : ℝ → ℝ) (s : ℝ) : ℝ := ∑' k : ℕ, shellSpectrum φ ((k + 1) * s)

/-- The energy `E_N = ∫ |φ̂(wτ)|² |D_x(τ)|²/N dτ` of a horizon block, `w = c/N`. -/
def blockEnergy (φ h : ℝ → ℝ) (c : ℝ) (N : ℕ) : ℝ :=
  ∫ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
    (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N)

/-- The aliasing functional `𝒜_N = (2/N) Σ_{n ≤ N} h(log(n/N))² a_φ(cn/N)` of a horizon block. -/
def horizonAlias (φ h : ℝ → ℝ) (c : ℝ) (N : ℕ) : ℝ :=
  2 / N * ∑ n ∈ Icc 1 N, h (Real.log n - Real.log N) ^ 2 * aliasDensity φ (c * n / N)

/-- The tapered profile `k(y) = e^{−y/2} h(y)`, so that `x_m = k(log(m/N))/√N`. -/
def taperedProfile (h : ℝ → ℝ) (y : ℝ) : ℝ := Real.exp (-(y / 2)) * h y

/-! ### Plancherel -/

theorem bumpCorr_atomDilate_eq' {w : ℝ} (hw : 0 < w) (s : ℝ) :
    bumpCorr (atomDilate φ w) s = w * shellAutocorr φ (s / w) := by
  have h := Measure.integral_comp_div (fun y => φ y * φ (y + s / w)) w
  simp only [smul_eq_mul, abs_of_pos hw] at h
  unfold bumpCorr atomDilate
  rw [show (fun v => φ (v / w) * φ ((v + s) / w)) = fun v => φ (v / w) * φ (v / w + s / w) from
    funext fun v => by rw [add_div], h]
  rfl

/-- **Plancherel for a horizon block**: `E_N = (2π/c) Σ_{m,n} x_m x_n G(N log(m/n)/c)`. -/
theorem blockEnergy_eq (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (h : ℝ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    blockEnergy φ h c N = 2 * Real.pi / c * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      horizonWeights h N m * horizonWeights h N n *
        shellAutocorr φ (N * (Real.log m - Real.log n) / c) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  set T := centredHorizonTest φ h c N with hT
  have hT2 : ContDiff ℝ 2 (cx T) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_centredHorizonTest hφ h c N)
  have hTc : HasCompactSupport (cx T) :=
    (hasCompactSupport_centredHorizonTest hφsupp h hc hN).comp_left Complex.ofReal_zero
  have hpl := RHTower.LebesgueAtomWeil.integral_norm_sq_paperFT_eq hT2 hTc
  have hint : ∀ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
      (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N) =
        ((c / N) ^ 2 * N)⁻¹ * ‖paperFT (cx T) τ‖ ^ 2 := by
    intro τ
    rw [hT, norm_sq_paperFT_centredHorizonTest hφ.continuous hφc h hc hN τ]
    field_simp
  have hsq : ∫ r : ℝ, ‖paperFT (cx T) r‖ ^ 2 = 2 * Real.pi * ∫ u, T u ^ 2 := by
    have e : ∫ u : ℝ, ‖cx T u‖ ^ 2 = ∫ u, T u ^ 2 := by
      congr 1; funext u; simp [cx, Complex.norm_real, sq_abs]
    rw [← e, ← hpl]
    field_simp
  set g := atomDilate φ (c / N) with hg
  have hgcont : Continuous g := hφ.continuous.comp (continuous_id.div_const _)
  have hgc : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_Icc (a := 0) (b := c / N)) fun u hu => ?_
    simp only [hg, atomDilate]
    refine hφsupp _ fun hm => hu ?_
    obtain ⟨h0, h1⟩ := hm
    exact ⟨by rw [le_div_iff₀ hw, zero_mul] at h0; exact h0,
      by rw [div_le_one hw] at h1; exact h1⟩
  have htr : ∫ u, T u ^ 2 =
      ∫ u, atomicTest N (horizonWeights h N) g u * atomicTest N (horizonWeights h N) g (u + 0) := by
    have := integral_add_right_eq_self (μ := volume)
      (fun u => atomicTest N (horizonWeights h N) g u ^ 2) (Real.log N)
    simp only [hT, centredHorizonTest, add_zero, ← hg]
    rw [this]
    congr 1; funext u; ring
  unfold blockEnergy
  simp_rw [hint]
  rw [integral_const_mul, hsq, htr, integral_atomicTest_mul_shift hgcont hgc N _ 0, ← mul_assoc,
    mul_sum, mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [hg, bumpCorr_atomDilate_eq' hw]
  have e : (0 - (Real.log n - Real.log m)) / (c / N) = N * (Real.log m - Real.log n) / c := by
    field_simp; ring
  rw [e]
  field_simp

/-! ### Poisson summation on the atom grid -/

/-- **Poisson on the lattice `ℤ/a`**: the harmonics `k ≥ 1` sum to the aliasing density and
`Σ_j G(j/a) = a ((∫φ)² + 2 a_φ(a))`. -/
theorem hasSum_aliasDensity (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {a : ℝ} (ha : 0 < a) :
    HasSum (fun k : ℕ => shellSpectrum φ ((k + 1) * a)) (aliasDensity φ a) ∧
      ∑' m : ℤ, shellAutocorr φ (m * a⁻¹) = a * ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ a) := by
  have h1 := (hasSum_shellSpectrum_int hφ hφsupp ha).nat_add_neg
  have hev : ∀ n : ℕ, shellSpectrum φ ((n : ℤ) * a) + shellSpectrum φ (((-(n : ℤ) : ℤ) : ℝ) * a) =
      2 * shellSpectrum φ (n * a) := by
    intro n
    rw [Int.cast_neg, neg_mul, shellSpectrum_neg, Int.cast_natCast]
    ring
  simp_rw [hev] at h1
  rw [Int.cast_zero, zero_mul, shellSpectrum_zero] at h1
  have h2 := h1.div_const 2
  simp_rw [mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℝ) ≠ 0)] at h2
  have h3 := (hasSum_nat_add_iff' 1).mpr h2
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul,
    shellSpectrum_zero, Nat.cast_add, Nat.cast_one] at h3
  set S := a⁻¹ * ∑' m : ℤ, shellAutocorr φ (m * a⁻¹) with hS
  have hA : aliasDensity φ a = (S - (∫ u, φ u) ^ 2) / 2 := by
    rw [aliasDensity, h3.tsum_eq]; ring
  refine ⟨?_, ?_⟩
  · rw [hA]
    have e : (S - (∫ u, φ u) ^ 2) / 2 = (S + (∫ u, φ u) ^ 2) / 2 - (∫ u, φ u) ^ 2 := by ring
    rw [e]
    exact h3
  · rw [hA]
    have : ∑' m : ℤ, shellAutocorr φ (m * a⁻¹) = a * S := by
      rw [hS, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
    rw [this]
    ring

theorem tsum_shellAutocorr_eq (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {a : ℝ} (ha : 0 < a) :
    ∑' m : ℤ, shellAutocorr φ (m * a⁻¹) = a * ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ a) :=
  (hasSum_aliasDensity hφ hφsupp ha).2

theorem aliasDensity_nonneg (s : ℝ) : 0 ≤ aliasDensity φ s :=
  tsum_nonneg fun _ => shellSpectrum_nonneg _

/-! ### The weights in logarithmic coordinates -/

theorem horizonWeights_eq_tapered (h : ℝ → ℝ) {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m) :
    horizonWeights h N m = taperedProfile h (Real.log m - Real.log N) / Real.sqrt N := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : ∀ x : ℝ, 0 < x → Real.sqrt x = Real.exp (Real.log x / 2) := fun x hx => by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]; ring_nf
  unfold horizonWeights taperedProfile
  rw [hs _ hm0, hs _ hN0]
  have e : Real.exp (-((Real.log m - Real.log N) / 2)) * Real.exp (Real.log m / 2) =
      Real.exp (Real.log N / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  field_simp
  rw [mul_assoc, mul_comm (Real.exp (Real.log m / 2)), e]

theorem taperedProfile_eq_zero (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {y : ℝ}
    (hy : y ∉ Set.Icc (-A) 0) : taperedProfile h y = 0 := by
  rw [taperedProfile, hsupp y hy, mul_zero]

theorem contDiff_taperedProfile (hh : ContDiff ℝ 2 h) : ContDiff ℝ 2 (taperedProfile h) :=
  (Real.contDiff_exp.comp ((contDiff_id.div_const 2).neg)).mul hh

/-! ### Linearization of one row -/

/-- Counting the neighbours `|m − n| ≤ 2a` of `n`. -/
theorem card_filter_near_le (n K : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    ((Icc 1 (2 * K)).filter fun m : ℕ => |(m : ℝ) - n| ≤ 2 * a).card ≤ 4 * a + 1 := by
  set J := ⌊2 * a⌋₊ with hJ
  have hsub : (Icc 1 (2 * K)).filter (fun m : ℕ => |(m : ℝ) - n| ≤ 2 * a) ⊆ Icc (n - J) (n + J) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨-, hm⟩ := hm
    rw [abs_le] at hm
    rw [Finset.mem_Icc]
    constructor
    · rcases le_or_gt n m with hnm | hnm
      · omega
      · have h1 : ((n - m : ℕ) : ℝ) ≤ 2 * a := by
          rw [Nat.cast_sub hnm.le]; linarith [hm.1]
        have h2 : n - m ≤ J := Nat.le_floor h1
        omega
    · rcases le_or_gt m n with hnm | hnm
      · omega
      · have h1 : ((m - n : ℕ) : ℝ) ≤ 2 * a := by
          rw [Nat.cast_sub hnm.le]; linarith [hm.2]
        have h2 : m - n ≤ J := Nat.le_floor h1
        omega
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hJle : (J : ℝ) ≤ 2 * a := Nat.floor_le (by linarith)
  have : ((n + J + 1 - (n - J) : ℕ) : ℝ) ≤ 2 * J + 1 := by
    have : n + J + 1 - (n - J) ≤ 2 * J + 1 := by omega
    exact_mod_cast this
  calc (((Icc 1 (2 * K)).filter fun m : ℕ => |(m : ℝ) - n| ≤ 2 * a).card : ℝ)
      ≤ ((n + J + 1 - (n - J) : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ 2 * J + 1 := this
    _ ≤ 4 * a + 1 := by linarith

/-- `|log(1 + t) − t| ≤ 2t²` for `|t| ≤ 1/2`. -/
theorem abs_log_one_add_sub_le {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |Real.log (1 + t) - t| ≤ 2 * t ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(-t)| < 1 by rw [abs_neg]; linarith) 1
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_add, pow_one, div_one,
    sub_neg_eq_add, abs_neg] at h
  have e : -t + Real.log (1 + t) = Real.log (1 + t) - t := by ring
  rw [e, show (0 : ℕ) + 1 + 1 = 2 by rfl] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith), sq_abs]
  nlinarith [sq_nonneg t]

/-- One entry of a row: either both sides vanish, or the difference is `O(c N^{−3/2})`. -/
theorem abs_entry_le {k G : ℝ → ℝ} {Bk Lk BG LG : ℝ} (hk : ∀ y, |k y| ≤ Bk)
    (hkL : ∀ u v, |k u - k v| ≤ Lk * |u - v|) (hG : ∀ t, |G t| ≤ BG)
    (hGL : ∀ s t, |G s - G t| ≤ LG * |s - t|) (hG1 : ∀ t, 1 ≤ |t| → G t = 0)
    (hLk : 0 ≤ Lk) (hBk : 0 ≤ Bk) (hLG : 0 ≤ LG) (hBG : 0 ≤ BG)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hcN : 4 * c ≤ N) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    |k (Real.log m - Real.log N) / Real.sqrt N * G (N * (Real.log m - Real.log n) / c) -
        k (Real.log n - Real.log N) / Real.sqrt N * G (((m : ℝ) - n) * (c * n / N)⁻¹)| ≤
      if |(m : ℝ) - n| ≤ 2 * (c * n / N) then (Lk * BG + 8 * Bk * LG) * c / (N * Real.sqrt N)
      else 0 := by
  have hN0 : (0 : ℝ) < N := by
    have : (0 : ℝ) < 4 * c := by linarith
    linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  set a := c * n / N with ha
  have ha0 : 0 < a := by positivity
  have hcN' : c / N ≤ 1 / 4 := by rw [div_le_iff₀ hN0]; linarith
  set u := N * (Real.log m - Real.log n) / c with hu
  set v := ((m : ℝ) - n) * a⁻¹ with hv
  -- support of the first autocorrelation
  have hnear : |u| < 1 → |(m : ℝ) - n| < 2 * a := by
    intro hu1
    have hl : |Real.log m - Real.log n| < c / N := by
      rw [hu, abs_div, abs_mul, abs_of_pos hN0, abs_of_pos hc, div_lt_one hc] at hu1
      rw [lt_div_iff₀ hN0]; linarith
    have hl1 : |Real.log m - Real.log n| ≤ 1 := by linarith
    have he := Real.abs_exp_sub_one_le hl1
    rw [Real.exp_sub, Real.exp_log hm0, Real.exp_log hn0] at he
    have : |(m : ℝ) / n - 1| = |(m : ℝ) - n| / n := by
      rw [div_sub_one hn0.ne', abs_div, abs_of_pos hn0]
    rw [this, div_le_iff₀ hn0] at he
    have : 2 * |Real.log m - Real.log n| * n < 2 * (c / N) * n := by
      have := mul_lt_mul_of_pos_right hl hn0; linarith
    calc |(m : ℝ) - n| ≤ 2 * |Real.log m - Real.log n| * n := he
      _ < 2 * (c / N) * n := this
      _ = 2 * a := by rw [ha]; ring
  split_ifs with hmn
  · -- the two pieces
    have hsplit : k (Real.log m - Real.log N) / Real.sqrt N * G u -
        k (Real.log n - Real.log N) / Real.sqrt N * G v =
        (k (Real.log m - Real.log N) - k (Real.log n - Real.log N)) / Real.sqrt N * G u +
          k (Real.log n - Real.log N) / Real.sqrt N * (G u - G v) := by ring
    rw [hsplit]
    have hp1 : |(k (Real.log m - Real.log N) - k (Real.log n - Real.log N)) / Real.sqrt N * G u| ≤
        Lk * BG * c / (N * Real.sqrt N) := by
      by_cases hu1 : |u| < 1
      · have hl : |Real.log m - Real.log n| ≤ c / N := by
          rw [hu, abs_div, abs_mul, abs_of_pos hN0, abs_of_pos hc, div_lt_one hc] at hu1
          rw [le_div_iff₀ hN0]; linarith
        have hkd := hkL (Real.log m - Real.log N) (Real.log n - Real.log N)
        rw [show Real.log m - Real.log N - (Real.log n - Real.log N) =
          Real.log m - Real.log n by ring] at hkd
        rw [abs_mul, abs_div, abs_of_pos hsN]
        calc |k (Real.log m - Real.log N) - k (Real.log n - Real.log N)| / Real.sqrt N * |G u|
            ≤ Lk * (c / N) / Real.sqrt N * BG := by
              refine mul_le_mul (div_le_div_of_nonneg_right (hkd.trans
                (mul_le_mul_of_nonneg_left hl hLk)) hsN.le) (hG u) (abs_nonneg _) (by positivity)
          _ = Lk * BG * c / (N * Real.sqrt N) := by field_simp
      · rw [hG1 u (not_lt.mp hu1), mul_zero, abs_zero]; positivity
    have hp2 : |k (Real.log n - Real.log N) / Real.sqrt N * (G u - G v)| ≤
        8 * Bk * LG * c / (N * Real.sqrt N) := by
      set t := ((m : ℝ) - n) / n with ht
      have ht2 : |t| ≤ 2 * (c / N) := by
        rw [ht, abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
        calc |(m : ℝ) - n| ≤ 2 * a := hmn
          _ = 2 * (c / N) * n := by rw [ha]; ring
      have ht1 : |t| ≤ 1 / 2 := by linarith
      have hlog : Real.log m - Real.log n = Real.log (1 + t) := by
        rw [← Real.log_div hm0.ne' hn0.ne', ht]
        congr 1; field_simp; ring
      have huv : |u - v| ≤ 8 * c / N := by
        have e : u - v = N / c * (Real.log (1 + t) - t) := by
          rw [hu, hv, hlog, ha, ht]; field_simp
        rw [e, abs_mul, abs_of_pos (div_pos hN0 hc)]
        have hb := abs_log_one_add_sub_le ht1
        have ht2' : t ^ 2 ≤ (2 * (c / N)) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ht2 2
        calc N / c * |Real.log (1 + t) - t| ≤ N / c * (2 * (2 * (c / N)) ^ 2) :=
              mul_le_mul_of_nonneg_left (hb.trans (by linarith)) (by positivity)
          _ = 8 * c / N := by field_simp; ring
      rw [abs_mul, abs_div, abs_of_pos hsN]
      calc |k (Real.log n - Real.log N)| / Real.sqrt N * |G u - G v|
          ≤ Bk / Real.sqrt N * (LG * (8 * c / N)) :=
            mul_le_mul (div_le_div_of_nonneg_right (hk _) hsN.le)
              ((hGL u v).trans (mul_le_mul_of_nonneg_left huv hLG)) (abs_nonneg _) (by positivity)
        _ = 8 * Bk * LG * c / (N * Real.sqrt N) := by field_simp
    calc _ ≤ |(k (Real.log m - Real.log N) - k (Real.log n - Real.log N)) / Real.sqrt N * G u| +
          |k (Real.log n - Real.log N) / Real.sqrt N * (G u - G v)| := abs_add_le _ _
      _ ≤ Lk * BG * c / (N * Real.sqrt N) + 8 * Bk * LG * c / (N * Real.sqrt N) := add_le_add hp1 hp2
      _ = (Lk * BG + 8 * Bk * LG) * c / (N * Real.sqrt N) := by ring
  · -- far from `n` both autocorrelations vanish
    have hGu : G u = 0 := hG1 u (not_lt.mp fun h => hmn (hnear h).le)
    have hGv : G v = 0 := by
      refine hG1 v ?_
      rw [hv, abs_mul, abs_inv, abs_of_pos ha0, le_mul_inv_iff₀ ha0, one_mul]
      push Not at hmn
      linarith
    rw [hGu, hGv, mul_zero, mul_zero, sub_zero, abs_zero]

/-- **One row**: `Σ_m x_m G(N log(m/n)/c) = x_n Σ_j G(j/a_n) + O(c² N^{−3/2})`, `a_n = cn/N`. -/
theorem abs_row_sub_le {k G : ℝ → ℝ} {Bk Lk BG LG : ℝ} (hk : ∀ y, |k y| ≤ Bk)
    (hkL : ∀ u v, |k u - k v| ≤ Lk * |u - v|) (hG : ∀ t, |G t| ≤ BG)
    (hGL : ∀ s t, |G s - G t| ≤ LG * |s - t|) (hG1 : ∀ t, 1 ≤ |t| → G t = 0)
    (hk0 : ∀ y, 0 < y → k y = 0) (hLk : 0 ≤ Lk) (hBk : 0 ≤ Bk) (hLG : 0 ≤ LG) (hBG : 0 ≤ BG)
    {c : ℝ} (hc : 1 ≤ c) {N : ℕ} (hcN : 4 * c ≤ N) {n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    |∑ m ∈ Icc 1 N, k (Real.log m - Real.log N) / Real.sqrt N *
        G (N * (Real.log m - Real.log n) / c) -
      k (Real.log n - Real.log N) / Real.sqrt N * ∑' j : ℤ, G (j * (c * n / N)⁻¹)| ≤
      5 * (Lk * BG + 8 * Bk * LG) * c ^ 2 / (N * Real.sqrt N) := by
  have hc0 : 0 < c := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  set a := c * n / N with ha
  have ha0 : 0 < a := by positivity
  have han : 4 * a ≤ n := by
    rw [ha, show 4 * (c * n / N) = 4 * c / N * n by ring]
    exact mul_le_of_le_one_left hn0.le ((div_le_one hN0).mpr hcN)
  have hac : a ≤ c := by
    rw [ha, div_le_iff₀ hN0]; exact mul_le_mul_of_nonneg_left hnN' hc0.le
  -- the lattice sum is a finite sum over `1 ≤ m ≤ 2N`
  have hlat : ∑' j : ℤ, G (j * a⁻¹) = ∑ m ∈ Icc 1 (2 * N), G (((m : ℝ) - n) * a⁻¹) := by
    rw [tsum_eq_sum (s := (Icc 1 (2 * N)).image (fun m : ℕ => (m : ℤ) - n))]
    · rw [Finset.sum_image]
      · refine sum_congr rfl fun m _ => ?_
        push_cast; rfl
      · intro x _ y _ hxy
        simp only at hxy
        omega
    · intro j hj
      apply hG1
      rw [abs_mul, abs_inv, abs_of_pos ha0, le_mul_inv_iff₀ ha0, one_mul]
      have hj' : ¬ (1 ≤ j + n ∧ j + n ≤ 2 * N) := by
        rintro ⟨h1, h2⟩
        apply hj
        rw [Finset.mem_image]
        exact ⟨(j + n).toNat, by rw [Finset.mem_Icc]; omega, by omega⟩
      rcases not_and_or.mp hj' with h | h
      · have : (j : ℝ) ≤ -n := by exact_mod_cast (by omega : j ≤ -(n : ℤ))
        rw [abs_of_neg (by linarith)]; linarith
      · have : (2 * N + 1 : ℝ) - n ≤ j := by
          exact_mod_cast (by omega : (2 * N + 1 : ℤ) - n ≤ j)
        rw [abs_of_pos (by linarith)]; linarith
  -- the row extends by zero to `1 ≤ m ≤ 2N`
  have hrow : ∑ m ∈ Icc 1 N, k (Real.log m - Real.log N) / Real.sqrt N *
      G (N * (Real.log m - Real.log n) / c) = ∑ m ∈ Icc 1 (2 * N),
        k (Real.log m - Real.log N) / Real.sqrt N * G (N * (Real.log m - Real.log n) / c) := by
    refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (by omega)) fun m hm hmN => ?_
    have hm1 : N < m := by
      rw [Finset.mem_Icc] at hm hmN; omega
    have hlog : 0 < Real.log m - Real.log N := by
      rw [sub_pos]; exact Real.log_lt_log hN0 (by exact_mod_cast hm1)
    rw [hk0 _ hlog, zero_div, zero_mul]
  rw [hlat, hrow, mul_sum, ← sum_sub_distrib]
  set X := (Lk * BG + 8 * Bk * LG) * c / (N * Real.sqrt N) with hX
  have hX0 : 0 ≤ X := by positivity
  have hterm : ∀ m ∈ Icc 1 (2 * N), |k (Real.log m - Real.log N) / Real.sqrt N *
      G (N * (Real.log m - Real.log n) / c) - k (Real.log n - Real.log N) / Real.sqrt N *
        G (((m : ℝ) - n) * a⁻¹)| ≤ if |(m : ℝ) - n| ≤ 2 * a then X else 0 := fun m hm =>
    abs_entry_le hk hkL hG hGL hG1 hLk hBk hLG hBG hc0 hcN hn (Finset.mem_Icc.mp hm).1
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hcard := card_filter_near_le n N ha0.le
  calc (((Icc 1 (2 * N)).filter fun m : ℕ => |(m : ℝ) - n| ≤ 2 * a).card : ℝ) * X
      ≤ (4 * a + 1) * X := mul_le_mul_of_nonneg_right hcard hX0
    _ ≤ 5 * c * X := mul_le_mul_of_nonneg_right (by linarith) hX0
    _ = 5 * (Lk * BG + 8 * Bk * LG) * c ^ 2 / (N * Real.sqrt N) := by rw [hX]; ring

/-! ### The energy of a horizon block -/

/-- **The energy of a horizon block**:
`E_N = 2π (∫φ)² N⁻¹ Σ_n h(log(n/N))² + 2π 𝒜_N + O(c/N)` for `1 ≤ c ≤ N/4`. -/
theorem abs_blockEnergy_sub_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 4 * c ≤ N →
      |blockEnergy φ h c N - (2 * Real.pi / N * (∫ u, φ u) ^ 2 *
          ∑ n ∈ Icc 1 N, h (Real.log n - Real.log N) ^ 2 + 2 * Real.pi * horizonAlias φ h c N)| ≤
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
  set X := 5 * (|Lk| * |BG| + 8 * |Bk| * (LG : ℝ)) with hX
  have hX0 : 0 ≤ X := by positivity
  refine ⟨2 * Real.pi * |Bk| * X, by positivity, fun c hc N hcN => ?_⟩
  have hc0 : 0 < c := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hN : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  rw [blockEnergy_eq hφ hφsupp h hc0 hN, Finset.sum_comm]
  -- each row against its Poisson value
  have hrow : ∀ n ∈ Icc 1 N, |∑ m ∈ Icc 1 N, horizonWeights h N m * horizonWeights h N n *
      shellAutocorr φ (N * (Real.log m - Real.log n) / c) -
        horizonWeights h N n * (horizonWeights h N n * (c * n / N) *
          ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (c * n / N)))| ≤
        |Bk| / Real.sqrt N * (X * c ^ 2 / (N * Real.sqrt N)) := by
    intro n hn
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hnN := (Finset.mem_Icc.mp hn).2
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hpoi := tsum_shellAutocorr_eq hφ hφsupp (a := c * n / N) (by positivity)
    have hr := abs_row_sub_le hkb hkL' hGb hGL hG1 hk0 (abs_nonneg _) (abs_nonneg _)
      (NNReal.coe_nonneg _) (abs_nonneg _) hc hcN hn1 hnN
    rw [hpoi] at hr
    have hxn : horizonWeights h N n = taperedProfile h (Real.log n - Real.log N) / Real.sqrt N :=
      horizonWeights_eq_tapered h hN hn1
    have hsum : ∑ m ∈ Icc 1 N, horizonWeights h N m * horizonWeights h N n *
        shellAutocorr φ (N * (Real.log m - Real.log n) / c) = horizonWeights h N n *
          ∑ m ∈ Icc 1 N, taperedProfile h (Real.log m - Real.log N) / Real.sqrt N *
            shellAutocorr φ (N * (Real.log m - Real.log n) / c) := by
      rw [mul_sum]
      refine sum_congr rfl fun m hm => ?_
      rw [horizonWeights_eq_tapered h hN (Finset.mem_Icc.mp hm).1]
      ring
    rw [hsum, ← mul_sub, abs_mul]
    have hxb : |horizonWeights h N n| ≤ |Bk| / Real.sqrt N := by
      rw [hxn, abs_div, abs_of_pos hsN]
      exact div_le_div_of_nonneg_right (hkb _) hsN.le
    rw [← hxn] at hr
    have hX' : 5 * (|Lk| * |BG| + 8 * |Bk| * (LG : ℝ)) * c ^ 2 / (N * Real.sqrt N) =
        X * c ^ 2 / (N * Real.sqrt N) := by rw [hX]
    rw [hX', ← mul_assoc (horizonWeights h N n)] at hr
    exact mul_le_mul hxb hr (abs_nonneg _) (by positivity)
  -- the Poisson values add up to the two terms
  have hmain : 2 * Real.pi / c * ∑ n ∈ Icc 1 N, horizonWeights h N n *
      (horizonWeights h N n * (c * n / N) * ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (c * n / N))) =
      2 * Real.pi / N * (∫ u, φ u) ^ 2 * ∑ n ∈ Icc 1 N, h (Real.log n - Real.log N) ^ 2 +
        2 * Real.pi * horizonAlias φ h c N := by
    unfold horizonAlias
    rw [mul_sum, mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hx2 : horizonWeights h N n * horizonWeights h N n =
        h (Real.log n - Real.log N) ^ 2 / n := by
      rw [horizonWeights, div_mul_div_comm, Real.mul_self_sqrt hn0.le, sq]
    rw [show horizonWeights h N n * (horizonWeights h N n * (c * n / N) *
        ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (c * n / N))) = horizonWeights h N n *
          horizonWeights h N n * (c * n / N) * ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (c * n / N))
        by ring, hx2]
    field_simp
  rw [← hmain, ← mul_sub, ← sum_sub_distrib, abs_mul,
    abs_of_pos (by positivity : 0 < 2 * Real.pi / c)]
  have hsumb := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hrow)
  rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hsumb
  calc 2 * Real.pi / c * |∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 N, horizonWeights h N m *
        horizonWeights h N n * shellAutocorr φ (N * (Real.log m - Real.log n) / c) -
          horizonWeights h N n * (horizonWeights h N n * (c * n / N) *
            ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (c * n / N))))|
      ≤ 2 * Real.pi / c * (N * (|Bk| / Real.sqrt N * (X * c ^ 2 / (N * Real.sqrt N)))) :=
        mul_le_mul_of_nonneg_left hsumb (by positivity)
    _ = 2 * Real.pi * |Bk| * X * c / N := by
        field_simp
        rw [Real.sq_sqrt hN0.le]
        ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
