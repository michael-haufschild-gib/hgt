import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSelfEnergyHasConstantOne

/-!
# The stability law reaches the spacing up to a logarithm

`TheSelfEnergyHasConstantOne` keeps only the shifts `s ≤ δ_N/2`, which separate the atoms, and
counts the self-energy relative to the spacing: `log(δ_N/w)`. This file keeps every shift
`s ∈ (w, 1]`. Then each atom has its full self-energy `log(1/w)`, and the atoms interact through the
archimedean place.

For an atomic test `f = Σ_{n ≤ N} x_n g(· − log n)`, `g` supported in `[0, w]`, `w ≤ δ_N/4`:

* **Shift expansion** (`integral_sub_shift_sq`): `∫ (f − f(· + s))² = 2∫f² − 2 Σ_{m,n} x_m x_n c_{mn}(s)`
  with the bump pairings `c_{mn}(s) = ∫ g(u − log m) g(u + s − log n) du`
  (`bumpPairing`, `abs_bumpPairing_le`, `bumpPairing_eq_zero`): `|c_{mn}| ≤ ∫ g²`, and
  `c_{mn}(s) = 0` unless `|s − log(n/m)| ≤ w`.
* **The Lévy density** (`archLevyDensity_le`, `archLevyDensity_ge_sub`):
  `1/(2s) − 1/4 ≤ ω(s) ≤ 1/(2s) + 1`.
* **The cross terms** (`archLevyDensity_mul_cross_le`, `integral_crossMajorant_le`): at shift `s` only
  pairs with `log(n/m) ∈ [s − w, s + w]` meet, with weight `ω(s) ≤ 2/(3 log(n/m)) + 1`; integrated over
  `s` each pair costs `2w`.
* **The Hilbert-type row bound** (`abs_sub_div_le_abs_log_sub`, `sum_erase_inv_abs_sub_le`,
  `sum_crossCoeff_le`): `|log n − log m| ≥ |n − m|/N`, so the cross kernel has rows
  `≤ N((4/3)H_N + 1)`.
* **The Lévy energy with interaction** (`levyEnergy_atomicTest_ge_cross`):
  `levyEnergy f ≥ (log(1/w) − 1/2 − 4wN((4/3)H_N + 1)) ∫ f²`.
* **The stability law at the spacing over a logarithm** (`markovEnergy_atomicTest_ge_cross`,
  `markovEnergy_atomicTest_nonneg_logSpacing`): the Markov form of every atomic test of width
  `w ≤ e^{−C₁}/(N(1 + log N))` is nonnegative, `C₁ = 29/2 + log 4 + 2|θ′(0)|`.

So the archimedean place pays the prime place down to width `δ_N/(C log N)`. The self-energy
`log(1/w) = log N + log log N + O(1)` beats the covariant counterterm `log N + O(1)` with a margin
`log log N`, while the interaction of distinct atoms, a Hilbert-type kernel `w/|log n − log m|`, has
norm `O(wN log N) = O(1)`. At width `c δ_N` the same kernel has norm `≍ c log N`, the order of the
counterterm: from there on the interaction of the atoms, the pole and the prime form must be
weighed together.
-/

noncomputable section

open MeasureTheory Finset RHTower
open scoped Real

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.ArithmeticElectrostatics GaloisForLFunctions.ArithmeticEffectivityTheory

/-! ### The Lévy density -/

/-- `ω(s) ≤ 1/(2s) + 1`, from `1 − e^{−2s} ≥ 2s/(1 + 2s)`. -/
theorem archLevyDensity_le {s : ℝ} (hs : 0 < s) : archLevyDensity s ≤ 1 / (2 * s) + 1 := by
  have hE := Real.add_one_le_exp (2 * s)
  have he : Real.exp (-2 * s) * Real.exp (2 * s) = 1 := by rw [← Real.exp_add]; simp
  have hden : 2 * s / (1 + 2 * s) ≤ 1 - Real.exp (-2 * s) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hE (Real.exp_pos (-2 * s)).le]
  have hpos : 0 < 2 * s / (1 + 2 * s) := by positivity
  have h1 : Real.exp (-s / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  unfold archLevyDensity
  calc Real.exp (-s / 2) / (1 - Real.exp (-2 * s))
      ≤ 1 / (1 - Real.exp (-2 * s)) := div_le_div_of_nonneg_right h1 (by linarith)
    _ ≤ 1 / (2 * s / (1 + 2 * s)) := one_div_le_one_div_of_le hpos hden
    _ = 1 / (2 * s) + 1 := by field_simp

/-- `ω(s) ≥ 1/(2s) − 1/4`, from `ω(s) ≥ e^{−s/2}/(2s)` and `e^{−s/2} ≥ 1 − s/2`. -/
theorem archLevyDensity_ge_sub {s : ℝ} (hs : 0 < s) : 1 / (2 * s) - 1 / 4 ≤ archLevyDensity s := by
  have h := archLevyDensity_ge_of_le hs le_rfl
  have he : 1 - s / 2 ≤ Real.exp (-(s / 2)) := by linarith [Real.add_one_le_exp (-(s / 2))]
  have heq : 1 / (2 * s) - 1 / 4 = (1 - s / 2) / (2 * s) := by field_simp; ring
  rw [heq]
  exact (div_le_div_of_nonneg_right he (by positivity)).trans h

/-! ### Bump pairings and the shift expansion -/

variable {g : ℝ → ℝ} {w : ℝ}

/-- The **bump pairing** `c_{mn}(s) = ∫ g(u − log m) g(u + s − log n) du`. -/
def bumpPairing (g : ℝ → ℝ) (m n : ℕ) (s : ℝ) : ℝ :=
  ∫ u, g (u - Real.log m) * g (u + (s - Real.log n))

theorem integrable_bump_mul (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (a b : ℝ) :
    Integrable fun u => g (u - a) * g (u + b) := by
  have hc : HasCompactSupport fun u => g (u - a) := hgc.comp_homeomorph (Homeomorph.subRight a)
  exact Continuous.integrable_of_hasCompactSupport
    ((hg.continuous.comp (continuous_id.sub continuous_const)).mul
      (hg.continuous.comp (continuous_id.add continuous_const))) hc.mul_right

/-- `∫ f(u) f(u + s) du = Σ_{m,n} x_m x_n c_{mn}(s)`. -/
theorem integral_atomicTest_mul_shift (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (N : ℕ)
    (x : ℕ → ℝ) (s : ℝ) :
    ∫ u, atomicTest N x g u * atomicTest N x g (u + s) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n * bumpPairing g m n s := by
  have hpt : ∀ u, atomicTest N x g u * atomicTest N x g (u + s) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        x m * x n * (g (u - Real.log m) * g (u + (s - Real.log n))) := by
    intro u
    rw [atomicTest, atomicTest, sum_mul_sum]
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
    rw [show u + s - Real.log n = u + (s - Real.log n) by ring]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ =>
    (integrable_bump_mul hg hgc _ _).const_mul _]
  refine sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ fun n _ => (integrable_bump_mul hg hgc _ _).const_mul _]
  exact sum_congr rfl fun n _ => by rw [integral_const_mul, bumpPairing]

/-- **Shift expansion**: `∫ (f − f(· + s))² = 2∫f² − 2 Σ_{m,n} x_m x_n c_{mn}(s)`. -/
theorem integral_sub_shift_sq (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (N : ℕ) (x : ℕ → ℝ) (s : ℝ) :
    ∫ u, (atomicTest N x g u - atomicTest N x g (u + s)) ^ 2 =
      2 * (∫ u, atomicTest N x g u ^ 2) -
        2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n * bumpPairing g m n s := by
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  set f := atomicTest N x g
  have h1 : Integrable fun u => f u ^ 2 := by
    have h0 : Integrable (fun t => f t * f t) :=
      (hf.continuous.mul hf.continuous).integrable_of_hasCompactSupport hfc.mul_right
    simpa [pow_two] using h0
  have h2 : Integrable fun u => f (u + s) ^ 2 := h1.comp_add_right s
  have h3 : Integrable fun u => f u * f (u + s) :=
    (hf.continuous.mul (hf.continuous.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hfc.mul_right
  have hpt : ∀ u, (f u - f (u + s)) ^ 2 = f u ^ 2 + f (u + s) ^ 2 - 2 * (f u * f (u + s)) :=
    fun u => by ring
  have h12 : Integrable fun u => f u ^ 2 + f (u + s) ^ 2 := h1.add h2
  simp_rw [hpt]
  rw [integral_sub h12 (h3.const_mul 2), integral_add h1 h2, integral_const_mul,
    integral_add_right_eq_self (fun u => f u ^ 2) s, integral_atomicTest_mul_shift hg hgc N x s]
  ring

/-- `|c_{mn}(s)| ≤ ∫ g²`. -/
theorem abs_bumpPairing_le (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (m n : ℕ) (s : ℝ) :
    |bumpPairing g m n s| ≤ ∫ u, g u ^ 2 := by
  unfold bumpPairing
  have hA := integrable_bump_sq hg hgc (Real.log m)
  have hB := integrable_bump_sq hg hgc (Real.log n - s)
  have hpt : ∀ u, |g (u - Real.log m) * g (u + (s - Real.log n))| ≤
      (g (u - Real.log m) ^ 2 + g (u - (Real.log n - s)) ^ 2) / 2 := by
    intro u
    rw [show u + (s - Real.log n) = u - (Real.log n - s) by ring, abs_mul]
    nlinarith [sq_nonneg (|g (u - Real.log m)| - |g (u - (Real.log n - s))|),
      sq_abs (g (u - Real.log m)), sq_abs (g (u - (Real.log n - s)))]
  calc |∫ u, g (u - Real.log m) * g (u + (s - Real.log n))|
      ≤ ∫ u, |g (u - Real.log m) * g (u + (s - Real.log n))| := abs_integral_le_integral_abs
    _ ≤ ∫ u, (g (u - Real.log m) ^ 2 + g (u - (Real.log n - s)) ^ 2) / 2 :=
        integral_mono (integrable_bump_mul hg hgc _ _).abs ((hA.add hB).div_const 2) hpt
    _ = ∫ u, g u ^ 2 := by
        rw [integral_div, integral_add hA hB, integral_sub_right_eq_self (fun u => g u ^ 2),
          integral_sub_right_eq_self (fun u => g u ^ 2)]
        ring

/-- `c_{mn}(s) = 0` unless `|s − (log n − log m)| ≤ w`. -/
theorem bumpPairing_eq_zero (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {m n : ℕ} {s : ℝ}
    (hs : s ∉ Set.Icc (Real.log n - Real.log m - w) (Real.log n - Real.log m + w)) :
    bumpPairing g m n s = 0 := by
  have h0 : (fun u => g (u - Real.log m) * g (u + (s - Real.log n))) = fun _ => 0 := by
    funext u
    by_contra hne
    have h1 : u - Real.log m ∈ Set.Icc 0 w := by
      by_contra h
      apply hne
      simp only [hgsupp _ h, zero_mul]
    have h2 : u + (s - Real.log n) ∈ Set.Icc 0 w := by
      by_contra h
      apply hne
      simp only [hgsupp _ h, mul_zero]
    rw [Set.mem_Icc] at h1 h2
    exact hs (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
  rw [bumpPairing, h0, integral_zero]

/-! ### The cross terms -/

/-- The weight `|x_m| |x_n| (2/(3|log n − log m|) + 1)` of a pair of distinct atoms. -/
def crossCoeff (x : ℕ → ℝ) (m n : ℕ) : ℝ :=
  if m = n then 0 else |x m| * |x n| * (2 / (3 * |Real.log n - Real.log m|) + 1)

theorem crossCoeff_nonneg (x : ℕ → ℝ) (m n : ℕ) : 0 ≤ crossCoeff x m n := by
  unfold crossCoeff
  split_ifs
  · exact le_rfl
  · positivity

/-- The **cross majorant** at shift `s`: the weights of the pairs with `|s − log(n/m)| ≤ w`. -/
def crossMajorant (N : ℕ) (x : ℕ → ℝ) (w s : ℝ) : ℝ :=
  ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
    (Set.Icc (Real.log n - Real.log m - w) (Real.log n - Real.log m + w)).indicator
      (fun _ => crossCoeff x m n) s

/-- **At shift `s > w` only distinct atoms at distance `≈ s` meet**:
`ω(s) Σ x_m x_n c_{mn}(s) ≤ (∫ g²) · crossMajorant(s)`. -/
theorem archLevyDensity_mul_cross_le (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ atomSpacing N / 4) (x : ℕ → ℝ) {s : ℝ} (hs : w < s) :
    archLevyDensity s * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n * bumpPairing g m n s ≤
      (∫ u, g u ^ 2) * crossMajorant N x w s := by
  have hω := archLevyDensity_pos (hw0.trans hs)
  have hδ := atomSpacing_pos hN
  unfold crossMajorant
  rw [mul_sum, mul_sum]
  refine sum_le_sum fun m hm => ?_
  rw [mul_sum, mul_sum]
  refine sum_le_sum fun n hn => ?_
  set L := Real.log n - Real.log m with hLdef
  by_cases hI : s ∈ Set.Icc (L - w) (L + w)
  · rw [Set.indicator_of_mem hI]
    by_cases hmn : m = n
    · -- the diagonal does not meet itself beyond the width
      exfalso
      have hL0 : L = 0 := by rw [hLdef, hmn, sub_self]
      linarith [hI.2]
    · have hm1 := (mem_Icc.mp hm).1
      have hmN := (mem_Icc.mp hm).2
      have hn1 := (mem_Icc.mp hn).1
      have hnN := (mem_Icc.mp hn).2
      -- the pair meets only for `n > m`, at `s ≥ 3L/4`
      have hL : atomSpacing N ≤ L := by
        rcases lt_or_gt_of_ne hmn with hlt | hgt
        · exact atomSpacing_le_log_sub hm1 hmN hlt
        · exfalso
          have := atomSpacing_le_log_sub hn1 hnN hgt
          linarith [hI.2]
      have hLabs : |L| = L := abs_of_pos (by linarith)
      have hs34 : 3 * L / 4 ≤ s := by linarith [hI.1]
      have hωle : archLevyDensity s ≤ 2 / (3 * L) + 1 := by
        refine (archLevyDensity_le (hw0.trans hs)).trans ?_
        have : 1 / (2 * s) ≤ 2 / (3 * L) := by
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          linarith
        linarith
      have hc := abs_bumpPairing_le hg hgc m n s
      rw [crossCoeff, if_neg hmn, ← hLdef, hLabs]
      calc archLevyDensity s * (x m * x n * bumpPairing g m n s)
          ≤ archLevyDensity s * (|x m| * |x n| * ∫ u, g u ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hω.le
            calc x m * x n * bumpPairing g m n s ≤ |x m * x n * bumpPairing g m n s| :=
                  le_abs_self _
              _ = |x m| * |x n| * |bumpPairing g m n s| := by rw [abs_mul, abs_mul]
              _ ≤ |x m| * |x n| * ∫ u, g u ^ 2 :=
                  mul_le_mul_of_nonneg_left hc (by positivity)
        _ ≤ (2 / (3 * L) + 1) * (|x m| * |x n| * ∫ u, g u ^ 2) :=
            mul_le_mul_of_nonneg_right hωle
              (mul_nonneg (by positivity) (integral_nonneg fun u => sq_nonneg _))
        _ = (∫ u, g u ^ 2) * (|x m| * |x n| * (2 / (3 * L) + 1)) := by ring
  · rw [Set.indicator_of_notMem hI, bumpPairing_eq_zero hgsupp hI]
    simp

/-- **Each pair costs `2w`**: `∫_{(a, b]} crossMajorant ≤ 2w Σ_{m,n} crossCoeff`. -/
theorem integral_crossMajorant_le (N : ℕ) (x : ℕ → ℝ) (hw0 : 0 ≤ w) (a b : ℝ) :
    ∫ s in Set.Ioc a b, crossMajorant N x w s ≤
      2 * w * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, crossCoeff x m n := by
  unfold crossMajorant
  have hint : ∀ m n : ℕ, IntegrableOn (fun s =>
      (Set.Icc (Real.log n - Real.log m - w) (Real.log n - Real.log m + w)).indicator
        (fun _ => crossCoeff x m n) s) (Set.Ioc a b) :=
    fun m n => IntegrableOn.indicator (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Icc
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ => hint m n, mul_sum]
  refine sum_le_sum fun m _ => ?_
  rw [integral_finsetSum _ fun n _ => hint m n, mul_sum]
  refine sum_le_sum fun n _ => ?_
  rw [setIntegral_indicator measurableSet_Icc]
  simp only [setIntegral_const, smul_eq_mul]
  have hvol : volume.real (Set.Ioc a b ∩
      Set.Icc (Real.log n - Real.log m - w) (Real.log n - Real.log m + w)) ≤ 2 * w :=
    calc _ ≤ volume.real
          (Set.Icc (Real.log n - Real.log m - w) (Real.log n - Real.log m + w)) :=
          measureReal_mono Set.inter_subset_right measure_Icc_lt_top.ne
      _ = 2 * w := by rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  exact mul_le_mul_of_nonneg_right hvol (crossCoeff_nonneg x m n)

/-! ### The Hilbert-type row bound -/

/-- `|log n − log m| ≥ |n − m|/N` for `1 ≤ m, n ≤ N`. -/
theorem abs_sub_div_le_abs_log_sub {m n N : ℕ} (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N) :
    |(n : ℝ) - m| / N ≤ |Real.log n - Real.log m| := by
  wlog hle : m ≤ n generalizing m n
  · have := this hn hm (by omega)
    rwa [abs_sub_comm, abs_sub_comm (Real.log m)] at this
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
  have hle' : (m : ℝ) ≤ n := by exact_mod_cast hle
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hm0 hle'))]
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < n / m by positivity)
  rw [Real.log_div hn0.ne' hm0.ne', inv_div] at h
  calc ((n : ℝ) - m) / N ≤ ((n : ℝ) - m) / n := div_le_div_of_nonneg_left (by linarith) hn0 hnN
    _ = 1 - m / n := by field_simp
    _ ≤ _ := h

/-- `H_N ≤ 1 + log N`. -/
theorem harmonicSum_le_one_add_log (N : ℕ) : harmonicSum N ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  simp_rw [_root_.harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  simpa [harmonicSum, one_div] using h

/-- Reindexing a sum of reciprocals into the harmonic sum. -/
theorem sum_le_harmonicSum_of_injOn {T : Finset ℕ} {φ : ℕ → ℕ} {N : ℕ}
    (hφ : ∀ n ∈ T, φ n ∈ Icc 1 N) (hinj : Set.InjOn φ T) :
    ∑ n ∈ T, 1 / (φ n : ℝ) ≤ harmonicSum N := by
  rw [← sum_image (f := fun k : ℕ => 1 / (k : ℝ)) hinj, harmonicSum]
  exact sum_le_sum_of_subset_of_nonneg (fun k hk => by
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hk
    exact hφ n hn) fun _ _ _ => by positivity

/-- **Hilbert-type row**: `Σ_{n ≠ m} 1/|n − m| ≤ 2H_N`. -/
theorem sum_erase_inv_abs_sub_le {m N : ℕ} (hm : m ∈ Icc 1 N) :
    ∑ n ∈ (Icc 1 N).erase m, 1 / |(n : ℝ) - m| ≤ 2 * harmonicSum N := by
  rw [← sum_filter_add_sum_filter_not ((Icc 1 N).erase m) (fun n => n < m)]
  have h1 : ∑ n ∈ ((Icc 1 N).erase m).filter (fun n => n < m), 1 / |(n : ℝ) - m| =
      ∑ n ∈ ((Icc 1 N).erase m).filter (fun n => n < m), 1 / ((m - n : ℕ) : ℝ) := by
    refine sum_congr rfl fun n hn => ?_
    have hlt := (mem_filter.mp hn).2
    have hlt' : (n : ℝ) < m := by exact_mod_cast hlt
    rw [Nat.cast_sub hlt.le, abs_sub_comm, abs_of_pos (by linarith)]
  have h2 : ∑ n ∈ ((Icc 1 N).erase m).filter (fun n => ¬ n < m), 1 / |(n : ℝ) - m| =
      ∑ n ∈ ((Icc 1 N).erase m).filter (fun n => ¬ n < m), 1 / ((n - m : ℕ) : ℝ) := by
    refine sum_congr rfl fun n hn => ?_
    obtain ⟨hne, hn'⟩ := mem_filter.mp hn
    have hgt : m < n := by have := ne_of_mem_erase hne; omega
    have hgt' : (m : ℝ) < n := by exact_mod_cast hgt
    rw [Nat.cast_sub hgt.le, abs_of_pos (by linarith)]
  rw [h1, h2, two_mul]
  refine add_le_add (sum_le_harmonicSum_of_injOn (fun n hn => ?_) (fun a ha b hb h => ?_))
    (sum_le_harmonicSum_of_injOn (fun n hn => ?_) (fun a ha b hb h => ?_))
  · obtain ⟨he, hlt⟩ := mem_filter.mp hn
    have := mem_Icc.mp (mem_of_mem_erase he)
    have := (mem_Icc.mp hm).2
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    omega
  · obtain ⟨he, hlt⟩ := mem_filter.mp hn
    have := mem_Icc.mp (mem_of_mem_erase he)
    have := ne_of_mem_erase he
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    omega

/-- The symmetric kernel `2N/(3|n − m|) + 1` off the diagonal. -/
def pairKernel (N m n : ℕ) : ℝ := if m = n then 0 else 2 * N / (3 * |(n : ℝ) - m|) + 1

theorem pairKernel_comm (N m n : ℕ) : pairKernel N m n = pairKernel N n m := by
  unfold pairKernel
  by_cases h : m = n
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h), abs_sub_comm]

/-- `crossCoeff x m n ≤ ½(x_m² + x_n²) · pairKernel N m n` on the orders `≤ N`. -/
theorem crossCoeff_le {N m n : ℕ} (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N) (x : ℕ → ℝ) :
    crossCoeff x m n ≤ (x m ^ 2 + x n ^ 2) / 2 * pairKernel N m n := by
  unfold crossCoeff pairKernel
  by_cases hmn : m = n
  · simp [hmn]
  rw [if_neg hmn, if_neg hmn]
  have hd : (0 : ℝ) < |(n : ℝ) - m| :=
    abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast Ne.symm hmn))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (mem_Icc.mp hm).1.trans (mem_Icc.mp hm).2
  have hlog := abs_sub_div_le_abs_log_sub hm hn
  have hk : 2 / (3 * |Real.log n - Real.log m|) ≤ 2 * N / (3 * |(n : ℝ) - m|) := by
    calc 2 / (3 * |Real.log n - Real.log m|) ≤ 2 / (3 * (|(n : ℝ) - m| / N)) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      _ = 2 * N / (3 * |(n : ℝ) - m|) := by field_simp
  have hxy : |x m| * |x n| ≤ (x m ^ 2 + x n ^ 2) / 2 := by
    nlinarith [sq_nonneg (|x m| - |x n|), sq_abs (x m), sq_abs (x n)]
  exact mul_le_mul hxy (by linarith) (by positivity) (by positivity)

/-- **The cross kernel is `O(N log N)`**: `Σ_{m,n} crossCoeff ≤ N((4/3)H_N + 1) |x|²`. -/
theorem sum_crossCoeff_le (N : ℕ) (x : ℕ → ℝ) :
    ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, crossCoeff x m n ≤
      N * (4 / 3 * harmonicSum N + 1) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  set S := Icc 1 N
  -- the rows of the kernel: `(2N/3) · 2H_N + N`
  have hrow : ∀ m ∈ S, ∑ n ∈ S, pairKernel N m n ≤ N * (4 / 3 * harmonicSum N + 1) := by
    intro m hm
    have h0 : pairKernel N m m = 0 := by simp [pairKernel]
    have hpt : ∀ n ∈ S.erase m, pairKernel N m n = 2 * N / 3 * (1 / |(n : ℝ) - m|) + 1 := by
      intro n hn
      rw [pairKernel, if_neg (Ne.symm (ne_of_mem_erase hn))]
      ring
    rw [← add_sum_erase S _ hm, h0, zero_add, sum_congr rfl hpt, sum_add_distrib, ← mul_sum,
      sum_const, nsmul_eq_mul, mul_one]
    have hH := mul_le_mul_of_nonneg_left (sum_erase_inv_abs_sub_le hm)
      (by positivity : (0 : ℝ) ≤ 2 * N / 3)
    have hcard : ((S.erase m).card : ℝ) ≤ N := by
      have : (S.erase m).card ≤ N := by
        rw [card_erase_of_mem hm, Nat.card_Icc]
        omega
      exact_mod_cast this
    linarith
  have hsym : ∑ m ∈ S, ∑ n ∈ S, x n ^ 2 * pairKernel N m n =
      ∑ m ∈ S, ∑ n ∈ S, x m ^ 2 * pairKernel N m n := by
    rw [sum_comm]
    exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by rw [pairKernel_comm]
  calc ∑ m ∈ S, ∑ n ∈ S, crossCoeff x m n
      ≤ ∑ m ∈ S, ∑ n ∈ S, (x m ^ 2 + x n ^ 2) / 2 * pairKernel N m n :=
        sum_le_sum fun m hm => sum_le_sum fun n hn => crossCoeff_le hm hn x
    _ = (∑ m ∈ S, ∑ n ∈ S, x m ^ 2 * pairKernel N m n +
          ∑ m ∈ S, ∑ n ∈ S, x n ^ 2 * pairKernel N m n) / 2 := by
        rw [← sum_add_distrib, sum_div]
        refine sum_congr rfl fun m _ => ?_
        rw [← sum_add_distrib, sum_div]
        exact sum_congr rfl fun n _ => by ring
    _ = ∑ m ∈ S, x m ^ 2 * ∑ n ∈ S, pairKernel N m n := by
        rw [hsym, add_self_div_two]
        exact sum_congr rfl fun m _ => by rw [mul_sum]
    _ ≤ ∑ m ∈ S, x m ^ 2 * (N * (4 / 3 * harmonicSum N + 1)) :=
        sum_le_sum fun m hm => mul_le_mul_of_nonneg_left (hrow m hm) (sq_nonneg _)
    _ = N * (4 / 3 * harmonicSum N + 1) * ∑ n ∈ S, x n ^ 2 := by
        rw [mul_sum]
        exact sum_congr rfl fun n _ => by ring

/-! ### The Lévy energy with interaction -/

/-- **The Lévy energy with interaction**: every shift `s ∈ (w, 1]` counts, so the self-energy is
`log(1/w)`, and the cross terms cost at most `4w (∫ g²) Σ crossCoeff`. -/
theorem levyEnergy_atomicTest_ge_cross (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ atomSpacing N / 4) (x : ℕ → ℝ) :
    (Real.log (1 / w) - 1 / 2) * (∫ u, atomicTest N x g u ^ 2) -
        4 * w * (∫ u, g u ^ 2) * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, crossCoeff x m n ≤
      levyEnergy (atomicTest N x g) := by
  have hδ1 := atomSpacing_le_one hN
  have hδ0 := atomSpacing_pos hN
  have hw1 : w ≤ 1 := by linarith
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  have hF : 0 ≤ ∫ u, atomicTest N x g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hG : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hLint := integrableOn_levyIntegrand hf hfc
  have hsub : Set.Ioc w 1 ⊆ Set.Ioi 0 := fun s hs => lt_trans hw0 hs.1
  have hstep1 : ∫ s in Set.Ioc w 1, archLevyDensity s *
        ∫ u, (atomicTest N x g u - atomicTest N x g (u + s)) ^ 2 ≤
      ∫ s in Set.Ioi 0, archLevyDensity s *
        ∫ u, (atomicTest N x g u - atomicTest N x g (u + s)) ^ 2 :=
    setIntegral_mono_set hLint (levyIntegrand_nonneg _) (Filter.Eventually.of_forall hsub)
  -- the lower function: self-energy density minus the cross majorant
  have hlow : ∀ s ∈ Set.Ioc w 1,
      2 * (∫ u, atomicTest N x g u ^ 2) * (1 / 2 * s⁻¹ - 1 / 4) -
          2 * (∫ u, g u ^ 2) * crossMajorant N x w s ≤
        archLevyDensity s * ∫ u, (atomicTest N x g u - atomicTest N x g (u + s)) ^ 2 := by
    intro s hs
    have hs0 : 0 < s := lt_trans hw0 hs.1
    have hωge := archLevyDensity_ge_sub hs0
    have hcross := archLevyDensity_mul_cross_le hg hgc hgsupp hN hw0 hw x hs.1
    rw [integral_sub_shift_sq hg hgc hgsupp N x s]
    have hinv : 1 / 2 * s⁻¹ = 1 / (2 * s) := by field_simp
    rw [hinv]
    have e1 := mul_le_mul_of_nonneg_left hωge (by positivity : (0 : ℝ) ≤ 2 * ∫ u, atomicTest N x g u ^ 2)
    have e2 : archLevyDensity s * (2 * (∫ u, atomicTest N x g u ^ 2) -
        2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n * bumpPairing g m n s) =
        2 * (∫ u, atomicTest N x g u ^ 2) * archLevyDensity s -
          2 * (archLevyDensity s * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n * bumpPairing g m n s) := by
      ring
    rw [e2]
    linarith
  have hinv_int : IntegrableOn (fun s : ℝ => s⁻¹) (Set.Ioc w 1) := by
    have hc : ContinuousOn (fun s : ℝ => s⁻¹) (Set.Icc w 1) :=
      continuousOn_inv₀.mono fun s hs => ne_of_gt (lt_of_lt_of_le hw0 hs.1)
    exact (hc.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hself_int : IntegrableOn (fun s : ℝ => 1 / 2 * s⁻¹ - 1 / 4) (Set.Ioc w 1) :=
    (hinv_int.const_mul _).sub (integrableOn_const measure_Ioc_lt_top.ne)
  have hCM_int : IntegrableOn (fun s => crossMajorant N x w s) (Set.Ioc w 1) := by
    unfold crossMajorant
    exact integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ =>
      IntegrableOn.indicator (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Icc
  have hstep2 : ∫ s in Set.Ioc w 1, (2 * (∫ u, atomicTest N x g u ^ 2) * (1 / 2 * s⁻¹ - 1 / 4) -
        2 * (∫ u, g u ^ 2) * crossMajorant N x w s) ≤
      ∫ s in Set.Ioc w 1, archLevyDensity s *
        ∫ u, (atomicTest N x g u - atomicTest N x g (u + s)) ^ 2 :=
    setIntegral_mono_on ((hself_int.const_mul (2 * ∫ u, atomicTest N x g u ^ 2)).sub
      (hCM_int.const_mul (2 * ∫ u, g u ^ 2))) (hLint.mono_set hsub) measurableSet_Ioc hlow
  -- `∫_w^1 (1/(2s) − 1/4) ds = ½ log(1/w) − (1 − w)/4`
  have hval1 : ∫ s in Set.Ioc w 1, (1 / 2 * s⁻¹ - 1 / 4) =
      1 / 2 * Real.log (1 / w) - (1 - w) / 4 := by
    rw [integral_sub (hinv_int.const_mul _) (integrableOn_const measure_Ioc_lt_top.ne),
      integral_const_mul,
      ← intervalIntegral.integral_of_le hw1, integral_inv_of_pos hw0 one_pos, setIntegral_const,
      Real.volume_real_Ioc_of_le hw1, smul_eq_mul]
    ring
  rw [integral_sub (hself_int.const_mul _) (hCM_int.const_mul _), integral_const_mul,
    integral_const_mul, hval1] at hstep2
  have hCM := mul_le_mul_of_nonneg_left (integral_crossMajorant_le N x hw0.le w 1)
    (by positivity : (0 : ℝ) ≤ 2 * ∫ u, g u ^ 2)
  have hFw : 0 ≤ (∫ u, atomicTest N x g u ^ 2) * w := mul_nonneg hF hw0.le
  unfold levyEnergy
  nlinarith

/-! ### The stability law at the spacing over a logarithm -/

/-- **The stability law with interaction, quantitative form**:
`M(f) ≥ (2θ′(0) + log(1/w) − 1/2 − 4wN((4/3)H_N + 1) − log N − log 4 − 4) ∫ f²`. -/
theorem markovEnergy_atomicTest_ge_cross (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ atomSpacing N / 4) (x : ℕ → ℝ) :
    (2 * gammaHardyPhaseRate 0 + Real.log (1 / w) - 1 / 2 -
        4 * w * N * (4 / 3 * harmonicSum N + 1) - (Real.log N + (Real.log 4 + 4))) *
        ∫ u, atomicTest N x g u ^ 2 ≤
      markovEnergy (fun u => (atomicTest N x g u : ℂ)) := by
  have hδ := atomSpacing_pos hN
  have hw' : w < atomSpacing N := by linarith
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  rw [markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, archForm_eq_levyEnergy hf hfc,
    primeSum_atomicTest hg hgc hgsupp hw' x]
  have hlevy := levyEnergy_atomicTest_ge_cross hg hgc hgsupp hN hw0 hw x
  have hsq := integral_atomicTest_sq hg hgc hgsupp hw' x
  have hW := atomicWeilForm_le_log N x
  have hsum := sum_crossCoeff_le N x
  have hG : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have h1 : 4 * w * (∫ u, g u ^ 2) * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, crossCoeff x m n ≤
      4 * w * N * (4 / 3 * harmonicSum N + 1) * ∫ u, atomicTest N x g u ^ 2 := by
    rw [hsq]
    calc _ ≤ 4 * w * (∫ u, g u ^ 2) *
          (N * (4 / 3 * harmonicSum N + 1) * ∑ n ∈ Icc 1 N, x n ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg (by positivity) hG)
      _ = _ := by ring
  have h2 : (∫ u, g u ^ 2) * atomicWeilForm N x ≤
      (Real.log N + (Real.log 4 + 4)) * ∫ u, atomicTest N x g u ^ 2 := by
    rw [hsq]
    calc _ ≤ (∫ u, g u ^ 2) * ((Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2) :=
          mul_le_mul_of_nonneg_left hW hG
      _ = _ := by ring
  linarith

/-- The constant `C₁ = 29/2 + log 4 + 2|θ′(0)|`. -/
def spacingConstant : ℝ := 29 / 2 + Real.log 4 + 2 * |gammaHardyPhaseRate 0|

/-- The **logarithmic spacing width** `e^{−C₁}/(N(1 + log N))`. -/
def logSpacingWidth (N : ℕ) : ℝ := Real.exp (-spacingConstant) / (N * (1 + Real.log N))

theorem logSpacingWidth_pos {N : ℕ} (hN : 1 ≤ N) : 0 < logSpacingWidth N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have := Real.log_nonneg hN'
  exact div_pos (Real.exp_pos _) (mul_pos (by linarith) (by linarith))

/-- `δ_N ≥ 1/(2N)`. -/
theorem one_div_two_mul_le_atomSpacing {N : ℕ} (hN : 1 ≤ N) : 1 / (2 * N) ≤ atomSpacing N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 + 1 / N by positivity)
  have hinv : 1 - (1 + 1 / (N : ℝ))⁻¹ = 1 / (N + 1) := by
    have : (N : ℝ) + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hinv] at h
  exact (one_div_le_one_div_of_le (by linarith) (by linarith)).trans h

/-- **The stability law at the spacing over a logarithm**: every atomic test of width
`w ≤ e^{−C₁}/(N(1 + log N))` at the points `log n`, `n ≤ N`, has nonnegative Markov form. -/
theorem markovEnergy_atomicTest_nonneg_logSpacing (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N)
    (hw0 : 0 < w) (hw : w ≤ logSpacingWidth N) (x : ℕ → ℝ) :
    0 ≤ markovEnergy (fun u => (atomicTest N x g u : ℂ)) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  have hlogN := Real.log_nonneg hN'
  have hD : 0 < (N : ℝ) * (1 + Real.log N) := mul_pos (by linarith) (by linarith)
  have hc0 : 0 < Real.exp (-spacingConstant) := Real.exp_pos _
  have hC : 29 / 2 ≤ spacingConstant := by
    unfold spacingConstant
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    have := abs_nonneg (gammaHardyPhaseRate 0)
    linarith
  -- `e^{−C₁} ≤ 1/8`
  have hc8 : Real.exp (-spacingConstant) ≤ 1 / 8 := by
    have h := Real.add_one_le_exp spacingConstant
    have he : Real.exp (-spacingConstant) * Real.exp spacingConstant = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [mul_le_mul_of_nonneg_left h hc0.le]
  -- the width is below `δ_N/4`
  have hwW : logSpacingWidth N ≤ atomSpacing N / 4 := by
    unfold logSpacingWidth
    rw [div_le_iff₀ hD]
    have h1 : 1 / 2 ≤ atomSpacing N * N := by
      have := mul_le_mul_of_nonneg_right (one_div_two_mul_le_atomSpacing hN) (Nat.cast_nonneg N)
      rwa [show 1 / (2 * (N : ℝ)) * N = 1 / 2 by field_simp] at this
    have h2 : atomSpacing N * N ≤ atomSpacing N * N * (1 + Real.log N) :=
      le_mul_of_one_le_right (by linarith) (by linarith)
    nlinarith
  have hw4 : w ≤ atomSpacing N / 4 := hw.trans hwW
  -- the self-energy: `log(1/w) ≥ C₁ + log N`
  have hlogw : spacingConstant + Real.log N ≤ Real.log (1 / w) := by
    have h1 : 1 / logSpacingWidth N ≤ 1 / w := one_div_le_one_div_of_le hw0 hw
    have h2 : Real.log (1 / logSpacingWidth N) =
        spacingConstant + Real.log N + Real.log (1 + Real.log N) := by
      unfold logSpacingWidth
      rw [one_div_div, Real.log_div hD.ne' hc0.ne', Real.log_mul hN0 (by linarith), Real.log_exp]
      ring
    have h3 := Real.log_le_log (one_div_pos.mpr (logSpacingWidth_pos hN)) h1
    have h4 : 0 ≤ Real.log (1 + Real.log N) := Real.log_nonneg (by linarith)
    linarith
  -- the interaction: `4wN((4/3)H_N + 1) ≤ (28/3) w N (1 + log N) ≤ 10`
  have hcross : 4 * w * N * (4 / 3 * harmonicSum N + 1) ≤ 10 := by
    have hH := harmonicSum_le_one_add_log N
    have hwN : w * (N * (1 + Real.log N)) ≤ Real.exp (-spacingConstant) :=
      (le_div_iff₀ hD).mp hw
    have hH' : 4 / 3 * harmonicSum N + 1 ≤ 7 / 3 * (1 + Real.log N) := by linarith
    have h4wN : 0 ≤ 4 * w * N := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hH' h4wN]
  have hcoef : 0 ≤ 2 * gammaHardyPhaseRate 0 + Real.log (1 / w) - 1 / 2 -
      4 * w * N * (4 / 3 * harmonicSum N + 1) - (Real.log N + (Real.log 4 + 4)) := by
    unfold spacingConstant at hlogw
    linarith [neg_abs_le (gammaHardyPhaseRate 0)]
  have hint : 0 ≤ ∫ u, atomicTest N x g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  exact le_trans (mul_nonneg hcoef hint) (markovEnergy_atomicTest_ge_cross hg hgc hgsupp hN hw0 hw4 x)

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
