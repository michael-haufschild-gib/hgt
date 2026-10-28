import GaloisForLFunctions.ArithmeticLorentzianGeometry.ThePoleDefectPaysThePole
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# Weil's form is positive on every test near the logarithms

An atomic test `Σ_n x_n g(· − log n)` uses one profile `g` for all atoms. This file removes the
profile. A **window test** `f = Σ_{n ≤ N} G_n(· − log n)` (`windowTest`) carries an arbitrary `C²`
profile `G_n` supported in `[0, w]` at each atom. The analytic estimates of the atomic family hold
window by window, with the norms `y_n = ‖G_n‖₂` as coefficients.

* **Orthogonality and exact lags** (`integral_windowTest_sq`, `primeSum_windowTest`): below the
  spacing `‖f‖² = Σ‖G_n‖²`, and the prime sum is the Weil kernel against the window Gram,
  `Σ_{m,n} P(m, n) ⟨G_m, G_n⟩`. By Cauchy–Schwarz and `P ≥ 0` it is at most the atomic prime form
  `P_N(y)` (`primeSum_windowTest_le`).
* **The Lévy energy with its diagonal** (`levyEnergy_windowTest_ge_diag`): the windows interact only
  through pair windows of the Lévy density, with correlations at most `y_m y_n`.
* **The self-energy of a window** (`levyEnergy_profile_ge`): every `C²` bump in `[0, w]` has
  `levyEnergy G ≥ (log(1/w) + 2c_∞ − (e^{1/2}/2) w) ‖G‖²`, the shape term `β(G) ≥ 0` being dropped.
* **Weil positivity** (`eventually_weilQuad_windowTest_nonneg`): the defect bound of
  RenormalizedArithmeticPotentialTheory and the multiplicative Hardy inequality, applied to `y`,
  give `M(f) ≥ φ₀|y|² + c₀D_N(y)` and `2|AB| ≤ c_P e^{w/2} wN (2|y|² + D_N(y))`. So, eventually in
  `N`, at every width `w ≤ K★_∞(ε) δ_N`, Weil's form is nonnegative on every window test
  (`windowFraction`). This is the threshold of `ThePoleDefectPaysThePole` with the Robin constant
  `κ_L(φ)` replaced by its profile-free part `2c_∞`.
* **Every test near the logarithms** (`windowTest_of_support`,
  `eventually_weilQuad_nonneg_of_support`): every `C²` function whose support lies in
  `⋃_{n ≤ N} [log n, log n + w]` is a window test. So eventually in `N`, Weil's form is nonnegative
  on the whole space of `C²` tests supported within `K★_∞ δ_N` to the right of the logarithms of the
  integers up to `N`. That is an infinite-dimensional space of tests whose prime lags
  `log(n/m)` reach every rational lag of the horizon.
-/

noncomputable section

open MeasureTheory Finset RHTower

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.ArithmeticEffectivityTheory

local notation "γ" => Real.eulerMascheroniConstant

/-! ### Window tests -/

/-- A **window test** `Σ_{1 ≤ n ≤ N} G_n(u − log n)`: one profile per atom. -/
def windowTest (N : ℕ) (G : ℕ → ℝ → ℝ) (u : ℝ) : ℝ := ∑ n ∈ Icc 1 N, G n (u - Real.log n)

/-- The window norms `y_n = ‖G_n‖₂`. -/
def windowNorm (G : ℕ → ℝ → ℝ) (n : ℕ) : ℝ := Real.sqrt (∫ u, G n u ^ 2)

variable {G : ℕ → ℝ → ℝ} {w : ℝ}

theorem windowNorm_nonneg (G : ℕ → ℝ → ℝ) (n : ℕ) : 0 ≤ windowNorm G n := Real.sqrt_nonneg _

theorem windowNorm_sq (G : ℕ → ℝ → ℝ) (n : ℕ) : windowNorm G n ^ 2 = ∫ u, G n u ^ 2 :=
  Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)

theorem hasCompactSupport_profile (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (n : ℕ) :
    HasCompactSupport (G n) :=
  HasCompactSupport.intro isCompact_Icc fun u hu => hGsupp n u hu

theorem contDiff_windowTest (hG : ∀ n, ContDiff ℝ 2 (G n)) (N : ℕ) :
    ContDiff ℝ 2 (windowTest N G) :=
  ContDiff.sum fun n _ => (hG n).comp (contDiff_id.sub contDiff_const)

theorem hasCompactSupport_windowTest (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (N : ℕ) :
    HasCompactSupport (windowTest N G) := by
  refine HasCompactSupport.intro (K := Set.Icc 0 (Real.log N + w)) isCompact_Icc fun u hu => ?_
  refine sum_eq_zero fun n hn => ?_
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hlogN : Real.log n ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
  refine hGsupp n _ fun hm => ?_
  rw [Set.mem_Icc] at hm
  exact hu (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)

/-- Windows at distinct atoms, one of them `≤ N`, do not meet below the spacing. -/
theorem window_mul_eq_zero (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {N a b : ℕ}
    (hw : w < atomSpacing N) (ha : 1 ≤ a) (hb : 1 ≤ b) (hmin : min a b ≤ N) (hab : a ≠ b)
    (t : ℝ) : G a (t - Real.log a) * G b (t - Real.log b) = 0 := by
  by_contra hne
  have h1 : t - Real.log a ∈ Set.Icc 0 w := by
    by_contra h; apply hne; simp only [hGsupp a _ h, zero_mul]
  have h2 : t - Real.log b ∈ Set.Icc 0 w := by
    by_contra h; apply hne; simp only [hGsupp b _ h, mul_zero]
  rw [Set.mem_Icc] at h1 h2
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have := atomSpacing_le_log_sub (N := N) ha (by rwa [min_eq_left hlt.le] at hmin) hlt
    linarith
  · have := atomSpacing_le_log_sub (N := N) hb (by rwa [min_eq_right hgt.le] at hmin) hgt
    linarith

theorem integrable_profile_mul (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (m n : ℕ) (a b : ℝ) :
    Integrable fun u => G m (u - a) * G n (u - b) :=
  (((hG m).continuous.comp (continuous_sub_right a)).mul
    ((hG n).continuous.comp (continuous_sub_right b))).integrable_of_hasCompactSupport
    ((hasCompactSupport_profile hGsupp m).comp_homeomorph (Homeomorph.subRight a)).mul_right

/-- **Orthogonality**: `‖f‖² = Σ‖G_n‖²` below the spacing. -/
theorem integral_windowTest_sq (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {N : ℕ} (hw : w < atomSpacing N) :
    ∫ u, windowTest N G u ^ 2 = ∑ n ∈ Icc 1 N, ∫ u, G n u ^ 2 := by
  have hpt : ∀ u, windowTest N G u ^ 2 = ∑ n ∈ Icc 1 N, G n (u - Real.log n) ^ 2 := by
    intro u
    rw [windowTest, sq, sum_mul_sum]
    refine sum_congr rfl fun m hm => ?_
    rw [← add_sum_erase _ _ hm, sum_eq_zero fun n hn => ?_, add_zero, sq]
    exact window_mul_eq_zero hGsupp hw (Finset.mem_Icc.mp hm).1
      (Finset.mem_Icc.mp (mem_of_mem_erase hn)).1
      ((min_le_left _ _).trans (Finset.mem_Icc.mp hm).2) (ne_of_mem_erase hn).symm u
  simp_rw [hpt]
  rw [integral_finsetSum _ fun n _ => by
    simpa [sq] using integrable_profile_mul hG hGsupp n n (Real.log n) (Real.log n)]
  refine sum_congr rfl fun n _ => ?_
  exact integral_sub_right_eq_self (fun u => G n u ^ 2) _

/-! ### The prime sum -/

/-- The window Gram `⟨G_m, G_n⟩`. -/
def windowGram (G : ℕ → ℝ → ℝ) (m n : ℕ) : ℝ := ∫ u, G m u * G n u

/-- The lag `−log k`: only `m = nk` survives. -/
theorem integral_windowTest_mul_shift_neg (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {N : ℕ} (hw : w < atomSpacing N) {k : ℕ}
    (hk : 1 ≤ k) :
    ∫ t, windowTest N G t * windowTest N G (t - Real.log k) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, if m = n * k then windowGram G m n else 0 := by
  have hpt : ∀ t, windowTest N G t * windowTest N G (t - Real.log k) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        if m = n * k then G m (t - Real.log m) * G n (t - Real.log m) else 0 := by
    intro t
    rw [windowTest, windowTest, sum_mul_sum]
    refine sum_congr rfl fun m hm => sum_congr rfl fun n hn => ?_
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hlog : t - Real.log k - Real.log n = t - Real.log ((n * k : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (show n ≠ 0 by omega))
        (by exact_mod_cast (show k ≠ 0 by omega))]
      ring
    rw [hlog]
    split_ifs with h
    · rw [← h]
    · have hz := window_mul_eq_zero (G := fun j => if j = m then G m else G n) (w := w)
        (fun j u hu => by split_ifs <;> exact hGsupp _ u hu) hw (Finset.mem_Icc.mp hm).1
        (Nat.mul_pos (by omega) (by omega)) ((min_le_left _ _).trans (Finset.mem_Icc.mp hm).2) h t
      simp only [if_neg (Ne.symm h)] at hz
      exact hz
  simp_rw [hpt]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ => by
    split_ifs
    · exact integrable_profile_mul hG hGsupp m n _ _
    · exact integrable_zero _ _ _]
  refine sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ fun n _ => by
    split_ifs
    · exact integrable_profile_mul hG hGsupp m n _ _
    · exact integrable_zero _ _ _]
  refine sum_congr rfl fun n _ => ?_
  split_ifs
  · exact integral_sub_right_eq_self (fun u => G m u * G n u) _
  · simp

/-- The lag `+log k`: only `n = mk` survives. -/
theorem integral_windowTest_mul_shift_pos (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {N : ℕ} (hw : w < atomSpacing N) {k : ℕ}
    (hk : 1 ≤ k) :
    ∫ t, windowTest N G t * windowTest N G (t + Real.log k) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, if n = m * k then windowGram G m n else 0 := by
  have hpt : ∀ t, windowTest N G t * windowTest N G (t + Real.log k) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        if n = m * k then G m (t - Real.log m) * G n (t - Real.log m) else 0 := by
    intro t
    rw [windowTest, windowTest, sum_mul_sum]
    refine sum_congr rfl fun m hm => sum_congr rfl fun n hn => ?_
    have hm1 := (Finset.mem_Icc.mp hm).1
    have hlogmk : Real.log ((m * k : ℕ) : ℝ) = Real.log m + Real.log k := by
      rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (show m ≠ 0 by omega))
        (by exact_mod_cast (show k ≠ 0 by omega))]
    split_ifs with h
    · rw [h, hlogmk, show t + Real.log k - (Real.log m + Real.log k) = t - Real.log m by ring]
    · have hz := window_mul_eq_zero (G := fun j => if j = n then G n else G m) (w := w)
        (fun j u hu => by split_ifs <;> exact hGsupp _ u hu) hw (Finset.mem_Icc.mp hn).1
        (Nat.mul_pos (by omega) (by omega)) ((min_le_left _ _).trans (Finset.mem_Icc.mp hn).2) h
        (t + Real.log k)
      simp only [if_neg (Ne.symm h)] at hz
      rw [hlogmk, show t + Real.log k - (Real.log m + Real.log k) = t - Real.log m by ring] at hz
      rw [mul_comm]; exact hz
  simp_rw [hpt]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ => by
    split_ifs
    · exact integrable_profile_mul hG hGsupp m n _ _
    · exact integrable_zero _ _ _]
  refine sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ fun n _ => by
    split_ifs
    · exact integrable_profile_mul hG hGsupp m n _ _
    · exact integrable_zero _ _ _]
  refine sum_congr rfl fun n _ => ?_
  split_ifs
  · exact integral_sub_right_eq_self (fun u => G m u * G n u) _
  · simp

theorem windowGram_comm (G : ℕ → ℝ → ℝ) (m n : ℕ) : windowGram G m n = windowGram G n m := by
  simp only [windowGram, mul_comm]

/-- **The prime sum of a window test is the Weil kernel against the window Gram.** -/
theorem primeSum_windowTest (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {N : ℕ} (hw : w < atomSpacing N) :
    primeSum (windowTest N G) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, windowGram G m n * weilPrimeKernel m n := by
  have hk : ∀ k : ℕ, vonMangoldtAtom k *
      ((∫ t, windowTest N G t * windowTest N G (t - Real.log k)) +
        ∫ t, windowTest N G t * windowTest N G (t + Real.log k)) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, windowGram G m n * (vonMangoldtAtom k *
        ((if m = n * k then 1 else 0) + (if n = m * k then 1 else 0))) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · simp [vonMangoldtAtom]
    rw [integral_windowTest_mul_shift_neg hG hGsupp hw hk1,
      integral_windowTest_mul_shift_pos hG hGsupp hw hk1, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    split_ifs <;> ring
  have hvanish : ∀ k ∉ range (N + 1), vonMangoldtAtom k *
      ((∫ t, windowTest N G t * windowTest N G (t - Real.log k)) +
        ∫ t, windowTest N G t * windowTest N G (t + Real.log k)) = 0 := by
    intro k hk'
    have hkN : N < k := by simpa using hk'
    rw [hk k]
    refine sum_eq_zero fun m hm => sum_eq_zero fun n hn => ?_
    have hm1 := Finset.mem_Icc.mp hm
    have hn1 := Finset.mem_Icc.mp hn
    rw [if_neg (by intro h; nlinarith), if_neg (by intro h; nlinarith)]
    simp
  rw [primeSum, tsum_eq_sum hvanish, sum_congr rfl fun k _ => hk k, sum_comm]
  refine sum_congr rfl fun m hm => ?_
  rw [sum_comm]
  refine sum_congr rfl fun n hn => ?_
  rw [← mul_sum, sum_vonMangoldtAtom_hecke hm hn]

/-- Cauchy–Schwarz for two windows: `|⟨G_m, G_n⟩| ≤ y_m y_n`. -/
theorem abs_windowGram_le (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (m n : ℕ) :
    |windowGram G m n| ≤ windowNorm G m * windowNorm G n := by
  have hsq : ∀ j, Integrable fun u => G j u ^ 2 := fun j => by
    simpa [sq] using integrable_profile_mul hG hGsupp j j 0 0
  have h := HTGeometry.sq_integral_mul_le (hG m).continuous.aestronglyMeasurable
    (hG n).continuous.aestronglyMeasurable (hsq m) (hsq n)
  rw [← windowNorm_sq, ← windowNorm_sq, ← mul_pow] at h
  exact abs_le_of_sq_le_sq' h (mul_nonneg (windowNorm_nonneg G m) (windowNorm_nonneg G n)) |>.elim
    (fun h1 h2 => abs_le.mpr ⟨h1, h2⟩)

/-- **The prime sum is at most the atomic prime form of the window norms.** -/
theorem primeSum_windowTest_le (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {N : ℕ} (hw : w < atomSpacing N) :
    primeSum (windowTest N G) ≤ atomicWeilForm N (windowNorm G) := by
  rw [primeSum_windowTest hG hGsupp hw, atomicWeilForm]
  refine sum_le_sum fun m _ => sum_le_sum fun n _ => ?_
  exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (abs_windowGram_le hG hGsupp m n))
    (weilPrimeKernel_nonneg m n)

/-! ### The Lévy energy -/

/-- The pair correlation `c_{mn}(s) = ∫ G_m(v) G_n(v + s) dv`. -/
def pairCorr (G : ℕ → ℝ → ℝ) (m n : ℕ) (s : ℝ) : ℝ := ∫ v, G m v * G n (v + s)

theorem integral_windowTest_mul_shift (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (N : ℕ) (y : ℝ) :
    ∫ u, windowTest N G u * windowTest N G (u + y) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, pairCorr G m n (y - (Real.log n - Real.log m)) := by
  have hint : ∀ m n : ℕ, Integrable fun u => G m (u - Real.log m) * G n (u + y - Real.log n) :=
    fun m n => (integrable_profile_mul hG hGsupp m n (Real.log m) (Real.log n - y)).congr
      (ae_of_all _ fun u => by
        show G m (u - Real.log m) * G n (u - (Real.log n - y)) =
          G m (u - Real.log m) * G n (u + y - Real.log n)
        rw [show u - (Real.log n - y) = u + y - Real.log n by ring])
  have hpt : ∀ u, windowTest N G u * windowTest N G (u + y) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, G m (u - Real.log m) * G n (u + y - Real.log n) := by
    intro u; rw [windowTest, windowTest, sum_mul_sum]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ => hint m n]
  refine sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ fun n _ => hint m n]
  refine sum_congr rfl fun n _ => ?_
  rw [pairCorr, ← integral_sub_right_eq_self
    (fun v => G m v * G n (v + (y - (Real.log n - Real.log m)))) (Real.log m)]
  congr 1
  funext u
  rw [show u - Real.log m + (y - (Real.log n - Real.log m)) = u + y - Real.log n by ring]

/-- **The shifted energy with its diagonal**: `∫ (f − f(·+y))² = Σ_m ∫ (G_m − G_m(·+y))² −
2 Σ_{m ≠ n} c_{mn}(y − log(n/m))`. -/
theorem integral_sub_shift_sq_windowTest_eq (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {N : ℕ} (hw : w < atomSpacing N) (y : ℝ) :
    ∫ u, (windowTest N G u - windowTest N G (u + y)) ^ 2 =
      ∑ m ∈ Icc 1 N, (∫ u, (G m u - G m (u + y)) ^ 2) -
        2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else
          pairCorr G m n (y - (Real.log n - Real.log m))) := by
  have hf := (contDiff_windowTest hG N).continuous
  have hfc := hasCompactSupport_windowTest hGsupp N
  rw [integral_sub_shift_sq_eq hf hfc, integral_windowTest_mul_shift hG hGsupp N y,
    integral_windowTest_sq hG hGsupp hw]
  have hself : ∀ m, ∫ u, (G m u - G m (u + y)) ^ 2 =
      2 * (∫ u, G m u ^ 2) - 2 * pairCorr G m m (y - (Real.log m - Real.log m)) := by
    intro m
    rw [integral_sub_shift_sq_eq (hG m).continuous (hasCompactSupport_profile hGsupp m), sub_self,
      sub_zero, pairCorr]
  have hdiag : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, pairCorr G m n (y - (Real.log n - Real.log m)) =
      ∑ m ∈ Icc 1 N, pairCorr G m m (y - (Real.log m - Real.log m)) +
        ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else
          pairCorr G m n (y - (Real.log n - Real.log m))) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun m hm => sum_eq_diag_add hm _
  rw [hdiag, sum_congr rfl fun m _ => hself m, sum_sub_distrib, ← mul_sum, ← mul_sum]
  ring

/-- Cauchy–Schwarz for a shifted pair: `|c_{mn}(s)| ≤ y_m y_n`. -/
theorem abs_pairCorr_le (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (m n : ℕ) (s : ℝ) :
    |pairCorr G m n s| ≤ windowNorm G m * windowNorm G n := by
  have hsq : ∀ j, Integrable fun u => G j u ^ 2 := fun j => by
    simpa [sq] using integrable_profile_mul hG hGsupp j j 0 0
  have h := HTGeometry.sq_integral_mul_le (hG m).continuous.aestronglyMeasurable
    ((hG n).continuous.comp (continuous_add_const s)).aestronglyMeasurable (hsq m)
    ((hsq n).comp_add_right s)
  simp only [Function.comp_def] at h
  rw [integral_add_right_eq_self (fun v => G n v ^ 2) s, ← windowNorm_sq, ← windowNorm_sq,
    ← mul_pow] at h
  exact abs_le_of_sq_le_sq' h (mul_nonneg (windowNorm_nonneg G m) (windowNorm_nonneg G n)) |>.elim
    (fun h1 h2 => abs_le.mpr ⟨h1, h2⟩)

theorem pairCorr_eq_zero (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (m n : ℕ) {s : ℝ}
    (hs : w < |s|) : pairCorr G m n s = 0 := by
  have hpt : ∀ v, G m v * G n (v + s) = 0 := fun v => by
    by_cases hv : v ∈ Set.Icc 0 w
    · by_cases hvs : v + s ∈ Set.Icc 0 w
      · exfalso
        obtain ⟨h1, h2⟩ := hv
        obtain ⟨h3, h4⟩ := hvs
        have : |s| ≤ w := abs_le.mpr ⟨by linarith, by linarith⟩
        linarith
      · rw [hGsupp n _ hvs, mul_zero]
    · rw [hGsupp m _ hv, zero_mul]
  simp [pairCorr, hpt]

/-- **The Lévy energy of a window test with its pair windows**: the diagonal is kept exactly and
the pair `(m, n)` costs at most `y_m y_n` times the Lévy mass of its window
`[log(n/m) − w, log(n/m) + w]` on `(0, ∞)`. -/
theorem levyEnergy_windowTest_ge_windows (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ atomSpacing N / 2) :
    ∑ m ∈ Icc 1 N, levyEnergy (G m) -
        2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else
          |windowNorm G m| * |windowNorm G n| * ∫ t in Set.Ioi 0,
            (Set.Icc (Real.log n - Real.log m - w) (Real.log n - Real.log m + w)).indicator
              archLevyDensity t) ≤
      levyEnergy (windowTest N G) := by
  have hδ := atomSpacing_pos hN
  have hw' : w < atomSpacing N := by linarith
  set ω := archLevyDensity
  set y := windowNorm G
  set win : ℕ → ℕ → Set ℝ := fun m n =>
    Set.Icc (Real.log n - Real.log m - w) (Real.log n - Real.log m + w)
  have hsep : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N, m ≠ n → 2 * w ≤ |Real.log n - Real.log m| := by
    intro m hm n hn hmn
    have := atomSpacing_le_abs_logGap hm hn hmn
    simp only [logGap] at this
    linarith
  have hwin : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N, m ≠ n →
      IntegrableOn ((win m n).indicator ω) (Set.Ioi 0) ∧
        ∫ t in Set.Ioi 0, (win m n).indicator ω t ≤
          2 * w * (1 / |Real.log n - Real.log m| + 1) :=
    fun m hm n hn hmn => window_integrable_and_le hw0 (hsep m hm n hn hmn)
  set c : ℕ → ℕ → ℝ → ℝ := fun m n t =>
    if m = n then 0 else |y m| * |y n| * (win m n).indicator ω t
  have hcint : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N, IntegrableOn (c m n) (Set.Ioi 0) := by
    intro m hm n hn
    by_cases hmn : m = n
    · simp only [c, if_pos hmn]; exact integrableOn_zero
    · simp only [c, if_neg hmn]; exact (hwin m hm n hn hmn).1.const_mul _
  have hGint : ∀ m, IntegrableOn
      (fun t => ω t * ∫ u, (G m u - G m (u + t)) ^ 2) (Set.Ioi 0) :=
    fun m => integrableOn_levyIntegrand (hG m) (hasCompactSupport_profile hGsupp m)
  have hcsum : IntegrableOn (fun t => ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m n t) (Set.Ioi 0) :=
    integrable_finsetSum _ fun m hm => integrable_finsetSum _ fun n hn => hcint m hm n hn
  have hdsum : IntegrableOn
      (fun t => ∑ m ∈ Icc 1 N, ω t * ∫ u, (G m u - G m (u + t)) ^ 2) (Set.Ioi 0) :=
    integrable_finsetSum _ fun m _ => hGint m
  set ℓ : ℝ → ℝ := fun t => ∑ m ∈ Icc 1 N, ω t * (∫ u, (G m u - G m (u + t)) ^ 2) -
    2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m n t
  have hℓint : IntegrableOn ℓ (Set.Ioi 0) := hdsum.sub (hcsum.const_mul _)
  have hf := contDiff_windowTest hG N
  have hfc := hasCompactSupport_windowTest hGsupp N
  -- pointwise in the shift
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ),
      ℓ t ≤ ω t * ∫ u, (windowTest N G u - windowTest N G (u + t)) ^ 2 := by
    intro t ht
    have hω0 : 0 ≤ ω t := (archLevyDensity_pos ht).le
    rw [integral_sub_shift_sq_windowTest_eq hG hGsupp hw' t]
    have hpair : ∀ m n, ω t * (if m = n then 0 else
        pairCorr G m n (t - (Real.log n - Real.log m))) ≤ c m n t := by
      intro m n
      by_cases hmn : m = n
      · simp [c, hmn]
      simp only [c, if_neg hmn]
      by_cases hmem : t ∈ win m n
      · rw [Set.indicator_of_mem hmem]
        have hb := (le_abs_self _).trans (abs_pairCorr_le hG hGsupp m n
          (t - (Real.log n - Real.log m)))
        rw [abs_of_nonneg (windowNorm_nonneg G m), abs_of_nonneg (windowNorm_nonneg G n)]
        nlinarith [mul_le_mul_of_nonneg_left hb hω0]
      · rw [Set.indicator_of_notMem hmem, mul_zero]
        have hout : w < |t - (Real.log n - Real.log m)| := by
          by_contra h
          obtain ⟨h1, h2⟩ := abs_le.mp (not_lt.mp h)
          exact hmem ⟨by linarith, by linarith⟩
        rw [pairCorr_eq_zero hGsupp m n hout, mul_zero]
    have hsum : ω t * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else
        pairCorr G m n (t - (Real.log n - Real.log m))) ≤
        ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m n t := by
      rw [mul_sum]
      refine sum_le_sum fun m _ => ?_
      rw [mul_sum]
      exact sum_le_sum fun n _ => hpair m n
    simp only [ℓ]
    have e : ω t * (∑ m ∈ Icc 1 N, (∫ u, (G m u - G m (u + t)) ^ 2) -
        2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else
          pairCorr G m n (t - (Real.log n - Real.log m)))) =
        ∑ m ∈ Icc 1 N, ω t * (∫ u, (G m u - G m (u + t)) ^ 2) -
          2 * (ω t * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else
            pairCorr G m n (t - (Real.log n - Real.log m)))) := by
      rw [mul_sub, Finset.mul_sum]; ring
    rw [e]
    linarith [hsum]
  have hLint : IntegrableOn
      (fun t => ω t * ∫ u, (windowTest N G u - windowTest N G (u + t)) ^ 2) (Set.Ioi 0) :=
    integrableOn_levyIntegrand hf hfc
  have hmono := setIntegral_mono_on hℓint hLint measurableSet_Ioi hpt
  have hℓ : ∫ t in Set.Ioi 0, ℓ t = ∑ m ∈ Icc 1 N, levyEnergy (G m) -
      2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, ∫ t in Set.Ioi 0, c m n t := by
    simp only [ℓ]
    rw [integral_sub hdsum (hcsum.const_mul _), integral_const_mul,
      integral_finsetSum _ fun m _ => hGint m, integral_finsetSum _ fun m hm =>
        integrable_finsetSum _ fun n hn => hcint m hm n hn]
    congr 2
    exact sum_congr rfl fun m hm => integral_finsetSum _ fun n hn => hcint m hm n hn
  have hcbound : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, ∫ t in Set.Ioi 0, c m n t =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else
        |y m| * |y n| * ∫ t in Set.Ioi 0, (win m n).indicator ω t) := by
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
    by_cases hmn : m = n
    · simp [c, hmn]
    simp only [c, if_neg hmn]
    rw [integral_const_mul]
  rw [hℓ] at hmono
  have hL : levyEnergy (windowTest N G) = ∫ t in Set.Ioi 0,
      ω t * ∫ u, (windowTest N G u - windowTest N G (u + t)) ^ 2 := rfl
  linarith

/-- **Lower bound on the Lévy energy of a window test**, the diagonal kept exactly:
`levyEnergy f ≥ Σ_m levyEnergy G_m − 2 Σ_{m ≠ n} y_m y_n · 2w(1/|log(n/m)| + 1)`. -/
theorem levyEnergy_windowTest_ge_diag (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ atomSpacing N / 2) :
    ∑ m ∈ Icc 1 N, levyEnergy (G m) -
        2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else
          |windowNorm G m| * |windowNorm G n| * (2 * w * (1 / |Real.log n - Real.log m| + 1))) ≤
      levyEnergy (windowTest N G) := by
  have h := levyEnergy_windowTest_ge_windows hG hGsupp hN hw0 hw
  have hb : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else
      |windowNorm G m| * |windowNorm G n| * ∫ t in Set.Ioi 0,
        (Set.Icc (Real.log n - Real.log m - w) (Real.log n - Real.log m + w)).indicator
          archLevyDensity t) ≤
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else
        |windowNorm G m| * |windowNorm G n| * (2 * w * (1 / |Real.log n - Real.log m| + 1))) := by
    refine sum_le_sum fun m hm => sum_le_sum fun n hn => ?_
    by_cases hmn : m = n
    · simp [hmn]
    simp only [if_neg hmn]
    have hsep := atomSpacing_le_abs_logGap hm hn hmn
    simp only [logGap] at hsep
    exact mul_le_mul_of_nonneg_left (window_integrable_and_le hw0 (by linarith)).2 (by positivity)
  linarith

/-- **The self-energy of a window**: a `C²` bump supported in `[0, w]`, `w ≤ 1`, has
`levyEnergy G ≥ (log(1/w) + 2c_∞ − (e^{1/2}/2) w) ‖G‖²`. -/
theorem levyEnergy_profile_ge {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 < w) (hw1 : w ≤ 1) :
    (Real.log (1 / w) + archRobinConstant - Real.exp (1 / 2) / 2 * w) * ∫ u, g u ^ 2 ≤
      levyEnergy g := by
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hgsupp
  obtain ⟨C, hC⟩ := hg.lipschitzWith_of_hasCompactSupport hgc two_ne_zero
  have hK : ∀ u v, |g u - g v| ≤ (C : ℝ) * |u - v| := fun u v => by
    simpa [Real.dist_eq] using hC.dist_le_mul u v
  have h := abs_levyEnergy_atom_sub_le hg hgc hgsupp hw0 hw1 hK
  have hβ : 0 ≤ bumpRobin g w := setIntegral_nonneg measurableSet_Ioc fun t ht =>
    div_nonneg (integral_nonneg fun _ => sq_nonneg _) (by linarith [ht.1])
  have := (abs_le.mp h).1
  linarith

/-! ### The Markov form keeps its defect -/

/-- **The Markov form of a window test with its defect.** Eventually in `N`, at every width
`w ≤ δ_N/2` with `wN ≤ 1/(64e²)`, every window test has `M(f) ≥ φ₀|y|² + c₀ D_N(y)` with
`φ₀ = 2θ′(0) + log(1/(wN)) + 2c_∞ + γ − ε − (e^{1/2}/2) w − A wN` and `c₀ = 1 − ε − 32e² wN`. -/
theorem eventually_markovEnergy_windowTest_ge {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ atomSpacing N / 2 →
      ∀ G : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ 2 (G n)) → (∀ n u, u ∉ Set.Icc 0 w → G n u = 0) →
        (2 * gammaHardyPhaseRate 0 + Real.log (1 / (w * N)) + archRobinConstant + γ - ε -
            Real.exp (1 / 2) / 2 * w - markovCrossConstant * (w * N)) *
            (∑ n ∈ Icc 1 N, windowNorm G n ^ 2) +
          (1 - ε - 32 * Real.exp 2 * (w * N)) * poleDefect N (windowNorm G) ≤
          markovEnergy (fun u => (windowTest N G u : ℂ)) := by
  obtain ⟨N₁, hN₁⟩ := eventually_atomicWeilForm_add_poleDefect_le hε
  refine ⟨max N₁ 1, fun N hN w hw0 hw G hG hGsupp => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hδ := atomSpacing_pos hN1
  have hδ1 := atomSpacing_le_one hN1
  have hw' : w < atomSpacing N := by linarith
  have hw1 : w ≤ 1 := by linarith
  have hf := contDiff_windowTest hG N
  have hfc := hasCompactSupport_windowTest hGsupp N
  rw [markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, archForm_eq_levyEnergy hf hfc,
    integral_windowTest_sq hG hGsupp hw']
  have hy : ∑ n ∈ Icc 1 N, ∫ u, G n u ^ 2 = ∑ n ∈ Icc 1 N, windowNorm G n ^ 2 :=
    sum_congr rfl fun n _ => (windowNorm_sq G n).symm
  rw [hy]
  have hlevy := levyEnergy_windowTest_ge_diag hG hGsupp hN1 hw0 hw
  have hpen := cross_penalty_le hN1 hw0 (windowNorm G)
  have hP := hN₁ N (le_trans (le_max_left _ _) hN) (windowNorm G)
  have hprime := primeSum_windowTest_le hG hGsupp hw'
  have hself : (Real.log (1 / w) + archRobinConstant - Real.exp (1 / 2) / 2 * w) *
      (∑ n ∈ Icc 1 N, windowNorm G n ^ 2) ≤ ∑ m ∈ Icc 1 N, levyEnergy (G m) := by
    rw [mul_sum]
    refine sum_le_sum fun n _ => ?_
    rw [windowNorm_sq]
    exact levyEnergy_profile_ge (hG n) (hGsupp n) hw0 hw1
  have hlog : Real.log (1 / (w * N)) = Real.log (1 / w) - Real.log N := by
    rw [one_div, Real.log_inv, Real.log_mul hw0.ne' hN0.ne', one_div, Real.log_inv]; ring
  rw [hlog]
  unfold markovCrossConstant
  linarith

/-! ### The defect pays the pole -/

theorem integral_abs_profile_le (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (hw0 : 0 < w) (n : ℕ) :
    ∫ u, |G n u| ≤ Real.sqrt w * windowNorm G n := by
  have h := sq_integral_abs_le (hG n).continuous (hGsupp n) hw0
  rw [← windowNorm_sq] at h
  have h0 : 0 ≤ ∫ u, |G n u| := integral_nonneg fun _ => abs_nonneg _
  calc ∫ u, |G n u| ≤ Real.sqrt (w * windowNorm G n ^ 2) := (Real.le_sqrt h0 (by positivity)).mpr h
    _ = Real.sqrt w * windowNorm G n := by
        rw [Real.sqrt_mul hw0.le, Real.sqrt_sq (windowNorm_nonneg G n)]

/-- The moment of a window test is the sum of the window moments. -/
theorem integral_windowTest_mul (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) {φ : ℝ → ℝ} (hφ : Continuous φ) (N : ℕ) :
    ∫ u, windowTest N G u * φ u = ∑ n ∈ Icc 1 N, ∫ u, G n (u - Real.log n) * φ u := by
  simp only [windowTest, sum_mul]
  refine integral_finsetSum _ fun n _ => ?_
  exact (((hG n).continuous.comp (continuous_sub_right _)).mul hφ).integrable_of_hasCompactSupport
    ((hasCompactSupport_profile hGsupp n).comp_homeomorph (Homeomorph.subRight _)).mul_right

/-- **The defect pays the pole** for window tests: for `N ≥ 3`,
`2|AB| ≤ c_P e^{w/2} wN (2|y|² + D_N(y))`. -/
theorem two_mul_abs_poleMoments_windowTest_le (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (hw0 : 0 < w) {N : ℕ} (hN : 3 ≤ N) :
    2 * |(∫ u, windowTest N G u * Real.exp (-(u / 2))) * ∫ u, windowTest N G u * Real.exp (u / 2)| ≤
      poleConstant * Real.exp (w / 2) * (w * N) *
        (2 * ∑ n ∈ Icc 1 N, windowNorm G n ^ 2 + poleDefect N (windowNorm G)) := by
  set y := windowNorm G
  set X := ∑ n ∈ Icc 1 N, y n ^ 2
  set D := poleDefect N y
  set sw := Real.sqrt w
  have hsw : sw ^ 2 = w := Real.sq_sqrt hw0.le
  have hsw0 : 0 ≤ sw := Real.sqrt_nonneg w
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hL1 : 1 ≤ Real.log N := by
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have he : Real.exp 1 ≤ 3 := le_of_lt (Real.exp_one_lt_d9.trans (by norm_num))
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (he.trans h3)
  have hX : 0 ≤ X := sum_nonneg fun _ _ => sq_nonneg _
  have hD : 0 ≤ D := poleDefect_nonneg N y
  have hy0 : ∀ n, 0 ≤ y n := windowNorm_nonneg G
  -- the window moments
  have hA : |∫ u, windowTest N G u * Real.exp (-(u / 2))| ≤
      sw * ∑ n ∈ Icc 1 N, y n * Real.exp (-(Real.log n / 2)) := by
    rw [integral_windowTest_mul hG hGsupp (by fun_prop), mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
    have h := abs_integral_shift_mul_le (hG n).continuous (hasCompactSupport_profile hGsupp n)
      (hGsupp n) (φ := fun u => Real.exp (-(u / 2))) (by fun_prop) (c := Real.log n)
      (M := Real.exp (-(Real.log n / 2))) fun u hu => by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (by linarith [hu.1])
    have h2 := integral_abs_profile_le hG hGsupp hw0 n
    calc _ ≤ Real.exp (-(Real.log n / 2)) * ∫ u, |G n u| := h
      _ ≤ Real.exp (-(Real.log n / 2)) * (sw * y n) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = sw * (y n * Real.exp (-(Real.log n / 2))) := by ring
  have hB : |∫ u, windowTest N G u * Real.exp (u / 2)| ≤
      Real.exp (w / 2) * sw * ∑ n ∈ Icc 1 N, y n * Real.sqrt n := by
    rw [integral_windowTest_mul hG hGsupp (by fun_prop), mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hsq : Real.exp (Real.log n / 2) = Real.sqrt n := by
      rw [← Real.sqrt_sq (Real.exp_pos _).le, exp_half_log_sq hn1]
    have h := abs_integral_shift_mul_le (hG n).continuous (hasCompactSupport_profile hGsupp n)
      (hGsupp n) (φ := fun u => Real.exp (u / 2)) (by fun_prop) (c := Real.log n)
      (M := Real.exp (Real.log n / 2) * Real.exp (w / 2)) fun u hu => by
        rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith [hu.2])
    rw [hsq] at h
    have h2 := integral_abs_profile_le hG hGsupp hw0 n
    calc _ ≤ Real.sqrt n * Real.exp (w / 2) * ∫ u, |G n u| := h
      _ ≤ Real.sqrt n * Real.exp (w / 2) * (sw * y n) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Real.exp (w / 2) * sw * (y n * Real.sqrt n) := by ring
  -- the `H`-row by Cauchy–Schwarz, the `V`-row by the multiplicative Hardy inequality
  set S₁ := ∑ n ∈ Icc 1 N, y n * Real.exp (-(Real.log n / 2))
  set S₂ := ∑ n ∈ Icc 1 N, y n * Real.sqrt n
  have hS₁ : S₁ ^ 2 ≤ X * (2 * Real.log N) := by
    have h := sum_mul_sq_le_sq_mul_sq (Icc 1 N) y (fun n => Real.exp (-(Real.log n / 2)))
    have hharm : ∑ n ∈ Icc 1 N, (1 : ℝ) / n ≤ 1 + Real.log N := by
      have h := harmonic_le_one_add_log N
      simp only [_root_.harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
      simpa only [one_div] using h
    have e2 : ∑ n ∈ Icc 1 N, Real.exp (-(Real.log n / 2)) ^ 2 = ∑ n ∈ Icc 1 N, (1 : ℝ) / n :=
      sum_congr rfl fun n hn => exp_neg_half_log_sq (Finset.mem_Icc.mp hn).1
    rw [e2] at h
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith) hX)
  have hS₂ : S₂ ^ 2 ≤ hardyConstant * ((N : ℝ) ^ 2 / Real.log N) * (D + X) := by
    have h := sq_vRow_le hN y
    have e1 : ∑ n ∈ Icc 1 N, Real.sqrt n * y n = S₂ := sum_congr rfl fun n _ => mul_comm _ _
    rw [e1] at h
    exact h
  have hS₁0 : 0 ≤ S₁ := sum_nonneg fun n _ => mul_nonneg (hy0 n) (Real.exp_pos _).le
  have hS₂0 : 0 ≤ S₂ := sum_nonneg fun n _ => mul_nonneg (hy0 n) (Real.sqrt_nonneg _)
  set P := (∫ u, windowTest N G u * Real.exp (-(u / 2))) * ∫ u, windowTest N G u * Real.exp (u / 2)
  have hP : |P| ≤ sw * S₁ * (Real.exp (w / 2) * sw * S₂) := by
    rw [abs_mul]; exact mul_le_mul hA hB (abs_nonneg _) (by positivity)
  have hP2 : P ^ 2 ≤ 2 * hardyConstant * Real.exp w * (w * N) ^ 2 * X * (D + X) := by
    have hexp : Real.exp (w / 2) ^ 2 = Real.exp w := by rw [← Real.exp_nat_mul]; ring_nf
    have hP' : P ^ 2 ≤ (sw * S₁ * (Real.exp (w / 2) * sw * S₂)) ^ 2 := by
      rw [← sq_abs P]; exact pow_le_pow_left₀ (abs_nonneg _) hP 2
    have e : (sw * S₁ * (Real.exp (w / 2) * sw * S₂)) ^ 2 =
        Real.exp w * (sw ^ 2) ^ 2 * (S₁ ^ 2 * S₂ ^ 2) := by rw [← hexp]; ring
    rw [e, hsw] at hP'
    have hSS : S₁ ^ 2 * S₂ ^ 2 ≤
        X * (2 * Real.log N) * (hardyConstant * ((N : ℝ) ^ 2 / Real.log N) * (D + X)) :=
      mul_le_mul hS₁ hS₂ (sq_nonneg _) (by positivity)
    have e2 : X * (2 * Real.log N) * (hardyConstant * ((N : ℝ) ^ 2 / Real.log N) * (D + X)) =
        2 * hardyConstant * N ^ 2 * X * (D + X) := by field_simp
    rw [e2] at hSS
    calc P ^ 2 ≤ Real.exp w * w ^ 2 * (S₁ ^ 2 * S₂ ^ 2) := hP'
      _ ≤ Real.exp w * w ^ 2 * (2 * hardyConstant * N ^ 2 * X * (D + X)) :=
          mul_le_mul_of_nonneg_left hSS (by positivity)
      _ = 2 * hardyConstant * Real.exp w * (w * N) ^ 2 * X * (D + X) := by ring
  set c := poleConstant * Real.exp (w / 2) * (w * N)
  have hc0 : 0 ≤ c := by have := poleConstant_pos; positivity
  have hc2 : c ^ 2 = 2 * hardyConstant * Real.exp w * (w * N) ^ 2 := by
    simp only [c]
    rw [mul_pow, mul_pow, poleConstant_sq, ← Real.exp_nat_mul]; ring_nf
  have h2 : (2 * |P|) ^ 2 ≤ (c * (2 * X + D)) ^ 2 := by
    have hl : (2 * |P|) ^ 2 = 4 * P ^ 2 := by rw [mul_pow, sq_abs]; norm_num
    have hr : (c * (2 * X + D)) ^ 2 = c ^ 2 * (2 * X + D) ^ 2 := by ring
    rw [hl, hr, hc2]
    nlinarith [mul_nonneg (mul_nonneg hardyConstant_pos.le (Real.exp_pos w).le)
      (sq_nonneg (w * N)), sq_nonneg D]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h2

/-! ### Weil positivity -/

/-- **Weil positivity on window tests from the finite part.** Eventually in `N`, at every width
`w ≤ δ_N/2` with `c_P e^{w/2} wN ≤ c₀` and `2c_P e^{w/2} wN ≤ φ₀`, Weil's form is nonnegative on
every window test. -/
theorem eventually_weilQuad_windowTest_nonneg_of_finitePart {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ atomSpacing N / 2 →
      poleConstant * Real.exp (w / 2) * (w * N) ≤ 1 - ε - 32 * Real.exp 2 * (w * N) →
      2 * (poleConstant * Real.exp (w / 2) * (w * N)) ≤
        2 * gammaHardyPhaseRate 0 + Real.log (1 / (w * N)) + archRobinConstant + γ - ε -
          Real.exp (1 / 2) / 2 * w - markovCrossConstant * (w * N) →
      ∀ G : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ 2 (G n)) → (∀ n u, u ∉ Set.Icc 0 w → G n u = 0) →
        0 ≤ weilQuad (windowTest N G) := by
  obtain ⟨N₀, hN₀⟩ := eventually_markovEnergy_windowTest_ge hε
  refine ⟨max N₀ 3, fun N hN w hw0 hw hc₀ hφ₀ G hG hGsupp => ?_⟩
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hM := hN₀ N (le_trans (le_max_left _ _) hN) w hw0 hw G hG hGsupp
  have hf := contDiff_windowTest hG N
  have hfc := hasCompactSupport_windowTest hGsupp N
  have hpole := two_mul_abs_poleMoments_windowTest_le hG hGsupp hw0 hN3
  have hW : weilQuad (windowTest N G) = markovEnergy (fun u => (windowTest N G u : ℂ)) +
      2 * ((∫ u, windowTest N G u * Real.exp (-(u / 2))) *
        ∫ u, windowTest N G u * Real.exp (u / 2)) := by
    rw [weilQuad_eq hf hfc, add_sub_assoc, two_mul_cosh_sq_sub_sinh_sq_eq hf.continuous hfc,
      markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, archForm_eq_levyEnergy hf hfc]
    ring
  rw [hW]
  set X := ∑ n ∈ Icc 1 N, windowNorm G n ^ 2
  set D := poleDefect N (windowNorm G)
  set c := poleConstant * Real.exp (w / 2) * (w * N)
  set P := (∫ u, windowTest N G u * Real.exp (-(u / 2))) * ∫ u, windowTest N G u * Real.exp (u / 2)
  have hX : 0 ≤ X := sum_nonneg fun _ _ => sq_nonneg _
  have hD : 0 ≤ D := poleDefect_nonneg N _
  have hP := neg_abs_le P
  nlinarith

/-- The fraction `K★_∞(ε)` of the spacing for window tests: `K★` with the Robin constant of the
profile replaced by its profile-free part `2c_∞`. -/
def windowFraction (ε : ℝ) : ℝ :=
  min (min markovOverlapBound (1 / (4 * (poleConstant * Real.exp (1 / 2) + 32 * Real.exp 2))))
    (min (1 / (markovCrossConstant + 2 * (poleConstant * Real.exp (1 / 2))))
      (Real.exp (2 * gammaHardyPhaseRate 0 + archRobinConstant + γ - ε - 2)))

theorem windowFraction_pos (ε : ℝ) : 0 < windowFraction ε := by
  have := poleConstant_pos
  have := markovCrossConstant_pos
  unfold windowFraction markovOverlapBound
  exact lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (Real.exp_pos _))

/-- **Weil positivity on every window test at the fraction `K★_∞(ε)`, eventually in `N`.** -/
theorem eventually_weilQuad_windowTest_nonneg {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ windowFraction ε * atomSpacing N →
      ∀ G : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ 2 (G n)) → (∀ n u, u ∉ Set.Icc 0 w → G n u = 0) →
        0 ≤ weilQuad (windowTest N G) := by
  obtain ⟨N₀, hN₀⟩ := eventually_weilQuad_windowTest_nonneg_of_finitePart hε
  refine ⟨max N₀ 1, fun N hN w hw0 hw => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hδ := atomSpacing_pos hN1
  have hδN : atomSpacing N * N ≤ 1 := by
    have h := atomSpacing_le_inv hN1
    calc atomSpacing N * N ≤ 1 / N * N := mul_le_mul_of_nonneg_right h hN0.le
      _ = 1 := by field_simp
  set Ks := windowFraction ε
  have hKs := windowFraction_pos ε
  have hc := poleConstant_pos
  have hA := markovCrossConstant_pos
  have hK1 : Ks ≤ markovOverlapBound := (min_le_left _ _).trans (min_le_left _ _)
  have hK2 : Ks ≤ 1 / (4 * (poleConstant * Real.exp (1 / 2) + 32 * Real.exp 2)) :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hK3 : Ks ≤ 1 / (markovCrossConstant + 2 * (poleConstant * Real.exp (1 / 2))) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hK4 : Ks ≤ Real.exp (2 * gammaHardyPhaseRate 0 + archRobinConstant + γ - ε - 2) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hMOB : markovOverlapBound ≤ 1 / 2 := by
    unfold markovOverlapBound
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.add_one_le_exp 2]
  have hwN : w * N ≤ Ks := by
    calc w * N ≤ Ks * atomSpacing N * N := mul_le_mul_of_nonneg_right hw hN0.le
      _ = Ks * (atomSpacing N * N) := by ring
      _ ≤ Ks * 1 := mul_le_mul_of_nonneg_left hδN hKs.le
      _ = Ks := mul_one Ks
  have hwN0 : 0 < w * N := by positivity
  have hw2 : w ≤ atomSpacing N / 2 := by
    calc w ≤ Ks * atomSpacing N := hw
      _ ≤ 1 / 2 * atomSpacing N := mul_le_mul_of_nonneg_right (hK1.trans hMOB) hδ.le
      _ = atomSpacing N / 2 := by ring
  have hw1 : w ≤ 1 / 2 := by linarith [atomSpacing_le_one hN1]
  have hexp : Real.exp (w / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith)
  have hcK : poleConstant * Real.exp (w / 2) * (w * N) ≤ poleConstant * Real.exp (1 / 2) * Ks :=
    mul_le_mul (mul_le_mul_of_nonneg_left hexp hc.le) hwN hwN0.le (by positivity)
  refine hN₀ N (le_trans (le_max_left _ _) hN) w hw0 hw2 ?_ ?_
  · have h4 : (poleConstant * Real.exp (1 / 2) + 32 * Real.exp 2) * Ks ≤ 1 / 4 := by
      have hpos : 0 < 4 * (poleConstant * Real.exp (1 / 2) + 32 * Real.exp 2) := by positivity
      rw [le_div_iff₀ hpos] at hK2
      linarith
    have : 32 * Real.exp 2 * (w * N) ≤ 32 * Real.exp 2 * Ks :=
      mul_le_mul_of_nonneg_left hwN (by positivity)
    nlinarith
  · have h5 : (markovCrossConstant + 2 * (poleConstant * Real.exp (1 / 2))) * Ks ≤ 1 := by
      have hpos : 0 < markovCrossConstant + 2 * (poleConstant * Real.exp (1 / 2)) := by positivity
      rw [le_div_iff₀ hpos] at hK3
      linarith
    have hlog : -(2 * gammaHardyPhaseRate 0 + archRobinConstant + γ - ε - 2) ≤
        Real.log (1 / (w * N)) := by
      have h6 : Real.log (w * N) ≤ 2 * gammaHardyPhaseRate 0 + archRobinConstant + γ - ε - 2 := by
        have := Real.log_le_log hwN0 (hwN.trans hK4)
        rwa [Real.log_exp] at this
      rw [one_div, Real.log_inv]
      linarith
    have hAK : markovCrossConstant * (w * N) ≤ markovCrossConstant * Ks :=
      mul_le_mul_of_nonneg_left hwN hA.le
    have hew : Real.exp (1 / 2) / 2 * w ≤ 1 := by
      have := exp_half_lt_two
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    linarith

/-! ### Every test near the logarithms -/

/-- **Every test near the logarithms is a window test.** If `f` is `C²` and vanishes off
`⋃_{n ≤ N} [log n, log n + w]` with `w < δ_N`, then `f = Σ_n G_n(· − log n)` with `C²` profiles
supported in `[0, w]`. Here `G_n` is `f(· + log n)` on `(−η, w + η)`, `η = (δ_N − w)/2`, and `0`
off it. On the margins `f(· + log n)` vanishes, since no other window reaches them. -/
theorem windowTest_of_support {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {N : ℕ}
    (hw : w < atomSpacing N)
    (hsupp : ∀ u, f u ≠ 0 → ∃ n ∈ Icc 1 N, u ∈ Set.Icc (Real.log n) (Real.log n + w)) :
    ∃ G : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ 2 (G n)) ∧ (∀ n u, u ∉ Set.Icc 0 w → G n u = 0) ∧
      windowTest N G = f := by
  classical
  set δ := atomSpacing N
  set η := (δ - w) / 2 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  -- two windows are `δ` apart
  have hfar : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N, m ≠ n →
      Real.log m - Real.log n ≤ -δ ∨ δ ≤ Real.log m - Real.log n := fun m hm n hn hmn => by
    have h := atomSpacing_le_abs_logGap hn hm (Ne.symm hmn)
    simp only [logGap] at h
    exact le_abs'.mp h
  -- `f(u + log n) = 0` on the margins around the window of `n`
  have hzero : ∀ n ∈ Icc 1 N, ∀ u ∈ Set.Ioo (-η) (w + η), u ∉ Set.Icc 0 w →
      f (u + Real.log n) = 0 := by
    intro n hn u hu hu'
    by_contra hne
    obtain ⟨m, hm, hmem⟩ := hsupp _ hne
    rcases eq_or_ne m n with rfl | hmn
    · exact hu' ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
    · obtain ⟨h1, h2⟩ := hmem
      obtain ⟨h3, h4⟩ := hu
      rcases hfar m hm n hn hmn with h | h <;> linarith
  set G : ℕ → ℝ → ℝ := fun n u =>
    if n ∈ Icc 1 N ∧ u ∈ Set.Ioo (-η) (w + η) then f (u + Real.log n) else 0 with hGdef
  have hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0 := fun n u hu => by
    simp only [hGdef]
    split_ifs with h
    · exact hzero n h.1 u h.2 hu
    · rfl
  refine ⟨G, fun n => ?_, hGsupp, ?_⟩
  · by_cases hn : n ∈ Icc 1 N
    swap
    · have : G n = fun _ => 0 := funext fun u => by simp only [hGdef, hn, false_and, if_false]
      rw [this]; exact contDiff_const
    refine contDiff_iff_contDiffAt.mpr fun x => ?_
    by_cases hx : x ∈ Set.Ioo (-η) (w + η)
    · have hfn : ContDiff ℝ 2 (fun u => f (u + Real.log n)) :=
        hf.comp (contDiff_id.add contDiff_const)
      refine hfn.contDiffAt.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with u hu
      show (if n ∈ Icc 1 N ∧ u ∈ Set.Ioo (-η) (w + η) then f (u + Real.log n) else 0) =
        f (u + Real.log n)
      exact if_pos ⟨hn, hu⟩
    · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      rcases not_and_or.mp (fun h => hx h) with h | h
      · -- `x ≤ −η`: near `x` the profile vanishes
        filter_upwards [Iio_mem_nhds (show x < 0 by linarith [not_lt.mp h])] with u hu
        exact hGsupp n u fun h' => by linarith [h'.1, Set.mem_Iio.mp hu]
      · filter_upwards [Ioi_mem_nhds (show w < x by linarith [not_lt.mp h])] with u hu
        exact hGsupp n u fun h' => by linarith [h'.2, Set.mem_Ioi.mp hu]
  · funext u
    simp only [windowTest]
    by_cases hfu : f u = 0
    · rw [hfu]
      refine sum_eq_zero fun n hn => ?_
      simp only [hGdef]
      split_ifs
      · rw [sub_add_cancel, hfu]
      · rfl
    obtain ⟨m, hm, hmem⟩ := hsupp u hfu
    rw [Finset.sum_eq_single m]
    · simp only [hGdef, hm, true_and]
      rw [if_pos ⟨by linarith [hmem.1], by linarith [hmem.2]⟩, sub_add_cancel]
    · intro n hn hnm
      simp only [hGdef]
      rw [if_neg]
      rintro ⟨-, h3, h4⟩
      obtain ⟨h1, h2⟩ := hmem
      rcases hfar m hm n hn (Ne.symm hnm) with h | h <;> linarith
    · intro h; exact absurd hm h

theorem windowFraction_le_half (ε : ℝ) : windowFraction ε ≤ 1 / 2 := by
  have hK1 : windowFraction ε ≤ markovOverlapBound := (min_le_left _ _).trans (min_le_left _ _)
  refine hK1.trans ?_
  unfold markovOverlapBound
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [Real.add_one_le_exp 2]

/-- **Weil's form is positive on every test near the logarithms.** For `0 < ε ≤ 1/4`, eventually
in `N`, at every width `0 < w ≤ K★_∞(ε) δ_N`, every `C²` function vanishing off
`⋃_{n ≤ N} [log n, log n + w]` has nonnegative Weil form. -/
theorem eventually_weilQuad_nonneg_of_support {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ windowFraction ε * atomSpacing N →
      ∀ f : ℝ → ℝ, ContDiff ℝ 2 f →
        (∀ u, f u ≠ 0 → ∃ n ∈ Icc 1 N, u ∈ Set.Icc (Real.log n) (Real.log n + w)) →
        0 ≤ weilQuad f := by
  obtain ⟨N₀, h⟩ := eventually_weilQuad_windowTest_nonneg hε hε1
  refine ⟨max N₀ 1, fun N hN w hw0 hw f hf hsupp => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hδ := atomSpacing_pos hN1
  have hw' : w < atomSpacing N := by
    have := mul_le_mul_of_nonneg_right (windowFraction_le_half ε) hδ.le
    linarith
  obtain ⟨G, hG, hGsupp, rfl⟩ := windowTest_of_support hf hw' hsupp
  exact h N (le_trans (le_max_left _ _) hN) w hw0 hw G hG hGsupp

end GaloisForLFunctions.ArithmeticLorentzianGeometry
