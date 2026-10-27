import GaloisForLFunctions.RHTower.WeilMarkovThinNonnegativeOddPositivity
import GaloisForLFunctions.ArithmeticElectrostatics.TheWeilPrimeFormOnAtomsIsLogarithmic

/-!
# The stability law at atomic resolution

The torsion counterterm and the atomic Weil prime form both grow like `log N`
(`TheTorsionCountertermIsLogarithmic`, `TheWeilPrimeFormOnAtomsIsLogarithmic`). The archimedean
place supplies a self-energy of the same kind: a test of width `w` has Lévy gain
`e^{−1/2} log(1/w)` (`RHTower.archForm_ge_of_width`). This file matches the two and proves the
resulting adjunction law for Weil's form, without the pole term (the Markov form
`M = archForm − primeSum`), at atomic resolution.

Fix a real `C²` bump `g` supported in `[0, w]` and put a copy of it, with weight `x_n`, at each atom
`log n`, `1 ≤ n ≤ N` (`atomicTest`). The atoms are `δ_N = log(1 + 1/N)` apart.

* **Lévy gain of disjoint shifts** (`levyEnergy_ge_of_disjoint_shifts`): if every shift by
  `x ∈ (w, s]` moves the support of `f` off itself, the Lévy energy is at least
  `e^{−1/2} log(s/w) ∫ f²`.
* **The atoms do not interact through the archimedean place below their spacing**
  (`integral_atomicTest_sq`, `levyEnergy_atomicTest_ge`): for `w ≤ δ_N/4`, `∫ f² = Σ x_n² ∫ g²` and
  the Lévy energy is at least `e^{−1/2} log(δ_N/(2w)) ∫ f²`.
* **The prime sum is the atomic Weil prime form** (`primeSum_atomicTest`): for `w < δ_N`,
  `primeSum f = (∫ g²) Σ_{m,n} x_m x_n P(m, n)` exactly — only the exact Hecke relations `m = nk`
  survive.
* **The stability law** (`markovEnergy_atomicTest_ge`, `markovEnergy_atomicTest_nonneg`):
  `M(f) ≥ (2θ′(0) + e^{−1/2} log(δ_N/(2w)) − 2 log N − log 4 − 4) ∫ f²`, hence `M(f) ≥ 0` for every
  width `w ≤ atomicWidth N = (δ_N/4) exp(−e^{1/2}(2 log N + log 4 + 4 + 2|θ′(0)|))`, a power `N^{−O(1)}`.

The archimedean self-energy is a counterterm constant on all atoms — compatible with the Hecke
translations — and it preserves positivity once the atoms are narrower than a fixed power of their
spacing. At widths comparable to the spacing the gain `log(δ_N/w)` is bounded while the prime
counterterm is not (it is at least `√(log 2 (log N − C))`): the matching stops exactly where the
tests begin to see the zeros.
-/

noncomputable section

open MeasureTheory Finset RHTower
open scoped Real

namespace GaloisForLFunctions.ArithmeticElectrostatics

open ArithmeticEffectivityTheory

/-! ### The Lévy gain of disjoint shifts -/

/-- If a shift moves the support off itself, `∫ (f(u) − f(u + x))² = 2 ∫ f²`. -/
theorem integral_sq_sub_shift_of_disjoint {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {x : ℝ} (hx : ∀ u, f u * f (u + x) = 0) :
    ∫ u, (f u - f (u + x)) ^ 2 = 2 * ∫ u, f u ^ 2 := by
  have h1 : Integrable fun t => f t ^ 2 := by
    have h0 : Integrable (fun t => f t * f t) :=
      (hf.mul hf).integrable_of_hasCompactSupport hfc.mul_right
    simpa [pow_two] using h0
  have h2 : Integrable fun u => f (u + x) ^ 2 := h1.comp_add_right x
  have hpt : ∀ u, (f u - f (u + x)) ^ 2 = f u ^ 2 + f (u + x) ^ 2 := fun u => by nlinarith [hx u]
  simp_rw [hpt]
  rw [integral_add h1 h2, integral_add_right_eq_self (fun u => f u ^ 2) x]
  ring

/-- **Lévy gain of disjoint shifts**: `levyEnergy f ≥ e^{−1/2} log(s/w) ∫ f²` when every shift by
`x ∈ (w, s]`, `s ≤ 1`, moves the support of `f` off itself. -/
theorem levyEnergy_ge_of_disjoint_shifts {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {w s : ℝ} (hw0 : 0 < w) (hws : w ≤ s) (hs1 : s ≤ 1)
    (hdisj : ∀ x ∈ Set.Ioc w s, ∀ u, f u * f (u + x) = 0) :
    Real.exp (-(1 / 2)) * Real.log (s / w) * ∫ u, f u ^ 2 ≤ levyEnergy f := by
  set M : ℝ := ∫ u, f u ^ 2
  set L : ℝ → ℝ := fun x => archLevyDensity x * ∫ u, (f u - f (u + x)) ^ 2
  have hLint : IntegrableOn L (Set.Ioi 0) := integrableOn_levyIntegrand hf hfc
  have hsub : Set.Ioc w s ⊆ Set.Ioi 0 := fun x hx => lt_trans hw0 hx.1
  have hstep1 : ∫ x in Set.Ioc w s, L x ≤ ∫ x in Set.Ioi 0, L x :=
    setIntegral_mono_set hLint (levyIntegrand_nonneg f) (Filter.Eventually.of_forall hsub)
  have hlow : ∀ x ∈ Set.Ioc w s, Real.exp (-(1 / 2)) * M * x⁻¹ ≤ L x := by
    intro x hx
    have hx0 : 0 < x := lt_trans hw0 hx.1
    have hinner := integral_sq_sub_shift_of_disjoint hf.continuous hfc (hdisj x hx)
    have hdens := archLevyDensity_ge hx0 (hx.2.trans hs1)
    simp only [L]
    rw [hinner]
    calc Real.exp (-(1 / 2)) * M * x⁻¹ = Real.exp (-(1 / 2)) / (2 * x) * (2 * M) := by
          field_simp
      _ ≤ archLevyDensity x * (2 * M) := by
          gcongr
  have hcont : ContinuousOn (fun x : ℝ => Real.exp (-(1 / 2)) * M * x⁻¹) (Set.Icc w s) :=
    continuousOn_const.mul (continuousOn_inv₀.mono fun x hx => ne_of_gt (lt_of_lt_of_le hw0 hx.1))
  have hlint : IntegrableOn (fun x : ℝ => Real.exp (-(1 / 2)) * M * x⁻¹) (Set.Ioc w s) :=
    (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hstep2 : ∫ x in Set.Ioc w s, Real.exp (-(1 / 2)) * M * x⁻¹ ≤ ∫ x in Set.Ioc w s, L x :=
    setIntegral_mono_on hlint (hLint.mono_set hsub) measurableSet_Ioc hlow
  have hval : ∫ x in Set.Ioc w s, Real.exp (-(1 / 2)) * M * x⁻¹ =
      Real.exp (-(1 / 2)) * Real.log (s / w) * M := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hws,
      integral_inv_of_pos hw0 (lt_of_lt_of_le hw0 hws)]
    ring
  unfold levyEnergy
  rw [← hval]
  exact hstep2.trans hstep1

/-! ### Atomic tests -/

variable {g : ℝ → ℝ} {w : ℝ}

/-- The **atomic test** `Σ_{1 ≤ n ≤ N} x_n g(u − log n)`. -/
def atomicTest (N : ℕ) (x : ℕ → ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, x n * g (u - Real.log n)

/-- The spacing of the atoms `log n`, `n ≤ N`. -/
def atomSpacing (N : ℕ) : ℝ := Real.log (1 + 1 / (N : ℝ))

theorem atomSpacing_pos {N : ℕ} (hN : 1 ≤ N) : 0 < atomSpacing N := by
  have : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  exact Real.log_pos (by linarith)

theorem atomSpacing_le_log_two {N : ℕ} (hN : 1 ≤ N) : atomSpacing N ≤ Real.log 2 := by
  have h1 : 1 / (N : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast hN
  have : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  exact Real.log_le_log (by linarith) (by linarith)

theorem atomSpacing_le_one {N : ℕ} (hN : 1 ≤ N) : atomSpacing N ≤ 1 :=
  (atomSpacing_le_log_two hN).trans
    (by have := Real.log_two_lt_d9; norm_num at this ⊢; linarith)

/-- **Separation**: if `1 ≤ a ≤ N` and `a < b`, then `log b − log a ≥ δ_N`. -/
theorem atomSpacing_le_log_sub {N a b : ℕ} (ha : 1 ≤ a) (haN : a ≤ N) (hab : a < b) :
    atomSpacing N ≤ Real.log b - Real.log a := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le a) hab)
  rw [← Real.log_div hb0.ne' ha0.ne', atomSpacing]
  refine Real.log_le_log (by positivity) ?_
  have hab' : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
  have haN' : (a : ℝ) ≤ N := by exact_mod_cast haN
  rw [le_div_iff₀ ha0]
  have : 1 / (N : ℝ) * a ≤ 1 := by
    rw [one_div, inv_mul_le_iff₀ (by linarith)]; linarith
  nlinarith

/-- Two copies of a bump of width `w < δ_N` at distinct atoms, one of them `≤ N`, do not meet. -/
theorem bump_mul_eq_zero (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N a b : ℕ} (hw : w < atomSpacing N)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hmin : min a b ≤ N) (hab : a ≠ b) (t : ℝ) :
    g (t - Real.log a) * g (t - Real.log b) = 0 := by
  by_contra hne
  have h1 : t - Real.log a ∈ Set.Icc 0 w := by
    by_contra h
    apply hne
    simp only [hgsupp _ h, zero_mul]
  have h2 : t - Real.log b ∈ Set.Icc 0 w := by
    by_contra h
    apply hne
    simp only [hgsupp _ h, mul_zero]
  rw [Set.mem_Icc] at h1 h2
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have hmin' : a ≤ N := by rwa [min_eq_left hlt.le] at hmin
    have := atomSpacing_le_log_sub (N := N) ha hmin' hlt
    linarith
  · have hmin' : b ≤ N := by rwa [min_eq_right hgt.le] at hmin
    have := atomSpacing_le_log_sub (N := N) hb hmin' hgt
    linarith

theorem contDiff_atomicTest (hg : ContDiff ℝ 2 g) (N : ℕ) (x : ℕ → ℝ) :
    ContDiff ℝ 2 (atomicTest N x g) := by
  unfold atomicTest
  exact ContDiff.sum fun n _ => contDiff_const.mul (hg.comp (contDiff_id.sub contDiff_const))

theorem hasCompactSupport_atomicTest (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (N : ℕ)
    (x : ℕ → ℝ) : HasCompactSupport (atomicTest N x g) := by
  refine HasCompactSupport.intro (K := Set.Icc 0 (Real.log N + w)) isCompact_Icc fun u hu => ?_
  refine sum_eq_zero fun n hn => ?_
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hlogN : Real.log n ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
  rw [hgsupp, mul_zero]
  intro hm
  rw [Set.mem_Icc] at hm
  exact hu (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)

theorem integrable_bump_sq (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (c : ℝ) :
    Integrable fun u => g (u - c) ^ 2 := by
  have h0 : Integrable (fun t => g t * g t) :=
    (hg.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_right
  have h1 : Integrable fun t => g t ^ 2 := by simpa [pow_two] using h0
  exact h1.comp_sub_right c

/-- **The atoms are orthogonal**: `∫ f² = Σ x_n² ∫ g²` below the spacing. -/
theorem integral_atomicTest_sq (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hw : w < atomSpacing N) (x : ℕ → ℝ) :
    ∫ u, atomicTest N x g u ^ 2 = (∑ n ∈ Icc 1 N, x n ^ 2) * ∫ u, g u ^ 2 := by
  have hpt : ∀ u, atomicTest N x g u ^ 2 = ∑ n ∈ Icc 1 N, x n ^ 2 * g (u - Real.log n) ^ 2 := by
    intro u
    rw [atomicTest, sq, sum_mul_sum]
    refine sum_congr rfl fun m hm => ?_
    rw [← add_sum_erase _ _ hm, sum_eq_zero fun n hn => ?_, add_zero]
    · ring
    · have hmn := (ne_of_mem_erase hn).symm
      have hmN := (Finset.mem_Icc.mp hm).2
      have := bump_mul_eq_zero hgsupp hw (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp (mem_of_mem_erase hn)).1
        (le_trans (min_le_left _ _) hmN) hmn u
      rw [show x m * g (u - Real.log m) * (x n * g (u - Real.log n)) =
        x m * x n * (g (u - Real.log m) * g (u - Real.log n)) by ring, this, mul_zero]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun n _ => (integrable_bump_sq hg hgc _).const_mul _, sum_mul]
  refine sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, integral_sub_right_eq_self (fun u => g u ^ 2)]

/-- **No archimedean interaction below the spacing**: for `w ≤ δ_N/4`,
`levyEnergy f ≥ e^{−1/2} log(δ_N/(2w)) ∫ f²`. -/
theorem levyEnergy_atomicTest_ge (hg : ContDiff ℝ 2 g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ atomSpacing N / 4) (x : ℕ → ℝ) :
    Real.exp (-(1 / 2)) * Real.log (atomSpacing N / 2 / w) * ∫ u, atomicTest N x g u ^ 2 ≤
      levyEnergy (atomicTest N x g) := by
  have hδ := atomSpacing_pos hN
  refine levyEnergy_ge_of_disjoint_shifts (contDiff_atomicTest hg N x)
    (hasCompactSupport_atomicTest hgsupp N x) hw0 (by linarith)
    (by linarith [atomSpacing_le_one hN]) fun y hy u => ?_
  rw [atomicTest, atomicTest, sum_mul_sum]
  refine sum_eq_zero fun m hm => sum_eq_zero fun n hn => ?_
  rw [show x m * g (u - Real.log m) * (x n * g (u + y - Real.log n)) =
    x m * x n * (g (u - Real.log m) * g (u + y - Real.log n)) by ring]
  refine mul_eq_zero_of_right _ ?_
  by_contra hne
  have h1 : u - Real.log m ∈ Set.Icc 0 w := by
    by_contra h
    apply hne
    simp only [hgsupp _ h, zero_mul]
  have h2 : u + y - Real.log n ∈ Set.Icc 0 w := by
    by_contra h
    apply hne
    simp only [hgsupp _ h, mul_zero]
  rw [Set.mem_Icc] at h1 h2
  obtain ⟨hy1, hy2⟩ := hy
  rcases lt_trichotomy m n with hlt | rfl | hgt
  · have := atomSpacing_le_log_sub (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2 hlt
    linarith
  · linarith
  · have := atomSpacing_le_log_sub (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2 hgt
    linarith

/-! ### The prime sum of an atomic test -/

/-- The lag `−log k` pairing: only `m = nk` survives. -/
theorem integral_atomicTest_mul_shift_neg (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hw : w < atomSpacing N) (x : ℕ → ℝ)
    {k : ℕ} (hk : 1 ≤ k) :
    ∫ t, atomicTest N x g t * atomicTest N x g (t - Real.log k) =
      (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, if m = n * k then x m * x n else 0) * ∫ u, g u ^ 2 := by
  have hpt : ∀ t, atomicTest N x g t * atomicTest N x g (t - Real.log k) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        if m = n * k then x m * x n * g (t - Real.log m) ^ 2 else 0 := by
    intro t
    rw [atomicTest, atomicTest, sum_mul_sum]
    refine sum_congr rfl fun m hm => sum_congr rfl fun n hn => ?_
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hlog : t - Real.log k - Real.log n = t - Real.log ((n * k : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (show n ≠ 0 by omega))
        (by exact_mod_cast (show k ≠ 0 by omega))]
      ring
    rw [hlog]
    split_ifs with h
    · rw [← h]; ring
    · rw [show x m * g (t - Real.log m) * (x n * g (t - Real.log ((n * k : ℕ) : ℝ))) =
        x m * x n * (g (t - Real.log m) * g (t - Real.log ((n * k : ℕ) : ℝ))) by ring,
        bump_mul_eq_zero hgsupp hw (Finset.mem_Icc.mp hm).1 (Nat.mul_pos (by omega) (by omega))
          ((min_le_left _ _).trans (Finset.mem_Icc.mp hm).2) h t, mul_zero]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ => by
    split_ifs
    · exact (integrable_bump_sq hg hgc _).const_mul _
    · exact integrable_zero _ _ _, sum_mul]
  refine sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ fun n _ => by
    split_ifs
    · exact (integrable_bump_sq hg hgc _).const_mul _
    · exact integrable_zero _ _ _, sum_mul]
  refine sum_congr rfl fun n _ => ?_
  split_ifs
  · rw [integral_const_mul, integral_sub_right_eq_self (fun u => g u ^ 2)]
  · simp

/-- The lag `+log k` pairing: only `n = mk` survives. -/
theorem integral_atomicTest_mul_shift_pos (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hw : w < atomSpacing N) (x : ℕ → ℝ)
    {k : ℕ} (hk : 1 ≤ k) :
    ∫ t, atomicTest N x g t * atomicTest N x g (t + Real.log k) =
      (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, if n = m * k then x m * x n else 0) * ∫ u, g u ^ 2 := by
  have hpt : ∀ t, atomicTest N x g t * atomicTest N x g (t + Real.log k) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        if n = m * k then x m * x n * g (t - Real.log m) ^ 2 else 0 := by
    intro t
    rw [atomicTest, atomicTest, sum_mul_sum]
    refine sum_congr rfl fun m hm => sum_congr rfl fun n hn => ?_
    have hm1 := (Finset.mem_Icc.mp hm).1
    have hlogmk : Real.log ((m * k : ℕ) : ℝ) = Real.log m + Real.log k := by
      rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (show m ≠ 0 by omega))
        (by exact_mod_cast (show k ≠ 0 by omega))]
    split_ifs with h
    · rw [h, hlogmk, show t + Real.log k - (Real.log m + Real.log k) = t - Real.log m by ring]
      ring
    · have hz := bump_mul_eq_zero hgsupp hw (Nat.mul_pos (by omega) (by omega)) (Finset.mem_Icc.mp hn).1
        ((min_le_right _ _).trans (Finset.mem_Icc.mp hn).2) (Ne.symm h) (t + Real.log k)
      rw [hlogmk, show t + Real.log k - (Real.log m + Real.log k) = t - Real.log m by ring] at hz
      rw [show x m * g (t - Real.log m) * (x n * g (t + Real.log k - Real.log n)) =
        x m * x n * (g (t - Real.log m) * g (t + Real.log k - Real.log n)) by ring, hz, mul_zero]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ => by
    split_ifs
    · exact (integrable_bump_sq hg hgc _).const_mul _
    · exact integrable_zero _ _ _, sum_mul]
  refine sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ fun n _ => by
    split_ifs
    · exact (integrable_bump_sq hg hgc _).const_mul _
    · exact integrable_zero _ _ _, sum_mul]
  refine sum_congr rfl fun n _ => ?_
  split_ifs
  · rw [integral_const_mul, integral_sub_right_eq_self (fun u => g u ^ 2)]
  · simp

/-- One Hecke direction: `Σ_{k ≤ N} Λ_k [a = bk] = [b ∣ a, b ≠ a] Λ(a/b)/√(a/b)`. -/
theorem sum_vonMangoldtAtom_eq {N a b : ℕ} (ha : 1 ≤ a) (haN : a ≤ N) (hb : 1 ≤ b) :
    ∑ k ∈ range (N + 1), vonMangoldtAtom k * (if a = b * k then 1 else 0) =
      if b ∣ a ∧ b ≠ a then ArithmeticFunction.vonMangoldt (a / b) / Real.sqrt ((a / b : ℕ) : ℝ)
      else 0 := by
  by_cases hd : b ∣ a
  · have hk : a / b ∈ range (N + 1) :=
      mem_range.mpr (Nat.lt_succ_of_le ((Nat.div_le_self a b).trans haN))
    have hterm : ∀ k ∈ range (N + 1), vonMangoldtAtom k * (if a = b * k then 1 else 0) =
        if k = a / b then vonMangoldtAtom (a / b) else 0 := by
      intro k _
      by_cases hka : k = a / b
      · rw [if_pos hka, hka, if_pos (Nat.mul_div_cancel' hd).symm, mul_one]
      · rw [if_neg hka, if_neg, mul_zero]
        rintro rfl
        exact hka (Nat.mul_div_cancel_left k (by omega)).symm
    rw [sum_congr rfl hterm, sum_ite_eq' (range (N + 1)) (a / b), if_pos hk, vonMangoldtAtom]
    by_cases hba : b = a
    · subst hba
      rw [Nat.div_self (by omega), if_neg (by norm_num), if_neg (fun h => h.2 rfl)]
    · obtain ⟨q, rfl⟩ := hd
      have hq2 : 2 ≤ b * q / b := by
        rw [Nat.mul_div_cancel_left q (by omega)]
        rcases Nat.lt_or_ge q 2 with h | h
        · interval_cases q
          · omega
          · exact absurd (mul_one b).symm hba
        · exact h
      rw [if_pos hq2, if_pos ⟨dvd_mul_right b q, hba⟩]
  · rw [sum_eq_zero fun k _ => by rw [if_neg fun h => hd ⟨k, h⟩, mul_zero],
      if_neg fun h => hd h.1]

/-- **The Hecke weights of the atoms**: `Σ_{k ≤ N} Λ_k ([m = nk] + [n = mk]) = P(m, n)`. -/
theorem sum_vonMangoldtAtom_hecke {N m n : ℕ} (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N) :
    ∑ k ∈ range (N + 1), vonMangoldtAtom k *
        ((if m = n * k then 1 else 0) + (if n = m * k then 1 else 0)) =
      weilPrimeKernel m n := by
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  simp_rw [mul_add]
  rw [sum_add_distrib, sum_vonMangoldtAtom_eq hm1 hmN hn1, sum_vonMangoldtAtom_eq hn1 hnN hm1,
    weilPrimeKernel]
  by_cases h1 : m ∣ n ∧ m ≠ n
  · have h2 : ¬ (n ∣ m ∧ n ≠ m) := fun h => h1.2 (Nat.dvd_antisymm h1.1 h.1)
    rw [if_pos h1, if_neg h2, if_pos h1, zero_add]
  · rw [if_neg h1, if_neg h1, add_zero]

/-- **The prime sum of an atomic test is the atomic Weil prime form**: below the spacing,
`primeSum f = (∫ g²) Σ_{m,n} x_m x_n P(m, n)`. -/
theorem primeSum_atomicTest (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hw : w < atomSpacing N) (x : ℕ → ℝ) :
    primeSum (atomicTest N x g) = (∫ u, g u ^ 2) * atomicWeilForm N x := by
  set G := ∫ u, g u ^ 2
  -- the summand at every order
  have hk : ∀ k : ℕ, vonMangoldtAtom k *
      ((∫ t, atomicTest N x g t * atomicTest N x g (t - Real.log k)) +
        ∫ t, atomicTest N x g t * atomicTest N x g (t + Real.log k)) =
      G * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n * (vonMangoldtAtom k *
        ((if m = n * k then 1 else 0) + (if n = m * k then 1 else 0))) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · simp [vonMangoldtAtom]
    rw [integral_atomicTest_mul_shift_neg hg hgc hgsupp hw x hk1,
      integral_atomicTest_mul_shift_pos hg hgc hgsupp hw x hk1]
    calc _ = G * (vonMangoldtAtom k * ∑ m ∈ Icc 1 N,
          ((∑ n ∈ Icc 1 N, if m = n * k then x m * x n else 0) +
            ∑ n ∈ Icc 1 N, if n = m * k then x m * x n else 0)) := by
          rw [sum_add_distrib]; ring
      _ = _ := by
          rw [mul_sum]
          congr 1
          refine sum_congr rfl fun m _ => ?_
          rw [← sum_add_distrib, mul_sum]
          refine sum_congr rfl fun n _ => ?_
          split_ifs <;> ring
  -- only the orders `k ≤ N` contribute
  have hvanish : ∀ k ∉ range (N + 1), vonMangoldtAtom k *
      ((∫ t, atomicTest N x g t * atomicTest N x g (t - Real.log k)) +
        ∫ t, atomicTest N x g t * atomicTest N x g (t + Real.log k)) = 0 := by
    intro k hk'
    have hkN : N < k := by simpa using hk'
    rw [hk k]
    refine mul_eq_zero_of_right _ (sum_eq_zero fun m hm => sum_eq_zero fun n hn => ?_)
    have hm1 := (Finset.mem_Icc.mp hm)
    have hn1 := (Finset.mem_Icc.mp hn)
    rw [if_neg (by intro h; nlinarith), if_neg (by intro h; nlinarith)]
    simp
  rw [primeSum, tsum_eq_sum hvanish, sum_congr rfl fun k _ => hk k, ← mul_sum, atomicWeilForm]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun m hm => ?_
  rw [sum_comm]
  refine sum_congr rfl fun n hn => ?_
  rw [← mul_sum, sum_vonMangoldtAtom_hecke hm hn]

/-! ### The stability law -/

/-- **The stability law at atomic resolution, quantitative form**:
`M(f) ≥ (2θ′(0) + e^{−1/2} log(δ_N/(2w)) − 2 log N − log 4 − 4) ∫ f²`. -/
theorem markovEnergy_atomicTest_ge (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ atomSpacing N / 4) (x : ℕ → ℝ) :
    (2 * gammaHardyPhaseRate 0 + Real.exp (-(1 / 2)) * Real.log (atomSpacing N / 2 / w) -
        (2 * Real.log N + (Real.log 4 + 4))) * ∫ u, atomicTest N x g u ^ 2 ≤
      markovEnergy (fun u => (atomicTest N x g u : ℂ)) := by
  have hδ := atomSpacing_pos hN
  have hw' : w < atomSpacing N := by linarith
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  rw [markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, archForm_eq_levyEnergy hf hfc,
    primeSum_atomicTest hg hgc hgsupp hw' x]
  have hlevy := levyEnergy_atomicTest_ge hg hgsupp hN hw0 hw x
  have hsq := integral_atomicTest_sq hg hgc hgsupp hw' x
  have hW := atomicWeilForm_le N x
  have hG : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hprime : (∫ u, g u ^ 2) * atomicWeilForm N x ≤
      (2 * Real.log N + (Real.log 4 + 4)) * ∫ u, atomicTest N x g u ^ 2 := by
    rw [hsq]
    calc (∫ u, g u ^ 2) * atomicWeilForm N x
        ≤ (∫ u, g u ^ 2) * ((2 * Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2) :=
          mul_le_mul_of_nonneg_left hW hG
      _ = _ := by ring
  nlinarith

/-- The **atomic width** `(δ_N/4) exp(−e^{1/2}(2 log N + log 4 + 4 + 2|θ′(0)|))`. -/
def atomicWidth (N : ℕ) : ℝ :=
  atomSpacing N / 4 *
    Real.exp (-(Real.exp (1 / 2) * (2 * Real.log N + (Real.log 4 + 4) + 2 * |gammaHardyPhaseRate 0|)))

theorem atomicWidth_pos {N : ℕ} (hN : 1 ≤ N) : 0 < atomicWidth N :=
  mul_pos (by linarith [atomSpacing_pos hN]) (Real.exp_pos _)

/-- **The Lévy gain beats the prime counterterm** at every width `0 < w ≤ atomicWidth N`. -/
theorem atomicGain_nonneg {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w) (hw : w ≤ atomicWidth N) :
    w ≤ atomSpacing N / 4 ∧ 0 ≤ 2 * gammaHardyPhaseRate 0 + Real.exp (-(1 / 2)) *
      Real.log (atomSpacing N / 2 / w) - (2 * Real.log N + (Real.log 4 + 4)) := by
  have hδ := atomSpacing_pos hN
  set X := Real.exp (1 / 2) * (2 * Real.log N + (Real.log 4 + 4) + 2 * |gammaHardyPhaseRate 0|)
  have hX : 0 ≤ X := by
    have := Real.log_natCast_nonneg N
    have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hexp : Real.exp (-X) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  refine ⟨hw.trans (by rw [atomicWidth]; nlinarith [Real.exp_pos (-X)]), ?_⟩
  have hlog : X ≤ Real.log (atomSpacing N / 2 / w) := by
    have hle : atomSpacing N / 2 / atomicWidth N ≤ atomSpacing N / 2 / w :=
      div_le_div_of_nonneg_left (by positivity) hw0 hw
    have hval : atomSpacing N / 2 / atomicWidth N = 2 * Real.exp X := by
      rw [atomicWidth, Real.exp_neg]
      field_simp
      ring
    have h2 : X ≤ Real.log (2 * Real.exp X) := by
      rw [Real.log_mul (by norm_num) (Real.exp_pos X).ne', Real.log_exp]
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]
    exact h2.trans (Real.log_le_log (by positivity) (hval ▸ hle))
  have he : Real.exp (-(1 / 2)) * Real.exp (1 / 2) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 : Real.exp (-(1 / 2)) * X ≤ Real.exp (-(1 / 2)) * Real.log (atomSpacing N / 2 / w) :=
    mul_le_mul_of_nonneg_left hlog (Real.exp_pos _).le
  have h4 : Real.exp (-(1 / 2)) * X =
      2 * Real.log N + (Real.log 4 + 4) + 2 * |gammaHardyPhaseRate 0| := by
    simp only [X]; rw [← mul_assoc, he, one_mul]
  linarith [neg_abs_le (gammaHardyPhaseRate 0)]

/-- **The stability law at atomic resolution**: every atomic test of width at most
`atomicWidth N` at the points `log n`, `n ≤ N`, has nonnegative Markov form. -/
theorem markovEnergy_atomicTest_nonneg (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ atomicWidth N) (x : ℕ → ℝ) :
    0 ≤ markovEnergy (fun u => (atomicTest N x g u : ℂ)) := by
  obtain ⟨hw4, hcoef⟩ := atomicGain_nonneg hN hw0 hw
  have h := markovEnergy_atomicTest_ge hg hgc hgsupp hN hw0 hw4 x
  have hint : 0 ≤ ∫ u, atomicTest N x g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  exact le_trans (mul_nonneg hcoef hint) h

end GaloisForLFunctions.ArithmeticElectrostatics
