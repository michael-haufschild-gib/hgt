import GaloisForLFunctions.RHTower.SelbergEisensteinCuspSlice
import GaloisForLFunctions.RHTower.SelbergPeterssonKloosterman

open Complex MeasureTheory UpperHalfPlane
open scoped MatrixGroups

/-!
# The constant term of the `Γ(N)` Eisenstein series `E_∞` at the cusp `σ∞`

For `Re s > 1`, integrating the lattice sum `E_∞(σz, s) = Σ_{(c,d) ∈ adm·σ} (y/|cz+d|²)^s` over one period `[0, N]`
and interchanging sum and integral (the norms are summable: `summable_integral_norm`, dominated row by row by
`(c²)^{-Re s} · |c|N`), the `c = 0` rows contribute `N · y^s` for each of `d = ±1` that is a row at `σ∞`
(`hasSum_Gc_zero`), and each `c ≠ 0` row contributes `(c²)^{-s} · count_σ(c) · ∫_ℝ ker₀` (`hasSum_Gc`). Hence
`∫_0^N E_∞(σ(x+iy), s) dx = N · count₀ · y^s + (Σ_c (c²)^{-s} count_σ(c)) · ∫_ℝ ker₀` (`integral_poincare_cusp`).
-/

namespace GaloisForLFunctions.RHTower.SelbergEisensteinCuspConstant
open GaloisForLFunctions.RHTower.SelbergPoincareKernel GaloisForLFunctions.RHTower.SelbergEisensteinCusp
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspRows GaloisForLFunctions.RHTower.SelbergPoincareFourier
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspSlice GaloisForLFunctions.RHTower.SelbergMaassMean
  GaloisForLFunctions.RHTower.SelbergPeterssonKloosterman GaloisForLFunctions.RHTower.SelbergPoincare

theorem esum_point {x y : ℝ} (hy : 0 < y) (s : ℂ) (p : ℤ × ℤ) :
    esum s (ofComplex (point x y)) p = esumxy s y x p := by
  have hp : 0 < (point x y).im := by simpa [point] using hy
  unfold esum esumxy
  congr 3
  · rw [ofComplex_apply_of_im_pos hp]; simp [point, UpperHalfPlane.im]
  · rw [ofComplex_apply_of_im_pos hp, Complex.normSq_apply]
    simp [point]
    ring

variable (N : ℕ) [NeZero N] (σ : SL(2, ℤ))

theorem poincare_point {x y : ℝ} (hy : 0 < y) (s : ℂ) :
    poincare N 0 s (σ • ofComplex (point x y)) = ∑' p, (rowMul σ '' adm N).indicator (esumxy s y x) p := by
  rw [poincare_smul_eq, range_botσ]
  congr 1; funext p
  by_cases hm : p ∈ rowMul σ '' adm N
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, esum_point hy]
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]

omit [NeZero N] in
theorem coprime_of_mem {p : ℤ × ℤ} (h : p ∈ rowMul σ '' adm N) : IsCoprime p.1 p.2 := by
  obtain ⟨q, hq, rfl⟩ := h
  exact isCoprime_rowMul σ hq.2.2

omit [NeZero N] in
theorem mem_zero {d : ℤ} (h : ((0 : ℤ), d) ∈ rowMul σ '' adm N) : d = 1 ∨ d = -1 :=
  Int.isUnit_iff.mp (isCoprime_zero_left.mp (coprime_of_mem N σ h))

/-- The real majorant `(y/|cz+d|²)^σ`. -/
noncomputable def esumR (r y x : ℝ) (p : ℤ × ℤ) : ℝ := (y / ((p.1 * x + p.2) ^ 2 + (p.1 * y) ^ 2)) ^ r

theorem base_nonneg {y : ℝ} (hy : 0 < y) (x : ℝ) (p : ℤ × ℤ) :
    0 ≤ y / ((p.1 * x + p.2) ^ 2 + (p.1 * y) ^ 2) := div_nonneg hy.le (by positivity)

theorem norm_esumxy {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : s.re ≠ 0) (x : ℝ) (p : ℤ × ℤ) :
    ‖esumxy s y x p‖ = esumR s.re y x p :=
  Complex.norm_cpow_eq_rpow_re_of_nonneg (base_nonneg hy x p) hs

theorem esumxy_re {y : ℝ} (hy : 0 < y) (r x : ℝ) (p : ℤ × ℤ) :
    esumxy (r : ℂ) y x p = ((esumR r y x p : ℝ) : ℂ) :=
  (Complex.ofReal_cpow (base_nonneg hy x p) r).symm

omit [NeZero N] in
theorem countσ_zero : countσ N σ 0 = 0 := by simp [countσ]

omit [NeZero N] in
theorem countσ_le (c : ℤ) : (countσ N σ c : ℝ) ≤ |(c : ℝ)| * N := by
  classical
  have h : countσ N σ c ≤ c.natAbs * N := by
    unfold countσ
    exact (Finset.card_filter_le _ _).trans (by simp)
  have h' : (countσ N σ c : ℝ) ≤ ((c.natAbs * N : ℕ) : ℝ) := by exact_mod_cast h
  simpa [Nat.cast_natAbs] using h'

omit [NeZero N] in
theorem weight_le {r : ℝ} (c : ℤ) :
    ((c : ℝ) ^ 2) ^ (-r) * (countσ N σ c : ℝ) ≤ N * |(c : ℝ)| ^ (-(2 * r - 1)) := by
  by_cases hc : c = 0
  · subst hc; rw [countσ_zero]; simp only [Nat.cast_zero, mul_zero]; positivity
  have hcR : (0 : ℝ) < |(c : ℝ)| := abs_pos.mpr (by exact_mod_cast hc)
  have e : ((c : ℝ) ^ 2) ^ (-r) * |(c : ℝ)| = |(c : ℝ)| ^ (-(2 * r - 1)) := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul hcR.le, ← Real.rpow_add_one hcR.ne']
    congr 1; push_cast; ring
  calc ((c : ℝ) ^ 2) ^ (-r) * (countσ N σ c : ℝ) ≤ ((c : ℝ) ^ 2) ^ (-r) * (|(c : ℝ)| * N) :=
        mul_le_mul_of_nonneg_left (countσ_le N σ c) (by positivity)
    _ = N * |(c : ℝ)| ^ (-(2 * r - 1)) := by rw [← e]; ring

omit [NeZero N] in
theorem summable_weight {r : ℝ} (hr : 1 < r) :
    Summable (fun c : ℤ => ((c : ℝ) ^ 2) ^ (-r) * (countσ N σ c : ℝ)) :=
  Summable.of_nonneg_of_le (fun c => by positivity) (weight_le N σ)
    ((Real.summable_abs_int_rpow (b := 2 * r - 1) (by linarith)).mul_left _)

variable {N σ}

omit [NeZero N] in
theorem integrableOn_F {s : ℂ} (hs : 1 / 2 < s.re) {y : ℝ} (hy : 0 < y) (p : ℤ × ℤ) :
    IntegrableOn (fun x => (rowMul σ '' adm N).indicator (esumxy s y x) p) (Set.Ioc 0 N) := by
  by_cases hm : p ∈ rowMul σ '' adm N
  · simp only [Set.indicator_of_mem hm]
    obtain ⟨c, d⟩ := p
    by_cases hc : c = 0
    · subst hc
      have : (fun x => esumxy s y x (0, d)) = fun _ => esumxy s y 0 (0, d) := by
        funext x; simp [esumxy]
      rw [this]
      exact integrableOn_const measure_Ioc_lt_top.ne
    · have : (fun x => esumxy s y x (c, d)) = fun x => (((c : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) * ker 0 y s (x + d / c) := by
        funext x; exact esumxy_eq hy s x hc d
      rw [this]
      exact (((integrable_ker (β := 0) le_rfl hy hs).comp_add_right _).const_mul _).integrableOn
  · simp only [Set.indicator_of_notMem hm]
    exact integrableOn_zero

omit [NeZero N] in
theorem norm_F {s : ℂ} (hs : s.re ≠ 0) {y : ℝ} (hy : 0 < y) (x : ℝ) (p : ℤ × ℤ) :
    ‖(rowMul σ '' adm N).indicator (esumxy s y x) p‖ = (rowMul σ '' adm N).indicator (esumR s.re y x) p := by
  by_cases hm : p ∈ rowMul σ '' adm N
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, norm_esumxy hy hs]
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, norm_zero]

omit [NeZero N] in
theorem integral_norm_F {s : ℂ} (hs : s.re ≠ 0) {y : ℝ} (hy : 0 < y) (p : ℤ × ℤ) :
    ∫ x in Set.Ioc (0 : ℝ) N, ‖(rowMul σ '' adm N).indicator (esumxy s y x) p‖ =
      (Gc N σ (s.re : ℂ) y p.1 p.2).re := by
  simp_rw [norm_F hs hy]
  have : ∀ x, (rowMul σ '' adm N).indicator (esumxy (s.re : ℂ) y x) (p.1, p.2) =
      (((rowMul σ '' adm N).indicator (esumR s.re y x) p : ℝ) : ℂ) := by
    intro x
    by_cases hm : p ∈ rowMul σ '' adm N
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, esumxy_re hy]
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, ofReal_zero]
  unfold Gc
  simp_rw [this]
  rw [intervalIntegral.integral_ofReal, ofReal_re, intervalIntegral.integral_of_le (Nat.cast_nonneg N)]

variable (N σ)

/-- The number of `d ∈ {1, -1}` with `(0, d)` a row at `σ∞`: the multiplicity of `y^s` in the constant term. -/
noncomputable def count0 : ℕ := by
  classical
  exact (({1, -1} : Finset ℤ).filter (fun d => ((0 : ℤ), d) ∈ rowMul σ '' adm N)).card

variable {N σ}

omit [NeZero N] in
theorem Gc_zero (s : ℂ) (y : ℝ) (d : ℤ) :
    Gc N σ s y 0 d = N * (rowMul σ '' adm N).indicator (fun _ => ((y : ℝ) : ℂ) ^ s) ((0 : ℤ), d) := by
  unfold Gc
  by_cases hm : ((0 : ℤ), d) ∈ rowMul σ '' adm N
  · simp only [Set.indicator_of_mem hm]
    have hd : (d : ℝ) ^ 2 = 1 := by
      rcases mem_zero N σ hm with h | h <;> subst h <;> norm_num
    have : ∀ x : ℝ, esumxy s y x (0, d) = ((y : ℝ) : ℂ) ^ s := by
      intro x; simp [esumxy, hd]
    simp_rw [this]
    rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul]
    push_cast; ring
  · simp [Set.indicator_of_notMem hm]

omit [NeZero N] in
theorem hasSum_Gc_zero (s : ℂ) (y : ℝ) :
    HasSum (Gc N σ s y 0) ((N : ℂ) * ((y : ℝ) : ℂ) ^ s * (count0 N σ : ℂ)) := by
  classical
  have h : HasSum (Gc N σ s y 0) (∑ d ∈ ({1, -1} : Finset ℤ), Gc N σ s y 0 d) := hasSum_sum_of_ne_finset_zero (by
    intro d hd
    rw [Gc_zero]
    have hm : ((0 : ℤ), d) ∉ rowMul σ '' adm N := by
      intro hm
      rcases mem_zero N σ hm with h | h <;> simp [h] at hd
    rw [Set.indicator_of_notMem hm, mul_zero])
  convert h using 1
  simp_rw [Gc_zero, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun d _ => Set.indicator_apply _ _ _), Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, count0]
  ring

variable (N σ) in
/-- The row value: `Σ_d ∫_0^N` of the row summand, for every `c` (the `c = 0` row carries the `y^s` terms). -/
noncomputable def rowVal (s : ℂ) (y : ℝ) (c : ℤ) : ℂ :=
  (((c : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) * (countσ N σ c : ℂ) * (∫ x, ker 0 y s x) +
    if c = 0 then (N : ℂ) * ((y : ℝ) : ℂ) ^ s * (count0 N σ : ℂ) else 0

theorem hasSum_row {s : ℂ} (hs : 1 / 2 < s.re) {y : ℝ} (hy : 0 < y) (c : ℤ) :
    HasSum (Gc N σ s y c) (rowVal N σ s y c) := by
  unfold rowVal
  by_cases hc : c = 0
  · subst hc
    rw [countσ_zero, if_pos rfl]
    simpa using hasSum_Gc_zero s y
  · rw [if_neg hc, add_zero]
    exact hasSum_Gc N σ hs hy hc

omit [NeZero N] in
theorem summable_rowVal {s : ℂ} (hs : 1 < s.re) (y : ℝ) : Summable (rowVal N σ s y) := by
  unfold rowVal
  refine Summable.add ?_ (hasSum_ite_eq 0 _).summable
  refine Summable.mul_right _ (Summable.of_norm_bounded (summable_weight N σ hs) (fun c => ?_))
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_nonneg (by positivity) (by simp; linarith)]
  simp

theorem summable_integral_norm {s : ℂ} (hs : 1 < s.re) {y : ℝ} (hy : 0 < y) :
    Summable (fun p : ℤ × ℤ => ∫ x in Set.Ioc (0 : ℝ) N, ‖(rowMul σ '' adm N).indicator (esumxy s y x) p‖) := by
  have hre : s.re ≠ 0 := by linarith
  have hr : 1 / 2 < ((s.re : ℂ)).re := by simp; linarith
  refine (summable_prod_of_nonneg (fun p => integral_nonneg (fun x => norm_nonneg _))).mpr ⟨fun c => ?_, ?_⟩
  · simp_rw [integral_norm_F hre hy]
    exact (Complex.hasSum_re (hasSum_row hr hy c)).summable
  · have : (fun c => ∑' d, ∫ x in Set.Ioc (0 : ℝ) N, ‖(rowMul σ '' adm N).indicator (esumxy s y x) (c, d)‖) =
        fun c => (rowVal N σ (s.re : ℂ) y c).re := by
      funext c
      simp_rw [integral_norm_F hre hy]
      exact (Complex.hasSum_re (hasSum_row hr hy c)).tsum_eq
    rw [this]
    exact (Complex.hasSum_re (summable_rowVal (by simpa using hs) y).hasSum).summable

/-- **The constant term of `E_∞` at the cusp `σ∞`** (`Re s > 1`):
`∫_0^N E_∞(σ(x+iy), s) dx = N · #{d = ±1 : (0,d) at σ∞} · y^s + (Σ_c (c²)^{-s} count_σ(c)) · ∫_ℝ ker₀`. -/
theorem integral_poincare_cusp {s : ℂ} (hs : 1 < s.re) {y : ℝ} (hy : 0 < y) :
    ∫ x in (0 : ℝ)..N, poincare N 0 s (σ • ofComplex (point x y)) =
      (N : ℂ) * ((y : ℝ) : ℂ) ^ s * (count0 N σ : ℂ) +
        (∑' c : ℤ, (((c : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) * (countσ N σ c : ℂ)) * ∫ x, ker 0 y s x := by
  have hs' : 1 / 2 < s.re := by linarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  simp_rw [poincare_point N σ hy s]
  rw [intervalIntegral.integral_of_le hN, ← integral_tsum_of_summable_integral_norm
    (fun p => integrableOn_F hs' hy p) (summable_integral_norm (N := N) (σ := σ) hs hy)]
  have hG : ∀ p : ℤ × ℤ, ∫ x in Set.Ioc (0 : ℝ) N, (rowMul σ '' adm N).indicator (esumxy s y x) p =
      Gc N σ s y p.1 p.2 := fun p => by
    unfold Gc; rw [intervalIntegral.integral_of_le hN]
  simp_rw [hG]
  have hGs : Summable (fun p : ℤ × ℤ => Gc N σ s y p.1 p.2) := by
    refine Summable.of_norm_bounded (summable_integral_norm (N := N) (σ := σ) hs hy) (fun p => ?_)
    rw [← hG]
    exact norm_integral_le_integral_norm _
  rw [hGs.tsum_prod]
  have hr : ∀ c, ∑' d, Gc N σ s y c d = rowVal N σ s y c := fun c => (hasSum_row hs' hy c).tsum_eq
  simp only [hr]
  unfold rowVal
  have h1 : Summable (fun c : ℤ => (((c : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) * (countσ N σ c : ℂ)) := by
    refine Summable.of_norm_bounded (summable_weight N σ hs) (fun c => ?_)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_nonneg (by positivity) (by simp; linarith)]
    simp
  rw [Summable.tsum_add (h1.mul_right _) (hasSum_ite_eq 0 _).summable, tsum_ite_eq, tsum_mul_right]
  ring

end GaloisForLFunctions.RHTower.SelbergEisensteinCuspConstant
