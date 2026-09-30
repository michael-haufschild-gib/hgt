import GaloisForLFunctions.RHTower.WeilPolarConeKernelTransformForm
import GaloisForLFunctions.RHTower.WeilPositivityLogDensityMaximality
import GaloisForLFunctions.RHTower.Sieve.AbelInequality

/-!
# `Λ` is an extreme point of the polar Weil cone

**Theorem** (`eq_zero_of_weilPositive_add_of_sub`). Let `w` be real weights. If `Λ + w` and
`Λ − w` are both Weil-positive on polar tests (`WeilPositive`), then `w(n) = 0` for every `n ≥ 2`.
Unconditional, with no hypothesis on `w`: Weil positivity bounds `|w(n)| ≤ √n (log n + C)`,
and the injectivity of the Riemann-kernel transform needs only `Σ |w(n)| n^{−2} < ∞`.

The polar cone does not see the pole, so the first variation at Riemann's kernel leaves a
two-dimensional family: `G_w = ν y (e₊ − e₋) + A (e₊ + e₋)` (`exists_weightKernelTransform_form`).
The theta primitive `F = S + S(−·)` then carries the log-powers `y²` and `y`.

They are removed by the Abelian functional `J(Y) = ∫_{−Y}^0 e^{y/2} S(y) dy`, computed two ways.
* **Theta side.** `S(y) = F(y) − S(−y)`, and `S` decays on `[0, ∞)`. So
  `J(Y) = (ν/6) Y³ + ((A − ν)/2) Y² + O(Y)`.
* **Dirichlet side.** Termwise, `J(Y) = Σ_k (a(k)/k)(ψ(k) − ψ(k e^{−Y}))` with
  `ψ(v) = ∫_0^v e^{−πt²}` and `a = 1 ⋆ w'`. Abel's inequality bounds this by the partial sums
  `B(K) = Σ_{k ≤ K} a(k)/k = Σ_{nm ≤ K} w'(n)/(nm)`. Weil positivity of `Λ ± w` gives
  `|B(K)| = o(log² K)` (`weil_supersystem_excess_small`), so `J(Y) = o(Y²)`.

Hence `ν = A = 0`, so `G_w ≡ 0`, and the Riemann-kernel transform is injective.
-/

open Complex MeasureTheory Filter Topology Set Polynomial
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-! ## The Gaussian primitive -/

/-- `ψ(v) = ∫_0^v e^{−πt²} dt`. -/
def gaussianPrimitive (v : ℝ) : ℝ := ∫ t in (0 : ℝ)..v, Real.exp (-π * t ^ 2)

theorem continuous_gaussianDensity : Continuous fun t : ℝ => Real.exp (-π * t ^ 2) := by
  fun_prop

theorem hasDerivAt_gaussianPrimitive (v : ℝ) :
    HasDerivAt gaussianPrimitive (Real.exp (-π * v ^ 2)) v :=
  (continuous_gaussianDensity.integral_hasStrictDerivAt 0 v).hasDerivAt

theorem gaussianPrimitive_sub {u v : ℝ} :
    gaussianPrimitive v - gaussianPrimitive u = ∫ t in u..v, Real.exp (-π * t ^ 2) :=
  intervalIntegral.integral_interval_sub_left (continuous_gaussianDensity.intervalIntegrable _ _)
    (continuous_gaussianDensity.intervalIntegrable _ _)

theorem gaussianPrimitive_mono {u v : ℝ} (h : u ≤ v) : gaussianPrimitive u ≤ gaussianPrimitive v := by
  have := intervalIntegral.integral_nonneg (μ := volume) h fun t _ => (Real.exp_pos (-π * t ^ 2)).le
  rw [← gaussianPrimitive_sub] at this; linarith

theorem gaussianPrimitive_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ gaussianPrimitive v := by
  have := gaussianPrimitive_mono hv
  simpa [gaussianPrimitive] using this

theorem gaussianPrimitive_le_half (v : ℝ) : gaussianPrimitive v ≤ 1 / 2 := by
  rcases le_or_gt v 0 with hv | hv
  · have := gaussianPrimitive_mono hv
    have h0 : gaussianPrimitive 0 = 0 := by simp [gaussianPrimitive]
    linarith
  · have hI : ∫ t in Ioi (0 : ℝ), Real.exp (-π * t ^ 2) = 1 / 2 := by
      rw [integral_gaussian_Ioi, div_self Real.pi_pos.ne', Real.sqrt_one]
    rw [gaussianPrimitive, intervalIntegral.integral_of_le hv.le, ← hI]
    refine setIntegral_mono_set (integrable_exp_neg_mul_sq Real.pi_pos).integrableOn
      (Eventually.of_forall fun t => (Real.exp_pos _).le) (Eventually.of_forall ?_)
    intro t ht
    exact ht.1

/-- Over `[u, v]` with `0 ≤ u`, the increment of `ψ` is at most `(v − u) e^{−πu²}`. -/
theorem gaussianPrimitive_sub_le {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    gaussianPrimitive v - gaussianPrimitive u ≤ (v - u) * Real.exp (-π * u ^ 2) := by
  rw [gaussianPrimitive_sub]
  calc ∫ t in u..v, Real.exp (-π * t ^ 2) ≤ ∫ _t in u..v, Real.exp (-π * u ^ 2) :=
        intervalIntegral.integral_mono_on huv (continuous_gaussianDensity.intervalIntegrable _ _)
          intervalIntegrable_const fun t ht => by
            apply Real.exp_le_exp.mpr
            have : u ^ 2 ≤ t ^ 2 := by nlinarith [ht.1]
            nlinarith [Real.pi_pos]
    _ = (v - u) * Real.exp (-π * u ^ 2) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]

/-! ## The Dirichlet side of the Abelian functional -/

/-- `∫_{−Y}^0 e^{y/2} · e^{y/2} e^{−πn²e^{2y}} dy = (ψ(n) − ψ(n e^{−Y}))/n`. -/
theorem integral_exp_half_mul_cuspTerm_one {n : ℕ} (hn : 0 < n) (Y : ℝ) :
    ∫ y in (-Y)..0, Real.exp (y / 2) * cuspTerm 1 n y =
      (gaussianPrimitive n - gaussianPrimitive (n * Real.exp (-Y))) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hderiv : ∀ y ∈ uIcc (-Y) 0, HasDerivAt (fun y => gaussianPrimitive (n * Real.exp y) / n)
      (Real.exp (y / 2) * cuspTerm 1 n y) y := by
    intro y _
    have h := ((hasDerivAt_gaussianPrimitive (n * Real.exp y)).comp y
      ((Real.hasDerivAt_exp y).const_mul (n : ℝ))).div_const (n : ℝ)
    refine h.congr_deriv ?_
    unfold cuspTerm
    simp only [eval_one, mul_one]
    have e1 : Real.exp (y / 2) * Real.exp (y / 2) = Real.exp y := by rw [← Real.exp_add]; ring_nf
    have e2 : (n * Real.exp y) ^ 2 = (n : ℝ) ^ 2 * Real.exp (2 * y) := by
      rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
    rw [e2]
    field_simp
    rw [← e1]; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by unfold cuspTerm; fun_prop : Continuous fun y => Real.exp (y / 2) * cuspTerm 1 n y).intervalIntegrable _ _)]
  simp only [Real.exp_zero, mul_one]
  ring

/-- Termwise integration of the theta primitive against `e^{y/2}` over `[−Y, 0]`. -/
theorem hasSum_integral_exp_half_mul_atomCuspSeries {w : ℕ → ℝ} {K : ℝ}
    (hK : ∀ n : ℕ, |w (n + 1)| ≤ K * ((n + 1 : ℕ) : ℝ) ^ 2) {Y : ℝ} (hY : 0 ≤ Y) :
    HasSum (fun k : ℕ => oneConvWeight (restrictAtoms w) (k + 1) *
        ((gaussianPrimitive ((k + 1 : ℕ) : ℝ) -
          gaussianPrimitive (((k + 1 : ℕ) : ℝ) * Real.exp (-Y))) / ((k + 1 : ℕ) : ℝ)))
      (∫ y in (-Y)..0, Real.exp (y / 2) * atomCuspSeries w 0 y) := by
  set a := oneConvWeight (restrictAtoms w) with hadef
  have ha := abs_oneConvWeight_le (abs_restrictAtoms_le hK)
  have hY₁ : 0 < Real.exp (-(2 * Y)) := Real.exp_pos _
  set bnd : ℕ → ℝ := fun k => K * (1 * polyAbsBound 1 * (1 + 1) ^ (1 : ℝ[X]).natDegree) *
    (((k + 1 : ℕ) : ℝ) ^ (2 + 1 + 2 * (1 : ℝ[X]).natDegree) *
      Real.exp (-(π * Real.exp (-(2 * Y))) * ((k + 1 : ℕ) : ℝ))) with hbnd
  have hbsum : Summable bnd := (summable_cuspTerm_bound _ (mul_pos Real.pi_pos hY₁)).mul_left _
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := -Y) (b := 0) (f := fun y => Real.exp (y / 2) * atomCuspSeries w 0 y)
    (F := fun k y => a (k + 1) * (Real.exp (y / 2) * cuspTerm 1 (k + 1) y))
    (fun k _ => bnd k)
    (fun k => (by unfold cuspTerm; fun_prop : Continuous fun y =>
      a (k + 1) * (Real.exp (y / 2) * cuspTerm 1 (k + 1) y)).aestronglyMeasurable)
    (fun k => Eventually.of_forall fun y hy => by
      rw [uIoc_of_le (by linarith)] at hy
      have hy1 : Real.exp (-(2 * Y)) ≤ Real.exp (2 * y) :=
        Real.exp_le_exp.mpr (by linarith [hy.1])
      have hy2 : Real.exp (2 * y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hy.2])
      have hy3 : Real.exp (y / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hy.2])
      have hc := abs_weightedCuspTerm_le ha 1 k hY₁ hy1 hy2 hy3
      rw [Real.norm_eq_abs, show a (k + 1) * (Real.exp (y / 2) * cuspTerm 1 (k + 1) y) =
        Real.exp (y / 2) * (a (k + 1) * cuspTerm 1 (k + 1) y) by ring, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      calc Real.exp (y / 2) * |a (k + 1) * cuspTerm 1 (k + 1) y|
          ≤ 1 * |a (k + 1) * cuspTerm 1 (k + 1) y| :=
            mul_le_mul_of_nonneg_right hy3 (abs_nonneg _)
        _ ≤ bnd k := by rw [one_mul]; exact hc)
    (Eventually.of_forall fun _ _ => hbsum) intervalIntegrable_const
    (Eventually.of_forall fun y _ => by
      have hs := (summable_weightedCuspTerm ha 1 y).hasSum.mul_left (Real.exp (y / 2))
      have e : (fun k => a (k + 1) * (Real.exp (y / 2) * cuspTerm 1 (k + 1) y)) =
          fun k => Real.exp (y / 2) * (a (k + 1) * cuspTerm 1 (k + 1) y) := by
        funext k; ring
      show HasSum (fun k => a (k + 1) * (Real.exp (y / 2) * cuspTerm 1 (k + 1) y))
        (Real.exp (y / 2) * weightedCuspSeries a 1 y)
      rw [e]; exact hs)
  have e2 : (fun k => ∫ y in (-Y)..0, a (k + 1) * (Real.exp (y / 2) * cuspTerm 1 (k + 1) y)) =
      fun k => a (k + 1) * ((gaussianPrimitive ((k + 1 : ℕ) : ℝ) -
        gaussianPrimitive (((k + 1 : ℕ) : ℝ) * Real.exp (-Y))) / ((k + 1 : ℕ) : ℝ)) := by
    funext k
    rw [intervalIntegral.integral_const_mul, integral_exp_half_mul_cuspTerm_one (Nat.succ_pos k)]
  rw [e2] at h
  exact h

/-! ## Partial sums and the log-density bound -/

/-- `B(K) = Σ_{k < K} (1 ⋆ w')(k+1)/(k+1)`. -/
def atomPartialSum (w : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, oneConvWeight (restrictAtoms w) (k + 1) / ((k + 1 : ℕ) : ℝ)

/-- `B(N) = Σ_{n ≥ 2, nm ≤ N} w(n)/(nm)`. -/
theorem atomPartialSum_eq (w : ℕ → ℝ) (N : ℕ) :
    atomPartialSum w N = ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
      (if n * m ≤ N then w n / (n * m) else 0) := by
  have h1 : atomPartialSum w N =
      ∑ k ∈ Finset.Icc 1 N, oneConvWeight (restrictAtoms w) k / (k : ℝ) := by
    induction N with
    | zero => simp [atomPartialSum]
    | succ N ih =>
      rw [atomPartialSum, Finset.sum_range_succ, ← atomPartialSum, ih,
        Finset.sum_Icc_succ_top (by omega)]
  have h2 := CriticalGibbs.sum_mulPairs_eq_sum_divisors N
    (fun n k => restrictAtoms w n / (k : ℝ))
  have h3 : ∑ k ∈ Finset.Icc 1 N, ∑ n ∈ k.divisors, restrictAtoms w n / (k : ℝ) =
      ∑ k ∈ Finset.Icc 1 N, oneConvWeight (restrictAtoms w) k / (k : ℝ) :=
    Finset.sum_congr rfl fun k _ => by rw [oneConvWeight, Finset.sum_div]
  rw [h1, ← h3, ← h2]
  have hsub : ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
      (if n * m ≤ N then restrictAtoms w n / ((n * m : ℕ) : ℝ) else 0) =
      ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
      (if n * m ≤ N then restrictAtoms w n / ((n * m : ℕ) : ℝ) else 0) := by
    refine Finset.sum_subset (Finset.Icc_subset_Icc_left (by norm_num)) fun n hn hn2 => ?_
    have h1n : n = 1 := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hn hn2; omega
    subst h1n
    simp [restrictAtoms]
  rw [← hsub]
  refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m _ => ?_
  have h2n : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  simp only [restrictAtoms, if_pos h2n]
  push_cast; rfl

/-- **Log-density of the perturbation.** If `Λ ± w` are Weil-positive, then
`|B(N)| ≤ ε log² N` for large `N`. -/
theorem exists_abs_atomPartialSum_le {w : ℕ → ℝ}
    (hp : WeilPositive fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + w n)
    (hm : WeilPositive fun n => (ArithmeticFunction.vonMangoldt n : ℝ) - w n) {ε : ℝ}
    (hε : 0 < ε) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |atomPartialSum w N| ≤ ε * Real.log N ^ 2 := by
  obtain ⟨N₁, h₁⟩ := weil_supersystem_excess_small hp hε
  obtain ⟨N₂, h₂⟩ := weil_supersystem_excess_small hm hε
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  have b1 := h₁ N (le_trans (le_max_left _ _) hN)
  have b2 := h₂ N (le_trans (le_max_right _ _) hN)
  have e1 : ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
      (if n * m ≤ N then ((ArithmeticFunction.vonMangoldt n : ℝ) + w n -
        ArithmeticFunction.vonMangoldt n) / (n * m) else 0) = atomPartialSum w N := by
    rw [atomPartialSum_eq]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> ring
  have e2 : ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
      (if n * m ≤ N then ((ArithmeticFunction.vonMangoldt n : ℝ) - w n -
        ArithmeticFunction.vonMangoldt n) / (n * m) else 0) = -atomPartialSum w N := by
    rw [atomPartialSum_eq, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> ring
  rw [e1] at b1
  rw [e2] at b2
  rw [abs_le]; constructor <;> linarith

/-! ## The Dirichlet side is `o(Y²)` -/

theorem gaussianIncrement_nonneg {n r : ℝ} (hn : 0 ≤ n) (hr : r ≤ 1) :
    0 ≤ gaussianPrimitive n - gaussianPrimitive (n * r) := by
  have : n * r ≤ n := mul_le_of_le_one_right hn hr
  linarith [gaussianPrimitive_mono this]

/-- Beyond `n ≥ e^{2Y}`, the increment `ψ(n) − ψ(n e^{−Y})` is at most `n e^{−πn}`. -/
theorem gaussianIncrement_le {n Y : ℝ} (hY : 0 ≤ Y) (hn : Real.exp (2 * Y) ≤ n) :
    gaussianPrimitive n - gaussianPrimitive (n * Real.exp (-Y)) ≤ n * Real.exp (-π * n) := by
  have hn0 : 0 < n := lt_of_lt_of_le (Real.exp_pos _) hn
  have heY : Real.exp (-Y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hnY : 0 ≤ n * Real.exp (-Y) := by positivity
  have hnY' : n * Real.exp (-Y) ≤ n := mul_le_of_le_one_right hn0.le heY
  have hsq : n ≤ (n * Real.exp (-Y)) ^ 2 := by
    have h2 : Real.exp (-Y) ^ 2 = Real.exp (-(2 * Y)) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have h3 : Real.exp (2 * Y) * Real.exp (-(2 * Y)) = 1 := by
      rw [← Real.exp_add]; simp
    have h4 : 1 ≤ n * Real.exp (-(2 * Y)) := by
      have := mul_le_mul_of_nonneg_right hn (Real.exp_pos (-(2 * Y))).le
      linarith
    rw [mul_pow, h2]
    nlinarith
  have hexp : Real.exp (-π * (n * Real.exp (-Y)) ^ 2) ≤ Real.exp (-π * n) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have h := gaussianPrimitive_sub_le hnY hnY'
  calc gaussianPrimitive n - gaussianPrimitive (n * Real.exp (-Y))
      ≤ (n - n * Real.exp (-Y)) * Real.exp (-π * (n * Real.exp (-Y)) ^ 2) := h
    _ ≤ n * Real.exp (-π * (n * Real.exp (-Y)) ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ ≤ n * Real.exp (-π * n) := mul_le_mul_of_nonneg_left hexp hn0.le

/-- **Abel's inequality for the Gaussian increments.** If the partial sums of `c` up to `M` are
bounded by `B`, then `|Σ_{k < M} c_k (ψ(k+1) − ψ((k+1)r))| ≤ B` for `0 < r ≤ 1`. -/
theorem abs_sum_mul_gaussianIncrement_le {c : ℕ → ℝ} {M : ℕ} {r B : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hB : ∀ k, k ≤ M → |∑ j ∈ Finset.range k, c j| ≤ B) :
    |∑ k ∈ Finset.range M, c k * (gaussianPrimitive ((k + 1 : ℕ) : ℝ) -
      gaussianPrimitive (((k + 1 : ℕ) : ℝ) * r))| ≤ B := by
  set g : ℕ → ℝ := fun k => if k < M then c k else 0 with hg
  have hgpart : ∀ k, ∑ j ∈ Finset.range k, g j = ∑ j ∈ Finset.range (min k M), c j := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      rcases lt_or_ge k M with hk | hk
      · rw [min_eq_left hk.le, min_eq_left (by omega : k + 1 ≤ M), Finset.sum_range_succ]
        simp only [hg, if_pos hk]
      · rw [min_eq_right hk, min_eq_right (by omega : M ≤ k + 1)]
        simp only [hg, if_neg (not_lt.mpr hk), add_zero]
  have hgB : ∀ k, |∑ j ∈ Finset.range k, g j| ≤ B := fun k => by
    rw [hgpart]; exact hB _ (min_le_right _ _)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB 0)
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  set W₁ : ℕ → ℝ := fun k => gaussianPrimitive M -
    gaussianPrimitive (min (((k + 1 : ℕ) : ℝ) * r) M) with hW₁
  set W₂ : ℕ → ℝ := fun k => gaussianPrimitive M - gaussianPrimitive (min ((k + 1 : ℕ) : ℝ) M)
    with hW₂
  have hW₁0 : ∀ k, 0 ≤ W₁ k := fun k =>
    sub_nonneg.mpr (gaussianPrimitive_mono (min_le_right _ _))
  have hW₂0 : ∀ k, 0 ≤ W₂ k := fun k =>
    sub_nonneg.mpr (gaussianPrimitive_mono (min_le_right _ _))
  have hW₁a : ∀ k, W₁ (k + 1) ≤ W₁ k := fun k =>
    sub_le_sub_left (gaussianPrimitive_mono (min_le_min_right _
      (mul_le_mul_of_nonneg_right (by push_cast; linarith) hr0.le))) _
  have hW₂a : ∀ k, W₂ (k + 1) ≤ W₂ k := fun k =>
    sub_le_sub_left (gaussianPrimitive_mono (min_le_min_right _ (by push_cast; linarith))) _
  have hψM := gaussianPrimitive_le_half (M : ℝ)
  have hW₁b : W₁ 0 ≤ 1 / 2 := by
    have := gaussianPrimitive_nonneg (le_min (by positivity : (0 : ℝ) ≤ ((0 + 1 : ℕ) : ℝ) * r) hM0)
    exact (sub_le_self _ this).trans hψM
  have hW₂b : W₂ 0 ≤ 1 / 2 := by
    have := gaussianPrimitive_nonneg (le_min (by positivity : (0 : ℝ) ≤ ((0 + 1 : ℕ) : ℝ)) hM0)
    exact (sub_le_self _ this).trans hψM
  have hA₁ := Sieve.abs_sum_mul_le_of_bounded_partial M hgB hW₁0 hW₁a
  have hA₂ := Sieve.abs_sum_mul_le_of_bounded_partial M hgB hW₂0 hW₂a
  have hsplit : ∑ k ∈ Finset.range M, c k * (gaussianPrimitive ((k + 1 : ℕ) : ℝ) -
      gaussianPrimitive (((k + 1 : ℕ) : ℝ) * r)) =
      ∑ k ∈ Finset.range M, W₁ k * g k - ∑ k ∈ Finset.range M, W₂ k * g k := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkM : k < M := Finset.mem_range.mp hk
    have hk1 : ((k + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hkM
    have hk2 : ((k + 1 : ℕ) : ℝ) * r ≤ M :=
      (mul_le_of_le_one_right (by positivity) hr1).trans hk1
    rw [hW₁, hW₂, hg]
    simp only [if_pos hkM, min_eq_left hk1, min_eq_left hk2]
    ring
  rw [hsplit]
  have h1 : B * W₁ 0 ≤ B / 2 := by nlinarith
  have h2 : B * W₂ 0 ≤ B / 2 := by nlinarith
  calc _ ≤ |∑ k ∈ Finset.range M, W₁ k * g k| + |∑ k ∈ Finset.range M, W₂ k * g k| := abs_sub _ _
    _ ≤ B := by linarith

/-- The partial sums up to `⌈e^{2Y}⌉` are at most `C₀ + ε (1 + 2Y)²`. -/
theorem exists_abs_atomPartialSum_le_of_le_ceil {w : ℕ → ℝ}
    (hp : WeilPositive fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + w n)
    (hm : WeilPositive fun n => (ArithmeticFunction.vonMangoldt n : ℝ) - w n) {ε : ℝ}
    (hε : 0 < ε) : ∃ C₀ : ℝ, ∀ Y : ℝ, 0 ≤ Y → ∀ k, k ≤ ⌈Real.exp (2 * Y)⌉₊ →
      |atomPartialSum w k| ≤ C₀ + ε * (1 + 2 * Y) ^ 2 := by
  obtain ⟨N₀, hN₀⟩ := exists_abs_atomPartialSum_le hp hm hε
  refine ⟨∑ k ∈ Finset.range N₀, |atomPartialSum w k|, fun Y hY k hk => ?_⟩
  have hC₀0 : 0 ≤ ∑ k ∈ Finset.range N₀, |atomPartialSum w k| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hE : 0 ≤ ε * (1 + 2 * Y) ^ 2 := by positivity
  rcases lt_or_ge k N₀ with hkN | hkN
  · have := Finset.single_le_sum (f := fun k => |atomPartialSum w k|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hkN)
    linarith
  · have he2Y : 1 ≤ Real.exp (2 * Y) := Real.one_le_exp (by linarith)
    have hM1 : Real.exp (2 * Y) ≤ ⌈Real.exp (2 * Y)⌉₊ := Nat.le_ceil _
    have hM2 : (⌈Real.exp (2 * Y)⌉₊ : ℝ) < Real.exp (2 * Y) + 1 :=
      Nat.ceil_lt_add_one (Real.exp_pos _).le
    have hMpos : (0 : ℝ) < ⌈Real.exp (2 * Y)⌉₊ := by linarith
    have hlogM : Real.log ⌈Real.exp (2 * Y)⌉₊ ≤ 1 + 2 * Y := by
      have h1 : Real.log ⌈Real.exp (2 * Y)⌉₊ ≤ Real.log (2 * Real.exp (2 * Y)) :=
        Real.log_le_log hMpos (by linarith)
      rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h1
      have := Real.log_two_lt_d9
      norm_num at this
      linarith
    have h0 := Real.log_natCast_nonneg k
    have hlk : Real.log k ≤ Real.log ⌈Real.exp (2 * Y)⌉₊ := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; simpa using Real.log_natCast_nonneg ⌈Real.exp (2 * Y)⌉₊
      · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hk)
    have hsq : Real.log k ^ 2 ≤ (1 + 2 * Y) ^ 2 := pow_le_pow_left₀ h0 (hlk.trans hlogM) 2
    have := hN₀ k hkN
    have : ε * Real.log k ^ 2 ≤ ε * (1 + 2 * Y) ^ 2 := mul_le_mul_of_nonneg_left hsq hε.le
    linarith

/-- **Abelian bound.** If `Λ ± w` are Weil-positive, the Dirichlet side of the Abelian functional
is at most `C_ε + ε Y²` for `Y ≥ 0`. -/
theorem exists_abs_tsum_gaussianPrimitive_le {w : ℕ → ℝ} {K : ℝ}
    (hK : ∀ n : ℕ, |w (n + 1)| ≤ K * ((n + 1 : ℕ) : ℝ) ^ 2)
    (hp : WeilPositive fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + w n)
    (hm : WeilPositive fun n => (ArithmeticFunction.vonMangoldt n : ℝ) - w n) {ε : ℝ}
    (hε : 0 < ε) : ∃ C : ℝ, ∀ Y : ℝ, 0 ≤ Y →
      |∑' k : ℕ, oneConvWeight (restrictAtoms w) (k + 1) *
        ((gaussianPrimitive ((k + 1 : ℕ) : ℝ) -
          gaussianPrimitive (((k + 1 : ℕ) : ℝ) * Real.exp (-Y))) / ((k + 1 : ℕ) : ℝ))| ≤
        C + ε * Y ^ 2 := by
  have ha := abs_oneConvWeight_le (abs_restrictAtoms_le hK)
  obtain ⟨C₀, hC₀⟩ := exists_abs_atomPartialSum_le_of_le_ceil hp hm (ε := ε / 8) (by positivity)
  have hbs : Summable fun k : ℕ => K * (((k + 1 : ℕ) : ℝ) ^ 3 * Real.exp (-π * ((k + 1 : ℕ) : ℝ))) :=
    (summable_cuspTerm_bound 3 Real.pi_pos).mul_left K
  have hK0 : 0 ≤ K := by have := (abs_nonneg _).trans (hK 0); simpa using this
  refine ⟨C₀ + (∑' k : ℕ, K * (((k + 1 : ℕ) : ℝ) ^ 3 * Real.exp (-π * ((k + 1 : ℕ) : ℝ)))) + ε / 4,
    fun Y hY => ?_⟩
  set c : ℕ → ℝ := fun k => oneConvWeight (restrictAtoms w) (k + 1) / ((k + 1 : ℕ) : ℝ) with hc
  set u : ℕ → ℝ := fun k => gaussianPrimitive ((k + 1 : ℕ) : ℝ) -
    gaussianPrimitive (((k + 1 : ℕ) : ℝ) * Real.exp (-Y)) with hu
  have hterm : (fun k : ℕ => oneConvWeight (restrictAtoms w) (k + 1) *
      ((gaussianPrimitive ((k + 1 : ℕ) : ℝ) -
        gaussianPrimitive (((k + 1 : ℕ) : ℝ) * Real.exp (-Y))) / ((k + 1 : ℕ) : ℝ))) =
      fun k => c k * u k := by
    funext k; simp only [hc, hu]; ring
  have hsum := (hasSum_integral_exp_half_mul_atomCuspSeries hK hY).summable
  rw [hterm] at hsum ⊢
  set M := ⌈Real.exp (2 * Y)⌉₊ with hM
  have heY : Real.exp (-Y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  -- head
  have hhead : |∑ k ∈ Finset.range M, c k * u k| ≤ C₀ + ε / 8 * (1 + 2 * Y) ^ 2 :=
    abs_sum_mul_gaussianIncrement_le (Real.exp_pos _) heY fun k hk => by
      have := hC₀ Y hY k hk
      simpa [atomPartialSum, hc] using this
  -- tail
  have htailb : ∀ k, |c (k + M) * u (k + M)| ≤
      K * (((k + M + 1 : ℕ) : ℝ) ^ 3 * Real.exp (-π * ((k + M + 1 : ℕ) : ℝ))) := by
    intro k
    have hn1 : Real.exp (2 * Y) ≤ ((k + M + 1 : ℕ) : ℝ) := by
      have h1 : Real.exp (2 * Y) ≤ M := Nat.le_ceil _
      have h2 : (M : ℝ) ≤ ((k + M + 1 : ℕ) : ℝ) := by push_cast; linarith
      linarith
    have hn0 : (0 : ℝ) < ((k + M + 1 : ℕ) : ℝ) := by positivity
    have hu0 : 0 ≤ u (k + M) := gaussianIncrement_nonneg hn0.le heY
    have hu1 : u (k + M) ≤ ((k + M + 1 : ℕ) : ℝ) * Real.exp (-π * ((k + M + 1 : ℕ) : ℝ)) :=
      gaussianIncrement_le hY hn1
    have hak := ha (k + M)
    simp only [hc]
    rw [abs_mul, abs_div, abs_of_pos hn0, abs_of_nonneg hu0]
    calc |oneConvWeight (restrictAtoms w) (k + M + 1)| / ((k + M + 1 : ℕ) : ℝ) * u (k + M)
        ≤ K * ((k + M + 1 : ℕ) : ℝ) ^ (2 + 1) / ((k + M + 1 : ℕ) : ℝ) *
            (((k + M + 1 : ℕ) : ℝ) * Real.exp (-π * ((k + M + 1 : ℕ) : ℝ))) :=
          mul_le_mul (div_le_div_of_nonneg_right hak hn0.le) hu1 hu0 (by positivity)
      _ = _ := by field_simp
  have htail : |∑' k, c (k + M) * u (k + M)| ≤
      ∑' k : ℕ, K * (((k + 1 : ℕ) : ℝ) ^ 3 * Real.exp (-π * ((k + 1 : ℕ) : ℝ))) := by
    have hbshift := (summable_nat_add_iff M).mpr hbs
    have h1 := tsum_of_norm_bounded hbshift.hasSum (fun k => by
      rw [Real.norm_eq_abs]; exact htailb k)
    have h2 := hbs.sum_add_tsum_nat_add M
    have h3 : 0 ≤ ∑ k ∈ Finset.range M,
        K * (((k + 1 : ℕ) : ℝ) ^ 3 * Real.exp (-π * ((k + 1 : ℕ) : ℝ))) :=
      Finset.sum_nonneg fun k _ => by positivity
    rw [Real.norm_eq_abs] at h1
    linarith
  rw [← hsum.sum_add_tsum_nat_add M]
  have hsq : (1 + 2 * Y) ^ 2 ≤ 2 + 8 * Y ^ 2 := by nlinarith [sq_nonneg (2 * Y - 1)]
  have : ε / 8 * (1 + 2 * Y) ^ 2 ≤ ε / 4 + ε * Y ^ 2 := by nlinarith
  calc |∑ k ∈ Finset.range M, c k * u k + ∑' k, c (k + M) * u (k + M)|
      ≤ |∑ k ∈ Finset.range M, c k * u k| + |∑' k, c (k + M) * u (k + M)| := abs_add_le _ _
    _ ≤ _ := by linarith

/-! ## The theta side of the Abelian functional -/

/-- On `[0, ∞)` the theta primitive is uniformly small: `|e^{−u/2} S₀(u)| ≤ Σ K k³ e^{−πk}`. -/
theorem abs_exp_neg_half_mul_atomCuspSeries_le {w : ℕ → ℝ} {K : ℝ}
    (hK : ∀ n : ℕ, |w (n + 1)| ≤ K * ((n + 1 : ℕ) : ℝ) ^ 2) {u : ℝ} (hu : 0 ≤ u) :
    |Real.exp (-(u / 2)) * atomCuspSeries w 0 u| ≤
      ∑' k : ℕ, K * (((k + 1 : ℕ) : ℝ) ^ 3 * Real.exp (-π * ((k + 1 : ℕ) : ℝ))) := by
  have ha := abs_oneConvWeight_le (abs_restrictAtoms_le hK)
  have hbs : Summable fun k : ℕ => K * (((k + 1 : ℕ) : ℝ) ^ 3 * Real.exp (-π * ((k + 1 : ℕ) : ℝ))) :=
    (summable_cuspTerm_bound 3 Real.pi_pos).mul_left K
  have hS : Real.exp (-(u / 2)) * atomCuspSeries w 0 u = ∑' k : ℕ,
      oneConvWeight (restrictAtoms w) (k + 1) *
        Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) := by
    show Real.exp (-(u / 2)) * weightedCuspSeries _ 1 u = _
    unfold weightedCuspSeries
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    unfold cuspTerm
    simp only [eval_one, mul_one]
    have : Real.exp (-(u / 2)) * Real.exp (u / 2) = 1 := by rw [← Real.exp_add]; simp
    calc Real.exp (-(u / 2)) * (oneConvWeight (restrictAtoms w) (k + 1) *
          (Real.exp (u / 2) * Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)))))
        = (Real.exp (-(u / 2)) * Real.exp (u / 2)) * (oneConvWeight (restrictAtoms w) (k + 1) *
          Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)))) := by ring
      _ = _ := by rw [this, one_mul]
  rw [hS, ← Real.norm_eq_abs]
  refine tsum_of_norm_bounded hbs.hasSum fun k => ?_
  have hn1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
  have he : 1 ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  have hexp : Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) ≤
      Real.exp (-π * ((k + 1 : ℕ) : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have : ((k + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) := by nlinarith
    nlinarith [Real.pi_pos]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |oneConvWeight (restrictAtoms w) (k + 1)| *
        Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)))
      ≤ (K * ((k + 1 : ℕ) : ℝ) ^ (2 + 1)) * Real.exp (-π * ((k + 1 : ℕ) : ℝ)) :=
        mul_le_mul (ha k) hexp (Real.exp_pos _).le ((abs_nonneg _).trans (ha k))
    _ = _ := by ring

/-- `∫_{−Y}^0 e^{y/2}` of the explicit theta primitive is `(ν/6)Y³ + ((A−ν)/2)Y² + C₋Y + O(1)`. -/
theorem exists_abs_integral_explicitPrimitive_sub_le (ν A Cp Cm : ℝ) :
    ∃ T : ℝ, ∀ Y : ℝ, 0 ≤ Y →
      |(∫ y in (-Y)..0, Real.exp (y / 2) *
          (ν / 2 * (y ^ 2 * (Real.exp (y / 2) + Real.exp (-(y / 2)))) +
            (A - ν) * (y * (Real.exp (y / 2) - Real.exp (-(y / 2)))) +
            Cp * Real.exp (y / 2) + Cm * Real.exp (-(y / 2)))) -
        (ν / 6 * Y ^ 3 + (A - ν) / 2 * Y ^ 2 + Cm * Y)| ≤ T := by
  set Q : ℝ → ℝ := fun x => ν / 2 * ((x ^ 2 - 2 * x + 2) * Real.exp x + x ^ 3 / 3) +
    (A - ν) * ((x - 1) * Real.exp x - x ^ 2 / 2) + Cp * Real.exp x + Cm * x with hQ
  have hQd : ∀ y, HasDerivAt Q (Real.exp (y / 2) *
      (ν / 2 * (y ^ 2 * (Real.exp (y / 2) + Real.exp (-(y / 2)))) +
        (A - ν) * (y * (Real.exp (y / 2) - Real.exp (-(y / 2)))) +
        Cp * Real.exp (y / 2) + Cm * Real.exp (-(y / 2)))) y := by
    intro y
    have e := Real.hasDerivAt_exp y
    have h1 := ((((hasDerivAt_pow 2 y).sub ((hasDerivAt_id' y).const_mul 2)).add_const 2).mul e)
    have h2 := (hasDerivAt_pow 3 y).div_const 3
    have h3 := ((hasDerivAt_id' y).sub_const 1).mul e
    have h4 := (hasDerivAt_pow 2 y).div_const 2
    have h := ((((h1.add h2).const_mul (ν / 2)).add ((h3.sub h4).const_mul (A - ν))).add
      (e.const_mul Cp)).add ((hasDerivAt_id' y).const_mul Cm)
    refine h.congr_deriv ?_
    have e1 : Real.exp (y / 2) * Real.exp (y / 2) = Real.exp y := by rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (y / 2) * Real.exp (-(y / 2)) = 1 := by rw [← Real.exp_add]; simp
    simp only [Pi.sub_apply, show (2 - 1 : ℕ) = 1 from rfl,
      show (3 - 1 : ℕ) = 2 from rfl, pow_one]
    push_cast
    linear_combination (-(ν / 2 * y ^ 2) - (A - ν) * y - Cp) * e1 +
      (-(ν / 2 * y ^ 2) + (A - ν) * y - Cm) * e2
  have hcont : Continuous fun y : ℝ => Real.exp (y / 2) *
      (ν / 2 * (y ^ 2 * (Real.exp (y / 2) + Real.exp (-(y / 2)))) +
        (A - ν) * (y * (Real.exp (y / 2) - Real.exp (-(y / 2)))) +
        Cp * Real.exp (y / 2) + Cm * Real.exp (-(y / 2))) := by fun_prop
  refine ⟨|Q 0| + |ν| + |A - ν| + |Cp|, fun Y hY => ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hQd y) (hcont.intervalIntegrable _ _)]
  have hq : 1 + Y + Y ^ 2 / 2 ≤ Real.exp Y := Real.quadratic_le_exp_of_nonneg hY
  have hl : Y + 1 ≤ Real.exp Y := Real.add_one_le_exp Y
  have hE : Real.exp Y * Real.exp (-Y) = 1 := by rw [← Real.exp_add]; simp
  have hE0 : 0 < Real.exp (-Y) := Real.exp_pos _
  have hE1 : Real.exp (-Y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hb2 : (Y ^ 2 + 2 * Y + 2) * Real.exp (-Y) ≤ 2 := by nlinarith
  have hb1 : (Y + 1) * Real.exp (-Y) ≤ 1 := by nlinarith
  have hb20 : 0 ≤ (Y ^ 2 + 2 * Y + 2) * Real.exp (-Y) := by positivity
  have hb10 : 0 ≤ (Y + 1) * Real.exp (-Y) := by positivity
  have hrest : Q 0 - Q (-Y) - (ν / 6 * Y ^ 3 + (A - ν) / 2 * Y ^ 2 + Cm * Y) =
      Q 0 - ν / 2 * ((Y ^ 2 + 2 * Y + 2) * Real.exp (-Y)) +
        (A - ν) * ((Y + 1) * Real.exp (-Y)) - Cp * Real.exp (-Y) := by
    simp only [hQ]; ring
  rw [hrest]
  have t1 : |ν / 2 * ((Y ^ 2 + 2 * Y + 2) * Real.exp (-Y))| ≤ |ν| := by
    rw [abs_mul, abs_div, abs_two, abs_of_nonneg hb20]
    nlinarith [abs_nonneg ν]
  have t2 : |(A - ν) * ((Y + 1) * Real.exp (-Y))| ≤ |A - ν| := by
    rw [abs_mul, abs_of_nonneg hb10]
    nlinarith [abs_nonneg (A - ν)]
  have t3 : |Cp * Real.exp (-Y)| ≤ |Cp| := by
    rw [abs_mul, abs_of_pos hE0]
    nlinarith [abs_nonneg Cp]
  calc |Q 0 - ν / 2 * ((Y ^ 2 + 2 * Y + 2) * Real.exp (-Y)) +
        (A - ν) * ((Y + 1) * Real.exp (-Y)) - Cp * Real.exp (-Y)|
      ≤ |Q 0| + |ν / 2 * ((Y ^ 2 + 2 * Y + 2) * Real.exp (-Y))| +
          |(A - ν) * ((Y + 1) * Real.exp (-Y))| + |Cp * Real.exp (-Y)| := by
        have a1 := abs_sub (Q 0 - ν / 2 * ((Y ^ 2 + 2 * Y + 2) * Real.exp (-Y)) +
          (A - ν) * ((Y + 1) * Real.exp (-Y))) (Cp * Real.exp (-Y))
        have a2 := abs_add_le (Q 0 - ν / 2 * ((Y ^ 2 + 2 * Y + 2) * Real.exp (-Y)))
          ((A - ν) * ((Y + 1) * Real.exp (-Y)))
        have a3 := abs_sub (Q 0) (ν / 2 * ((Y ^ 2 + 2 * Y + 2) * Real.exp (-Y)))
        linarith
    _ ≤ _ := by linarith

/-! ## Growth comparison -/

/-- If `|pY³ + qY²| ≤ C_ε + εY² + DY` for every `ε > 0` and all `Y ≥ 0`, then `p = q = 0`. -/
theorem eq_zero_of_forall_abs_cubic_le {p q D : ℝ} (hD : 0 ≤ D)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Y : ℝ, 0 ≤ Y → |p * Y ^ 3 + q * Y ^ 2| ≤ C + ε * Y ^ 2 + D * Y) :
    p = 0 ∧ q = 0 := by
  have hp : p = 0 := by
    by_contra hp0
    have hpa : 0 < |p| := abs_pos.mpr hp0
    obtain ⟨C, hC⟩ := h 1 one_pos
    set Y := max 1 ((|q| + |C| + 1 + D) / |p| + 1) with hY
    have hY1 : 1 ≤ Y := le_max_left _ _
    have hY2 : (|q| + |C| + 1 + D) / |p| + 1 ≤ Y := le_max_right _ _
    have hb := hC Y (by linarith)
    have hlow : |p| * Y ^ 3 - |q| * Y ^ 2 ≤ |p * Y ^ 3 + q * Y ^ 2| := by
      have := abs_sub_abs_le_abs_sub (p * Y ^ 3) (-(q * Y ^ 2))
      rw [abs_neg, sub_neg_eq_add, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Y ^ 3),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ Y ^ 2)] at this
      linarith
    have hCY : C ≤ |C| * Y ^ 2 := by
      have : 1 ≤ Y ^ 2 := by nlinarith
      nlinarith [le_abs_self C, abs_nonneg C]
    have hDY : D * Y ≤ D * Y ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hD
    have key : |p| * Y ^ 3 ≤ (|q| + |C| + 1 + D) * Y ^ 2 := by nlinarith
    have hYp : |p| * Y ≤ |q| + |C| + 1 + D := by
      have hY2pos : 0 < Y ^ 2 := by positivity
      have : (|p| * Y) * Y ^ 2 ≤ (|q| + |C| + 1 + D) * Y ^ 2 := by nlinarith
      exact le_of_mul_le_mul_right this hY2pos
    have : |q| + |C| + 1 + D < |p| * Y := by
      have h1 : (|q| + |C| + 1 + D) / |p| < Y := by linarith
      rwa [div_lt_iff₀ hpa, mul_comm] at h1
    linarith
  refine ⟨hp, ?_⟩
  subst hp
  by_contra hq0
  have hqa : 0 < |q| := abs_pos.mpr hq0
  obtain ⟨C, hC⟩ := h (|q| / 2) (by positivity)
  set Y := max 1 (2 * (|C| + D) / |q| + 1) with hY
  have hY1 : 1 ≤ Y := le_max_left _ _
  have hY2 : 2 * (|C| + D) / |q| + 1 ≤ Y := le_max_right _ _
  have hb := hC Y (by linarith)
  simp only [zero_mul, zero_add] at hb
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Y ^ 2)] at hb
  have hCY : C ≤ |C| * Y := by nlinarith [le_abs_self C, abs_nonneg C]
  have key : |q| / 2 * Y ^ 2 ≤ (|C| + D) * Y := by nlinarith
  have hYq : |q| / 2 * Y ≤ |C| + D := by
    have : (|q| / 2 * Y) * Y ≤ (|C| + D) * Y := by nlinarith
    exact le_of_mul_le_mul_right this (by linarith)
  have : |C| + D < |q| / 2 * Y := by
    have h1 : 2 * (|C| + D) / |q| < Y := by linarith
    rw [div_lt_iff₀ hqa] at h1
    linarith
  linarith

/-! ## The theorem -/

/-- **`Λ` is an extreme point of the polar Weil cone.** If `Λ + w` and `Λ − w` are both
Weil-positive on polar tests, then `w(n) = 0` for all `n ≥ 2`. Unconditional, no hypothesis
on `w`. -/
theorem eq_zero_of_weilPositive_add_of_sub {w : ℕ → ℝ}
    (hp : WeilPositive fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + w n)
    (hm : WeilPositive fun n => (ArithmeticFunction.vonMangoldt n : ℝ) - w n) :
    ∀ n, 2 ≤ n → w n = 0 := by
  have hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2 := by
    have h := summable_sub_vonMangoldt_div_sq_of_weilPositive hp
    simp only [add_sub_cancel_left] at h
    exact h
  obtain ⟨K, hK⟩ := exists_abs_le_of_summable_div_sq (summable_rpow_two_of_div_sq hw2)
  obtain ⟨ν, A, Cp, Cm, hG, hF⟩ := exists_weightKernelTransform_form hp hm
  set T₀ := ∑' k : ℕ, K * (((k + 1 : ℕ) : ℝ) ^ 3 * Real.exp (-π * ((k + 1 : ℕ) : ℝ))) with hT₀
  have hT₀0 : 0 ≤ T₀ := by
    have hK0 : 0 ≤ K := by have := (abs_nonneg _).trans (hK 0); simpa using this
    exact tsum_nonneg fun k => by positivity
  obtain ⟨T, hT⟩ := exists_abs_integral_explicitPrimitive_sub_le ν A Cp Cm
  set S := atomCuspSeries w 0 with hS
  have hSc : Continuous S := continuous_iff_continuousAt.mpr fun y =>
    (hasDerivAt_atomCuspSeries hK 0 y).continuousAt
  -- the two sides of the Abelian functional
  have hcubic : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Y : ℝ, 0 ≤ Y →
      |ν / 6 * Y ^ 3 + (A - ν) / 2 * Y ^ 2| ≤ C + ε * Y ^ 2 + (T₀ + |Cm|) * Y := by
    intro ε hε
    obtain ⟨C, hC⟩ := exists_abs_tsum_gaussianPrimitive_le hK hp hm hε
    refine ⟨C + T, fun Y hY => ?_⟩
    have hJ := hC Y hY
    rw [(hasSum_integral_exp_half_mul_atomCuspSeries hK hY).tsum_eq] at hJ
    -- theta side
    have hsplit : ∫ y in (-Y)..0, Real.exp (y / 2) * S y =
        (∫ y in (-Y)..0, Real.exp (y / 2) * (S y + S (-y))) -
          ∫ u in (0 : ℝ)..Y, Real.exp (-(u / 2)) * S u := by
      have hneg : ∫ y in (-Y)..0, Real.exp (y / 2) * S (-y) =
          ∫ u in (0 : ℝ)..Y, Real.exp (-(u / 2)) * S u := by
        have := intervalIntegral.integral_comp_neg (a := -Y) (b := 0)
          (fun u => Real.exp (-(u / 2)) * S u)
        simp only [neg_neg, neg_zero] at this
        rw [← this]
        refine intervalIntegral.integral_congr fun y _ => ?_
        simp only [neg_div, neg_neg]
      rw [← hneg, ← intervalIntegral.integral_sub]
      · refine intervalIntegral.integral_congr fun y _ => ?_
        ring
      · exact ((by fun_prop : Continuous fun y : ℝ => Real.exp (y / 2)).mul
          (hSc.add (hSc.comp continuous_neg))).intervalIntegrable _ _
      · exact ((by fun_prop : Continuous fun y : ℝ => Real.exp (y / 2)).mul
          (hSc.comp continuous_neg)).intervalIntegrable _ _
    have htail : |∫ u in (0 : ℝ)..Y, Real.exp (-(u / 2)) * S u| ≤ T₀ * Y := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := Y) (C := T₀)
        (f := fun u => Real.exp (-(u / 2)) * S u) (fun u hu => by
          rw [uIoc_of_le hY] at hu
          rw [Real.norm_eq_abs]
          exact abs_exp_neg_half_mul_atomCuspSeries_le hK hu.1.le)
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hY] at this
      exact this
    have hFint : ∫ y in (-Y)..0, Real.exp (y / 2) * (S y + S (-y)) =
        ∫ y in (-Y)..0, Real.exp (y / 2) *
          (ν / 2 * (y ^ 2 * (Real.exp (y / 2) + Real.exp (-(y / 2)))) +
            (A - ν) * (y * (Real.exp (y / 2) - Real.exp (-(y / 2)))) +
            Cp * Real.exp (y / 2) + Cm * Real.exp (-(y / 2))) :=
      intervalIntegral.integral_congr fun y _ => by simp only [hS]; rw [hF y]
    have hTY := hT Y hY
    rw [← hFint] at hTY
    rw [hsplit] at hJ
    have hCmY : |Cm * Y| ≤ |Cm| * Y := by rw [abs_mul, abs_of_nonneg hY]
    have e : ν / 6 * Y ^ 3 + (A - ν) / 2 * Y ^ 2 =
        ((∫ y in (-Y)..0, Real.exp (y / 2) * (S y + S (-y))) -
            ∫ u in (0 : ℝ)..Y, Real.exp (-(u / 2)) * S u) +
          (∫ u in (0 : ℝ)..Y, Real.exp (-(u / 2)) * S u) -
          ((∫ y in (-Y)..0, Real.exp (y / 2) * (S y + S (-y))) -
            (ν / 6 * Y ^ 3 + (A - ν) / 2 * Y ^ 2 + Cm * Y)) - Cm * Y := by ring
    rw [e]
    calc _ ≤ |(∫ y in (-Y)..0, Real.exp (y / 2) * (S y + S (-y))) -
              ∫ u in (0 : ℝ)..Y, Real.exp (-(u / 2)) * S u| +
            |∫ u in (0 : ℝ)..Y, Real.exp (-(u / 2)) * S u| +
            |(∫ y in (-Y)..0, Real.exp (y / 2) * (S y + S (-y))) -
              (ν / 6 * Y ^ 3 + (A - ν) / 2 * Y ^ 2 + Cm * Y)| + |Cm * Y| := by
          have a1 := abs_sub (((∫ y in (-Y)..0, Real.exp (y / 2) * (S y + S (-y))) -
              ∫ u in (0 : ℝ)..Y, Real.exp (-(u / 2)) * S u) +
            (∫ u in (0 : ℝ)..Y, Real.exp (-(u / 2)) * S u) -
            ((∫ y in (-Y)..0, Real.exp (y / 2) * (S y + S (-y))) -
              (ν / 6 * Y ^ 3 + (A - ν) / 2 * Y ^ 2 + Cm * Y))) (Cm * Y)
          have a2 := abs_sub (((∫ y in (-Y)..0, Real.exp (y / 2) * (S y + S (-y))) -
              ∫ u in (0 : ℝ)..Y, Real.exp (-(u / 2)) * S u) +
            (∫ u in (0 : ℝ)..Y, Real.exp (-(u / 2)) * S u))
            ((∫ y in (-Y)..0, Real.exp (y / 2) * (S y + S (-y))) -
              (ν / 6 * Y ^ 3 + (A - ν) / 2 * Y ^ 2 + Cm * Y))
          have a3 := abs_add_le ((∫ y in (-Y)..0, Real.exp (y / 2) * (S y + S (-y))) -
              ∫ u in (0 : ℝ)..Y, Real.exp (-(u / 2)) * S u)
            (∫ u in (0 : ℝ)..Y, Real.exp (-(u / 2)) * S u)
          linarith
      _ ≤ (C + ε * Y ^ 2) + T₀ * Y + T + |Cm| * Y := by linarith
      _ = C + T + ε * Y ^ 2 + (T₀ + |Cm|) * Y := by ring
  obtain ⟨hν, hA⟩ := eq_zero_of_forall_abs_cubic_le (by positivity) hcubic
  have hν0 : ν = 0 := by linarith
  have hA0 : A = 0 := by linarith
  refine eq_zero_of_weightKernelTransform_eq_zero hw2 fun y => ?_
  rw [hG y, hν0, hA0]; ring

end

end RHTower
