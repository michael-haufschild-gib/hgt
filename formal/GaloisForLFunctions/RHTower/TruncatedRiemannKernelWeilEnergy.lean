import GaloisForLFunctions.RHTower.CuspSeriesBulkTailBounds
import GaloisForLFunctions.HTGeometry.SmoothTransitionDerivBound


/-!
# Truncated combinations of Riemann's kernel and their Weil energy

For coefficients `a ∈ ℂ^{K+1}` let `F_a = ∑ a_i Φ^{(i)}`, which has transform `Q_a(-iz) Ξ(z)` and so
lies in the exact radical of the Weil form.  Truncate it with the cutoff
`χ_L(u) = ϑ(L-u)ϑ(L+u)` (equal to `1` on `[-(L-1), L-1]`, zero off `(-L, L)`):
`f_a = F_a χ_L`, tail `t_a = F_a(1 - χ_L)`.

* `norm_W_nearRadicalTest_le`: at every zero the Weil values of `f_a` are those of `-t_a`, so
  `‖W(f_a,f_a)‖ ≤ (5/4) S_Z (∫|t_a|e^{|u|/2} + ∫|t_a'|e^{|u|/2})²`.
* `nearRadicalTail_pointwise_le`, `nearRadicalTail_integrals_le`: in terms of the bulk maxima
  `M₁,…,M₄` of the four real polynomials attached to `a` (real and imaginary parts and their parity
  images), the tail integrals are at most `2(1+2Λ) K_t (M₁+⋯+M₄)`.
* `integral_norm_sq_nearRadicalTest_ge`: `∫|f_a|² ≥ K_b (M₁²+⋯+M₄²)`, from the bulk windows on
  both sides of the origin.
-/

open Complex MeasureTheory Filter Topology Set Polynomial
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-! ## The bulk cutoff -/

/-- `χ_L(u) = ϑ(L-u) ϑ(L+u)`: equal to `1` on `[-(L-1), L-1]` and to `0` off `(-L, L)`. -/
def bulkCutoff (L u : ℝ) : ℝ := Real.smoothTransition (L - u) * Real.smoothTransition (L + u)

theorem contDiff_bulkCutoff (L : ℝ) {n : ℕ∞} : ContDiff ℝ n (bulkCutoff L) := by
  unfold bulkCutoff
  exact (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.add contDiff_id))

theorem bulkCutoff_nonneg (L u : ℝ) : 0 ≤ bulkCutoff L u :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem bulkCutoff_le_one (L u : ℝ) : bulkCutoff L u ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem bulkCutoff_eq_one {L u : ℝ} (h : |u| ≤ L - 1) : bulkCutoff L u = 1 := by
  have h1 := neg_abs_le u; have h2 := le_abs_self u
  unfold bulkCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), mul_one]

theorem bulkCutoff_eq_zero {L u : ℝ} (h : L ≤ |u|) : bulkCutoff L u = 0 := by
  unfold bulkCutoff
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu] at h
    rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  · rw [abs_of_nonpos hu] at h
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : L + u ≤ 0), mul_zero]

/-- The derivative of the cutoff. -/
def bulkCutoffDeriv (L u : ℝ) : ℝ :=
  -deriv Real.smoothTransition (L - u) * Real.smoothTransition (L + u) +
    Real.smoothTransition (L - u) * deriv Real.smoothTransition (L + u)

theorem hasDerivAt_bulkCutoff (L u : ℝ) :
    HasDerivAt (bulkCutoff L) (bulkCutoffDeriv L u) u := by
  have hd : ∀ x : ℝ, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
    fun x => ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
      |>.differentiableAt).hasDerivAt
  have h1 := (hd (L - u)).comp u ((hasDerivAt_id u).const_sub L)
  have h2 := (hd (L + u)).comp u ((hasDerivAt_id u).const_add L)
  have h := h1.mul h2
  unfold bulkCutoff bulkCutoffDeriv
  refine h.congr_deriv ?_
  simp only [Function.comp_apply]
  ring

theorem bulkCutoffDeriv_eq_zero {L u : ℝ} (h : |u| < L - 1) : bulkCutoffDeriv L u = 0 := by
  have h1 := neg_abs_le u; have h2 := le_abs_self u
  unfold bulkCutoffDeriv
  rw [GaloisForLFunctions.HTGeometry.deriv_smoothTransition_eq_zero_of_notMem
      (x := L - u) (by intro hm; linarith [hm.2]),
    GaloisForLFunctions.HTGeometry.deriv_smoothTransition_eq_zero_of_notMem
      (x := L + u) (by intro hm; linarith [hm.2])]
  ring

theorem abs_bulkCutoffDeriv_le {Λ : ℝ} (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ)
    (L u : ℝ) : |bulkCutoffDeriv L u| ≤ 2 * Λ := by
  unfold bulkCutoffDeriv
  have ha := Real.smoothTransition.nonneg (L + u)
  have hb := Real.smoothTransition.le_one (L + u)
  have hc := Real.smoothTransition.nonneg (L - u)
  have hd := Real.smoothTransition.le_one (L - u)
  have e1 : |-deriv Real.smoothTransition (L - u) * Real.smoothTransition (L + u)| ≤ Λ := by
    rw [abs_mul, abs_neg, abs_of_nonneg ha]
    calc |deriv Real.smoothTransition (L - u)| * Real.smoothTransition (L + u)
        ≤ Λ * 1 := mul_le_mul (hΛ _) hb ha ((abs_nonneg _).trans (hΛ 0))
      _ = Λ := mul_one _
  have e2 : |Real.smoothTransition (L - u) * deriv Real.smoothTransition (L + u)| ≤ Λ := by
    rw [abs_mul, abs_of_nonneg hc]
    calc Real.smoothTransition (L - u) * |deriv Real.smoothTransition (L + u)|
        ≤ 1 * Λ := mul_le_mul hd (hΛ _) (abs_nonneg _) zero_le_one
      _ = Λ := one_mul _
  linarith [abs_add_le (-deriv Real.smoothTransition (L - u) * Real.smoothTransition (L + u))
    (Real.smoothTransition (L - u) * deriv Real.smoothTransition (L + u))]


/-! ## Combinations of `Φ, Φ', …, Φ^{(K)}` -/

theorem cuspDeriv_add (R S : ℝ[X]) : cuspDeriv (R + S) = cuspDeriv R + cuspDeriv S := by
  unfold cuspDeriv; rw [derivative_add]; ring

theorem cuspDeriv_C_mul (c : ℝ) (R : ℝ[X]) : cuspDeriv (C c * R) = C c * cuspDeriv R := by
  unfold cuspDeriv; rw [derivative_C_mul]; ring

theorem cuspDeriv_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (R : ι → ℝ[X]) :
    cuspDeriv (∑ i ∈ s, C (c i) * R i) = ∑ i ∈ s, C (c i) * cuspDeriv (R i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cuspDeriv]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, cuspDeriv_add, cuspDeriv_C_mul, ih]

/-- The polynomial of the real combination `∑ x_i Φ^{(i)}`. -/
def kernelPoly {K : ℕ} (x : Fin (K + 1) → ℝ) : ℝ[X] := ∑ i, C (x i) * riemannKernelPoly i

theorem natDegree_kernelPoly_le {K : ℕ} (x : Fin (K + 1) → ℝ) :
    (kernelPoly x).natDegree ≤ K + 2 := by
  unfold kernelPoly
  refine (natDegree_sum_le _ _).trans ?_
  refine Finset.fold_max_le _ |>.mpr ⟨by omega, fun i _ => ?_⟩
  refine (natDegree_C_mul_le _ _).trans ((natDegree_riemannKernelPoly_le _).trans ?_)
  have := i.2; omega

theorem cuspDeriv_kernelPoly {K : ℕ} (x : Fin (K + 1) → ℝ) :
    cuspDeriv (kernelPoly x) = ∑ i, C (x i) * riemannKernelPoly (i + 1) := by
  unfold kernelPoly
  rw [cuspDeriv_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold riemannKernelPoly
  rw [Function.iterate_succ_apply']

theorem cuspSeries_kernelPoly {K : ℕ} (x : Fin (K + 1) → ℝ) (u : ℝ) :
    cuspSeries (kernelPoly x) u = ∑ i, x i * cuspSeries (riemannKernelPoly i) u := by
  unfold kernelPoly; exact cuspSeries_sum _ _ _ _

theorem cuspSeries_cuspDeriv_kernelPoly {K : ℕ} (x : Fin (K + 1) → ℝ) (u : ℝ) :
    cuspSeries (cuspDeriv (kernelPoly x)) u =
      ∑ i, x i * cuspSeries (riemannKernelPoly (i + 1)) u := by
  rw [cuspDeriv_kernelPoly]; exact cuspSeries_sum _ _ _ _

theorem riemannKernelDeriv_eq_cuspSeries (k : ℕ) (u : ℝ) :
    riemannKernelDeriv k u = (cuspSeries (riemannKernelPoly k) u : ℂ) := rfl

theorem cuspSeries_riemannKernelPoly_neg (k : ℕ) (u : ℝ) :
    cuspSeries (riemannKernelPoly k) (-u) = (-1) ^ k * cuspSeries (riemannKernelPoly k) u := by
  have h := riemannKernelDeriv_neg k u
  rw [riemannKernelDeriv_eq_cuspSeries, riemannKernelDeriv_eq_cuspSeries] at h
  exact_mod_cast h

/-- Parity of coefficients: `x_i ↦ (-1)^i x_i`. -/
def parityCoeff {K : ℕ} (x : Fin (K + 1) → ℝ) : Fin (K + 1) → ℝ := fun i => (-1) ^ (i : ℕ) * x i

theorem cuspSeries_kernelPoly_neg {K : ℕ} (x : Fin (K + 1) → ℝ) (u : ℝ) :
    cuspSeries (kernelPoly x) (-u) = cuspSeries (kernelPoly (parityCoeff x)) u := by
  rw [cuspSeries_kernelPoly, cuspSeries_kernelPoly]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cuspSeries_riemannKernelPoly_neg]; unfold parityCoeff; ring

theorem cuspSeries_cuspDeriv_kernelPoly_neg {K : ℕ} (x : Fin (K + 1) → ℝ) (u : ℝ) :
    cuspSeries (cuspDeriv (kernelPoly x)) (-u) =
      -cuspSeries (cuspDeriv (kernelPoly (parityCoeff x))) u := by
  rw [cuspSeries_cuspDeriv_kernelPoly, cuspSeries_cuspDeriv_kernelPoly, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cuspSeries_riemannKernelPoly_neg]; unfold parityCoeff; ring

/-- The complex combination `F_a = ∑ a_i Φ^{(i)}`. -/
def kernelComb {K : ℕ} (a : Fin (K + 1) → ℂ) (u : ℝ) : ℂ := ∑ i, a i * riemannKernelDeriv i u

/-- Its derivative `∑ a_i Φ^{(i+1)}`. -/
def kernelCombDeriv {K : ℕ} (a : Fin (K + 1) → ℂ) (u : ℝ) : ℂ :=
  ∑ i, a i * riemannKernelDeriv (i + 1) u

theorem hasDerivAt_kernelComb {K : ℕ} (a : Fin (K + 1) → ℂ) (u : ℝ) :
    HasDerivAt (kernelComb a) (kernelCombDeriv a u) u := by
  unfold kernelComb kernelCombDeriv
  exact HasDerivAt.fun_sum fun i _ => (hasDerivAt_riemannKernelDeriv i u).const_mul (a i)

theorem kernelComb_eq {K : ℕ} (a : Fin (K + 1) → ℂ) (u : ℝ) :
    kernelComb a u = (cuspSeries (kernelPoly fun i => (a i).re) u : ℂ) +
      I * (cuspSeries (kernelPoly fun i => (a i).im) u : ℂ) := by
  unfold kernelComb
  rw [cuspSeries_kernelPoly, cuspSeries_kernelPoly]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [riemannKernelDeriv_eq_cuspSeries]
  conv_lhs => rw [← Complex.re_add_im (a i)]
  ring

theorem kernelCombDeriv_eq {K : ℕ} (a : Fin (K + 1) → ℂ) (u : ℝ) :
    kernelCombDeriv a u = (cuspSeries (cuspDeriv (kernelPoly fun i => (a i).re)) u : ℂ) +
      I * (cuspSeries (cuspDeriv (kernelPoly fun i => (a i).im)) u : ℂ) := by
  unfold kernelCombDeriv
  rw [cuspSeries_cuspDeriv_kernelPoly, cuspSeries_cuspDeriv_kernelPoly]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [riemannKernelDeriv_eq_cuspSeries]
  conv_lhs => rw [← Complex.re_add_im (a i)]
  ring

theorem superExpDecay_finset_sum {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℂ}
    (hg : ∀ i ∈ s, SuperExpDecay (g i)) : SuperExpDecay (fun u => ∑ i ∈ s, g i u) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨continuous_const, fun c => ?_⟩
    simp
  | insert a s ha ih =>
    have h1 := hg a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have h3 := h1.add h2
    refine (show (fun u => ∑ i ∈ insert a s, g i u) = fun u => g a u + ∑ i ∈ s, g i u from
      funext fun u => Finset.sum_insert ha) ▸ ?_
    exact h3

theorem superExpDecay_kernelComb {K : ℕ} (a : Fin (K + 1) → ℂ) : SuperExpDecay (kernelComb a) :=
  superExpDecay_finset_sum _ fun i _ => (superExpDecay_riemannKernelDeriv i).const_mul (a i)

theorem superExpDecay_kernelCombDeriv {K : ℕ} (a : Fin (K + 1) → ℂ) :
    SuperExpDecay (kernelCombDeriv a) :=
  superExpDecay_finset_sum _ fun i _ => (superExpDecay_riemannKernelDeriv (i + 1)).const_mul (a i)


/-! ## Truncated tests and their Weil energy -/

/-- The truncated test `f_a = F_a χ_L`. -/
def nearRadicalTest {K : ℕ} (L : ℝ) (a : Fin (K + 1) → ℂ) (u : ℝ) : ℂ :=
  kernelComb a u * (bulkCutoff L u : ℂ)

/-- The tail `t_a = F_a (1 - χ_L)`. -/
def nearRadicalTail {K : ℕ} (L : ℝ) (a : Fin (K + 1) → ℂ) (u : ℝ) : ℂ :=
  kernelComb a u * ((1 - bulkCutoff L u : ℝ) : ℂ)

/-- The derivative of the tail. -/
def nearRadicalTailDeriv {K : ℕ} (L : ℝ) (a : Fin (K + 1) → ℂ) (u : ℝ) : ℂ :=
  kernelCombDeriv a u * ((1 - bulkCutoff L u : ℝ) : ℂ) - kernelComb a u * (bulkCutoffDeriv L u : ℂ)

theorem nearRadicalTest_eq_sub {K : ℕ} (L : ℝ) (a : Fin (K + 1) → ℂ) (u : ℝ) :
    nearRadicalTest L a u = kernelComb a u - nearRadicalTail L a u := by
  unfold nearRadicalTest nearRadicalTail; push_cast; ring

theorem hasDerivAt_nearRadicalTail {K : ℕ} (L : ℝ) (a : Fin (K + 1) → ℂ) (u : ℝ) :
    HasDerivAt (nearRadicalTail L a) (nearRadicalTailDeriv L a u) u := by
  have h1 := hasDerivAt_kernelComb a u
  have h2 : HasDerivAt (fun u => ((1 - bulkCutoff L u : ℝ) : ℂ)) ((-bulkCutoffDeriv L u : ℝ) : ℂ) u :=
    ((hasDerivAt_bulkCutoff L u).const_sub 1).ofReal_comp
  have h := h1.mul h2
  unfold nearRadicalTail nearRadicalTailDeriv
  refine h.congr_deriv ?_
  push_cast; ring

theorem continuous_bulkCutoffDeriv (L : ℝ) : Continuous (bulkCutoffDeriv L) := by
  unfold bulkCutoffDeriv
  have hc := GaloisForLFunctions.HTGeometry.continuous_deriv_smoothTransition
  have hs := Real.smoothTransition.continuous
  fun_prop

theorem superExpDecay_nearRadicalTail {K : ℕ} (L : ℝ) (a : Fin (K + 1) → ℂ) :
    SuperExpDecay (nearRadicalTail L a) := by
  have h := (superExpDecay_kernelComb a).mul_bounded (χ := fun u => ((1 - bulkCutoff L u : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (continuous_const.sub (contDiff_bulkCutoff L (n := 0)).continuous))
    (B := 1) (fun u => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [bulkCutoff_le_one L u])]
      linarith [bulkCutoff_nonneg L u])
  refine (show (fun u => ((1 - bulkCutoff L u : ℝ) : ℂ) * kernelComb a u) = nearRadicalTail L a from
    funext fun u => by unfold nearRadicalTail; ring) ▸ h

theorem superExpDecay_nearRadicalTailDeriv {K : ℕ} (L : ℝ) (a : Fin (K + 1) → ℂ) {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) :
    SuperExpDecay (nearRadicalTailDeriv L a) := by
  have h1 := (superExpDecay_kernelCombDeriv a).mul_bounded
    (χ := fun u => ((1 - bulkCutoff L u : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (continuous_const.sub (contDiff_bulkCutoff L (n := 0)).continuous))
    (B := 1) (fun u => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [bulkCutoff_le_one L u])]
      linarith [bulkCutoff_nonneg L u])
  have h2 := (superExpDecay_kernelComb a).mul_bounded (χ := fun u => ((bulkCutoffDeriv L u : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (continuous_bulkCutoffDeriv L)) (B := 2 * Λ) (fun u => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_bulkCutoffDeriv_le hΛ L u)
  have h3 := h1.add (h2.const_mul (-1))
  refine (show (fun u => ((1 - bulkCutoff L u : ℝ) : ℂ) * kernelCombDeriv a u +
      (-1) * (((bulkCutoffDeriv L u : ℝ) : ℂ) * kernelComb a u)) = nearRadicalTailDeriv L a from
    funext fun u => by unfold nearRadicalTailDeriv; ring) ▸ h3

theorem paperFT_kernelComb {K : ℕ} (a : Fin (K + 1) → ℂ) (z : ℂ) :
    paperFT (kernelComb a) z = ∑ i, a i * paperFT (riemannKernelDeriv i) z := by
  unfold paperFT kernelComb
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]; congr 1; funext u; ring
  · have := ((superExpDecay_riemannKernelDeriv i).integrable_mul_cexp z).const_mul (a i)
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only; ring

theorem paperFT_kernelComb_at_zero {K : ℕ} (a : Fin (K + 1) → ℂ) {ρ : ℂ}
    (hρ : ρ ∈ zetaZeroConfig.carrier) :
    paperFT (kernelComb a) (gammaOf ρ) = 0 ∧
      paperFT (kernelComb a) ((starRingEnd ℂ) (gammaOf ρ)) = 0 := by
  constructor
  · rw [paperFT_kernelComb]
    exact Finset.sum_eq_zero fun i _ => by rw [(paperFT_riemannKernelDeriv_at_zero i hρ).1, mul_zero]
  · rw [paperFT_kernelComb]
    exact Finset.sum_eq_zero fun i _ => by rw [(paperFT_riemannKernelDeriv_at_zero i hρ).2, mul_zero]

theorem paperFT_nearRadicalTest_eq {K : ℕ} (L : ℝ) (a : Fin (K + 1) → ℂ) (z : ℂ) :
    paperFT (nearRadicalTest L a) z =
      paperFT (kernelComb a) z - paperFT (nearRadicalTail L a) z := by
  unfold paperFT
  rw [← integral_sub ((superExpDecay_kernelComb a).integrable_mul_cexp z)
    ((superExpDecay_nearRadicalTail L a).integrable_mul_cexp z)]
  congr 1; funext u; rw [nearRadicalTest_eq_sub]; ring

/-- `|ĝ(z)| ≤ ∫ |g| e^{|u|/2}` in the strip `|Im z| ≤ 1/2`. -/
theorem norm_paperFT_le_weighted {g : ℝ → ℂ} (hg : SuperExpDecay g) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT g z‖ ≤ ∫ u : ℝ, ‖g u‖ * Real.exp (1 / 2 * |u|) := by
  unfold paperFT
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun u => norm_nonneg _) (hg.2 (1 / 2))
    (Eventually.of_forall fun u => ?_))
  simp only
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le_exp hz u) (norm_nonneg _)

/-- In the strip, `(1 + |Re z|) |t̂(z)| ≤ ∫ |t| e^{|u|/2} + ∫ |t'| e^{|u|/2}`. -/
theorem one_add_abs_re_mul_norm_paperFT_tail_le {K : ℕ} (L : ℝ) (a : Fin (K + 1) → ℂ) {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    (1 + |z.re|) * ‖paperFT (nearRadicalTail L a) z‖ ≤
      (∫ u : ℝ, ‖nearRadicalTail L a u‖ * Real.exp (1 / 2 * |u|)) +
        ∫ u : ℝ, ‖nearRadicalTailDeriv L a u‖ * Real.exp (1 / 2 * |u|) := by
  have hT := superExpDecay_nearRadicalTail L a
  have hT' := superExpDecay_nearRadicalTailDeriv L a hΛ
  have h1 := norm_paperFT_le_weighted hT hz
  have hder := paperFT_deriv_of_superExpDecay hT hT' (hasDerivAt_nearRadicalTail L a) z
  have h2 := norm_paperFT_le_weighted hT' hz
  rw [hder, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul] at h2
  have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hn := norm_nonneg (paperFT (nearRadicalTail L a) z)
  nlinarith [mul_le_mul_of_nonneg_right hre hn]

/-- **Weil energy of a truncated radical combination.**  With `A = ∫|t|e^{|u|/2}` and
`B = ∫|t'|e^{|u|/2}` for the tail `t = F_a(1-χ_L)`:
`‖W(f_a, f_a)‖ ≤ (5/4) S_Z (A + B)²`, where `S_Z = ∑_ρ m_ρ/(1 + |γ_ρ|²)`. -/
theorem norm_W_nearRadicalTest_le {K : ℕ} (L : ℝ) (a : Fin (K + 1) → ℂ) {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) :
    ‖zetaZeroConfig.W (nearRadicalTest L a) (nearRadicalTest L a)‖ ≤
      (5 / 4) * (∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) *
      ((∫ u : ℝ, ‖nearRadicalTail L a u‖ * Real.exp (1 / 2 * |u|)) +
        ∫ u : ℝ, ‖nearRadicalTailDeriv L a u‖ * Real.exp (1 / 2 * |u|)) ^ 2 := by
  set E := (∫ u : ℝ, ‖nearRadicalTail L a u‖ * Real.exp (1 / 2 * |u|)) +
    ∫ u : ℝ, ‖nearRadicalTailDeriv L a u‖ * Real.exp (1 / 2 * |u|) with hE
  have hE0 : 0 ≤ E := add_nonneg (integral_nonneg fun _ => by positivity)
    (integral_nonneg fun _ => by positivity)
  have hsum : Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    have := WeilEF.zero_sum_inv_sq zetaSeam
    simpa [zetaZeroConfig] using this
  have hpt : ∀ ρ : zetaZeroConfig.carrier,
      ‖zetaZeroConfig.Wsummand (nearRadicalTest L a) (nearRadicalTest L a) ρ‖ ≤
        (5 / 4) * E ^ 2 * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    intro ρ
    have hmem := ρ.2
    have hstrip := zetaZeroConfig.strip ρ hmem
    have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
      have h : IsNontrivialZero (ρ : ℂ) := hmem
      exact ⟨h.2.1, h.2.2⟩
    have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
    have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
      rw [Complex.conj_im, abs_neg]; exact hIm
    obtain ⟨hz1, hz2⟩ := paperFT_kernelComb_at_zero a hmem
    have hv1 : (1 + |(ρ : ℂ).im|) * ‖paperFT (nearRadicalTest L a) (gammaOf ρ)‖ ≤ E := by
      rw [paperFT_nearRadicalTest_eq, hz1, zero_sub, norm_neg]
      have h := one_add_abs_re_mul_norm_paperFT_tail_le L a hΛ hIm
      rwa [WeilEF.gammaOf_re] at h
    have hv2 : (1 + |(ρ : ℂ).im|) *
        ‖paperFT (nearRadicalTest L a) ((starRingEnd ℂ) (gammaOf ρ))‖ ≤ E := by
      rw [paperFT_nearRadicalTest_eq, hz2, zero_sub, norm_neg]
      have h := one_add_abs_re_mul_norm_paperFT_tail_le L a hΛ hIm'
      rwa [Complex.conj_re, WeilEF.gammaOf_re] at h
    have hq := one_div_one_add_abs_im_sq_le hstrip
    have hd : 0 < 1 + |(ρ : ℂ).im| := by positivity
    unfold ZeroConfig.Wsummand
    rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    set x1 := ‖paperFT (nearRadicalTest L a) (gammaOf ρ)‖
    set x2 := ‖paperFT (nearRadicalTest L a) ((starRingEnd ℂ) (gammaOf ρ))‖
    have hprod : x1 * x2 ≤ E ^ 2 * (1 / (1 + |(ρ : ℂ).im|) ^ 2) := by
      have h12 : ((1 + |(ρ : ℂ).im|) * x1) * ((1 + |(ρ : ℂ).im|) * x2) ≤ E * E :=
        mul_le_mul hv1 hv2 (by positivity) hE0
      rw [← div_eq_mul_one_div, le_div_iff₀ (by positivity)]
      nlinarith
    calc (zetaZeroConfig.mult ρ : ℝ) * x1 * x2 = (zetaZeroConfig.mult ρ : ℝ) * (x1 * x2) := by ring
      _ ≤ (zetaZeroConfig.mult ρ : ℝ) * (E ^ 2 * (1 / (1 + |(ρ : ℂ).im|) ^ 2)) :=
          mul_le_mul_of_nonneg_left hprod hm
      _ ≤ (zetaZeroConfig.mult ρ : ℝ) *
            (E ^ 2 * ((5 / 4) * (1 / (1 + Complex.normSq (gammaOf ρ))))) := by
          gcongr
      _ = (5 / 4) * E ^ 2 * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
          ring
  have hsum' : Summable (fun ρ : zetaZeroConfig.carrier =>
      ‖zetaZeroConfig.Wsummand (nearRadicalTest L a) (nearRadicalTest L a) ρ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hsum.mul_left _)
  unfold ZeroConfig.W
  refine (norm_tsum_le_tsum_norm hsum').trans ?_
  refine (Summable.tsum_le_tsum hpt hsum' (hsum.mul_left _)).trans (le_of_eq ?_)
  rw [tsum_mul_left]; ring


/-! ## Tail and bulk in terms of the bulk maxima -/

theorem exists_bulk_max (R : ℝ[X]) {Y₀ : ℝ} (hY₀ : 0 < Y₀) :
    ∃ z ∈ Icc (Y₀ / 8) (Y₀ / 4), ∀ t ∈ Icc (Y₀ / 8) (Y₀ / 4), |R.eval t| ≤ |R.eval z| := by
  obtain ⟨z, hz, hmax⟩ := (isCompact_Icc (a := Y₀ / 8) (b := Y₀ / 4)).exists_isMaxOn
    ⟨Y₀ / 8, le_rfl, by linarith⟩ (Polynomial.continuous R).abs.continuousOn
  exact ⟨z, hz, fun t ht => hmax ht⟩

theorem norm_re_add_I_mul_le (x y : ℝ) : ‖(x : ℂ) + I * (y : ℂ)‖ ≤ |x| + |y| := by
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]

theorem norm_sq_re_add_I_mul (x y : ℝ) : ‖(x : ℂ) + I * (y : ℂ)‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp; ring

/-- **Pointwise tail bound.**  With `Y₀ = e^{2(L-1)}`, `k = K + 2`, `k + 1 ≤ Y₀/10`, and `M₁,…,M₄`
the bulk maxima of the four real polynomials attached to `a` (real and imaginary parts, and their
parity images), for every `u`:
`(‖t_a(u)‖ + ‖t_a'(u)‖) e^{|u|/2} ≤ (1+2Λ) K_t (M₁+M₂+M₃+M₄) e^{-|u|}`. -/
theorem nearRadicalTail_pointwise_le {K : ℕ} (L : ℝ) (a : Fin (K + 1) → ℂ) {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ)
    (hY₀ : 8 ≤ Real.exp (2 * (L - 1))) (hkY : ((K + 2 : ℕ) : ℝ) + 1 ≤ Real.exp (2 * (L - 1)) / 10)
    {M₁ M₂ M₃ M₄ : ℝ}
    (h₁ : ∀ t ∈ Icc (Real.exp (2 * (L - 1)) / 8) (Real.exp (2 * (L - 1)) / 4),
      |(kernelPoly fun i => (a i).re).eval t| ≤ M₁)
    (h₂ : ∀ t ∈ Icc (Real.exp (2 * (L - 1)) / 8) (Real.exp (2 * (L - 1)) / 4),
      |(kernelPoly fun i => (a i).im).eval t| ≤ M₂)
    (h₃ : ∀ t ∈ Icc (Real.exp (2 * (L - 1)) / 8) (Real.exp (2 * (L - 1)) / 4),
      |(kernelPoly (parityCoeff fun i => (a i).re)).eval t| ≤ M₃)
    (h₄ : ∀ t ∈ Icc (Real.exp (2 * (L - 1)) / 8) (Real.exp (2 * (L - 1)) / 4),
      |(kernelPoly (parityCoeff fun i => (a i).im)).eval t| ≤ M₄) (u : ℝ) :
    (‖nearRadicalTail L a u‖ + ‖nearRadicalTailDeriv L a u‖) * Real.exp (1 / 2 * |u|) ≤
      (1 + 2 * Λ) * (28 * ((K + 2 : ℕ) : ℝ) * (16 * Real.exp 1) ^ (K + 2) *
        Real.exp (2 * (L - 1)) ^ 2 * Real.exp (-π * Real.exp (2 * (L - 1)))) *
        (M₁ + M₂ + M₃ + M₄) * Real.exp (-|u|) := by
  set Kt := 28 * ((K + 2 : ℕ) : ℝ) * (16 * Real.exp 1) ^ (K + 2) *
    Real.exp (2 * (L - 1)) ^ 2 * Real.exp (-π * Real.exp (2 * (L - 1))) with hKt
  have hΛ0 : 0 ≤ Λ := (abs_nonneg _).trans (hΛ 0)
  have hk : 1 ≤ K + 2 := by omega
  have hM0 : ∀ {R : ℝ[X]} {M : ℝ}, (∀ t ∈ Icc (Real.exp (2 * (L - 1)) / 8)
      (Real.exp (2 * (L - 1)) / 4), |R.eval t| ≤ M) → 0 ≤ M := fun h =>
    (abs_nonneg _).trans (h _ ⟨le_rfl, by linarith [Real.exp_pos (2 * (L - 1))]⟩)
  have hKt0 : 0 ≤ Kt := by rw [hKt]; positivity
  have hRHS0 : 0 ≤ (1 + 2 * Λ) * Kt * (M₁ + M₂ + M₃ + M₄) * Real.exp (-|u|) := by
    have := hM0 h₁; have := hM0 h₂; have := hM0 h₃; have := hM0 h₄
    positivity
  -- inside the plateau both the tail and its derivative vanish
  by_cases hin : |u| < L - 1
  · have hχ := bulkCutoff_eq_one hin.le
    have hχ' := bulkCutoffDeriv_eq_zero hin
    have ht : nearRadicalTail L a u = 0 := by unfold nearRadicalTail; rw [hχ]; simp
    have ht' : nearRadicalTailDeriv L a u = 0 := by
      unfold nearRadicalTailDeriv; rw [hχ, hχ']; simp
    rw [ht, ht', norm_zero, add_zero, zero_mul]; exact hRHS0
  push Not at hin
  -- general bound by the untruncated combination
  have hcut : ‖nearRadicalTail L a u‖ + ‖nearRadicalTailDeriv L a u‖ ≤
      (1 + 2 * Λ) * (‖kernelComb a u‖ + ‖kernelCombDeriv a u‖) := by
    have h1c : ‖((1 - bulkCutoff L u : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [bulkCutoff_le_one L u])]
      linarith [bulkCutoff_nonneg L u]
    have h2c : ‖((bulkCutoffDeriv L u : ℝ) : ℂ)‖ ≤ 2 * Λ := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_bulkCutoffDeriv_le hΛ L u
    have e1 : ‖nearRadicalTail L a u‖ ≤ ‖kernelComb a u‖ := by
      unfold nearRadicalTail; rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) h1c)
    have e2 : ‖nearRadicalTailDeriv L a u‖ ≤ ‖kernelCombDeriv a u‖ + 2 * Λ * ‖kernelComb a u‖ := by
      unfold nearRadicalTailDeriv
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) h1c
      · rw [norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_right h2c (norm_nonneg _)
    have hn1 := norm_nonneg (kernelComb a u)
    have hn2 := norm_nonneg (kernelCombDeriv a u)
    nlinarith
  -- the weighted cusp tail at a point beyond the plateau
  have htailR : ∀ {x : Fin (K + 1) → ℝ} {M : ℝ}, (∀ t ∈ Icc (Real.exp (2 * (L - 1)) / 8)
      (Real.exp (2 * (L - 1)) / 4), |(kernelPoly x).eval t| ≤ M) → ∀ {v : ℝ}, L - 1 ≤ v →
      (|cuspSeries (kernelPoly x) v| + |cuspSeries (cuspDeriv (kernelPoly x)) v|) *
        Real.exp (v / 2) ≤ M * Kt * Real.exp (-v) := by
    intro x M hM v hv
    have := cuspSeries_tail_weighted_le hk (kernelPoly x) (natDegree_kernelPoly_le x)
      (u₀ := L - 1) hY₀ hkY hM hv
    rw [hKt]; linarith
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu] at hin ⊢
    have hA := htailR h₁ hin
    have hB := htailR h₂ hin
    rw [kernelComb_eq, kernelCombDeriv_eq] at hcut
    have n1 := norm_re_add_I_mul_le (cuspSeries (kernelPoly fun i => (a i).re) u)
      (cuspSeries (kernelPoly fun i => (a i).im) u)
    have n2 := norm_re_add_I_mul_le (cuspSeries (cuspDeriv (kernelPoly fun i => (a i).re)) u)
      (cuspSeries (cuspDeriv (kernelPoly fun i => (a i).im)) u)
    have hexp : Real.exp (1 / 2 * u) = Real.exp (u / 2) := by ring_nf
    rw [hexp]
    have hE := Real.exp_pos (u / 2)
    have hM3 := hM0 h₃; have hM4 := hM0 h₄
    have hEu := Real.exp_pos (-u)
    calc (‖nearRadicalTail L a u‖ + ‖nearRadicalTailDeriv L a u‖) * Real.exp (u / 2)
        ≤ (1 + 2 * Λ) * ((|cuspSeries (kernelPoly fun i => (a i).re) u| +
            |cuspSeries (cuspDeriv (kernelPoly fun i => (a i).re)) u|) * Real.exp (u / 2) +
            (|cuspSeries (kernelPoly fun i => (a i).im) u| +
            |cuspSeries (cuspDeriv (kernelPoly fun i => (a i).im)) u|) * Real.exp (u / 2)) := by
          refine (mul_le_mul_of_nonneg_right hcut hE.le).trans ?_
          have hN : ‖(cuspSeries (kernelPoly fun i => (a i).re) u : ℂ) +
                I * (cuspSeries (kernelPoly fun i => (a i).im) u : ℂ)‖ +
              ‖(cuspSeries (cuspDeriv (kernelPoly fun i => (a i).re)) u : ℂ) +
                I * (cuspSeries (cuspDeriv (kernelPoly fun i => (a i).im)) u : ℂ)‖ ≤
              (|cuspSeries (kernelPoly fun i => (a i).re) u| +
                |cuspSeries (cuspDeriv (kernelPoly fun i => (a i).re)) u|) +
              (|cuspSeries (kernelPoly fun i => (a i).im) u| +
                |cuspSeries (cuspDeriv (kernelPoly fun i => (a i).im)) u|) := by linarith
          have h1 : (0 : ℝ) ≤ 1 + 2 * Λ := by linarith
          calc (1 + 2 * Λ) * (‖(cuspSeries (kernelPoly fun i => (a i).re) u : ℂ) +
                I * (cuspSeries (kernelPoly fun i => (a i).im) u : ℂ)‖ +
              ‖(cuspSeries (cuspDeriv (kernelPoly fun i => (a i).re)) u : ℂ) +
                I * (cuspSeries (cuspDeriv (kernelPoly fun i => (a i).im)) u : ℂ)‖) *
                  Real.exp (u / 2)
              ≤ (1 + 2 * Λ) * ((|cuspSeries (kernelPoly fun i => (a i).re) u| +
                |cuspSeries (cuspDeriv (kernelPoly fun i => (a i).re)) u|) +
              (|cuspSeries (kernelPoly fun i => (a i).im) u| +
                |cuspSeries (cuspDeriv (kernelPoly fun i => (a i).im)) u|)) * Real.exp (u / 2) := by
                gcongr
            _ = _ := by ring
      _ ≤ (1 + 2 * Λ) * (M₁ * Kt * Real.exp (-u) + M₂ * Kt * Real.exp (-u)) := by gcongr
      _ ≤ (1 + 2 * Λ) * Kt * (M₁ + M₂ + M₃ + M₄) * Real.exp (-u) := by
          have : 0 ≤ (1 + 2 * Λ) * Kt * (M₃ + M₄) * Real.exp (-u) := by positivity
          nlinarith
  · have hnu : L - 1 ≤ -u := by rw [abs_of_nonpos hu] at hin; linarith
    have hA := htailR h₃ hnu
    have hB := htailR h₄ hnu
    rw [kernelComb_eq, kernelCombDeriv_eq] at hcut
    have e1 : ∀ x : Fin (K + 1) → ℝ, |cuspSeries (kernelPoly x) u| =
        |cuspSeries (kernelPoly (parityCoeff x)) (-u)| := by
      intro x; rw [← cuspSeries_kernelPoly_neg, neg_neg]
    have e2 : ∀ x : Fin (K + 1) → ℝ, |cuspSeries (cuspDeriv (kernelPoly x)) u| =
        |cuspSeries (cuspDeriv (kernelPoly (parityCoeff x))) (-u)| := by
      intro x
      have := cuspSeries_cuspDeriv_kernelPoly_neg x (-u)
      rw [neg_neg] at this; rw [this, abs_neg]
    have n1 := norm_re_add_I_mul_le (cuspSeries (kernelPoly fun i => (a i).re) u)
      (cuspSeries (kernelPoly fun i => (a i).im) u)
    have n2 := norm_re_add_I_mul_le (cuspSeries (cuspDeriv (kernelPoly fun i => (a i).re)) u)
      (cuspSeries (cuspDeriv (kernelPoly fun i => (a i).im)) u)
    rw [e1, e1] at n1
    rw [e2, e2] at n2
    rw [abs_of_nonpos hu]
    have hexp : Real.exp (1 / 2 * -u) = Real.exp (-u / 2) := by ring_nf
    rw [hexp]
    have hE := Real.exp_pos (-u / 2)
    have hM1 := hM0 h₁; have hM2 := hM0 h₂
    have hEu := Real.exp_pos (-(-u))
    calc (‖nearRadicalTail L a u‖ + ‖nearRadicalTailDeriv L a u‖) * Real.exp (-u / 2)
        ≤ (1 + 2 * Λ) *
            ((|cuspSeries (kernelPoly (parityCoeff fun i => (a i).re)) (-u)| +
            |cuspSeries (cuspDeriv (kernelPoly (parityCoeff fun i => (a i).re))) (-u)|) *
              Real.exp (-u / 2) +
            (|cuspSeries (kernelPoly (parityCoeff fun i => (a i).im)) (-u)| +
            |cuspSeries (cuspDeriv (kernelPoly (parityCoeff fun i => (a i).im))) (-u)|) *
              Real.exp (-u / 2)) := by
          refine (mul_le_mul_of_nonneg_right hcut hE.le).trans ?_
          have hN : ‖(cuspSeries (kernelPoly fun i => (a i).re) u : ℂ) +
                I * (cuspSeries (kernelPoly fun i => (a i).im) u : ℂ)‖ +
              ‖(cuspSeries (cuspDeriv (kernelPoly fun i => (a i).re)) u : ℂ) +
                I * (cuspSeries (cuspDeriv (kernelPoly fun i => (a i).im)) u : ℂ)‖ ≤
              (|cuspSeries (kernelPoly (parityCoeff fun i => (a i).re)) (-u)| +
                |cuspSeries (cuspDeriv (kernelPoly (parityCoeff fun i => (a i).re))) (-u)|) +
              (|cuspSeries (kernelPoly (parityCoeff fun i => (a i).im)) (-u)| +
                |cuspSeries (cuspDeriv (kernelPoly (parityCoeff fun i => (a i).im))) (-u)|) := by
            linarith
          have h1 : (0 : ℝ) ≤ 1 + 2 * Λ := by linarith
          calc (1 + 2 * Λ) * (‖(cuspSeries (kernelPoly fun i => (a i).re) u : ℂ) +
                I * (cuspSeries (kernelPoly fun i => (a i).im) u : ℂ)‖ +
              ‖(cuspSeries (cuspDeriv (kernelPoly fun i => (a i).re)) u : ℂ) +
                I * (cuspSeries (cuspDeriv (kernelPoly fun i => (a i).im)) u : ℂ)‖) *
                  Real.exp (-u / 2)
              ≤ (1 + 2 * Λ) * ((|cuspSeries (kernelPoly (parityCoeff fun i => (a i).re)) (-u)| +
                |cuspSeries (cuspDeriv (kernelPoly (parityCoeff fun i => (a i).re))) (-u)|) +
              (|cuspSeries (kernelPoly (parityCoeff fun i => (a i).im)) (-u)| +
                |cuspSeries (cuspDeriv (kernelPoly (parityCoeff fun i => (a i).im))) (-u)|)) *
                  Real.exp (-u / 2) := by gcongr
            _ = _ := by ring
      _ ≤ (1 + 2 * Λ) * (M₃ * Kt * Real.exp (-(-u)) + M₄ * Kt * Real.exp (-(-u))) := by
          gcongr
      _ ≤ (1 + 2 * Λ) * Kt * (M₁ + M₂ + M₃ + M₄) * Real.exp (-(-u)) := by
          have : 0 ≤ (1 + 2 * Λ) * Kt * (M₁ + M₂) * Real.exp (-(-u)) := by positivity
          nlinarith


/-- **The tail integrals.**  `∫|t_a|e^{|u|/2} + ∫|t_a'|e^{|u|/2} ≤ 2(1+2Λ) K_t (M₁+M₂+M₃+M₄)`. -/
theorem nearRadicalTail_integrals_le {K : ℕ} (L : ℝ) (a : Fin (K + 1) → ℂ) {Λ C : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ)
    (hpt : ∀ u : ℝ, (‖nearRadicalTail L a u‖ + ‖nearRadicalTailDeriv L a u‖) *
      Real.exp (1 / 2 * |u|) ≤ C * Real.exp (-|u|)) :
    (∫ u : ℝ, ‖nearRadicalTail L a u‖ * Real.exp (1 / 2 * |u|)) +
      ∫ u : ℝ, ‖nearRadicalTailDeriv L a u‖ * Real.exp (1 / 2 * |u|) ≤ 2 * C := by
  have hT := (superExpDecay_nearRadicalTail L a).2 (1 / 2)
  have hT' := (superExpDecay_nearRadicalTailDeriv L a hΛ).2 (1 / 2)
  rw [← integral_add hT hT']
  have hC : ∫ u : ℝ, C * Real.exp (-|u|) = 2 * C := by
    rw [integral_const_mul, integral_exp_neg_abs]; ring
  rw [← hC]
  refine integral_mono (hT.add hT') (integrable_exp_neg_abs.const_mul C) fun u => ?_
  simp only
  have := hpt u
  linarith

/-- On the bulk window the truncated test coincides with the untruncated combination. -/
theorem nearRadicalTest_eq_kernelComb {K : ℕ} {L u : ℝ} (a : Fin (K + 1) → ℂ)
    (hu : |u| ≤ L - 1) : nearRadicalTest L a u = kernelComb a u := by
  unfold nearRadicalTest; rw [bulkCutoff_eq_one hu]; simp

theorem setIntegral_Ioo_comp_neg (h : ℝ → ℝ) (p q : ℝ) (hpq : p ≤ q) :
    ∫ u in Ioo (-q) (-p), h u = ∫ v in Ioo p q, h (-v) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith), ← intervalIntegral.integral_of_le hpq,
    intervalIntegral.integral_comp_neg]

/-- **The bulk integral.**  With `z_j` maximizers of the four bulk polynomials,
`∫‖f_a‖² ≥ K_b (M₁² + M₂² + M₃² + M₄²)`, `K_b = e^{-πY₀/2}/(176(8e)^{2k})`. -/
theorem integral_norm_sq_nearRadicalTest_ge {K : ℕ} (L : ℝ) (a : Fin (K + 1) → ℂ)
    (hY₀ : 40 ≤ Real.exp (2 * (L - 1))) (hkY : ((K + 2 : ℕ) : ℝ) + 1 ≤ Real.exp (2 * (L - 1)) / 10)
    {z₁ z₂ z₃ z₄ : ℝ}
    (hz₁ : z₁ ∈ Icc (Real.exp (2 * (L - 1)) / 8) (Real.exp (2 * (L - 1)) / 4))
    (hz₂ : z₂ ∈ Icc (Real.exp (2 * (L - 1)) / 8) (Real.exp (2 * (L - 1)) / 4))
    (hz₃ : z₃ ∈ Icc (Real.exp (2 * (L - 1)) / 8) (Real.exp (2 * (L - 1)) / 4))
    (hz₄ : z₄ ∈ Icc (Real.exp (2 * (L - 1)) / 8) (Real.exp (2 * (L - 1)) / 4))
    (h₁ : ∀ t ∈ Icc (Real.exp (2 * (L - 1)) / 8) (Real.exp (2 * (L - 1)) / 4),
      |(kernelPoly fun i => (a i).re).eval t| ≤ |(kernelPoly fun i => (a i).re).eval z₁|)
    (h₂ : ∀ t ∈ Icc (Real.exp (2 * (L - 1)) / 8) (Real.exp (2 * (L - 1)) / 4),
      |(kernelPoly fun i => (a i).im).eval t| ≤ |(kernelPoly fun i => (a i).im).eval z₂|)
    (h₃ : ∀ t ∈ Icc (Real.exp (2 * (L - 1)) / 8) (Real.exp (2 * (L - 1)) / 4),
      |(kernelPoly (parityCoeff fun i => (a i).re)).eval t| ≤
        |(kernelPoly (parityCoeff fun i => (a i).re)).eval z₃|)
    (h₄ : ∀ t ∈ Icc (Real.exp (2 * (L - 1)) / 8) (Real.exp (2 * (L - 1)) / 4),
      |(kernelPoly (parityCoeff fun i => (a i).im)).eval t| ≤
        |(kernelPoly (parityCoeff fun i => (a i).im)).eval z₄|) :
    (Real.exp (-π * Real.exp (2 * (L - 1)) / 2) / (176 * (8 * Real.exp 1) ^ (2 * (K + 2)))) *
      (|(kernelPoly fun i => (a i).re).eval z₁| ^ 2 + |(kernelPoly fun i => (a i).im).eval z₂| ^ 2 +
        |(kernelPoly (parityCoeff fun i => (a i).re)).eval z₃| ^ 2 +
        |(kernelPoly (parityCoeff fun i => (a i).im)).eval z₄| ^ 2) ≤
      ∫ u : ℝ, ‖nearRadicalTest L a u‖ ^ 2 := by
  set Kb := Real.exp (-π * Real.exp (2 * (L - 1)) / 2) / (176 * (8 * Real.exp 1) ^ (2 * (K + 2)))
    with hKb
  set p := (L - 1) - 3 / 2 * Real.log 2 with hp
  set q := (L - 1) - Real.log 2 with hq
  have hlog2 := Real.log_two_gt_d9
  have hpq : p ≤ q := by rw [hp, hq]; linarith
  have hk : 1 ≤ K + 2 := by omega
  have hp0 : 0 < p := by
    have : 40 ≤ Real.exp (2 * (L - 1)) := hY₀
    have hL : Real.log 40 ≤ 2 * (L - 1) := by
      rw [← Real.log_exp (2 * (L - 1))]; exact Real.log_le_log (by norm_num) this
    have h40 : 3 * Real.log 2 < Real.log 40 := by
      rw [← Real.log_rpow (by norm_num)]
      exact Real.log_lt_log (by positivity) (by norm_num)
    rw [hp]; linarith
  set R₁ := kernelPoly fun i => (a i).re
  set R₂ := kernelPoly fun i => (a i).im
  set R₃ := kernelPoly (parityCoeff fun i => (a i).re)
  set R₄ := kernelPoly (parityCoeff fun i => (a i).im)
  have b₁ := cuspSeries_bulk_ge hk R₁ (natDegree_kernelPoly_le _) hY₀ hkY hz₁ rfl h₁
  have b₂ := cuspSeries_bulk_ge hk R₂ (natDegree_kernelPoly_le _) hY₀ hkY hz₂ rfl h₂
  have b₃ := cuspSeries_bulk_ge hk R₃ (natDegree_kernelPoly_le _) hY₀ hkY hz₃ rfl h₃
  have b₄ := cuspSeries_bulk_ge hk R₄ (natDegree_kernelPoly_le _) hY₀ hkY hz₄ rfl h₄
  rw [← hKb] at b₁ b₂ b₃ b₄
  -- continuity and integrability
  have hcontF : ∀ x : Fin (K + 1) → ℝ, Continuous fun u => (cuspSeries (kernelPoly x) u) ^ 2 :=
    fun x => (continuous_cuspSeries _).pow 2
  have hIoo : ∀ x : Fin (K + 1) → ℝ,
      IntegrableOn (fun u => (cuspSeries (kernelPoly x) u) ^ 2) (Ioo p q) :=
    fun x => (hcontF x).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hcontf : Continuous (nearRadicalTest L a) := by
    unfold nearRadicalTest
    exact (superExpDecay_kernelComb a).1.mul
      (Complex.continuous_ofReal.comp (contDiff_bulkCutoff L (n := 0)).continuous)
  have hsupp : ∀ u, L ≤ |u| → nearRadicalTest L a u = 0 := by
    intro u hu; unfold nearRadicalTest; rw [bulkCutoff_eq_zero hu]; simp
  have hcs : HasCompactSupport (fun u => ‖nearRadicalTest L a u‖ ^ 2) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -L) (b := L)) fun u hu => ?_
    have : L ≤ |u| := by
      by_contra h; push Not at h; exact hu ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
    simp [hsupp u this]
  have hint : Integrable (fun u => ‖nearRadicalTest L a u‖ ^ 2) :=
    (hcontf.norm.pow 2).integrable_of_hasCompactSupport hcs
  -- the two windows
  have hB : ∫ u in Ioo p q, ‖nearRadicalTest L a u‖ ^ 2 =
      (∫ u in Ioo p q, (cuspSeries R₁ u) ^ 2) + ∫ u in Ioo p q, (cuspSeries R₂ u) ^ 2 := by
    rw [← integral_add (hIoo _) (hIoo _)]
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    have hu' : |u| ≤ L - 1 := by
      rw [abs_of_pos (by linarith [hu.1])]; linarith [hu.2]
    rw [nearRadicalTest_eq_kernelComb a hu', kernelComb_eq, norm_sq_re_add_I_mul]
  have hBneg : ∫ u in Ioo (-q) (-p), ‖nearRadicalTest L a u‖ ^ 2 =
      (∫ u in Ioo p q, (cuspSeries R₃ u) ^ 2) + ∫ u in Ioo p q, (cuspSeries R₄ u) ^ 2 := by
    rw [setIntegral_Ioo_comp_neg _ p q hpq, ← integral_add (hIoo _) (hIoo _)]
    refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
    have hv' : |-v| ≤ L - 1 := by
      rw [abs_neg, abs_of_pos (by linarith [hv.1])]; linarith [hv.2]
    rw [nearRadicalTest_eq_kernelComb a hv', kernelComb_eq, norm_sq_re_add_I_mul,
      cuspSeries_kernelPoly_neg, cuspSeries_kernelPoly_neg]
  have hdisj : Disjoint (Ioo p q) (Ioo (-q) (-p)) := by
    rw [Set.disjoint_left]
    intro u hu hu'
    linarith [hu.1, hu'.2]
  have hunion : (∫ u in Ioo p q, ‖nearRadicalTest L a u‖ ^ 2) +
      ∫ u in Ioo (-q) (-p), ‖nearRadicalTest L a u‖ ^ 2 ≤ ∫ u, ‖nearRadicalTest L a u‖ ^ 2 := by
    rw [← setIntegral_union hdisj measurableSet_Ioo hint.integrableOn hint.integrableOn]
    exact setIntegral_le_integral hint (Eventually.of_forall fun u => by positivity)
  rw [hB, hBneg] at hunion
  nlinarith

end

end RHTower
