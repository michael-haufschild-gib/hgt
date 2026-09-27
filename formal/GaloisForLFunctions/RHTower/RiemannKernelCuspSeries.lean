import GaloisForLFunctions.RHTower.ResolventDivisionDecay


/-!
# Derivatives of Riemann's kernel as cusp series

For a real polynomial `R` put `S_R(u) = ∑_{n ≥ 1} e^{u/2} R(n²e^{2u}) e^{-πn²e^{2u}}`.  The operator
`DR = R/2 + 2XR' - 2πXR` satisfies `S_R' = S_{DR}` (`hasDerivAt_cuspSeries`).  Riemann's kernel is
`Φ = S_{4π²X² - 6πX}` for every real `u` (`riemannPhiKernel_eq_cuspSeries`), so its derivatives are
`Φ^{(k)} = S_{P_k}` with `P_k = D^k(4π²X² - 6πX)` of degree exactly `k + 2`
(`coeff_riemannKernelPoly_top`).  They satisfy:

* parity: `Φ^{(k)}(-u) = (-1)^k Φ^{(k)}(u)`;
* super-exponential decay against every exponential weight;
* transform `(Φ^{(k)})^(z) = (-iz)^k Ξ(z)`, hence vanishing at both Weil evaluation points of every
  nontrivial zero (`paperFT_riemannKernelDeriv_at_zero`);
* the polynomials `P_0, …, P_K` are linearly independent.

So `Φ, Φ', …, Φ^{(K)}` span a `(K+1)`-dimensional space in the exact radical of the Weil form, on
which every element is, near the cusp, an explicit weighted polynomial in `e^{2u}`.
-/

open Complex MeasureTheory Filter Topology Set Polynomial
open scoped Real
open Bottcher

namespace RHTower

noncomputable section

/-! ## The cusp operator on polynomials -/

/-- `DR = R/2 + 2X R' - 2πX R`, the action of `d/du` on `e^{u/2} R(n²e^{2u}) e^{-πn²e^{2u}}`. -/
def cuspDeriv (R : ℝ[X]) : ℝ[X] :=
  C (1 / 2) * R + C 2 * X * derivative R - C (2 * π) * X * R

/-- One cusp term `e^{u/2} R(n²e^{2u}) e^{-πn²e^{2u}}`. -/
def cuspTerm (R : ℝ[X]) (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (u / 2) * R.eval ((n : ℝ) ^ 2 * Real.exp (2 * u)) *
    Real.exp (-π * ((n : ℝ) ^ 2 * Real.exp (2 * u)))

theorem hasDerivAt_cuspTerm (R : ℝ[X]) (n : ℕ) (u : ℝ) :
    HasDerivAt (cuspTerm R n) (cuspTerm (cuspDeriv R) n u) u := by
  have hY : HasDerivAt (fun u : ℝ => (n : ℝ) ^ 2 * Real.exp (2 * u))
      ((n : ℝ) ^ 2 * (Real.exp (2 * u) * 2)) u := by
    have := ((Real.hasDerivAt_exp (2 * u)).comp u ((hasDerivAt_id u).const_mul 2)).const_mul
      ((n : ℝ) ^ 2)
    simpa using this
  have hR := (Polynomial.hasDerivAt R ((n : ℝ) ^ 2 * Real.exp (2 * u))).comp u hY
  have hE := (Real.hasDerivAt_exp (-π * ((n : ℝ) ^ 2 * Real.exp (2 * u)))).comp u
    (hY.const_mul (-π))
  have hH : HasDerivAt (fun u : ℝ => Real.exp (u / 2)) (Real.exp (u / 2) * (1 / 2)) u := by
    have := (Real.hasDerivAt_exp (u / 2)).comp u ((hasDerivAt_id u).div_const 2)
    exact this.congr_deriv (by simp)
  have h := (hH.mul hR).mul hE
  unfold cuspTerm cuspDeriv
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply, Function.comp_apply, eval_sub, eval_add, eval_mul, eval_C, eval_X]
  ring

/-! ## Crude polynomial bounds -/

/-- `∑ |coeff j|`. -/
def polyAbsBound (R : ℝ[X]) : ℝ := ∑ j ∈ Finset.range (R.natDegree + 1), |R.coeff j|

theorem polyAbsBound_nonneg (R : ℝ[X]) : 0 ≤ polyAbsBound R :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_eval_le_polyAbsBound (R : ℝ[X]) {t : ℝ} (ht : 0 ≤ t) :
    |R.eval t| ≤ polyAbsBound R * (1 + t) ^ R.natDegree := by
  rw [eval_eq_sum_range, polyAbsBound, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  rw [abs_mul, abs_pow, abs_of_nonneg ht]
  have hj' : j ≤ R.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc t ^ j ≤ (1 + t) ^ j := pow_le_pow_left₀ ht (by linarith) j
    _ ≤ (1 + t) ^ R.natDegree := pow_le_pow_right₀ (by linarith) hj'

/-- On a window where `e^{2u} ∈ [Y₁, Y₂]` and `e^{u/2} ≤ H`, the `n`-th cusp term is at most
`H ‖R‖ (1+Y₂)^d n^{2d} e^{-π Y₁ n}`. -/
theorem abs_cuspTerm_le (R : ℝ[X]) (n : ℕ) {u Y₁ Y₂ H : ℝ} (hY₁ : 0 < Y₁)
    (h1 : Y₁ ≤ Real.exp (2 * u)) (h2 : Real.exp (2 * u) ≤ Y₂) (hH : Real.exp (u / 2) ≤ H) :
    |cuspTerm R (n + 1) u| ≤
      H * polyAbsBound R * (1 + Y₂) ^ R.natDegree * ((n + 1 : ℕ) : ℝ) ^ (2 * R.natDegree) *
        Real.exp (-(π * Y₁) * ((n + 1 : ℕ) : ℝ)) := by
  set m : ℝ := ((n + 1 : ℕ) : ℝ) with hm
  have hm1 : 1 ≤ m := by rw [hm]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  set Y := Real.exp (2 * u) with hYdef
  have hY0 : 0 ≤ Y := (Real.exp_pos _).le
  have ht : 0 ≤ m ^ 2 * Y := by positivity
  have hRb := abs_eval_le_polyAbsBound R ht
  have hpoly : (1 + m ^ 2 * Y) ^ R.natDegree ≤ (1 + Y₂) ^ R.natDegree * m ^ (2 * R.natDegree) := by
    rw [pow_mul, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have : m ^ 2 * Y ≤ m ^ 2 * Y₂ := mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith [sq_nonneg m, one_le_pow₀ (n := 2) hm1]
  have hexp : Real.exp (-π * (m ^ 2 * Y)) ≤ Real.exp (-(π * Y₁) * m) := by
    apply Real.exp_le_exp.mpr
    have : m ≤ m ^ 2 := by nlinarith
    have : Y₁ * m ≤ m ^ 2 * Y := by nlinarith
    nlinarith [Real.pi_pos]
  unfold cuspTerm
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  have hP := polyAbsBound_nonneg R
  calc Real.exp (u / 2) * |R.eval (m ^ 2 * Y)| * Real.exp (-π * (m ^ 2 * Y))
      ≤ H * (polyAbsBound R * ((1 + Y₂) ^ R.natDegree * m ^ (2 * R.natDegree))) *
          Real.exp (-(π * Y₁) * m) := by
        have hH0 : 0 ≤ H := (Real.exp_pos _).le.trans hH
        apply mul_le_mul _ hexp (Real.exp_pos _).le
          (mul_nonneg hH0 (mul_nonneg hP (mul_nonneg (pow_nonneg (by linarith) _)
            (pow_nonneg (by linarith) _))))
        exact mul_le_mul hH (hRb.trans (mul_le_mul_of_nonneg_left hpoly hP)) (abs_nonneg _) hH0
    _ = _ := by ring

theorem summable_cuspTerm_bound (d : ℕ) {r : ℝ} (hr : 0 < r) :
    Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ d * Real.exp (-r * ((n + 1 : ℕ) : ℝ)) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul d hr
  exact (summable_nat_add_iff 1).mpr h |>.congr fun n => by push_cast; ring_nf


/-! ## The cusp series -/

/-- `S_R(u) = ∑_{n ≥ 1} e^{u/2} R(n²e^{2u}) e^{-πn²e^{2u}}`. -/
def cuspSeries (R : ℝ[X]) (u : ℝ) : ℝ := ∑' n : ℕ, cuspTerm R (n + 1) u

theorem summable_cuspTerm (R : ℝ[X]) (u : ℝ) : Summable fun n : ℕ => cuspTerm R (n + 1) u := by
  have hY := Real.exp_pos (2 * u)
  refine Summable.of_norm_bounded ((summable_cuspTerm_bound (2 * R.natDegree)
    (mul_pos Real.pi_pos hY)).mul_left
      (Real.exp (u / 2) * polyAbsBound R * (1 + Real.exp (2 * u)) ^ R.natDegree)) fun n => ?_
  rw [Real.norm_eq_abs]
  refine (abs_cuspTerm_le R n hY le_rfl le_rfl le_rfl).trans (le_of_eq ?_)
  ring

theorem hasDerivAt_cuspSeries (R : ℝ[X]) (u₀ : ℝ) :
    HasDerivAt (cuspSeries R) (cuspSeries (cuspDeriv R) u₀) u₀ := by
  set Y₁ := Real.exp (2 * (u₀ - 1)) with hY₁
  set Y₂ := Real.exp (2 * (u₀ + 1)) with hY₂
  set H := Real.exp ((u₀ + 1) / 2) with hH
  have hY₁0 : 0 < Y₁ := Real.exp_pos _
  set d := (cuspDeriv R).natDegree with hd
  have hbound : ∀ n : ℕ, ∀ y ∈ Ioo (u₀ - 1) (u₀ + 1), ‖cuspTerm (cuspDeriv R) (n + 1) y‖ ≤
      H * polyAbsBound (cuspDeriv R) * (1 + Y₂) ^ d * (((n + 1 : ℕ) : ℝ) ^ (2 * d) *
        Real.exp (-(π * Y₁) * ((n + 1 : ℕ) : ℝ))) := by
    intro n y hy
    have hy' : u₀ - 1 < y ∧ y < u₀ + 1 := hy
    rw [Real.norm_eq_abs]
    have h1 : Y₁ ≤ Real.exp (2 * y) := Real.exp_le_exp.mpr (by linarith [hy'.1])
    have h2 : Real.exp (2 * y) ≤ Y₂ := Real.exp_le_exp.mpr (by linarith [hy'.2])
    have h3 : Real.exp (y / 2) ≤ H := Real.exp_le_exp.mpr (by linarith [hy'.2])
    refine (abs_cuspTerm_le (cuspDeriv R) n hY₁0 h1 h2 h3).trans (le_of_eq ?_)
    ring
  have hsum := (summable_cuspTerm_bound (2 * d) (mul_pos Real.pi_pos hY₁0)).mul_left
    (H * polyAbsBound (cuspDeriv R) * (1 + Y₂) ^ d)
  have h := hasDerivAt_tsum_of_isPreconnected (g := fun n : ℕ => cuspTerm R (n + 1))
    (g' := fun n : ℕ => cuspTerm (cuspDeriv R) (n + 1)) hsum isOpen_Ioo
    isPreconnected_Ioo (fun n y _ => hasDerivAt_cuspTerm R (n + 1) y) hbound
    (y₀ := u₀) (show u₀ ∈ Ioo (u₀ - 1) (u₀ + 1) from ⟨by linarith, by linarith⟩)
    (summable_cuspTerm R u₀) (show u₀ ∈ Ioo (u₀ - 1) (u₀ + 1) from ⟨by linarith, by linarith⟩)
  exact h

theorem continuous_cuspSeries (R : ℝ[X]) : Continuous (cuspSeries R) :=
  continuous_iff_continuousAt.mpr fun u => (hasDerivAt_cuspSeries R u).continuousAt

theorem cuspTerm_add (R S : ℝ[X]) (n : ℕ) (u : ℝ) :
    cuspTerm (R + S) n u = cuspTerm R n u + cuspTerm S n u := by
  unfold cuspTerm; rw [eval_add]; ring

theorem cuspTerm_smul (c : ℝ) (R : ℝ[X]) (n : ℕ) (u : ℝ) :
    cuspTerm (C c * R) n u = c * cuspTerm R n u := by
  unfold cuspTerm; rw [eval_mul, eval_C]; ring

theorem cuspSeries_add (R S : ℝ[X]) (u : ℝ) :
    cuspSeries (R + S) u = cuspSeries R u + cuspSeries S u := by
  unfold cuspSeries
  simp_rw [cuspTerm_add]
  exact (summable_cuspTerm R u).tsum_add (summable_cuspTerm S u)

theorem cuspSeries_smul (c : ℝ) (R : ℝ[X]) (u : ℝ) :
    cuspSeries (C c * R) u = c * cuspSeries R u := by
  unfold cuspSeries
  simp_rw [cuspTerm_smul]
  exact tsum_mul_left

theorem cuspSeries_sub (R S : ℝ[X]) (u : ℝ) :
    cuspSeries (R - S) u = cuspSeries R u - cuspSeries S u := by
  have h := cuspSeries_add R (C (-1) * S) u
  rw [cuspSeries_smul] at h
  rw [sub_eq_add_neg, show -S = C (-1) * S by simp, h]; ring

theorem cuspSeries_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (R : ι → ℝ[X]) (u : ℝ) :
    cuspSeries (∑ i ∈ s, C (c i) * R i) u = ∑ i ∈ s, c i * cuspSeries (R i) u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cuspSeries, cuspTerm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, cuspSeries_add, cuspSeries_smul, ih]


/-! ## Riemann's kernel as a cusp series -/

local notation "Φ" => riemannPhiKernel

/-- The theta tail is the cusp series of the constant polynomial `1`. -/
theorem modTail_thetaThree_eq_cuspSeries (u : ℝ) :
    modTail thetaThree 1 u = (cuspSeries 1 u : ℂ) := by
  have him : 0 < (modAxisPoint u).im := modAxisPoint_mem u
  have hθ : thetaThree (modAxisPoint u) = 1 + 2 * ∑' n : ℕ,
      cexp (π * I * ((n : ℂ) + 1) ^ 2 * modAxisPoint u) := by
    rw [thetaThree, ← jacobiTheta_eq_jacobiTheta₂, jacobiTheta_eq_tsum_nat him]
  have hterm : ∀ n : ℕ, cexp (π * I * ((n : ℂ) + 1) ^ 2 * modAxisPoint u) =
      ((Real.exp (-π * (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) : ℝ) : ℂ) := by
    intro n
    rw [Complex.ofReal_exp]
    congr 1
    unfold modAxisPoint
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  unfold modTail cuspSeries
  rw [hθ]
  simp_rw [hterm]
  rw [Complex.ofReal_tsum]
  have hsum : Summable fun n : ℕ => Real.exp (-π * (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) := by
    have h := summable_cuspTerm 1 u
    refine (h.mul_left (Real.exp (-(u / 2)))).congr fun n => ?_
    unfold cuspTerm
    simp only [eval_one, mul_one]
    rw [← mul_assoc, ← Real.exp_add]; simp
  rw [← Complex.ofReal_tsum, ← Complex.ofReal_tsum]
  have : ∑' n : ℕ, cuspTerm 1 (n + 1) u =
      Real.exp (u / 2) * ∑' n : ℕ, Real.exp (-π * (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    unfold cuspTerm; simp
  rw [this]
  push_cast
  ring

theorem modTailDeriv_thetaThree_eq_cuspSeries (u : ℝ) :
    modTailDeriv thetaThree 1 u = (cuspSeries (cuspDeriv 1) u : ℂ) := by
  have h1 := hasDerivAt_modTail (c := 1) thetaThree_differentiableOn u
  have h2 := (hasDerivAt_cuspSeries 1 u).ofReal_comp
  have hfun : modTail thetaThree 1 = fun x : ℝ => ((cuspSeries 1 x : ℝ) : ℂ) :=
    funext modTail_thetaThree_eq_cuspSeries
  rw [hfun] at h1
  exact h1.unique h2

theorem modTailDeriv2_thetaThree_eq_cuspSeries (u : ℝ) :
    modTailDeriv2 thetaThree 1 u = (cuspSeries (cuspDeriv (cuspDeriv 1)) u : ℂ) := by
  have h1 := hasDerivAt_modTailDeriv (c := 1) thetaThree_differentiableOn u
  have h2 := (hasDerivAt_cuspSeries (cuspDeriv 1) u).ofReal_comp
  have hfun : modTailDeriv thetaThree 1 = fun x : ℝ => ((cuspSeries (cuspDeriv 1) x : ℝ) : ℂ) :=
    funext modTailDeriv_thetaThree_eq_cuspSeries
  rw [hfun] at h1
  exact h1.unique h2

/-- The polynomial `D²1 - 1/4 = 4π²X² - 6πX` of Riemann's kernel. -/
def riemannCuspPoly : ℝ[X] := cuspDeriv (cuspDeriv 1) - C (1 / 4) * 1

/-- **Riemann's kernel is a cusp series:**
`Φ(u) = ∑_{n ≥ 1} e^{u/2}(4π²n⁴e^{4u} - 6πn²e^{2u}) e^{-πn²e^{2u}}` for every real `u`. -/
theorem riemannPhiKernel_eq_cuspSeries (u : ℝ) : Φ u = (cuspSeries riemannCuspPoly u : ℂ) := by
  have h := modSource_eq thetaThree 1 u
  rw [modTailDeriv2_thetaThree_eq_cuspSeries, modTail_thetaThree_eq_cuspSeries] at h
  unfold riemannPhiKernel
  rw [h, riemannCuspPoly, cuspSeries_sub, cuspSeries_smul]
  push_cast; ring

/-- The `k`-th derivative of Riemann's kernel, `Φ^{(k)} = S_{D^k(4π²X²-6πX)}`. -/
def riemannKernelDeriv (k : ℕ) (u : ℝ) : ℂ := (cuspSeries (cuspDeriv^[k] riemannCuspPoly) u : ℂ)

theorem riemannKernelDeriv_zero : riemannKernelDeriv 0 = Φ := by
  funext u; rw [riemannPhiKernel_eq_cuspSeries]; rfl

theorem hasDerivAt_riemannKernelDeriv (k : ℕ) (u : ℝ) :
    HasDerivAt (riemannKernelDeriv k) (riemannKernelDeriv (k + 1) u) u := by
  have h := (hasDerivAt_cuspSeries (cuspDeriv^[k] riemannCuspPoly) u).ofReal_comp
  unfold riemannKernelDeriv
  rw [Function.iterate_succ_apply']
  exact h

theorem continuous_riemannKernelDeriv (k : ℕ) : Continuous (riemannKernelDeriv k) :=
  continuous_iff_continuousAt.mpr fun u => (hasDerivAt_riemannKernelDeriv k u).continuousAt

/-- Parity: `Φ^{(k)}(-u) = (-1)^k Φ^{(k)}(u)`. -/
theorem riemannKernelDeriv_neg (k : ℕ) (u : ℝ) :
    riemannKernelDeriv k (-u) = (-1) ^ k * riemannKernelDeriv k u := by
  induction k generalizing u with
  | zero => rw [riemannKernelDeriv_zero]; simp [riemannPhiKernel_neg]
  | succ k ih =>
    have hl : HasDerivAt (fun x => riemannKernelDeriv k (-x)) (-riemannKernelDeriv (k + 1) (-u)) u := by
      have := (hasDerivAt_riemannKernelDeriv k (-u)).scomp u (hasDerivAt_neg u)
      simpa [Function.comp_def] using this
    have hr : HasDerivAt (fun x => (-1 : ℂ) ^ k * riemannKernelDeriv k x)
        ((-1) ^ k * riemannKernelDeriv (k + 1) u) u :=
      (hasDerivAt_riemannKernelDeriv k u).const_mul _
    have hfun : (fun x => riemannKernelDeriv k (-x)) =
        fun x => (-1 : ℂ) ^ k * riemannKernelDeriv k x := funext ih
    rw [hfun] at hl
    have := hl.unique hr
    rw [pow_succ]
    linear_combination -this


/-! ## Degrees -/

theorem natDegree_cuspDeriv_le (R : ℝ[X]) : (cuspDeriv R).natDegree ≤ R.natDegree + 1 := by
  unfold cuspDeriv
  refine (natDegree_sub_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
  · exact (natDegree_C_mul_le _ _).trans (Nat.le_succ _)
  · refine (natDegree_mul_le).trans ?_
    have h1 : (C (2 : ℝ) * X).natDegree ≤ 1 :=
      (natDegree_C_mul_le _ _).trans natDegree_X_le
    have h2 := natDegree_derivative_le R
    omega
  · refine (natDegree_mul_le).trans ?_
    have h1 : (C (2 * π) * X).natDegree ≤ 1 :=
      (natDegree_C_mul_le _ _).trans natDegree_X_le
    omega

theorem coeff_cuspDeriv_succ (R : ℝ[X]) :
    (cuspDeriv R).coeff (R.natDegree + 1) = -(2 * π) * R.coeff R.natDegree := by
  unfold cuspDeriv
  rw [coeff_sub, coeff_add, coeff_C_mul, mul_assoc, coeff_C_mul, coeff_X_mul, mul_assoc,
    coeff_C_mul, coeff_X_mul, coeff_derivative]
  rw [coeff_eq_zero_of_natDegree_lt (by omega : R.natDegree < R.natDegree + 1)]
  ring

theorem natDegree_riemannCuspPoly_le : riemannCuspPoly.natDegree ≤ 2 := by
  unfold riemannCuspPoly
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_cuspDeriv_le _).trans ?_
    have := (natDegree_cuspDeriv_le (1 : ℝ[X]))
    simp only [natDegree_one] at this
    omega
  · simp

theorem coeff_riemannCuspPoly_two : riemannCuspPoly.coeff 2 = 4 * π ^ 2 := by
  have h1 : (cuspDeriv (1 : ℝ[X])).coeff 1 = -(2 * π) := by
    have := coeff_cuspDeriv_succ (1 : ℝ[X]); simpa using this
  have hdeg1 : (cuspDeriv (1 : ℝ[X])).natDegree ≤ 1 := by
    have := natDegree_cuspDeriv_le (1 : ℝ[X]); simpa using this
  have h2 : (cuspDeriv (cuspDeriv (1 : ℝ[X]))).coeff 2 = -(2 * π) * (-(2 * π)) := by
    rcases Nat.lt_or_ge (cuspDeriv (1 : ℝ[X])).natDegree 1 with h | h
    · exfalso
      rw [coeff_eq_zero_of_natDegree_lt h] at h1
      have := Real.pi_pos; linarith
    · have he : (cuspDeriv (1 : ℝ[X])).natDegree = 1 := le_antisymm hdeg1 h
      have := coeff_cuspDeriv_succ (cuspDeriv (1 : ℝ[X]))
      rw [he] at this
      rw [this, h1]
  unfold riemannCuspPoly
  rw [coeff_sub, h2, mul_one, coeff_C]
  simp; ring

/-- The polynomial of `Φ^{(k)}`. -/
def riemannKernelPoly (k : ℕ) : ℝ[X] := cuspDeriv^[k] riemannCuspPoly

theorem natDegree_riemannKernelPoly_le (k : ℕ) : (riemannKernelPoly k).natDegree ≤ k + 2 := by
  induction k with
  | zero => exact natDegree_riemannCuspPoly_le
  | succ k ih =>
    unfold riemannKernelPoly at *
    rw [Function.iterate_succ_apply']
    exact (natDegree_cuspDeriv_le _).trans (by omega)

theorem coeff_riemannKernelPoly_top (k : ℕ) :
    (riemannKernelPoly k).coeff (k + 2) = 4 * π ^ 2 * (-(2 * π)) ^ k := by
  induction k with
  | zero => simpa [riemannKernelPoly] using coeff_riemannCuspPoly_two
  | succ k ih =>
    have hdeg := natDegree_riemannKernelPoly_le k
    have hne : (riemannKernelPoly k).coeff (k + 2) ≠ 0 := by
      rw [ih]
      have := Real.pi_pos
      exact mul_ne_zero (by positivity) (pow_ne_zero _ (by linarith))
    have heq : (riemannKernelPoly k).natDegree = k + 2 :=
      le_antisymm hdeg (le_natDegree_of_ne_zero hne)
    have h := coeff_cuspDeriv_succ (riemannKernelPoly k)
    rw [heq] at h
    unfold riemannKernelPoly at h ⊢
    rw [Function.iterate_succ_apply', show k + 1 + 2 = k + 2 + 1 by ring, h]
    unfold riemannKernelPoly at ih
    rw [ih]; ring

/-- The polynomials of `Φ, Φ', …, Φ^{(K)}` are linearly independent. -/
theorem eq_zero_of_sum_riemannKernelPoly {K : ℕ} (x : Fin (K + 1) → ℝ)
    (h : ∑ k : Fin (K + 1), C (x k) * riemannKernelPoly k = 0) : x = 0 := by
  induction K with
  | zero =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
    have h' := congrArg (fun P : ℝ[X] => P.coeff 2) h
    simp only [coeff_C_mul, coeff_zero] at h'
    have := coeff_riemannKernelPoly_top 0
    simp only [pow_zero, mul_one, zero_add] at this
    have h0 : ((0 : Fin (0 + 1)) : ℕ) = 0 := rfl
    rw [h0, this] at h'
    have hp : (4 : ℝ) * π ^ 2 ≠ 0 := by positivity
    funext i
    have hi : i = 0 := Fin.ext (by have := i.2; omega)
    subst hi
    simpa [hp] using h'
  | succ K ih =>
    rw [Fin.sum_univ_castSucc] at h
    have hlow : (∑ k : Fin (K + 1), C (x k.castSucc) * riemannKernelPoly k.castSucc).natDegree
        ≤ K + 2 := by
      refine (natDegree_sum_le _ _).trans ?_
      refine Finset.fold_max_le _ |>.mpr ⟨by omega, fun k _ => ?_⟩
      refine (natDegree_C_mul_le _ _).trans ((natDegree_riemannKernelPoly_le _).trans ?_)
      have := k.2; simp only [Fin.val_castSucc]; omega
    have htop := congrArg (fun P : ℝ[X] => P.coeff (K + 1 + 2)) h
    simp only [coeff_add, coeff_C_mul, coeff_zero] at htop
    rw [coeff_eq_zero_of_natDegree_lt (by omega)] at htop
    simp only [Fin.val_last] at htop
    rw [coeff_riemannKernelPoly_top] at htop
    have hp : (4 : ℝ) * π ^ 2 * (-(2 * π)) ^ (K + 1) ≠ 0 := by
      have := Real.pi_pos
      exact mul_ne_zero (by positivity) (pow_ne_zero _ (by linarith))
    have hxl : x (Fin.last (K + 1)) = 0 := by
      have : x (Fin.last (K + 1)) * (4 * π ^ 2 * (-(2 * π)) ^ (K + 1)) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right hp
    rw [hxl, C_0, zero_mul, add_zero] at h
    have hrest := ih (fun k => x k.castSucc) h
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hxl
    · exact congrFun hrest j


/-! ## Decay and transform of `Φ^{(k)}` -/

/-- Global constant for the cusp bound on `u ≥ 0`. -/
def cuspDecayConst (R : ℝ[X]) : ℝ :=
  polyAbsBound R * 2 ^ R.natDegree * Real.exp π *
    ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (2 * R.natDegree) * Real.exp (-π * ((n + 1 : ℕ) : ℝ))

theorem cuspDecayConst_nonneg (R : ℝ[X]) : 0 ≤ cuspDecayConst R := by
  unfold cuspDecayConst
  have := polyAbsBound_nonneg R
  have : 0 ≤ ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (2 * R.natDegree) * Real.exp (-π * ((n + 1 : ℕ) : ℝ)) :=
    tsum_nonneg fun n => by positivity
  positivity

/-- For `u ≥ 0`: `|S_R(u)| ≤ C_R e^{u/2} e^{2du} e^{-πe^{2u}}`. -/
theorem abs_cuspSeries_le (R : ℝ[X]) {u : ℝ} (hu : 0 ≤ u) :
    |cuspSeries R u| ≤ cuspDecayConst R * Real.exp (u / 2) *
      Real.exp (2 * R.natDegree * u) * Real.exp (-π * Real.exp (2 * u)) := by
  set d := R.natDegree with hd
  set Y := Real.exp (2 * u) with hY
  have hY1 : 1 ≤ Y := Real.one_le_exp (by linarith)
  have hsumb := summable_cuspTerm_bound (2 * d) Real.pi_pos
  have hterm : ∀ n : ℕ, |cuspTerm R (n + 1) u| ≤
      (polyAbsBound R * 2 ^ d * Real.exp π * Real.exp (u / 2) * Real.exp (2 * d * u) *
        Real.exp (-π * Y)) * (((n + 1 : ℕ) : ℝ) ^ (2 * d) * Real.exp (-π * ((n + 1 : ℕ) : ℝ))) := by
    intro n
    set m : ℝ := ((n + 1 : ℕ) : ℝ) with hm
    have hm1 : 1 ≤ m := by rw [hm]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hR := abs_eval_le_polyAbsBound R (show 0 ≤ m ^ 2 * Y by positivity)
    have hpoly : (1 + m ^ 2 * Y) ^ d ≤ 2 ^ d * m ^ (2 * d) * Real.exp (2 * d * u) := by
      have h1 : 1 + m ^ 2 * Y ≤ 2 * (m ^ 2 * Y) := by nlinarith
      have h2 : (2 * (m ^ 2 * Y)) ^ d = 2 ^ d * m ^ (2 * d) * Y ^ d := by
        rw [mul_pow, mul_pow, pow_mul]; ring
      have h3 : Y ^ d = Real.exp (2 * d * u) := by
        rw [hY, ← Real.exp_nat_mul]; ring_nf
      calc (1 + m ^ 2 * Y) ^ d ≤ (2 * (m ^ 2 * Y)) ^ d := pow_le_pow_left₀ (by positivity) h1 d
        _ = _ := by rw [h2, h3]
    have hexp : Real.exp (-π * (m ^ 2 * Y)) ≤ Real.exp π * Real.exp (-π * Y) *
        Real.exp (-π * m) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hYm : 0 ≤ Y * (m + 1) - 1 := by nlinarith
      have : Y + m - 1 ≤ m ^ 2 * Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hm1) hYm]
      nlinarith [Real.pi_pos]
    unfold cuspTerm
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    have hP := polyAbsBound_nonneg R
    calc Real.exp (u / 2) * |R.eval (m ^ 2 * Y)| * Real.exp (-π * (m ^ 2 * Y))
        ≤ Real.exp (u / 2) * (polyAbsBound R * (2 ^ d * m ^ (2 * d) * Real.exp (2 * d * u))) *
            (Real.exp π * Real.exp (-π * Y) * Real.exp (-π * m)) := by
          apply mul_le_mul _ hexp (Real.exp_pos _).le (by positivity)
          exact mul_le_mul_of_nonneg_left (hR.trans (mul_le_mul_of_nonneg_left hpoly hP))
            (Real.exp_pos _).le
      _ = _ := by ring
  have hbsum := hsumb.mul_left (polyAbsBound R * 2 ^ d * Real.exp π * Real.exp (u / 2) *
    Real.exp (2 * d * u) * Real.exp (-π * Y))
  unfold cuspSeries
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm (summable_cuspTerm R u).norm).trans ?_
  simp_rw [Real.norm_eq_abs]
  refine (Summable.tsum_le_tsum hterm ((summable_cuspTerm R u).abs) hbsum).trans (le_of_eq ?_)
  rw [tsum_mul_left]; unfold cuspDecayConst; ring

theorem norm_riemannKernelDeriv_neg (k : ℕ) (u : ℝ) :
    ‖riemannKernelDeriv k (-u)‖ = ‖riemannKernelDeriv k u‖ := by
  rw [riemannKernelDeriv_neg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

/-- `Φ^{(k)}` is continuous and integrable against every exponential weight. -/
theorem superExpDecay_riemannKernelDeriv (k : ℕ) : SuperExpDecay (riemannKernelDeriv k) := by
  refine ⟨continuous_riemannKernelDeriv k, fun c => ?_⟩
  set R := riemannKernelPoly k with hR
  set d := R.natDegree
  obtain ⟨C₀, hC₀, hC₀le⟩ := exists_superexp_le (c + 1 / 2 + 2 * d)
  have hB := cuspDecayConst_nonneg R
  have hpos : ∀ u : ℝ, 0 ≤ u → ‖riemannKernelDeriv k u‖ * Real.exp (c * |u|) ≤
      cuspDecayConst R * C₀ * Real.exp (-|u|) := by
    intro u hu
    have h1 : ‖riemannKernelDeriv k u‖ = |cuspSeries R u| := by
      unfold riemannKernelDeriv; rw [Complex.norm_real, Real.norm_eq_abs]; rfl
    rw [h1, abs_of_nonneg hu]
    have h2 := abs_cuspSeries_le R hu
    have h3 := hC₀le u hu
    have hE : 0 ≤ Real.exp (-π * Real.exp (2 * u)) := (Real.exp_pos _).le
    have h4 : Real.exp ((c + 1 / 2 + 2 * d) * u) * Real.exp (-π * Real.exp (2 * u)) ≤
        C₀ * Real.exp (-u) := by
      refine le_trans ?_ h3
      have : 1 ≤ 1 + Real.exp (2 * u) + Real.exp (2 * u) ^ 2 := by
        have := Real.exp_pos (2 * u); nlinarith
      have hx := Real.exp_pos ((c + 1 / 2 + 2 * d) * u)
      nlinarith [mul_nonneg (mul_nonneg hx.le hE) (sub_nonneg.mpr this)]
    calc |cuspSeries R u| * Real.exp (c * u)
        ≤ cuspDecayConst R * Real.exp (u / 2) * Real.exp (2 * d * u) *
            Real.exp (-π * Real.exp (2 * u)) * Real.exp (c * u) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = cuspDecayConst R * (Real.exp ((c + 1 / 2 + 2 * d) * u) *
            Real.exp (-π * Real.exp (2 * u))) := by
          rw [show (c + 1 / 2 + 2 * d) * u = u / 2 + 2 * d * u + c * u by ring,
            Real.exp_add, Real.exp_add]; ring
      _ ≤ cuspDecayConst R * (C₀ * Real.exp (-u)) := mul_le_mul_of_nonneg_left h4 hB
      _ = _ := by ring
  have hall : ∀ u : ℝ, ‖riemannKernelDeriv k u‖ * Real.exp (c * |u|) ≤
      cuspDecayConst R * C₀ * Real.exp (-|u|) := by
    intro u
    rcases le_total 0 u with h | h
    · exact hpos u h
    · have := hpos (-u) (by linarith)
      rwa [norm_riemannKernelDeriv_neg, abs_neg] at this
  refine Integrable.mono' (integrable_exp_neg_abs.const_mul (cuspDecayConst R * C₀)) ?_
    (Eventually.of_forall fun u => ?_)
  · exact ((continuous_riemannKernelDeriv k).norm.mul
      (by fun_prop : Continuous fun u : ℝ => Real.exp (c * |u|))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hall u

/-- `(Φ^{(k)})^(z) = (-iz)^k Ξ(z)`. -/
theorem paperFT_riemannKernelDeriv (k : ℕ) (z : ℂ) :
    Zeta23.paperFT (riemannKernelDeriv k) z =
      (-(I * z)) ^ k * riemannPhiTransform (1 / 2 + I * z) := by
  induction k with
  | zero => rw [riemannKernelDeriv_zero, paperFT_riemannPhiKernel]; ring
  | succ k ih =>
    rw [paperFT_deriv_of_superExpDecay (superExpDecay_riemannKernelDeriv k)
      (superExpDecay_riemannKernelDeriv (k + 1)) (hasDerivAt_riemannKernelDeriv k) z, ih]
    ring

/-- **Radical property**: every `Φ^{(k)}` has transform vanishing at both Weil evaluation points
of every nontrivial zero. -/
theorem paperFT_riemannKernelDeriv_at_zero (k : ℕ) {ρ : ℂ}
    (hρ : ρ ∈ Zeta23.zetaZeroConfig.carrier) :
    Zeta23.paperFT (riemannKernelDeriv k) (Zeta23.gammaOf ρ) = 0 ∧
      Zeta23.paperFT (riemannKernelDeriv k) ((starRingEnd ℂ) (Zeta23.gammaOf ρ)) = 0 := by
  have hz : ∀ σ ∈ Zeta23.zetaZeroConfig.carrier, riemannPhiTransform σ = 0 := by
    intro σ hσ
    rw [Zeta23.zetaZeroConfig_carrier] at hσ
    exact riemannPhiTransform_eq_zero_of_nontrivial hσ.1 hσ.2.1 hσ.2.2
  have h1 : 1 / 2 + I * Zeta23.gammaOf ρ = ρ := by
    unfold Zeta23.gammaOf; field_simp; ring
  have h2 : 1 / 2 + I * (starRingEnd ℂ) (Zeta23.gammaOf ρ) = Zeta23.reflect ρ := by
    unfold Zeta23.gammaOf Zeta23.reflect
    apply Complex.ext
    · simp; ring
    · simp
  refine ⟨?_, ?_⟩
  · rw [paperFT_riemannKernelDeriv, h1, hz ρ hρ, mul_zero]
  · rw [paperFT_riemannKernelDeriv, h2, hz _ (Zeta23.zetaZeroConfig.reflect_mem ρ hρ), mul_zero]

end

end RHTower
