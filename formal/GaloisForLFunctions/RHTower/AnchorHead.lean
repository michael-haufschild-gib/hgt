/-
The finite Euler head as a nonvanishing pencil anchor, and its phase budget.

The anchor of the incidence pencil is a finite product `∏_{p∈P} (1 − p^{−s})` — the inverse
of a partial Euler product, a Dirichlet-computable entire function that is nonvanishing on the
open right half plane (each factor's modulus obeys `|p^{−s}| = p^{−σ} < 1` for `σ > 0`,
`p ≥ 2`).  Its logarithmic derivative is the finite prime sum
`∑_{p∈P} (log p) p^{−s} / (1 − p^{−s})`, whose modulus is bounded, uniformly in the height, by

  `∑_{p∈P} (log p) p^{−σ} / (1 − p^{−σ})`.

This is the anchor's phase-advance budget `C₁`: a height-independent constant, the "finite
prime sum" the winding argument concedes on the anchor side.  Because it does not grow with
the height, the archimedean winding floor — which grows like `½ log(τ/2π)` — overwhelms it on
any sufficiently high edge.
-/
import GaloisForLFunctions.RHTower.LateralWindingFloor

open Complex

namespace RHTower

/-- The finite Euler head anchor: `∏_{p∈P} (1 − p^{−s})`. -/
noncomputable def eulerHeadAnchor (P : Finset ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ P, (1 - (p : ℂ) ^ (-s))

/-- The anchor's height-independent phase-advance budget: `∑_{p∈P} (log p) p^{−σ}/(1−p^{−σ})`. -/
noncomputable def eulerHeadBound (P : Finset ℕ) (σ : ℝ) : ℝ :=
  ∑ p ∈ P, Real.log p * (p : ℝ) ^ (-σ) / (1 - (p : ℝ) ^ (-σ))

/-! ### The single factor -/

/-- Each Euler factor is nonvanishing in the open right half plane. -/
theorem eulerFactor_ne_zero {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
  have hpr : (0 : ℝ) < (p : ℝ) := by positivity
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hpr, Complex.neg_re]
  have hlt : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [hnorm]; exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp) (by linarith)
  intro hz
  have hone : (p : ℂ) ^ (-s) = 1 := by linear_combination -hz
  rw [hone, norm_one] at hlt
  exact lt_irrefl _ hlt

/-- Line derivative of a Euler factor. -/
theorem hasDerivAt_eulerFactor {p : ℕ} (hp : (p : ℂ) ≠ 0) (s : ℂ) :
    HasDerivAt (fun s => 1 - (p : ℂ) ^ (-s)) ((Complex.log p) * (p : ℂ) ^ (-s)) s := by
  have hns : HasDerivAt (fun s : ℂ => -s) (-1) s := (hasDerivAt_id s).neg
  have hcpow : HasDerivAt (fun s : ℂ => (p : ℂ) ^ (-s))
      ((p : ℂ) ^ (-s) * Complex.log p * (-1)) s := HasDerivAt.const_cpow hns (Or.inl hp)
  have h3 := hcpow.const_sub 1
  convert h3 using 1
  ring

/-- Each Euler factor is entire. -/
theorem differentiable_eulerFactor {p : ℕ} (hp : (p : ℂ) ≠ 0) :
    Differentiable ℂ (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) :=
  fun s => (hasDerivAt_eulerFactor hp s).differentiableAt

/-- The logarithmic derivative of a Euler factor is the prime term `(log p) p^{−s}/(1−p^{−s})`. -/
theorem logDeriv_eulerFactor {p : ℕ} (hp : (p : ℂ) ≠ 0) (s : ℂ) :
    logDeriv (fun s => 1 - (p : ℂ) ^ (-s)) s
      = (Complex.log p) * (p : ℂ) ^ (-s) / (1 - (p : ℂ) ^ (-s)) := by
  rw [logDeriv_apply, (hasDerivAt_eulerFactor hp s).deriv]

/-- The prime term's modulus is bounded, uniformly in the height, by
`(log p) p^{−σ}/(1 − p^{−σ})`. -/
theorem norm_logDeriv_eulerFactor_le {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    ‖(Complex.log p) * (p : ℂ) ^ (-s) / (1 - (p : ℂ) ^ (-s))‖
      ≤ Real.log p * (p : ℝ) ^ (-s.re) / (1 - (p : ℝ) ^ (-s.re)) := by
  have hpr : (0 : ℝ) < (p : ℝ) := by positivity
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hpr, Complex.neg_re]
  have hlt : (p : ℝ) ^ (-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hlogp : ‖Complex.log (p : ℂ)‖ = Real.log p := by
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_log (by positivity),
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hp.trans' (by norm_num)))]
  have hlognn : (0 : ℝ) ≤ Real.log p :=
    Real.log_nonneg (by exact_mod_cast hp.trans' (by norm_num))
  have hbpos : (0 : ℝ) < 1 - (p : ℝ) ^ (-s.re) := by linarith
  have hden : (1 : ℝ) - (p : ℝ) ^ (-s.re) ≤ ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ := by
    calc (1 : ℝ) - (p : ℝ) ^ (-s.re) = ‖(1 : ℂ)‖ - ‖(p : ℂ) ^ (-s)‖ := by rw [norm_one, hnorm]
      _ ≤ ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ := norm_sub_norm_le _ _
  rw [norm_div, norm_mul, hlogp, hnorm]
  exact div_le_div_of_nonneg_left (by positivity) hbpos hden

/-! ### The finite product -/

/-- The finite Euler head is nonvanishing in the open right half plane. -/
theorem eulerHeadAnchor_ne_zero {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    eulerHeadAnchor P s ≠ 0 := by
  unfold eulerHeadAnchor
  exact Finset.prod_ne_zero_iff.mpr fun p hp => eulerFactor_ne_zero (hP p hp) hs

/-- The finite Euler head is entire. -/
theorem differentiable_eulerHeadAnchor {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) :
    Differentiable ℂ (eulerHeadAnchor P) := by
  have heq : eulerHeadAnchor P = ∏ p ∈ P, (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) := by
    funext s; rw [eulerHeadAnchor, Finset.prod_apply]
  rw [heq]
  exact Differentiable.finsetProd fun p hp =>
    differentiable_eulerFactor (Nat.cast_ne_zero.mpr (by have := hP p hp; omega))

/-- The logarithmic derivative of the finite Euler head is the finite prime sum. -/
theorem logDeriv_eulerHeadAnchor {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    logDeriv (eulerHeadAnchor P) s
      = ∑ p ∈ P, (Complex.log p) * (p : ℂ) ^ (-s) / (1 - (p : ℂ) ^ (-s)) := by
  have hne : ∀ p ∈ P, (fun s => 1 - (p : ℂ) ^ (-s)) s ≠ 0 :=
    fun p hp => eulerFactor_ne_zero (hP p hp) hs
  have hdiff : ∀ p ∈ P, DifferentiableAt ℂ (fun s => 1 - (p : ℂ) ^ (-s)) s := by
    intro p hp
    have hpc : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hP p hp; omega)
    exact (differentiable_eulerFactor hpc) s
  unfold eulerHeadAnchor
  rw [logDeriv_prod hne hdiff]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpc : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hP p hp; omega)
  exact logDeriv_eulerFactor hpc s

/-- **The anchor phase budget.**  The finite Euler head's logarithmic derivative has modulus
bounded, uniformly in the height, by the prime sum `eulerHeadBound P σ` — hence so does its
real part, the anchor's phase-advance rate along a vertical edge. -/
theorem norm_logDeriv_eulerHeadAnchor_le {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p)
    {s : ℂ} (hs : 0 < s.re) :
    ‖logDeriv (eulerHeadAnchor P) s‖ ≤ eulerHeadBound P s.re := by
  rw [logDeriv_eulerHeadAnchor hP hs]
  refine le_trans (norm_sum_le _ _) ?_
  unfold eulerHeadBound
  exact Finset.sum_le_sum fun p hp => norm_logDeriv_eulerFactor_le (hP p hp) hs

/-- **The anchor's phase-advance rate is bounded by the prime sum, uniformly in the height.**
On a vertical edge at abscissa `σ`, the real part of the anchor's logarithmic derivative — the
integrand of its phase advance — is bounded by the height-independent `eulerHeadBound P σ`. -/
theorem abs_re_logDeriv_eulerHeadAnchor_le {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p)
    {σ : ℝ} (hσ : 0 < σ) (τ : ℝ) :
    |(logDeriv (eulerHeadAnchor P) (stripPt σ τ)).re| ≤ eulerHeadBound P σ := by
  have hs : 0 < (stripPt σ τ).re := by rw [stripPt_re]; exact hσ
  have h := norm_logDeriv_eulerHeadAnchor_le hP hs
  rw [stripPt_re] at h
  exact le_trans (Complex.abs_re_le_norm _) h

/-- The anchor phase budget is nonnegative. -/
theorem eulerHeadBound_nonneg {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {σ : ℝ} (hσ : 0 < σ) :
    0 ≤ eulerHeadBound P σ := by
  unfold eulerHeadBound
  refine Finset.sum_nonneg fun p hp => ?_
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hP p hp
  have hlt : (p : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hlognn : (0 : ℝ) ≤ Real.log p :=
    Real.log_nonneg (by exact_mod_cast (hP p hp).trans' (by norm_num))
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by positivity) _
  positivity

end RHTower
