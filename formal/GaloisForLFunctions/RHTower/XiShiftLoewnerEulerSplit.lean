/-
# The exact Euler--Gamma split of the shifted Loewner generator

On the Euler region the shifted generator splits as a finite-degree archimedean term minus the
complete von Mangoldt phase series: the two shifted Dirichlet series recombine into one series with
the hyperbolic weight `2 cosh (ω log n)`.
-/
import GaloisForLFunctions.RHTower.XiShiftLoewnerCriticalGenerator
import GaloisForLFunctions.RHTower.XiShiftDivisorPrimeSymbol

noncomputable section

open Complex Filter Topology
open scoped ComplexConjugate ComplexOrder

namespace RHTower

theorem deriv_xiCent (W : ℂ) : deriv xiCent W = deriv xi (1 / 2 + W) := by
  have h : HasDerivAt xi (deriv xi (W + 1 / 2)) (W + 1 / 2) := (xi_differentiable _).hasDerivAt
  have h2 : HasDerivAt (fun z : ℂ => xi (z + 1 / 2)) (deriv xi (W + 1 / 2)) W :=
    h.comp_add_const W (1 / 2)
  have h3 : xiCent = fun z : ℂ => xi (z + 1 / 2) := by
    funext z
    simp only [xiCent]
    congr 1
    ring
  rw [h3, h2.deriv, show W + (1 : ℂ) / 2 = 1 / 2 + W by ring]

theorem logDeriv_xiCent (W : ℂ) : logDeriv xiCent W = logDeriv xi (1 / 2 + W) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_xiCent, xiCent]

/-- The archimedean part `B_ω` of the shifted generator. -/
def xiShiftArch (ω : ℝ) (W : ℂ) : ℂ :=
  logDeriv archFactor (1 / 2 + (W - ω)) + logDeriv archFactor (1 / 2 + (W + ω))

/-- The card's `b (s) = 1/s + 1/(s-1) + (log Γ_ℝ)' (s)`. -/
theorem logDeriv_archFactor_split {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1)
    (hG : Gammaℝ s ≠ 0) (hGd : DifferentiableAt ℂ Gammaℝ s) :
    logDeriv archFactor s = 1 / s + 1 / (s - 1) + logDeriv Gammaℝ s := by
  have hpoly : HasDerivAt (fun z : ℂ => z * (z - 1) / 2) ((2 * s - 1) / 2) s := by
    have h1 : HasDerivAt (fun z : ℂ => z * (z - 1)) (1 * (s - 1) + s * 1) s :=
      (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)
    have h2 := h1.div_const 2
    have hval : (1 * (s - 1) + s * 1) / 2 = (2 * s - 1) / 2 := by ring
    rwa [hval] at h2
  have hGam : HasDerivAt Gammaℝ (deriv Gammaℝ s) s := hGd.hasDerivAt
  have hprod : HasDerivAt archFactor
      ((2 * s - 1) / 2 * Gammaℝ s + s * (s - 1) / 2 * deriv Gammaℝ s) s := hpoly.mul hGam
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  rw [logDeriv_apply, hprod.deriv, archFactor, logDeriv_apply]
  field_simp
  ring

/-- The complete prime phase carrier `2 Λ(n) n^{-1/2} cosh (ω log n) n^{-W}`. -/
def xiShiftPrimeTerm (ω : ℝ) (W : ℂ) (n : ℕ) : ℂ :=
  2 * (ArithmeticFunction.vonMangoldt n : ℂ) * ((n : ℂ) ^ (-(1 / 2 : ℂ) - W)) *
    ((Real.cosh (ω * Real.log n) : ℝ) : ℂ)

theorem lSeries_term_pair (ω : ℝ) (W : ℂ) (n : ℕ) :
    LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (1 / 2 + (W - ω)) n
      + LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (1 / 2 + (W + ω)) n
      = xiShiftPrimeTerm ω W n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term, xiShiftPrimeTerm]
  · have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
    have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hnpos.le]
    have hpow : ∀ t : ℝ, (n : ℂ) ^ ((t : ℝ) : ℂ) = ((Real.exp (t * Real.log n) : ℝ) : ℂ) := by
      intro t
      rw [Complex.cpow_def_of_ne_zero hnc, hlog, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
      congr 2
      ring
    have hbne : ∀ z : ℂ, (n : ℂ) ^ z ≠ 0 := by
      intro z
      rw [Complex.cpow_def_of_ne_zero hnc]
      exact Complex.exp_ne_zero _
    have hcosh : 2 * ((Real.cosh (ω * Real.log n) : ℝ) : ℂ)
        = (n : ℂ) ^ ((ω : ℂ)) + ((n : ℂ) ^ ((ω : ℂ)))⁻¹ := by
      have h1 := hpow ω
      have h2 := hpow (-ω)
      rw [Complex.ofReal_neg] at h2
      have hinv : ((n : ℂ) ^ ((ω : ℂ)))⁻¹ = (n : ℂ) ^ (-(ω : ℂ)) := by
        rw [Complex.cpow_neg]
      rw [hinv, h1, h2, ← Complex.ofReal_add, Real.cosh_eq]
      push_cast
      ring
    have hsplit1 : (n : ℂ) ^ (1 / 2 + (W - (ω : ℂ)))
        = (n : ℂ) ^ (1 / 2 + W) * ((n : ℂ) ^ ((ω : ℂ)))⁻¹ := by
      rw [← Complex.cpow_neg, ← Complex.cpow_add _ _ hnc]
      congr 1
      ring
    have hsplit2 : (n : ℂ) ^ (1 / 2 + (W + (ω : ℂ)))
        = (n : ℂ) ^ (1 / 2 + W) * (n : ℂ) ^ ((ω : ℂ)) := by
      rw [← Complex.cpow_add _ _ hnc]
      congr 1
      ring
    have hbase : (n : ℂ) ^ (-(1 / 2 : ℂ) - W) = ((n : ℂ) ^ (1 / 2 + W))⁻¹ := by
      rw [← Complex.cpow_neg]
      congr 1
      ring
    have hcosh' : ((Real.cosh (ω * Real.log n) : ℝ) : ℂ)
        = ((n : ℂ) ^ ((ω : ℂ)) + ((n : ℂ) ^ ((ω : ℂ)))⁻¹) / 2 := by
      rw [eq_div_iff (two_ne_zero)]
      linear_combination hcosh
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, xiShiftPrimeTerm,
      hsplit1, hsplit2, hbase, hcosh']
    have h1 := hbne (1 / 2 + W)
    have h2 := hbne ((ω : ℂ))
    field_simp

/-- **The exact Euler--Gamma split.**  On the Euler region the shifted generator is the archimedean
term minus the complete von Mangoldt phase series. -/
theorem xiShiftGen_eq_arch_sub_primeSeries {ω : ℝ} {W : ℂ} (hW : 1 / 2 + |ω| < W.re) :
    xiShiftGen ω W = xiShiftArch ω W - ∑' n : ℕ, xiShiftPrimeTerm ω W n := by
  have hle : ω ≤ |ω| := le_abs_self ω
  have hle' : -ω ≤ |ω| := neg_le_abs ω
  have hre1 : 1 < ((1 : ℂ) / 2 + (W - (ω : ℂ))).re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.div_re, Complex.one_re,
      Complex.one_im]
    norm_num
    linarith
  have hre2 : 1 < ((1 : ℂ) / 2 + (W + (ω : ℂ))).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.div_re, Complex.one_re, Complex.one_im]
    norm_num
    linarith
  have hs1 := ArithmeticFunction.LSeriesSummable_vonMangoldt hre1
  have hs2 := ArithmeticFunction.LSeriesSummable_vonMangoldt hre2
  have hsum : (∑' n : ℕ, xiShiftPrimeTerm ω W n)
      = LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (1 / 2 + (W - (ω : ℂ)))
        + LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (1 / 2 + (W + (ω : ℂ))) := by
    rw [LSeries, LSeries, ← Summable.tsum_add hs1 hs2]
    exact tsum_congr (fun n => (lSeries_term_pair ω W n).symm)
  have e1 := logDeriv_xi_sub_archFactor_eq_neg_vonMangoldtLSeries hre1
  have e2 := logDeriv_xi_sub_archFactor_eq_neg_vonMangoldtLSeries hre2
  rw [xiShiftGen, logDeriv_xiCent, logDeriv_xiCent, hsum, xiShiftArch]
  linear_combination e1 + e2

/-- **Absolute convergence in the Euler region.** -/
theorem summable_xiShiftPrimeTerm {ω : ℝ} {W : ℂ} (hW : 1 / 2 + |ω| < W.re) :
    Summable (fun n : ℕ => xiShiftPrimeTerm ω W n) := by
  have hle : ω ≤ |ω| := le_abs_self ω
  have hle' : -ω ≤ |ω| := neg_le_abs ω
  have hre1 : 1 < ((1 : ℂ) / 2 + (W - (ω : ℂ))).re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.div_re, Complex.one_re,
      Complex.one_im]
    norm_num
    linarith
  have hre2 : 1 < ((1 : ℂ) / 2 + (W + (ω : ℂ))).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.div_re, Complex.one_re, Complex.one_im]
    norm_num
    linarith
  have hs1 : Summable (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      (1 / 2 + (W - (ω : ℂ)))) := ArithmeticFunction.LSeriesSummable_vonMangoldt hre1
  have hs2 : Summable (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      (1 / 2 + (W + (ω : ℂ)))) := ArithmeticFunction.LSeriesSummable_vonMangoldt hre2
  exact (hs1.add hs2).congr (fun n => lSeries_term_pair ω W n)


/-! ## The Schur-complement interface -/

/-- The archimedean generator kernel `C_{B,ω}`. -/
def xiShiftArchKernel (ω : ℝ) (W V : ℂ) : ℂ :=
  (xiShiftArch ω W + conj (xiShiftArch ω V)) / (W + conj V)

/-- The complete prime generator kernel `C_{P,ω}`. -/
def xiShiftPrimeKernel (ω : ℝ) (W V : ℂ) : ℂ :=
  ((∑' n : ℕ, xiShiftPrimeTerm ω W n) + conj (∑' n : ℕ, xiShiftPrimeTerm ω V n)) / (W + conj V)

/-- **The Schur-complement splitting.**  On the Euler region the generator kernel is the
archimedean kernel minus the complete prime kernel. -/
theorem xiShiftGenKernel_eq_arch_sub_prime {ω : ℝ} {W V : ℂ}
    (hW : 1 / 2 + |ω| < W.re) (hV : 1 / 2 + |ω| < V.re) :
    xiShiftGenKernel ω W V = xiShiftArchKernel ω W V - xiShiftPrimeKernel ω W V := by
  rw [xiShiftGenKernel, xiShiftArchKernel, xiShiftPrimeKernel,
    xiShiftGen_eq_arch_sub_primeSeries hW, xiShiftGen_eq_arch_sub_primeSeries hV, map_sub,
    ← sub_div]
  ring_nf

/-- **The Gram-completion interface.**  Positivity of the critical generator on a finite node set
is exactly the Loewner domination of the prime matrix by the archimedean matrix. -/
theorem posSemidef_criticalGenerator_iff_arch_sub_prime {n : ℕ} (Z : Fin n → ℂ)
    (hZ : ∀ j, 1 / 2 < (Z j).re) :
    (Matrix.of fun j k => xiShiftGenKernel 0 (Z j) (Z k)).PosSemidef ↔
      ((Matrix.of fun j k => xiShiftArchKernel 0 (Z j) (Z k))
        - Matrix.of fun j k => xiShiftPrimeKernel 0 (Z j) (Z k)).PosSemidef := by
  have hEq : (Matrix.of fun j k => xiShiftGenKernel 0 (Z j) (Z k))
      = ((Matrix.of fun j k => xiShiftArchKernel 0 (Z j) (Z k))
        - Matrix.of fun j k => xiShiftPrimeKernel 0 (Z j) (Z k)) := by
    ext j k
    rw [Matrix.sub_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply]
    exact xiShiftGenKernel_eq_arch_sub_prime (by simpa using hZ j) (by simpa using hZ k)
  rw [hEq]

end RHTower
