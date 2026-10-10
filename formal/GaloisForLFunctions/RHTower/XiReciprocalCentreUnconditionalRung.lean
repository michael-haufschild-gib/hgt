import GaloisForLFunctions.RHTower.XiReciprocalCentreCriterion
import GaloisForLFunctions.RHTower.XiHorizontalSlicePolyaFrequencyCone
import GaloisForLFunctions.HTGeometry.ToeplitzHessenbergReciprocal

/-!
# The first reciprocal centre coefficients are nonnegative, unconditionally

Write `ξ(½ + x) = Σ_k a_k x^{2k}`, so `Ξ(σ) = Σ_k (−1)^k a_k σ^{2k}`, and let `β_m` be the coefficient
of `σ^{2m}` in `1/Ξ(σ)` (`evenRecipCoeff XiC`).  The relation `Ξ · (1/Ξ) = 1` at even order reads
`Σ_{k ≤ m} (−1)^k a_k β_{m−k} = [m = 0]`.  By the Hessenberg–Wronski identity, `a₀^{m+1} β_m` is a
Toeplitz minor of `(a_k)`.  So `PF_k` of the centre coefficients gives `β_m ≥ 0` for `m ≤ k`
(`evenRecipCoeff_XiC_nonneg_of_pfSeq`).  The unconditional `PF_37` of the centre coefficients
(`xi_centre_pfSeq_thirtySeven`) gives `β_m ≥ 0` for every `m ≤ 37`
(`evenRecipCoeff_XiC_nonneg_of_le_thirtySeven`).  These are the first 38 diagonal entries of the
single-sequence criterion `riemannHypothesis_iff_reciprocalTP_xiCentreLift`.
-/

open Complex
open scoped ComplexOrder Nat
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The even coefficients of `Ξ` are `(−1)^k a_k`. -/
theorem factorial_inv_mul_iteratedDeriv_XiC_even (k : ℕ) :
    (((2 * k).factorial : ℂ))⁻¹ * iteratedDeriv (2 * k) XiC 0 =
      ((((-1 : ℝ) ^ k * evenTaylorRe (fun x => xi (1 / 2 + x)) k : ℝ)) : ℂ) := by
  have hfun : XiC = fun σ => (fun x => xi (1 / 2 + x)) (I * σ) := by
    funext σ
    simp only [XiC]
    congr 1
    ring
  have hdiff : Differentiable ℂ (fun x => xi (1 / 2 + x)) :=
    xi_differentiable.comp (by fun_prop)
  rw [hfun, iteratedDeriv_comp_const_mul hdiff.contDiff I]
  simp only [mul_zero]
  have hreal : (((2 * k).factorial : ℂ))⁻¹ * iteratedDeriv (2 * k) (fun x => xi (1 / 2 + x)) 0 =
      ((evenTaylorRe (fun x => xi (1 / 2 + x)) k : ℝ) : ℂ) := by
    have h := (turanTaylorAtZero_XiC_neg_I_mul_of_cone sqrt3Cone_centre).1.2 (2 * k)
    have he : (fun x => XiC (-(I * x))) = fun x => xi (1 / 2 + x) := by
      funext x
      simp only [XiC]
      congr 1
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [he] at h
    apply Complex.ext
    · simp [evenTaylorRe]
    · simp only [Complex.ofReal_im]
      rw [Complex.mul_im, (Complex.nonneg_iff.mp h).2.symm, mul_zero, zero_add,
        show (((2 * k).factorial : ℂ))⁻¹ = ((((2 * k).factorial : ℝ))⁻¹ : ℝ) by push_cast; rfl,
        Complex.ofReal_im, zero_mul]
  rw [pow_mul, Complex.I_sq, mul_left_comm, hreal]
  push_cast
  ring

/-- The reciprocal `1/Ξ` has real even Taylor coefficients at `0`. -/
theorem factorial_inv_mul_iteratedDeriv_inv_XiC_even (j : ℕ) :
    (((2 * j).factorial : ℂ))⁻¹ * iteratedDeriv (2 * j) (fun σ => (XiC σ)⁻¹) 0 =
      ((evenRecipCoeff XiC j : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [evenRecipCoeff]
  · simp only [Complex.ofReal_im]
    have hsym : (starRingEnd ℂ) ∘ (fun σ => (XiC σ)⁻¹) ∘ (starRingEnd ℂ) =
        fun σ => (XiC σ)⁻¹ := by
      funext σ
      simp only [Function.comp_apply, XiC_conj, map_inv₀, Complex.conj_conj]
    have h := congrFun (iteratedDeriv_conj_comp_conj (fun σ => (XiC σ)⁻¹) (2 * j)) 0
    rw [hsym] at h
    simp only [Function.comp_apply, map_zero] at h
    have him : (iteratedDeriv (2 * j) (fun σ => (XiC σ)⁻¹) 0).im = 0 := by
      have := congrArg Complex.im h
      simp only [Complex.conj_im] at this
      linarith
    rw [Complex.mul_im, him, mul_zero, zero_add,
      show (((2 * j).factorial : ℂ))⁻¹ = ((((2 * j).factorial : ℝ))⁻¹ : ℝ) by push_cast; rfl,
      Complex.ofReal_im, zero_mul]

/-- The centre coefficient `a₀ = ξ(½)` is positive. -/
theorem evenTaylorRe_xi_half_zero_pos : 0 < evenTaylorRe (fun x => xi (1 / 2 + x)) 0 := by
  have : evenTaylorRe (fun x => xi (1 / 2 + x)) 0 = (xi ((1 / 2 : ℝ) : ℂ)).re := by
    simp [evenTaylorRe]
  rw [this]
  exact re_xi_half_pos

/-- The even-order reciprocal relation `Σ_k (−1)^k a_k β_{m−k} = [m = 0]`. -/
theorem sum_centre_mul_evenRecipCoeff_XiC (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), (-1 : ℝ) ^ k * evenTaylorRe (fun x => xi (1 / 2 + x)) k *
      evenRecipCoeff XiC (m - k) = if m = 0 then 1 else 0 := by
  have hXi0 : XiC 0 ≠ 0 := by
    have : XiC 0 = xi (((1 / 2 : ℝ)) : ℂ) := by simp [XiC]
    rw [this]
    exact xi_ne_zero_of_real _
  have han : AnalyticAt ℂ XiC 0 := XiC_differentiable.analyticAt 0
  have hinv : AnalyticAt ℂ (fun σ => (XiC σ)⁻¹) 0 := han.inv hXi0
  have hodd : ∀ k : ℕ, iteratedDeriv (2 * k + 1) XiC 0 = 0 :=
    iteratedDeriv_odd_eq_zero_of_even XiC_even
  -- `Ξ · (1/Ξ) = 1` near `0`
  have hev : (XiC * fun σ => (XiC σ)⁻¹) =ᶠ[nhds 0] fun _ => (1 : ℂ) := by
    filter_upwards [XiC_differentiable.continuous.continuousAt.eventually_ne hXi0] with σ hσ
    simp only [Pi.mul_apply]
    exact mul_inv_cancel₀ hσ
  have hL := factorial_inv_mul_iteratedDeriv_mul_even_of_analyticAt han hinv hodd m
  rw [hev.iteratedDeriv_eq (2 * m), iteratedDeriv_const] at hL
  have hE := factorial_inv_mul_iteratedDeriv_inv_XiC_even
  simp only [factorial_inv_mul_iteratedDeriv_XiC_even, hE] at hL
  have hre := congrArg Complex.re hL
  rw [Complex.re_sum] at hre
  simp only [← Complex.ofReal_mul, Complex.ofReal_re] at hre
  rw [← hre]
  by_cases hm : m = 0
  · subst hm
    simp
  · have h2m : 2 * m ≠ 0 := by omega
    rw [if_neg h2m, if_neg hm, mul_zero, Complex.zero_re]

/-- **`PF_k` of the centre coefficients gives `β_m ≥ 0` for `m ≤ k`.** -/
theorem evenRecipCoeff_XiC_nonneg_of_pfSeq {k : ℕ}
    (h : PFSeq k (evenTaylorRe (fun x => xi (1 / 2 + x)))) {m : ℕ} (hm : m ≤ k) :
    0 ≤ evenRecipCoeff XiC m := by
  exact hessenberg_reciprocal_nonneg h evenTaylorRe_xi_half_zero_pos sum_centre_mul_evenRecipCoeff_XiC hm

/-- **Unconditionally, the first 38 reciprocal centre coefficients are nonnegative.** -/
theorem evenRecipCoeff_XiC_nonneg_of_le_thirtySeven {m : ℕ} (hm : m ≤ 37) :
    0 ≤ evenRecipCoeff XiC m :=
  evenRecipCoeff_XiC_nonneg_of_pfSeq xi_centre_pfSeq_thirtySeven hm

end

end RHTower
