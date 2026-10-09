import GaloisForLFunctions.RHTower.RiemannKernelStripFirstOrderEnergy
import GaloisForLFunctions.RHTower.RiemannKernelStripFirstOrderPreimage
import GaloisForLFunctions.RHTower.XiExponentialMeanSquareThetaBound
import GaloisForLFunctions.RHTower.XiDyadicFourthMoment

/-!
# No first-order Laguerre–Pólya preimage of `Ξ`

For `a ≠ 0` there is no Laguerre–Pólya `f` with `f − f′/a = Ξ`
(`not_exists_laguerrePolya_firstOrder_preimage_XiC`).  The proof combines the fourth-moment form
`not_exists_laguerrePolya_firstOrder_preimage_XiC_of_fourthMoment` with the dyadic fourth moment
`∫_X^{2X} e^{πy} Ξ(y)⁴ dy ≲ X⁸ log⁴ X` (`exists_integral_exp_mul_Xi_pow_four_le`).

* `a > 0`.  RH holds and `ψ = Re f` has zeros in every window `[x − 1, x]` and in every window
  containing two zeros of `ξ` (`riemannHypothesis_and_zero_data_of_firstOrder_preimage`).  Zeros
  far to the right identify `ψ` with `kernelPsi (lorentzOne a)`
  (`ofReal_eq_kernelPsi_lorentzOne_of_ode`).  The large-gap tail under RH
  (`riemannHypothesis_measureReal_zeroGap_le`), the second moment from the theta boundary
  (`exists_integral_exp_mul_norm_sq_XiC_le`) and the fourth moment feed the two-radius energy
  contradiction `false_of_firstOrder_data`.
* `a < 0`.  `z ↦ f(−z)` is Laguerre–Pólya and solves `g − g′/(−a) = Ξ`, since `Ξ` is even.

**Every real-rooted polynomial symbol.**  For nonzero reals `c₁, …, c_n` (`n ≥ 1`, any signs) there
is no Laguerre–Pólya `ψ` with `(1 − c₁D)⋯(1 − c_nD)ψ = Ξ`
(`not_exists_laguerrePolya_polynomial_preimage_XiC`).  The inner factors map `ψ` into the
Laguerre–Pólya class (`laguerrePolya_sub_smul_deriv`), so the outer factor is a first-order preimage.
-/

open Complex MeasureTheory Filter Topology Set Polynomial
open scoped Real
open GaloisForLFunctions.HTGeometry Zeta23

noncomputable section

namespace RHTower.KernelStrip

/-- The Laguerre–Pólya class is invariant under `z ↦ −z`. -/
theorem laguerrePolya_comp_neg {f : ℂ → ℂ} (hf : GaloisForLFunctions.HTGeometry.LaguerrePolya f) :
    GaloisForLFunctions.HTGeometry.LaguerrePolya fun z => f (-z) := by
  obtain ⟨p, hs, hconv⟩ := hf
  refine ⟨fun m => (p m).comp (-X), fun m => (hs m).comp_neg_X, ?_⟩
  have h := hconv.comp (fun z : ℂ => -z) continuous_neg
  refine h.congr fun m z => ?_
  simp [polyEvalC, aeval_comp]

/-- Reflection of a first-order preimage. -/
theorem firstOrder_preimage_comp_neg {a : ℝ} {f : ℂ → ℂ}
    (hode : ∀ z, f z - ((1 / a : ℝ) : ℂ) * deriv f z = XiC z) (z : ℂ) :
    f (-z) - ((1 / -a : ℝ) : ℂ) * deriv (fun w => f (-w)) z = XiC z := by
  rw [deriv_comp_neg, ← XiC_even, ← hode (-z)]
  push_cast
  ring

/-- The `a > 0` case. -/
theorem not_exists_laguerrePolya_firstOrder_preimage_XiC_pos_of_fourthMoment {a : ℝ} (ha : 0 < a)
    {C₄ : ℝ} (hC₄ : 0 ≤ C₄) (h4 : ∀ X ≥ 2,
      ∫ y in X..2 * X, Real.exp (π * y) * Xi y ^ 4 ≤ C₄ * X ^ (8 : ℝ) * Real.log X ^ 4) :
    ¬ ∃ f : ℂ → ℂ, GaloisForLFunctions.HTGeometry.LaguerrePolya f ∧ ∀ z, f z - ((1 / a : ℝ) : ℂ) * deriv f z = XiC z := by
  rintro ⟨f, hf, hode⟩
  obtain ⟨hRH, -, hder, x₀, hlong, hshort⟩ :=
    Littlewood.riemannHypothesis_and_zero_data_of_firstOrder_preimage ha.ne' hf hode
  have hzero : ∀ T, ∃ x > T, (fun x : ℝ => (f x).re) x = 0 := fun T => by
    obtain ⟨q, hq, hq0⟩ := hlong (max T x₀ + 2) (by linarith [le_max_right T x₀])
    exact ⟨q, by linarith [hq.1, le_max_left T x₀], hq0⟩
  have hF : ∀ x : ℝ, ((Xi x : ℝ) : ℂ) = paperFT riemannPhiKernel x := fun x => by
    rw [← XiC_ofReal, Littlewood.paperFT_riemannPhiKernel_eq_XiC]
  have hψk := ofReal_eq_kernelPsi_lorentzOne_of_ode ha hder hF hzero
  obtain ⟨C, T₀, hC, hLGT⟩ := Littlewood.riemannHypothesis_measureReal_zeroGap_le hRH 24
  obtain ⟨C₂, hC₂, h2⟩ := exists_integral_exp_mul_norm_sq_XiC_le
  have h2' : ∀ X ≥ 2, ∫ y in X..2 * X, Real.exp (π / 2 * y) * Xi y ^ 2 ≤
      C₂ * X ^ (9 / 2 : ℝ) * Real.log X := fun X hX => by
    have e : (fun y : ℝ => Real.exp (π / 2 * y) * Xi y ^ 2) =
        fun y : ℝ => Real.exp (π / 2 * y) * ‖XiC (y : ℂ)‖ ^ 2 := by
      funext y; rw [XiC_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [e]; exact h2 X hX
  exact false_of_firstOrder_data ha (fun _ _ h => xiZeroCount_mono h) Littlewood.continuous_Xi
    hder hψk hlong hshort hC hLGT hC₂ h2' hC₄ h4

/-- **No first-order Laguerre–Pólya preimage of `Ξ`, given the fourth moment.** -/
theorem not_exists_laguerrePolya_firstOrder_preimage_XiC_of_fourthMoment {a : ℝ} (ha : a ≠ 0)
    {C₄ : ℝ} (hC₄ : 0 ≤ C₄) (h4 : ∀ X ≥ 2,
      ∫ y in X..2 * X, Real.exp (π * y) * Xi y ^ 4 ≤ C₄ * X ^ (8 : ℝ) * Real.log X ^ 4) :
    ¬ ∃ f : ℂ → ℂ, GaloisForLFunctions.HTGeometry.LaguerrePolya f ∧ ∀ z, f z - ((1 / a : ℝ) : ℂ) * deriv f z = XiC z := by
  rcases ha.lt_or_gt with hneg | hpos
  · rintro ⟨f, hf, hode⟩
    exact not_exists_laguerrePolya_firstOrder_preimage_XiC_pos_of_fourthMoment (neg_pos.mpr hneg)
      hC₄ h4 ⟨fun z => f (-z), laguerrePolya_comp_neg hf, firstOrder_preimage_comp_neg hode⟩
  · exact not_exists_laguerrePolya_firstOrder_preimage_XiC_pos_of_fourthMoment hpos hC₄ h4

/-- **No first-order Laguerre–Pólya preimage of `Ξ`.**  For every real `a ≠ 0` there is no
Laguerre–Pólya `f` with `f − f′/a = Ξ`. -/
theorem not_exists_laguerrePolya_firstOrder_preimage_XiC {a : ℝ} (ha : a ≠ 0) :
    ¬ ∃ f : ℂ → ℂ, GaloisForLFunctions.HTGeometry.LaguerrePolya f ∧
      ∀ z, f z - ((1 / a : ℝ) : ℂ) * deriv f z = XiC z := by
  obtain ⟨C₄, hC₄, h4⟩ := exists_integral_exp_mul_Xi_pow_four_le
  exact not_exists_laguerrePolya_firstOrder_preimage_XiC_of_fourthMoment ha hC₄ h4

/-- `(1 − c₁D)⋯(1 − c_nD)F`. -/
def firstOrderChain : List ℝ → (ℂ → ℂ) → ℂ → ℂ
  | [], F => F
  | c :: cs, F => fun z => firstOrderChain cs F z - (c : ℂ) * deriv (firstOrderChain cs F) z

theorem laguerrePolya_firstOrderChain (cs : List ℝ) {F : ℂ → ℂ}
    (hF : GaloisForLFunctions.HTGeometry.LaguerrePolya F) :
    GaloisForLFunctions.HTGeometry.LaguerrePolya (firstOrderChain cs F) := by
  induction cs with
  | nil => exact hF
  | cons c cs ih => exact laguerrePolya_sub_smul_deriv ih c

/-- **LP-maximality of `Ξ` for real-rooted polynomial symbols.**  For nonzero reals
`c₁, …, c_n`, `n ≥ 1`, of any signs, there is no Laguerre–Pólya `ψ` with
`(1 − c₁D)⋯(1 − c_nD)ψ = Ξ`. -/
theorem not_exists_laguerrePolya_polynomial_preimage_XiC {cs : List ℝ} (hne : cs ≠ [])
    (hcs : ∀ c ∈ cs, c ≠ 0) :
    ¬ ∃ ψ : ℂ → ℂ, GaloisForLFunctions.HTGeometry.LaguerrePolya ψ ∧
      firstOrderChain cs ψ = XiC := by
  rintro ⟨ψ, hψ, heq⟩
  obtain ⟨c, cs', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hc : c ≠ 0 := hcs c List.mem_cons_self
  refine not_exists_laguerrePolya_firstOrder_preimage_XiC (a := 1 / c) (one_div_ne_zero hc)
    ⟨firstOrderChain cs' ψ, laguerrePolya_firstOrderChain cs' hψ, fun z => ?_⟩
  rw [one_div_one_div, ← heq]
  rfl

end RHTower.KernelStrip
