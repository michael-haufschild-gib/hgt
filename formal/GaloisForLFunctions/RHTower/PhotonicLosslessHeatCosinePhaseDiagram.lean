import GaloisForLFunctions.RHTower.PhotonicLosslessHeatFlowFiniteDefect
import GaloisForLFunctions.RHTower.DeBruijnNewmanStrictBound
import GaloisForLFunctions.RHTower.XiCosineShiftHeatStrip

/-!
# The lossless phase diagram of the heat–cosine family

For a super-exponentially decaying even kernel `g ≥ 0`, its transform `T g(z) = ∫ g(x) e^{izx} dx`
is a lossless product-port limit as soon as its zeros are real
(`isPtrProductPortLimit_cosTransform_of_zeros_real`). For the two-parameter family

  `A_{h,t}(z) = (H_t(z + ih) + H_t(z − ih))/2`,   the transform of `Φ(x) cosh(hx) e^{tx²}`,

this gives:

* `isPtrProductPortLimit_riemannHeat_of_newmanConstant_lt`: `H_t` is lossless for every
  `t > Λ`, and `Λ < 1/8` (Ki–Kim–Lee). So the lossless region of the heat axis reaches strictly
  past de Bruijn's bound (`exists_isPtrProductPortLimit_riemannHeat_below_eighth`).
* `isPtrProductPortLimit_cosineShift_heat`: `A_{h,t}` is lossless whenever `h, t > 0` and
  `1/4 ≤ h² + 2t`.
* `riemannHypothesis_iff_forall_isPtrProductPortLimit_heatCosine`: RH holds iff `A_{h,t}` is
  lossless on the whole closed quadrant minus the origin.
-/

open Complex Filter Topology Set Metric

namespace RHTower

noncomputable section

/-- **Lossless transforms.** A super-exponential kernel whose transform has only real zeros has a
lossless product-port transform. -/
theorem isPtrProductPortLimit_cosTransform_of_zeros_real {g : ℝ → ℝ} (hg : DeBruijn.SuperExpKernel g)
    (hreal : ∀ z, DeBruijn.cosTransform g z = 0 → z.im = 0) :
    IsPtrProductPortLimit (DeBruijn.cosTransform g) := by
  obtain ⟨C, hC0, hC⟩ := hg.exists_envelope
  exact isPtrProductPortLimit_of_even_realZeros hC0
    (hg.differentiable.differentiableOn.analyticOnNhd isOpen_univ) hg.cosTransform_zero_ne
    hg.cosTransform_neg hC hreal

/-- `H_t` is lossless for every `t` above the de Bruijn–Newman constant. -/
theorem isPtrProductPortLimit_riemannHeat_of_newmanConstant_lt {t : ℝ}
    (ht : DeBruijn.newmanConstant < t) : IsPtrProductPortLimit (DeBruijn.riemannHeat t) := by
  obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt DeBruijn.realRootedTimes_nonempty ht
  have hmem := DeBruijn.realRootedTimes_upper hs hst.le
  exact isPtrProductPortLimit_cosTransform_of_zeros_real
    (DeBruijn.riemannKernel_superExp.mul_exp_sq hmem.1) hmem.2

/-- The lossless region of the heat axis reaches strictly past de Bruijn's bound `1/8`. -/
theorem exists_isPtrProductPortLimit_riemannHeat_below_eighth :
    ∃ t₀ : ℝ, t₀ < 1 / 8 ∧ ∀ t : ℝ, t₀ < t → IsPtrProductPortLimit (DeBruijn.riemannHeat t) :=
  ⟨DeBruijn.newmanConstant, DeBruijn.newmanConstant_lt_eighth,
    fun _ ht => isPtrProductPortLimit_riemannHeat_of_newmanConstant_lt ht⟩

/-- The heat–cosine family is the transform of `Φ(x) cosh(hx) e^{tx²}`. -/
theorem heatCosine_eq_cosTransform (h t : ℝ) (ht : 0 ≤ t) :
    (fun z => (DeBruijn.riemannHeat t (z + h * I) + DeBruijn.riemannHeat t (z - h * I)) / 2) =
      DeBruijn.cosTransform
        (fun x => riemannKernelReal x * Real.cosh (h * x) * Real.exp (t * x ^ 2)) :=
  funext fun z => (DeBruijn.cosTransform_heat_cosh h t ht z).symm

/-- `A_{h,t}` is lossless whenever `h, t > 0` and `1/4 ≤ h² + 2t`. -/
theorem isPtrProductPortLimit_cosineShift_heat {h t : ℝ} (hh : 0 < h) (ht : 0 < t)
    (hht : 1 / 4 - h ^ 2 ≤ 2 * t) :
    IsPtrProductPortLimit
      (fun z => (DeBruijn.riemannHeat t (z + h * I) + DeBruijn.riemannHeat t (z - h * I)) / 2) := by
  rw [heatCosine_eq_cosTransform h t ht.le]
  refine isPtrProductPortLimit_cosTransform_of_zeros_real
    ((DeBruijn.riemannKernel_mul_cosh_superExp h).mul_exp_sq ht.le) fun z hz => ?_
  rw [← heatCosine_eq_cosTransform h t ht.le] at hz
  exact DeBruijn.cosineShift_heat_zeros_real hh ht hht hz

/-- **The lossless phase diagram is RH.** RH holds iff `A_{h,t}` is a lossless product-port limit
for all `h, t ≥ 0` other than `h = t = 0`. -/
theorem riemannHypothesis_iff_forall_isPtrProductPortLimit_heatCosine :
    RiemannHypothesis ↔ ∀ h t : ℝ, 0 ≤ h → 0 ≤ t → (0 < h ∨ 0 < t) →
      IsPtrProductPortLimit
        (fun z => (DeBruijn.riemannHeat t (z + h * I) + DeBruijn.riemannHeat t (z - h * I)) / 2) := by
  constructor
  · intro hRH h t hh ht hpos
    have hreal0 := DeBruijn.riemannHypothesis_iff_riemannHeat_zero_real.mp hRH
    -- zeros of the heat transform at time `t` are real
    have hzeros0 : ∀ w, DeBruijn.cosTransform riemannKernelReal w = 0 → w.im ^ 2 ≤ 0 := by
      intro w hw
      rw [DeBruijn.cosTransform_riemannKernel, ← DeBruijn.riemannHeat_zero] at hw
      rw [hreal0 w hw]; norm_num
    have hzerost : ∀ w, DeBruijn.cosTransform
        (fun x => riemannKernelReal x * Real.exp (t * x ^ 2)) w = 0 → w.im ^ 2 ≤ 0 := by
      intro w hw
      rcases ht.eq_or_lt with h0 | htpos
      · subst h0
        have : (fun x => riemannKernelReal x * Real.exp (0 * x ^ 2)) = riemannKernelReal := by
          funext x; simp
        rw [this] at hw
        exact hzeros0 w hw
      · rw [DeBruijn.cosTransform_heat_zeros_real DeBruijn.riemannKernel_superExp hzeros0
          (by linarith) htpos w hw]
        norm_num
    have hkt := DeBruijn.riemannKernel_superExp.mul_exp_sq ht
    have hfun : (fun x => riemannKernelReal x * Real.cosh (h * x) * Real.exp (t * x ^ 2)) =
        fun x => riemannKernelReal x * Real.exp (t * x ^ 2) * Real.cosh (h * x) := by
      funext x; ring
    rw [heatCosine_eq_cosTransform h t ht, hfun]
    rcases hh.eq_or_lt with h0 | hhpos
    · subst h0
      have hc : (fun x => riemannKernelReal x * Real.exp (t * x ^ 2) * Real.cosh (0 * x)) =
          fun x => riemannKernelReal x * Real.exp (t * x ^ 2) := by
        funext x; simp
      rw [hc]
      refine isPtrProductPortLimit_cosTransform_of_zeros_real hkt fun z hz => ?_
      have := hzerost z hz
      exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (le_antisymm this (sq_nonneg _))
    · refine isPtrProductPortLimit_cosTransform_of_zeros_real
        (by simpa using hkt.mul_cosh_pow h 1) fun z hz => ?_
      have h1 := hkt.zeros_mul_cosh le_rfl hzerost hhpos z hz
      have h2 : max (0 - h ^ 2) 0 = 0 := max_eq_right (by nlinarith)
      rw [h2] at h1
      exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (le_antisymm h1 (sq_nonneg _))
  · intro hall
    refine riemannHypothesis_iff_forall_isPtrProductPortLimit_riemannHeat.mpr fun t ht => ?_
    have := hall 0 t le_rfl ht.le (Or.inr ht)
    simpa using this

end

end RHTower
