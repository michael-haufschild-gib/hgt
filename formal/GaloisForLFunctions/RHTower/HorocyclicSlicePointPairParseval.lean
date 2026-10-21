import GaloisForLFunctions.RHTower.HorocyclicFibreKontorovichLebedevPositivity

/-!
# Parseval along two horocycles

For `y, y' > 0` the point-pair kernel restricted to the horocycles `Im z = y`, `Im w = y'` is the
convolution kernel `κ(x − x')`, `κ(t) = k(u(t + iy, iy'))`, and its Fourier transform is the fibre
kernel `K_ξ(y, y')`.  Fourier inversion of the second slice and two applications of Fubini give
(`integral_integral_pairKernel_slices`)

`∫∫ k(u(x + iy, x' + iy')) a(x) b̄(x') dx dx' = ∫ K_ξ(y, y') â(ξ) b̂(ξ)‾ dξ`

for continuous compactly supported `a` and smooth compactly supported `b`.
-/

open Complex MeasureTheory Set Filter Topology FourierTransform
open scoped ComplexConjugate Real ContDiff

noncomputable section

namespace GaloisForLFunctions.RHTower.MehlerFock

/-! ### The horocyclic phase as the Fourier character -/

/-- `𝓕f(ξ) = ∫ e^{−2πiξx} f(x) dx`. -/
theorem fourier_eq_integral_horocyclicPhase (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 f ξ = ∫ x, horocyclicPhase ξ x * f x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, horocyclicPhase]
  congr 2
  push_cast
  ring

theorem horocyclicPhase_sub (ξ x t : ℝ) :
    horocyclicPhase ξ (x - t) = horocyclicPhase ξ x * horocyclicPhase ξ (-t) := by
  simp only [horocyclicPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem continuous_horocyclicPhase_uncurry :
    Continuous fun p : ℝ × ℝ => horocyclicPhase p.1 p.2 := by
  unfold horocyclicPhase; fun_prop

/-- Fourier inversion in the horocyclic phase: `∫ e_ξ(x) 𝓕f(ξ)‾ dξ = f(x)‾`. -/
theorem integral_horocyclicPhase_mul_conj_fourier {f : ℝ → ℂ} (hf : Continuous f)
    (hfi : Integrable f) (hFi : Integrable (𝓕 f)) (x : ℝ) :
    ∫ ξ, horocyclicPhase ξ x * conj (𝓕 f ξ) = conj (f x) := by
  have h := congrFun (hf.fourierInv_fourier_eq hfi hFi) x
  rw [Real.fourierInv_eq'] at h
  rw [← h, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul, map_mul, horocyclicPhase, ← Complex.exp_conj]
  congr 2
  simp only [Complex.conj_ofReal, Complex.conj_I, RCLike.inner_apply, conj_trivial]
  push_cast
  ring

/-- `(ξ, y, y') ↦ K_ξ(y, y')` is measurable. -/
theorem measurable_horocyclicFibreKernel_uncurry {k : ℝ → ℝ} (hkc : Continuous k) :
    Measurable fun q : ℝ × ℝ × ℝ => horocyclicFibreKernel k q.1 q.2.1 q.2.2 := by
  have hp : Measurable fun p : (ℝ × ℝ × ℝ) × ℝ => pairUCoord p.2 p.1.2.1 0 p.1.2.2 := by
    unfold pairUCoord; fun_prop
  have h : StronglyMeasurable fun p : (ℝ × ℝ × ℝ) × ℝ =>
      (k (pairUCoord p.2 p.1.2.1 0 p.1.2.2) : ℂ) * horocyclicPhase p.1.1 p.2 :=
    ((Complex.measurable_ofReal.comp (hkc.measurable.comp hp)).mul
      (continuous_horocyclicPhase_uncurry.measurable.comp
        (measurable_fst.fst.prodMk measurable_snd))).stronglyMeasurable
  exact h.integral_prod_right'.measurable

/-- `ξ ↦ K_ξ(y, y')` is measurable. -/
theorem measurable_horocyclicFibreKernel_freq {k : ℝ → ℝ} (hkc : Continuous k) (y y' : ℝ) :
    Measurable fun ξ => horocyclicFibreKernel k ξ y y' := by
  have hp : Measurable fun p : ℝ × ℝ => pairUCoord p.2 y 0 y' := by unfold pairUCoord; fun_prop
  have h : StronglyMeasurable fun p : ℝ × ℝ =>
      (k (pairUCoord p.2 y 0 y') : ℂ) * horocyclicPhase p.1 p.2 :=
    ((Complex.measurable_ofReal.comp (hkc.measurable.comp hp)).mul
      continuous_horocyclicPhase_uncurry.measurable).stronglyMeasurable
  exact h.integral_prod_right'.measurable

theorem pairUCoord_eq_sub (x y x' y' : ℝ) : pairUCoord x y x' y' = pairUCoord (x - x') y 0 y' := by
  simp [pairUCoord]

theorem pairUCoord_neg (t y y' : ℝ) : pairUCoord (-t) y 0 y' = pairUCoord t y 0 y' := by
  simp [pairUCoord]

/-! ### Parseval -/

section Slices

variable {k : ℝ → ℝ} {R : ℝ} (hkc : Continuous k) (hkR : DeckPointPair.KernelSupport k R)
include hkc hkR

/-- The slice kernel `κ(t) = k(u(t + iy, iy'))` is integrable. -/
theorem integrable_pairKernel_slice {y y' : ℝ} (hy : 0 < y) (hy' : 0 < y') :
    Integrable fun t : ℝ => (k (pairUCoord t y 0 y') : ℂ) := by
  set L := 2 * Real.sqrt (max R 0 * (y * y'))
  refine (by unfold pairUCoord; fun_prop : Continuous fun t : ℝ =>
    (k (pairUCoord t y 0 y') : ℂ)).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_Icc (a := -L) (b := L)) fun t ht => ?_)
  have hL0 : 0 ≤ L := by positivity
  have hlt : L < |t| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  simp [pairKernel_slice_eq_zero hkR hy hy' hlt]

omit hkc hkR in
/-- Convolving the slice kernel against a phase: `∫ κ(x − x') e_ξ(x') dx' = e_ξ(x) K_ξ(y, y')`. -/
theorem integral_pairKernel_slice_mul_horocyclicPhase (y y' x ξ : ℝ) :
    ∫ x', (k (pairUCoord (x - x') y 0 y') : ℂ) * horocyclicPhase ξ x' =
      horocyclicPhase ξ x * horocyclicFibreKernel k ξ y y' := by
  have h1 := integral_sub_left_eq_self
    (fun t => (k (pairUCoord t y 0 y') : ℂ) * horocyclicPhase ξ (x - t)) volume x
  simp only [sub_sub_cancel] at h1
  have h2 := integral_neg_eq_self
    (fun t => (k (pairUCoord t y 0 y') : ℂ) * horocyclicPhase ξ (-t)) volume
  simp only [neg_neg, pairUCoord_neg] at h2
  rw [h1, horocyclicFibreKernel, h2, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [horocyclicPhase_sub]
  ring

/-- **Parseval along two horocycles.**  For `y, y' > 0`, continuous compactly supported `a` and
smooth compactly supported `b`,
`∫∫ k(u(x + iy, x' + iy')) a(x) b̄(x') = ∫ K_ξ(y, y') â(ξ) b̂(ξ)‾ dξ`. -/
theorem integral_integral_pairKernel_slices {a b : ℝ → ℂ} (ha : Continuous a)
    (hac : HasCompactSupport a) (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b) {y y' : ℝ}
    (hy : 0 < y) (hy' : 0 < y') :
    ∫ x, ∫ x', (k (pairUCoord x y x' y') : ℂ) * a x * conj (b x') =
      ∫ ξ, horocyclicFibreKernel k ξ y y' * 𝓕 a ξ * conj (𝓕 b ξ) := by
  have hκi := integrable_pairKernel_slice hkc hkR hy hy'
  have hκc : Continuous fun t : ℝ => (k (pairUCoord t y 0 y') : ℂ) := by
    unfold pairUCoord; fun_prop
  obtain ⟨S, hS⟩ : ∃ S : SchwartzMap ℝ ℂ, ⇑S = b := ⟨hbc.toSchwartzMap hb, rfl⟩
  have hbF : 𝓕 b = ⇑(𝓕 S : SchwartzMap ℝ ℂ) := by rw [← hS, SchwartzMap.fourier_coe]
  have hbFi : Integrable (𝓕 b) := by rw [hbF]; exact (𝓕 S : SchwartzMap ℝ ℂ).integrable
  have hbFc : Continuous (𝓕 b) := by rw [hbF]; exact (𝓕 S : SchwartzMap ℝ ℂ).continuous
  have hbi : Integrable b := hb.continuous.integrable_of_hasCompactSupport hbc
  have hai : Integrable a := ha.integrable_of_hasCompactSupport hac
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_of_kernelSupport hkc hkR
  have hK : ∀ ξ, ‖horocyclicFibreKernel k ξ y y'‖ ≤ 4 * Real.sqrt (max R 0 * (y * y')) * M :=
    fun _ => norm_horocyclicFibreKernel_le hkR hM hy hy'
  have hKm := measurable_horocyclicFibreKernel_freq hkc y y'
  -- inner integral: expand `b̄` by Fourier inversion and integrate the slice kernel first
  have hstep : ∀ x, ∫ x', (k (pairUCoord x y x' y') : ℂ) * a x * conj (b x') =
      a x * ∫ ξ, horocyclicPhase ξ x * horocyclicFibreKernel k ξ y y' * conj (𝓕 b ξ) := by
    intro x
    have hF : Integrable (Function.uncurry fun x' ξ => (k (pairUCoord (x - x') y 0 y') : ℂ) *
        horocyclicPhase ξ x' * conj (𝓕 b ξ)) (volume.prod volume) := by
      refine (Integrable.mul_prod (hκi.comp_sub_left x).norm hbFi.norm).mono' ?_
        (Eventually.of_forall fun p => ?_)
      · exact (((hκc.comp (continuous_const.sub continuous_fst)).mul
          (continuous_horocyclicPhase_uncurry.comp continuous_swap)).mul
          (Complex.continuous_conj.comp (hbFc.comp continuous_snd))).aestronglyMeasurable
      · simp only [Function.uncurry, norm_mul, norm_horocyclicPhase, mul_one,
          Complex.norm_conj, le_refl]
    calc ∫ x', (k (pairUCoord x y x' y') : ℂ) * a x * conj (b x')
        = a x * ∫ x', ∫ ξ, (k (pairUCoord (x - x') y 0 y') : ℂ) * horocyclicPhase ξ x' *
            conj (𝓕 b ξ) := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall fun x' => ?_)
          dsimp only
          rw [← integral_horocyclicPhase_mul_conj_fourier hb.continuous hbi hbFi x',
            ← integral_const_mul, ← integral_const_mul, pairUCoord_eq_sub]
          refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
          ring
      _ = a x * ∫ ξ, ∫ x', (k (pairUCoord (x - x') y 0 y') : ℂ) * horocyclicPhase ξ x' *
            conj (𝓕 b ξ) := by rw [integral_integral_swap hF]
      _ = a x * ∫ ξ, horocyclicPhase ξ x * horocyclicFibreKernel k ξ y y' * conj (𝓕 b ξ) := by
          congr 1
          refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
          dsimp only
          rw [integral_mul_const, integral_pairKernel_slice_mul_horocyclicPhase]
  -- outer integral: integrate `a` against the phase
  have hG : Integrable (Function.uncurry fun x ξ => a x *
      (horocyclicPhase ξ x * horocyclicFibreKernel k ξ y y' * conj (𝓕 b ξ)))
      (volume.prod volume) := by
    refine (Integrable.mul_prod hai.norm (hbFi.norm.const_mul (4 * Real.sqrt (max R 0 * (y * y')) * M))).mono' ?_
      (Eventually.of_forall fun p => ?_)
    · exact ((ha.measurable.comp measurable_fst).mul
        (((continuous_horocyclicPhase_uncurry.comp continuous_swap).measurable.mul
          (hKm.comp measurable_snd)).mul
          ((Complex.continuous_conj.comp (hbFc.comp continuous_snd)).measurable))).aestronglyMeasurable
    · simp only [Function.uncurry, norm_mul, norm_horocyclicPhase, one_mul,
        Complex.norm_conj]
      gcongr
      exact hK p.2
  rw [integral_congr_ae (Eventually.of_forall hstep)]
  simp_rw [← integral_const_mul (a _)]
  rw [integral_integral_swap hG]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [fourier_eq_integral_horocyclicPhase a ξ, ← integral_const_mul, ← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  ring

end Slices

end GaloisForLFunctions.RHTower.MehlerFock
