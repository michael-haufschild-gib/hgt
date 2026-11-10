import GaloisForLFunctions.HTGeometry.DecayingStripVerticalShift
import Mathlib

/-!
# Continuation from a common signal

The analytic step that turns two estimates for one sum into a zero-free half-plane.

A **kernel** `G` is holomorphic on `Re s > 1` and decays like `C/(1+t²)` uniformly on every strip
`2 ≤ Re s ≤ B`. Its **signal** is `f(Z) = (1/2π) ∫ G(2+it) Z^{2+it} dt`.

* **The signal is small at zero** (`norm_signal_two_le`): `|f(Z)| ≤ (C_B/2) Z^B` for every
  `B ≥ 2`, by moving the line to `Re s = B`.
* **The Mellin transform of the signal is the kernel** (`mellin_signal_eq`): on the line
  `Re w = −2` the Mellin transform of `f` is `G(−w)`, by Fourier inversion.
* **Continuation** (`exists_differentiableOn_eq_of_signal_le`): if `|f(Z)| ≤ K Z^b` for large `Z`,
  with `b < 2`, then `G` extends holomorphically to `Re s > b`.
* **Zeros** (`ne_zero_of_signal_le`): if moreover `G L = E` on `Re s > 1` with `L, E` holomorphic
  on `Re s > b`, `E` without zeros there and `b < 1`, then `L` has no zero in `Re s > b`.
* **Two estimates** (`ne_zero_of_common_signal`): a sum `J` with `|J(Z)| ≤ K Z^{a₁}` and
  `|J(Z) − f(Z)| ≤ K Z^{a₂}` for large `Z` gives the half-plane `Re s > max a₁ a₂`.

In the application `L` is an `L`-function of a family, `E` a zero-free factor, the first bound is a
direct estimate of a completed sum, and the second compares it with the signal up to the scale
of the rightmost zeros of the family: the half-plane of every member improves at once.
-/

noncomputable section

open Complex MeasureTheory Filter Set Topology Asymptotics
open scoped FourierTransform

namespace GaloisForLFunctions.FamilyContinuationTheory

/-- A kernel: holomorphic on `Re s > 1`, with the decay `C/(1+t²)` on each strip
`2 ≤ Re s ≤ B`. -/
structure IsSignalKernel (G : ℂ → ℂ) : Prop where
  differentiableAt : ∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ G s
  decay : ∀ B : ℝ, ∃ C : ℝ, ∀ s : ℂ, 2 ≤ s.re → s.re ≤ B → ‖G s‖ ≤ C / (1 + s.im ^ 2)

/-- The signal of `G` read on the line `Re s = c`: `(1/2π) ∫ G(c+it) Z^{c+it} dt`, written as the
inverse Mellin transform of `w ↦ G(−w)` on the line `Re w = −c`. -/
def signal (G : ℂ → ℂ) (c : ℝ) : ℝ → ℂ := mellinInv (-c) fun w => G (-w)

/-- On the strip `2 ≤ t ≤ B` a power of a positive number is at most the larger endpoint
power. -/
theorem rpow_le_max_of_mem {Z t B : ℝ} (hZ : 0 < Z) (h2 : 2 ≤ t) (hB : t ≤ B) :
    Z ^ t ≤ max (Z ^ (2 : ℝ)) (Z ^ B) := by
  rcases le_total 1 Z with h | h
  · exact le_max_of_le_right (Real.rpow_le_rpow_of_exponent_le h hB)
  · exact le_max_of_le_left (Real.rpow_le_rpow_of_exponent_ge hZ h h2)

/-- **The line can be moved to the right.** -/
theorem signal_two_eq {G : ℂ → ℂ} (hG : IsSignalKernel G) {B : ℝ} (hB : 2 ≤ B) {Z : ℝ}
    (hZ : 0 < Z) : signal G 2 Z = signal G B Z := by
  obtain ⟨C, hC⟩ := hG.decay B
  have hmem : ∀ s : ℂ, s.re ∈ uIcc (-2 : ℝ) (-B) → 2 ≤ (-s).re ∧ (-s).re ≤ B := by
    intro s hs
    rw [Set.uIcc_of_ge (by linarith : -B ≤ (-2 : ℝ))] at hs
    rw [neg_re]
    exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  unfold signal
  rw [mellinInv, mellinInv]
  congr 1
  refine HTGeometry.integral_vertical_line_shift_of_decay
    (Φ := fun w : ℂ => (Z : ℂ) ^ (-w) • G (-w)) (C := max (Z ^ (2 : ℝ)) (Z ^ B) * C) ?_ ?_
  · intro s hs
    have hneg : DifferentiableAt ℂ (fun w : ℂ => -w) s := differentiableAt_id.neg
    exact (hneg.const_cpow (Or.inl (ofReal_ne_zero.mpr hZ.ne'))).smul
      ((hG.differentiableAt (-s) (by linarith [(hmem s hs).1])).comp s hneg)
  · intro s hs
    obtain ⟨h2, hBs⟩ := hmem s hs
    have hGs := hC (-s) h2 hBs
    rw [neg_im, neg_sq] at hGs
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hZ, mul_div_assoc]
    exact mul_le_mul (rpow_le_max_of_mem hZ h2 hBs) hGs (norm_nonneg _)
      (le_max_of_le_left (Real.rpow_nonneg hZ.le _))

/-- The signal on the line `Re s = B` is at most `(C/2) Z^B`, `C` the decay constant of the
line. -/
theorem norm_signal_le {G : ℂ → ℂ} {B C : ℝ}
    (hC : ∀ s : ℂ, s.re = B → ‖G s‖ ≤ C / (1 + s.im ^ 2)) {Z : ℝ} (hZ : 0 < Z) :
    ‖signal G B Z‖ ≤ C / 2 * Z ^ B := by
  have hbound : ∀ y : ℝ,
      ‖(Z : ℂ) ^ (-(((-B : ℝ) : ℂ) + y * I)) • G (-(((-B : ℝ) : ℂ) + y * I))‖ ≤
        Z ^ B * (C * (1 + y ^ 2)⁻¹) := by
    intro y
    have hre : (-(((-B : ℝ) : ℂ) + y * I)).re = B := by simp
    have him : (-(((-B : ℝ) : ℂ) + y * I)).im = -y := by simp
    have h := hC _ hre
    rw [him, neg_sq, div_eq_mul_inv] at h
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hZ, hre]
    exact mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hZ.le B)
  have hint : Integrable fun y : ℝ => Z ^ B * (C * (1 + y ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.const_mul C).const_mul _
  have h := norm_integral_le_of_norm_le hint (Eventually.of_forall hbound)
  rw [integral_const_mul, integral_const_mul, integral_univ_inv_one_add_sq] at h
  unfold signal
  rw [mellinInv, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc 1 / (2 * Real.pi) * ‖∫ y : ℝ, (Z : ℂ) ^ (-(((-B : ℝ) : ℂ) + y * I)) •
          G (-(((-B : ℝ) : ℂ) + y * I))‖
      ≤ 1 / (2 * Real.pi) * (Z ^ B * (C * Real.pi)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = C / 2 * Z ^ B := by
        field_simp

/-- **The signal is small at zero.** -/
theorem norm_signal_two_le {G : ℂ → ℂ} (hG : IsSignalKernel G) {B : ℝ} (hB : 2 ≤ B) :
    ∃ C : ℝ, ∀ Z : ℝ, 0 < Z → ‖signal G 2 Z‖ ≤ C / 2 * Z ^ B := by
  obtain ⟨C, hC⟩ := hG.decay B
  refine ⟨C, fun Z hZ => ?_⟩
  rw [signal_two_eq hG hB hZ]
  exact norm_signal_le (fun s hs => hC s (by rw [hs]; exact hB) hs.le) hZ

/-- The restriction of the kernel to the line `Re s = 2`, in the Fourier variable. -/
def lineKernel (G : ℂ → ℂ) (y : ℝ) : ℂ := G (-(((-2 : ℝ) : ℂ) + 2 * Real.pi * y * I))

theorem continuous_lineKernel {G : ℂ → ℂ} (hG : IsSignalKernel G) :
    Continuous (lineKernel G) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hre : (-(((-2 : ℝ) : ℂ) + 2 * Real.pi * y * I)).re = 2 := by simp
  exact ((hG.differentiableAt _ (by rw [hre]; norm_num)).continuousAt).comp (by fun_prop)

theorem integrable_lineKernel {G : ℂ → ℂ} (hG : IsSignalKernel G) :
    Integrable (lineKernel G) := by
  obtain ⟨C, hC⟩ := hG.decay 2
  have hdom : Integrable fun y : ℝ => |C| * (1 + y ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul _
  refine hdom.mono' (continuous_lineKernel hG).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have hre : (-(((-2 : ℝ) : ℂ) + 2 * Real.pi * y * I)).re = 2 := by simp
  have him : (-(((-2 : ℝ) : ℂ) + 2 * Real.pi * y * I)).im = -(2 * Real.pi * y) := by simp
  have h := hC _ hre.ge hre.le
  rw [him, neg_sq] at h
  have hy : (1 : ℝ) + y ^ 2 ≤ 1 + (2 * Real.pi * y) ^ 2 := by
    have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    nlinarith [sq_nonneg y, mul_nonneg (sq_nonneg y) (by nlinarith : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 - 1)]
  calc ‖lineKernel G y‖ ≤ C / (1 + (2 * Real.pi * y) ^ 2) := h
    _ ≤ |C| / (1 + (2 * Real.pi * y) ^ 2) := by gcongr; exact le_abs_self C
    _ ≤ |C| / (1 + y ^ 2) := by gcongr
    _ = |C| * (1 + y ^ 2)⁻¹ := div_eq_mul_inv _ _

/-- The inverse transform of the line kernel is the signal in the logarithmic variable. -/
theorem fourierInv_lineKernel (G : ℂ → ℂ) (u : ℝ) :
    𝓕⁻ (lineKernel G) u = Real.exp (2 * u) • signal G 2 (Real.exp (-u)) := by
  have h := mellinInv_eq_fourierInv (-2 : ℝ) (fun w => G (-w)) (Real.exp_pos (-u))
  rw [Real.log_exp, neg_neg] at h
  have hsig : signal G 2 (Real.exp (-u)) =
      (Real.exp (-u) : ℂ) ^ (-((-2 : ℝ) : ℂ)) • 𝓕⁻ (lineKernel G) u := h
  rw [hsig, ← smul_assoc]
  have hone : Real.exp (2 * u) • (Real.exp (-u) : ℂ) ^ (-((-2 : ℝ) : ℂ)) = 1 := by
    have h2 : (-((-2 : ℝ) : ℂ)) = ((2 : ℕ) : ℂ) := by push_cast; ring
    rw [h2, cpow_natCast, Complex.real_smul, ← ofReal_pow, ← ofReal_mul, ← Real.exp_nat_mul,
      ← Real.exp_add]
    norm_num
  rw [hone, one_smul]

/-- The signal is continuous on the positive reals. -/
theorem continuousOn_signal_two {G : ℂ → ℂ} (hG : IsSignalKernel G) :
    ContinuousOn (signal G 2) (Ioi 0) := by
  have hF : Continuous (𝓕⁻ (lineKernel G)) := by
    rw [Real.fourierInv_eq_fourier_comp_neg]
    have hint : Integrable fun y : ℝ => lineKernel G (-y) := (integrable_lineKernel hG).comp_neg
    exact VectorFourier.fourierIntegral_continuous (V := ℝ) (W := ℝ) (E := ℂ)
      (e := Real.fourierChar) (μ := volume) (L := innerₗ ℝ) Real.continuous_fourierChar
      (by fun_prop) hint
  have hrep : ∀ Z ∈ Ioi (0 : ℝ), signal G 2 Z =
      (Z : ℂ) ^ (-((-2 : ℝ) : ℂ)) • 𝓕⁻ (lineKernel G) (-Real.log Z) := fun Z hZ =>
    mellinInv_eq_fourierInv (-2 : ℝ) (fun w => G (-w)) hZ
  refine ContinuousOn.congr ?_ hrep
  refine ContinuousOn.smul (f := fun Z : ℝ => (Z : ℂ) ^ (-((-2 : ℝ) : ℂ)))
    (g := fun Z : ℝ => 𝓕⁻ (lineKernel G) (-Real.log Z)) ?_ ?_
  · intro Z hZ
    exact (continuousAt_ofReal_cpow_const Z _ (Or.inr (ne_of_gt hZ))).continuousWithinAt
  · exact hF.comp_continuousOn
      ((Real.continuousOn_log.mono fun Z hZ => ne_of_gt hZ).neg)

/-- The inverse transform of the line kernel is integrable when the signal is `O(Z^b)` at
infinity, `b < 2`. -/
theorem integrable_fourierInv_lineKernel {G : ℂ → ℂ} (hG : IsSignalKernel G) {b K Z₀ : ℝ}
    (hb : b < 2) (hZ₀ : 0 < Z₀) (hK : ∀ Z : ℝ, Z₀ ≤ Z → ‖signal G 2 Z‖ ≤ K * Z ^ b) :
    Integrable (𝓕⁻ (lineKernel G)) := by
  have hcont : Continuous (𝓕⁻ (lineKernel G)) := by
    rw [Real.fourierInv_eq_fourier_comp_neg]
    exact VectorFourier.fourierIntegral_continuous (V := ℝ) (W := ℝ) (E := ℂ)
      (e := Real.fourierChar) (μ := volume) (L := innerₗ ℝ) Real.continuous_fourierChar
      (by fun_prop) (integrable_lineKernel hG).comp_neg
  obtain ⟨C₂, hC₂⟩ := norm_signal_two_le hG (le_refl (2 : ℝ))
  obtain ⟨C₃, hC₃⟩ := norm_signal_two_le hG (by norm_num : (2 : ℝ) ≤ 3)
  -- the norm of the transform in terms of the signal
  have hnorm : ∀ u : ℝ, ‖𝓕⁻ (lineKernel G) u‖ =
      Real.exp (2 * u) * ‖signal G 2 (Real.exp (-u))‖ := by
    intro u
    rw [fourierInv_lineKernel, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  -- a bound valid everywhere
  have hall : ∀ u : ℝ, ‖𝓕⁻ (lineKernel G) u‖ ≤ |C₂| / 2 := by
    intro u
    rw [hnorm]
    have h := hC₂ (Real.exp (-u)) (Real.exp_pos _)
    have hexp : Real.exp (2 * u) * Real.exp (-u) ^ (2 : ℝ) = 1 := by
      rw [← Real.exp_mul, ← Real.exp_add]
      convert Real.exp_zero using 2
      ring
    calc Real.exp (2 * u) * ‖signal G 2 (Real.exp (-u))‖
        ≤ Real.exp (2 * u) * (C₂ / 2 * Real.exp (-u) ^ (2 : ℝ)) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = C₂ / 2 := by rw [mul_left_comm, hexp, mul_one]
      _ ≤ |C₂| / 2 := by gcongr; exact le_abs_self C₂
  -- decay to the right
  have hright : IntegrableOn (𝓕⁻ (lineKernel G)) (Ioi 0) := by
    have hdom : IntegrableOn (fun u : ℝ => |C₃| / 2 * Real.exp (-1 * u)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 one_pos).const_mul _
    refine hdom.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [hnorm]
    have h := hC₃ (Real.exp (-u)) (Real.exp_pos _)
    have hexp : Real.exp (2 * u) * Real.exp (-u) ^ (3 : ℝ) = Real.exp (-1 * u) := by
      rw [← Real.exp_mul, ← Real.exp_add]; ring_nf
    calc Real.exp (2 * u) * ‖signal G 2 (Real.exp (-u))‖
        ≤ Real.exp (2 * u) * (C₃ / 2 * Real.exp (-u) ^ (3 : ℝ)) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = C₃ / 2 * Real.exp (-1 * u) := by rw [mul_left_comm, hexp]
      _ ≤ |C₃| / 2 * Real.exp (-1 * u) := by gcongr; exact le_abs_self C₃
  -- decay to the left
  have hκ : 0 < 2 - b := by linarith
  set v₀ : ℝ := max (Real.log Z₀) 0 with hv₀
  set A : ℝ := max |K| (|C₂| / 2 * Real.exp ((2 - b) * v₀)) with hA
  have hleft : IntegrableOn (𝓕⁻ (lineKernel G)) (Iic 0) := by
    have hdom : IntegrableOn (fun u : ℝ => A * Real.exp ((2 - b) * u)) (Iic 0) :=
      (integrableOn_exp_mul_Iic hκ 0).const_mul _
    refine hdom.mono' hcont.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun u hu => ?_)
    have hu0 : u ≤ 0 := hu
    by_cases hcase : u ≤ -v₀
    · -- the signal bound at infinity
      have hZ : Z₀ ≤ Real.exp (-u) := by
        have : Real.log Z₀ ≤ -u := le_trans (le_max_left _ _) (by linarith)
        calc Z₀ = Real.exp (Real.log Z₀) := (Real.exp_log hZ₀).symm
          _ ≤ Real.exp (-u) := Real.exp_le_exp.mpr this
      have h := hK _ hZ
      rw [hnorm]
      have hexp : Real.exp (2 * u) * Real.exp (-u) ^ b = Real.exp ((2 - b) * u) := by
        rw [← Real.exp_mul, ← Real.exp_add]; ring_nf
      calc Real.exp (2 * u) * ‖signal G 2 (Real.exp (-u))‖
          ≤ Real.exp (2 * u) * (K * Real.exp (-u) ^ b) :=
            mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
        _ = K * Real.exp ((2 - b) * u) := by rw [mul_left_comm, hexp]
        _ ≤ A * Real.exp ((2 - b) * u) := by
            gcongr
            exact le_trans (le_abs_self K) (le_max_left _ _)
    · -- the bounded range
      rw [not_le] at hcase
      have hmono : Real.exp ((2 - b) * -v₀) ≤ Real.exp ((2 - b) * u) :=
        Real.exp_le_exp.mpr (by nlinarith)
      calc ‖𝓕⁻ (lineKernel G) u‖ ≤ |C₂| / 2 := hall u
        _ = |C₂| / 2 * Real.exp ((2 - b) * v₀) * Real.exp ((2 - b) * -v₀) := by
            rw [mul_assoc, ← Real.exp_add]; ring_nf; simp
        _ ≤ A * Real.exp ((2 - b) * u) :=
            mul_le_mul (le_max_right _ _) hmono (Real.exp_pos _).le
              (le_trans (abs_nonneg K) (le_max_left _ _))
  have := hleft.union hright
  rwa [Iic_union_Ioi, integrableOn_univ] at this

/-- **The Mellin transform of the signal is the kernel** on the line `Re w = −2`. -/
theorem mellin_signal_eq {G : ℂ → ℂ} (hG : IsSignalKernel G) {b K Z₀ : ℝ} (hb : b < 2)
    (hZ₀ : 0 < Z₀) (hK : ∀ Z : ℝ, Z₀ ≤ Z → ‖signal G 2 Z‖ ≤ K * Z ^ b) (τ : ℝ) :
    mellin (signal G 2) (((-2 : ℝ) : ℂ) + τ * I) = G (-(((-2 : ℝ) : ℂ) + τ * I)) := by
  have hF := integrable_fourierInv_lineKernel hG hb hZ₀ hK
  have hFf : Integrable (𝓕 (lineKernel G)) := by
    have h : 𝓕 (lineKernel G) = fun u => 𝓕⁻ (lineKernel G) (-u) := by
      funext u
      rw [Real.fourierInv_eq_fourier_neg, neg_neg]
    rw [h]
    exact hF.comp_neg
  have hinv := (integrable_lineKernel hG).fourier_fourierInv_eq hFf
    (v := τ / (2 * Real.pi)) (continuous_lineKernel hG).continuousAt
  rw [mellin_eq_fourier]
  have hre : (((-2 : ℝ) : ℂ) + τ * I).re = -2 := by simp
  have him : (((-2 : ℝ) : ℂ) + τ * I).im = τ := by simp
  rw [hre, him]
  have hfun : (fun u : ℝ => Real.exp (-(-2) * u) • signal G 2 (Real.exp (-u))) =
      𝓕⁻ (lineKernel G) := by
    funext u
    rw [fourierInv_lineKernel]
    norm_num
  rw [hfun, hinv]
  unfold lineKernel
  congr 2
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

/-- The half-open strips of the Mellin variable. -/
theorem isOpen_strip (a c : ℝ) : IsOpen {w : ℂ | a < w.re ∧ w.re < c} :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)

theorem isPreconnected_strip (a c : ℝ) : IsPreconnected {w : ℂ | a < w.re ∧ w.re < c} :=
  ((convex_halfSpace_re_gt a).inter (convex_halfSpace_re_lt c)).isPreconnected

/-- **Continuation.** A kernel whose signal is `O(Z^b)` at infinity, `b < 2`, extends
holomorphically to `Re s > b`. -/
theorem exists_differentiableOn_eq_of_signal_le {G : ℂ → ℂ} (hG : IsSignalKernel G)
    {b K Z₀ : ℝ} (hb : b < 2) (hZ₀ : 0 < Z₀)
    (hK : ∀ Z : ℝ, Z₀ ≤ Z → ‖signal G 2 Z‖ ≤ K * Z ^ b) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {s : ℂ | b < s.re} ∧
      ∀ s : ℂ, max b 1 < s.re → F s = G s := by
  set f : ℝ → ℂ := signal G 2 with hf
  have hloc : LocallyIntegrableOn f (Ioi 0) :=
    (continuousOn_signal_two hG).locallyIntegrableOn measurableSet_Ioi
  have htop : f =O[atTop] fun Z : ℝ => Z ^ (-(-b)) := by
    refine IsBigO.of_bound K ?_
    filter_upwards [eventually_ge_atTop Z₀] with Z hZ
    have hZpos : 0 < Z := lt_of_lt_of_le hZ₀ hZ
    rw [neg_neg, Real.norm_of_nonneg (Real.rpow_nonneg hZpos.le b)]
    exact hK Z hZ
  have hbot : ∀ B : ℝ, 2 ≤ B → f =O[𝓝[>] 0] fun Z : ℝ => Z ^ (-(-B)) := by
    intro B hB
    obtain ⟨C, hC⟩ := norm_signal_two_le hG hB
    refine IsBigO.of_bound (C / 2) ?_
    filter_upwards [self_mem_nhdsWithin] with Z hZ
    rw [neg_neg, Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt hZ) B)]
    exact hC Z hZ
  -- the Mellin transform is holomorphic on `−B < Re w < −b`
  have hdiff : ∀ w : ℂ, w.re < -b → DifferentiableAt ℂ (mellin f) w := by
    intro w hw
    have hB : (2 : ℝ) ≤ max 2 (1 - w.re) := le_max_left _ _
    exact mellin_differentiableAt_of_isBigO_rpow hloc htop hw (hbot _ hB)
      (by have := le_max_right (2 : ℝ) (1 - w.re); linarith)
  -- it is the kernel on the line `Re w = −2`, hence left of `−max b 1`
  have heq : ∀ w : ℂ, w.re < -(max b 1) → mellin f w = G (-w) := by
    intro w hw
    set B : ℝ := max 3 (1 - w.re) with hBdef
    have hB3 : (3 : ℝ) ≤ B := le_max_left _ _
    have hBw : -B < w.re := by have := le_max_right (3 : ℝ) (1 - w.re); linarith
    have hmax1 : (1 : ℝ) ≤ max b 1 := le_max_right _ _
    have hmaxb : b ≤ max b 1 := le_max_left _ _
    have hmax2 : max b 1 < 2 := max_lt hb (by norm_num)
    set U : Set ℂ := {z : ℂ | -B < z.re ∧ z.re < -(max b 1)} with hU
    have hUo : IsOpen U := isOpen_strip _ _
    have hA1 : AnalyticOnNhd ℂ (mellin f) U := by
      refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
      exact (hdiff z (by have := hz.2; linarith)).differentiableWithinAt
    have hA2 : AnalyticOnNhd ℂ (fun z : ℂ => G (-z)) U := by
      refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
      have hre : 1 < (-z).re := by rw [neg_re]; have := hz.2; linarith
      exact ((hG.differentiableAt _ hre).comp z differentiableAt_id.neg).differentiableWithinAt
    have h0 : (((-2 : ℝ) : ℂ)) ∈ U := by
      refine ⟨?_, ?_⟩ <;> simp only [ofReal_re] <;> linarith
    have hfreq : ∃ᶠ z in 𝓝[≠] (((-2 : ℝ) : ℂ)), mellin f z = (fun z : ℂ => G (-z)) z := by
      rw [frequently_iff]
      intro S hS
      obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhdsWithin_iff.mp hS
      refine ⟨((-2 : ℝ) : ℂ) + ((ε / 2 : ℝ) : ℂ) * I, hεS ⟨?_, ?_⟩, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_I, mul_one,
          norm_real, Real.norm_of_nonneg (by positivity)]
        linarith
      · intro h
        have := congrArg Complex.im h
        simp at this
        linarith
      · exact mellin_signal_eq hG hb hZ₀ hK (ε / 2)
    exact hA1.eqOn_of_preconnected_of_frequently_eq hA2 (isPreconnected_strip _ _) h0 hfreq
      ⟨hBw, hw⟩
  refine ⟨fun s => mellin f (-s), ?_, ?_⟩
  · intro s hs
    have hd := hdiff (-s) (by rw [neg_re]; exact neg_lt_neg hs)
    exact (hd.comp s differentiableAt_id.neg).differentiableWithinAt
  · intro s hs
    have := heq (-s) (by rw [neg_re]; exact neg_lt_neg hs)
    simpa using this

/-- **Zeros.** If `G L = E` on `Re s > 1`, with `L` and `E` holomorphic on `Re s > b`, `E`
without zeros there, `b < 1`, and the signal of `G` is `O(Z^b)` at infinity, then `L` has no
zero in `Re s > b`. -/
theorem ne_zero_of_signal_le {G L E : ℂ → ℂ} (hG : IsSignalKernel G) {b K Z₀ : ℝ} (hb : b < 1)
    (hZ₀ : 0 < Z₀) (hK : ∀ Z : ℝ, Z₀ ≤ Z → ‖signal G 2 Z‖ ≤ K * Z ^ b)
    (hL : DifferentiableOn ℂ L {s : ℂ | b < s.re}) (hE : DifferentiableOn ℂ E {s : ℂ | b < s.re})
    (hE0 : ∀ s : ℂ, b < s.re → E s ≠ 0) (hGL : ∀ s : ℂ, 1 < s.re → G s * L s = E s)
    (ρ : ℂ) (hρ : b < ρ.re) : L ρ ≠ 0 := by
  obtain ⟨F, hF, hFG⟩ := exists_differentiableOn_eq_of_signal_le hG (by linarith) hZ₀ hK
  have hmax : max b 1 = 1 := max_eq_right hb.le
  rw [hmax] at hFG
  have hopen : IsOpen {s : ℂ | b < s.re} := isOpen_lt continuous_const continuous_re
  have hA1 : AnalyticOnNhd ℂ (fun s => F s * L s) {s : ℂ | b < s.re} :=
    (hF.mul hL).analyticOnNhd hopen
  have hA2 : AnalyticOnNhd ℂ E {s : ℂ | b < s.re} := hE.analyticOnNhd hopen
  have h2 : ((2 : ℝ) : ℂ) ∈ {s : ℂ | b < s.re} := by
    show b < ((2 : ℝ) : ℂ).re
    rw [ofReal_re]; linarith
  have hev : (fun s => F s * L s) =ᶠ[𝓝 ((2 : ℝ) : ℂ)] E := by
    have hnhds : {s : ℂ | 1 < s.re} ∈ 𝓝 ((2 : ℝ) : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by
        show 1 < ((2 : ℝ) : ℂ).re
        rw [ofReal_re]; norm_num)
    filter_upwards [hnhds] with s hs
    rw [hFG s hs, hGL s hs]
  have heq := hA1.eqOn_of_preconnected_of_eventuallyEq hA2
    (convex_halfSpace_re_gt b).isPreconnected h2 hev
  intro h0
  have := heq hρ
  simp only [h0, mul_zero] at this
  exact hE0 ρ hρ this.symm

/-- **Two estimates give a half-plane.** A sum `J` with a direct bound `K Z^{a₁}` and a
comparison `‖J − f‖ ≤ K Z^{a₂}` with the signal `f` of `G`, for large `Z`, forces `L` to have
no zero in `Re s > max a₁ a₂`. -/
theorem ne_zero_of_common_signal {G L E : ℂ → ℂ} (hG : IsSignalKernel G) {a₁ a₂ K Z₀ : ℝ}
    (J : ℝ → ℂ) (ha₁ : a₁ < 1) (ha₂ : a₂ < 1) (hZ₀ : 1 ≤ Z₀)
    (hJ : ∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ K * Z ^ a₁)
    (hJf : ∀ Z : ℝ, Z₀ ≤ Z → ‖J Z - signal G 2 Z‖ ≤ K * Z ^ a₂)
    (hL : DifferentiableOn ℂ L {s : ℂ | max a₁ a₂ < s.re})
    (hE : DifferentiableOn ℂ E {s : ℂ | max a₁ a₂ < s.re})
    (hE0 : ∀ s : ℂ, max a₁ a₂ < s.re → E s ≠ 0) (hGL : ∀ s : ℂ, 1 < s.re → G s * L s = E s)
    (ρ : ℂ) (hρ : max a₁ a₂ < ρ.re) : L ρ ≠ 0 := by
  refine ne_zero_of_signal_le hG (b := max a₁ a₂) (K := 2 * |K|) (max_lt ha₁ ha₂)
    (lt_of_lt_of_le one_pos hZ₀) ?_ hL hE hE0 hGL ρ hρ
  intro Z hZ
  have hZ1 : 1 ≤ Z := le_trans hZ₀ hZ
  have h1 : Z ^ a₁ ≤ Z ^ max a₁ a₂ := Real.rpow_le_rpow_of_exponent_le hZ1 (le_max_left _ _)
  have h2 : Z ^ a₂ ≤ Z ^ max a₁ a₂ := Real.rpow_le_rpow_of_exponent_le hZ1 (le_max_right _ _)
  have hpos : 0 ≤ Z ^ max a₁ a₂ := Real.rpow_nonneg (by linarith) _
  have hpos1 : 0 ≤ Z ^ a₁ := Real.rpow_nonneg (by linarith) _
  have hpos2 : 0 ≤ Z ^ a₂ := Real.rpow_nonneg (by linarith) _
  have hsub : signal G 2 Z = J Z - (J Z - signal G 2 Z) := by ring
  calc ‖signal G 2 Z‖ = ‖J Z - (J Z - signal G 2 Z)‖ := by rw [← hsub]
    _ ≤ ‖J Z‖ + ‖J Z - signal G 2 Z‖ := norm_sub_le _ _
    _ ≤ K * Z ^ a₁ + K * Z ^ a₂ := add_le_add (hJ Z hZ) (hJf Z hZ)
    _ ≤ |K| * Z ^ max a₁ a₂ + |K| * Z ^ max a₁ a₂ :=
        add_le_add
          (le_trans (mul_le_mul_of_nonneg_right (le_abs_self K) hpos1)
            (mul_le_mul_of_nonneg_left h1 (abs_nonneg K)))
          (le_trans (mul_le_mul_of_nonneg_right (le_abs_self K) hpos2)
            (mul_le_mul_of_nonneg_left h2 (abs_nonneg K)))
    _ = 2 * |K| * Z ^ max a₁ a₂ := by ring

end GaloisForLFunctions.FamilyContinuationTheory
